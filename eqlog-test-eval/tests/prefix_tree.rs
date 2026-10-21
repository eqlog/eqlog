use eqlog_runtime::__private::SnapshotSet;
use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::wbtree::mapping::MonotoneMap;
use eqlog_runtime::{
    PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6, PrefixTree7,
    PrefixTree8, PrefixTree9,
};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

#[test]
fn sparse_nonmonotone_head_maps_only_read_their_domain() {
    let mut source = PrefixTree3::new();
    for key in 0..1024 {
        source.insert([key, key % 8, key]);
    }
    let forced = Rc::new(Cell::new(0));
    let calls = forced.clone();
    source.map = source.map.mapped_entries(None, move |value| {
        calls.set(calls.get() + 1);
        Some(value.clone())
    });
    let mut heads = PrefixTree2::new();
    for row in [[7, 70], [19, 70], [31, 20], [31, 21], [2048, 99]] {
        heads.insert(row);
    }
    let mut tails = PrefixTree2::new();
    tails.insert([7, 700]);
    tails.insert([31, 3100]);
    let mapped = source.mapped(Some(heads), None, Some(tails));
    assert_eq!(forced.get(), 3);
    assert_eq!(
        mapped.iter().collect::<Vec<_>>(),
        vec![[20, 7, 3100], [21, 7, 3100], [70, 7, 700]]
    );
    assert_eq!(forced.get(), 3);
}

macro_rules! restriction_tests {
    ($name:ident, $tree:ident, $restriction:ident, $arity:expr) => {
        #[test]
        fn $name() {
            let mut tree = $tree::new();
            tree.insert_restriction(0, $restriction::new());
            assert!(tree.is_empty());
            assert!(tree.get(0).is_none());
            assert_eq!(tree.iter_restrictions().count(), 0);

            let mut restriction = $restriction::new();
            restriction.insert([1; $arity - 1]);
            tree.insert_restriction(0, restriction.clone());
            assert_eq!(tree.iter().count(), 1);
            tree.remove_restriction(0, &restriction);
            assert!(tree.is_empty());
            assert!(tree.get(0).is_none());
            assert_eq!(tree.iter_restrictions().count(), 0);
        }
    };
}

restriction_tests!(binary_restrictions, PrefixTree2, PrefixTree1, 2);
restriction_tests!(ternary_restrictions, PrefixTree3, PrefixTree2, 3);
restriction_tests!(arity_4_restrictions, PrefixTree4, PrefixTree3, 4);
restriction_tests!(arity_5_restrictions, PrefixTree5, PrefixTree4, 5);
restriction_tests!(arity_6_restrictions, PrefixTree6, PrefixTree5, 6);
restriction_tests!(arity_7_restrictions, PrefixTree7, PrefixTree6, 7);
restriction_tests!(arity_8_restrictions, PrefixTree8, PrefixTree7, 8);
restriction_tests!(arity_9_restrictions, PrefixTree9, PrefixTree8, 9);

#[test]
fn filtering_a_later_column_does_not_leave_empty_prefixes() {
    let mut tree = PrefixTree3::new();
    tree.insert([1, 2, 3]);
    let mapped = tree.mapped(None, None, Some(PrefixTree2::new()));
    assert!(mapped.is_empty());
    assert!(mapped.get(1).is_none());
    assert_eq!(mapped.iter_restrictions().count(), 0);
}

#[test]
fn mapping_a_prefix_shares_its_unchanged_suffixes() {
    let mut tree = PrefixTree3::new();
    let mut mapping = PrefixTree2::new();
    for key in 0..128 {
        mapping.insert([key, key + 150]);
        for suffix in 0..16 {
            tree.insert([key, suffix, suffix + 1]);
        }
    }
    let mut mapped = tree.mapped(Some(mapping), None, None);
    for key in 0..128 {
        assert!(SnapshotSet::shares_root(
            tree.get(key).unwrap(),
            mapped.get(key + 150).unwrap(),
        ));
    }
    mapped.remove([150, 0, 1]);
    assert!(tree.contains([0, 0, 1]));
    assert!(!mapped.contains([150, 0, 1]));
}

#[test]
fn singleton_prefix_mapping_preserves_unread_and_filtered_suffixes() {
    let mut suffix = PrefixTree2::new();
    for key in 0..128 {
        suffix.insert([key, key]);
    }
    let calls = Rc::new(Cell::new(0));
    let counter = calls.clone();
    suffix.map = suffix.map.mapped_entries(None, move |value| {
        counter.set(counter.get() + 1);
        Some(value.clone())
    });
    let mut source = PrefixTree3::new();
    source.map.insert(7, suffix.clone());
    let mut accepted = PrefixTree2::new();
    accepted.insert([7, 70]);
    let mut rejected = PrefixTree2::new();
    rejected.insert([8, 80]);

    let mapped = source.mapped(Some(accepted), None, None);
    assert!(SnapshotSet::shares_root(mapped.get(70).unwrap(), &suffix));
    assert!(source.mapped(Some(rejected.clone()), None, None).is_empty());
    assert_eq!(calls.get(), 0);

    let head_calls = Rc::new(Cell::new(0));
    let counter = head_calls.clone();
    let mut deferred = source.clone();
    deferred.map = deferred.map.mapped_entries(None, move |value| {
        counter.set(counter.get() + 1);
        Some(value.clone())
    });
    assert!(deferred.mapped(Some(rejected), None, None).is_empty());
    assert_eq!(head_calls.get(), 0);
    assert_eq!(calls.get(), 0);

    let mut last = PrefixTree2::new();
    last.insert([0, 200]);
    let partial = source.mapped(None, None, Some(last));
    assert!(partial.contains([7, 0, 200]));
    assert_eq!(calls.get(), 1);
    assert_eq!(partial.iter().collect::<Vec<_>>(), [[7, 0, 200]]);
    assert_eq!(source.iter().count(), 128);

    let mut absent = PrefixTree2::new();
    absent.insert([999, 1999]);
    let empty = source.mapped(None, None, Some(absent));
    assert!(empty.is_empty());
    assert!(empty.get(7).is_none());
}

#[test]
fn mapping_early_and_late_columns_does_not_visit_unrequested_prefixes() {
    let mut tree = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    for key in 0..128 {
        tree.insert([key, key % 5, key]);
        first.insert([key, key + 150]);
        last.insert([key, key + 300]);
    }
    let calls = Rc::new(Cell::new(0));
    let transform_calls = calls.clone();
    tree.map = tree.map.mapped_entries(None, move |value| {
        transform_calls.set(transform_calls.get() + 1);
        Some(value.clone())
    });
    let mapped = tree.mapped(Some(first), None, Some(last));
    assert_eq!(calls.get(), 0);
    assert!(mapped.contains([167, 2, 317]));
    assert_eq!(calls.get(), 1);
    assert!(mapped.contains([167, 2, 317]));
    assert_eq!(calls.get(), 1);
    assert!(mapped.get(0).is_none());
    assert_eq!(calls.get(), 1);
    assert_eq!(mapped.iter().count(), 128);
    assert_eq!(calls.get(), 128);
}

#[test]
fn small_prefix_mapping_filters_heads_before_visiting_large_suffixes() {
    for groups in [1, 2, 3, 4, 8] {
        let mut restriction = PrefixTree3::new();
        let mut group_map = PrefixTree2::new();
        let mut last_map = PrefixTree2::new();
        let mut counters = Vec::new();
        for group in 0..groups {
            let mut suffix = PrefixTree2::new();
            for key in 0..64 {
                suffix.insert([key, key]);
                last_map.insert([key, key + 200]);
            }
            let calls = Rc::new(Cell::new(0));
            let counter = calls.clone();
            suffix.map = suffix.map.mapped_entries(None, move |value| {
                counter.set(counter.get() + 1);
                Some(value.clone())
            });
            counters.push(calls);
            restriction.map.insert(group, suffix);
            if group % 2 == 0 {
                group_map.insert([group, group + 100]);
            }
        }
        let mut source = PrefixTree4::new();
        for outer in 0..128 {
            source.map.insert(outer, restriction.clone());
        }
        let mapped = source.mapped(None, Some(group_map), None, Some(last_map));
        assert!(counters.iter().all(|counter| counter.get() == 0));
        let expected: BTreeSet<_> = (0..groups)
            .filter(|group| group % 2 == 0)
            .flat_map(|group| (0..64).map(move |key| [group + 100, key, key + 200]))
            .collect();
        assert_eq!(
            mapped.get(17).unwrap().iter().collect::<BTreeSet<_>>(),
            expected
        );
        for (group, counter) in counters.iter().enumerate() {
            assert_eq!(counter.get(), if group % 2 == 0 { 64 } else { 0 });
        }
        assert!(source.contains([17, 0, 63, 63]));
        assert!(!source.contains([17, 100, 63, 263]));
    }
}

#[test]
fn small_prefix_mapping_defers_unknown_suffix_emptiness() {
    let mut suffix = PrefixTree2::new();
    for key in 0..4096 {
        suffix.insert([key, key]);
    }
    let calls = Rc::new(Cell::new(0));
    let counter = calls.clone();
    suffix.map = suffix.map.mapped_entries(None, move |value| {
        counter.set(counter.get() + 1);
        Some(value.clone())
    });
    let mut source = PrefixTree3::new();
    source.map.insert(7, suffix);
    let mut absent = PrefixTree2::new();
    absent.insert([8192, 16384]);
    let mapped = source.mapped(None, None, Some(absent));
    assert_eq!(calls.get(), 0);
    assert!(mapped.is_empty());
    assert_eq!(calls.get(), 4096);
    assert!(source.contains([7, 4095, 4095]));
}

#[test]
fn small_materialized_images_filter_pivots_and_remain_editable() {
    for mask in 0..16 {
        let mut source = PrefixTree2::new();
        let mut first = PrefixTree2::new();
        let mut last = PrefixTree2::new();
        let mut expected = BTreeSet::new();
        for key in 0..4 {
            source.insert([key + 10, key + 100]);
            first.insert([key + 10, key + 1000]);
            if mask & (1 << key) != 0 {
                last.insert([key + 100, key + 2000]);
                expected.insert([key + 1000, key + 2000]);
            }
        }
        let mut mapped = source.mapped(Some(first), Some(last));
        assert_eq!(mapped.iter().collect::<BTreeSet<_>>(), expected);
        let snapshot = mapped.clone();
        mapped.insert([1001, 3001]);
        mapped.insert([999, 2999]);
        assert!(mapped.contains([1001, 3001]));
        assert!(mapped.contains([999, 2999]));
        assert_eq!(snapshot.iter().collect::<BTreeSet<_>>(), expected);
        assert!(source.contains([11, 101]));
        assert_eq!(source.iter().count(), 4);
    }
}

#[test]
fn mapping_through_an_unchanged_column_visits_only_needed_branches() {
    let mut tree = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    for key in 0..64 {
        first.insert([key, key + 150]);
        last.insert([key, key + 300]);
        for ambient in 0..64 {
            tree.insert([key, ambient, ambient]);
        }
    }
    let calls: Vec<_> = (0..64).map(|_| Rc::new(Cell::new(0))).collect();
    for (key, restriction) in tree.iter_restrictions_mut() {
        let transform_calls = calls[key as usize].clone();
        restriction.map = restriction.map.mapped_entries(None, move |value| {
            transform_calls.set(transform_calls.get() + 1);
            Some(value.clone())
        });
    }
    let mapped = tree.mapped(Some(first), None, Some(last));
    assert!(calls.iter().all(|count| count.get() == 0));
    assert!(mapped.contains([167, 43, 343]));
    assert_eq!(calls[17].get(), 2);
    assert!(calls
        .iter()
        .enumerate()
        .all(|(key, count)| key == 17 || count.get() == 0));
    assert!(mapped.contains([167, 43, 343]));
    assert_eq!(calls[17].get(), 2);
    assert!(mapped.contains([167, 63, 363]));
    assert_eq!(calls[17].get(), 3);
}

#[test]
fn sparse_mapping_with_an_unchanged_head_does_not_scan_the_image_map() {
    let mut tree = PrefixTree2::new();
    tree.insert([7, 2048]);
    let mut mapping = PrefixTree2::new();
    for key in 0..4096 {
        mapping.insert([key, key + 8192]);
    }
    let calls = Rc::new(Cell::new(0));
    let transform_calls = calls.clone();
    mapping.map = mapping.map.mapped_entries(None, move |value| {
        transform_calls.set(transform_calls.get() + 1);
        Some(value.clone())
    });
    let mapped = tree.mapped(None, Some(mapping));
    assert_eq!(mapped.iter().collect::<Vec<_>>(), [[7, 10240]]);
    assert_eq!(calls.get(), 1);
    assert!(tree.contains([7, 2048]));
}

#[test]
fn mapping_multiple_columns_composes_through_unchanged_columns() {
    let mut tree = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    let mut next_first = PrefixTree2::new();
    let mut next_last = PrefixTree2::new();
    for key in 0..128 {
        tree.insert([key, key % 5, key]);
        first.insert([key, key + 150]);
        last.insert([key, key + 300]);
        next_first.insert([key + 150, key * 2 + 1000]);
        next_last.insert([key + 300, key * 3 + 2000]);
    }
    let mapped = tree.mapped(Some(first), None, Some(last));
    let composed = mapped.mapped(Some(next_first), None, Some(next_last));
    assert_eq!(
        composed.iter().collect::<Vec<_>>(),
        (0..128)
            .map(|key| [key * 2 + 1000, key % 5, key * 3 + 2000])
            .collect::<Vec<_>>(),
    );
    for key in 0..128 {
        assert!(tree.contains([key, key % 5, key]));
        assert!(mapped.contains([key + 150, key % 5, key + 300]));
    }
}

#[test]
fn mapping_later_columns_filters_every_empty_prefix() {
    let mut tree = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    let mut expected = Vec::new();
    for key in 0..128 {
        tree.insert([key, key % 5, key]);
        first.insert([key, key + 150]);
        if key % 3 == 0 {
            last.insert([key, key + 300]);
            expected.push([key + 150, key % 5, key + 300]);
        }
    }
    let mapped = tree.mapped(Some(first), None, Some(last));
    for key in 0..128 {
        assert_eq!(mapped.get(key + 150).is_some(), key % 3 == 0);
    }
    assert_eq!(mapped.iter_restrictions().count(), expected.len());
    assert_eq!(mapped.iter().collect::<Vec<_>>(), expected);
    assert!(mapped
        .iter_restrictions()
        .all(|(_, restriction)| !restriction.is_empty()));
    let empty = mapped.mapped(None, None, Some(PrefixTree2::new()));
    assert!(empty.is_empty());
    assert!(empty.get(150).is_none());
    assert_eq!(empty.iter_restrictions().count(), 0);
}

#[test]
fn canonical_replacements_merge_mapped_prefixes_and_preserve_snapshots() {
    let mut tree = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    for key in 0..128 {
        tree.insert([key, key % 2, key]);
        first.insert([key, key + 150]);
        last.insert([key, key + 300]);
    }
    let mapped = tree.mapped(Some(first), None, Some(last));
    let replacements = [
        BTreeMap::from([(150, 151), (152, 151)]),
        BTreeMap::from([(1, 0)]),
        BTreeMap::from([(300, 301), (302, 301)]),
    ];
    let canonical = mapped.replace_keys(replacements.each_ref()).unwrap();
    let expected: BTreeSet<_> = (0..128)
        .map(|key| [key + 150, key % 2, key + 300])
        .map(|row| {
            std::array::from_fn(|column| {
                replacements[column]
                    .get(&row[column])
                    .copied()
                    .unwrap_or(row[column])
            })
        })
        .collect();
    assert_eq!(canonical.iter().collect::<BTreeSet<_>>(), expected);
    assert_eq!(canonical.iter().count(), 126);
    assert_eq!(
        canonical.get(151).unwrap().iter().collect::<Vec<_>>(),
        [[0, 301]]
    );
    assert!(canonical.get(150).is_none());
    assert!(canonical.get(152).is_none());
    assert!(mapped.contains([150, 0, 300]));
    assert!(mapped.contains([151, 1, 301]));
    assert!(tree.contains([0, 0, 0]));
}

#[test]
fn mapped_columns_and_set_operations_agree_with_tuple_sets() {
    for seed in 0..32u64 {
        let mut state = seed;
        let mut tree = PrefixTree4::new();
        let mut first = PrefixTree2::new();
        let mut last = PrefixTree2::new();
        let mut first_images = BTreeMap::new();
        let mut last_images = BTreeMap::new();
        for key in 0..64 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            if state >> 62 != 0 {
                first.insert([key, key * 2 + 256]);
                first_images.insert(key, key * 2 + 256);
            }
            for shift in [24, 32] {
                let suffix = (state >> shift) as u32;
                tree.insert([key, suffix % 8, suffix % 32, suffix % 3]);
            }
        }
        for key in 0..32 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            if state >> 62 != 0 {
                last.insert([key, key * 3 + 512]);
                last_images.insert(key, key * 3 + 512);
            }
        }
        let mapped = tree.mapped(Some(first), None, Some(last), None);
        let expected: BTreeSet<_> = tree
            .iter()
            .filter_map(|[a, b, c, d]| Some([*first_images.get(&a)?, b, *last_images.get(&c)?, d]))
            .collect();
        assert_eq!(
            mapped.iter().collect::<BTreeSet<_>>(),
            expected,
            "seed {seed}"
        );
        assert_eq!(mapped.is_empty(), expected.is_empty());
        for row in &expected {
            assert!(mapped.contains(*row));
        }
        let mut edited = mapped.clone();
        for (index, &row) in expected.iter().enumerate() {
            if index % 3 == 0 {
                edited.remove(row);
                let [a, b, c, d] = row;
                edited.insert([a, b + 8, c, d]);
            }
        }
        let edited_rows: BTreeSet<_> = edited.iter().collect();
        for (left, right, left_rows, right_rows) in [
            (&mapped, &edited, &expected, &edited_rows),
            (&edited, &mapped, &edited_rows, &expected),
        ] {
            assert_eq!(
                left.difference(right).iter().collect::<BTreeSet<_>>(),
                left_rows.difference(right_rows).copied().collect(),
                "seed {seed}",
            );
            assert_eq!(
                left.union(right).iter().collect::<BTreeSet<_>>(),
                left_rows.union(right_rows).copied().collect(),
                "seed {seed}",
            );
            assert_eq!(
                left.intersection(right).iter().collect::<BTreeSet<_>>(),
                left_rows.intersection(right_rows).copied().collect(),
                "seed {seed}",
            );
            assert_eq!(left.is_subset(right), left_rows.is_subset(right_rows));
            let mut difference = BTreeSet::new();
            left.visit_difference(right, &mut |row| {
                difference.insert(row);
            });
            assert_eq!(
                difference,
                left_rows.difference(right_rows).copied().collect()
            );
        }
        assert_eq!(mapped.iter().collect::<BTreeSet<_>>(), expected);
    }
}

#[test]
fn column_mapping_preserves_all_images_and_merges_collisions() {
    let mut tree = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    for row in [[1, 5, 1], [2, 5, 2], [3, 6, 3], [4, 7, 4]] {
        tree.insert(row);
    }
    for row in [[1, 20], [1, 21], [2, 20], [3, 19]] {
        first.insert(row);
    }
    for row in [[1, 10], [2, 11], [2, 12], [3, 13], [4, 14]] {
        last.insert(row);
    }
    let mapped = tree.mapped(Some(first), None, Some(last));
    assert_eq!(
        mapped.iter().collect::<Vec<_>>(),
        [
            [19, 6, 13],
            [20, 5, 10],
            [20, 5, 11],
            [20, 5, 12],
            [21, 5, 10]
        ],
    );
    let empty = mapped.mapped(None, None, Some(PrefixTree2::new()));
    assert!(empty.is_empty());
    assert_eq!(empty.iter_restrictions().count(), 0);
}

#[test]
fn colliding_head_images_share_multiple_images_and_filter_empty_suffixes() {
    let mut source = PrefixTree3::new();
    let mut heads = PrefixTree2::new();
    let mut tails = PrefixTree2::new();
    heads.insert([1, 10]);
    heads.insert([1, 11]);
    for value in 0..64 {
        source.insert([1, value, value]);
        tails.insert([value, 200 + value / 2]);
    }
    let shared = source.mapped(Some(heads.clone()), None, Some(tails.clone()));
    assert!(SnapshotSet::shares_root(
        shared.get(10).unwrap(),
        shared.get(11).unwrap()
    ));

    source.insert([2, 7, 8]);
    source.insert([3, 70, 998]);
    source.insert([4, 71, 999]);
    heads.insert([2, 10]);
    heads.insert([3, 12]);
    heads.insert([4, 10]);
    let mut mapped = source.mapped(Some(heads), None, Some(tails));
    let expected: BTreeSet<_> = (0..64)
        .flat_map(|value| [[10, value, 200 + value / 2], [11, value, 200 + value / 2]])
        .chain([[10, 7, 204]])
        .collect();
    assert_eq!(mapped.iter().collect::<BTreeSet<_>>(), expected);
    assert!(mapped.get(12).is_none());
    assert!(mapped.get(10).unwrap().get(71).is_none());
    mapped.insert([10, 99, 777]);
    assert!(!mapped.contains([11, 99, 777]));
    assert_eq!(shared.iter().count(), 128);
    assert_eq!(source.iter().count(), 67);
}

#[test]
fn filtered_collisions_leave_shared_mapped_suffixes_intact() {
    let mut heads = PrefixTree2::new();
    for row in [[0, 10], [0, 11], [1, 10]] {
        heads.insert(row);
    }
    let mut tails = PrefixTree2::new();
    let mut source = PrefixTree3::new();
    for value in 0..64 {
        tails.insert([value, value + 200]);
        source.insert([0, value, value]);
    }
    source.insert([1, 999, 999]);
    let mapped = source.mapped(Some(heads.clone()), None, Some(tails));
    assert!(SnapshotSet::shares_root(
        mapped.get(10).unwrap(),
        mapped.get(11).unwrap()
    ));
    assert_eq!(mapped.iter().count(), 128);

    let mut tails = PrefixTree2::new();
    let mut source = PrefixTree2::new();
    for value in (0..128).step_by(2) {
        tails.insert([value, value + 200]);
        source.insert([0, value]);
    }
    source.insert([1, 999]);
    source.insert([1, 1001]);
    let mapped = source.mapped(Some(heads), Some(tails));
    assert!(SnapshotSet::shares_root(
        mapped.get(10).unwrap(),
        mapped.get(11).unwrap()
    ));
    assert_eq!(mapped.iter().count(), 128);
}

#[test]
fn a_single_source_can_share_its_entire_image_set() {
    let mut source = PrefixTree1::new();
    source.insert([7]);
    let mut mapping = PrefixTree2::new();
    for image in 0..128 {
        mapping.insert([7, image]);
    }
    let images = mapping.get(7).unwrap().clone();
    let mut mapped = source.mapped(Some(mapping));
    assert!(SnapshotSet::shares_root(&mapped, &images));
    mapped.insert([128]);
    assert_eq!(mapped.iter().count(), 129);
    assert_eq!(images.iter().count(), 128);
}

#[test]
fn set_operations_preserve_shared_prefixes() {
    let mut base = PrefixTree3::new();
    for i in 0..128 {
        base.insert([i, i, i]);
    }
    let mut disjoint = PrefixTree3::new();
    for i in 0..128 {
        disjoint.insert([i, i, i + 128]);
    }
    let mut difference = base.difference(&disjoint);
    assert!(SnapshotSet::shares_root(&difference, &base));
    difference.insert([0, 0, 128]);
    assert_eq!(base.iter().count(), 128);
    assert_eq!(difference.iter().count(), 129);
    assert_eq!(base.get(0).unwrap().iter().collect::<Vec<_>>(), [[0, 0]]);
    let same = base.union(&base);
    assert!(SnapshotSet::shares_root(&same, &base));
    let mut extended = base.clone();
    extended.insert([128, 128, 128]);
    assert!(base.is_subset(&extended));
    assert!(!extended.is_subset(&base));
    assert!(SnapshotSet::shares_root(
        &base.intersection(&extended),
        &base
    ));
    let union = base.union(&extended);
    assert_eq!(
        union.iter().collect::<Vec<_>>(),
        extended.iter().collect::<Vec<_>>()
    );
    assert!(SnapshotSet::shares_root(
        base.get(0).unwrap(),
        union.get(0).unwrap()
    ));
}

#[test]
fn subset_comparisons_respect_mappings_and_filtered_prefixes() {
    let mut base = PrefixTree2::new();
    let mut mapping = PrefixTree2::new();
    let mut expected = PrefixTree2::new();
    for i in 0..128 {
        base.insert([i, i]);
        if i % 3 != 0 {
            mapping.insert([i, i + 128]);
            expected.insert([i + 128, i]);
        }
    }
    let mapped = PrefixTree2 {
        map: base.map.mapped(mapping),
    };
    assert!(mapped.is_subset(&expected));
    assert!(expected.is_subset(&mapped));
    assert!(!mapped.is_subset(&base));
    assert!(!base.is_subset(&mapped));
    assert!(mapped.difference(&expected).is_empty());
    assert!(expected.difference(&mapped).is_empty());
    assert!(SnapshotSet::shares_root(
        &mapped.intersection(&mapped),
        &mapped
    ));
    assert!(SnapshotSet::shares_root(&mapped.union(&mapped), &mapped));
    expected.insert([0, 0]);
    assert!(mapped.is_subset(&expected));
    assert!(!expected.is_subset(&mapped));
    assert_eq!(
        expected.difference(&mapped).iter().collect::<Vec<_>>(),
        vec![[0, 0]]
    );
    let union = mapped.union(&expected);
    assert_eq!(
        union.iter().collect::<Vec<_>>(),
        expected.iter().collect::<Vec<_>>()
    );
    for (left, right) in [(&mapped, &expected), (&expected, &mapped)] {
        assert_eq!(
            left.intersection(right).iter().collect::<Vec<_>>(),
            mapped.iter().collect::<Vec<_>>()
        );
    }
}

#[test]
fn differences_agree_with_tuple_sets_after_scattered_edits() {
    let mut original = PrefixTree2::new();
    for i in 0..512 {
        original.insert([i, i % 7]);
    }
    for stride in [1, 2, 3, 17, 32, 127] {
        let mut edited = original.clone();
        for i in (0..512).step_by(stride) {
            edited.remove([i, i % 7]);
            edited.insert([i + 512, i % 5]);
        }
        for (left, right) in [(&original, &edited), (&edited, &original)] {
            let left_rows: BTreeSet<_> = left.iter().collect();
            let right_rows: BTreeSet<_> = right.iter().collect();
            let expected: Vec<_> = left_rows.difference(&right_rows).copied().collect();
            assert_eq!(left.difference(right).iter().collect::<Vec<_>>(), expected);
            let mut visited = Vec::new();
            left.visit_difference(right, &mut |row| visited.push(row));
            assert_eq!(visited, expected);
            let expected: Vec<_> = left_rows.intersection(&right_rows).copied().collect();
            assert_eq!(
                left.intersection(right).iter().collect::<Vec<_>>(),
                expected
            );
        }
    }
}

#[test]
fn singleton_suffix_snapshots_survive_edits_and_key_replacement() {
    let original_rows = [[0, 0], [1, 1 << 31], [2, u32::MAX], [3, 7], [4, 7]];
    let mut original = PrefixTree2::new();
    for row in original_rows {
        original.insert(row);
    }
    let mut multiple = original.clone();
    multiple.insert([0, u32::MAX]);
    let mut edited = multiple.clone();
    edited.remove([0, 0]);
    edited.remove([3, 7]);

    assert_eq!(original.iter().collect::<Vec<_>>(), original_rows);
    assert_eq!(multiple.get(0).unwrap().iter().count(), 2);
    assert_eq!(
        edited.get(0).unwrap().iter().collect::<Vec<_>>(),
        [[u32::MAX]]
    );
    assert!(edited.get(3).is_none());
    assert_eq!(
        edited.difference(&original).iter().collect::<Vec<_>>(),
        [[0, u32::MAX]]
    );

    let replacements = BTreeMap::from([(0, 1), (1 << 31, 2), (u32::MAX, 3), (7, 4)]);
    for snapshot in [original, multiple, edited] {
        let renamed = snapshot
            .replace_keys([&BTreeMap::new(), &replacements])
            .unwrap();
        let expected: BTreeSet<_> = snapshot
            .iter()
            .map(|[prefix, key]| [prefix, replacements[&key]])
            .collect();
        assert_eq!(renamed.iter().collect::<BTreeSet<_>>(), expected);
    }
}

#[test]
fn repeated_restriction_inserts_preserve_mapped_and_sibling_snapshots() {
    let mut source = PrefixTree3::new();
    let mut first = PrefixTree2::new();
    let mut last = PrefixTree2::new();
    for key in 0..32 {
        first.insert([key, key + 100]);
        last.insert([key, key + 200]);
        for suffix in 0..32 {
            source.insert([key, key % 3, suffix]);
        }
    }
    let mapped = source.mapped(Some(first), None, Some(last));
    let mut tree = PrefixTree4::new();
    tree.insert_restriction(7, mapped.clone());
    tree.insert_restriction(8, mapped.clone());
    let before = tree.clone();
    let before_rows: BTreeSet<_> = [7, 8]
        .into_iter()
        .flat_map(|owner| {
            source
                .iter()
                .map(move |[first, label, last]| [owner, first + 100, label, last + 200])
        })
        .collect();
    let mut expected = before_rows.clone();
    for key in 0..32 {
        for label in [key % 3, 9] {
            let row = [key + 100, label, key + 232];
            let mut incoming = PrefixTree3::new();
            incoming.insert(row);
            tree.insert_restriction(7, incoming.clone());
            tree.insert_restriction(7, incoming);
            expected.insert([7, row[0], row[1], row[2]]);
        }
    }
    let mut bulk = PrefixTree3::new();
    for key in 0..16 {
        bulk.insert([100, 10, key + 300]);
        bulk.insert([101, 10, key + 300]);
        expected.insert([7, 100, 10, key + 300]);
        expected.insert([7, 101, 10, key + 300]);
    }
    tree.insert_restriction(7, bulk);
    tree.insert_restriction(9, PrefixTree3::new());

    assert_eq!(
        tree.iter().collect::<Vec<_>>(),
        expected.into_iter().collect::<Vec<_>>()
    );
    assert_eq!(before.iter().collect::<BTreeSet<_>>(), before_rows);
    assert_eq!(
        tree.get(8).unwrap().iter().collect::<Vec<_>>(),
        mapped.iter().collect::<Vec<_>>()
    );
    assert!(tree.get(9).is_none());
    assert_eq!(source.iter().count(), 32 * 32);
}

#[test]
fn bulk_restriction_unions_preserve_filtered_snapshots() {
    let mut tree = PrefixTree4::new();
    let mut expected = BTreeSet::new();
    let mut snapshots = Vec::new();
    let mut sources = Vec::new();
    for round in 0..8 {
        let mut source = PrefixTree3::new();
        let mut first = PrefixTree2::new();
        let mut last = PrefixTree2::new();
        for key in 0..24 {
            if key % 3 != round % 3 {
                first.insert([key, key + 100]);
            }
            for label in 0..3 {
                source.insert([key, label, 2 * ((17 * key + 7 * label + round) % 41)]);
            }
        }
        for key in 0..41 {
            if key % 4 != round % 4 {
                last.insert([2 * key, 2 * key + 200]);
            }
        }
        let source_rows: BTreeSet<_> = source.iter().collect();
        let image_rows: BTreeSet<_> = source_rows
            .iter()
            .filter(|[key, _, last]| key % 3 != round % 3 && (last / 2) % 4 != round % 4)
            .map(|[key, label, last]| [key + 100, *label, last + 200])
            .collect();
        let image = source.mapped(Some(first), None, Some(last));
        let incoming = if round % 2 == 0 {
            image.clone()
        } else {
            let mut plain = PrefixTree3::new();
            for row in &image_rows {
                plain.insert(*row);
            }
            plain
        };
        tree.insert_restriction(7, incoming.clone());
        tree.insert_restriction(7, incoming);
        expected.extend(
            image_rows
                .iter()
                .map(|[first, label, last]| [7, *first, *label, *last]),
        );
        assert_eq!(tree.iter().collect::<BTreeSet<_>>(), expected);
        if round % 2 == 0 {
            snapshots.push((tree.clone(), expected.clone()));
        }
        sources.push((source, source_rows, image, image_rows));
    }
    for (snapshot, rows) in snapshots {
        assert_eq!(snapshot.iter().collect::<BTreeSet<_>>(), rows);
    }
    for (source, source_rows, image, image_rows) in sources {
        assert_eq!(source.iter().collect::<BTreeSet<_>>(), source_rows);
        assert_eq!(image.iter().collect::<BTreeSet<_>>(), image_rows);
    }
}

#[test]
fn difference_visitors_stop_early_and_skip_shared_subtrees() {
    let mut original = WBTreeMap::new();
    for key in 0..4096 {
        original.insert(key, ());
    }
    let mut visited = Vec::new();
    assert!(
        !original.all_difference_entries(&WBTreeMap::new(), |key, (), right| {
            assert!(right.is_none());
            visited.push(key);
            key < 3
        })
    );
    assert_eq!(visited, [0, 1, 2, 3]);

    for removed in [0, 17, 2048, 4095] {
        let mut edited = original.clone();
        edited.remove(&removed);
        edited.insert(4096, ());
        for (left, right, missing) in [(&original, &edited, removed), (&edited, &original, 4096)] {
            let mut visits = 0;
            let mut difference = Vec::new();
            assert!(left.all_difference_entries(right, |key, (), other| {
                visits += 1;
                if other.is_none() {
                    difference.push(key);
                }
                true
            }));
            assert_eq!(difference, [missing]);
            assert!(visits < 64, "a sparse edit scanned shared subtrees");
        }
    }
}

#[test]
fn prepared_shared_maps_defer_lookups_through_sparse_prefixes() {
    let mut source = PrefixTree3::new();
    let mut images = PrefixTree2::new();
    for key in 0..64 {
        images.insert([key, key + 100]);
        for inner in 0..32 {
            source.insert([key, inner, inner]);
        }
    }
    let forced = Rc::new(Cell::new(0));
    let calls = forced.clone();
    source.map = source.map.mapped_entries(None, move |value| {
        calls.set(calls.get() + 1);
        Some(value.clone())
    });
    let mapping = MonotoneMap::new(&images).unwrap();
    let mut mapped = source.mapped_shared([Some(mapping.clone()), None, Some(mapping)]);
    assert_eq!(forced.get(), 0);
    assert!(mapped.contains([107, 3, 103]));
    assert_eq!(forced.get(), 1);
    assert!(mapped.contains([107, 4, 104]));
    assert_eq!(forced.get(), 1);
    let snapshot = mapped.clone();
    mapped.remove([107, 3, 103]);
    assert!(snapshot.contains([107, 3, 103]));
    assert!(source.contains([7, 3, 3]));
    assert_eq!(snapshot.iter().count(), 64 * 32);
    assert!(SnapshotSet::shares_root(
        &source,
        &source.mapped_shared([None, None, None])
    ));
}

#[test]
fn equivalent_suffix_maps_compare_without_forcing_shared_values() {
    let mut source = PrefixTree2::new();
    for key in 0..512 {
        source.insert([key, key]);
    }
    let forced = Rc::new(Cell::new(0));
    let calls = forced.clone();
    source.map = source.map.mapped_entries(None, move |value| {
        calls.set(calls.get() + 1);
        Some(value.clone())
    });
    let first = MonotoneMap::from_offsets([(0..=1023, 2048)]).unwrap();
    let second = MonotoneMap::from_offsets([(0..=1023, 2048)]).unwrap();
    let left = source.mapped_shared([None, Some(first)]);
    let right = source.mapped_shared([None, Some(second)]);
    assert!(left.is_subset(&right));
    assert!(right.is_subset(&left));
    assert!(left.difference(&right).is_empty());
    assert!(left.union(&right).is_subset(&left));
    assert_eq!(forced.get(), 0);

    let changed = source.mapped_shared([
        None,
        Some(MonotoneMap::from_offsets([(0..=1023, 4096)]).unwrap()),
    ]);
    assert!(!left.is_subset(&changed));
    assert!(!changed.is_subset(&left));
    assert!(left.contains([7, 2055]));
    assert!(changed.contains([7, 4103]));
}

#[test]
fn suffix_map_identity_does_not_hide_source_edits_or_filtered_domains() {
    let mut source = PrefixTree2::new();
    for key in 0..128 {
        source.insert([key, key]);
    }
    let mapping = MonotoneMap::from_offsets([(0..=255, 1024)]).unwrap();
    let before = source.mapped_shared([None, Some(mapping.clone())]);
    source.remove([5, 5]);
    source.insert([5, 200]);
    source.insert([128, 128]);
    let after = source.mapped_shared([None, Some(mapping)]);
    assert_eq!(
        after.difference(&before).iter().collect::<Vec<_>>(),
        vec![[5, 1224], [128, 1152]]
    );
    assert_eq!(
        before.difference(&after).iter().collect::<Vec<_>>(),
        vec![[5, 1029]]
    );
    let filtered = source.mapped_shared([
        None,
        Some(MonotoneMap::from_offsets([(0..=127, 1024)]).unwrap()),
    ]);
    assert!(filtered.is_subset(&after));
    assert!(!after.is_subset(&filtered));
}
