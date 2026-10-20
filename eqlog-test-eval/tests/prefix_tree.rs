use eqlog_runtime::__private::SnapshotSet;
use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::{
    PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6, PrefixTree7,
    PrefixTree8, PrefixTree9,
};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

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
