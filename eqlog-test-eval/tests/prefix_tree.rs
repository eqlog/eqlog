use eqlog_runtime::__private::SnapshotSet;
use eqlog_runtime::{
    PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6, PrefixTree7,
    PrefixTree8, PrefixTree9,
};
use std::collections::{BTreeMap, BTreeSet};

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
fn set_operations_preserve_shared_prefixes() {
    let mut base = PrefixTree3::new();
    for i in 0..128 {
        base.insert([i, i, i]);
    }
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
