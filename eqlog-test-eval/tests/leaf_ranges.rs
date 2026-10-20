use eqlog_runtime::wbtree::set::WBTreeSet;
use eqlog_runtime::{PrefixTree1, PrefixTree2};
use std::collections::BTreeSet;

fn check(set: &WBTreeSet, expected: &BTreeSet<u32>) {
    assert_eq!(set.len(), expected.len());
    assert_eq!(set.is_empty(), expected.is_empty());
    assert_eq!(set.iter().collect::<BTreeSet<_>>(), *expected);
    assert_eq!(
        set.iter().collect::<Vec<_>>(),
        expected.iter().copied().collect::<Vec<_>>()
    );
    for value in expected {
        assert!(set.contains(value));
    }
}

fn set(values: impl IntoIterator<Item = u32>) -> WBTreeSet {
    let mut result = WBTreeSet::new();
    for value in values {
        result.insert(value);
    }
    result
}

#[test]
fn interval_leaf_algebra_matches_sparse_and_dense_sets() {
    let inputs = [
        Vec::new(),
        vec![0],
        vec![u32::MAX],
        (0..256).collect(),
        (0..256).filter(|i| i % 2 == 0).collect(),
        (0..256).map(|i| i / 8 * 32 + i % 8).collect(),
        (u32::MAX - 255..=u32::MAX).collect(),
        (0u32..256).map(|i| i.wrapping_mul(2_654_435_761)).collect(),
    ];
    for left_values in &inputs {
        let left = set(left_values.iter().copied());
        let expected_left: BTreeSet<_> = left_values.iter().copied().collect();
        for right_values in &inputs {
            let right = set(right_values.iter().copied());
            let expected_right: BTreeSet<_> = right_values.iter().copied().collect();
            check(
                &left.union(&right),
                &expected_left.union(&expected_right).copied().collect(),
            );
            check(
                &left.intersection(&right),
                &expected_left
                    .intersection(&expected_right)
                    .copied()
                    .collect(),
            );
            check(
                &left.difference(&right),
                &expected_left.difference(&expected_right).copied().collect(),
            );
            assert_eq!(
                left.difference_iter(&right).collect::<Vec<_>>(),
                expected_left
                    .difference(&expected_right)
                    .copied()
                    .collect::<Vec<_>>()
            );
        }
        let mut mutated = left.clone();
        let mut expected = expected_left.clone();
        for value in left_values.iter().step_by(2) {
            assert_eq!(mutated.remove(value), expected.remove(value));
        }
        for value in [0, 1, 2, u32::MAX - 1, u32::MAX] {
            assert_eq!(mutated.insert(value), expected.insert(value));
            assert!(!mutated.insert(value));
        }
        check(&mutated, &expected);
        check(&left, &expected_left);
    }
}

#[test]
fn interval_leaf_mutations_preserve_snapshots() {
    let mut actual = WBTreeSet::new();
    let mut expected = BTreeSet::new();
    let mut random = 73u32;
    for round in 0..32 {
        let snapshot = actual.clone();
        let expected_snapshot = expected.clone();
        for i in 0..512 {
            random = random.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let value = match round % 4 {
                0 => random % 256,
                1 => random,
                2 => u32::MAX - random % 256,
                3 => random % 32 * 32 + i % 8,
                _ => unreachable!(),
            };
            if i % 3 == 0 {
                assert_eq!(actual.remove(&value), expected.remove(&value));
            } else {
                assert_eq!(actual.insert(value), expected.insert(value));
            }
        }
        check(&actual, &expected);
        check(&snapshot, &expected_snapshot);
    }
}

#[test]
fn interval_leaf_mapping_preserves_holes_boundaries_and_quotients() {
    for shape in 0..5 {
        let source = PrefixTree1 { set: set(0..256) };
        let mut mapping = PrefixTree2::new();
        let mut expected = BTreeSet::new();
        for key in 0u32..256 {
            if key % 7 == 0 {
                continue;
            }
            let image = match shape {
                0 => u32::MAX - 255 + key,
                1 => key * 2,
                2 => key / 8 * 32 + key % 8,
                3 => key.wrapping_mul(2_654_435_761),
                4 => key / 3,
                _ => unreachable!(),
            };
            mapping.insert([key, image]);
            expected.insert(image);
        }
        let mapped = source.mapped(Some(mapping));
        check(&mapped.set, &expected);
        let mut mutated = mapped.clone();
        for value in expected.iter().step_by(2) {
            assert!(mutated.set.remove(value));
        }
        check(&mapped.set, &expected);
        check(&source.set, &(0..256).collect());
    }
}

#[test]
fn interval_leaf_folds_resume_in_order_at_every_boundary() {
    for values in [
        vec![],
        vec![u32::MAX],
        vec![0, 1, 5, 6, u32::MAX - 1, u32::MAX],
        (0..128).map(|i| i * 2).collect(),
        (0..128).flat_map(|i| [i * 4, i * 4 + 1]).collect(),
        (0..64)
            .flat_map(|i| [u32::MAX - 253 + i * 4, u32::MAX - 252 + i * 4])
            .collect(),
    ] {
        let source = set(values.iter().copied());
        for consumed in 0..=values.len() + 1 {
            let mut iter = source.iter();
            for _ in 0..consumed {
                iter.next();
            }
            let remaining = iter.fold(Vec::new(), |mut result, value| {
                result.push(value);
                result
            });
            assert_eq!(remaining, values[consumed.min(values.len())..]);
        }
    }
}

#[test]
fn fragmented_dense_leaves_preserve_interval_snapshots() {
    let values = (0..2048).chain(u32::MAX - 2047..=u32::MAX);
    let mut actual = set(values.clone());
    let mut expected: BTreeSet<_> = values.collect();
    let original = actual.clone();
    let original_expected = expected.clone();
    let keys: Vec<_> = (0..256)
        .flat_map(|index| {
            let offset = (index * 127 % 512) * 4 + 1;
            [offset, u32::MAX - offset]
        })
        .chain([0, 1, u32::MAX - 1, u32::MAX])
        .collect();
    let mut snapshots = Vec::new();
    for (index, key) in keys.iter().enumerate() {
        if index % 32 == 0 {
            snapshots.push((actual.clone(), expected.clone()));
        }
        assert_eq!(actual.remove(key), expected.remove(key));
        assert!(!actual.remove(key));
    }
    check(&actual, &expected);
    for key in keys.iter().rev() {
        assert_eq!(actual.insert(*key), expected.insert(*key));
        assert!(!actual.insert(*key));
    }
    check(&actual, &expected);
    check(&original, &original_expected);
    for (snapshot, expected) in snapshots {
        check(&snapshot, &expected);
    }
}

#[test]
fn fragmented_algebra_results_remain_editable_and_mappable() {
    let dense = set(0..8192);
    let holes = set((0..8192).step_by(11));
    let mut actual = dense.difference(&holes);
    let snapshot = actual.clone();
    let mut expected: BTreeSet<_> = (0..8192).filter(|key| key % 11 != 0).collect();
    assert!(actual.insert(0));
    expected.insert(0);
    assert!(actual.remove(&1));
    expected.remove(&1);
    check(&actual, &expected);
    check(&snapshot, &(0..8192).filter(|key| key % 11 != 0).collect());

    let mut mapping = PrefixTree2::new();
    for key in 0..8192 {
        if key % 7 != 0 {
            mapping.insert([key, u32::MAX - 8191 + key]);
        }
    }
    let mapped = PrefixTree1 { set: actual }.mapped(Some(mapping));
    let expected: BTreeSet<_> = expected
        .into_iter()
        .filter(|key| key % 7 != 0)
        .map(|key| u32::MAX - 8191 + key)
        .collect();
    check(&mapped.set, &expected);
    let mut changed = mapped.clone();
    assert!(changed.set.remove(&u32::MAX));
    assert!(changed.set.insert(0));
    check(&mapped.set, &expected);
    let mut changed_expected = expected;
    changed_expected.remove(&u32::MAX);
    changed_expected.insert(0);
    check(&changed.set, &changed_expected);
}
