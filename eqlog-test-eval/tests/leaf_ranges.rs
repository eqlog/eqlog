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
