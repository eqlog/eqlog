use std::cell::Cell;

use eqlog_runtime::__private::{IndexSeed, LazyIndex, RelationVersions, SnapshotSet};
use eqlog_runtime::{PrefixTree1, PrefixTree2, PrefixTree3};

#[test]
fn a_warm_index_catches_up_only_when_read_and_keeps_untouched_branches() {
    let mut rows = PrefixTree2::new();
    for x in 0..100 {
        rows.insert([x, x % 2]);
    }
    let mut index = LazyIndex::<PrefixTree2, PrefixTree2>::new();
    let visited = Cell::new(0);
    let project = |[x, y]: [u32; 2]| {
        visited.set(visited.get() + 1);
        Some([y, x])
    };
    let first = index.get(&rows, project).clone();
    assert_eq!(visited.get(), 100);
    for x in (100..110).step_by(2) {
        index.invalidate();
        rows.insert([x, 0]);
    }
    rows.remove([0, 0]);
    assert_eq!(visited.get(), 100);
    let current = index.get(&rows, project);
    assert_eq!(visited.get(), 106);
    assert!(!current.contains([0, 0]));
    assert!(current.contains([0, 108]));
    assert!(SnapshotSet::shares_root(
        first.get(1).unwrap(),
        current.get(1).unwrap()
    ));
    assert!(first.contains([0, 0]));
    index.get(&rows, project);
    assert_eq!(visited.get(), 106);
}

#[test]
fn equal_rebuilt_sources_keep_the_index_identity() {
    let mut rows = PrefixTree2::new();
    for x in 0..100 {
        rows.insert([x, x + 1]);
    }
    let mut seed = IndexSeed::<PrefixTree2, PrefixTree2>::new();
    let first = seed.update(&rows, |[x, y]| Some([y, x]));
    let mut rebuilt = PrefixTree2::new();
    for x in (0..100).rev() {
        rebuilt.insert([x, x + 1]);
    }
    let second = seed.update(&rebuilt, |_| {
        panic!("equal contents should not be reindexed")
    });
    assert!(SnapshotSet::shares_root(&first, &second));
}

#[test]
fn off_diagonal_removals_do_not_remove_a_valid_projection() {
    let mut rows = PrefixTree3::new();
    rows.insert([1, 1, 3]);
    rows.insert([1, 2, 3]);
    let mut seed = IndexSeed::<PrefixTree3, PrefixTree2>::new();
    let project = |[x, y, z]: [u32; 3]| (x == y).then_some([z, x]);
    seed.update(&rows, project);
    rows.remove([1, 2, 3]);
    let index = seed.update(&rows, project);
    assert_eq!(index.iter().collect::<Vec<_>>(), vec![[3, 1]]);
    rows.remove([1, 1, 3]);
    rows.insert([2, 2, 3]);
    assert_eq!(
        seed.update(&rows, project).iter().collect::<Vec<_>>(),
        vec![[3, 2]]
    );
}

#[test]
fn consumers_share_index_roots_even_when_the_same_snapshot_changes_age() {
    let mut rows = PrefixTree2::new();
    rows.insert([0, 1]);
    rows.insert([2, 3]);
    let mut versions = RelationVersions::new();
    let mut first_seed = IndexSeed::<PrefixTree2, PrefixTree2>::new();
    let mut second_seed = IndexSeed::<PrefixTree2, PrefixTree2>::new();
    let project = |[x, y]: [u32; 2]| Some([y, x]);
    versions.publish(&rows, PrefixTree2::empty());
    let first = versions.consume(0).new_index(7, &mut first_seed, project);
    let second = versions.consume(1).new_index(7, &mut second_seed, |_| {
        panic!("shared snapshot should hit cache")
    });
    let old = versions.consume(0).old_index(7, &mut second_seed, |_| {
        panic!("age change should hit cache")
    });
    assert!(SnapshotSet::shares_root(&first, &second));
    assert!(SnapshotSet::shares_root(&first, &old));

    rows.remove([0, 1]);
    rows.insert([0, 0]);
    versions.publish(&rows, PrefixTree2::empty());
    let first_view = versions.consume(0);
    let second_view = versions.consume(1);
    let first = first_view.old_index(7, &mut first_seed, project);
    let second = second_view.old_index(7, &mut second_seed, |_| {
        panic!("filtered old should be shared")
    });
    assert!(SnapshotSet::shares_root(&first, &second));
    assert_eq!(first.iter().collect::<Vec<_>>(), vec![[3, 2]]);
    assert_eq!(
        first_view
            .new_index(7, &mut first_seed, project)
            .iter()
            .collect::<Vec<_>>(),
        vec![[0, 0]]
    );
}

#[test]
fn streaming_nested_difference_agrees_with_tuple_sets() {
    for seed in 0..40 {
        let mut left = PrefixTree3::new();
        let mut right = PrefixTree3::new();
        for x in 0..80 {
            if (x + seed) % 3 != 0 {
                left.insert([x % 7, x % 11, x]);
            }
            if (x + seed) % 5 != 0 {
                right.insert([x % 7, x % 11, x]);
            }
        }
        let mut actual = Vec::new();
        left.visit_difference(&right, &mut |row| actual.push(row));
        let expected: Vec<_> = left.iter().filter(|row| !right.contains(*row)).collect();
        assert_eq!(actual, expected);
    }
    let mut unary = PrefixTree1::new();
    unary.insert([1]);
    let mut actual = Vec::new();
    unary.visit_difference(PrefixTree1::empty(), &mut |row| actual.push(row));
    assert_eq!(actual, vec![[1]]);
}
