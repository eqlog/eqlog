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
fn maintenance_uses_the_latest_shared_index_while_consumers_keep_their_checkpoints() {
    let mut rows = PrefixTree2::new();
    rows.insert([1, 10]);
    rows.insert([2, 20]);
    let mut seed = IndexSeed::<PrefixTree2, PrefixTree2>::new();
    let mut versions = RelationVersions::new();
    let visited = Cell::new(0);
    let project = |[x, y]: [u32; 2]| {
        visited.set(visited.get() + 1);
        Some([y, x])
    };
    versions.publish(&seed.update(&rows, project));
    let initial = versions.consume(0).new;
    let initial_c = versions.consume(2).new;
    assert!(SnapshotSet::shares_root(&initial, &initial_c));
    assert_eq!(visited.get(), 2);

    rows.insert([3, 10]);
    versions.publish(&seed.update(&rows, project));
    let a = versions.consume(0);
    assert_eq!(visited.get(), 3);
    assert!(SnapshotSet::shares_root(&a.old, &initial));
    assert_eq!(a.new.iter().collect::<Vec<_>>(), vec![[10, 3]]);
    let after_a = versions.current().clone();

    rows.insert([4, 20]);
    assert_eq!(visited.get(), 3);
    versions.publish(&seed.update(&rows, project));
    let c = versions.consume(2);
    assert_eq!(visited.get(), 4);
    assert!(SnapshotSet::shares_root(&c.old, &initial));
    assert_eq!(c.new.iter().collect::<Vec<_>>(), vec![[10, 3], [20, 4]]);

    versions.publish(&seed.update(&rows, |_| panic!("A can reuse the index maintained by C")));
    let a = versions.consume(0);
    assert!(SnapshotSet::shares_root(&a.old, &after_a));
    assert_eq!(a.new.iter().collect::<Vec<_>>(), vec![[20, 4]]);
    assert!(SnapshotSet::shares_root(
        &versions.consume(0).old,
        &versions.consume(2).old,
    ));

    rows.remove([3, 10]);
    rows.insert([3, 20]);
    versions.publish(&seed.update(&rows, project));
    assert_eq!(visited.get(), 6);
    let a = versions.consume(0);
    let c = versions.consume(2);
    assert!(!a.old.contains([10, 3]));
    assert_eq!(a.new.iter().collect::<Vec<_>>(), vec![[20, 3]]);
    assert!(SnapshotSet::shares_root(&a.old, &c.old));
    assert!(SnapshotSet::shares_root(&a.new, &c.new));
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
