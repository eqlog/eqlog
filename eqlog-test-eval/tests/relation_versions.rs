use eqlog_runtime::__private::{RelationVersions, SnapshotSet};
use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::{PrefixTree1, PrefixTree2};

#[test]
fn consumers_advance_to_the_same_root_even_after_a_storage_rebuild() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree1::new();
    for i in 0..100 {
        rows.insert([i]);
    }
    versions.publish(&rows, PrefixTree1::empty());
    versions.consume(0);
    versions.consume(1);
    let first = versions.consume(0);
    let second = versions.consume(1);
    assert!(SnapshotSet::shares_root(&first.old, &second.old));
    assert!(SnapshotSet::shares_root(&first.old, &rows));

    let mut rebuilt = PrefixTree1::new();
    for i in (0..100).rev() {
        rebuilt.insert([i]);
    }
    assert!(!SnapshotSet::shares_root(&rows, &rebuilt));
    versions.publish(PrefixTree1::empty(), &rebuilt);
    let unchanged = versions.consume(0);
    assert!(SnapshotSet::shares_root(&first.old, &unchanged.old));
    assert!(unchanged.new.is_empty());
}

#[test]
fn a_lagging_consumer_keeps_its_snapshot_and_sees_all_intervening_changes() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree2::new();
    rows.insert([0, 0]);
    rows.insert([1, 1]);
    versions.publish(&rows, PrefixTree2::empty());
    versions.consume(0);
    versions.consume(1);
    let original = versions.consume(0).old;

    rows.insert([0, 2]);
    versions.publish(&rows, PrefixTree2::empty());
    assert_eq!(
        versions.consume(0).new.iter().collect::<Vec<_>>(),
        vec![[0, 2]]
    );
    rows.insert([0, 3]);
    versions.publish(&rows, PrefixTree2::empty());
    let lagging = versions.consume(1);
    assert!(SnapshotSet::shares_root(&original, &lagging.old));
    assert_eq!(lagging.new.iter().collect::<Vec<_>>(), vec![[0, 2], [0, 3]]);

    let current = versions.consume(1).old;
    assert!(SnapshotSet::shares_root(
        original.get(1).unwrap(),
        current.get(1).unwrap()
    ));
    assert!(!SnapshotSet::shares_root(
        original.get(0).unwrap(),
        current.get(0).unwrap()
    ));
    versions.consume(0);
    assert!(SnapshotSet::shares_root(&current, &versions.consume(0).old));
}

#[test]
fn equality_replacements_are_unseen_and_filtered_old_views_are_shared() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree2::new();
    rows.insert([0, 1]);
    rows.insert([2, 3]);
    versions.publish(&rows, PrefixTree2::empty());
    versions.consume(0);
    versions.consume(1);
    rows.remove([0, 1]);
    rows.insert([0, 0]);
    versions.publish(&rows, PrefixTree2::empty());
    let first = versions.consume(0);
    let second = versions.consume(1);
    assert_eq!(first.old.iter().collect::<Vec<_>>(), vec![[2, 3]]);
    assert_eq!(first.new.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert!(SnapshotSet::shares_root(&first.old, &second.old));
    assert!(SnapshotSet::shares_root(&first.new, &second.new));
}

#[test]
fn mapped_snapshots_share_roots_without_materializing_empty_differences() {
    let mut rows = PrefixTree2::new();
    let mut mapping = PrefixTree2::new();
    for i in 0..10 {
        rows.insert([i, i]);
        mapping.insert([i, i + 10]);
    }
    let mapped = PrefixTree2 {
        map: rows.map.mapped(mapping),
    };
    let mut versions = RelationVersions::new();
    versions.publish(PrefixTree2::empty(), &mapped);
    let first = versions.consume(0);
    assert!(SnapshotSet::shares_root(&first.new, &mapped));
    let second = versions.consume(0);
    assert!(second.new.is_empty());
    assert!(SnapshotSet::shares_root(&second.old, &mapped));
    let mut rebuilt = PrefixTree2::new();
    for row in mapped.iter() {
        rebuilt.insert(row);
    }
    versions.publish(&rebuilt, PrefixTree2::empty());
    assert!(SnapshotSet::shares_root(&versions.consume(0).old, &mapped));
}

#[test]
fn generic_map_difference_still_applies_callbacks_to_shared_values() {
    let mut map = WBTreeMap::new();
    map.insert(1, 2);
    let snapshot = map.clone();
    let result = map.difference(&snapshot, |_, left, right| Some(left + right));
    assert_eq!(result.get(&1), Some(&4));
}
