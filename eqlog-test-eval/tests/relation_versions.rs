use eqlog_runtime::__private::{RelationVersions, SnapshotSet};
use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::{PrefixTree1, PrefixTree2};

#[test]
fn model_consumers_share_filtered_ambient_views() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree1::new();
    for i in 0..100 {
        rows.insert([i]);
    }
    versions.publish(&rows);
    versions.consume((0, vec![10]));
    versions.consume((0, vec![20]));
    rows.remove([5]);
    rows.insert([100]);
    versions.publish(&rows);
    let first = versions.consume((0, vec![10]));
    let second = versions.consume((0, vec![20]));
    assert!(SnapshotSet::shares_root(&first.old, &second.old));
    assert!(SnapshotSet::shares_root(&first.new, &second.new));
    rows.insert([101]);
    versions.publish(&rows);
    let pending = versions.consume((0, vec![20]));
    assert!(pending.new.contains([101]));
}

#[test]
fn consumers_advance_to_the_same_root_even_after_a_storage_rebuild() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree1::new();
    for i in 0..100 {
        rows.insert([i]);
    }
    versions.publish(&rows);
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
    versions.publish(&rebuilt);
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
    versions.publish(&rows);
    versions.consume(0);
    versions.consume(1);
    let original = versions.consume(0).old;

    rows.insert([0, 2]);
    versions.publish(&rows);
    assert_eq!(
        versions.consume(0).new.iter().collect::<Vec<_>>(),
        vec![[0, 2]]
    );
    rows.insert([0, 3]);
    versions.publish(&rows);
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
    versions.publish(&rows);
    versions.consume(0);
    versions.consume(1);
    rows.remove([0, 1]);
    rows.insert([0, 0]);
    versions.publish(&rows);
    let first = versions.consume(0);
    let second = versions.consume(1);
    assert_eq!(first.old.iter().collect::<Vec<_>>(), vec![[2, 3]]);
    assert_eq!(first.new.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert!(SnapshotSet::shares_root(&first.old, &second.old));
    assert!(SnapshotSet::shares_root(&first.new, &second.new));
}

#[test]
fn separately_requested_ages_share_views_and_advance_their_consumers() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree2::new();
    rows.insert([0, 1]);
    rows.insert([2, 3]);
    versions.publish(&rows);
    for consumer in 0..3 {
        versions.consume(consumer);
    }

    rows.remove([0, 1]);
    rows.insert([0, 0]);
    versions.publish(&rows);
    let old_only = versions.consume_required::<true, false>(0);
    let new_only = versions.consume_required::<false, true>(1);
    let both = versions.consume(2);
    assert_eq!(old_only.old.iter().collect::<Vec<_>>(), vec![[2, 3]]);
    assert_eq!(new_only.new.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert!(old_only.new.is_empty());
    assert!(new_only.old.is_empty());
    assert!(SnapshotSet::shares_root(&old_only.old, &both.old));
    assert!(SnapshotSet::shares_root(&new_only.new, &both.new));
    for consumer in 0..3 {
        let next = versions.consume(consumer);
        assert!(next.new.is_empty());
        assert!(SnapshotSet::shares_root(&next.old, &rows));
    }
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
    versions.publish(&mapped);
    let first = versions.consume(0);
    assert!(SnapshotSet::shares_root(&first.new, &mapped));
    let second = versions.consume(0);
    assert!(second.new.is_empty());
    assert!(SnapshotSet::shares_root(&second.old, &mapped));
    let mut rebuilt = PrefixTree2::new();
    for row in mapped.iter() {
        rebuilt.insert(row);
    }
    versions.publish(&rebuilt);
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

#[test]
fn materialized_deltas_reuse_whole_added_prefixes() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree2::new();
    rows.insert([0, 0]);
    versions.publish(&rows);
    versions.consume(0);
    for i in 0..1000 {
        rows.insert([1, i]);
    }
    versions.publish(&rows);
    let lagging = versions.consume(0);
    let fresh = versions.consume(1);
    assert_eq!(lagging.new.iter().count(), 1000);
    assert!(SnapshotSet::shares_root(
        lagging.new.get(1).unwrap(),
        fresh.new.get(1).unwrap(),
    ));
}
