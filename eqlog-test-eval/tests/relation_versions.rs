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
    versions.publish(&rebuilt);
    assert!(versions.consume(0).new.is_empty());

    let previous = rebuilt.clone();
    rebuilt.insert([100]);
    versions.publish(&rebuilt);
    assert_eq!(
        versions.consume(0).new.iter().collect::<Vec<_>>(),
        vec![[100]]
    );
    versions.publish(&previous);
    assert!(!versions.current().contains([100]));
    assert!(versions.consume(0).new.is_empty());

    rebuilt.remove([5]);
    versions.publish(&rebuilt);
    let lagging = versions.consume(1);
    assert_eq!(lagging.new.iter().collect::<Vec<_>>(), vec![[100]]);
    assert!(!lagging.old.contains([5]));
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
fn historical_views_share_deltas_without_changing_filtered_consumers() {
    let mut versions = RelationVersions::new();
    let mut rows = PrefixTree2::new();
    rows.insert([0, 1]);
    rows.insert([2, 3]);
    versions.publish(&rows);
    versions.consume(0);
    versions.consume(1);
    let before = rows.clone();
    rows.remove([0, 1]);
    rows.insert([0, 0]);
    versions.publish(&rows);
    let historical = versions.consume_membership::<true, true>(0);
    let filtered = versions.consume(1);
    assert!(SnapshotSet::shares_root(&historical.old, &before));
    assert_eq!(filtered.old.iter().collect::<Vec<_>>(), vec![[2, 3]]);
    assert_eq!(historical.new.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert!(SnapshotSet::shares_root(&historical.new, &filtered.new));
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
fn generic_map_operations_still_apply_callbacks_to_shared_values() {
    let mut map = WBTreeMap::new();
    map.insert(1, 2);
    let snapshot = map.clone();
    let result = map.difference(&snapshot, |_, left, right| Some(left + right));
    assert_eq!(result.get(&1), Some(&4));
    let union = map.union(&snapshot, |_, left, right| left + right);
    assert_eq!(union.get(&1), Some(&4));
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

#[test]
fn inherited_resets_replay_local_rows_before_resuming_temporal_differences() {
    let mut baseline = PrefixTree2::new();
    baseline.insert([0, 0]);
    let mut rows = baseline.clone();
    rows.insert([1, 1]);
    let mut versions = RelationVersions::new();
    versions.publish(&rows);
    versions.consume(0);

    let inherited = versions.consume_inherited_required::<true, true>(0, &baseline);
    assert_eq!(inherited.old.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert_eq!(inherited.new.iter().collect::<Vec<_>>(), vec![[1, 1]]);
    let unchanged = versions.consume(0);
    assert!(unchanged.new.is_empty());
    assert!(SnapshotSet::shares_root(&unchanged.old, &rows));

    rows.insert([2, 2]);
    versions.publish(&rows);
    let temporal = versions.consume(0);
    assert_eq!(
        temporal.old.iter().collect::<Vec<_>>(),
        vec![[0, 0], [1, 1]]
    );
    assert_eq!(temporal.new.iter().collect::<Vec<_>>(), vec![[2, 2]]);
}

fn check_inherited_age_selection<const OLD: bool, const NEW: bool>() {
    let mut rows = PrefixTree1::new();
    rows.insert([7]);
    let mut versions = RelationVersions::new();
    versions.publish(&rows);
    let inherited = versions.consume_inherited_required::<OLD, NEW>(0, &rows);
    assert_eq!(inherited.old.is_empty(), !OLD);
    assert!(inherited.new.is_empty());
    let temporal = versions.consume(0);
    assert!(temporal.new.is_empty());
    assert!(SnapshotSet::shares_root(&temporal.old, &rows));

    let inherited = versions.consume_inherited_membership::<OLD, NEW>(1, &rows);
    assert_eq!(inherited.old.is_empty(), !OLD);
    assert!(inherited.new.is_empty());
    let temporal = versions.consume(1);
    assert!(temporal.new.is_empty());
    assert!(SnapshotSet::shares_root(&temporal.old, &rows));
}

#[test]
fn inherited_resets_advance_even_when_requested_views_are_empty() {
    check_inherited_age_selection::<false, false>();
    check_inherited_age_selection::<false, true>();
    check_inherited_age_selection::<true, false>();
    check_inherited_age_selection::<true, true>();
}

#[test]
fn new_parent_rows_join_with_local_rows_from_an_earlier_visit() {
    let mut parent_p = PrefixTree1::new();
    parent_p.insert([1]);
    let parent_q = PrefixTree1::new();
    let mut local_q = PrefixTree1::new();
    local_q.insert([2]);
    let mut p_versions = RelationVersions::new();
    let mut q_versions = RelationVersions::new();
    p_versions.publish(&parent_p);
    q_versions.publish(&local_q);
    p_versions.consume(0);
    q_versions.consume(0);

    parent_p.insert([2]);
    p_versions.publish(&parent_p);
    let p = p_versions.consume_inherited_required::<true, true>(0, &parent_p);
    let q = q_versions.consume_inherited_required::<true, true>(0, &parent_q);
    let mut matches = PrefixTree1::new();
    for row in p.new.iter().filter(|&row| local_q.contains(row)) {
        matches.insert(row);
    }
    for row in q.new.iter().filter(|&row| p.old.contains(row)) {
        matches.insert(row);
    }
    assert_eq!(matches.iter().collect::<Vec<_>>(), vec![[2]]);
    assert!(p.new.is_empty());
    assert_eq!(q.new.iter().collect::<Vec<_>>(), vec![[2]]);
}

#[test]
fn inherited_quotient_replacements_remain_new_after_prior_consumption() {
    let mut baseline = PrefixTree2::new();
    baseline.insert([0, 1]);
    baseline.insert([2, 3]);
    let mut rows = baseline.clone();
    rows.remove([0, 1]);
    rows.insert([0, 0]);
    let mut versions = RelationVersions::new();
    versions.publish(&rows);
    versions.consume(0);
    versions.consume(1);

    let filtered = versions.consume_inherited_required::<true, true>(0, &baseline);
    let membership = versions.consume_inherited_membership::<true, true>(1, &baseline);
    assert_eq!(filtered.old.iter().collect::<Vec<_>>(), vec![[2, 3]]);
    assert_eq!(filtered.new.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert!(SnapshotSet::shares_root(&membership.old, &baseline));
    assert_eq!(membership.new.iter().collect::<Vec<_>>(), vec![[0, 0]]);
    assert_eq!(baseline.iter().collect::<Vec<_>>(), vec![[0, 1], [2, 3]]);
    for consumer in 0..2 {
        let temporal = versions.consume(consumer);
        assert!(temporal.new.is_empty());
        assert!(SnapshotSet::shares_root(&temporal.old, &rows));
    }
}

#[test]
fn sibling_resets_use_their_own_baselines_and_preserve_lagging_consumers() {
    let mut first_baseline = PrefixTree1::new();
    first_baseline.insert([0]);
    let mut second_baseline = PrefixTree1::new();
    second_baseline.insert([1]);
    let mut rows = first_baseline.clone();
    rows.insert([1]);
    let mut versions = RelationVersions::new();
    versions.publish(&rows);
    for consumer in 0..3 {
        versions.consume(consumer);
    }
    rows.insert([2]);
    versions.publish(&rows);

    let first = versions.consume_inherited_required::<true, true>(0, &first_baseline);
    let second = versions.consume_inherited_required::<true, true>(1, &second_baseline);
    assert_eq!(first.old.iter().collect::<Vec<_>>(), vec![[0]]);
    assert_eq!(first.new.iter().collect::<Vec<_>>(), vec![[1], [2]]);
    assert_eq!(second.old.iter().collect::<Vec<_>>(), vec![[1]]);
    assert_eq!(second.new.iter().collect::<Vec<_>>(), vec![[0], [2]]);

    rows.insert([3]);
    versions.publish(&rows);
    for consumer in 0..2 {
        let temporal = versions.consume(consumer);
        assert_eq!(temporal.new.iter().collect::<Vec<_>>(), vec![[3]]);
    }
    let lagging = versions.consume(2);
    assert_eq!(lagging.old.iter().collect::<Vec<_>>(), vec![[0], [1]]);
    assert_eq!(lagging.new.iter().collect::<Vec<_>>(), vec![[2], [3]]);
}
