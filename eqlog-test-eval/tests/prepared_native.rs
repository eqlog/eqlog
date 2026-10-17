#![cfg(not(feature = "desugared"))]

use eqlog_runtime::__private::SnapshotSet;
use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/prepared_native.eql.rs"
));

#[test]
fn prepared_secondary_indices_share_inherited_subtrees_after_updates() {
    let mut model = PreparedNative::new();
    let source = model.new_container();
    let target = model.new_container();
    let morphism = model.new_container_mor();
    model.insert_container_mor_dom(morphism, source);
    model.insert_container_mor_cod(morphism, target);
    let a = model.new_atom();
    let b = model.new_atom();
    model.insert_pair(source, a, b);
    model.insert_forwards(target, a);
    model.insert_backwards(target, b);
    model.close();
    assert!(model.forward_result(target, b));
    assert!(model.backward_result(target, a));
    let before = model.__native_input_0.consume(usize::MAX).new;
    assert!(SnapshotSet::shares_root(
        before.get(source.0).unwrap(),
        before.get(target.0).unwrap()
    ));

    let c = model.new_atom();
    model.insert_pair(source, a, c);
    model.insert_backwards(target, c);
    model.close();
    assert!(model.forward_result(target, c));
    let after = model.__native_input_0.consume(usize::MAX - 1).new;
    assert!(SnapshotSet::shares_root(
        after.get(source.0).unwrap(),
        after.get(target.0).unwrap()
    ));
    assert_eq!(before.iter().count(), 2);
    assert_eq!(after.iter().count(), 4);
    model.close();
    let unchanged = model.__native_input_0.consume(usize::MAX - 2).new;
    assert!(SnapshotSet::shares_root(&after, &unchanged));
    let lagging = model.__native_input_0.consume(usize::MAX);
    assert!(SnapshotSet::shares_root(&before, &lagging.old));
    assert_eq!(lagging.new.iter().count(), 2);
}

#[test]
fn new_graph_edges_reactivate_consumers_and_cycles_keep_owned_support() {
    let mut model = PreparedNative::new();
    let source = model.new_container();
    let target = model.new_container();
    let a = model.new_atom();
    let b = model.new_atom();
    model.insert_pair(source, a, b);
    model.insert_backwards(target, b);
    model.close();
    assert!(!model.backward_result(target, a));

    let forward = model.new_container_mor();
    model.insert_container_mor_dom(forward, source);
    model.insert_container_mor_cod(forward, target);
    model.close();
    assert!(model.backward_result(target, a));
    let backward = model.new_container_mor();
    model.insert_container_mor_dom(backward, target);
    model.insert_container_mor_cod(backward, source);
    model.close();
    assert!(model.backward_result(target, a));

    let c = model.new_atom();
    model.equate_atom(b, c);
    model.close();
    assert!(model.pair(source, a, c));
    assert!(model.pair(target, a, c));
    model.close();
    assert!(model.pair(source, a, c));
}

#[test]
fn closing_refreshes_member_relations_without_rule_consumers() {
    let mut model = PreparedNative::new();
    let source = model.new_unused();
    let target = model.new_unused();
    let morphism = model.new_unused_mor();
    model.insert_unused_mor_dom(morphism, source);
    model.insert_unused_mor_cod(morphism, target);
    let a = model.new_atom();
    model.insert_spare(source, a);
    assert!(model.close_until(|model| model.spare(target, a)));

    let b = model.new_atom();
    model.insert_spare(source, b);
    model.close();
    assert!(model.spare(target, b));
}

#[test]
fn unrelated_equality_keeps_inherited_relation_snapshots() {
    let mut model = PreparedNative::new();
    let source = model.new_container();
    let target = model.new_container();
    let morphism = model.new_container_mor();
    model.insert_container_mor_dom(morphism, source);
    model.insert_container_mor_cod(morphism, target);
    let a = model.new_atom();
    let b = model.new_atom();
    model.insert_pair(source, a, b);
    model.close();
    let before = model.pair_order_0_1_2_all.clone();

    let x = model.new_atom();
    let y = model.new_atom();
    model.equate_atom(x, y);
    model.__canonicalize_relations();
    assert!(SnapshotSet::shares_root(
        &before,
        &model.pair_order_0_1_2_all
    ));
    assert!(model.pair(target, a, b));
    model.close();
    assert!(model.pair(target, a, b));
}

#[test]
fn inherited_rows_survive_simultaneous_column_and_owner_merges() {
    let mut model = PreparedNative::new();
    let source = model.new_container();
    let target = model.new_container();
    let morphism = model.new_container_mor();
    model.insert_container_mor_dom(morphism, source);
    model.insert_container_mor_cod(morphism, target);
    let a = model.new_atom();
    let b = model.new_atom();
    for (x, y) in [(a, b), (b, a), (a, a)] {
        model.insert_pair(source, x, y);
    }
    model.insert_backwards(target, b);
    model.close();
    assert_eq!(model.iter_pair().count(), 6);

    model.equate_atom(a, b);
    model.equate_container(source, target);
    for _ in 0..2 {
        model.canonicalize();
        assert_eq!(model.iter_pair().count(), 1);
        assert!(model.pair(target, a, b));
    }
    assert!(model.close_until(|model| model.backward_result(target, a)));
    model.close();
    assert_eq!(model.iter_pair().count(), 1);
    assert!(model.backward_result(target, b));
}

#[test]
fn equality_preserves_shared_inherited_suffixes() {
    let mut model = PreparedNative::new();
    let source = model.new_container();
    let targets: Vec<_> = (0..8).map(|_| model.new_container()).collect();
    for &target in &targets {
        let morphism = model.new_container_mor();
        model.insert_container_mor_dom(morphism, source);
        model.insert_container_mor_cod(morphism, target);
    }
    let a = model.new_atom();
    let b = model.new_atom();
    let keys: Vec<_> = (0..32).map(|_| model.new_atom()).collect();
    for &key in &keys {
        model.insert_pair(source, key, a);
        model.insert_pair(source, key, b);
    }
    model.close();
    let before = model.pair_order_0_1_2_all.get(source.0).unwrap();
    for &target in &targets {
        assert!(SnapshotSet::shares_root(
            before,
            model.pair_order_0_1_2_all.get(target.0).unwrap()
        ));
    }

    for _ in 0..8 {
        let x = model.new_atom();
        let y = model.new_atom();
        model.equate_atom(x, y);
    }
    model.equate_atom(a, b);
    model.__canonicalize_relations();
    let after = model.pair_order_0_1_2_all.get(source.0).unwrap();
    assert_eq!(after.iter().count(), keys.len());
    for &target in &targets {
        assert!(SnapshotSet::shares_root(
            after,
            model.pair_order_0_1_2_all.get(target.0).unwrap()
        ));
        assert!(model.pair(target, keys[0], b));
    }
    model.close();
    assert_eq!(model.iter_pair().count(), keys.len() * (targets.len() + 1));
}
