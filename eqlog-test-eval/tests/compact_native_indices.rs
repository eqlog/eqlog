#![cfg(not(feature = "desugared"))]

use eqlog_runtime::__private::SnapshotSet;
use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/compact_native_indices.eql.rs"
));

fn origin(model: &CompactNativeIndices, owner: World, member: El) -> u32 {
    model.__compact_el_origin(owner.0, model.root_el(member))
}

fn image(model: &CompactNativeIndices, member: El, owner: World) -> El {
    El(model
        .__compact_members_el
        .as_ref()
        .unwrap()
        .image(member.0, owner.0)
        .unwrap())
}

fn inherit(model: &mut CompactNativeIndices, source: World, target: World) {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.__compact_inherit_world(source.0, target.0);
    model.__total_members_world.insert(morphism.0);
}

#[test]
fn unrelated_local_facts_keep_published_relation_roots() {
    let mut model = CompactNativeIndices::new();
    let world = model.new_world();
    let element = model.new_el(world);
    let tag = model.new_tag();
    model.insert_item(world, tag, element);
    model.insert_marked(world, element);
    model.__enable_compact_world_indices();
    let before = model.marked_order_0_1_all.clone();
    let other = model.new_tag();
    model.insert_item(world, other, element);
    assert!(SnapshotSet::shares_root(
        &before,
        &model.marked_order_0_1_all
    ));
}

#[test]
fn scoped_rules_use_shared_origin_indexes_after_local_and_source_changes() {
    let mut model = CompactNativeIndices::new();
    let source = model.new_world();
    let target = model.new_world();
    let destination = model.new_world();
    let first = model.new_el(source);
    let second = model.new_el(source);
    let tag = model.new_tag();
    model.insert_edge(source, first, second);
    model.insert_marked(source, first);
    model.insert_item(source, tag, second);
    model.__enable_compact_world_indices();
    inherit(&mut model, source, target);
    inherit(&mut model, target, destination);
    model.close();
    for owner in [source, target, destination] {
        assert_eq!(
            model
                .__compact_primary_marked(owner.0)
                .unwrap()
                .iter()
                .count(),
            2
        );
        assert_eq!(
            model
                .__compact_primary_scanned(owner.0)
                .unwrap()
                .iter()
                .count(),
            2
        );
        assert!(model
            .__compact_primary_seen(owner.0)
            .unwrap()
            .contains(&[tag.0]));
    }
    let target_first = image(&model, first, target);
    let target_second = image(&model, second, target);
    let before = model
        .__compact_indices_world
        .as_ref()
        .unwrap()
        .snapshot(target.0);
    let local = model.new_el(target);
    model.insert_edge(target, target_second, local);
    model.equate_el(target, target_first, target_second);
    model.close();
    assert!(!model.are_equal_el(first, second));
    assert!(model.are_equal_el(target_first, target_second));
    let local_origin = origin(&model, target, local);
    assert!(model
        .__compact_primary_marked(target.0)
        .unwrap()
        .contains(&[local_origin]));
    assert!(
        before.revision()
            < model
                .__compact_indices_world
                .as_ref()
                .unwrap()
                .revision(target.0)
    );

    // Parent rows can change without a member-partition revision. The local
    // quotient must still be replayed when its inherited index is replaced.
    let late_tag = model.new_tag();
    model.insert_item(source, late_tag, first);
    model.close();
    for owner in [target, destination] {
        let local_root = if owner == target {
            local
        } else {
            image(&model, local, destination)
        };
        assert!(model
            .__compact_primary_marked(owner.0)
            .unwrap()
            .contains(&[origin(&model, owner, local_root)]));
        assert!(model
            .__compact_primary_seen(owner.0)
            .unwrap()
            .contains(&[late_tag.0]));
    }

    let late = model.new_el(source);
    model.insert_edge(source, second, late);
    model.close();
    let target_late = image(&model, late, target);
    let destination_late = image(&model, target_late, destination);
    for (owner, member) in [
        (source, late),
        (target, target_late),
        (destination, destination_late),
    ] {
        let origin = origin(&model, owner, member);
        assert!(model
            .__compact_primary_marked(owner.0)
            .unwrap()
            .contains(&[origin]));
        assert!(model
            .__compact_primary_scanned(owner.0)
            .unwrap()
            .contains(&[origin]));
    }
}
