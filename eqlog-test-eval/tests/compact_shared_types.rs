#![cfg(not(feature = "desugared"))]

use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_shared_types.eql.rs"
    ));
}

use generated::{CompactSharedTypes, World, WorldMor};

fn inherit(model: &mut CompactSharedTypes, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn incoming_images_require_proofs_for_every_member_type() {
    for witness_second in [false, true] {
        let mut model = CompactSharedTypes::new();
        model.enable_compact_world();
        let source = model.new_world();
        let left = model.new_world();
        let right = model.new_world();
        let target = model.new_world();
        let key = model.new_key();
        let first = model.new_first(source);
        let second = model.new_second(source);
        model.insert_named_first(source, key, first);
        if witness_second {
            model.insert_named_second(source, key, second);
        }
        let source_left = inherit(&mut model, source, left);
        let source_right = inherit(&mut model, source, right);
        let first_left = model.first_mor_app(source_left, first).unwrap();
        let second_left = model.second_mor_app(source_left, second).unwrap();
        let first_right = model.first_mor_app(source_right, first).unwrap();
        let second_right = model.second_mor_app(source_right, second).unwrap();
        model.insert_left(left, first_left, second_left);
        model.insert_right(right, first_right, second_right);
        let left_target = inherit(&mut model, left, target);
        let right_target = inherit(&mut model, right, target);
        assert_eq!(model.first_mor_app(right_target, first_right), None);
        assert_eq!(model.second_mor_app(right_target, second_right), None);
        model.close();
        let first_target = model.first_mor_app(left_target, first_left).unwrap();
        let second_target = model.second_mor_app(left_target, second_left).unwrap();
        let other_first = model.first_mor_app(right_target, first_right).unwrap();
        let other_second = model.second_mor_app(right_target, second_right).unwrap();
        assert!(model.are_equal_first(first_target, other_first));
        assert_eq!(
            model.are_equal_second(second_target, other_second),
            witness_second
        );
        assert!(model.left(target, first_target, second_target));
        assert!(model.right(target, other_first, other_second));
        assert_eq!(
            model.joined(target, first_target, second_target),
            witness_second
        );
        assert_eq!(
            model.joined(target, other_first, other_second),
            witness_second
        );
        assert!(!model.joined(left, first_left, second_left));
        assert!(!model.joined(right, first_right, second_right));
    }
}

#[test]
fn mixed_member_sizes_preserve_one_coherent_incoming_join() {
    let mut model = CompactSharedTypes::new();
    model.enable_compact_world();
    let [source, primary, secondary, target] = std::array::from_fn(|_| model.new_world());
    let key = model.new_key();
    let first = model.new_first(source);
    let second = model.new_second(source);
    model.insert_named_first(source, key, first);
    model.insert_named_second(source, key, second);
    let to_primary = inherit(&mut model, source, primary);
    let to_secondary = inherit(&mut model, source, secondary);
    let primary_first = model.first_mor_app(to_primary, first).unwrap();
    let primary_second = model.second_mor_app(to_primary, second).unwrap();
    let secondary_first = model.first_mor_app(to_secondary, first).unwrap();
    let secondary_second = model.second_mor_app(to_secondary, second).unwrap();
    model.insert_left(primary, primary_first, primary_second);
    model.insert_right(secondary, secondary_first, secondary_second);
    for _ in 0..8 {
        let key = model.new_key();
        let extra = model.new_first(primary);
        model.insert_named_first(primary, key, extra);
        model.insert_left(primary, extra, primary_second);
    }
    for _ in 0..12 {
        let key = model.new_key();
        let extra = model.new_second(secondary);
        model.insert_named_second(secondary, key, extra);
        model.insert_right(secondary, secondary_first, extra);
    }
    model.close();

    let from_primary = inherit(&mut model, primary, target);
    let target_first = model.first_mor_app(from_primary, primary_first).unwrap();
    let target_second = model.second_mor_app(from_primary, primary_second).unwrap();
    let from_secondary = inherit(&mut model, secondary, target);
    model.close();
    let other_first = model
        .first_mor_app(from_secondary, secondary_first)
        .unwrap();
    let other_second = model
        .second_mor_app(from_secondary, secondary_second)
        .unwrap();
    assert!(model.are_equal_first(target_first, other_first));
    assert!(model.are_equal_second(target_second, other_second));
    assert!(model.joined(target, target_first, target_second));
    assert!(!model.joined(primary, primary_first, primary_second));
    assert!(!model.joined(secondary, secondary_first, secondary_second));
    assert_eq!(model.iter_joined().count(), 1);

    let bare_first = model.new_first(secondary);
    model.close();
    let image_first = model.first_mor_app(from_secondary, bare_first).unwrap();
    assert!(model.world_member_first(target, image_first));
    assert!(!model.joined(target, image_first, target_second));
    let bare_second = model.new_second(secondary);
    model.close();
    let image_second = model.second_mor_app(from_secondary, bare_second).unwrap();
    assert!(model.world_member_second(target, image_second));
    assert!(!model.joined(target, target_first, image_second));
    assert_eq!(model.iter_joined().count(), 1);
    assert_eq!(
        model.first_mor_app(from_primary, primary_first),
        Some(target_first)
    );
    assert_eq!(
        model.second_mor_app(from_primary, primary_second),
        Some(target_second)
    );
}

#[test]
fn interrupted_target_closure_resumes_descendant_matches() {
    let mut model = CompactSharedTypes::new();
    model.enable_compact_world();
    let [source, left, right, target, child] = std::array::from_fn(|_| model.new_world());
    let key = model.new_key();
    let first = model.new_first(source);
    let second = model.new_second(source);
    let extra_key = model.new_key();
    let extra_first = model.new_first(source);
    model.insert_named_first(source, key, first);
    model.insert_named_first(source, extra_key, extra_first);
    model.insert_named_second(source, key, second);
    let source_left = inherit(&mut model, source, left);
    let source_right = inherit(&mut model, source, right);
    let first_left = model.first_mor_app(source_left, first).unwrap();
    let extra_left = model.first_mor_app(source_left, extra_first).unwrap();
    let second_left = model.second_mor_app(source_left, second).unwrap();
    let first_right = model.first_mor_app(source_right, first).unwrap();
    let extra_right = model.first_mor_app(source_right, extra_first).unwrap();
    let second_right = model.second_mor_app(source_right, second).unwrap();
    let right_target = inherit(&mut model, right, target);
    let left_target = inherit(&mut model, left, target);
    let target_child = inherit(&mut model, target, child);
    let target_first = model.first_mor_app(right_target, first_right).unwrap();
    let target_extra = model.first_mor_app(right_target, extra_right).unwrap();
    let target_second = model.second_mor_app(right_target, second_right).unwrap();
    let child_first = model.first_mor_app(target_child, target_first).unwrap();
    let child_extra = model.first_mor_app(target_child, target_extra).unwrap();
    let child_second = model.second_mor_app(target_child, target_second).unwrap();
    assert_eq!(model.first_mor_app(left_target, first_left), None);
    model.insert_left(left, first_left, second_left);
    model.insert_left(left, extra_left, second_left);
    model.insert_right(right, first_right, second_right);
    model.insert_right(child, child_extra, child_second);

    assert!(model.close_until(|model| {
        model.joined(target, target_first, target_second)
            && !model.joined(child, child_extra, child_second)
    }));
    assert!(model.are_equal_first(
        target_first,
        model.first_mor_app(left_target, first_left).unwrap()
    ));
    assert!(model.are_equal_second(
        target_second,
        model.second_mor_app(left_target, second_left).unwrap()
    ));
    model.close();
    assert!(model.joined(child, child_first, child_second));
    assert!(model.joined(child, child_extra, child_second));
    assert_eq!(
        model.first_mor_app(right_target, first_right),
        Some(target_first)
    );
    assert_eq!(
        model.second_mor_app(right_target, second_right),
        Some(target_second)
    );
    assert!(!model.joined(left, first_left, second_left));
    assert!(!model.joined(right, first_right, second_right));
    model.close();
    assert!(model.joined(child, child_first, child_second));
}

#[test]
fn materialization_keeps_deferred_edges_from_earlier_sources() {
    let mut model = CompactSharedTypes::new();
    model.enable_compact_world();
    let [source, left, right, target, child] = std::array::from_fn(|_| model.new_world());
    let key = model.new_key();
    let first = model.new_first(source);
    let second = model.new_second(source);
    model.insert_named_first(source, key, first);
    let source_left = inherit(&mut model, source, left);
    let source_right = inherit(&mut model, source, right);
    let first_left = model.first_mor_app(source_left, first).unwrap();
    let second_left = model.second_mor_app(source_left, second).unwrap();
    let first_right = model.first_mor_app(source_right, first).unwrap();
    let second_right = model.second_mor_app(source_right, second).unwrap();
    model.insert_left(left, first_left, second_left);
    model.insert_right(right, first_right, second_right);
    let left_target = inherit(&mut model, left, target);
    let right_target = inherit(&mut model, right, target);
    let target_child = inherit(&mut model, target, child);
    let left_child = inherit(&mut model, left, child);
    let target_second = model.second_mor_app(left_target, second_left).unwrap();
    assert!(model.second_mor_app(target_child, target_second).is_some());
    assert_eq!(model.second_mor_app(left_child, second_left), None);

    model.close();
    let direct_first = model.first_mor_app(left_child, first_left).unwrap();
    let direct_second = model.second_mor_app(left_child, second_left).unwrap();
    assert!(model.left(child, direct_first, direct_second));
    let target_first = model.first_mor_app(right_target, first_right).unwrap();
    let target_second = model.second_mor_app(right_target, second_right).unwrap();
    let child_first = model.first_mor_app(target_child, target_first).unwrap();
    let child_second = model.second_mor_app(target_child, target_second).unwrap();
    assert!(model.right(child, child_first, child_second));
    assert!(model.are_equal_first(direct_first, child_first));
    assert!(!model.are_equal_second(direct_second, child_second));
}

#[test]
fn failed_second_member_proof_replays_every_incoming_edge() {
    let mut model = CompactSharedTypes::new();
    model.enable_compact_world();
    let [source, left, right, independent, target] = std::array::from_fn(|_| model.new_world());
    let key = model.new_key();
    let first = model.new_first(source);
    let second = model.new_second(source);
    model.insert_named_first(source, key, first);
    let other_first = model.new_first(independent);
    let other_second = model.new_second(independent);
    model.insert_named_first(independent, key, other_first);
    model.insert_left(independent, other_first, other_second);
    let source_left = inherit(&mut model, source, left);
    let source_right = inherit(&mut model, source, right);
    let left_first = model.first_mor_app(source_left, first).unwrap();
    let left_second = model.second_mor_app(source_left, second).unwrap();
    let right_first = model.first_mor_app(source_right, first).unwrap();
    let right_second = model.second_mor_app(source_right, second).unwrap();
    model.insert_left(left, left_first, left_second);
    model.insert_right(right, right_first, right_second);
    let left_target = inherit(&mut model, left, target);
    let right_target = inherit(&mut model, right, target);
    let other_target = inherit(&mut model, independent, target);
    let initial_first = model.first_mor_app(left_target, left_first).unwrap();
    let initial_second = model.second_mor_app(left_target, left_second).unwrap();
    assert_eq!(model.second_mor_app(right_target, right_second), None);
    assert_eq!(model.second_mor_app(other_target, other_second), None);
    model.close();
    let firsts = [
        model.first_mor_app(left_target, left_first).unwrap(),
        model.first_mor_app(right_target, right_first).unwrap(),
        model.first_mor_app(other_target, other_first).unwrap(),
    ];
    let seconds = [
        model.second_mor_app(left_target, left_second).unwrap(),
        model.second_mor_app(right_target, right_second).unwrap(),
        model.second_mor_app(other_target, other_second).unwrap(),
    ];
    assert!(model.are_equal_first(initial_first, firsts[0]));
    assert!(model.are_equal_second(initial_second, seconds[0]));
    assert!(model.left(target, firsts[0], seconds[0]));
    assert!(model.right(target, firsts[1], seconds[1]));
    assert!(model.left(target, firsts[2], seconds[2]));
    for first in firsts {
        assert!(model.are_equal_first(firsts[0], first));
    }
    for left in 0..seconds.len() {
        assert!(!model.joined(target, firsts[0], seconds[left]));
        for right in left + 1..seconds.len() {
            assert!(!model.are_equal_second(seconds[left], seconds[right]));
        }
    }
    assert_eq!(model.iter_first().count(), 5);
    assert_eq!(model.iter_second().count(), 7);
}
