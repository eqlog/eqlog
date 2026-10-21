#![cfg(not(feature = "desugared"))]

use eqlog_test_eval as _;

mod generated {
    include!(concat!(
        env!("EQLOG_OUT_DIR"),
        "/eqlog-test-eval/src/compact_rule_closure.eql.rs"
    ));
}

use generated::{CompactRuleClosure, World, WorldMor};

fn inherit(model: &mut CompactRuleClosure, source: World, target: World) -> WorldMor {
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.inherit_total_world_members(morphism);
    morphism
}

#[test]
fn inherited_closure_includes_rules_and_existential_consequences() {
    for close_source_first in [false, true] {
        let mut model = CompactRuleClosure::new();
        model.enable_compact_world();
        let source = model.new_world();
        let target = model.new_world();
        let child = model.new_world();
        let first = model.new_el(source);
        let second = model.new_el(source);
        model.insert_p(source, first);
        model.insert_q(source, first);
        model.insert_link(source, first, second);
        model.insert_requested(source, second);
        if close_source_first {
            model.close();
        }
        let to_target = inherit(&mut model, source, target);
        let to_child = inherit(&mut model, target, child);
        model.close();

        let target_first = model.el_mor_app(to_target, first).unwrap();
        let target_second = model.el_mor_app(to_target, second).unwrap();
        let child_first = model.el_mor_app(to_child, target_first).unwrap();
        let child_second = model.el_mor_app(to_child, target_second).unwrap();
        let source_witness = model.witness(source, second).unwrap();
        let target_witness = model.el_mor_app(to_target, source_witness).unwrap();
        let child_witness = model.el_mor_app(to_child, target_witness).unwrap();
        assert!(model.r(source, first));
        assert!(model.r(target, target_first));
        assert!(model.r(child, child_first));
        assert!(model.visited(target, target_second));
        assert!(model.visited(child, child_second));
        assert_eq!(model.witness(target, target_second), Some(target_witness));
        assert_eq!(model.witness(child, child_second), Some(child_witness));
        assert!(model.witnessed(target, target_second, target_witness));
        assert!(model.witnessed(child, child_second, child_witness));
        assert!(!model.are_equal_el(source_witness, target_witness));
        assert!(!model.are_equal_el(target_witness, child_witness));
    }
}

#[test]
fn recursive_rules_combine_local_and_inherited_premises() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let child = model.new_world();
    let first = model.new_el(source);
    let second = model.new_el(source);
    let third = model.new_el(source);
    let fourth = model.new_el(source);
    model.insert_p(source, first);
    model.insert_link(source, first, second);
    model.insert_link(source, third, fourth);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    model.close();
    let target_first = model.el_mor_app(to_target, first).unwrap();
    let target_second = model.el_mor_app(to_target, second).unwrap();
    let target_third = model.el_mor_app(to_target, third).unwrap();
    let target_fourth = model.el_mor_app(to_target, fourth).unwrap();
    let local = model.new_el(target);
    model.insert_q(target, target_first);
    model.insert_link(target, target_second, target_third);
    model.insert_link(target, target_fourth, local);
    let to_child = inherit(&mut model, target, child);
    let child_local = model.el_mor_app(to_child, local).unwrap();
    model.close();

    assert!(model.r(target, target_first));
    assert!(model.visited(target, target_third));
    assert!(model.visited(target, target_fourth));
    assert!(model.visited(target, local));
    assert!(model.visited(child, child_local));
    assert!(!model.r(source, first));
    assert!(!model.visited(source, third));
    let sibling_first = model.el_mor_app(to_sibling, first).unwrap();
    let sibling_fourth = model.el_mor_app(to_sibling, fourth).unwrap();
    assert!(!model.r(sibling, sibling_first));
    assert!(!model.visited(sibling, sibling_fourth));
}

#[test]
fn target_equality_creates_a_join_between_inherited_rows() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let child = model.new_world();
    let left = model.new_el(source);
    let right = model.new_el(source);
    model.insert_p(source, left);
    model.insert_q(source, right);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    let to_child = inherit(&mut model, target, child);
    model.close();
    let target_left = model.el_mor_app(to_target, left).unwrap();
    let target_right = model.el_mor_app(to_target, right).unwrap();
    let sibling_left = model.el_mor_app(to_sibling, left).unwrap();
    let sibling_right = model.el_mor_app(to_sibling, right).unwrap();
    let child_left = model.el_mor_app(to_child, target_left).unwrap();
    let child_right = model.el_mor_app(to_child, target_right).unwrap();
    assert_eq!(model.iter_r().count(), 0);
    model.equate_el(target, target_left, target_right);
    model.close();

    assert!(model.r(target, target_left));
    assert!(model.r(target, target_right));
    assert!(model.r(child, child_left));
    assert!(model.r(child, child_right));
    assert_eq!(model.iter_r().count(), 2);
    assert!(!model.are_equal_el(left, right));
    assert!(!model.are_equal_el(sibling_left, sibling_right));
    assert!(!model.r(source, left));
    assert!(!model.r(sibling, sibling_left));
}

#[test]
fn member_input_equality_runs_functionality_and_new_predicate_joins() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let child = model.new_world();
    let left = model.new_el(source);
    let right = model.new_el(source);
    let left_result = model.new_el(source);
    let right_result = model.new_el(source);
    model.insert_next(source, left, left_result);
    model.insert_next(source, right, right_result);
    model.insert_p(source, left_result);
    model.insert_q(source, right_result);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let to_child = inherit(&mut model, target, child);
    model.close();
    let target_left = model.el_mor_app(to_target, left).unwrap();
    let target_right = model.el_mor_app(to_target, right).unwrap();
    let target_left_result = model.el_mor_app(to_target, left_result).unwrap();
    let target_right_result = model.el_mor_app(to_target, right_result).unwrap();
    let child_left_result = model.el_mor_app(to_child, target_left_result).unwrap();
    let child_right_result = model.el_mor_app(to_child, target_right_result).unwrap();
    assert!(!model.are_equal_el(target_left_result, target_right_result));
    model.equate_el(target, target_left, target_right);
    model.close();

    assert!(model.are_equal_el(target_left_result, target_right_result));
    assert!(model.are_equal_el(child_left_result, child_right_result));
    assert!(model.r(target, target_left_result));
    assert!(model.r(child, child_right_result));
    assert!(!model.are_equal_el(left_result, right_result));
    assert!(!model.r(source, left_result));
}

#[test]
fn late_parent_growth_and_equality_recheck_local_premises() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let child = model.new_world();
    let left = model.new_el(source);
    let right = model.new_el(source);
    let waiting = model.new_el(source);
    model.insert_p(source, left);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    let target_left = model.el_mor_app(to_target, left).unwrap();
    let target_right = model.el_mor_app(to_target, right).unwrap();
    let target_waiting = model.el_mor_app(to_target, waiting).unwrap();
    let local = model.new_el(target);
    model.insert_q(target, target_right);
    model.insert_q(target, target_waiting);
    model.insert_link(target, target_right, local);
    let to_child = inherit(&mut model, target, child);
    let child_local = model.el_mor_app(to_child, local).unwrap();
    model.close();
    assert!(!model.visited(target, local));
    assert!(!model.r(target, target_left));

    let late = model.new_el(source);
    model.insert_p(source, late);
    model.insert_p(source, right);
    model.close();
    let target_late = model.el_mor_app(to_target, late).unwrap();
    let child_late = model.el_mor_app(to_child, target_late).unwrap();
    assert!(model.visited(target, local));
    assert!(model.visited(child, child_local));
    assert!(model.visited(target, target_late));
    assert!(model.visited(child, child_late));
    assert!(model.r(target, target_right));
    assert!(!model.r(source, right));
    assert!(!model.r(target, target_left));
    assert!(!model.r(target, target_waiting));

    model.equate_el(source, left, waiting);
    model.close();
    let child_left = model.el_mor_app(to_child, target_left).unwrap();
    let sibling_left = model.el_mor_app(to_sibling, left).unwrap();
    assert!(model.are_equal_el(target_left, target_waiting));
    assert!(model.r(target, target_left));
    assert!(model.r(child, child_left));
    assert!(model.visited(target, local));
    assert!(!model.r(source, left));
    assert!(!model.r(sibling, sibling_left));
}

#[test]
fn partial_close_keeps_existential_requests_after_parent_equality() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let child = model.new_world();
    let left = model.new_el(source);
    let right = model.new_el(source);
    model.insert_p(source, left);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    let to_child = inherit(&mut model, target, child);
    model.close();
    let target_left = model.el_mor_app(to_target, left).unwrap();
    let target_right = model.el_mor_app(to_target, right).unwrap();
    let child_left = model.el_mor_app(to_child, target_left).unwrap();
    let sibling_left = model.el_mor_app(to_sibling, left).unwrap();
    model.insert_requested(target, target_left);
    assert!(model.close_until(|model| {
        model.ready(target, target_left) && model.witness(target, target_left).is_none()
    }));
    model.equate_el(source, right, left);
    model.close();

    let target_witness = model.witness(target, target_right).unwrap();
    let child_witness = model.el_mor_app(to_child, target_witness).unwrap();
    assert!(model.witnessed(target, target_left, target_witness));
    assert!(model.witnessed(child, child_left, child_witness));
    assert_eq!(model.witness(child, child_left), Some(child_witness));
    assert!(model.world_member_el(target, target_witness));
    assert!(model.world_member_el(child, child_witness));
    assert!(!model.world_member_el(source, target_witness));
    assert_eq!(model.witness(source, left), None);
    assert_eq!(model.witness(sibling, sibling_left), None);
}

#[test]
fn global_owner_premises_can_enable_only_a_target_rule() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    let child = model.new_world();
    let member = model.new_el(source);
    model.insert_p(source, member);
    model.insert_enabled(target);
    model.close();
    let to_target = inherit(&mut model, source, target);
    let to_sibling = inherit(&mut model, source, sibling);
    let to_child = inherit(&mut model, target, child);
    model.close();

    let target_member = model.el_mor_app(to_target, member).unwrap();
    let sibling_member = model.el_mor_app(to_sibling, member).unwrap();
    let child_member = model.el_mor_app(to_child, target_member).unwrap();
    assert!(model.active(target, target_member));
    assert!(model.active(child, child_member));
    assert!(!model.active(source, member));
    assert!(!model.active(sibling, sibling_member));
}

#[test]
fn inherited_owner_values_can_enable_a_target_diagonal() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    model.new_el(source);
    model.insert_peer(source, target);
    model.close();
    assert!(!model.owner_seen(source));
    inherit(&mut model, source, target);
    inherit(&mut model, source, sibling);
    model.close();

    assert!(model.peer(target, target));
    assert!(model.owner_seen(target));
    assert!(model.peer(sibling, target));
    assert!(!model.owner_seen(sibling));
    assert!(!model.owner_seen(source));
}

#[test]
fn inherited_premises_emit_the_target_owner_as_data() {
    let mut model = CompactRuleClosure::new();
    model.enable_compact_world();
    let source = model.new_world();
    let target = model.new_world();
    let sibling = model.new_world();
    model.new_el(source);
    model.insert_tick(source);
    model.close();
    assert!(model.backref(source, source));
    inherit(&mut model, source, target);
    inherit(&mut model, source, sibling);
    model.close();

    assert!(model.backref(target, source));
    assert!(model.backref(target, target));
    assert!(model.backref(sibling, source));
    assert!(model.backref(sibling, sibling));
    assert!(!model.backref(source, target));
    assert!(!model.backref(target, sibling));
    assert!(!model.backref(sibling, target));
}
