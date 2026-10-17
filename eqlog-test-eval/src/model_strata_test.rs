use crate::model_strata::{ModelStrata, World};
#[cfg(all(not(feature = "simultaneous"), not(feature = "desugared")))]
use std::cell::Cell;

fn morphism(m: &mut ModelStrata, a: World, b: World) {
    let f = m.new_world_mor();
    m.insert_world_mor_dom(f, a);
    m.insert_world_mor_cod(f, b);
}

#[test]
fn bound_rules_keep_model_inputs_separate() {
    let mut m = ModelStrata::new();
    let a = m.new_world();
    let b = m.new_world();
    let x = m.new_atom();
    let y = m.new_atom();
    m.insert_seed(a, x);
    m.insert_edge(a, x, y);
    m.close();
    assert!(m.marked(a, y));
    assert!(!m.marked(b, x));
    m.insert_enabled(x);
    m.close();
    assert!(m.marked(b, x));
    assert!(!m.marked(b, y));
    m.insert_edge(b, x, y);
    m.close();
    assert!(m.marked(b, y));
}

#[test]
fn external_rules_respect_receivers_and_cross_owner_inputs() {
    let mut m = ModelStrata::new();
    let a = m.new_scoped();
    let b = m.new_scoped();
    let x = m.new_atom();
    let y = m.new_atom();
    m.insert_owned_seed(a, x);
    m.insert_owned_seed(b, y);
    m.insert_cross_seed(a, x);
    m.insert_scope_input(x);
    m.insert_export_seed(b, y);
    m.close();
    assert!(m.owned_result(a, x));
    assert!(m.owned_result(b, y));
    assert!(!m.owned_result(a, y));
    assert!(!m.owned_result(b, x));
    for owner in [a, b] {
        assert!(m.cross_result(owner, x));
        assert!(!m.cross_result(owner, y));
        assert!(m.ambient_result(owner, x));
        assert!(!m.ambient_result(owner, y));
    }
    assert!(m.scope_output(b, y));
    assert!(!m.scope_output(a, y));

    m.insert_cross_seed(b, y);
    m.insert_scope_input(y);
    m.insert_export_seed(a, x);
    m.close();
    for owner in [a, b] {
        assert!(m.cross_result(owner, y));
        assert!(m.ambient_result(owner, y));
    }
    assert!(m.scope_output(a, x));
    assert!(!m.scope_output(b, x));
    assert!(!m.owned_result(a, y));
    assert!(!m.owned_result(b, x));
}

#[test]
fn new_models_and_late_ambient_inputs_have_independent_checkpoints() {
    let mut m = ModelStrata::new();
    let a = m.new_world();
    m.close();
    assert!(m.born(a));
    let x = m.new_atom();
    m.insert_enabled(x);
    m.close();
    let b = m.new_world();
    m.close();
    assert!(m.born(b));
    assert!(m.marked(b, x));
    let y = m.new_atom();
    m.insert_seed(a, y);
    assert!(m.close_until(|m| m.marked(a, y)));
    m.insert_seed(b, y);
    m.close();
    assert!(m.marked(b, y));
}

#[test]
fn component_closure_combines_local_rules_and_internal_transport() {
    let mut m = ModelStrata::new();
    let a = m.new_world();
    let b = m.new_world();
    let c = m.new_world();
    let d = m.new_world();
    morphism(&mut m, a, b);
    morphism(&mut m, b, c);
    morphism(&mut m, c, b);
    morphism(&mut m, c, d);
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_seed(a, x);
    m.insert_unlock(c, x, y);
    m.insert_unlock(b, y, z);
    m.close();
    assert!(m.marked(d, z));
    assert!(m.marked(c, z));
    assert!(!m.marked(a, y));
    m.close();
    assert!(m.marked(b, z));
}

#[test]
fn secondary_indices_transport_new_owned_rows_between_components() {
    let mut m = ModelStrata::new();
    let a = m.new_world();
    let b = m.new_world();
    morphism(&mut m, a, b);
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_edge(a, x, y);
    m.insert_query(b, y);
    m.close();
    assert!(m.marked(b, x));
    assert!(!m.marked(a, x));
    m.insert_edge(a, z, y);
    m.close();
    assert!(m.marked(b, z));
    assert!(!m.marked(a, z));
}

#[test]
fn allocation_and_late_edges_rebuild_model_components() {
    let mut m = ModelStrata::new();
    let a = m.new_world();
    let b = m.new_world();
    let x = m.new_atom();
    let y = m.new_atom();
    m.insert_seed(a, x);
    m.insert_unlock(b, x, y);
    m.close();
    assert!(!m.marked(b, x));
    m.insert_requested_edge(a, b);
    m.close();
    assert!(m.marked(b, y));
    assert!(!m.marked(a, y));
    m.insert_requested_edge(b, a);
    m.close();
    assert!(m.marked(a, y));
}

#[test]
fn merging_models_replays_the_combined_inputs() {
    let mut m = ModelStrata::new();
    let a = m.new_world();
    let b = m.new_world();
    let x = m.new_atom();
    let y = m.new_atom();
    m.insert_seed(a, x);
    m.insert_edge(b, x, y);
    m.close();
    assert!(!m.marked(a, y));
    assert!(!m.marked(b, y));
    m.equate_world(a, b);
    m.close();
    assert!(m.marked(a, y));
    m.close();
    assert!(m.marked(b, y));
}

#[test]
fn merging_nested_owners_replays_the_combined_inputs() {
    let mut m = ModelStrata::new();
    let a = m.new_nest();
    let b = m.new_nest();
    let a0 = m.new_child(a);
    let b0 = m.new_child(b);
    let x = m.new_atom();
    let y = m.new_atom();
    m.insert_child_seed(a, a0, x);
    m.insert_child_unlock(b, b0, x, y);
    m.close();
    assert!(!m.child_reached(b, b0, y));
    m.equate_nest(a, b);
    m.close();
    assert!(!m.child_reached(a, a0, y));
    m.equate_child(a, a0, b0);
    m.close();
    assert!(m.child_reached(a, a0, y));
    assert!(m.child_reached(b, b0, y));
}

#[test]
fn sparse_updates_reach_old_empty_models_after_transport_and_merges() {
    let mut m = ModelStrata::new();
    let worlds: Vec<_> = (0..128).map(|_| m.new_world()).collect();
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_seed(worlds[0], x);
    m.insert_edge(worlds[1], x, y);
    m.insert_edge(worlds[2], y, z);
    m.close();
    for &world in &worlds {
        assert!(m.born(world));
        assert!(!m.marked(world, y));
    }

    morphism(&mut m, worlds[0], worlds[1]);
    m.close();
    assert!(m.marked(worlds[1], y));
    assert!(!m.marked(worlds[2], z));
    m.equate_world(worlds[1], worlds[2]);
    m.close();
    assert!(m.marked(worlds[1], z));
    assert!(m.marked(worlds[2], z));

    m.insert_seed(worlds[127], y);
    m.insert_edge(worlds[127], y, z);
    m.close();
    assert!(m.marked(worlds[127], z));
    for &world in &worlds[3..127] {
        assert!(!m.marked(world, x));
        assert!(!m.marked(world, y));
        assert!(!m.marked(world, z));
    }
}

#[test]
fn a_recursive_owner_can_advance_while_another_rule_has_an_empty_input() {
    let mut m = ModelStrata::new();
    let owner = m.new_choice();
    let empty_owner = m.new_choice();
    let a = m.new_atom();
    let b = m.new_atom();
    let c = m.new_atom();
    let d = m.new_atom();
    m.insert_east(owner, a);
    m.insert_east_edge(owner, a, b);
    m.insert_east_edge(owner, c, d);
    m.close();
    assert!(m.west(owner, b));
    assert!(!m.east(owner, c));
    assert!(!m.west(owner, d));

    m.insert_west_edge(owner, b, c);
    m.close();
    assert!(m.east(owner, c));
    assert!(m.west(owner, d));
    for atom in [a, b, c, d] {
        assert!(!m.east(empty_owner, atom));
        assert!(!m.west(empty_owner, atom));
    }
}

#[cfg(all(not(feature = "simultaneous"), not(feature = "desugared")))]
#[test]
fn merging_two_owners_does_not_replay_unrelated_owners() {
    let mut checks = Vec::new();
    for count in [2, 128] {
        let mut m = ModelStrata::new();
        let worlds: Vec<_> = (0..count).map(|_| m.new_world()).collect();
        let parent = m.new_nest();
        let child = m.new_child(parent);
        let x = m.new_atom();
        let y = m.new_atom();
        m.insert_seed(worlds[0], x);
        m.insert_edge(worlds[1], x, y);
        m.insert_child_seed(parent, child, x);
        m.close();
        m.equate_world(worlds[0], worlds[1]);
        let observed = Cell::new(0);
        assert!(!m.close_until(|_| {
            observed.set(observed.get() + 1);
            false
        }));
        assert!(m.marked(worlds[0], y));
        assert!(m.child_reached(parent, child, x));
        for &world in &worlds[2..] {
            assert!(m.born(world));
            assert!(!m.marked(world, y));
        }
        checks.push(observed.get());
    }
    assert_eq!(checks[0], checks[1]);
}

#[test]
fn rules_crossing_ambient_and_model_scopes_keep_their_dependency_order() {
    let mut m = ModelStrata::new();
    let a = m.new_fallback();
    let x = m.new_atom();
    m.insert_initial(a, x);
    m.close();
    assert!(m.completed(a, x));
}

#[test]
fn ambient_and_member_rules_close_a_feedback_cycle() {
    let mut m = ModelStrata::new();
    let f = m.new_feedback();
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_feedback_seed(f, x);
    m.insert_feedback_next(f, x, y);
    m.insert_feedback_next(f, y, z);
    m.close();
    assert!(m.feedback_completed(f, x));
    assert!(m.feedback_completed(f, y));
    assert!(m.feedback_completed(f, z));
}

#[test]
fn nested_rules_close_inside_an_outer_cycle() {
    let mut m = ModelStrata::new();
    let a = m.new_nest();
    let b = m.new_nest();
    let a0 = m.new_child(a);
    let a1 = m.new_child(a);
    let b0 = m.new_child(b);
    let f = m.new_nest_mor();
    m.insert_nest_mor_dom(f, a);
    m.insert_nest_mor_cod(f, b);
    m.insert_child_mor_app(f, a0, b0);
    let g = m.new_nest_mor();
    m.insert_nest_mor_dom(g, b);
    m.insert_nest_mor_cod(g, a);
    m.insert_child_mor_app(g, b0, a1);
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_child_seed(a, a0, x);
    m.insert_child_unlock(b, b0, x, y);
    m.insert_child_unlock(a, a1, y, z);
    assert!(m.close_until(|m| m.child_reached(a, a0, x)));
    for _ in 0..3 {
        m.close();
        assert!(m.child_reached(a, a1, z));
        assert!(m.child_reached(b, b0, y));
        assert!(!m.child_reached(a, a0, y));
        assert!(!m.child_reached(b, b0, z));
    }
}

#[test]
fn outer_transport_can_change_a_previously_evaluated_child_graph() {
    let mut m = ModelStrata::new();
    let a = m.new_nest();
    let b = m.new_nest();
    let a0 = m.new_child(a);
    let a1 = m.new_child(a);
    let b0 = m.new_child(b);
    let b1 = m.new_child(b);
    let f = m.new_nest_mor();
    m.insert_nest_mor_dom(f, a);
    m.insert_nest_mor_cod(f, b);
    m.insert_child_mor_app(f, a0, b0);
    m.insert_child_mor_app(f, a1, b1);
    let x = m.new_atom();
    m.insert_child_seed(b, b1, x);
    m.close();
    assert!(!m.child_reached(b, b0, x));
    for (source, target) in [(a0, a1), (a1, a0)] {
        let g = m.new_child_mor(a);
        m.insert_child_mor_dom(a, g, source);
        m.insert_child_mor_cod(a, g, target);
        let image = m.new_child_mor(b);
        m.insert_child_mor_mor_app(f, g, image);
    }
    m.close();
    assert!(m.child_reached(b, b0, x));
    assert!(!m.child_reached(a, a0, x));
}
