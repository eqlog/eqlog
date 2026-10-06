use crate::model_strata::{ModelStrata, World};

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
fn ambient_feedback_keeps_its_dependency_order() {
    let mut m = ModelStrata::new();
    let a = m.new_fallback();
    let x = m.new_atom();
    m.insert_initial(a, x);
    m.close();
    assert!(m.completed(a, x));
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
