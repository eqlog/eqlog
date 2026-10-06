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
