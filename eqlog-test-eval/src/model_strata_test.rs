use crate::model_strata::ModelStrata;

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
