use crate::model_hierarchy::ModelHierarchy;

#[test]
fn nested_allocation_only_bodies_have_graph_support() {
    let mut m = ModelHierarchy::new();
    let p = m.new_container();
    let a = m.new_alloc_only(p);
    m.close();
    assert!(m.fresh(p, a).is_some());
    let b = m.new_alloc_only(p);
    m.close();
    assert!(m.fresh(p, b).is_some());
}

#[test]
fn parent_and_child_feedback_reaches_a_common_fixed_point() {
    let mut m = ModelHierarchy::new();
    let a = m.new_container();
    let b = m.new_container();
    let ca = m.new_child(a);
    let cb = m.new_child(b);
    let sa = m.new_sibling(a);
    let sb = m.new_sibling(b);
    for (source, target, child_source, child_target, sibling_source, sibling_target) in
        [(a, b, ca, cb, sa, sb), (b, a, cb, ca, sb, sa)]
    {
        let f = m.new_container_mor();
        m.insert_container_mor_dom(f, source);
        m.insert_container_mor_cod(f, target);
        m.insert_child_mor_app(f, child_source, child_target);
        m.insert_sibling_mor_app(f, sibling_source, sibling_target);
    }
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_start(a, x);
    m.insert_next(b, x, y);
    m.insert_next(a, y, z);
    for _ in 0..3 {
        m.close();
        assert!(m.child_done(a, ca, z));
        assert!(m.sibling_done(b, sb, z));
        assert!(m.after_sibling(a, z));
    }
}

#[test]
fn parent_reads_secondary_indices_of_new_inherited_child_facts() {
    let mut m = ModelHierarchy::new();
    let p = m.new_container();
    let a = m.new_child(p);
    let b = m.new_child(p);
    let f = m.new_child_mor(p);
    m.insert_child_mor_dom(p, f, a);
    m.insert_child_mor_cod(p, f, b);
    let x = m.new_atom();
    let y = m.new_atom();
    let z = m.new_atom();
    m.insert_child_pair(p, a, x, y);
    m.insert_ask(p, b, y);
    m.insert_ask_any(p, y);
    m.close();
    assert!(m.answer(p, x));
    assert!(m.answer_any(p, x));
    assert!(m.child_seen(p, b, x));
    m.insert_child_pair(p, a, z, y);
    m.close();
    assert!(m.answer(p, z));
    assert!(m.answer_any(p, z));
    assert!(m.child_seen(p, b, z));
}

#[test]
fn parent_reads_descendants_without_local_rule_bodies() {
    let mut m = ModelHierarchy::new();
    let p = m.new_container();
    let a = m.new_passive(p);
    let b = m.new_passive(p);
    let x = m.new_atom();
    let y = m.new_atom();
    m.insert_passive_pair(p, a, x, y);
    m.insert_passive_ask(p, b, y);
    m.close();
    assert!(!m.passive_answer(p, x));
    let f = m.new_passive_mor(p);
    m.insert_passive_mor_dom(p, f, a);
    m.insert_passive_mor_cod(p, f, b);
    m.close();
    assert!(m.passive_answer(p, x));
}

#[cfg(all(feature = "stratified", not(feature = "desugared")))]
#[test]
fn a_parent_runs_its_child_body_before_moving_to_an_unrelated_parent() {
    let mut m = ModelHierarchy::new();
    let a = m.new_container();
    let b = m.new_container();
    let ca = m.new_child(a);
    let cb = m.new_child(b);
    let x = m.new_atom();
    m.insert_start(a, x);
    m.insert_start(b, x);
    assert!(m.close_until(|m| m.child_done(a, ca, x) || m.child_done(b, cb, x)));
    assert_ne!(m.ready(a, x), m.ready(b, x));
    m.close();
    assert!(m.child_done(a, ca, x));
    assert!(m.child_done(b, cb, x));
}
