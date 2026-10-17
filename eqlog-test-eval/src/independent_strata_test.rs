use crate::independent_strata::IndependentStrata;

#[test]
fn independent_cycles_and_acyclic_rules_handle_incremental_inputs() {
    let mut m = IndependentStrata::new();
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    let d = m.new_el();
    m.insert_seed(a);
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    m.insert_backwards(c);
    m.close();
    assert!(m.result(a));
    assert!(m.reached(c));
    assert!(!m.result(c));
    assert!(!m.reached(d));
    assert!(m.backwards(a));

    m.insert_seed(c);
    m.insert_edge(c, d);
    m.insert_edge(d, a);
    m.close();
    assert!(m.result(c));
    assert!(m.reached(d));
    assert!(!m.result(d));
    assert!(m.backwards(d));
}

#[cfg(not(feature = "simultaneous"))]
#[test]
fn independent_readers_resume_without_consuming_each_others_input() {
    let mut m = IndependentStrata::new();
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    m.insert_seed(a);
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    assert!(m.close_until(|m| m.left(a) || m.right(a)));
    assert_ne!(m.left(a), m.right(a));

    assert!(m.close_until(|m| m.result(a)));
    assert!(m.reach_left(c));
    assert!(m.reach_right(c));
    assert!(m.reached(c));
    m.close();
    assert!(m.result(a));
}

#[test]
fn shared_output_only_relations_combine_both_producers() {
    let mut m = IndependentStrata::new();
    let a = m.new_el();
    let b = m.new_el();
    m.insert_seed(a);
    m.insert_alternate(b);
    m.close();
    assert!(m.out_done(a));
    assert!(m.out_done(b));
}

#[cfg(not(feature = "simultaneous"))]
#[test]
fn interrupted_recursion_reloads_changed_stable_inputs() {
    let mut m = IndependentStrata::new();
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    let d = m.new_el();
    m.insert_backwards(c);
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    assert!(m.close_until(|m| m.backwards(b)));
    assert!(!m.backwards(a));
    m.insert_edge(d, a);
    m.close();
    assert!(m.backwards(a));
    assert!(m.backwards(d));
}

#[cfg(not(feature = "simultaneous"))]
#[test]
fn consumers_wait_for_recursive_producers_to_close() {
    let mut m = IndependentStrata::new();
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    m.insert_reach_right(a);
    m.insert_reach_left(a);
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    assert!(m.close_until(|m| m.reached(a)));
    assert!(m.reach_right(c));
    assert!(m.reach_left(c));
    assert!(m.reached(c));
}

#[test]
fn stable_inherited_inputs_are_refreshed_between_loop_visits() {
    let mut m = IndependentStrata::new();
    let source = m.new_stable_box();
    let target = m.new_stable_box();
    let f = m.new_stable_box_mor();
    m.insert_stable_box_mor_dom(f, source);
    m.insert_stable_box_mor_cod(f, target);
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    let d = m.new_el();
    m.insert_link(source, a, b);
    m.insert_link(source, b, c);
    m.insert_global_reach(target, c);
    m.insert_local_reach(target, c);
    m.close();
    assert!(m.global_reach(target, a));
    assert!(m.echo(target, a));
    m.insert_link(source, d, a);
    m.close();
    assert!(m.global_reach(target, d));
    assert!(m.echo(target, d));
}

#[test]
fn parent_rules_read_inherited_child_relations_in_both_directions() {
    let mut m = IndependentStrata::new();
    let p = m.new_stable_box();
    let source = m.new_detail(p);
    let target = m.new_detail(p);
    let f = m.new_detail_mor(p);
    m.insert_detail_mor_dom(p, f, source);
    m.insert_detail_mor_cod(p, f, target);
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    let d = m.new_el();
    let e = m.new_el();
    m.insert_detail_link(p, source, a, b);
    m.insert_detail_link(p, source, c, b);
    m.insert_detail_link(p, source, c, d);
    m.insert_descended(p, target, a);
    m.insert_detail_query(p, target, a);
    m.close();
    assert!(m.descended(p, target, d));
    assert!(m.detail_result(p, target, c));
    assert!(!m.descended(p, target, e));
    assert!(!m.detail_result(p, target, e));
    assert!(!m.descended(p, source, d));
    assert!(!m.detail_result(p, source, c));

    m.insert_detail_link(p, source, e, b);
    m.close();
    assert!(m.descended(p, target, e));
    assert!(m.detail_result(p, target, e));
    assert!(!m.descended(p, source, e));
    assert!(!m.detail_result(p, source, e));
}
