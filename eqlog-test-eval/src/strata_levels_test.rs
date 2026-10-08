use crate::strata_levels::StrataLevels;

#[test]
fn independent_cycles_and_acyclic_rules_share_incremental_rounds() {
    let mut m = StrataLevels::new();
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    let d = m.new_el();
    m.insert_seed(a);
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    m.close();
    assert!(m.result(a));
    assert!(m.reached(c));
    assert!(!m.result(c));
    assert!(!m.reached(d));

    m.insert_seed(c);
    m.insert_edge(c, d);
    m.close();
    assert!(m.result(c));
    assert!(m.reached(d));
    assert!(!m.result(d));
}

#[cfg(feature = "stratified")]
#[test]
fn parallel_rules_commit_together_and_consumers_wait_for_recursive_closure() {
    let mut m = StrataLevels::new();
    let a = m.new_el();
    let b = m.new_el();
    let c = m.new_el();
    m.insert_seed(a);
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    assert!(m.close_until(|m| m.left(a) || m.right(a)));
    assert!(m.left(a));
    assert!(m.right(a));
    assert!(!m.right_next(a));

    assert!(m.close_until(|m| m.joined(a)));
    assert!(m.reach_left(c));
    assert!(m.reach_right(c));
    assert!(m.reached(c));
    assert!(!m.result(a));
    m.close();
    assert!(m.result(a));
}
