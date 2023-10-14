use eqlog_runtime::eqlog_mod;
eqlog_mod!(trans_refl);
pub use crate::trans_refl::*;

#[test]
fn test_close_empty() {
    let mut m = TransRefl::new();
    m.close();
}

#[test]
fn test_one_elment() {
    let mut m = TransRefl::new();
    m.new_v();
    m.close();
    assert_eq!(m.iter_v().count(), 1);
    assert_eq!(m.iter_edge().count(), 1);
}

#[test]
fn test_two_discrete_elements() {
    let mut m = TransRefl::new();
    m.new_v();
    m.new_v();
    m.close();
    assert_eq!(m.iter_v().count(), 2);
    assert_eq!(m.iter_edge().count(), 2);
}

#[test]
fn test_arrow() {
    let mut m = TransRefl::new();
    let a = m.new_v();
    let b = m.new_v();
    m.insert_edge(a, b);
    m.close();
    assert_eq!(m.iter_v().count(), 2);
    assert_eq!(m.iter_edge().count(), 3);
}

#[test]
fn test_bi_arrow() {
    let mut m = TransRefl::new();
    let a = m.new_v();
    let b = m.new_v();
    m.insert_edge(a, b);
    m.insert_edge(b, a);
    m.close();
    assert_eq!(m.iter_v().count(), 2);
    assert_eq!(m.iter_edge().count(), 4);
}

#[test]
fn test_arrow_arrow() {
    let mut m = TransRefl::new();
    let a = m.new_v();
    let b = m.new_v();
    let c = m.new_v();
    m.insert_edge(a, b);
    m.insert_edge(b, c);
    m.close();
    assert_eq!(m.iter_v().count(), 3);
    assert_eq!(m.iter_edge().count(), 6);
}
