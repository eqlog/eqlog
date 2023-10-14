use eqlog_runtime::eqlog_mod;
eqlog_mod!(logic);

pub use crate::logic::*;

#[test]
fn test_close_empty() {
    let mut m = Logic::new();
    m.close();
    assert!(!m.absurd());
    assert!(m.truth());
    assert!(!m.undetermined());
}

#[test]
fn test_close_undetermined() {
    let mut m = Logic::new();
    m.insert_undetermined();
    m.close();
    assert!(!m.absurd());
    assert!(m.truth());
    assert!(m.undetermined());
}

#[test]
fn test_close_absurd() {
    let mut m = Logic::new();
    m.insert_absurd();
    m.close();
    assert!(m.absurd());
    assert!(m.truth());
    assert!(m.undetermined());
}
