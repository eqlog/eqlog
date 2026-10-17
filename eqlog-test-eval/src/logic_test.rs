use crate::logic::*;
use std::cell::Cell;

#[test]
fn closed_models_still_check_conditions_and_resume_after_insertion() {
    let mut model = Logic::new();
    model.close();
    let calls = Cell::new(0);
    for result in [false, true] {
        assert_eq!(
            model.close_until(|model| {
                calls.set(calls.get() + 1);
                assert!(model.truth());
                result
            }),
            result
        );
    }
    assert_eq!(calls.get(), 2);
    model.insert_truth();
    model.close();
    assert!(!model.undetermined());
    model.insert_absurd();
    model.close();
    assert!(model.undetermined());
}

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
