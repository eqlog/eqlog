use crate::logic::*;

#[test]
fn test_close_empty() {
    let mut m = Logic::new();
    m.close();
    assert_eq!(m.iter_absurd().count(), 0);
    assert_eq!(m.iter_truth().count(), 1);
    assert_eq!(m.iter_undetermined().count(), 0);
}

#[test]
fn test_close_undetermined() {
    let mut m = Logic::new();
    m.insert_undetermined();
    m.close();
    assert_eq!(m.iter_absurd().count(), 0);
    assert_eq!(m.iter_truth().count(), 1);
    assert_eq!(m.iter_undetermined().count(), 1);
}

#[test]
fn test_close_absurd() {
    let mut m = Logic::new();
    m.insert_absurd();
    m.close();
    assert_eq!(m.iter_absurd().count(), 1);
    assert_eq!(m.iter_truth().count(), 1);
    assert_eq!(m.iter_undetermined().count(), 1);
}
