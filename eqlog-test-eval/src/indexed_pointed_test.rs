use crate::indexed_pointed::*;

#[test]
fn empty_model() {
    let mut model = IndexedPointed::new();
    model.close();
}

#[test]
fn single_pointed() {
    let mut model = IndexedPointed::new();
    model.new_pointed();

    model.close();
    assert_eq!(model.iter_pointed().count(), 1);
}

#[test]
fn single_terminal_pointed() {
    let mut model = IndexedPointed::new();

    let ptd = model.new_pointed();
    model.insert_is_terminal_pointed(ptd);

    let ptd_model = model.get_pointed_model_mut(ptd);
    let a = ptd_model.new_p();
    let b = ptd_model.new_p();
    assert!(!ptd_model.are_equal_p(a, b));
    model.close();

    let ptd_model = model.get_pointed_model(ptd);
    assert!(ptd_model.are_equal_p(a, b));
}
