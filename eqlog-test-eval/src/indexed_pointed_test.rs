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
fn merge_non_empty_without_pt() {
    let mut model = IndexedPointed::new();

    let pointed0 = model.new_pointed();
    let pointed1 = model.new_pointed();

    model.new_p(pointed0);
    model.new_p(pointed1);

    model.equate_pointed(pointed0, pointed1);
    model.close();

    // Elements a, b and the pt() constant.
    assert_eq!(model.iter_p().count(), 3);
}

#[test]
fn merge_initial_models() {
    let mut model = IndexedPointed::new();

    let pointed0 = model.new_pointed();
    let pointed1 = model.new_pointed();
    model.close();

    assert_eq!(model.iter_pointed().count(), 2);
    assert_eq!(model.iter_p().count(), 2);
    assert_eq!(model.iter_p_parent().count(), 2);

    model.equate_pointed(pointed0, pointed1);
    model.close();

    assert_eq!(model.iter_pointed().count(), 1);
    assert_eq!(model.iter_p().count(), 1);
    assert_eq!(model.iter_p_parent().count(), 1);
}
