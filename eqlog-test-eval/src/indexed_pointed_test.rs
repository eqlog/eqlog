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
fn single_external_terminal_pointed() {
    let mut model = IndexedPointed::new();

    let ptd = model.new_pointed();
    model.insert_is_subterminal_pointed(ptd);

    let a = model.new_p();
    let b = model.new_p();
    model.insert_p_parent(a, ptd);
    model.insert_p_parent(b, ptd);
    assert!(!model.are_equal_p(a, b));
    model.close();

    assert!(model.are_equal_p(a, b));
}

#[test]
fn merge_non_empty_models() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    let a = model.new_p();
    let b = model.new_p();
    model.insert_p_parent(a, ptd0);
    model.insert_p_parent(b, ptd1);

    model.equate_pointed(ptd0, ptd1);
    model.close();

    assert_eq!(model.iter_p().count(), 2);
}

#[test]
fn merge_non_empty_models_terminal() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    model.insert_is_subterminal_pointed(ptd0);

    let a = model.new_p();
    let b = model.new_p();
    model.insert_p_parent(a, ptd0);
    model.insert_p_parent(b, ptd1);

    model.close();

    assert!(!model.are_equal_pointed(ptd0, ptd1));
    assert!(!model.are_equal_p(a, b));

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert_eq!(model.iter_p().count(), 1);
    assert!(model.are_equal_p(a, b));
}

#[test]
fn merge_non_empty_models_internal() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    model.insert_is_subterminal(ptd0);

    let a = model.new_p();
    let b = model.new_p();
    model.insert_p_parent(a, ptd0);
    model.insert_p_parent(b, ptd1);

    model.close();

    assert!(!model.are_equal_pointed(ptd0, ptd1));
    assert!(!model.are_equal_p(a, b));

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert_eq!(model.iter_p().count(), 1);
    assert!(model.are_equal_p(a, b));
}

#[test]
fn merge_non_empty_models_with_pt() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    model.insert_is_subterminal_pointed(ptd0);

    let a = model.define_pt(ptd0);
    let b = model.define_pt(ptd1);
    model.insert_p_parent(a, ptd0);
    model.insert_p_parent(b, ptd1);

    model.close();

    assert!(!model.are_equal_pointed(ptd0, ptd1));
    assert!(!model.are_equal_p(a, b));

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert_eq!(model.iter_p().count(), 1);
    assert!(model.are_equal_p(a, b));
}
