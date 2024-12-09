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

#[test]
fn merge_empty_models() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    assert!(!model.are_equal_pointed(ptd0, ptd1));
    model.equate_pointed(ptd0, ptd1);

    // Check that getting models still works (i.e. doesn't panic) after equating but before
    // closing/canonicalizing.
    let _: &PointedModel = model.get_pointed_model(ptd0);
    let _: &PointedModel = model.get_pointed_model(ptd1);

    model.close();
    let ptd0_model = model.get_pointed_model(ptd0);
    let ptd1_model = model.get_pointed_model(ptd1);
    assert_eq!(
        ptd0_model as *const PointedModel,
        ptd1_model as *const PointedModel
    );
}

#[test]
fn merge_non_empty_models() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    assert!(!model.are_equal_pointed(ptd0, ptd1));

    let ptd0_model = model.get_pointed_model_mut(ptd0);
    ptd0_model.new_p();
    let ptd1_model = model.get_pointed_model_mut(ptd1);
    ptd1_model.new_p();

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert!(model.are_equal_pointed(ptd0, ptd1));
    assert_eq!(model.get_pointed_model(ptd0).iter_p().count(), 2);
}

#[test]
fn merge_non_empty_models_terminal() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    model.insert_is_terminal_pointed(ptd0);
    let ptd1 = model.new_pointed();

    assert!(!model.are_equal_pointed(ptd0, ptd1));

    let ptd0_model = model.get_pointed_model_mut(ptd0);
    ptd0_model.new_p();
    let ptd1_model = model.get_pointed_model_mut(ptd1);
    ptd1_model.new_p();

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert!(model.are_equal_pointed(ptd0, ptd1));
    assert_eq!(model.get_pointed_model(ptd0).iter_p().count(), 1);
}
