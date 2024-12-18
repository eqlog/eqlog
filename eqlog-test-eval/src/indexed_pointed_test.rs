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
    model.insert_is_subterminal_pointed(ptd);

    let mut ptd_model = model.get_pointed_model_mut(ptd);
    let a = ptd_model.new_p();
    let b = ptd_model.new_p();
    assert!(!ptd_model.are_equal_p(a, b));
    drop(ptd_model);
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
    let _ = model.get_pointed_model(ptd0);
    let _ = model.get_pointed_model(ptd1);

    model.close();
    let ptd0_model = model.get_pointed_model(ptd0);
    let ptd1_model = model.get_pointed_model(ptd1);
    assert_eq!(
        &*ptd0_model as *const PointedModelData,
        &*ptd1_model as *const PointedModelData
    );
}

#[test]
fn merge_non_empty_models() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    let ptd1 = model.new_pointed();

    assert!(!model.are_equal_pointed(ptd0, ptd1));

    let mut ptd0_model = model.get_pointed_model_mut(ptd0);
    ptd0_model.new_p();
    drop(ptd0_model);
    let mut ptd1_model = model.get_pointed_model_mut(ptd1);
    ptd1_model.new_p();
    drop(ptd1_model);

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert!(model.are_equal_pointed(ptd0, ptd1));
    assert_eq!(model.get_pointed_model(ptd0).iter_p().count(), 2);
}

#[test]
fn merge_non_empty_models_terminal() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    model.insert_is_subterminal_pointed(ptd0);
    let ptd1 = model.new_pointed();

    assert!(!model.are_equal_pointed(ptd0, ptd1));

    let mut ptd0_model = model.get_pointed_model_mut(ptd0);
    ptd0_model.new_p();
    drop(ptd0_model);
    let mut ptd1_model = model.get_pointed_model_mut(ptd1);
    ptd1_model.new_p();
    drop(ptd1_model);

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert!(model.are_equal_pointed(ptd0, ptd1));
    assert_eq!(model.get_pointed_model(ptd0).iter_p().count(), 1);
}

#[test]
fn merge_non_empty_models_with_pt() {
    let mut model = IndexedPointed::new();

    let ptd0 = model.new_pointed();
    model.insert_is_subterminal_pointed(ptd0);
    let ptd1 = model.new_pointed();

    assert!(!model.are_equal_pointed(ptd0, ptd1));

    let mut ptd0_model = model.get_pointed_model_mut(ptd0);
    ptd0_model.define_pt();
    drop(ptd0_model);
    let mut ptd1_model = model.get_pointed_model_mut(ptd1);
    ptd1_model.define_pt();
    drop(ptd1_model);

    model.equate_pointed(ptd0, ptd1);

    model.close();
    assert!(model.are_equal_pointed(ptd0, ptd1));
    assert_eq!(model.get_pointed_model(ptd0).iter_p().count(), 1);
    assert!(model.get_pointed_model(ptd0).pt().is_some());
}

#[test]
fn merge_indexed_pointed_models() {
    let mut model0 = IndexedPointed::new();
    model0.new_pointed();

    let mut model1 = IndexedPointed::new();
    model1.new_pointed();

    model0.merge(model1);
    model0.close();
    assert_eq!(model0.iter_pointed().count(), 2,);
    for ptd in model0.iter_pointed() {
        assert_eq!(model0.get_pointed_model(ptd).iter_p().count(), 0);
    }
}
