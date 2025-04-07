use crate::indexed_set::*;

#[test]
fn empty_model() {
    let mut model = IndexedSet::new();
    model.close();
}

#[test]
fn single_empty_set() {
    let mut model = IndexedSet::new();
    model.new_set();

    model.close();
    assert_eq!(model.iter_set().count(), 1);
}

#[test]
fn singleton_set() {
    let mut model = IndexedSet::new();

    let set = model.new_set();
    let a = model.new_s(set);

    assert!(model.are_equal_set(model.s_parent(a), set));
    model.close();
    assert!(model.are_equal_set(model.s_parent(a), set));

    assert_eq!(model.iter_set().count(), 1);
    assert_eq!(model.iter_s().count(), 1);
}

#[test]
fn single_external_terminal_set() {
    let mut model = IndexedSet::new();

    let set = model.new_set();
    model.insert_is_subterminal_set(set);

    let a = model.new_s(set);
    let b = model.new_s(set);
    assert!(!model.are_equal_s(a, b));
    model.close();

    assert!(model.are_equal_s(a, b));
}

#[test]
fn merge_non_empty_models() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();

    model.new_s(set0);
    model.new_s(set1);

    model.equate_set(set0, set1);
    model.close();

    assert_eq!(model.iter_s().count(), 2);
}

#[test]
fn merge_non_empty_models_terminal() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();

    model.insert_is_subterminal_set(set0);

    let a = model.new_s(set0);
    let b = model.new_s(set1);

    model.close();

    assert!(!model.are_equal_set(set0, set1));
    assert!(!model.are_equal_s(a, b));

    model.equate_set(set0, set1);

    model.close();
    assert_eq!(model.iter_s().count(), 1);
    assert!(model.are_equal_s(a, b));
}

#[test]
fn merge_non_empty_models_internal() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();

    model.insert_is_subterminal(set0);

    let a = model.new_s(set0);
    let b = model.new_s(set1);

    model.close();

    assert!(!model.are_equal_set(set0, set1));
    assert!(!model.are_equal_s(a, b));

    model.equate_set(set0, set1);

    model.close();
    assert_eq!(model.iter_s().count(), 1);
    assert!(model.are_equal_s(a, b));
}
