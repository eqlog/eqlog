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

    assert!(model.set_member_s(set, a));
    model.close();
    assert!(model.set_member_s(set, a));

    assert_eq!(model.iter_set().count(), 1);
    assert_eq!(model.iter_s().count(), 1);
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn member_predicate_insert_rejects_wrong_parent() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();
    let x = model.new_s(set0);

    model.insert_flagged(set1, x);
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn member_predicate_query_rejects_wrong_parent() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();
    let x = model.new_s(set0);

    let _ = model.flagged(set1, x);
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

#[test]
fn morphism_propagates_member_before_parent_index() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();
    let morphism = model.new_set_mor();
    model.insert_set_mor_dom(morphism, set0);
    model.insert_set_mor_cod(morphism, set1);

    let x = model.new_s(set0);
    let y = model.new_s(set1);
    model.insert_s_mor_app(morphism, x, y);
    model.insert_flagged(set0, x);

    model.close();

    assert!(model.reached_flagged_image(set1));
}

#[test]
fn morphism_copies_visible_model_arguments() {
    let mut model = IndexedSet::new();

    let set0 = model.new_set();
    let set1 = model.new_set();
    let unrelated = model.new_set();
    let morphism = model.new_set_mor();
    model.insert_set_mor_dom(morphism, set0);
    model.insert_set_mor_cod(morphism, set1);

    let x = model.new_s(set0);
    let y = model.new_s(set1);
    model.insert_s_mor_app(morphism, x, y);
    model.insert_tagged_by(set0, unrelated, x);

    model.close();

    assert!(model.tagged_by(set1, unrelated, y));
}
