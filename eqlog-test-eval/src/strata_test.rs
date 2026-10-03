use crate::strata::Strata;

#[test]
fn incremental_strata_close_recursive_components_and_outer_allocation() {
    let mut model = Strata::new();
    let a = model.new_item();
    let b = model.new_item();
    let c = model.new_item();
    model.insert_seed(a);
    model.insert_edge(a, b);
    model.close();
    assert!(model.output(b));
    assert!(model.witnessed(a));
    assert!(model.witnessed(b));
    assert!(model.seed(b));
    assert!(!model.output(c));

    model.insert_edge(b, c);
    model.close();
    assert!(model.output(c));
    assert!(model.witnessed(c));
    assert!(model.seed(c));
    assert_eq!(model.iter_witness().count(), 3);
    model.close();
    assert_eq!(model.iter_witness().count(), 3);
}

#[test]
fn equality_enables_a_join_of_previously_consumed_inputs() {
    let mut model = Strata::new();
    let a = model.new_item();
    let b = model.new_item();
    model.insert_left(a);
    model.insert_right(b);
    model.close();
    assert!(!model.joined(a));
    model.insert_merge(a, b);
    model.close();
    assert!(model.joined(a));
    assert!(model.joined(b));
}

#[test]
fn early_return_preserves_deferred_definitions() {
    let mut model = Strata::new();
    let a = model.new_item();
    model.insert_output(a);
    assert!(model.close_until(|model| model.staged(a)));
    assert!(model.witness(a).is_none());
    model.close();
    assert!(model.witnessed(a));
    assert_eq!(model.iter_witness().count(), 1);
}

#[test]
fn deferred_definitions_recheck_equalities_after_an_interruption() {
    let mut model = Strata::new();
    let a = model.new_item();
    let b = model.new_item();
    model.insert_output(a);
    assert!(model.close_until(|model| model.staged(a)));
    assert!(model.witness(a).is_none());
    let existing = model.new_value();
    model.insert_witness(b, existing);
    model.equate_item(a, b);
    model.canonicalize();
    model.close();
    assert_eq!(model.witness(a), Some(existing));
    assert!(model.witnessed(a));
    assert_eq!(model.iter_value().count(), 1);
}

#[test]
fn external_canonicalization_preserves_unconsumed_equality_matches() {
    let mut model = Strata::new();
    let a = model.new_item();
    let b = model.new_item();
    model.insert_left(a);
    model.insert_right(b);
    model.close();
    model.equate_item(a, b);
    model.canonicalize();
    model.canonicalize();
    model.close();
    assert!(model.joined(a));
}
