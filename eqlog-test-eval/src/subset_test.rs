use crate::subset::*;

#[test]
fn test_singleton_subset_propagates() {
    let mut model = Subset::new();

    let a = model.new_subs();
    let b = model.new_subs();
    let mor = model.new_subs_mor();
    model.insert_subs_mor_dom(mor, a);
    model.insert_subs_mor_cod(mor, b);

    let el = model.new_carrier();
    model.insert_element(a, el);

    model.close();

    assert!(model.element(b, el));
}

#[test]
fn test_subset_union() {
    let mut model = Subset::new();

    let a = model.new_subs();
    let b = model.new_subs();
    let c = model.new_subs();

    let ac = model.new_subs_mor();
    let bc = model.new_subs_mor();

    model.insert_subs_mor_dom(ac, a);
    model.insert_subs_mor_dom(bc, b);

    model.insert_subs_mor_cod(ac, c);
    model.insert_subs_mor_cod(bc, c);

    let el0 = model.new_carrier();
    let el1 = model.new_carrier();
    let el2 = model.new_carrier();

    model.insert_element(a, el0);
    model.insert_element(b, el1);
    model.insert_element(b, el2);

    model.close();

    assert!(model.element(c, el0));
    assert!(model.element(c, el1));
    assert!(model.element(c, el2));

    assert!(!model.element(a, el1));
    assert!(!model.element(a, el2));
    assert!(!model.element(b, el0));
}

#[test]
fn test_subset_disjoint_diagrams() {
    let mut model = Subset::new();

    // a <= c and b <= c
    // d <= e
    let a = model.new_subs();
    let b = model.new_subs();
    let c = model.new_subs();
    let d = model.new_subs();
    let e = model.new_subs();

    let ac = model.new_subs_mor();
    let bc = model.new_subs_mor();
    let de = model.new_subs_mor();

    model.insert_subs_mor_dom(ac, a);
    model.insert_subs_mor_dom(bc, b);
    model.insert_subs_mor_dom(de, d);

    model.insert_subs_mor_cod(ac, c);
    model.insert_subs_mor_cod(bc, c);
    model.insert_subs_mor_cod(de, e);

    let el0 = model.new_carrier();
    let el1 = model.new_carrier();
    let el2 = model.new_carrier();
    let el3 = model.new_carrier();

    model.insert_element(a, el0);
    model.insert_element(b, el1);
    model.insert_element(b, el2);
    model.insert_element(d, el3);

    model.close();

    assert!(model.element(a, el0));
    assert!(!model.element(a, el1));
    assert!(!model.element(a, el2));
    assert!(!model.element(a, el3));

    assert!(!model.element(b, el0));
    assert!(model.element(b, el1));
    assert!(model.element(b, el2));
    assert!(!model.element(b, el3));

    assert!(model.element(c, el0));
    assert!(model.element(c, el1));
    assert!(model.element(c, el2));
    assert!(!model.element(c, el3));

    assert!(!model.element(d, el0));
    assert!(!model.element(d, el1));
    assert!(!model.element(d, el2));
    assert!(model.element(d, el3));

    assert!(!model.element(e, el0));
    assert!(!model.element(e, el1));
    assert!(!model.element(e, el2));
    assert!(model.element(e, el3));
}

#[test]
fn test_transitive() {
    let mut model = Subset::new();

    // a <= b and b <= c
    let a = model.new_subs();
    let b = model.new_subs();
    let c = model.new_subs();

    let ab = model.new_subs_mor();
    let bc = model.new_subs_mor();

    model.insert_subs_mor_dom(ab, a);
    model.insert_subs_mor_dom(bc, b);

    model.insert_subs_mor_cod(ab, b);
    model.insert_subs_mor_cod(bc, c);

    let el0 = model.new_carrier();
    let el1 = model.new_carrier();
    let el2 = model.new_carrier();

    model.insert_element(a, el0);
    model.insert_element(b, el1);
    model.insert_element(c, el2);

    model.close();

    assert!(model.element(a, el0));
    assert!(!model.element(a, el1));
    assert!(!model.element(a, el2));

    assert!(model.element(b, el0));
    assert!(model.element(b, el1));
    assert!(!model.element(b, el2));

    assert!(model.element(c, el0));
    assert!(model.element(c, el1));
    assert!(model.element(c, el2));
}
