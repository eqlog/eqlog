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
