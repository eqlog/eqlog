use crate::morphism_helper_names::*;

#[test]
fn public_relations_can_use_morphism_helper_names() {
    let mut model = MorphismHelperNames::new();
    let item = model.new_item();
    model.new_child(item);
    model.insert_propagate_item_morphisms();
    model.insert_support_insert_propagate_item_morphisms();
    model.insert_propagate_child_morphisms(item);

    model.close();

    assert!(model.propagate_item_morphisms());
    assert!(model.support_insert_propagate_item_morphisms());
    assert_eq!(model.propagate_child_morphisms(), Some(item));
}
