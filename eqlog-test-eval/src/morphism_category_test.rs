use eqlog_runtime::{CompiledModel, FunctionKind, RelationKind};

use crate::morphism_category::*;

fn arrow(model: &mut MorphismCategory, source: Set, target: Set) -> SetMor {
    let f = model.new_set_mor();
    model.insert_set_mor_dom(f, source);
    model.insert_set_mor_cod(f, target);
    f
}

#[test]
fn identities_fix_members_and_are_created_on_request() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let b = model.new_set();
    let x = model.new_el(a);
    model.close();
    assert_eq!(model.set_mor_id(a), None);
    model.insert_identity_requested(a);
    model.close();
    let identity = model.set_mor_id(a).unwrap();
    assert_eq!(model.set_mor_dom(identity), Some(a));
    assert_eq!(model.set_mor_cod(identity), Some(a));
    assert_eq!(model.el_mor_app(identity, x), Some(x));
    assert_eq!(model.set_mor_id(b), None);
    assert!(model.identity_observed(a));
    assert!(model.inferred_identity(identity));

    let later = model.new_el(a);
    model.close();
    assert_eq!(model.el_mor_app(identity, later), Some(later));
}

#[test]
fn composition_follows_written_order_and_preserves_partial_actions() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let b = model.new_set();
    let c = model.new_set();
    let x = model.new_el(a);
    let y = model.new_el(b);
    let z = model.new_el(c);
    let unmapped = model.new_el(a);
    let f = arrow(&mut model, a, b);
    let g = arrow(&mut model, b, c);
    model.insert_el_mor_app(f, x, y);
    model.insert_el_mor_app(g, y, z);
    model.insert_composition_requested(f, g);
    model.close();
    let composite = model.set_mor_comp(f, g).unwrap();
    assert_eq!(model.set_mor_dom(composite), Some(a));
    assert_eq!(model.set_mor_cod(composite), Some(c));
    assert_eq!(model.el_mor_app(composite, x), Some(z));
    assert_eq!(model.el_mor_app(composite, unmapped), None);
    assert!(model.observed(f, g));
    assert!(model.composite_observed(composite));
    assert_eq!(model.set_mor_comp(g, f), None);
}

#[test]
fn units_and_associativity_agree_as_morphisms() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let b = model.new_set();
    let c = model.new_set();
    let d = model.new_set();
    let f = arrow(&mut model, a, b);
    let g = arrow(&mut model, b, c);
    let h = arrow(&mut model, c, d);
    model.insert_identity_requested(a);
    model.insert_identity_requested(b);
    model.insert_composition_requested(f, g);
    model.insert_composition_requested(g, h);

    model.close();
    let ia = model.set_mor_id(a).unwrap();
    let ib = model.set_mor_id(b).unwrap();
    assert!(model.are_equal_set_mor(model.set_mor_comp(ia, f).unwrap(), f));
    assert!(model.are_equal_set_mor(model.set_mor_comp(f, ib).unwrap(), f));
    let fg = model.set_mor_comp(f, g).unwrap();
    let gh = model.set_mor_comp(g, h).unwrap();
    model.define_set_mor_comp(fg, h);
    model.close();
    assert!(model.are_equal_set_mor(
        model.set_mor_comp(fg, h).unwrap(),
        model.set_mor_comp(f, gh).unwrap(),
    ));
}

#[test]
fn nested_identities_and_composition_use_the_enclosing_model() {
    let mut model = MorphismCategory::new();
    let bundle = model.new_bundle();
    let a = model.new_fiber(bundle);
    let b = model.new_fiber(bundle);
    let c = model.new_fiber(bundle);
    let x = model.new_item(bundle, a);
    let y = model.new_item(bundle, b);
    let z = model.new_item(bundle, c);
    let f = model.new_fiber_mor(bundle);
    let g = model.new_fiber_mor(bundle);
    model.insert_fiber_mor_dom(bundle, f, a);
    model.insert_fiber_mor_cod(bundle, f, b);
    model.insert_fiber_mor_dom(bundle, g, b);
    model.insert_fiber_mor_cod(bundle, g, c);
    model.insert_item_mor_app(bundle, f, x, y);
    model.insert_item_mor_app(bundle, g, y, z);
    model.insert_inner_identity_requested(bundle, a);
    model.insert_inner_composition_requested(bundle, f, g);
    model.close();
    let identity = model.fiber_mor_id(bundle, a).unwrap();
    let composite = model.fiber_mor_comp(bundle, f, g).unwrap();
    assert_eq!(model.item_mor_app(bundle, identity, x), Some(x));
    assert_eq!(model.item_mor_app(bundle, composite, x), Some(z));
    assert_eq!(model.fiber_mor_dom(bundle, composite), Some(a));
    assert_eq!(model.fiber_mor_cod(bundle, composite), Some(c));
}

#[test]
fn outer_morphisms_act_on_deep_members() {
    let mut model = MorphismCategory::new();
    let a = model.new_bundle();
    let b = model.new_bundle();
    let c = model.new_bundle();
    let u = model.new_fiber(a);
    let v = model.new_fiber(b);
    let w = model.new_fiber(c);
    let x = model.new_item(a, u);
    let y = model.new_item(b, v);
    let z = model.new_item(c, w);
    let f = model.new_bundle_mor();
    let g = model.new_bundle_mor();
    model.insert_bundle_mor_dom(f, a);
    model.insert_bundle_mor_cod(f, b);
    model.insert_bundle_mor_dom(g, b);
    model.insert_bundle_mor_cod(g, c);
    model.insert_fiber_mor_app(f, u, v);
    model.insert_fiber_mor_app(g, v, w);
    model.insert_bundle_item_mor_app(f, x, y);
    model.insert_bundle_item_mor_app(g, y, z);
    model.insert_nested_identity_requested(a);
    model.insert_bundle_composition_requested(f, g);
    model.insert_nested_composition_requested(f, g);
    model.close();
    let identity = model.bundle_mor_id(a).unwrap();
    let composite = model.bundle_mor_comp(f, g).unwrap();
    assert_eq!(model.fiber_mor_app(identity, u), Some(u));
    assert_eq!(model.bundle_item_mor_app(identity, x), Some(x));
    assert_eq!(model.fiber_mor_app(composite, u), Some(w));
    assert_eq!(model.bundle_item_mor_app(composite, x), Some(z));
    assert!(model.deep_observed(f, g));
}

#[test]
fn chained_syntax_matches_parenthesized_composition() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let b = model.new_set();
    let c = model.new_set();
    let d = model.new_set();
    let f = arrow(&mut model, a, b);
    let g = arrow(&mut model, b, c);
    let h = arrow(&mut model, c, d);
    model.insert_composition_requested(f, g);
    model.insert_composition_requested(g, h);
    model.insert_chain_requested(f, g, h);
    model.close();
    let fg = model.set_mor_comp(f, g).unwrap();
    let gh = model.set_mor_comp(g, h).unwrap();
    assert!(model.are_equal_set_mor(
        model.set_mor_comp(fg, h).unwrap(),
        model.set_mor_comp(f, gh).unwrap(),
    ));
}

#[test]
fn existing_composite_images_constrain_the_second_map() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let b = model.new_set();
    let c = model.new_set();
    let x = model.new_el(a);
    let y = model.new_el(b);
    let z = model.new_el(c);
    let f = arrow(&mut model, a, b);
    let g = arrow(&mut model, b, c);
    let composite = model.define_set_mor_comp(f, g);
    model.close();
    model.insert_el_mor_app(composite, x, z);
    model.close();
    assert_eq!(model.el_mor_app(f, x), None);
    model.insert_el_mor_app(f, x, y);
    model.close();
    assert_eq!(model.el_mor_app(g, y), Some(z));
}

#[test]
fn composite_endpoints_propagate_back_to_the_operands() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let b = model.new_set();
    let c = model.new_set();
    let f = model.new_set_mor();
    let g = model.new_set_mor();
    let composite = model.define_set_mor_comp(f, g);
    model.insert_set_mor_dom(composite, a);
    model.insert_set_mor_cod(composite, c);
    model.insert_set_mor_cod(f, b);
    model.close();
    assert_eq!(model.set_mor_dom(f), Some(a));
    assert_eq!(model.set_mor_dom(g), Some(b));
    assert_eq!(model.set_mor_cod(g), Some(c));
}

#[test]
fn a_chain_only_requires_its_left_inner_composite() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let f = arrow(&mut model, a, a);
    let g = arrow(&mut model, a, a);
    let h = arrow(&mut model, a, a);
    let fg = model.define_set_mor_comp(f, g);
    model.insert_left_chain_requested(f, g, h);
    model.close();
    assert!(model.set_mor_comp(fg, h).is_some());
    assert_eq!(model.set_mor_comp(g, h), None);
}

#[test]
fn associativity_merges_existing_outer_composites() {
    let mut model = MorphismCategory::new();
    let a = model.new_set();
    let f = arrow(&mut model, a, a);
    let g = arrow(&mut model, a, a);
    let h = arrow(&mut model, a, a);
    let fg = model.define_set_mor_comp(f, g);
    let gh = model.define_set_mor_comp(g, h);
    let left = model.define_set_mor_comp(fg, h);
    let right = model.define_set_mor_comp(f, gh);
    assert!(!model.are_equal_set_mor(left, right));
    model.close();
    assert!(model.are_equal_set_mor(left, right));
}

#[test]
fn dynamic_signature_identifies_category_operations() {
    let signature = MorphismCategory::dynamic_signature();
    let set = signature.type_named("Set").unwrap();
    for (name, kind) in [
        ("set_mor_id", FunctionKind::MorphismIdentity(set)),
        ("set_mor_comp", FunctionKind::MorphismComposition(set)),
    ] {
        let relation = signature.relation_named(name).unwrap();
        assert_eq!(
            signature.relation(relation).unwrap().kind,
            RelationKind::Function(kind)
        );
    }
}
