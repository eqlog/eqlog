use std::panic::{catch_unwind, AssertUnwindSafe};

use eqlog_runtime::{CompiledModel, Element};
use eqlog_test_eval::dependent_signatures::DependentSignatures;

#[test]
fn dependent_columns_control_inference_allocation_and_public_arguments() {
    let mut model = DependentSignatures::new();
    let a = model.new_world();
    let b = model.new_world();
    let x = model.new_el(a);
    model.insert_requested(a, b, x);
    model.close();
    let y = model.transport(a, b, x).unwrap();
    assert!(model.related(a, b, x, y));
    assert!(model.marked(b, y));
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, a);
    model.insert_world_mor_cod(morphism, b);
    model.insert_el_mor_app(morphism, x, y);
    model.insert_foreign(a, a, x);
    model.close();
    assert!(model.foreign(b, a, x));
    assert!(!model.foreign(b, b, y));
    assert!(catch_unwind(AssertUnwindSafe(|| model.related(a, b, y, x))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| model.define_transport(b, a, x))).is_err());

    let f = model.new_fiber(a);
    let g = model.new_fiber(a);
    let point = model.new_point(a, f);
    let image = model.define_nested(a, f, g, point);
    assert!(catch_unwind(AssertUnwindSafe(|| model.nested(a, g, f, point))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(
        || model.insert_nested(a, f, f, point, image)
    ))
    .is_err());
}

#[test]
fn dynamic_signatures_retain_explicit_owner_columns() {
    let mut compiled = DependentSignatures::new();
    let a = compiled.new_world();
    compiled.new_world();
    compiled.new_el(a);
    compiled.close();
    let mut model = compiled.to_dynamic();
    let sig = model.signature();
    let world = sig.type_named("World").unwrap();
    let el = sig.type_named("World::El").unwrap();
    let transport = sig.relation_named("transport").unwrap();
    let element = |type_, index| Element { type_, index };
    let a = element(world, 0);
    let b = element(world, 1);
    let x = element(el, 0);
    let y = model.define(transport, &[a, b, x]).unwrap();
    assert_eq!(model.eval(transport, &[a, b, x]).unwrap(), Some(y));
    assert!(model.eval(transport, &[b, a, x]).is_err());
    assert!(model.insert(transport, &[a, b, x, x]).is_err());
    DependentSignatures::from_dynamic(&model).unwrap();
}

#[test]
fn member_equalities_rewrite_inherited_facts_with_local_and_foreign_owners() {
    let mut model = DependentSignatures::new();
    let source = model.new_world();
    let target = model.new_world();
    let foreign = model.new_world();
    let x = model.new_el(source);
    let y = model.new_el(target);
    let z = model.new_el(foreign);
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    model.insert_el_mor_app(morphism, x, y);
    model.insert_marked(source, x);
    model.insert_foreign(source, foreign, z);
    model.close();
    assert!(model.marked(target, y));
    assert!(model.foreign(target, foreign, z));

    let alias_y = model.new_el(target);
    let alias_z = model.new_el(foreign);
    model.insert_marked(target, alias_y);
    model.insert_foreign(target, foreign, alias_z);
    model.equate_el(target, alias_y, y);
    model.equate_el(foreign, alias_z, z);
    model.canonicalize();
    assert_eq!(model.iter_marked().count(), 2);
    assert_eq!(model.iter_foreign().count(), 2);
    assert!(model.marked(target, y));
    assert!(model.foreign(target, foreign, z));
    model.close();
    assert!(model.marked(source, x));
    assert!(model.foreign(source, foreign, z));
}
