use std::collections::BTreeSet;

use eqlog_runtime::{
    CompiledModel, Element, Error, FunctionKind, Model, RelationKind, Signature, TypeKind,
};
use std::sync::Arc;

use crate::consts::Consts;
use crate::diagonal_canonicalization::DiagonalCanonicalization;
use crate::empty::Empty;
use crate::logic::Logic;
use crate::member_parents::MemberParents;
use crate::morphism_preservation::MorphismPreservation;
use crate::nat::Nat;
use crate::partial_magma::PartialMagma;
use crate::trans_refl::{TransRefl, V};

fn handle<M: CompiledModel>(type_: &str, index: u32) -> Element {
    Element {
        type_: M::dynamic_signature().type_named(type_).unwrap(),
        index,
    }
}

fn round_trip<M: CompiledModel>(source: &M) -> M {
    let before = source.to_dynamic();
    let restored = M::from_dynamic(&before).unwrap();
    let after = restored.to_dynamic();
    assert_eq!(before.signature(), after.signature());
    for (type_, _) in before.signature().types() {
        assert_eq!(
            before.elements(type_).unwrap().collect::<BTreeSet<_>>(),
            after.elements(type_).unwrap().collect::<BTreeSet<_>>()
        );
    }
    for (relation, _) in before.signature().relations() {
        let expected: BTreeSet<_> = before.tuples(relation).unwrap().collect();
        let actual: BTreeSet<_> = after.tuples(relation).unwrap().collect();
        assert_eq!(expected, actual);
    }
    restored
}

#[test]
fn dynamic_round_trip_does_not_run_rules() {
    let mut model = TransRefl::new();
    let x = model.new_v();
    let y = model.new_v();
    let z = model.new_v();
    let isolated = model.new_v();
    model.insert_edge(x, y);
    model.insert_edge(y, z);
    let mut restored = round_trip(&model);
    assert_eq!(restored.iter_v().count(), 4);
    assert_eq!(restored.iter_edge().count(), 2);
    assert!(!restored.edge(x, z));
    assert!(!restored.edge(isolated, isolated));
    restored.close();
    assert!(restored.edge(x, z));
    assert!(restored.edge(isolated, isolated));
    round_trip(&restored);
}

#[test]
fn dynamic_export_tracks_pending_equalities_and_function_conflicts() {
    let mut model = PartialMagma::new();
    let x = model.new_el();
    let alias = model.new_el();
    let y = model.new_el();
    let z = model.new_el();
    model.insert_mul(x, x, y);
    model.insert_mul(alias, alias, z);
    model.equate_el(x, alias);
    let mut restored = round_trip(&model);
    assert!(restored.are_equal_el(x, alias));
    assert!(!restored.are_equal_el(y, z));
    assert_eq!(restored.iter_mul().count(), 2);
    restored.close();
    assert!(restored.are_equal_el(y, z));
    assert_eq!(restored.iter_mul().count(), 1);
}

#[test]
fn dynamic_construction_and_aliases_survive_import() {
    let signature = TransRefl::dynamic_signature();
    let type_ = signature.type_named("V").unwrap();
    let edge = signature.relation_named("edge").unwrap();
    let mut model = Model::new(signature);
    let x = model.new_element(type_, &[]).unwrap();
    let alias = model.new_element(type_, &[]).unwrap();
    let y = model.new_element(type_, &[]).unwrap();
    model.insert(edge, &[alias, y]).unwrap();
    model.equate(&[], alias, x).unwrap();
    let mut compiled = TransRefl::from_dynamic(&model).unwrap();
    assert!(compiled.are_equal_v(V(x.index), V(alias.index)));
    let x = V(x.index);
    let y = V(y.index);
    assert!(compiled.edge(compiled.root_v(x), y));
    assert!(!compiled.edge(y, y));
    compiled.close();
    assert!(compiled.edge(y, y));
}

#[test]
fn dynamic_nested_ownership_survives_pending_parent_equalities() {
    for closed in [false, true] {
        for reverse in [false, true] {
            let mut model = MemberParents::new();
            let a = model.new_outer();
            let b = model.new_outer();
            let i = model.new_inner(a);
            let j = model.new_inner(b);
            let x = model.new_el(a, i);
            let y = model.new_el(b, j);
            model.define_label_value(a, i);
            model.define_label_value(b, j);
            if closed {
                model.close();
            }
            let (a, b, i, j, x, y) = if reverse {
                (b, a, j, i, y, x)
            } else {
                (a, b, i, j, x, y)
            };
            model.equate_outer(a, b);
            model.equate_inner(b, i, j);
            model.equate_el(b, j, x, y);
            let mut restored = round_trip(&model);
            assert_eq!(restored.iter_outer().count(), 1);
            assert_eq!(restored.iter_inner().count(), 1);
            assert_eq!(restored.iter_el().count(), 1);
            assert_eq!(restored.iter_label().count(), 2);
            restored.close();
            assert_eq!(restored.iter_label().count(), 1);
            round_trip(&restored);
        }
    }
}

#[test]
fn dynamic_morphism_export_preserves_inherited_and_pending_facts() {
    let mut model = MorphismPreservation::new();
    let a = model.new_world();
    let b = model.new_world();
    let x = model.new_el(a);
    let y = model.new_el(b);
    let label = model.new_ambient();
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, a);
    model.insert_world_mor_cod(h, b);
    model.insert_el_mor_app(h, x, y);
    model.insert_ready(a);
    model.insert_tagged(a, x, label);
    let before = round_trip(&model);
    assert_eq!(before.iter_tagged().count(), 1);
    assert_eq!(before.iter_ready().count(), 1);
    model.close();
    assert!(model.tagged(b, y, label));
    let late_label = model.new_ambient();
    model.insert_tagged(a, x, late_label);
    let mut restored = round_trip(&model);
    assert_eq!(restored.iter_tagged().count(), 3);
    restored.close();
    assert_eq!(restored.iter_tagged().count(), 4);
    round_trip(&restored);
}

#[test]
fn dynamic_enum_graphs_allow_recursive_values_and_multiple_cases() {
    let mut model = Nat::new();
    let zero = model.define_zero();
    let one = model.define_succ(zero);
    model.insert_succ(one, one);
    model.equate_n(zero, one);
    let restored = round_trip(&model);
    assert_eq!(restored.iter_n().count(), 1);
    assert_eq!(restored.iter_zero().count(), 1);
    assert_eq!(restored.iter_succ().count(), 2);
    let signature = Nat::dynamic_signature();
    let zero = signature.relation_named("Zero").unwrap();
    assert_eq!(
        signature.relation(zero).unwrap().kind,
        RelationKind::Function(FunctionKind::Constructor)
    );
}

#[test]
fn dynamic_empty_structures_do_not_define_constants() {
    round_trip(&Empty::new());
    let mut restored = round_trip(&Consts::new());
    assert!(restored.foo().is_none());
    assert!(restored.main_container().is_none());
    restored.close();
    assert!(restored.foo().is_some());
    round_trip(&restored);
}

#[test]
fn dynamic_nullary_predicates_preserve_truth_without_saturation() {
    let mut model = Logic::new();
    model.insert_absurd();
    let mut restored = round_trip(&model);
    assert!(restored.absurd());
    assert!(!restored.truth());
    assert!(!restored.undetermined());
    restored.close();
    assert!(restored.truth());
    assert!(restored.undetermined());
    round_trip(&restored);
}

#[test]
fn dynamic_signatures_preserve_morphism_roles() {
    let signature = MorphismPreservation::dynamic_signature();
    let world = signature.type_named("World").unwrap();
    let morphism = signature.type_named("WorldMor").unwrap();
    let item = signature.type_named("World::Inner::Item").unwrap();
    let application = signature.relation_named("world_item_mor_app").unwrap();
    assert_eq!(
        signature.type_(morphism).unwrap().kind,
        TypeKind::Morphism(world)
    );
    assert_eq!(
        signature.relation(application).unwrap().kind,
        RelationKind::Function(FunctionKind::MorphismApplication {
            morphism,
            member: item
        })
    );
    let error = PartialMagma::from_dynamic(&Model::new(signature))
        .err()
        .unwrap();
    assert_eq!(error, Error::SignatureMismatch);
}

#[test]
fn dynamic_checks_parent_chains_before_mutation() {
    let signature = MemberParents::dynamic_signature();
    let outer = signature.type_named("Outer").unwrap();
    let inner = signature.type_named("Outer::Inner").unwrap();
    let el = signature.type_named("Outer::Inner::El").unwrap();
    let membership = signature
        .relation_named("Outer::Inner::inner_member_el")
        .unwrap();
    let mut model = Model::new(signature);
    let a = model.new_element(outer, &[]).unwrap();
    let b = model.new_element(outer, &[]).unwrap();
    let i = model.new_element(inner, &[a]).unwrap();
    let j = model.new_element(inner, &[b]).unwrap();
    let x = model.new_element(el, &[a, i]).unwrap();
    let y = model.new_element(el, &[b, j]).unwrap();
    assert_eq!(model.new_element(el, &[b, i]), Err(Error::ParentMismatch));
    assert_eq!(
        model.insert(membership, &[b, j, x]),
        Err(Error::ParentMismatch)
    );
    assert_eq!(model.equate(&[a, i], x, y), Err(Error::ParentMismatch));
    assert_eq!(model.equate(&[b, j], x, x), Err(Error::ParentMismatch));
    assert_eq!(model.elements(el).unwrap().count(), 2);
    model.equate(&[], a, b).unwrap();
    model.equate(&[b], i, j).unwrap();
    model.equate(&[b, j], x, y).unwrap();
    assert!(model.contains(membership, &[a, i, y]).unwrap());
    let restored = MemberParents::from_dynamic(&model).unwrap();
    assert_eq!(restored.iter_el().count(), 1);
    round_trip(&restored);
}

#[test]
fn dynamic_import_preserves_enum_elements_without_constructors() {
    let signature = Nat::dynamic_signature();
    let type_ = signature.type_named("N").unwrap();
    let mut dynamic = Model::new(signature);
    let element = dynamic.new_element(type_, &[]).unwrap();
    let compiled = Nat::from_dynamic(&dynamic).unwrap();
    assert_eq!(compiled.iter_n().count(), 1);
    assert_eq!(compiled.iter_zero().count(), 0);
    assert_eq!(compiled.iter_succ().count(), 0);
    let exported = compiled.to_dynamic();
    assert_eq!(
        exported.elements(type_).unwrap().collect::<Vec<_>>(),
        vec![element]
    );
    round_trip(&compiled);
}

#[test]
fn dynamic_import_preserves_applications_without_endpoints() {
    let signature = MorphismPreservation::dynamic_signature();
    let world = signature.type_named("World").unwrap();
    let el = signature.type_named("World::El").unwrap();
    let mor = signature.type_named("WorldMor").unwrap();
    let application = signature.relation_named("el_mor_app").unwrap();
    let mut dynamic = Model::new(signature);
    let a = dynamic.new_element(world, &[]).unwrap();
    let b = dynamic.new_element(world, &[]).unwrap();
    let x = dynamic.new_element(el, &[a]).unwrap();
    let y = dynamic.new_element(el, &[b]).unwrap();
    let h = dynamic.new_element(mor, &[]).unwrap();
    dynamic.insert(application, &[h, x, y]).unwrap();
    let compiled = MorphismPreservation::from_dynamic(&dynamic).unwrap();
    assert_eq!(compiled.iter_world_mor_dom().count(), 0);
    assert_eq!(compiled.iter_world_mor_cod().count(), 0);
    assert_eq!(compiled.iter_el_mor_app().count(), 1);
    let exported = compiled.to_dynamic();
    assert!(exported.contains(application, &[h, x, y]).unwrap());
    round_trip(&compiled);
}

#[test]
fn dynamic_import_requires_the_same_descriptor_order() {
    let signature = Logic::dynamic_signature();
    let types = signature.types().map(|(_, type_)| type_.clone()).collect();
    let mut relations: Vec<_> = signature
        .relations()
        .map(|(_, relation)| relation.clone())
        .collect();
    relations.reverse();
    let reordered = Signature::new(types, relations).unwrap();
    let dynamic = Model::new(Arc::new(reordered));
    assert_eq!(
        Logic::from_dynamic(&dynamic).err(),
        Some(Error::SignatureMismatch)
    );
}

#[test]
fn conversions_preserve_ids_and_mutate_independently() {
    let mut compiled = PartialMagma::new();
    let alias = compiled.new_el();
    let root = compiled.new_el();
    let isolated = compiled.new_el();
    compiled.insert_mul(root, root, alias);
    compiled.equate_el(alias, root);
    assert_eq!(compiled.root_el(alias), root);
    let mut dynamic = compiled.to_dynamic();
    let type_ = dynamic.signature().type_named("El").unwrap();
    let mul = dynamic.signature().relation_named("mul").unwrap();
    let alias_handle = handle::<PartialMagma>("El", alias.0);
    let root_handle = handle::<PartialMagma>("El", root.0);
    let isolated_handle = handle::<PartialMagma>("El", isolated.0);
    assert_eq!(dynamic.root(alias_handle).unwrap(), root_handle);
    assert_eq!(
        dynamic.tuples(mul).unwrap().collect::<Vec<_>>(),
        vec![vec![root_handle, root_handle, alias_handle]]
    );
    let mut restored = round_trip(&compiled);
    assert_eq!(restored.root_el(alias), root);
    assert_eq!(restored.root_el(isolated), isolated);
    assert_eq!(restored.new_el().0, 3);

    compiled.insert_mul(root, isolated, isolated);
    assert_eq!(dynamic.tuples(mul).unwrap().count(), 1);
    dynamic
        .insert(mul, &[isolated_handle, isolated_handle, root_handle])
        .unwrap();
    assert_eq!(restored.iter_mul().count(), 1);
    dynamic.equate(&[], root_handle, isolated_handle).unwrap();
    assert_eq!(restored.root_el(isolated), isolated);
    restored.insert_mul(isolated, root, root);
    assert_eq!(dynamic.tuples(mul).unwrap().count(), 2);
    assert_eq!(dynamic.new_element(type_, &[]).unwrap().index, 3);
}

#[test]
fn import_rebuilds_diagonals_before_pending_equalities_are_processed() {
    for closed in [false, true] {
        let mut source = DiagonalCanonicalization::new();
        let x = source.new_t();
        let y = source.new_t();
        let a = source.new_t();
        let b = source.new_t();
        source.insert_pair(x, x, y, y);
        source.insert_pair(x, a, y, y);
        source.insert_pair(b, b, b, b);
        source.insert_value(x, x, y, y);
        source.insert_value(x, a, y, y);
        source.insert_value(b, b, b, b);
        if closed {
            source.close();
        }
        source.equate_t(b, a);
        let mut restored = round_trip(&source);
        restored.insert_gate();
        restored.close();
        assert!(restored.matched_pair(x, y));
        assert!(restored.matched_value(x, y));
        assert!(restored.pair(x, b, y, y));
        assert_eq!(restored.value(x, b, y), Some(y));
    }
}
