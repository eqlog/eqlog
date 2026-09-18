use std::collections::BTreeSet;

use eqlog_runtime::dynamic::{
    CompiledModel, DynamicModel, Element, ElementMap, Error, FunctionKind, RelationKind, SortKind,
};

use crate::consts::Consts;
use crate::empty::Empty;
use crate::logic::Logic;
use crate::member_parents::MemberParents;
use crate::morphism_preservation::MorphismPreservation;
use crate::nat::Nat;
use crate::partial_magma::{El, PartialMagma};
use crate::trans_refl::{TransRefl, V};

fn handle<M: CompiledModel>(sort: &str, index: u32) -> Element {
    Element {
        sort: M::dynamic_signature().sort_named(sort).unwrap(),
        index,
    }
}

fn round_trip<M: CompiledModel>(source: &M) -> (M, ElementMap) {
    let (before, export) = source.to_dynamic();
    let (restored, import) = M::from_dynamic(&before).unwrap();
    let (after, second_export) = restored.to_dynamic();
    assert_eq!(before.signature(), after.signature());
    let map = |el: &Element| second_export[&import[el]];
    for (sort, _) in before.signature().sorts() {
        let expected: BTreeSet<_> = before.elements(sort).unwrap().map(|el| map(&el)).collect();
        let actual: BTreeSet<_> = after.elements(sort).unwrap().collect();
        assert_eq!(expected, actual);
        for el in before.elements(sort).unwrap() {
            let parents: Vec<_> = before.parents(el).unwrap().iter().map(map).collect();
            assert_eq!(parents, after.parents(map(&el)).unwrap());
        }
    }
    for (relation, _) in before.signature().relations() {
        let expected: BTreeSet<Vec<_>> = before
            .tuples(relation)
            .unwrap()
            .map(|tuple| tuple.iter().map(map).collect())
            .collect();
        let actual: BTreeSet<_> = after.tuples(relation).unwrap().collect();
        assert_eq!(expected, actual);
    }
    let correspondence = export
        .into_iter()
        .map(|(source, dynamic)| (source, import[&dynamic]))
        .collect();
    (restored, correspondence)
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
    let (mut restored, map) = round_trip(&model);
    let x = V(map[&handle::<TransRefl>("V", x.0)].index);
    let z = V(map[&handle::<TransRefl>("V", z.0)].index);
    let isolated = V(map[&handle::<TransRefl>("V", isolated.0)].index);
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
    let (mut restored, map) = round_trip(&model);
    assert_eq!(
        map[&handle::<PartialMagma>("El", x.0)],
        map[&handle::<PartialMagma>("El", alias.0)]
    );
    let y = El(map[&handle::<PartialMagma>("El", y.0)].index);
    let z = El(map[&handle::<PartialMagma>("El", z.0)].index);
    assert!(!restored.are_equal_el(y, z));
    assert_eq!(restored.iter_mul().count(), 2);
    restored.close();
    assert!(restored.are_equal_el(y, z));
    assert_eq!(restored.iter_mul().count(), 1);
}

#[test]
fn dynamic_construction_and_aliases_survive_import() {
    let signature = TransRefl::dynamic_signature();
    let sort = signature.sort_named("V").unwrap();
    let edge = signature.relation_named("edge").unwrap();
    let mut model = DynamicModel::new(signature);
    let x = model.new_element(sort, &[]).unwrap();
    let alias = model.new_element(sort, &[]).unwrap();
    let y = model.new_element(sort, &[]).unwrap();
    model.insert(edge, &[alias, y]).unwrap();
    model.equate(alias, x).unwrap();
    let (mut compiled, map) = TransRefl::from_dynamic(&model).unwrap();
    assert_eq!(map[&x], map[&alias]);
    let x = V(map[&x].index);
    let y = V(map[&y].index);
    assert!(compiled.edge(x, y));
    assert!(!compiled.edge(y, y));
    compiled.close();
    assert!(compiled.edge(y, y));
}

#[test]
fn dynamic_nested_ownership_survives_pending_parent_equalities() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let b = model.new_outer();
    let i = model.new_inner(a);
    let j = model.new_inner(b);
    let x = model.new_el(a, i);
    let y = model.new_el(b, j);
    model.define_label_value(a, i);
    model.define_label_value(b, j);
    model.close();
    model.equate_outer(a, b);
    model.equate_inner(i, j);
    model.equate_el(x, y);
    let (mut restored, _) = round_trip(&model);
    assert_eq!(restored.iter_outer().count(), 1);
    assert_eq!(restored.iter_inner().count(), 1);
    assert_eq!(restored.iter_el().count(), 1);
    assert_eq!(restored.iter_label().count(), 2);
    restored.close();
    assert_eq!(restored.iter_label().count(), 1);
    round_trip(&restored);
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
    let (before, _) = round_trip(&model);
    assert_eq!(before.iter_tagged().count(), 1);
    assert_eq!(before.iter_ready().count(), 1);
    model.close();
    assert!(model.tagged(b, y, label));
    let late_label = model.new_ambient();
    model.insert_tagged(a, x, late_label);
    let (mut restored, _) = round_trip(&model);
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
    let (restored, _) = round_trip(&model);
    assert_eq!(restored.iter_n().count(), 1);
    assert_eq!(restored.iter_zero().count(), 1);
    assert_eq!(restored.iter_succ().count(), 1);
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
    let (mut restored, _) = round_trip(&Consts::new());
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
    let (mut restored, _) = round_trip(&model);
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
    let world = signature.sort_named("World").unwrap();
    let morphism = signature.sort_named("WorldMor").unwrap();
    let item = signature.sort_named("World::Inner::Item").unwrap();
    let application = signature.relation_named("world_item_mor_app").unwrap();
    assert_eq!(
        signature.sort(morphism).unwrap().kind,
        SortKind::Morphism(world)
    );
    assert_eq!(
        signature.relation(application).unwrap().kind,
        RelationKind::Function(FunctionKind::MorphismApplication {
            morphism,
            member: item
        })
    );
    let error = PartialMagma::from_dynamic(&DynamicModel::new(signature))
        .err()
        .unwrap();
    assert_eq!(error, Error::SignatureMismatch);
}

#[test]
fn dynamic_checks_parent_chains_before_mutation() {
    let signature = MemberParents::dynamic_signature();
    let outer = signature.sort_named("Outer").unwrap();
    let inner = signature.sort_named("Outer::Inner").unwrap();
    let el = signature.sort_named("Outer::Inner::El").unwrap();
    let membership = signature
        .relation_named("Outer::Inner::inner_member_el")
        .unwrap();
    let mut model = DynamicModel::new(signature);
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
    assert_eq!(model.equate(x, y), Err(Error::ParentMismatch));
    assert_eq!(model.elements(el).unwrap().count(), 2);
    model.equate(a, b).unwrap();
    model.equate(i, j).unwrap();
    model.equate(x, y).unwrap();
    assert_eq!(
        model.parents(y).unwrap(),
        vec![model.root(a).unwrap(), model.root(i).unwrap()]
    );
    let (restored, _) = MemberParents::from_dynamic(&model).unwrap();
    assert_eq!(restored.iter_el().count(), 1);
    round_trip(&restored);
}
