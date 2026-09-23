use std::collections::BTreeSet;
use std::panic::{catch_unwind, AssertUnwindSafe};

use eqlog_runtime::{
    CompiledModel, Element, EnumCase, Error, FunctionKind, Model, RelationKind, Signature, TypeKind,
};
use std::sync::Arc;

use crate::consts::Consts;
use crate::diagonal_canonicalization::DiagonalCanonicalization;
use crate::empty::Empty;
use crate::logic::Logic;
use crate::member_parents::MemberParents;
use crate::morphism_preservation::MorphismPreservation;
use crate::nat::{NCase, Nat};
use crate::nested_image_creation::NestedImageCreation;
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
fn compiled_signatures_are_shared_by_models() {
    let signature: &'static Signature = TransRefl::dynamic_signature();
    let exported = TransRefl::new().to_dynamic();
    let constructed = Model::new(signature);
    let cloned = exported.clone();
    assert!(std::ptr::eq(signature, TransRefl::dynamic_signature()));
    for model in [&exported, &constructed, &cloned] {
        assert!(std::ptr::eq(signature, model.signature()));
    }

    let mut owned = Model::with_signature(Arc::new(signature.clone()));
    let type_ = signature.type_named("V").unwrap();
    let edge = signature.relation_named("edge").unwrap();
    let x = owned.new_element(type_, &[]).unwrap();
    owned.insert(edge, &[x, x]).unwrap();
    let compiled = TransRefl::from_dynamic(&owned).unwrap();
    assert!(compiled.edge(V(x.index), V(x.index)));
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
    let dynamic = model.to_dynamic();
    let signature = dynamic.signature();
    let zero_constructor = signature.relation_named("Zero").unwrap();
    let succ_constructor = signature.relation_named("Succ").unwrap();
    let expected: Vec<_> = model
        .n_cases(zero)
        .map(|case| match case {
            NCase::Zero() => EnumCase {
                constructor: zero_constructor,
                arguments: vec![],
            },
            NCase::Succ(n) => EnumCase {
                constructor: succ_constructor,
                arguments: vec![handle::<Nat>("N", n.0)],
            },
        })
        .collect();
    assert_eq!(
        dynamic
            .cases(handle::<Nat>("N", zero.0))
            .unwrap()
            .collect::<Vec<_>>(),
        expected
    );
    assert_eq!(
        dynamic.case(handle::<Nat>("N", one.0)).unwrap(),
        expected[0]
    );
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
fn dynamic_enum_construction_reuses_values_and_exposes_cases() {
    let signature = Nat::dynamic_signature();
    let type_ = signature.type_named("N").unwrap();
    let zero = signature.relation_named("Zero").unwrap();
    let succ = signature.relation_named("Succ").unwrap();
    let plus = signature.relation_named("plus").unwrap();
    let mut dynamic = Model::new(signature);
    assert_eq!(
        dynamic.new_element(type_, &[]),
        Err(Error::ConstructorRequired(type_))
    );
    let zero_case = EnumCase {
        constructor: zero,
        arguments: vec![],
    };
    let z = dynamic.new_enum(zero_case.clone()).unwrap();
    let succ_case = EnumCase {
        constructor: succ,
        arguments: vec![z],
    };
    let s = dynamic.new_enum(succ_case.clone()).unwrap();
    assert_eq!(dynamic.new_enum(zero_case.clone()).unwrap(), z);
    assert_eq!(dynamic.new_enum(succ_case.clone()).unwrap(), s);
    assert_eq!(dynamic.eval(succ, &[z]).unwrap(), Some(s));
    assert_eq!(dynamic.case(z).unwrap(), zero_case);
    assert_eq!(
        dynamic.cases(s).unwrap().collect::<Vec<_>>(),
        vec![succ_case]
    );
    assert_eq!(
        dynamic.define(plus, &[z, s]),
        Err(Error::ConstructorRequired(type_))
    );
    assert_eq!(
        dynamic.new_enum(EnumCase {
            constructor: plus,
            arguments: vec![z, s]
        }),
        Err(Error::ExpectedConstructor(plus))
    );
    assert_eq!(dynamic.elements(type_).unwrap().count(), 2);
    let mut compiled = Nat::from_dynamic(&dynamic).unwrap();
    let compiled_zero = compiled.define_zero();
    let compiled_succ = compiled.define_succ(compiled_zero);
    assert_eq!(compiled_zero.0, z.index);
    assert_eq!(compiled_succ.0, s.index);
    assert_eq!(compiled.n_cases(compiled_succ).count(), 1);
    round_trip(&compiled);
}

#[test]
fn dynamic_direct_morphism_checks_endpoints_and_defines_its_target() {
    let mut compiled = MorphismPreservation::new();
    let a = compiled.new_world();
    let b = compiled.new_world();
    let x = compiled.new_el(a);
    let y = compiled.new_el(b);
    let h = compiled.new_world_mor();
    let mut dynamic = compiled.to_dynamic();
    let signature = dynamic.signature();
    let dom = signature.relation_named("world_mor_dom").unwrap();
    let cod = signature.relation_named("world_mor_cod").unwrap();
    let application = signature.relation_named("el_mor_app").unwrap();
    let a_el = handle::<MorphismPreservation>("World", a.0);
    let x_el = handle::<MorphismPreservation>("World::El", x.0);
    let y_el = handle::<MorphismPreservation>("World::El", y.0);
    let h_el = handle::<MorphismPreservation>("WorldMor", h.0);
    assert_eq!(
        dynamic.eval(application, &[h_el, x_el]),
        Err(Error::UndefinedFunction(dom))
    );
    assert_eq!(
        dynamic.insert(application, &[h_el, x_el, y_el]),
        Err(Error::UndefinedFunction(dom))
    );
    assert!(catch_unwind(AssertUnwindSafe(|| compiled.el_mor_app(h, x))).is_err());
    compiled.insert_world_mor_dom(h, a);
    dynamic.insert(dom, &[h_el, a_el]).unwrap();
    assert_eq!(dynamic.eval(application, &[h_el, x_el]).unwrap(), None);
    assert_eq!(compiled.el_mor_app(h, x), None);
    assert_eq!(
        dynamic.insert(application, &[h_el, x_el, y_el]),
        Err(Error::UndefinedFunction(cod))
    );
    let image = compiled.define_el_mor_app(h, x);
    let image_el = dynamic.define(application, &[h_el, x_el]).unwrap();
    assert_eq!(image_el.index, image.0);
    let target = compiled.world_mor_cod(h).unwrap();
    assert_eq!(
        dynamic.eval(cod, &[h_el]).unwrap(),
        Some(handle::<MorphismPreservation>("World", target.0))
    );
    assert!(compiled.world_member_el(target, image));
    assert_eq!(
        dynamic.define(application, &[h_el, x_el]).unwrap(),
        image_el
    );
    assert_eq!(
        dynamic.eval(application, &[h_el, y_el]),
        Err(Error::ParentMismatch)
    );
    assert_eq!(
        dynamic.insert(application, &[h_el, x_el, y_el]),
        Err(Error::ParentMismatch)
    );
    assert_eq!(dynamic.tuples(application).unwrap().count(), 1);
    let restored = MorphismPreservation::from_dynamic(&dynamic).unwrap();
    assert_eq!(restored.el_mor_app(h, x), Some(image));
    round_trip(&restored);
}

#[test]
fn dynamic_functions_match_compiled_lookups_with_pending_aliases() {
    let mut compiled = PartialMagma::new();
    let x = compiled.new_el();
    let alias = compiled.new_el();
    let y = compiled.new_el();
    let result = compiled.new_el();
    compiled.insert_mul(alias, y, result);
    compiled.insert_mul(x, x, x);
    compiled.equate_el(x, alias);
    let mut dynamic = compiled.to_dynamic();
    let mul = dynamic.signature().relation_named("mul").unwrap();
    let element = |index| handle::<PartialMagma>("El", index);
    assert!(dynamic.are_equal(element(x.0), element(alias.0)).unwrap());
    assert!(!dynamic.are_equal(element(x.0), element(y.0)).unwrap());
    assert_eq!(compiled.mul(alias, y), None);
    assert_eq!(
        dynamic
            .eval(mul, &[element(alias.0), element(y.0)])
            .unwrap(),
        None
    );
    let defined = compiled.define_mul(alias, y);
    let dynamic_defined = dynamic
        .define(mul, &[element(alias.0), element(y.0)])
        .unwrap();
    assert_eq!(dynamic_defined, element(defined.0));
    assert_eq!(
        dynamic.define(mul, &[element(x.0), element(y.0)]).unwrap(),
        dynamic_defined
    );
    compiled.equate_el(result, defined);
    dynamic
        .equate(&[], element(result.0), dynamic_defined)
        .unwrap();
    assert_eq!(
        dynamic.eval(mul, &[element(x.0), element(y.0)]).unwrap(),
        compiled.mul(x, y).map(|value| element(value.0))
    );
    assert_ne!(compiled.root_el(defined), defined);
    assert_eq!(
        dynamic.eval(mul, &[element(x.0), element(y.0)]).unwrap(),
        Some(dynamic_defined)
    );
    assert!(dynamic
        .are_equal(element(result.0), dynamic_defined)
        .unwrap());
    round_trip(&PartialMagma::from_dynamic(&dynamic).unwrap());
}

#[test]
fn dynamic_function_evaluation_prefers_new_results_to_old_results() {
    let mut compiled = PartialMagma::new();
    let x = compiled.new_el();
    let y = compiled.new_el();
    let old_result = compiled.new_el();
    compiled.insert_mul(x, y, old_result);
    compiled.close();
    let new_result = compiled.new_el();
    compiled.insert_mul(x, y, new_result);
    assert!(new_result.0 > old_result.0);
    assert_eq!(compiled.mul(x, y), Some(new_result));
    let mut dynamic = compiled.to_dynamic();
    let mul = dynamic.signature().relation_named("mul").unwrap();
    let args = [
        handle::<PartialMagma>("El", x.0),
        handle::<PartialMagma>("El", y.0),
    ];
    let expected = handle::<PartialMagma>("El", new_result.0);
    assert_eq!(dynamic.eval(mul, &args).unwrap(), Some(expected));
    assert_eq!(dynamic.define(mul, &args).unwrap(), expected);
    assert_eq!(dynamic.tuples(mul).unwrap().count(), 2);
}

#[test]
fn dynamic_constants_are_defined_without_running_rules() {
    let mut compiled = Consts::new();
    let mut dynamic = compiled.to_dynamic();
    let signature = dynamic.signature();
    let foo = signature.relation_named("foo").unwrap();
    let main = signature.relation_named("main_container").unwrap();
    let inner = signature.relation_named("Container::inner").unwrap();
    let present = signature.relation_named("present").unwrap();
    assert_eq!(dynamic.eval(foo, &[]).unwrap(), None);
    assert_eq!(
        dynamic.eval(present, &[]),
        Err(Error::ExpectedFunction(present))
    );
    assert_eq!(
        dynamic.define(present, &[]),
        Err(Error::ExpectedFunction(present))
    );
    let value = dynamic.define(foo, &[]).unwrap();
    assert_eq!(value.index, compiled.define_foo().0);
    assert_eq!(dynamic.define(foo, &[]).unwrap(), value);
    assert!(!dynamic.contains(present, &[value]).unwrap());
    let container = dynamic.define(main, &[]).unwrap();
    let compiled_container = compiled.define_main_container();
    assert_eq!(container.index, compiled_container.0);
    let member = dynamic.define(inner, &[container]).unwrap();
    assert_eq!(member.index, compiled.define_inner(compiled_container).0);
    assert_eq!(dynamic.eval(inner, &[container]).unwrap(), Some(member));
    assert_eq!(
        dynamic.are_equal(value, container),
        Err(Error::TypeMismatch {
            expected: value.type_,
            actual: container.type_
        })
    );
    let restored = Consts::from_dynamic(&dynamic).unwrap();
    assert!(!restored.present(crate::consts::El(value.index)));
    round_trip(&restored);
}

#[test]
fn dynamic_predicates_and_functions_reject_members_of_other_models() {
    let mut compiled = MorphismPreservation::new();
    let a = compiled.new_world();
    let b = compiled.new_world();
    let x = compiled.new_el(a);
    let y = compiled.new_el(b);
    let label = compiled.new_ambient();
    let mut dynamic = compiled.to_dynamic();
    let tagged = dynamic.signature().relation_named("World::tagged").unwrap();
    let edge = dynamic.signature().relation_named("World::edge").unwrap();
    let a_el = handle::<MorphismPreservation>("World", a.0);
    let b_el = handle::<MorphismPreservation>("World", b.0);
    let x_el = handle::<MorphismPreservation>("World::El", x.0);
    let y_el = handle::<MorphismPreservation>("World::El", y.0);
    let label_el = handle::<MorphismPreservation>("Ambient", label.0);
    assert_eq!(
        dynamic.insert(tagged, &[b_el, x_el, label_el]),
        Err(Error::ParentMismatch)
    );
    assert_eq!(
        dynamic.contains(tagged, &[b_el, x_el, label_el]),
        Err(Error::ParentMismatch)
    );
    assert!(catch_unwind(AssertUnwindSafe(|| compiled.tagged(b, x, label))).is_err());
    assert_eq!(
        dynamic.eval(edge, &[b_el, x_el]),
        Err(Error::ParentMismatch)
    );
    assert_eq!(
        dynamic.define(edge, &[b_el, x_el]),
        Err(Error::ParentMismatch)
    );
    assert_eq!(
        dynamic.insert(edge, &[a_el, x_el, y_el]),
        Err(Error::ParentMismatch)
    );
    assert!(catch_unwind(AssertUnwindSafe(|| compiled.insert_edge(a, x, y))).is_err());
    assert_eq!(dynamic.tuples(tagged).unwrap().count(), 0);
    assert_eq!(dynamic.tuples(edge).unwrap().count(), 0);
    compiled.insert_tagged(a, x, label);
    dynamic.insert(tagged, &[a_el, x_el, label_el]).unwrap();
    assert_eq!(
        dynamic.define(edge, &[a_el, x_el]).unwrap().index,
        compiled.define_edge(a, x).0
    );
    compiled.equate_world(a, b);
    dynamic.equate(&[], a_el, b_el).unwrap();
    assert_eq!(
        dynamic.contains(tagged, &[b_el, x_el, label_el]).unwrap(),
        compiled.tagged(b, x, label)
    );
    round_trip(&MorphismPreservation::from_dynamic(&dynamic).unwrap());
}

#[test]
fn dynamic_nested_morphisms_require_each_parent_image() {
    let mut compiled = NestedImageCreation::new();
    let source = compiled.new_m();
    let target = compiled.new_m();
    let n = compiled.new_n(source);
    let o = compiled.new_o(source, n);
    let x = compiled.new_u(source, n, o);
    let wrong_n = compiled.new_n(target);
    let wrong_o = compiled.new_o(target, wrong_n);
    let wrong_x = compiled.new_u(target, wrong_n, wrong_o);
    let h = compiled.new_m_mor();
    compiled.insert_m_mor_dom(h, source);
    compiled.insert_m_mor_cod(h, target);
    let mut dynamic = compiled.to_dynamic();
    let signature = dynamic.signature();
    let n_app = signature.relation_named("n_mor_app").unwrap();
    let o_app = signature.relation_named("m_o_mor_app").unwrap();
    let u_app = signature.relation_named("m_u_mor_app").unwrap();
    let h_el = handle::<NestedImageCreation>("MMor", h.0);
    let n_el = handle::<NestedImageCreation>("M::N", n.0);
    let o_el = handle::<NestedImageCreation>("M::N::O", o.0);
    let x_el = handle::<NestedImageCreation>("M::N::O::U", x.0);
    let wrong_el = handle::<NestedImageCreation>("M::N::O::U", wrong_x.0);
    assert_eq!(dynamic.eval(u_app, &[h_el, x_el]).unwrap(), None);
    assert_eq!(compiled.m_u_mor_app(h, x), None);
    assert_eq!(
        dynamic.define(u_app, &[h_el, x_el]),
        Err(Error::UndefinedFunction(n_app))
    );
    assert_eq!(
        dynamic.insert(u_app, &[h_el, x_el, wrong_el]),
        Err(Error::UndefinedFunction(n_app))
    );
    assert!(catch_unwind(AssertUnwindSafe(|| compiled.define_m_u_mor_app(h, x))).is_err());
    let image_n = compiled.define_n_mor_app(h, n);
    assert_eq!(
        dynamic.define(n_app, &[h_el, n_el]).unwrap().index,
        image_n.0
    );
    assert_eq!(
        dynamic.define(u_app, &[h_el, x_el]),
        Err(Error::UndefinedFunction(o_app))
    );
    let image_o = compiled.define_m_o_mor_app(h, o);
    assert_eq!(
        dynamic.define(o_app, &[h_el, o_el]).unwrap().index,
        image_o.0
    );
    assert_eq!(
        dynamic.insert(u_app, &[h_el, x_el, wrong_el]),
        Err(Error::ParentMismatch)
    );
    let image_x = compiled.define_m_u_mor_app(h, x);
    let image_el = dynamic.define(u_app, &[h_el, x_el]).unwrap();
    assert_eq!(image_el.index, image_x.0);
    assert_eq!(dynamic.define(u_app, &[h_el, x_el]).unwrap(), image_el);
    assert_eq!(
        dynamic.eval(u_app, &[h_el, wrong_el]),
        Err(Error::ParentMismatch)
    );
    assert!(compiled.o_member_u(target, image_n, image_o, image_x));
    let restored = NestedImageCreation::from_dynamic(&dynamic).unwrap();
    assert!(restored.o_member_u(target, image_n, image_o, image_x));
    round_trip(&restored);
}

#[test]
fn dynamic_nested_morphisms_keep_the_enclosing_model() {
    let mut compiled = NestedImageCreation::new();
    let a = compiled.new_m();
    let b = compiled.new_m();
    let source = compiled.new_n(a);
    let target = compiled.new_n(a);
    let o = compiled.new_o(a, source);
    let x = compiled.new_u(a, source, o);
    let f = compiled.new_n_mor(a);
    compiled.insert_n_mor_dom(a, f, source);
    compiled.insert_n_mor_cod(a, f, target);
    let mut dynamic = compiled.to_dynamic();
    let o_app = dynamic.signature().relation_named("M::o_mor_app").unwrap();
    let u_app = dynamic
        .signature()
        .relation_named("M::n_u_mor_app")
        .unwrap();
    let a_el = handle::<NestedImageCreation>("M", a.0);
    let b_el = handle::<NestedImageCreation>("M", b.0);
    let f_el = handle::<NestedImageCreation>("M::NMor", f.0);
    let o_el = handle::<NestedImageCreation>("M::N::O", o.0);
    let x_el = handle::<NestedImageCreation>("M::N::O::U", x.0);
    assert_eq!(
        dynamic.eval(u_app, &[b_el, f_el, x_el]),
        Err(Error::ParentMismatch)
    );
    assert!(catch_unwind(AssertUnwindSafe(|| compiled.n_u_mor_app(b, f, x))).is_err());
    assert_eq!(
        dynamic.define(u_app, &[a_el, f_el, x_el]),
        Err(Error::UndefinedFunction(o_app))
    );
    let image_o = compiled.define_o_mor_app(a, f, o);
    assert_eq!(
        dynamic.define(o_app, &[a_el, f_el, o_el]).unwrap().index,
        image_o.0
    );
    let image_x = compiled.define_n_u_mor_app(a, f, x);
    assert_eq!(
        dynamic.define(u_app, &[a_el, f_el, x_el]).unwrap().index,
        image_x.0
    );
    let restored = NestedImageCreation::from_dynamic(&dynamic).unwrap();
    assert!(restored.o_member_u(a, target, image_o, image_x));
    round_trip(&restored);
}

#[test]
fn dynamic_enum_cases_include_enclosing_models() {
    let mut compiled = MemberParents::new();
    let a = compiled.new_outer();
    let b = compiled.new_outer();
    let inner = compiled.new_inner(a);
    let mut dynamic = compiled.to_dynamic();
    let constructor = dynamic
        .signature()
        .relation_named("Outer::Inner::LabelValue")
        .unwrap();
    let label_type = dynamic
        .signature()
        .type_named("Outer::Inner::Label")
        .unwrap();
    let a_el = handle::<MemberParents>("Outer", a.0);
    let b_el = handle::<MemberParents>("Outer", b.0);
    let inner_el = handle::<MemberParents>("Outer::Inner", inner.0);
    assert_eq!(
        dynamic.new_element(label_type, &[a_el, inner_el]),
        Err(Error::ConstructorRequired(label_type))
    );
    assert_eq!(
        dynamic.new_enum(EnumCase {
            constructor,
            arguments: vec![b_el, inner_el]
        }),
        Err(Error::ParentMismatch)
    );
    let case = EnumCase {
        constructor,
        arguments: vec![a_el, inner_el],
    };
    let label = dynamic.new_enum(case.clone()).unwrap();
    assert_eq!(label.index, compiled.define_label_value(a, inner).0);
    assert_eq!(dynamic.new_enum(case.clone()).unwrap(), label);
    assert_eq!(dynamic.case(label).unwrap(), case);
    assert_eq!(dynamic.cases(label).unwrap().count(), 1);
    assert_eq!(
        dynamic.cases(a_el).err(),
        Some(Error::ExpectedEnum(a_el.type_))
    );
    assert_eq!(dynamic.case(a_el), Err(Error::ExpectedEnum(a_el.type_)));
    assert_eq!(dynamic.elements(label_type).unwrap().count(), 1);
    round_trip(&MemberParents::from_dynamic(&dynamic).unwrap());
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
    let dynamic = Model::with_signature(Arc::new(reordered));
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
