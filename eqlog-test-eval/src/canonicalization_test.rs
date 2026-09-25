use std::collections::BTreeSet;

use eqlog_runtime::__private::{from_parts, relation_data, type_data, Table};
use eqlog_runtime::{CompiledModel, Error, Model};

use crate::canonicalization::Canonicalization;
use crate::member_parents::MemberParents;
use crate::morphism_preservation::MorphismPreservation;

fn assert_same_pending_work(left: &Model, right: &Model) {
    assert!(left.is_canonical());
    assert!(right.is_canonical());
    assert_eq!(left.signature(), right.signature());
    for (type_, _) in left.signature().types() {
        let left = type_data(left, type_).unwrap();
        let right = type_data(right, type_).unwrap();
        assert_eq!(
            left.new.iter().collect::<Vec<_>>(),
            right.new.iter().collect::<Vec<_>>()
        );
        assert_eq!(
            left.old.iter().collect::<Vec<_>>(),
            right.old.iter().collect::<Vec<_>>()
        );
        assert!(left.uprooted.is_empty());
        assert!(right.uprooted.is_empty());
    }
    for (relation, _) in left.signature().relations() {
        let left = relation_data(left, relation).unwrap();
        let right = relation_data(right, relation).unwrap();
        assert_eq!(
            left.new.tuples().collect::<BTreeSet<_>>(),
            right.new.tuples().collect()
        );
        assert_eq!(
            left.old.tuples().collect::<BTreeSet<_>>(),
            right.old.tuples().collect()
        );
    }
}

#[test]
fn canonicalization_preserves_matches_across_closure_and_external_edits() {
    for close_before_merge in [false, true] {
        let mut model = Canonicalization::new();
        let x = model.new_v();
        let y = model.new_v();
        model.insert_p(x);
        model.insert_q(y);
        model.insert_edge(x, y);
        if close_before_merge {
            model.close();
        }
        model.equate_v(x, y);
        let z = model.new_v();
        model.insert_p(z);
        let mut dynamic = model.to_dynamic();
        assert!(!dynamic.is_canonical());

        dynamic.canonicalize();
        let once = dynamic.clone();
        dynamic.canonicalize();
        assert_same_pending_work(&once, &dynamic);
        model.canonicalize();
        assert_same_pending_work(&model.to_dynamic(), &dynamic);
        model.canonicalize();
        assert_same_pending_work(&model.to_dynamic(), &dynamic);
        assert!(!model.joined(x));
        assert!(!model.loop_at(x));

        model.insert_gate();
        model.close();
        assert!(model.joined(x));
        assert!(model.loop_at(y));
        assert!(model.gated(y));
        assert!(!model.gated(z));

        model.insert_q(z);
        model.canonicalize();
        model.close();
        assert!(model.gated(z));
        model.equate_v(y, z);
        model.canonicalize();
        model.canonicalize();
        model.close();
        assert_eq!(model.iter_gated().count(), 1);
    }
}

#[test]
fn dynamic_canonicalization_preserves_old_collisions_and_physical_column_orders() {
    let signature = Canonicalization::dynamic_signature();
    let mut model = Canonicalization::new();
    let x = model.new_v();
    let y = model.new_v();
    let z = model.new_v();
    model.insert_edge(x, z);
    model.insert_edge(y, z);
    model.insert_gate();
    model.close();
    model.equate_v(x, y);
    let root = model.root_v(x).0;
    let alias = if root == x.0 { y.0 } else { x.0 };
    let snapshot = model.to_dynamic();
    let types = signature
        .types()
        .map(|(id, _)| type_data(&snapshot, id).unwrap().clone())
        .collect();
    let mut relations: Vec<_> = signature
        .relations()
        .map(|(id, _)| relation_data(&snapshot, id).unwrap().clone())
        .collect();
    let edge = signature.relation_named("edge").unwrap();
    let data = &mut relations[edge.0];
    data.old.order = vec![1, 0];
    data.old.table = Table::new(2);
    data.old.table.insert(&[z.0, root]);
    data.old.table.insert(&[z.0, alias]);
    data.old.table.insert(&[alias, z.0]);
    data.new.table.insert(&[root, z.0]);
    data.new.table.insert(&[alias, root]);
    let gate = signature.relation_named("gate").unwrap();
    relations[gate.0].new.table.insert(&[]);
    let mut dynamic = from_parts(signature, types, relations).unwrap();
    assert!(!dynamic.is_canonical());
    dynamic.canonicalize();

    let edge_data = relation_data(&dynamic, edge).unwrap();
    assert_eq!(edge_data.old.order, [1, 0]);
    assert_eq!(edge_data.new.order, [0, 1]);
    assert_eq!(
        edge_data.old.tuples().collect::<Vec<_>>(),
        [vec![root, z.0]]
    );
    assert_eq!(
        edge_data.new.tuples().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![z.0, root], vec![root, root]])
    );
    assert_eq!(
        relation_data(&dynamic, gate).unwrap().old.tuples().count(),
        1
    );
    assert_eq!(
        relation_data(&dynamic, gate).unwrap().new.tuples().count(),
        0
    );
    let v = signature.type_named("V").unwrap();
    let weights = &type_data(&dynamic, v).unwrap().weights;
    assert_eq!(weights[alias as usize], 0);
    assert_eq!(weights[root as usize], 4 * edge_data.weight);
    assert_eq!(weights[z.0 as usize], 2 * edge_data.weight);
    let once = dynamic.clone();
    dynamic.canonicalize();
    assert_same_pending_work(&once, &dynamic);
}

#[test]
fn duplicate_partitions_need_canonicalization_even_without_equalities() {
    let signature = Canonicalization::dynamic_signature();
    let mut model = Canonicalization::new();
    model.insert_gate();
    model.close();
    let snapshot = model.to_dynamic();
    let types = signature
        .types()
        .map(|(id, _)| type_data(&snapshot, id).unwrap().clone())
        .collect();
    let mut relations: Vec<_> = signature
        .relations()
        .map(|(id, _)| relation_data(&snapshot, id).unwrap().clone())
        .collect();
    let gate = signature.relation_named("gate").unwrap();
    relations[gate.0].new.table.insert(&[]);
    let mut dynamic = from_parts(signature, types, relations).unwrap();
    assert!(!dynamic.is_canonical());
    dynamic.canonicalize();
    assert_same_pending_work(&snapshot, &dynamic);
}

#[test]
fn canonicalization_leaves_function_equalities_for_closure() {
    let mut model = Canonicalization::new();
    let x = model.new_v();
    let y = model.new_v();
    let u = model.new_v();
    let v = model.new_v();
    model.insert_value(x, u);
    model.insert_value(y, v);
    model.close();
    model.equate_v(x, y);
    let mut dynamic = model.to_dynamic();
    dynamic.canonicalize();
    model.canonicalize();
    assert_same_pending_work(&model.to_dynamic(), &dynamic);
    assert!(!model.are_equal_v(u, v));
    assert_eq!(model.iter_value().count(), 2);
    assert_eq!(model.iter_v().count(), 3);
    model.close();
    assert!(model.are_equal_v(u, v));
    assert_eq!(model.iter_value().count(), 1);
}

#[test]
fn canonicalization_keeps_nested_member_handles_usable() {
    let mut model = MemberParents::new();
    let a = model.new_outer();
    let b = model.new_outer();
    let i = model.new_inner(a);
    let j = model.new_inner(b);
    let x = model.new_el(a, i);
    let y = model.new_el(b, j);
    model.close();
    model.equate_outer(a, b);
    model.equate_inner(b, i, j);
    model.equate_el(b, j, x, y);
    let mut dynamic = model.to_dynamic();
    dynamic.canonicalize();
    model.canonicalize();
    assert_same_pending_work(&model.to_dynamic(), &dynamic);
    model.insert_inner_member_el(b, j, y);
    model.new_el(b, j);
    model.canonicalize();
    model.close();
    assert_eq!(model.iter_outer_member_inner().count(), 1);
    assert_eq!(model.iter_inner_member_el().count(), 2);
}

#[test]
fn canonicalization_refreshes_shared_views_without_consuming_pending_facts() {
    let mut model = MorphismPreservation::new();
    let source = model.new_world();
    let target = model.new_world();
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, source);
    model.insert_world_mor_cod(h, target);
    model.close();
    model.insert_ready(source);
    model.canonicalize();
    let once = model.to_dynamic();
    model.canonicalize();
    assert_same_pending_work(&once, &model.to_dynamic());
    #[cfg(not(feature = "desugared"))]
    assert!(model.ready(target));
    assert!(!model.observed(target));
    model.close();
    assert!(model.observed(target));

    let third = model.new_world();
    let g = model.new_world_mor();
    model.insert_world_mor_dom(g, target);
    model.insert_world_mor_cod(g, third);
    model.canonicalize();
    model.canonicalize();
    model.close();
    assert!(model.observed(third));
}

#[test]
fn runtime_edits_retain_old_facts_between_closures() {
    let mut model = Canonicalization::new();
    let signature = Canonicalization::dynamic_signature();
    let v = signature.type_named("V").unwrap();
    let p = signature.relation_named("p").unwrap();
    let q = signature.relation_named("q").unwrap();
    let value = signature.relation_named("value").unwrap();
    let joined = signature.relation_named("joined").unwrap();
    let x = model.new_element(v, &[]).unwrap();
    assert!(model.insert(p, &[x]).unwrap());
    model.close();
    let before = model.to_dynamic();

    let y = model.new_element(v, &[]).unwrap();
    let z = model.define(value, &[x]).unwrap();
    assert_eq!(model.define(value, &[x]).unwrap(), z);
    assert!(!model.insert(p, &[x]).unwrap());
    let after = model.to_dynamic();
    assert_eq!(
        type_data(&after, v).unwrap().old.iter().collect::<Vec<_>>(),
        type_data(&before, v)
            .unwrap()
            .old
            .iter()
            .collect::<Vec<_>>()
    );
    assert_eq!(type_data(&after, v).unwrap().new.iter().count(), 2);
    assert_eq!(
        relation_data(&after, p)
            .unwrap()
            .old
            .tuples()
            .collect::<Vec<_>>(),
        relation_data(&before, p)
            .unwrap()
            .old
            .tuples()
            .collect::<Vec<_>>()
    );

    assert_eq!(
        model.insert(q, &[]),
        Err(Error::ArityMismatch {
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(
        model.new_element(v, &[x]),
        Err(Error::ArityMismatch {
            expected: 0,
            actual: 1
        })
    );
    assert_eq!(model.define(q, &[x]), Err(Error::ExpectedFunction(q)));
    assert_eq!(
        model.equate(&[x], x, y),
        Err(Error::ArityMismatch {
            expected: 0,
            actual: 1
        })
    );
    assert_same_pending_work(&after, &model.to_dynamic());

    model.insert(q, &[y]).unwrap();
    model.close();
    assert!(!model.to_dynamic().contains(joined, &[x]).unwrap());
    assert!(model.equate(&[], x, y).unwrap());
    model.close();
    assert!(model.to_dynamic().contains(joined, &[x]).unwrap());
}
