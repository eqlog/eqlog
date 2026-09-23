use std::collections::BTreeSet;
use std::sync::Arc;

use eqlog_runtime::dynamic::__private::{self, RelationData, RelationIndex, SortData, Table};
use eqlog_runtime::dynamic::{
    DynamicModel, Element, Error, FunctionKind, Relation, RelationId, RelationKind, Signature,
    Sort, SortId, SortKind,
};

fn signature(arity: usize, kind: RelationKind) -> Signature {
    Signature::new(
        vec![Sort {
            name: "El".into(),
            kind: SortKind::Plain,
            parents: vec![],
        }],
        vec![Relation {
            name: "r".into(),
            kind,
            arity: vec![SortId(0); arity],
            parents: vec![],
        }],
    )
    .unwrap()
}

#[test]
fn arbitrary_arities_keep_stored_rows_after_equality() {
    for arity in 0..=12 {
        let mut model = DynamicModel::new(Arc::new(signature(arity, RelationKind::Predicate)));
        let x = model.new_element(SortId(0), &[]).unwrap();
        let y = model.new_element(SortId(0), &[]).unwrap();
        let left = vec![x; arity];
        let right = vec![y; arity];
        assert!(model.insert(RelationId(0), &left).unwrap());
        assert!(!model.insert(RelationId(0), &left).unwrap());
        model.insert(RelationId(0), &right).unwrap();
        let original = model.clone();
        model.equate(&[], x, y).unwrap();
        assert!(model.contains(RelationId(0), &right).unwrap());
        assert_eq!(
            model.tuples(RelationId(0)).unwrap().collect::<Vec<_>>(),
            if arity == 0 {
                vec![left]
            } else {
                vec![left, right]
            }
        );
        assert_eq!(original.elements(SortId(0)).unwrap().count(), 2);
        assert_eq!(
            original.tuples(RelationId(0)).unwrap().count(),
            if arity == 0 { 1 } else { 2 }
        );
    }
}

#[test]
fn mixed_columns_survive_prefix_boundaries_and_equality() {
    for arity in [0, 1, 9, 10, 12] {
        let mut model = DynamicModel::new(Arc::new(signature(arity, RelationKind::Predicate)));
        let elements: Vec<_> = (0..=arity)
            .map(|_| model.new_element(SortId(0), &[]).unwrap())
            .collect();
        let forward = elements[..arity].to_vec();
        let reverse: Vec<_> = forward.iter().rev().copied().collect();
        let shifted = elements[1..].to_vec();
        let expected = BTreeSet::from([forward, reverse, shifted]);
        for tuple in &expected {
            assert!(model.insert(RelationId(0), tuple).unwrap());
            assert!(model.contains(RelationId(0), tuple).unwrap());
        }
        assert_eq!(
            model
                .tuples(RelationId(0))
                .unwrap()
                .collect::<BTreeSet<_>>(),
            expected
        );
        if arity == 0 {
            continue;
        }
        let absent = vec![elements[arity]; arity];
        assert_eq!(
            model.contains(RelationId(0), &absent).unwrap(),
            expected.contains(&absent)
        );
        model.equate(&[], elements[0], elements[arity]).unwrap();
        assert_eq!(
            model.root(elements[0]).unwrap(),
            model.root(elements[arity]).unwrap()
        );
        assert_eq!(
            model
                .tuples(RelationId(0))
                .unwrap()
                .collect::<BTreeSet<_>>(),
            expected
        );
    }
}

#[test]
fn invalid_operations_return_errors_without_adding_data() {
    let mut model = DynamicModel::new(Arc::new(signature(1, RelationKind::Predicate)));
    let x = model.new_element(SortId(0), &[]).unwrap();
    let invalid = Element {
        sort: SortId(0),
        index: 1,
    };
    assert_eq!(
        model.insert(RelationId(0), &[]),
        Err(Error::ArityMismatch {
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(
        model.insert(RelationId(0), &[invalid]),
        Err(Error::UnknownElement(invalid))
    );
    assert_eq!(
        model.equate(&[], x, invalid),
        Err(Error::UnknownElement(invalid))
    );
    assert_eq!(
        model.new_element(SortId(1), &[]),
        Err(Error::UnknownSort(SortId(1)))
    );
    assert_eq!(
        model.insert(RelationId(1), &[x]),
        Err(Error::UnknownRelation(RelationId(1)))
    );
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 0);
    assert_eq!(model.elements(SortId(0)).unwrap().count(), 1);
}

#[test]
fn function_conflicts_are_data_until_an_evaluator_processes_them() {
    let mut model = DynamicModel::new(Arc::new(signature(
        1,
        RelationKind::Function(FunctionKind::Ordinary),
    )));
    let x = model.new_element(SortId(0), &[]).unwrap();
    let y = model.new_element(SortId(0), &[]).unwrap();
    model.insert(RelationId(0), &[x]).unwrap();
    model.insert(RelationId(0), &[y]).unwrap();
    assert_ne!(model.root(x).unwrap(), model.root(y).unwrap());
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 2);
    model.equate(&[], x, y).unwrap();
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 2);
}

#[test]
fn signatures_reject_invalid_shapes() {
    let sort = Sort {
        name: "El".into(),
        kind: SortKind::Plain,
        parents: vec![],
    };
    let relation = Relation {
        name: "r".into(),
        kind: RelationKind::Predicate,
        parents: vec![],
        arity: vec![SortId(1)],
    };
    assert_eq!(
        Signature::new(vec![sort.clone()], vec![relation]),
        Err(Error::UnknownSort(SortId(1)))
    );
    assert!(Signature::new(vec![sort.clone(), sort.clone()], vec![]).is_err());
    let relation = Relation {
        name: "f".into(),
        kind: RelationKind::Function(FunctionKind::Ordinary),
        parents: vec![],
        arity: vec![],
    };
    assert!(Signature::new(vec![sort], vec![relation]).is_err());
    let parent = Sort {
        name: "Parent".into(),
        kind: SortKind::Model,
        parents: vec![],
    };
    let member = Sort {
        name: "Member".into(),
        kind: SortKind::Plain,
        parents: vec![SortId(0)],
    };
    assert!(Signature::new(vec![parent.clone(), member], vec![]).is_err());
    let recursive = Sort {
        parents: vec![SortId(0)],
        ..parent
    };
    assert!(Signature::new(vec![recursive], vec![]).is_err());
}

fn nested_signature() -> (Vec<Sort>, Vec<Relation>) {
    let sorts = vec![
        Sort {
            name: "Item".into(),
            kind: SortKind::Plain,
            parents: vec![SortId(2)],
        },
        Sort {
            name: "Map".into(),
            kind: SortKind::Morphism(SortId(2)),
            parents: vec![],
        },
        Sort {
            name: "World".into(),
            kind: SortKind::Model,
            parents: vec![],
        },
    ];
    let relations = vec![
        Relation {
            name: "member".into(),
            kind: RelationKind::Membership(SortId(0)),
            arity: vec![SortId(2), SortId(0)],
            parents: vec![SortId(2)],
        },
        Relation {
            name: "dom".into(),
            kind: RelationKind::Function(FunctionKind::MorphismDomain(SortId(2))),
            arity: vec![SortId(1), SortId(2)],
            parents: vec![],
        },
        Relation {
            name: "cod".into(),
            kind: RelationKind::Function(FunctionKind::MorphismCodomain(SortId(2))),
            arity: vec![SortId(1), SortId(2)],
            parents: vec![],
        },
        Relation {
            name: "apply".into(),
            kind: RelationKind::Function(FunctionKind::MorphismApplication {
                morphism: SortId(1),
                member: SortId(0),
            }),
            arity: vec![SortId(1), SortId(0), SortId(0)],
            parents: vec![],
        },
    ];
    (sorts, relations)
}

#[test]
fn descriptors_support_forward_references_but_reject_invalid_roles() {
    let (sorts, relations) = nested_signature();
    let signature = Signature::new(sorts.clone(), relations.clone()).unwrap();
    let mut model = DynamicModel::new(Arc::new(signature));
    let world = model.new_element(SortId(2), &[]).unwrap();
    let item = model.new_element(SortId(0), &[world]).unwrap();
    assert!(model.contains(RelationId(0), &[world, item]).unwrap());
    assert_eq!(
        model.equate(&[], world, item),
        Err(Error::SortMismatch {
            expected: SortId(2),
            actual: SortId(0)
        })
    );
    assert_eq!(
        model.insert(RelationId(0), &[item, world]),
        Err(Error::SortMismatch {
            expected: SortId(2),
            actual: SortId(0)
        })
    );

    for endpoint in [1, 2] {
        let mut bad = relations.clone();
        bad[endpoint].arity[0] = SortId(0);
        assert!(Signature::new(sorts.clone(), bad).is_err());
    }
    let mut bad = relations.clone();
    bad[3].arity[2] = SortId(2);
    assert!(Signature::new(sorts.clone(), bad).is_err());
    let mut bad = relations.clone();
    bad[3].kind = RelationKind::Function(FunctionKind::MorphismApplication {
        morphism: SortId(2),
        member: SortId(0),
    });
    assert!(Signature::new(sorts.clone(), bad).is_err());

    let mut bad = relations.clone();
    bad[0].arity.swap(0, 1);
    assert!(Signature::new(sorts.clone(), bad).is_err());
    let mut bad = relations.clone();
    let duplicate = Relation {
        name: "second_membership".into(),
        ..bad[0].clone()
    };
    bad.push(duplicate);
    assert!(Signature::new(sorts.clone(), bad).is_err());
    let mut bad = sorts.clone();
    bad[0].parents = vec![SortId(2), SortId(2)];
    assert!(Signature::new(bad, relations.clone()).is_err());
    let mut bad = relations;
    bad[3].kind = RelationKind::Function(FunctionKind::Constructor);
    assert!(Signature::new(sorts, bad).is_err());
}

#[test]
fn reindex_combines_permuted_partitions_and_projects_raw_diagonals() {
    let mut data = RelationData::new(3);
    data.new.order = vec![2, 0, 1];
    data.old.order = vec![1, 2, 0];
    for row in [[9, 1, 1], [8, 1, 2]] {
        data.new.table.insert(&row);
    }
    for row in [[1, 9, 1], [2, 7, 2]] {
        data.old.table.insert(&row);
    }
    let all = data.reindex(&[0, 1, 2], &[]).unwrap();
    assert_eq!(
        all.iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![1, 1, 9], vec![1, 2, 8], vec![2, 2, 7],])
    );
    let diagonal = data.reindex(&[1, 0], &[0, 0, 2]).unwrap();
    assert_eq!(
        diagonal.iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([vec![9, 1], vec![7, 2],])
    );
    assert!(data.reindex(&[0, 0], &[0, 0, 2]).is_err());
    assert!(data.reindex(&[0, 1], &[1, 0, 2]).is_err());
}

#[test]
fn table_copies_and_unions_are_independent_at_every_arity() {
    for arity in [0, 1, 9, 10, 12] {
        let mut source = Table::new(arity);
        let mut copy = source.clone();
        source.insert(&vec![1; arity]);
        assert_eq!(copy.iter().count(), 0);
        copy.insert(&vec![2; arity]);
        let mut union = source.union(&copy);
        assert!(union.contains(&vec![1; arity]));
        assert!(union.contains(&vec![2; arity]));
        union.insert(&vec![3; arity]);
        assert_eq!(source.iter().collect::<Vec<_>>(), vec![vec![1; arity]]);
        assert_eq!(copy.iter().collect::<Vec<_>>(), vec![vec![2; arity]]);
        let mut data = RelationData::new(arity);
        data.new.table = source;
        data.old.table = copy;
        let result = data
            .reindex(&(0..arity).rev().collect::<Vec<_>>(), &[])
            .unwrap();
        assert_eq!(result.iter().count(), if arity == 0 { 1 } else { 2 });
    }
}

#[test]
fn raw_storage_rejects_inconsistent_indices_and_handles() {
    let signature = Arc::new(signature(2, RelationKind::Predicate));
    let mut sort = SortData::new();
    sort.equalities.increase_size_to(2);
    sort.equalities.union_roots_into(0, 1);
    sort.new.insert([1]);
    sort.weights = vec![0; 2];
    sort.uprooted.push(0);
    let mut relation = RelationData::new(2);
    relation.new.table.insert(&[0, 1]);
    let model = __private::from_parts(
        signature.clone(),
        vec![sort.clone()],
        vec![relation.clone()],
    )
    .unwrap();
    assert_eq!(
        model.tuples(RelationId(0)).unwrap().next().unwrap()[0].index,
        0
    );
    let mut bad_sort = sort.clone();
    bad_sort.new.insert([0]);
    assert!(
        __private::from_parts(signature.clone(), vec![bad_sort], vec![relation.clone()]).is_err()
    );
    let mut bad_sort = sort.clone();
    bad_sort.new.remove([1]);
    assert!(
        __private::from_parts(signature.clone(), vec![bad_sort], vec![relation.clone()]).is_err()
    );
    let mut bad_sort = sort.clone();
    bad_sort.weights.pop();
    assert!(
        __private::from_parts(signature.clone(), vec![bad_sort], vec![relation.clone()]).is_err()
    );
    let mut bad_relation = relation.clone();
    bad_relation.new.order = vec![0, 0];
    assert!(
        __private::from_parts(signature.clone(), vec![sort.clone()], vec![bad_relation]).is_err()
    );
    let mut bad_relation = relation.clone();
    bad_relation.old = RelationIndex::new(1);
    assert!(
        __private::from_parts(signature.clone(), vec![sort.clone()], vec![bad_relation]).is_err()
    );
    relation.new.table.insert(&[0, 2]);
    assert_eq!(
        __private::from_parts(signature, vec![sort], vec![relation]).err(),
        Some(Error::UnknownElement(Element {
            sort: SortId(0),
            index: 2
        }))
    );
}
