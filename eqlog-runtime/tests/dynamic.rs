use std::collections::BTreeSet;
use std::sync::Arc;

use eqlog_runtime::{
    Element, Error, FunctionKind, Model, Relation, RelationId, RelationKind, Signature, Type,
    TypeId, TypeKind,
};

fn signature(arity: usize, kind: RelationKind) -> Signature {
    Signature::new(
        vec![Type {
            name: "El".into(),
            kind: TypeKind::Plain,
            parents: vec![],
        }],
        vec![Relation {
            name: "r".into(),
            kind,
            arity: vec![TypeId(0); arity],
            parents: vec![],
        }],
    )
    .unwrap()
}

#[test]
fn arbitrary_arities_keep_stored_rows_after_equality() {
    for arity in 0..=12 {
        let mut model = Model::new(Arc::new(signature(arity, RelationKind::Predicate)));
        let x = model.new_element(TypeId(0), &[]).unwrap();
        let y = model.new_element(TypeId(0), &[]).unwrap();
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
        assert_eq!(original.elements(TypeId(0)).unwrap().count(), 2);
        assert_eq!(
            original.tuples(RelationId(0)).unwrap().count(),
            if arity == 0 { 1 } else { 2 }
        );
    }
}

#[test]
fn mixed_columns_survive_prefix_boundaries_and_equality() {
    for arity in [0, 1, 9, 10, 12] {
        let mut model = Model::new(Arc::new(signature(arity, RelationKind::Predicate)));
        let elements: Vec<_> = (0..=arity)
            .map(|_| model.new_element(TypeId(0), &[]).unwrap())
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
    let mut model = Model::new(Arc::new(signature(1, RelationKind::Predicate)));
    let x = model.new_element(TypeId(0), &[]).unwrap();
    let invalid = Element {
        type_: TypeId(0),
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
        model.new_element(TypeId(1), &[]),
        Err(Error::UnknownType(TypeId(1)))
    );
    assert_eq!(
        model.insert(RelationId(1), &[x]),
        Err(Error::UnknownRelation(RelationId(1)))
    );
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 0);
    assert_eq!(model.elements(TypeId(0)).unwrap().count(), 1);
}

#[test]
fn function_conflicts_are_data_until_an_evaluator_processes_them() {
    let mut model = Model::new(Arc::new(signature(
        1,
        RelationKind::Function(FunctionKind::Ordinary),
    )));
    let x = model.new_element(TypeId(0), &[]).unwrap();
    let y = model.new_element(TypeId(0), &[]).unwrap();
    model.insert(RelationId(0), &[x]).unwrap();
    model.insert(RelationId(0), &[y]).unwrap();
    assert_ne!(model.root(x).unwrap(), model.root(y).unwrap());
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 2);
    model.equate(&[], x, y).unwrap();
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 2);
}

#[test]
fn signatures_reject_invalid_shapes() {
    let type_ = Type {
        name: "El".into(),
        kind: TypeKind::Plain,
        parents: vec![],
    };
    let relation = Relation {
        name: "r".into(),
        kind: RelationKind::Predicate,
        parents: vec![],
        arity: vec![TypeId(1)],
    };
    assert_eq!(
        Signature::new(vec![type_.clone()], vec![relation]),
        Err(Error::UnknownType(TypeId(1)))
    );
    assert!(Signature::new(vec![type_.clone(), type_.clone()], vec![]).is_err());
    let relation = Relation {
        name: "f".into(),
        kind: RelationKind::Function(FunctionKind::Ordinary),
        parents: vec![],
        arity: vec![],
    };
    assert!(Signature::new(vec![type_], vec![relation]).is_err());
    let parent = Type {
        name: "Parent".into(),
        kind: TypeKind::Model,
        parents: vec![],
    };
    let member = Type {
        name: "Member".into(),
        kind: TypeKind::Plain,
        parents: vec![TypeId(0)],
    };
    assert!(Signature::new(vec![parent.clone(), member], vec![]).is_err());
    let recursive = Type {
        parents: vec![TypeId(0)],
        ..parent
    };
    assert!(Signature::new(vec![recursive], vec![]).is_err());
}

fn nested_signature() -> (Vec<Type>, Vec<Relation>) {
    let types = vec![
        Type {
            name: "Item".into(),
            kind: TypeKind::Plain,
            parents: vec![TypeId(2)],
        },
        Type {
            name: "Map".into(),
            kind: TypeKind::Morphism(TypeId(2)),
            parents: vec![],
        },
        Type {
            name: "World".into(),
            kind: TypeKind::Model,
            parents: vec![],
        },
    ];
    let relations = vec![
        Relation {
            name: "member".into(),
            kind: RelationKind::Membership(TypeId(0)),
            arity: vec![TypeId(2), TypeId(0)],
            parents: vec![TypeId(2)],
        },
        Relation {
            name: "dom".into(),
            kind: RelationKind::Function(FunctionKind::MorphismDomain(TypeId(2))),
            arity: vec![TypeId(1), TypeId(2)],
            parents: vec![],
        },
        Relation {
            name: "cod".into(),
            kind: RelationKind::Function(FunctionKind::MorphismCodomain(TypeId(2))),
            arity: vec![TypeId(1), TypeId(2)],
            parents: vec![],
        },
        Relation {
            name: "apply".into(),
            kind: RelationKind::Function(FunctionKind::MorphismApplication {
                morphism: TypeId(1),
                member: TypeId(0),
            }),
            arity: vec![TypeId(1), TypeId(0), TypeId(0)],
            parents: vec![],
        },
    ];
    (types, relations)
}

#[test]
fn descriptors_support_forward_references_but_reject_invalid_roles() {
    let (types, relations) = nested_signature();
    let signature = Signature::new(types.clone(), relations.clone()).unwrap();
    let mut model = Model::new(Arc::new(signature));
    let world = model.new_element(TypeId(2), &[]).unwrap();
    let item = model.new_element(TypeId(0), &[world]).unwrap();
    assert!(model.contains(RelationId(0), &[world, item]).unwrap());
    assert_eq!(
        model.equate(&[], world, item),
        Err(Error::TypeMismatch {
            expected: TypeId(2),
            actual: TypeId(0)
        })
    );
    assert_eq!(
        model.insert(RelationId(0), &[item, world]),
        Err(Error::TypeMismatch {
            expected: TypeId(2),
            actual: TypeId(0)
        })
    );

    for endpoint in [1, 2] {
        let mut bad = relations.clone();
        bad[endpoint].arity[0] = TypeId(0);
        assert!(Signature::new(types.clone(), bad).is_err());
    }
    let mut bad = relations.clone();
    bad[3].arity[2] = TypeId(2);
    assert!(Signature::new(types.clone(), bad).is_err());
    let mut bad = relations.clone();
    bad[3].kind = RelationKind::Function(FunctionKind::MorphismApplication {
        morphism: TypeId(2),
        member: TypeId(0),
    });
    assert!(Signature::new(types.clone(), bad).is_err());

    let mut bad = relations.clone();
    bad[0].arity.swap(0, 1);
    assert!(Signature::new(types.clone(), bad).is_err());
    let mut bad = relations.clone();
    let duplicate = Relation {
        name: "second_membership".into(),
        ..bad[0].clone()
    };
    bad.push(duplicate);
    assert!(Signature::new(types.clone(), bad).is_err());
    let mut bad = types.clone();
    bad[0].parents = vec![TypeId(2), TypeId(2)];
    assert!(Signature::new(bad, relations.clone()).is_err());
    let mut bad = relations;
    bad[3].kind = RelationKind::Function(FunctionKind::Constructor);
    assert!(Signature::new(types, bad).is_err());
}
