use std::collections::BTreeSet;
use std::sync::Arc;

use eqlog_runtime::{
    Element, EnumCase, Error, FunctionKind, Model, Relation, RelationId, RelationKind, Signature,
    Type, TypeId, TypeKind,
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

#[test]
fn signatures_reject_ambiguous_morphism_functions() {
    let (types, relations) = nested_signature();
    for index in [1, 2, 3] {
        let mut duplicated = relations.clone();
        duplicated.push(Relation {
            name: "duplicate".into(),
            ..relations[index].clone()
        });
        assert_eq!(
            Signature::new(types.clone(), duplicated).err(),
            Some(Error::InvalidSignature(
                "duplicate morphism function role".into()
            ))
        );
    }
}

#[test]
fn endpoint_lookup_distinguishes_morphism_types_for_the_same_model() {
    let (mut types, mut relations) = nested_signature();
    types.push(Type {
        name: "OtherMap".into(),
        kind: TypeKind::Morphism(TypeId(2)),
        parents: vec![],
    });
    for index in [1, 2, 3] {
        let mut relation = relations[index].clone();
        let name = &relation.name;
        relation.name = format!("other_{name}");
        relation.arity[0] = TypeId(3);
        if index == 3 {
            relation.kind = RelationKind::Function(FunctionKind::MorphismApplication {
                morphism: TypeId(3),
                member: TypeId(0),
            });
        }
        relations.push(relation);
    }
    let mut model = Model::new(Arc::new(Signature::new(types, relations).unwrap()));
    let a = model.new_element(TypeId(2), &[]).unwrap();
    let b = model.new_element(TypeId(2), &[]).unwrap();
    let x = model.new_element(TypeId(0), &[a]).unwrap();
    let y = model.new_element(TypeId(0), &[b]).unwrap();
    let morphism = model.new_element(TypeId(3), &[]).unwrap();
    model.insert(RelationId(4), &[morphism, a]).unwrap();
    model.insert(RelationId(5), &[morphism, b]).unwrap();
    assert!(model.insert(RelationId(6), &[morphism, x, y]).unwrap());
    assert_eq!(model.eval(RelationId(6), &[morphism, x]).unwrap(), Some(y));
    assert_eq!(model.define(RelationId(6), &[morphism, x]).unwrap(), y);
}

#[test]
fn missing_domain_declarations_are_reported_when_applications_are_used() {
    let (types, mut relations) = nested_signature();
    relations.remove(1);
    let mut model = Model::new(Arc::new(Signature::new(types, relations).unwrap()));
    let world = model.new_element(TypeId(2), &[]).unwrap();
    let item = model.new_element(TypeId(0), &[world]).unwrap();
    let morphism = model.new_element(TypeId(1), &[]).unwrap();
    let error = Error::InvalidSignature(
        "missing morphism function MorphismDomain(TypeId(2)) for TypeId(1)".into(),
    );
    assert_eq!(
        model.eval(RelationId(2), &[morphism, item]),
        Err(error.clone())
    );
    assert_eq!(model.define(RelationId(2), &[morphism, item]), Err(error));
    assert_eq!(model.elements(TypeId(0)).unwrap().count(), 1);
    assert_eq!(model.tuples(RelationId(2)).unwrap().count(), 0);
}

#[test]
fn missing_codomain_declarations_do_not_prevent_reading_applications() {
    let (types, mut relations) = nested_signature();
    relations.remove(2);
    let mut model = Model::new(Arc::new(Signature::new(types, relations).unwrap()));
    let world = model.new_element(TypeId(2), &[]).unwrap();
    let item = model.new_element(TypeId(0), &[world]).unwrap();
    let morphism = model.new_element(TypeId(1), &[]).unwrap();
    model.insert(RelationId(1), &[morphism, world]).unwrap();
    assert_eq!(model.eval(RelationId(2), &[morphism, item]), Ok(None));
    let error = Error::InvalidSignature(
        "missing morphism function MorphismCodomain(TypeId(2)) for TypeId(1)".into(),
    );
    assert_eq!(
        model.insert(RelationId(2), &[morphism, item, item]),
        Err(error.clone())
    );
    assert_eq!(model.define(RelationId(2), &[morphism, item]), Err(error));
    assert_eq!(model.elements(TypeId(0)).unwrap().count(), 1);
    assert_eq!(model.elements(TypeId(2)).unwrap().count(), 1);
    assert_eq!(model.tuples(RelationId(2)).unwrap().count(), 0);
}

#[test]
fn nested_applications_report_missing_parent_image_declarations_or_values() {
    for declare_parent_application in [false, true] {
        let (mut types, mut relations) = nested_signature();
        types.push(Type {
            name: "Inner".into(),
            kind: TypeKind::Model,
            parents: vec![TypeId(2)],
        });
        types[0].parents.push(TypeId(3));
        relations[0].parents.push(TypeId(3));
        relations[0].arity = vec![TypeId(2), TypeId(3), TypeId(0)];
        relations.push(Relation {
            name: "inner_member".into(),
            kind: RelationKind::Membership(TypeId(3)),
            arity: vec![TypeId(2), TypeId(3)],
            parents: vec![TypeId(2)],
        });
        if declare_parent_application {
            relations.push(Relation {
                name: "parent_application".into(),
                kind: RelationKind::Function(FunctionKind::MorphismApplication {
                    morphism: TypeId(1),
                    member: TypeId(3),
                }),
                arity: vec![TypeId(1), TypeId(3), TypeId(3)],
                parents: vec![],
            });
        }
        let mut model = Model::new(Arc::new(Signature::new(types, relations).unwrap()));
        let a = model.new_element(TypeId(2), &[]).unwrap();
        let b = model.new_element(TypeId(2), &[]).unwrap();
        let i = model.new_element(TypeId(3), &[a]).unwrap();
        let j = model.new_element(TypeId(3), &[b]).unwrap();
        let x = model.new_element(TypeId(0), &[a, i]).unwrap();
        let y = model.new_element(TypeId(0), &[b, j]).unwrap();
        let morphism = model.new_element(TypeId(1), &[]).unwrap();
        model.insert(RelationId(1), &[morphism, a]).unwrap();
        model.insert(RelationId(2), &[morphism, b]).unwrap();
        assert_eq!(model.eval(RelationId(3), &[morphism, x]), Ok(None));
        let error = if declare_parent_application {
            Error::UndefinedFunction(RelationId(5))
        } else {
            Error::InvalidSignature(
                "missing morphism function MorphismApplication { morphism: TypeId(1), member: TypeId(3) } for TypeId(1)".into(),
            )
        };
        assert_eq!(
            model.insert(RelationId(3), &[morphism, x, y]),
            Err(error.clone())
        );
        assert_eq!(model.define(RelationId(3), &[morphism, x]), Err(error));
        assert_eq!(model.elements(TypeId(0)).unwrap().count(), 2);
        assert_eq!(model.tuples(RelationId(3)).unwrap().count(), 0);
    }
}

#[test]
fn enum_and_function_helpers_check_arguments_before_allocating() {
    let signature = Signature::new(
        vec![
            Type {
                name: "El".into(),
                kind: TypeKind::Plain,
                parents: vec![],
            },
            Type {
                name: "Choice".into(),
                kind: TypeKind::Enum,
                parents: vec![],
            },
        ],
        vec![
            Relation {
                name: "predicate".into(),
                kind: RelationKind::Predicate,
                arity: vec![TypeId(0)],
                parents: vec![],
            },
            Relation {
                name: "Wrap".into(),
                kind: RelationKind::Function(FunctionKind::Constructor),
                arity: vec![TypeId(0), TypeId(1)],
                parents: vec![],
            },
            Relation {
                name: "choice".into(),
                kind: RelationKind::Function(FunctionKind::Ordinary),
                arity: vec![TypeId(0), TypeId(1)],
                parents: vec![],
            },
        ],
    )
    .unwrap();
    let mut model = Model::new(Arc::new(signature));
    let x = model.new_element(TypeId(0), &[]).unwrap();
    assert_eq!(
        model.new_element(TypeId(1), &[]),
        Err(Error::ConstructorRequired(TypeId(1)))
    );
    assert_eq!(
        model.eval(RelationId(0), &[x]),
        Err(Error::ExpectedFunction(RelationId(0)))
    );
    assert_eq!(
        model.define(RelationId(0), &[x]),
        Err(Error::ExpectedFunction(RelationId(0)))
    );
    assert_eq!(
        model.new_enum(EnumCase {
            constructor: RelationId(0),
            arguments: vec![x]
        }),
        Err(Error::ExpectedConstructor(RelationId(0)))
    );
    assert_eq!(
        model.define(RelationId(2), &[x]),
        Err(Error::ConstructorRequired(TypeId(1)))
    );
    assert_eq!(
        model.new_enum(EnumCase {
            constructor: RelationId(1),
            arguments: vec![]
        }),
        Err(Error::ArityMismatch {
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(model.cases(x).err(), Some(Error::ExpectedEnum(TypeId(0))));
    assert_eq!(model.case(x), Err(Error::ExpectedEnum(TypeId(0))));
    assert_eq!(model.elements(TypeId(1)).unwrap().count(), 0);

    let value = EnumCase {
        constructor: RelationId(1),
        arguments: vec![x],
    };
    let element = model.new_enum(value.clone()).unwrap();
    assert_eq!(model.new_enum(value.clone()).unwrap(), element);
    assert_eq!(model.eval(RelationId(1), &[x]), Ok(Some(element)));
    assert_eq!(
        model.cases(element).unwrap().collect::<Vec<_>>(),
        vec![value.clone()]
    );
    assert_eq!(model.case(element).unwrap(), value);
    assert_eq!(model.elements(TypeId(1)).unwrap().count(), 1);
    assert_eq!(
        model.are_equal(x, element),
        Err(Error::TypeMismatch {
            expected: TypeId(0),
            actual: TypeId(1)
        })
    );
}
