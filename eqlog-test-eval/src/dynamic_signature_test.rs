use std::sync::Arc;

use eqlog_runtime::{
    Error, FunctionKind, Model, Relation, RelationId, RelationKind, Signature, Type, TypeId,
    TypeKind,
};

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
    let mut model = Model::with_signature(Arc::new(signature));
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
    let mut model = Model::with_signature(Arc::new(Signature::new(types, relations).unwrap()));
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
    let mut model = Model::with_signature(Arc::new(Signature::new(types, relations).unwrap()));
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
    let mut model = Model::with_signature(Arc::new(Signature::new(types, relations).unwrap()));
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
fn nested_applications_report_missing_parent_image_declarations() {
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
    let mut model = Model::with_signature(Arc::new(Signature::new(types, relations).unwrap()));
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
    let error = Error::InvalidSignature(
        "missing morphism function MorphismApplication { morphism: TypeId(1), member: TypeId(3) } for TypeId(1)".into(),
    );
    assert_eq!(
        model.insert(RelationId(3), &[morphism, x, y]),
        Err(error.clone())
    );
    assert_eq!(model.define(RelationId(3), &[morphism, x]), Err(error));
    assert_eq!(model.elements(TypeId(0)).unwrap().count(), 2);
    assert_eq!(model.tuples(RelationId(3)).unwrap().count(), 0);
}
