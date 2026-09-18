use std::sync::Arc;

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
fn arbitrary_arities_share_set_semantics_and_normalize_equalities() {
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
        model.equate(x, y).unwrap();
        assert!(model.contains(RelationId(0), &right).unwrap());
        assert_eq!(
            model.tuples(RelationId(0)).unwrap().collect::<Vec<_>>(),
            vec![left]
        );
        assert_eq!(original.elements(SortId(0)).unwrap().count(), 2);
        assert_eq!(
            original.tuples(RelationId(0)).unwrap().count(),
            if arity == 0 { 1 } else { 2 }
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
        model.equate(x, invalid),
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
    model.equate(x, y).unwrap();
    assert_eq!(model.tuples(RelationId(0)).unwrap().count(), 1);
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
