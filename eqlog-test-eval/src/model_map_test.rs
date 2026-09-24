use std::collections::BTreeSet;
use std::sync::Arc;

use eqlog_runtime::{
    find_isomorphism, find_isomorphism_under, CompiledModel, Element, Error, FunctionKind, Model,
    ModelMap, Relation, RelationId, RelationKind, Signature, Type, TypeId, TypeKind,
};

use crate::trans_refl::TransRefl;

fn signature(arities: &[usize]) -> Arc<Signature> {
    Arc::new(
        Signature::new(
            vec![Type {
                name: "V".into(),
                kind: TypeKind::Plain,
                parents: vec![],
            }],
            arities
                .iter()
                .enumerate()
                .map(|(index, &arity)| Relation {
                    name: format!("r{index}"),
                    kind: RelationKind::Predicate,
                    arity: vec![TypeId(0); arity],
                    parents: vec![],
                })
                .collect(),
        )
        .unwrap(),
    )
}

fn elements(model: &mut Model, count: usize) -> Vec<Element> {
    (0..count)
        .map(|_| model.new_element(TypeId(0), &[]).unwrap())
        .collect()
}

fn graph(count: usize, edges: &[(usize, usize)]) -> (Model, Vec<Element>) {
    let mut model = Model::with_signature(signature(&[2]));
    let vertices = elements(&mut model, count);
    for &(source, target) in edges {
        model
            .insert(RelationId(0), &[vertices[source], vertices[target]])
            .unwrap();
    }
    (model, vertices)
}

fn check_witness(map: &ModelMap<'_>) {
    let inverse = map.inverse().unwrap().unwrap();
    let identity = map.then(&inverse).unwrap();
    for (element, image) in identity.iter() {
        assert_eq!(element, image);
    }
    ModelMap::new(map.source(), map.target(), map.iter()).unwrap();
    ModelMap::new(inverse.source(), inverse.target(), inverse.iter()).unwrap();
}

#[test]
fn model_maps_validate_totality_types_handles_and_relations() {
    let (source, vertices) = graph(2, &[(0, 1)]);
    let (target, images) = graph(2, &[(1, 0)]);
    let valid = ModelMap::new(
        &source,
        &target,
        [(vertices[0], images[1]), (vertices[1], images[0])],
    )
    .unwrap();
    assert_eq!(valid.apply(vertices[0]).unwrap(), images[1]);
    check_witness(&valid);
    assert!(ModelMap::new(&source, &target, [(vertices[0], images[1])]).is_err());
    assert!(ModelMap::new(&source, &target, vertices.iter().copied().zip(images)).is_err());
    let unknown = Element {
        type_: TypeId(0),
        index: 100,
    };
    assert_eq!(valid.apply(unknown), Err(Error::UnknownElement(unknown)));
    assert_eq!(
        ModelMap::new(&source, &target, [(vertices[0], unknown)]).err(),
        Some(Error::UnknownElement(unknown))
    );
    assert_eq!(
        ModelMap::new(&source, &target, [(unknown, vertices[0])]).err(),
        Some(Error::UnknownElement(unknown))
    );

    let signature = Arc::new(
        Signature::new(
            ["A", "B"]
                .into_iter()
                .map(|name| Type {
                    name: name.into(),
                    kind: TypeKind::Plain,
                    parents: vec![],
                })
                .collect(),
            vec![],
        )
        .unwrap(),
    );
    let mut model = Model::with_signature(signature.clone());
    let a = model.new_element(TypeId(0), &[]).unwrap();
    let b = model.new_element(TypeId(1), &[]).unwrap();
    assert_eq!(
        ModelMap::new(&model, &model, [(a, b), (b, a)]).err(),
        Some(Error::TypeMismatch {
            expected: TypeId(0),
            actual: TypeId(1),
        })
    );
    let mut different_counts = Model::with_signature(signature);
    elements(&mut different_counts, 2);
    assert!(find_isomorphism(&model, &different_counts)
        .unwrap()
        .is_none());
}

#[test]
fn model_maps_normalize_aliases_without_running_rules() {
    let (mut source, vertices) = graph(3, &[(1, 2), (0, 2)]);
    source.equate(&[], vertices[0], vertices[1]).unwrap();
    let (mut target, images) = graph(3, &[(2, 0)]);
    target.equate(&[], images[1], images[2]).unwrap();
    let map = ModelMap::new(
        &source,
        &target,
        [
            (vertices[0], images[1]),
            (vertices[1], images[2]),
            (vertices[2], images[0]),
        ],
    )
    .unwrap();
    assert_eq!(map.iter().len(), 2);
    assert_eq!(
        map.apply(vertices[1]).unwrap(),
        target.root(images[2]).unwrap()
    );
    check_witness(&map);
    check_witness(&find_isomorphism(&source, &target).unwrap().unwrap());
    let (without_aliases, _) = graph(2, &[(0, 1)]);
    check_witness(
        &find_isomorphism(&source, &without_aliases)
            .unwrap()
            .unwrap(),
    );
    assert!(ModelMap::new(
        &source,
        &target,
        [
            (vertices[0], images[1]),
            (vertices[1], images[0]),
            (vertices[2], images[0]),
        ],
    )
    .is_err());
    assert_eq!(source.tuples(RelationId(0)).unwrap().count(), 2);
    assert_eq!(
        target.tuples(RelationId(0)).unwrap().next().unwrap()[0],
        images[2]
    );
}

#[test]
fn model_maps_can_collapse_elements_but_bijections_must_reflect_relations() {
    let (source, vertices) = graph(2, &[(0, 1)]);
    let (target, images) = graph(1, &[(0, 0)]);
    let quotient = ModelMap::new(
        &source,
        &target,
        vertices.iter().map(|&element| (element, images[0])),
    )
    .unwrap();
    assert!(quotient.inverse().unwrap().is_none());
    assert!(find_isomorphism(&source, &target).unwrap().is_none());

    let (extended, extra) = graph(2, &[(0, 1), (1, 0)]);
    let bijection = ModelMap::new(&source, &extended, vertices.iter().copied().zip(extra)).unwrap();
    assert!(bijection.inverse().unwrap().is_none());
    assert!(find_isomorphism(&source, &extended).unwrap().is_none());

    let (isolated, isolated_vertices) = graph(2, &[]);
    let (singleton, singleton_vertices) = graph(1, &[]);
    let inclusion = ModelMap::new(
        &singleton,
        &isolated,
        [(singleton_vertices[0], isolated_vertices[0])],
    )
    .unwrap();
    assert!(inclusion.inverse().unwrap().is_none());
    let identity = ModelMap::identity(&isolated);
    assert_eq!(
        inclusion
            .then(&identity)
            .unwrap()
            .iter()
            .collect::<Vec<_>>(),
        inclusion.iter().collect::<Vec<_>>()
    );
    let other = isolated.clone();
    assert!(inclusion.then(&ModelMap::identity(&other)).is_err());
}

#[test]
fn isomorphisms_under_a_base_respect_labels_and_identifications() {
    let (base, base_vertices) = graph(3, &[]);
    let (mut left, left_vertices) = graph(3, &[]);
    let (mut right, right_vertices) = graph(3, &[]);
    left.equate(&[], left_vertices[0], left_vertices[1])
        .unwrap();
    right
        .equate(&[], right_vertices[2], right_vertices[1])
        .unwrap();
    let left_map = ModelMap::new(
        &base,
        &left,
        base_vertices.iter().copied().zip(left_vertices),
    )
    .unwrap();
    let right_map = ModelMap::new(
        &base,
        &right,
        base_vertices
            .iter()
            .copied()
            .zip(right_vertices.iter().copied().rev()),
    )
    .unwrap();
    let iso = find_isomorphism_under(&left_map, &right_map)
        .unwrap()
        .unwrap();
    check_witness(&iso);
    for &element in &base_vertices {
        assert_eq!(
            iso.apply(left_map.apply(element).unwrap()).unwrap(),
            right_map.apply(element).unwrap()
        );
    }
    let different_kernel = ModelMap::new(
        &base,
        &right,
        base_vertices.iter().copied().zip(right_vertices),
    )
    .unwrap();
    assert!(find_isomorphism(&left, &right).unwrap().is_some());
    assert!(find_isomorphism_under(&left_map, &different_kernel)
        .unwrap()
        .is_none());
    assert!(find_isomorphism_under(&different_kernel, &left_map)
        .unwrap()
        .is_none());

    let (labels, label_vertices) = graph(2, &[]);
    let (ordered, ordered_vertices) = graph(2, &[(0, 1)]);
    let forward = ModelMap::new(
        &labels,
        &ordered,
        label_vertices
            .iter()
            .copied()
            .zip(ordered_vertices.iter().copied()),
    )
    .unwrap();
    let reverse = ModelMap::new(
        &labels,
        &ordered,
        label_vertices
            .iter()
            .copied()
            .zip(ordered_vertices.iter().copied().rev()),
    )
    .unwrap();
    assert!(find_isomorphism(&ordered, &ordered).unwrap().is_some());
    assert!(find_isomorphism_under(&forward, &reverse)
        .unwrap()
        .is_none());
    let other_base = labels.clone();
    let other_map = ModelMap::new(
        &other_base,
        &ordered,
        label_vertices.iter().copied().zip(ordered_vertices),
    )
    .unwrap();
    assert!(find_isomorphism_under(&forward, &other_map).is_err());
}

#[test]
fn isomorphisms_under_a_base_extend_the_specified_images() {
    let (base, base_vertices) = graph(1, &[]);
    let (left, a) = graph(4, &[(0, 1), (1, 2), (2, 0)]);
    let (right, b) = graph(4, &[(1, 2), (2, 3), (3, 1)]);
    let to_left = ModelMap::new(&base, &left, [(base_vertices[0], a[0])]).unwrap();
    let to_right = ModelMap::new(&base, &right, [(base_vertices[0], b[2])]).unwrap();
    let iso = find_isomorphism_under(&to_left, &to_right)
        .unwrap()
        .unwrap();
    check_witness(&iso);
    assert_eq!(iso.apply(a[0]).unwrap(), b[2]);
    assert_eq!(iso.apply(a[1]).unwrap(), b[3]);
    assert_eq!(iso.apply(a[2]).unwrap(), b[1]);
    assert_eq!(iso.apply(a[3]).unwrap(), b[0]);

    let (empty, _) = graph(0, &[]);
    let empty_to_left = ModelMap::new(&empty, &left, []).unwrap();
    let empty_to_right = ModelMap::new(&empty, &right, []).unwrap();
    check_witness(
        &find_isomorphism_under(&empty_to_left, &empty_to_right)
            .unwrap()
            .unwrap(),
    );
}

#[test]
fn isomorphism_search_handles_empty_carriers_and_nullary_relations() {
    let mut source = Model::with_signature(signature(&[0, 1]));
    let target = source.clone();
    check_witness(&find_isomorphism(&source, &target).unwrap().unwrap());
    source.insert(RelationId(0), &[]).unwrap();
    assert!(find_isomorphism(&source, &target).unwrap().is_none());
    assert!(ModelMap::new(&source, &target, []).is_err());
    assert!(ModelMap::new(&target, &source, [])
        .unwrap()
        .inverse()
        .unwrap()
        .is_none());
    check_witness(&find_isomorphism(&source, &source).unwrap().unwrap());
    elements(&mut source, 1);
    assert!(find_isomorphism(&source, &target).unwrap().is_none());

    let empty_signature = Arc::new(Signature::new(vec![], vec![]).unwrap());
    let empty = Model::with_signature(empty_signature);
    check_witness(&find_isomorphism(&empty, &empty).unwrap().unwrap());
}

#[test]
fn isomorphism_search_requires_matching_ordered_signatures() {
    let left = Model::with_signature(signature(&[1, 2]));
    let right = Model::with_signature(signature(&[2, 1]));
    assert_eq!(
        find_isomorphism(&left, &right).err(),
        Some(Error::SignatureMismatch)
    );
    assert_eq!(
        ModelMap::new(&left, &right, []).err(),
        Some(Error::SignatureMismatch)
    );
}

#[test]
fn isomorphism_search_backtracks_on_regular_graphs() {
    let cycle = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)];
    let triangles = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)];
    let (left, _) = graph(6, &cycle);
    let (right, _) = graph(6, &triangles);
    assert!(find_isomorphism(&left, &right).unwrap().is_none());

    let components = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 6), (6, 3)];
    let permutation = [4, 5, 6, 0, 1, 2, 3];
    let permuted: Vec<_> = components
        .iter()
        .map(|&(a, b)| (permutation[a], permutation[b]))
        .collect();
    let (left, _) = graph(8, &components);
    let (right, _) = graph(8, &permuted);
    let iso = find_isomorphism(&left, &right).unwrap().unwrap();
    check_witness(&iso);
    assert_eq!(
        iso.iter().collect::<Vec<_>>(),
        find_isomorphism(&left, &right)
            .unwrap()
            .unwrap()
            .iter()
            .collect::<Vec<_>>()
    );
}

#[test]
fn isomorphism_search_agrees_with_exhaustive_small_graph_oracle() {
    let possible_edges = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)];
    let permutations = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let graphs: Vec<_> = (0..64)
        .map(|mask| {
            let edges: Vec<_> = possible_edges
                .iter()
                .enumerate()
                .filter(|(bit, _)| mask & (1 << bit) != 0)
                .map(|(_, &edge)| edge)
                .collect();
            (graph(3, &edges).0, edges)
        })
        .collect();
    for (left, left_edges) in &graphs {
        for (right, right_edges) in &graphs {
            let right_edges: BTreeSet<_> = right_edges.iter().copied().collect();
            let expected = permutations.iter().any(|permutation| {
                left_edges
                    .iter()
                    .map(|&(a, b)| (permutation[a], permutation[b]))
                    .collect::<BTreeSet<_>>()
                    == right_edges
            });
            let actual = find_isomorphism(left, right).unwrap();
            assert_eq!(actual.is_some(), expected);
            if let Some(map) = actual {
                check_witness(&map);
            }
        }
    }
}

#[test]
fn isomorphism_search_preserves_relation_names_columns_and_repeated_arguments() {
    let shared = signature(&[3, 3]);
    let mut left = Model::with_signature(shared.clone());
    let a = elements(&mut left, 2);
    left.insert(RelationId(0), &[a[0], a[0], a[1]]).unwrap();
    left.insert(RelationId(1), &[a[1], a[0], a[0]]).unwrap();
    let mut right = Model::with_signature(shared.clone());
    let b = elements(&mut right, 2);
    right.insert(RelationId(0), &[b[1], b[1], b[0]]).unwrap();
    right.insert(RelationId(1), &[b[0], b[1], b[1]]).unwrap();
    check_witness(&find_isomorphism(&left, &right).unwrap().unwrap());
    let mut wrong_columns = Model::with_signature(shared.clone());
    let c = elements(&mut wrong_columns, 2);
    wrong_columns
        .insert(RelationId(0), &[c[0], c[1], c[0]])
        .unwrap();
    wrong_columns
        .insert(RelationId(1), &[c[1], c[0], c[0]])
        .unwrap();
    assert!(find_isomorphism(&left, &wrong_columns).unwrap().is_none());
    let mut wrong_relation = Model::with_signature(shared);
    let d = elements(&mut wrong_relation, 2);
    wrong_relation
        .insert(RelationId(1), &[d[0], d[0], d[1]])
        .unwrap();
    wrong_relation
        .insert(RelationId(0), &[d[1], d[0], d[0]])
        .unwrap();
    assert!(find_isomorphism(&left, &wrong_relation).unwrap().is_none());
}

#[test]
fn model_maps_preserve_membership_and_function_graphs() {
    let owner = TypeId(0);
    let member = TypeId(1);
    let signature = Arc::new(
        Signature::new(
            vec![
                Type {
                    name: "Owner".into(),
                    kind: TypeKind::Model,
                    parents: vec![],
                },
                Type {
                    name: "Owner::Member".into(),
                    kind: TypeKind::Plain,
                    parents: vec![owner],
                },
            ],
            vec![
                Relation {
                    name: "membership".into(),
                    kind: RelationKind::Membership(member),
                    arity: vec![owner, member],
                    parents: vec![owner],
                },
                Relation {
                    name: "choose".into(),
                    kind: RelationKind::Function(FunctionKind::Ordinary),
                    arity: vec![owner, member],
                    parents: vec![owner],
                },
            ],
        )
        .unwrap(),
    );
    let mut left = Model::with_signature(signature.clone());
    let a = left.new_element(owner, &[]).unwrap();
    let b = left.new_element(owner, &[]).unwrap();
    let x = left.new_element(member, &[a]).unwrap();
    let y = left.new_element(member, &[b]).unwrap();
    left.insert(RelationId(1), &[a, x]).unwrap();
    let mut right = Model::with_signature(signature);
    let d = right.new_element(owner, &[]).unwrap();
    let c = right.new_element(owner, &[]).unwrap();
    let u = right.new_element(member, &[c]).unwrap();
    let v = right.new_element(member, &[d]).unwrap();
    right.insert(RelationId(1), &[c, u]).unwrap();
    let iso = find_isomorphism(&left, &right).unwrap().unwrap();
    check_witness(&iso);
    assert_eq!(iso.apply(a).unwrap(), c);
    assert_eq!(iso.apply(x).unwrap(), u);
    assert!(ModelMap::new(&left, &right, [(a, c), (b, d), (x, v), (y, u)]).is_err());
    assert!(ModelMap::new(&left, &right, [(a, d), (b, c), (x, v), (y, u)]).is_err());
}

#[test]
fn model_maps_compare_compiled_snapshots_under_their_input() {
    let mut base = Model::new(TransRefl::dynamic_signature());
    let type_ = base.signature().type_named("V").unwrap();
    let edge = base.signature().relation_named("edge").unwrap();
    let a = base.new_element(type_, &[]).unwrap();
    let b = base.new_element(type_, &[]).unwrap();
    base.insert(edge, &[a, b]).unwrap();
    let mut compiled = TransRefl::from_dynamic(&base).unwrap();
    compiled.close();
    let result = compiled.to_dynamic();
    let imported = TransRefl::from_dynamic(&result).unwrap().to_dynamic();
    let left = ModelMap::new(&base, &result, [(a, a), (b, b)]).unwrap();
    let right = ModelMap::new(&base, &imported, [(a, a), (b, b)]).unwrap();
    check_witness(&find_isomorphism_under(&left, &right).unwrap().unwrap());
}
