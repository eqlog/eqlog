use crate::flat_ast::*;
use crate::llam::*;
use itertools::Itertools;
use maplit::{btreemap, btreeset};
use std::collections::{BTreeMap, BTreeSet};
use std::iter::once;

fn diagonals(args: &[FlatTerm]) -> BTreeSet<BTreeSet<usize>> {
    let mut enumerated_args: Vec<(usize, FlatTerm)> = args.iter().copied().enumerate().collect();
    enumerated_args.sort_by_key(|(_, tm)| *tm);

    enumerated_args
        .iter()
        .group_by(|(_, tm)| tm)
        .into_iter()
        .map(|(_, group)| -> BTreeSet<usize> { group.map(|(i, _)| *i).collect() })
        .filter(|diagonal| diagonal.len() > 1)
        .collect()
}

fn in_projections(
    fixed_terms: &BTreeSet<FlatTerm>,
    args: &[FlatTerm],
) -> BTreeMap<usize, FlatTerm> {
    args.iter()
        .copied()
        .enumerate()
        .filter(|(_, tm)| fixed_terms.contains(tm))
        .collect()
}

fn out_projections(
    fixed_terms: &BTreeSet<FlatTerm>,
    args: &[FlatTerm],
) -> BTreeMap<usize, FlatTerm> {
    args.iter()
        .copied()
        .enumerate()
        .filter(|(_, tm)| !fixed_terms.contains(tm))
        .collect()
}

fn translate_query_atom(fixed_terms: &mut BTreeSet<FlatTerm>, atom: &FlatAtom) -> QueryAtom {
    match atom {
        FlatAtom::Equal(lhs, rhs) => {
            debug_assert!(fixed_terms.contains(lhs));
            debug_assert!(fixed_terms.contains(rhs));
            QueryAtom::Equal(*lhs, *rhs)
        }
        FlatAtom::Relation(rel, args) => {
            let diagonals = diagonals(args);
            let in_projections = in_projections(&fixed_terms, args);
            let out_projections = out_projections(&fixed_terms, args);
            fixed_terms.extend(args.iter().copied());

            QueryAtom::Relation {
                relation: rel.clone(),
                in_projections,
                out_projections,
                diagonals,
                only_dirty: false,
                quantifier: Quantifier::All,
            }
        }
        FlatAtom::Unconstrained(tm, sort) => {
            fixed_terms.insert(*tm);
            QueryAtom::Sort {
                sort: sort.clone(),
                result: *tm,
                only_dirty: false,
            }
        }
    }
}

fn translate_action_atom(
    sorts: &BTreeMap<FlatTerm, String>,
    fixed_terms: &mut BTreeSet<FlatTerm>,
    atom: &FlatAtom,
) -> ActionAtom {
    match atom {
        FlatAtom::Equal(lhs, rhs) => {
            let sort = sorts.get(lhs).unwrap();
            assert_eq!(Some(sort), sorts.get(rhs));
            ActionAtom::Equate {
                sort: sort.to_string(),
                lhs: *lhs,
                rhs: *rhs,
            }
        }
        FlatAtom::Relation(rel, args) => {
            let in_projections = in_projections(&fixed_terms, args);
            let out_projections = out_projections(&fixed_terms, args);

            fixed_terms.extend(out_projections.iter().map(|(_, tm)| *tm));

            ActionAtom::InsertTuple {
                relation: rel.to_string(),
                in_projections,
                out_projections,
            }
        }
        FlatAtom::Unconstrained(_, _) => {
            panic!("FlatAtom::Unconstrained in conclusion not allowed")
        }
    }
}

// TODO: Very convoluted. Just compute used_variables \ introduced_variables.
fn action_inputs(atoms: &[ActionAtom]) -> BTreeSet<FlatTerm> {
    // We add terms that are added during an action to this set. These should not be added to
    // the result.
    let mut new_action_terms = BTreeSet::new();
    // The result.
    let mut query_terms: BTreeSet<FlatTerm> = BTreeSet::new();

    for action_atom in atoms.iter() {
        use ActionAtom::*;
        match action_atom {
            InsertTuple {
                in_projections,
                out_projections,
                ..
            } => {
                // `out_projections` contains terms that are introduced in the action, so
                // they're not in the query.
                new_action_terms.extend(out_projections.values().copied());
                // Add the terms of `in_projection` unless they were only introduced in the
                // action, not the query.
                query_terms.extend(in_projections.iter().filter_map(|(_, tm)| {
                    if new_action_terms.contains(tm) {
                        None
                    } else {
                        Some(*tm)
                    }
                }));
            }
            Equate { lhs, rhs, .. } => {
                if !new_action_terms.contains(lhs) {
                    query_terms.insert(*lhs);
                }
                if !new_action_terms.contains(rhs) {
                    query_terms.insert(*rhs);
                }
            }
        }
    }
    query_terms
}

fn query_outputs(atoms: &[QueryAtom]) -> BTreeSet<FlatTerm> {
    let mut outputs: BTreeSet<FlatTerm> = BTreeSet::new();
    for atom in atoms {
        use QueryAtom::*;
        match atom {
            Relation {
                out_projections, ..
            } => {
                outputs.extend(out_projections.values().copied());
            }
            Sort { result, .. } => {
                outputs.insert(*result);
            }
            Equal { .. } => (),
        }
    }
    outputs
}

#[allow(dead_code)]
pub fn lower_sequent_naive(
    name: Option<String>,
    sequent: &FlatSequent,
    sorts: &BTreeMap<FlatTerm, String>,
) -> QueryAction {
    let mut fixed_terms: BTreeSet<FlatTerm> = BTreeSet::new();
    let query: Vec<QueryAtom> = sequent
        .premise
        .iter()
        .map(|atom| translate_query_atom(&mut fixed_terms, atom))
        .collect();
    let action: Vec<ActionAtom> = sequent
        .conclusion
        .iter()
        .map(|atom| translate_action_atom(sorts, &mut fixed_terms, atom))
        .collect();

    let action_inputs = action_inputs(action.as_slice());
    QueryAction {
        name,
        queries: vec![query],
        action,
        action_inputs,
        sorts: sorts.clone(),
    }
}

pub fn lower_premise_atoms_seminaive(atoms: &[FlatAtom], dirty_index: usize) -> Vec<QueryAtom> {
    let mut fixed_terms: BTreeSet<FlatTerm> = BTreeSet::new();
    let mut dirty_atom = translate_query_atom(&mut fixed_terms, &atoms[dirty_index]);
    match &mut dirty_atom {
        QueryAtom::Relation { only_dirty, .. } | QueryAtom::Sort { only_dirty, .. } => {
            *only_dirty = true
        }
        QueryAtom::Equal(_, _) => panic!("Equal in premise of sequents should not occur"),
    }

    once(dirty_atom)
        .chain(
            atoms[..dirty_index]
                .iter()
                .chain(atoms[dirty_index + 1..].iter())
                .map(|atom| translate_query_atom(&mut fixed_terms, atom)),
        )
        .collect()
}

#[allow(dead_code)]
pub fn lower_sequent_seminaive(
    name: &Option<String>,
    sequent: &FlatSequent,
    sorts: &BTreeMap<FlatTerm, String>,
) -> QueryAction {
    let queries: Vec<Vec<QueryAtom>> = if sequent.premise.is_empty() {
        vec![vec![]]
    } else {
        (0..sequent.premise.len())
            .map(|dirty_index| lower_premise_atoms_seminaive(&sequent.premise, dirty_index))
            .collect()
    };

    let mut fixed_terms = query_outputs(queries.first().unwrap());

    let action: Vec<ActionAtom> = sequent
        .conclusion
        .iter()
        .map(|atom| translate_action_atom(sorts, &mut fixed_terms, atom))
        .collect();

    let action_inputs = action_inputs(action.as_slice());
    QueryAction {
        name: name.clone(),
        queries,
        action,
        action_inputs,
        sorts: sorts.clone(),
    }
}

pub fn functionality(relation: &str, arity: &[&str]) -> QueryAction {
    assert!(!arity.is_empty());
    let sorts: BTreeMap<FlatTerm, String> = arity
        .iter()
        .enumerate()
        .chain(once((arity.len(), arity.last().unwrap())))
        .map(|(i, s)| (FlatTerm(i), s.to_string()))
        .collect();

    let lhs_query = QueryAtom::Relation {
        relation: relation.to_string(),
        diagonals: BTreeSet::new(),
        in_projections: BTreeMap::new(),
        out_projections: (0..arity.len()).map(|i| (i, FlatTerm(i))).collect(),
        only_dirty: false,
        quantifier: Quantifier::All,
    };
    let rhs_query = QueryAtom::Relation {
        relation: relation.to_string(),
        diagonals: BTreeSet::new(),
        in_projections: (0..arity.len() - 1).map(|i| (i, FlatTerm(i))).collect(),
        out_projections: btreemap! { arity.len() - 1 => FlatTerm(arity.len())},
        only_dirty: false,
        quantifier: Quantifier::All,
    };

    let lhs = FlatTerm(arity.len() - 1);
    let rhs = FlatTerm(arity.len());

    let action_inputs = btreeset! { lhs, rhs };

    let equate = ActionAtom::Equate {
        sort: arity.last().unwrap().to_string(),
        lhs: FlatTerm(arity.len() - 1),
        rhs: FlatTerm(arity.len()),
    };

    QueryAction {
        name: Some(format!("functionality_{relation}")),
        queries: vec![vec![lhs_query, rhs_query]],
        sorts,
        action_inputs,
        action: vec![equate],
    }
}
