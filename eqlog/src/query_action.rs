use crate::flat_ast::*;
use crate::indirect_ast::*;
use crate::signature::*;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Query {
    Relation {
        relation: String,
        diagonals: BTreeSet<BTreeSet<usize>>,
        projections: BTreeMap<usize, FlatTerm>,
        results: BTreeMap<usize, FlatTerm>,
    },
    Sort {
        sort: String,
        result: FlatTerm,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Action {
    AddTerm {
        function: String,
        args: Vec<FlatTerm>,
        result: FlatTerm,
    },
    AddTuple {
        relation: String,
        args: Vec<FlatTerm>,
    },
    Equate {
        sort: String,
        lhs: FlatTerm,
        rhs: FlatTerm,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct QueryAction {
    pub queries: Vec<Query>,
    pub actions: Vec<Action>,
}

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

fn projections(
    fixed_terms: &HashMap<FlatTerm, String>,
    args: &[FlatTerm],
) -> BTreeMap<usize, FlatTerm> {
    args.iter()
        .copied()
        .enumerate()
        .filter(|(_, tm)| fixed_terms.contains_key(tm))
        .collect()
}

fn results(
    fixed_terms: &HashMap<FlatTerm, String>,
    args: &[FlatTerm],
) -> BTreeMap<usize, FlatTerm> {
    args.iter()
        .copied()
        .enumerate()
        .filter(|(_, tm)| !fixed_terms.contains_key(tm))
        .collect()
}

fn translate_premise(
    signature: &Signature,
    premise: &[FlatAtom],
) -> (Vec<Query>, HashMap<FlatTerm, String>) {
    let mut fixed_terms: HashMap<FlatTerm, String> = HashMap::new();
    let premise = premise
        .iter()
        .map(|atom| {
            use FlatAtom::*;
            match atom {
                Equal(_, _) => {
                    panic!("FlatAtom::Equal in premise not supported")
                }
                Relation(rel, args) => {
                    let diagonals = diagonals(args);
                    let projections = projections(&fixed_terms, args);
                    let results = results(&fixed_terms, args);
                    let arity = signature.arity(rel).unwrap();

                    for (arg, sort) in args.iter().copied().zip(arity.iter()) {
                        fixed_terms.insert(arg, sort.to_string());
                    }

                    Query::Relation {
                        relation: rel.clone(),
                        projections,
                        diagonals,
                        results,
                    }
                }
                Unconstrained(tm, sort) => {
                    fixed_terms.insert(*tm, sort.to_string());
                    Query::Sort {
                        sort: sort.clone(),
                        result: *tm,
                    }
                }
            }
        })
        .collect();
    (premise, fixed_terms)
}

fn translate_conclusion(
    signature: &Signature,
    mut fixed_terms: HashMap<FlatTerm, String>,
    conclusion: &[FlatAtom],
) -> Vec<Action> {
    conclusion
        .iter()
        .map(|atom| {
            use FlatAtom::*;
            match atom {
                Equal(lhs, rhs) => {
                    let sort = fixed_terms.get(lhs).unwrap();
                    assert_eq!(sort, fixed_terms.get(rhs).unwrap());
                    Action::Equate {
                        sort: sort.clone(),
                        lhs: *lhs,
                        rhs: *rhs,
                    }
                }
                Relation(rel, args) if args.is_empty() => Action::AddTuple {
                    relation: rel.clone(),
                    args: Vec::new(),
                },
                Relation(rel, rel_args) => {
                    let relation = rel.clone();
                    let mut args: Vec<FlatTerm> =
                        rel_args.iter().copied().take(rel_args.len() - 1).collect();
                    for arg in args.iter() {
                        assert!(fixed_terms.contains_key(arg));
                    }

                    let result = rel_args.last().copied().unwrap();
                    if fixed_terms.contains_key(&result) {
                        args.push(result);
                        Action::AddTuple { relation, args }
                    } else {
                        let function = relation;
                        let Function { cod, .. } = signature.functions().get(rel).unwrap();
                        fixed_terms.insert(result, cod.to_string());
                        Action::AddTerm {
                            function,
                            args,
                            result,
                        }
                    }
                }
                Unconstrained(_, _) => {
                    panic!("FlatAtom::Unconstrained in conclusion not allowed")
                }
            }
        })
        .collect()
}

impl QueryAction {
    pub fn new(signature: &Signature, sequent: &FlatSequent) -> Self {
        let (queries, fixed_terms) = translate_premise(signature, &sequent.premise);
        let actions = translate_conclusion(signature, fixed_terms, &sequent.conclusion);
        QueryAction { queries, actions }
    }
}
