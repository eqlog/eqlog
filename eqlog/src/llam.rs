use crate::flat_ast::*;
use crate::module::*;
use itertools::Itertools;
use maplit::btreemap;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum Quantifier {
    All,
    // TODO: Add Any quantifier.
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum QueryAtom {
    Equal(FlatTerm, FlatTerm),
    Relation {
        relation: String,
        diagonals: BTreeSet<BTreeSet<usize>>,
        in_projections: BTreeMap<usize, FlatTerm>,
        out_projections: BTreeMap<usize, FlatTerm>,
        only_dirty: bool,
        quantifier: Quantifier,
    },
    Sort {
        sort: String,
        result: FlatTerm,
        only_dirty: bool,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum ActionAtom {
    InsertTuple {
        relation: String,
        in_projections: BTreeMap<usize, FlatTerm>,
        out_projections: BTreeMap<usize, FlatTerm>,
        // Must not have diagonals in out_projections.
    },
    Equate {
        sort: String,
        lhs: FlatTerm,
        rhs: FlatTerm,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct QueryAction {
    pub queries: Vec<Vec<QueryAtom>>,
    pub action_inputs: BTreeMap<FlatTerm, String>,
    pub action: Vec<ActionAtom>,
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

fn in_projections(
    fixed_terms: &HashMap<FlatTerm, String>,
    args: &[FlatTerm],
) -> BTreeMap<usize, FlatTerm> {
    args.iter()
        .copied()
        .enumerate()
        .filter(|(_, tm)| fixed_terms.contains_key(tm))
        .collect()
}

fn out_projections(
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
    module: &Module,
    fixed_terms: &mut HashMap<FlatTerm, String>,
    premise: &[FlatAtom],
) -> Vec<QueryAtom> {
    let premise = premise
        .iter()
        .map(|atom| match atom {
            FlatAtom::Equal(lhs, rhs) => QueryAtom::Equal(*lhs, *rhs),
            FlatAtom::Relation(rel, args) => {
                let diagonals = diagonals(args);
                let in_projections = in_projections(&fixed_terms, args);
                let out_projections = out_projections(&fixed_terms, args);
                let arity = module.arity(rel).unwrap();

                for (arg, sort) in args.iter().copied().zip(arity.iter()) {
                    fixed_terms.insert(arg, sort.to_string());
                }

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
                fixed_terms.insert(*tm, sort.to_string());
                QueryAtom::Sort {
                    sort: sort.clone(),
                    result: *tm,
                    only_dirty: false,
                }
            }
        })
        .collect();
    premise
}

fn translate_conclusion(
    module: &Module,
    fixed_terms: &mut HashMap<FlatTerm, String>,
    conclusion: &[FlatAtom],
) -> Vec<ActionAtom> {
    conclusion
        .iter()
        .map(|atom| match atom {
            FlatAtom::Equal(lhs, rhs) => {
                let sort = fixed_terms.get(lhs).unwrap();
                assert_eq!(sort, fixed_terms.get(rhs).unwrap());
                ActionAtom::Equate {
                    sort: sort.clone(),
                    lhs: *lhs,
                    rhs: *rhs,
                }
            }
            FlatAtom::Relation(rel, args) => {
                let in_projections = in_projections(&fixed_terms, args);
                let out_projections = out_projections(&fixed_terms, args);

                let arity = module.arity(rel).unwrap();
                fixed_terms.extend(
                    out_projections
                        .iter()
                        .map(|(index, tm)| (*tm, arity[*index].to_string())),
                );

                ActionAtom::InsertTuple {
                    relation: rel.to_string(),
                    in_projections,
                    out_projections,
                }
            }
            FlatAtom::Unconstrained(_, _) => {
                panic!("FlatAtom::Unconstrained in conclusion not allowed")
            }
        })
        .collect()
}

fn action_inputs(module: &Module, atoms: &[ActionAtom]) -> BTreeMap<FlatTerm, String> {
    // We add terms that are added during an action to this set. These should not be added to
    // the result.
    let mut new_action_terms = BTreeSet::new();
    // The result.
    let mut query_terms: BTreeMap<FlatTerm, String> = BTreeMap::new();

    for action_atom in atoms.iter() {
        use ActionAtom::*;
        match action_atom {
            InsertTuple {
                relation,
                in_projections,
                out_projections,
            } => {
                // `out_projections` contains terms that are introduced in the action, so
                // they're not in the query.
                new_action_terms.extend(out_projections.values().copied());
                let arity = module.arity(relation).unwrap();
                // Add the terms of `in_projection` unless they were only introduced in the
                // action, not the query.
                query_terms.extend(in_projections.iter().filter_map(|(index, tm)| {
                    if new_action_terms.contains(tm) {
                        None
                    } else {
                        Some((*tm, arity[*index].to_string()))
                    }
                }));
            }
            Equate { lhs, rhs, sort } => {
                if !new_action_terms.contains(lhs) {
                    query_terms.insert(*lhs, sort.to_string());
                }
                if !new_action_terms.contains(rhs) {
                    query_terms.insert(*rhs, sort.to_string());
                }
            }
        }
    }
    query_terms
}

impl QueryAction {
    pub fn functionality(relation: &str, arity: &[&str]) -> Self {
        assert!(!arity.is_empty());
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

        let action_inputs = btreemap! {
            lhs => arity.last().unwrap().to_string(),
            rhs => arity.last().unwrap().to_string(),
        };

        let equate = ActionAtom::Equate {
            sort: arity.last().unwrap().to_string(),
            lhs: FlatTerm(arity.len() - 1),
            rhs: FlatTerm(arity.len()),
        };

        QueryAction {
            queries: vec![vec![lhs_query, rhs_query]],
            action_inputs,
            action: vec![equate],
        }
    }
    pub fn new(module: &Module, sequent: &FlatSequent) -> Self {
        let mut fixed_terms: HashMap<FlatTerm, String> = HashMap::new();
        let query = translate_premise(module, &mut fixed_terms, &sequent.premise);
        let action = translate_conclusion(module, &mut fixed_terms, &sequent.conclusion);
        let action_inputs = action_inputs(module, &action);
        QueryAction {
            queries: vec![query],
            action,
            action_inputs,
        }
    }
    pub fn is_surjective(&self) -> bool {
        self.action.iter().all(|action_atom| {
            use ActionAtom::*;
            match action_atom {
                InsertTuple {
                    out_projections, ..
                } => out_projections.is_empty(),
                Equate { .. } => true,
            }
        })
    }
}

pub struct PureQuery {
    pub inputs: Vec<(FlatTerm, String)>,
    pub output: FlatQueryOutput,
    pub queries: Vec<Vec<QueryAtom>>,
}

impl PureQuery {
    pub fn new(module: &Module, flat_query: &FlatQuery) -> Self {
        let mut fixed_terms: HashMap<FlatTerm, String> =
            flat_query.inputs.iter().cloned().collect();
        let query = translate_premise(module, &mut fixed_terms, &flat_query.atoms);
        PureQuery {
            inputs: flat_query.inputs.clone(),
            output: flat_query.output.clone(),
            queries: vec![query],
        }
    }
}
