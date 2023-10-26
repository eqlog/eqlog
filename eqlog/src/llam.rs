use crate::flat_ast::*;
use std::collections::{BTreeMap, BTreeSet};

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
    pub name: Option<String>,
    pub queries: Vec<Vec<QueryAtom>>,
    pub action_inputs: BTreeSet<FlatTerm>,
    pub action: Vec<ActionAtom>,
    pub sorts: BTreeMap<FlatTerm, String>,
}

impl QueryAction {
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
