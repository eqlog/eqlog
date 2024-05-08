use std::{
    collections::{BTreeMap, BTreeSet},
    iter::{once, repeat},
};

use super::ast::*;
use super::var_info::*;
use crate::eqlog_util::*;
use eqlog_eqlog::*;
use maplit::btreeset;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct QuerySpec {
    pub projections: BTreeSet<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
    pub only_dirty: bool,
}

impl QuerySpec {
    /// The [QuerySpec] to query for all tuples in a relation.
    pub fn all() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
            only_dirty: false,
        }
    }
    /// The [QuerySpec] to query for all dirty tuples in a relation.
    pub fn all_dirty() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
            only_dirty: true,
        }
    }
    /// The [QuerySpec] to query for one specific tuple in a relation.
    pub fn one(rel: Rel, eqlog: &Eqlog) -> Self {
        let arity_len =
            type_list_vec(eqlog.arity(rel).expect("arity should be total"), eqlog).len();
        QuerySpec {
            projections: (0..arity_len).collect(),
            diagonals: BTreeSet::new(),
            only_dirty: false,
        }
    }
    /// The [QuerySpec] for evaluating a function.
    pub fn eval_func(func: Func, eqlog: &Eqlog) -> Self {
        let domain = eqlog.domain(func).expect("domain should be total");
        let dom_len = type_list_vec(domain, eqlog).len();
        QuerySpec {
            projections: (0..dom_len).collect(),
            diagonals: BTreeSet::new(),
            only_dirty: false,
        }
    }

    pub fn le_restrictive(&self, rhs: &QuerySpec) -> bool {
        if self.diagonals != rhs.diagonals || self.only_dirty != rhs.only_dirty {
            false
        } else {
            self.projections.is_subset(&rhs.projections)
        }
    }
}

pub fn query_spec_chains(indices: BTreeSet<QuerySpec>) -> Vec<Vec<QuerySpec>> {
    let mut specs: Vec<QuerySpec> = indices.into_iter().collect();
    specs.sort_by_key(|index| index.projections.len());

    let mut chains: Vec<Vec<QuerySpec>> = Vec::new();
    for spec in specs.into_iter() {
        // TODO: Don't we have to check that `spec` fits anywhere into a given chain, not just at
        // the end?
        let compatible_chain = chains
            .iter_mut()
            .find(|chain| chain.last().unwrap().le_restrictive(&spec));
        match compatible_chain {
            Some(compatible_chain) => compatible_chain.push(spec),
            None => chains.push(vec![spec]),
        }
    }
    chains
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IndexSpec {
    pub order: Vec<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
    pub only_dirty: bool,
}

fn is_prefix(prefix: &BTreeSet<usize>, order: &[usize]) -> bool {
    let count = order.iter().take_while(|el| prefix.contains(el)).count();
    count == prefix.len()
}

impl IndexSpec {
    pub fn can_serve(&self, query: &QuerySpec) -> bool {
        self.only_dirty == query.only_dirty
            && query.diagonals == self.diagonals
            && is_prefix(&query.projections, &self.order)
    }
    pub fn from_query_spec_chain(arity_len: usize, chain: &[QuerySpec]) -> Self {
        let empty_projections = BTreeSet::new();
        let full_projections: BTreeSet<usize> = (0..arity_len).collect();

        // Some `impl Iterator<&BTreeSet<usize>`:
        let proj_chain = chain.iter().map(|query| &query.projections);
        let bot_chain = once(&empty_projections).chain(proj_chain.clone());
        let top_chain = proj_chain.chain(once(&full_projections));
        // An `impl Iterator<BTreeSet<usize>`:
        let diffs = bot_chain.zip(top_chain).map(|(prev, next)| next - prev);

        let order: Vec<usize> = diffs.flatten().collect();

        let last = chain.last().unwrap();
        let diagonals = last.diagonals.clone();
        let only_dirty = last.only_dirty;
        IndexSpec {
            order,
            diagonals,
            only_dirty,
        }
    }
}

// Maps relation name and query spec to an index for the relation that can serve the query.
pub type IndexSelection = BTreeMap<String, BTreeMap<QuerySpec, IndexSpec>>;

pub fn select_indices<'a>(
    if_stmt_rel_infos: &BTreeSet<(&'a FlatIfStmtRelation, &'a RelationInfo)>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> IndexSelection {
    // Every relation needs a QuerySpec for all tuples, and a QuerySpec for one specific tuple.
    // TODO: Can't we do without the QuerySpec for all dirty tuples though?
    let mut query_specs: BTreeMap<String, BTreeSet<QuerySpec>> = eqlog
        .iter_rel()
        .map(|rel| {
            let min_spec_set =
                btreeset! {QuerySpec::all(), QuerySpec::one(rel, eqlog), QuerySpec::all_dirty()};
            let rel = format!("{}", display_rel(rel, eqlog, identifiers));
            (rel, min_spec_set)
        })
        .collect();

    // Every func needs in addition a QuerySpec for the arguments to the functino to generate
    // the public eval function and for non surjective then statements.
    for func in eqlog.iter_func() {
        let rel = format!(
            "{}",
            display_rel(eqlog.func_rel(func).unwrap(), eqlog, identifiers)
        );
        let spec = QuerySpec::eval_func(func, eqlog);
        query_specs.get_mut(rel.as_str()).unwrap().insert(spec);
    }

    // Every relation if stmt needs a QuerySpec.
    for (if_stmt_rel, info) in if_stmt_rel_infos {
        let FlatIfStmtRelation {
            rel,
            args: _,
            only_dirty,
        } = if_stmt_rel;
        let rel = format!("{}", display_rel(*rel, eqlog, identifiers));
        let RelationInfo {
            diagonals,
            in_projections,
            out_projections: _,
        } = info;
        let spec = QuerySpec {
            diagonals: diagonals.clone(),
            projections: in_projections.keys().copied().collect(),
            only_dirty: *only_dirty,
        };
        query_specs.get_mut(rel.as_str()).unwrap().insert(spec);
    }

    query_specs
        .into_iter()
        .map(|(rel, query_specs)| {
            let chains = query_spec_chains(query_specs);
            let query_index_map: BTreeMap<QuerySpec, IndexSpec> = chains
                .into_iter()
                .flat_map(|queries| {
                    let index = IndexSpec::from_query_spec_chain(
                        get_arity(&rel, eqlog, identifiers).unwrap().len(),
                        &queries,
                    );
                    queries.into_iter().zip(repeat(index))
                })
                .collect();
            (rel, query_index_map)
        })
        .collect()
}
