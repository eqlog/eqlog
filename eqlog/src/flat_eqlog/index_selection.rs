use std::{
    collections::{BTreeMap, BTreeSet},
    iter::{once, repeat},
};

use super::ast::*;
use crate::eqlog_util::*;
use eqlog_eqlog::*;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct QuerySpec {
    pub projections: BTreeSet<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
    pub age: QueryAge,
}

impl QuerySpec {
    /// The specs needed to query for all tuples in a relation.
    pub fn all() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
            age: QueryAge::All,
        }
    }
    // TODO: Rename this to all_new.
    /// The [QuerySpec] to query for all dirty tuples in a relation.
    pub fn all_dirty() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
            age: QueryAge::New,
        }
    }
    /// The [QuerySpec] to query for one specific tuple in a relation.
    pub fn one(rel: Rel, eqlog: &Eqlog) -> Self {
        let arity_len =
            type_list_vec(eqlog.flat_arity(rel).expect("arity should be total"), eqlog).len();
        QuerySpec {
            projections: (0..arity_len).collect(),
            diagonals: BTreeSet::new(),
            age: QueryAge::All,
        }
    }
    /// The [QuerySpec] for evaluating a function.
    pub fn eval_func(func: Func, eqlog: &Eqlog) -> Self {
        let domain = eqlog.flat_domain(func).expect("domain should be total");
        let dom_len = type_list_vec(domain, eqlog).len();
        QuerySpec {
            projections: (0..dom_len).collect(),
            diagonals: BTreeSet::new(),
            age: QueryAge::All,
        }
    }

    pub fn le_restrictive(&self, rhs: &QuerySpec) -> bool {
        if self.diagonals != rhs.diagonals || self.age != rhs.age {
            false
            // In case we're querying for a single tuple, we should also consider a QueryAge::New
            // spec to be less restrictive than a QueryAge::All spec.
        } else {
            self.projections.is_subset(&rhs.projections)
        }
    }
}

pub fn query_spec_chains(indices: &BTreeSet<QuerySpec>) -> Vec<Vec<QuerySpec>> {
    let mut specs: Vec<QuerySpec> = indices.into_iter().cloned().collect();
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

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum IndexAge {
    New,
    Old,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IndexSpec {
    pub order: Vec<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
    pub age: IndexAge,
}

impl IndexSpec {
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
        let age = match last.age {
            QueryAge::All => panic!("QueryAge::All should have been desugared"),
            QueryAge::New => IndexAge::New,
            QueryAge::Old => IndexAge::Old,
        };
        IndexSpec {
            order,
            diagonals,
            age,
        }
    }
}

// Maps relation name and query spec to the index of the the relation that can serve the query.
pub type IndexSelection = BTreeMap<String, BTreeMap<QuerySpec, IndexSpec>>;

pub fn select_indices(
    flat_analyses: &[FlatRuleAnalysis],
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> IndexSelection {
    let if_stmt_rel_infos: BTreeSet<(&FlatIfStmtRelation, &RelationInfo)> = flat_analyses
        .iter()
        .flat_map(|analysis| analysis.if_stmt_rel_infos.iter())
        .map(|(ByAddress(if_stmt_rel), info)| (*if_stmt_rel, info))
        .collect();

    // Every relation needs a QuerySpec for all tuples, and a QuerySpec for one specific tuple.
    // TODO: Can't we do without the QuerySpec for all dirty tuples though?
    let mut query_specs: BTreeMap<Rel, BTreeSet<QuerySpec>> = eqlog
        .iter_rel()
        .map(|rel| {
            let mut min_spec_set: BTreeSet<QuerySpec> = BTreeSet::new();
            min_spec_set.extend(QuerySpec::all());
            min_spec_set.insert(QuerySpec::all_dirty());
            min_spec_set.extend(QuerySpec::one(rel, eqlog));
            (rel, min_spec_set)
        })
        .collect();

    // Every func needs in addition a QuerySpec for the arguments to the function to generate
    // the public eval function and for non surjective then statements.
    for func in eqlog.iter_func() {
        let rel = eqlog.func_rel(func).unwrap();
        query_specs
            .get_mut(&rel)
            .unwrap()
            .extend(QuerySpec::eval_func(func, eqlog));
    }

    // Every relation if stmt needs a QuerySpec.
    for (if_stmt_rel, info) in if_stmt_rel_infos.iter() {
        let FlatIfStmtRelation { rel, args: _, age } = if_stmt_rel;
        let RelationInfo {
            diagonals,
            in_projections,
            out_projections: _,
            age: _,
            rel: _,
        } = info;
        let spec = QuerySpec {
            diagonals: diagonals.clone(),
            projections: in_projections.keys().copied().collect(),
            age: *age,
        };
        query_specs.get_mut(rel).unwrap().insert(spec);
    }

    query_specs
        .into_iter()
        .map(|(rel, query_specs)| {
            let chains = query_spec_chains(&query_specs);
            let query_index_map: BTreeMap<QuerySpec, IndexSpec> = chains
                .into_iter()
                .flat_map(|queries| {
                    let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
                    let index = IndexSpec::from_query_spec_chain(arity.len(), &queries);
                    queries.into_iter().zip(repeat(index))
                })
                .collect();

            let rel = display_rel(rel, eqlog, identifiers).to_string();
            (rel, query_index_map)
        })
        .collect()
}
