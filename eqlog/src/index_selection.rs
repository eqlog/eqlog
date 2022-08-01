use crate::llam::*;
use crate::module::Module;
use maplit::hashset;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::iter::{once, repeat};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct QuerySpec {
    pub projections: BTreeSet<usize>,
    pub diagonals: BTreeSet<BTreeSet<usize>>,
}

impl QuerySpec {
    pub fn new() -> QuerySpec {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
        }
    }
}

impl PartialOrd<QuerySpec> for QuerySpec {
    fn partial_cmp(&self, rhs: &QuerySpec) -> Option<Ordering> {
        use Ordering::*;
        if self.diagonals != rhs.diagonals {
            None
        } else if self.projections == rhs.projections {
            Some(Equal)
        } else if self.projections.is_subset(&rhs.projections) {
            Some(Less)
        } else if self.projections.is_superset(&rhs.projections) {
            Some(Greater)
        } else {
            None
        }
    }
}

fn query_spec_chains(indices: HashSet<QuerySpec>) -> Vec<Vec<QuerySpec>> {
    let mut specs: Vec<QuerySpec> = indices.into_iter().collect();
    specs.sort_by_key(|index| index.projections.len());

    let mut chains: Vec<Vec<QuerySpec>> = Vec::new();
    for spec in specs.into_iter() {
        let compatible_chain = chains
            .iter_mut()
            .find(|chain| spec >= *chain.last().unwrap());
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
}

fn is_prefix(prefix: &BTreeSet<usize>, order: &[usize]) -> bool {
    let count = order.iter().take_while(|el| prefix.contains(el)).count();
    count == prefix.len()
}

impl IndexSpec {
    pub fn can_serve(&self, query: &QuerySpec) -> bool {
        query.diagonals == self.diagonals && is_prefix(&query.projections, &self.order)
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

        let diagonals = chain.last().unwrap().diagonals.clone();
        IndexSpec { order, diagonals }
    }
}

// Maps relation name and query spec to an index for the relation that can serve the query.
pub type IndexSelection = HashMap<String, HashMap<QuerySpec, IndexSpec>>;

pub fn select_indices<'a, Queries>(module: &Module, queries: Queries) -> IndexSelection
where
    Queries: IntoIterator<Item = &'a Query>,
{
    // Maps relations to tuple of arity.len() and set of collected query specs.
    let mut query_specs: HashMap<String, (usize, HashSet<QuerySpec>)> = module
        .relations()
        .map(|(rel, arity)| (rel.to_string(), (arity.len(), hashset! {QuerySpec::new()})))
        .collect();

    // Add indices for (implicit) functionality axioms.
    for func in module.iter_functions() {
        let spec = QuerySpec {
            projections: (0..func.dom.len()).collect(),
            diagonals: BTreeSet::new(),
        };
        query_specs.get_mut(&func.name).unwrap().1.insert(spec);
    }

    // Add indices for queries.
    for query in queries.into_iter() {
        use Query::*;
        match query {
            Relation {
                relation,
                diagonals,
                projections,
                ..
            } => {
                query_specs.get_mut(relation).unwrap().1.insert(QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: projections.keys().copied().collect(),
                });
            }
            Sort { .. } | Equal(_, _) => (),
        }
    }

    query_specs
        .into_iter()
        .map(|(rel, (arity_len, query_specs))| {
            let chains = query_spec_chains(query_specs);
            let query_index_map: HashMap<QuerySpec, IndexSpec> = chains
                .into_iter()
                .flat_map(|queries| {
                    let index = IndexSpec::from_query_spec_chain(arity_len, &queries);
                    queries.into_iter().zip(repeat(index))
                })
                .collect();
            (rel, query_index_map)
        })
        .collect()
}
