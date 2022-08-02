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
    pub only_dirty: bool,
}

impl QuerySpec {
    pub fn all() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
            only_dirty: false,
        }
    }
    pub fn all_dirty() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            diagonals: BTreeSet::new(),
            only_dirty: true,
        }
    }
}

impl PartialOrd<QuerySpec> for QuerySpec {
    fn partial_cmp(&self, rhs: &QuerySpec) -> Option<Ordering> {
        use Ordering::*;
        if self.diagonals != rhs.diagonals || self.only_dirty != rhs.only_dirty {
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
pub type IndexSelection = HashMap<String, HashMap<QuerySpec, IndexSpec>>;

pub fn select_indices<'a, QA, AA>(
    module: &Module,
    query_atoms: QA,
    action_atoms: AA,
) -> IndexSelection
where
    QA: IntoIterator<Item = &'a QueryAtom>,
    AA: IntoIterator<Item = &'a ActionAtom>,
{
    // Maps relations to a set of collected query specs. We always need a query for all (dirty)
    // tuples.
    let mut query_specs: HashMap<String, HashSet<QuerySpec>> = module
        .relations()
        .map(|(rel, _)| {
            (
                rel.to_string(),
                hashset! {QuerySpec::all(), QuerySpec::all_dirty()},
            )
        })
        .collect();

    // Add indices for queries.
    for query_atom in query_atoms.into_iter() {
        use QueryAtom::*;
        match query_atom {
            Relation {
                relation,
                diagonals,
                in_projections,
                only_dirty,
                ..
            } => {
                query_specs.get_mut(relation).unwrap().insert(QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: in_projections.keys().copied().collect(),
                    only_dirty: *only_dirty,
                });
            }
            Sort { .. } | Equal(_, _) => (),
        }
    }

    // Add indices for actions.
    for action_atom in action_atoms.into_iter() {
        use ActionAtom::*;
        match action_atom {
            InsertTuple {
                relation,
                in_projections,
                ..
            } => {
                query_specs.get_mut(relation).unwrap().insert(QuerySpec {
                    diagonals: BTreeSet::new(),
                    projections: in_projections.keys().copied().collect(),
                    only_dirty: false,
                });
            }
            Equate { .. } => (),
        }
    }

    query_specs
        .into_iter()
        .map(|(rel, query_specs)| {
            let chains = query_spec_chains(query_specs);
            let query_index_map: HashMap<QuerySpec, IndexSpec> = chains
                .into_iter()
                .flat_map(|queries| {
                    let index = IndexSpec::from_query_spec_chain(
                        module.arity(&rel).unwrap().len(),
                        &queries,
                    );
                    queries.into_iter().zip(repeat(index))
                })
                .collect();
            (rel, query_index_map)
        })
        .collect()
}
