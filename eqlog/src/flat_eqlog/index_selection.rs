use std::{
    collections::{BTreeMap, BTreeSet},
    iter::once,
};

use super::ast::*;
use crate::algebra::signature::{FuncId, Signature, TypeId};
use itertools::Itertools as _;
use maplit::btreeset;
use std::sync::Arc;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct QuerySpec {
    pub age: QueryAge,
    pub projections: BTreeSet<usize>,
}

fn premise_query_specs<'a>(
    premise: &'a [FlatIfStmt],
) -> impl 'a + Iterator<Item = (FlatInRel, QuerySpec)> {
    let mut fixed_vars: BTreeSet<FlatVar> = BTreeSet::new();
    premise.into_iter().map(move |stmt| {
        let FlatIfStmt { rel, args, age } = stmt;
        let projections: BTreeSet<usize> = stmt
            .args
            .iter()
            .enumerate()
            .filter_map(|(i, arg)| {
                if fixed_vars.contains(arg) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect();
        fixed_vars.extend(args.iter().cloned());

        let query_spec = QuerySpec {
            age: age.clone(),
            projections,
        };
        (rel.clone(), query_spec)
    })
}

impl QuerySpec {
    /// The specs needed to query for all tuples in a relation.
    pub fn all() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            age: QueryAge::All,
        }
    }
    /// The specs needed to query for all old tuples in a relation.
    pub fn all_old() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            age: QueryAge::Old,
        }
    }
    /// The [QuerySpec] to query for all new tuples in a relation.
    pub fn all_new() -> Self {
        QuerySpec {
            projections: BTreeSet::new(),
            age: QueryAge::New,
        }
    }
    /// The [QuerySpec] to query for one specific tuple in a relation.
    pub fn one(rel: FlatInRel, signature: &Signature) -> Self {
        let arity = rel.arity(signature);
        QuerySpec {
            projections: (0..arity.len()).collect(),
            age: QueryAge::All,
        }
    }
    /// The [QuerySpec] for evaluating a function.
    pub fn eval_func(func: FuncId, signature: &Signature) -> Self {
        let flat_dom = flat_domain(func, signature);
        let rel = FlatInRel::Rel(FlatRel::Func(func));
        let arity = rel.arity(signature);
        assert!(
            arity.len() > 0,
            "The codomain of a function is always in the arity"
        );
        QuerySpec {
            projections: (0..flat_dom.len()).collect(),
            age: QueryAge::All,
        }
    }

    pub fn member_parents(member_type: TypeId, signature: &Signature) -> Self {
        QuerySpec {
            projections: btreeset! {signature.type_(member_type).parents.len()},
            age: QueryAge::All,
        }
    }
}

/// Partitions a list of [QuerySpec] into ascending chains with respect to the set of projections.
pub fn query_spec_chains(mut specs: Vec<QuerySpec>) -> Vec<Vec<QuerySpec>> {
    // Strategy: Maintain a list of chains.
    // Check for each input spec whether it fits into an existing chain or add a new singleton
    // chain. Because we sort the specs wrt to the number of projections, it suffices to check
    // chain compatibility with only the last element of a given chain.
    specs.sort_by_key(|spec| spec.projections.len());

    let mut chains: Vec<Vec<QuerySpec>> = Vec::new();
    for spec in specs.into_iter() {
        let compatible_chain = chains.iter_mut().find(|chain| {
            let last = chain.last().unwrap();
            last.projections.is_subset(&spec.projections)
        });
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
    pub order: Arc<[usize]>,
    pub age: IndexAge,
}

impl IndexSpec {
    fn from_query_spec_chain(arity_len: usize, chain: &[QuerySpec]) -> Vec<Self> {
        let empty_projections = BTreeSet::new();
        let full_projections: BTreeSet<usize> = (0..arity_len).collect();

        // Some `impl Iterator<&BTreeSet<usize>`:
        let proj_chain = chain.iter().map(|query| &query.projections);
        let bot_chain = once(&empty_projections).chain(proj_chain.clone());
        let top_chain = proj_chain.chain(once(&full_projections));
        // An `impl Iterator<BTreeSet<usize>`:
        let diffs = bot_chain.zip(top_chain).map(|(prev, next)| next - prev);

        let order: Vec<usize> = diffs.flatten().collect();

        let ages: BTreeSet<IndexAge> = chain
            .iter()
            .flat_map(|query| match query.age {
                QueryAge::All => vec![IndexAge::Old, IndexAge::New],
                QueryAge::New => vec![IndexAge::New],
                QueryAge::Old => vec![IndexAge::Old],
            })
            .collect();

        ages.into_iter()
            .map(|age| IndexSpec {
                order: order.clone().into(),
                age,
            })
            .collect()
    }
}

// Maps relation name and query spec to the index of the the relation that can serve the query.
//pub type IndexSelection = BTreeMap<(FlatInRel, QuerySpec), Vec<IndexSpec>>;
pub struct IndexSelection {
    pub indices: BTreeMap<FlatInRel, Vec<IndexSpec>>,
    pub queries: BTreeMap<(FlatInRel, QuerySpec), Vec<IndexSpec>>,
}

pub fn iter_flat_rels(signature: &Signature) -> impl Iterator<Item = FlatRel> + '_ {
    signature
        .iter_preds()
        .map(FlatRel::Pred)
        .chain(signature.iter_funcs().map(FlatRel::Func))
        .chain(signature.iter_types().filter_map(|typ| {
            (!signature.type_(typ).parents.is_empty()).then_some(FlatRel::ModelMember(typ))
        }))
}

pub fn select_indices<'a>(
    rules: impl IntoIterator<Item = &'a FlatRule>,
    signature: &Signature,
) -> IndexSelection {
    let mut query_specs: BTreeSet<(FlatInRel, QuerySpec)> = BTreeSet::new();

    query_specs.extend(
        rules
            .into_iter()
            .flat_map(|rule| premise_query_specs(rule.premise.as_slice())),
    );

    // Query specs to generate public API functions.
    // TODO: Should probably generate flat eqlog premises for these and pass like normal rule
    // premises to this function.

    // The query specs for public relation functions
    // - The iter_{rel}() method needs a QuerySpec to iterate over all tuples.
    // - The contains_{rel}() method needs a QuerySpec to check for one specific tuple.
    query_specs.extend(iter_flat_rels(signature).flat_map(|rel| {
        let rel = FlatInRel::Rel(rel);
        let new_spec = QuerySpec::all_new();
        let old_spec = QuerySpec::all_old();
        let iter_all_spec = QuerySpec::all();
        let check_one_spec = QuerySpec::one(rel.clone(), signature);
        [
            (rel.clone(), new_spec),
            (rel.clone(), old_spec),
            (rel.clone(), iter_all_spec),
            (rel.clone(), check_one_spec),
        ]
    }));

    // The query specs to iterate over element of a given type.
    query_specs.extend(signature.iter_types().flat_map(|ty| {
        let rel = FlatInRel::TypeSet(ty);
        [
            (rel.clone(), QuerySpec::all()),
            (rel.clone(), QuerySpec::all_new()),
        ]
    }));

    // The query specs for public function evaluation functions.
    query_specs.extend(signature.iter_funcs().map(|func| {
        (
            FlatInRel::Rel(FlatRel::Func(func)),
            QuerySpec::eval_func(func, signature),
        )
    }));

    // Nested morphism checks recover parent chains from membership, including
    // inherited tuples, without scanning every member in the model.
    query_specs.extend(signature.iter_mor_app_funcs().filter_map(|(types, _)| {
        let parent_len = signature.type_(types.member_type).parents.len();
        let outer_len = signature.type_(types.morphism_type).parents.len();
        if parent_len <= outer_len + 1 {
            return None;
        }
        Some((
            FlatInRel::Rel(FlatRel::ModelMember(types.member_type)),
            QuerySpec::member_parents(types.member_type, signature),
        ))
    }));

    // The query specs needed for topological sorting of the model morphism graph.
    query_specs.extend(signature.iter_model_decls().flat_map(|(_decl, ids)| {
        let mor_type = FlatInRel::TypeSet(ids.mor);
        let dom = FlatInRel::Rel(FlatRel::Func(ids.dom));
        let cod = FlatInRel::Rel(FlatRel::Func(ids.cod));
        // `dom`/`cod` flatten as (parents..., mor, obj). Toposort needs
        // "given parents+object, outgoing mors" and "given parents+mor, obj".
        let parent_len = signature.func(ids.dom).parents.len();
        let mut dom_projections = (0..parent_len).collect::<BTreeSet<_>>();
        dom_projections.insert(parent_len + 1);
        let cod_projections = (0..=parent_len).collect::<BTreeSet<_>>();

        [
            // Given an object (and parent, when nested), look up outgoing morphisms.
            (
                dom,
                QuerySpec {
                    age: QueryAge::All,
                    projections: dom_projections,
                },
            ),
            // Given a morphism (and parent, when nested), look up the codomain.
            (
                cod,
                QuerySpec {
                    age: QueryAge::All,
                    projections: cod_projections,
                },
            ),
            (
                mor_type,
                QuerySpec {
                    age: QueryAge::All,
                    projections: btreeset! {0},
                },
            ),
        ]
    }));

    // Topological sorting groups model objects by their enclosing parents.
    // Preserve that prefix order even when membership also needs a reverse index.
    query_specs.extend(signature.iter_model_decls().flat_map(|(_, ids)| {
        let rel = FlatInRel::Rel(FlatRel::ModelMember(ids.type_));
        (1..=signature.type_(ids.type_).parents.len()).map(move |prefix_len| {
            (
                rel.clone(),
                QuerySpec {
                    age: QueryAge::All,
                    projections: (0..prefix_len).collect(),
                },
            )
        })
    }));

    let queries: BTreeMap<(FlatInRel, QuerySpec), Vec<IndexSpec>> = query_specs
        .into_iter()
        .chunk_by(|(rel, _query_spec)| rel.clone())
        .into_iter()
        .flat_map(|(rel, queries)| {
            let queries: Vec<QuerySpec> = queries.map(|(_rel, query)| query).collect();
            let query_chains = query_spec_chains(queries);

            let arity = rel.arity(signature);

            query_chains.into_iter().flat_map(move |query_chain| {
                let indices = IndexSpec::from_query_spec_chain(arity.len(), query_chain.as_slice());
                let rel = rel.clone();
                query_chain.into_iter().map(move |query| {
                    let indices = match query.age {
                        QueryAge::All => indices.clone(),
                        QueryAge::New => indices
                            .iter()
                            .filter(|index| index.age == IndexAge::New)
                            .cloned()
                            .collect(),
                        QueryAge::Old => indices
                            .iter()
                            .filter(|index| index.age == IndexAge::Old)
                            .cloned()
                            .collect(),
                    };
                    ((rel.clone(), query), indices)
                })
            })
        })
        .collect();

    // Compute indices map from queries map
    let mut indices: BTreeMap<FlatInRel, Vec<IndexSpec>> = BTreeMap::new();
    for ((rel, _query_spec), index_specs) in queries.iter() {
        indices
            .entry(rel.clone())
            .or_insert_with(Vec::new)
            .extend(index_specs.iter().cloned());
    }
    // Deduplicate indices for each relation
    for index_specs in indices.values_mut() {
        index_specs.sort();
        index_specs.dedup();
    }

    IndexSelection { indices, queries }
}
