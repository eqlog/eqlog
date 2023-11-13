use std::{
    collections::{BTreeMap, BTreeSet},
    iter::repeat,
};

use super::ast::*;
use super::var_info::*;
use crate::eqlog_util::*;
use crate::index_selection::*;
use eqlog_eqlog::*;
use maplit::btreeset;

pub fn select_indices_v2<'a>(
    if_stmt_rel_infos: &BTreeSet<(&'a FlatIfStmtRelation, &'a RelationInfo)>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> IndexSelection {
    // Every relation needs at least a QuerySpec for all tuples.
    // TODO: Can't we do without the QuerySpec for all dirty tuples though?
    let mut query_specs: BTreeMap<String, BTreeSet<QuerySpec>> = eqlog
        .iter_func()
        .map(Rel::Func)
        .chain(eqlog.iter_pred().map(Rel::Pred))
        .map(|rel| {
            let rel = format!("{}", rel.display(eqlog, identifiers));
            let min_spec_set = btreeset! {QuerySpec::all(), QuerySpec::all_dirty()};
            (rel, min_spec_set)
        })
        .collect();

    // Every func needs in addition a QuerySpec for the arguments to the functino to generate
    // the public eval function and for non surjective then statements.
    for func in eqlog.iter_func() {
        let rel = format!("{}", Rel::Func(func).display(eqlog, identifiers));
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
        let rel = format!("{}", rel.display(eqlog, identifiers));
        let RelationInfo {
            diagonals,
            in_projections,
            out_projections: _,
            quantifier: _,
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
