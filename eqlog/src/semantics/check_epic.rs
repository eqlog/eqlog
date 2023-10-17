use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::once;

use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn iter_surjectivity_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let should_be_ok: BTreeSet<El> = eqlog.iter_el_should_be_surjective_ok().collect();
    let is_ok: BTreeSet<El> = eqlog.iter_el_is_surjective_ok().collect();
    should_be_ok
        .into_iter()
        .filter(move |el| !is_ok.contains(el))
        .flat_map(move |el| {
            let mut tms = eqlog.iter_semantic_el().filter_map(move |(tm, tm_el)| {
                if eqlog.are_equal_el(tm_el, el) {
                    Some(tm)
                } else {
                    None
                }
            });

            // The semantics are set up such that every new element (and only those need to be
            // surjective-ok) must be the semantics of at least one term. To make sure that we
            // don't accidentally suppress an error here, we take on term from the iterator (making
            // sure that there is one!) and put it back afterwards.
            let first_tm = tms
                .next()
                .expect("every new element should correspond to a term");
            let tms = once(first_tm).chain(tms);

            tms.map(|tm| {
                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();
                CompileError::SurjectivityViolation { location }
            })
        })
}

pub fn iter_variable_introduced_in_then_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_term_should_be_epic_ok().filter_map(|tm| {
        // Only consider those terms that are variables:
        let name = eqlog.iter_var_term_node().find_map(|(var_tm, ident)| {
            if eqlog.are_equal_term_node(tm, var_tm) {
                Some(ident)
            } else {
                None
            }
        })?;

        let virt_name = eqlog.real_virt_ident(name).unwrap();
        if eqlog.var_before_term(tm, virt_name) {
            return None;
        }

        let loc = eqlog.term_node_loc(tm).unwrap();
        let location = *locations.get(&loc).unwrap();
        Some(CompileError::VariableIntroducedInThenStmt { location })
    })
}

pub fn iter_wildcard_in_then_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_term_should_be_epic_ok().filter_map(|tm| {
        if eqlog.wildcard_term_node(tm) {
            let loc = eqlog.term_node_loc(tm).unwrap();
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::WildcardInThenStmt { location })
        } else {
            None
        }
    })
}

pub fn iter_then_defined_variable_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_defined_then_atom_node()
        .filter_map(|(_, opt_var, _)| {
            let var_term = eqlog.iter_some_term_node().find_map(|(some_tm, tm)| {
                if eqlog.are_equal_opt_term_node(some_tm, opt_var) {
                    Some(tm)
                } else {
                    None
                }
            })?;

            if eqlog.wildcard_term_node(var_term) {
                return None;
            }

            let loc = eqlog.term_node_loc(var_term).unwrap();
            let location = *locations.get(&loc).unwrap();

            let var_name: Option<Ident> = eqlog.iter_var_term_node().find_map(|(vt, name)| {
                if eqlog.are_equal_term_node(vt, var_term) {
                    Some(name)
                } else {
                    None
                }
            });

            let var_name: Ident = match var_name {
                None => {
                    return Some(CompileError::ThenDefinedNotVar { location });
                }
                Some(name) => name,
            };

            if eqlog.var_before_term(var_term, eqlog.real_virt_ident(var_name).unwrap()) {
                return Some(CompileError::ThenDefinedVarNotNew { location });
            }

            None
        })
}
