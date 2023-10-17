use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn check_surjective<'a>(
    eqlog: &Eqlog,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let should_be_ok: BTreeSet<El> = eqlog.iter_el_should_be_surjective_ok().collect();
    let is_ok: BTreeSet<El> = eqlog.iter_el_is_surjective_ok().collect();
    let not_ok: Option<(TermNode, Location)> = should_be_ok
        .difference(&is_ok)
        .copied()
        .flat_map(|el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, tm_el)| {
                if eqlog.are_equal_el(tm_el, el) {
                    let loc = eqlog.term_node_loc(tm).unwrap();
                    let location = *locations.get(&loc).unwrap();
                    Some((tm, location))
                } else {
                    None
                }
            })
        })
        .min_by_key(|(_, location)| location.1);

    let (_, location): (TermNode, Location) = match not_ok {
        Some(not_ok) => not_ok,
        None => {
            return Ok(());
        }
    };

    Err(CompileError::SurjectivityViolation { location })
}

pub fn check_epic(eqlog: &Eqlog, locations: &BTreeMap<Loc, Location>) -> Result<(), CompileError> {
    let bad_variable_location: Option<Location> = eqlog
        .iter_term_should_be_epic_ok()
        .filter_map(|tm| {
            let name = eqlog.iter_var_term_node().find_map(|(var_tm, ident)| {
                if eqlog.are_equal_term_node(tm, var_tm) {
                    Some(ident)
                } else {
                    None
                }
            })?;
            let virt_name = eqlog.real_virt_ident(name).unwrap();
            if !eqlog.var_before_term(tm, virt_name) {
                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();
                Some(location)
            } else {
                None
            }
        })
        .min_by_key(|location| location.1);

    let bad_wildcard_location: Option<Location> = eqlog
        .iter_term_should_be_epic_ok()
        .filter_map(|tm| {
            if !eqlog.wildcard_term_node(tm) {
                return None;
            }

            let loc = eqlog.term_node_loc(tm).unwrap();
            let location = *locations.get(&loc).unwrap();
            Some(location)
        })
        .min_by_key(|location| location.1);

    match (bad_variable_location, bad_wildcard_location) {
        (None, None) => Ok(()),
        (Some(location), None) => Err(CompileError::VariableIntroducedInThenStmt { location }),
        (None, Some(location)) => Err(CompileError::WildcardInThenStmt { location: location }),
        (Some(bad_variable_location), Some(bad_wildcard_location)) => {
            if bad_variable_location.1 < bad_wildcard_location.1 {
                Err(CompileError::VariableIntroducedInThenStmt {
                    location: bad_variable_location,
                })
            } else {
                assert!(bad_variable_location.1 >= bad_wildcard_location.1);
                Err(CompileError::WildcardInThenStmt {
                    location: bad_wildcard_location,
                })
            }
        }
    }
}

pub fn check_then_defined_variable(
    eqlog: &Eqlog,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    // TODO: We should emit the error with the earliest source location. Currently it's some
    // arbitrary error.
    let error: Option<CompileError> =
        eqlog
            .iter_defined_then_atom_node()
            .find_map(|(_, opt_var, _)| {
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
            });

    match error {
        Some(error) => Err(error),
        None => Ok(()),
    }
}
