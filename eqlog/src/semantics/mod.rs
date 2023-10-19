mod check_epic;
mod symbol_table;
mod type_inference;

use std::collections::btree_map;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use check_epic::*;
use convert_case::Case;
use convert_case::Casing;
pub use symbol_table::*;
use type_inference::*;

use crate::ast::*;
use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn iter_variable_not_snake_case_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<String, Ident>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_var_term_node().filter_map(|(tm, ident)| {
        let name: &str = identifiers
            .iter()
            .find_map(|(s, i)| {
                if eqlog.are_equal_ident(*i, ident) {
                    Some(s.as_str())
                } else {
                    None
                }
            })
            .unwrap();

        if name == &name.to_case(Case::Snake) {
            return None;
        }

        let loc = eqlog.term_node_loc(tm).unwrap();
        let location = *locations.get(&loc).unwrap();

        Some(CompileError::VariableNotSnakeCase {
            name: name.to_string(),
            location,
        })
    })
}

pub fn iter_variable_occurs_twice<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<String, Ident>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut var_tms: BTreeMap<(RuleDeclNode, Ident), BTreeSet<TermNode>> = BTreeMap::new();

    for (tm, ident, rule) in eqlog.iter_var_term_in_rule() {
        var_tms
            .entry((rule, ident))
            .or_insert(BTreeSet::new())
            .insert(tm);
    }

    var_tms.into_iter().filter_map(|((_, ident), var_tms)| {
        if var_tms.len() >= 2 {
            return None;
        }

        assert!(var_tms.len() == 1);
        let var_tm = var_tms.into_iter().next().unwrap();

        let name: &str = identifiers
            .iter()
            .find_map(|(s, i)| {
                if eqlog.are_equal_ident(*i, ident) {
                    Some(s.as_str())
                } else {
                    None
                }
            })
            .unwrap();

        let loc = eqlog.term_node_loc(var_tm).unwrap();
        let location = *locations.get(&loc).unwrap();

        Some(CompileError::VariableOccursOnlyOnce {
            name: name.to_string(),
            location,
        })
    })
}

pub fn iter_conflicting_type_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut el_type: BTreeMap<El, Type> = BTreeMap::new();
    eqlog
        .iter_el_type()
        .filter_map(move |(el, ty)| match el_type.entry(el) {
            btree_map::Entry::Vacant(vacant) => {
                vacant.insert(ty);
                None
            }
            btree_map::Entry::Occupied(occupied) => {
                if eqlog.are_equal_type(*occupied.get(), ty) {
                    None
                } else {
                    Some(el)
                }
            }
        })
        .flat_map(move |el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, e)| {
                if !eqlog.are_equal_el(e, el) {
                    return None;
                }

                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();

                Some(CompileError::ConflictingTermType {
                    types: Vec::new(),
                    location,
                })
            })
        })
}

pub fn iter_undetermined_type_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let all_els: BTreeSet<El> = eqlog.iter_el().collect();
    let els_with_type: BTreeSet<El> = eqlog.iter_el_type().map(|(el, _)| el).collect();

    all_els
        .into_iter()
        .filter(move |el| !els_with_type.contains(el))
        .flat_map(move |el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, e)| {
                if !eqlog.are_equal_el(e, el) {
                    return None;
                }

                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();
                return Some(CompileError::UndeterminedTermType { location });
            })
        })
}

pub fn iter_if_after_then_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_if_after_then().map(|if_stmt| {
        let loc = eqlog.stmt_node_loc(if_stmt).unwrap();
        let location = *locations.get(&loc).unwrap();
        CompileError::IfAfterThen { location }
    })
}

pub struct CheckedRule<'a> {
    pub decl: &'a RuleDecl,
}

pub fn check_rule<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<CheckedRule<'a>, CompileError> {
    infer_types(symbols, rule)?;
    Ok(CheckedRule { decl: rule })
}

pub fn check_eqlog(
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let first_error: Option<CompileError> = iter_then_defined_variable_errors(eqlog, locations)
        .chain(iter_variable_introduced_in_then_errors(eqlog, locations))
        .chain(iter_wildcard_in_then_errors(eqlog, locations))
        .chain(iter_conflicting_type_errors(eqlog, locations))
        .chain(iter_undetermined_type_errors(eqlog, locations))
        .chain(iter_surjectivity_errors(eqlog, locations))
        .chain(iter_if_after_then_errors(eqlog, locations))
        .chain(iter_variable_occurs_twice(eqlog, identifiers, locations))
        .chain(iter_variable_not_snake_case_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .min_by_key(|err| err.primary_location().1);

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(())
    }
}
