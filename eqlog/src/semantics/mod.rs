mod check_epic;
mod symbol_table;
mod type_inference;

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
use crate::unification::*;
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

pub fn check_if_after_then<'a>(rule: &'a RuleDecl) -> Result<(), CompileError> {
    let mut then_atom_occurred = false;
    for stmt in rule.body.iter() {
        match &stmt.data {
            StmtData::If(_) => {
                if then_atom_occurred {
                    return Err(CompileError::IfAfterThen { location: stmt.loc });
                }
            }
            StmtData::Then(_) => {
                then_atom_occurred = true;
            }
        }
    }

    Ok(())
}

pub struct CheckedRule<'a> {
    pub decl: &'a RuleDecl,
    pub types: TermMap<&'a str>,
}

pub fn check_rule<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<CheckedRule<'a>, CompileError> {
    let types = infer_types(symbols, rule)?;
    check_if_after_then(rule)?;
    Ok(CheckedRule { types, decl: rule })
}

pub fn check_eqlog(
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let first_error: Option<CompileError> = iter_then_defined_variable_errors(eqlog, locations)
        .chain(iter_variable_introduced_in_then_errors(eqlog, locations))
        .chain(iter_wildcard_in_then_errors(eqlog, locations))
        .chain(iter_surjectivity_errors(eqlog, locations))
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
