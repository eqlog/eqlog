mod check_epic;
mod symbol_table;
mod type_inference;

use std::collections::BTreeMap;

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

/// Checks that the `var` term in all [ThenAtomData::Defined] that occur in a rule are actually
/// variables.
pub fn check_then_defined_var<'a>(rule: &'a RuleDecl) -> Result<(), CompileError> {
    let context = &rule.term_context;
    for stmt in rule.body.iter() {
        match &stmt.data {
            StmtData::If(_) => {}
            StmtData::Then(atom) => {
                if let ThenAtomData::Defined { var, term: _ } = &atom.data {
                    if let Some(var) = var {
                        match context.data(*var) {
                            TermData::Variable(_) | TermData::Wildcard => {}
                            TermData::Application { .. } => {
                                let location = context.loc(*var);
                                return Err(CompileError::ThenDefinedNotVar { location });
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

pub fn check_var_case(rule: &RuleDecl) -> Result<(), CompileError> {
    let context = &rule.term_context;
    for tm in context.iter_terms() {
        match context.data(tm) {
            TermData::Variable(name) => {
                if name != &name.to_case(Case::Snake) {
                    return Err(CompileError::VariableNotSnakeCase {
                        name: name.into(),
                        location: context.loc(tm),
                    });
                }
            }
            TermData::Wildcard | TermData::Application { .. } => {}
        }
    }

    Ok(())
}

pub fn check_vars_occur_twice<'a>(rule: &'a RuleDecl) -> Result<(), CompileError> {
    let context = &rule.term_context;
    let mut occ_nums: BTreeMap<&str, (usize, Location)> = BTreeMap::new();
    for tm in context.iter_terms() {
        if let TermData::Variable(v) = context.data(tm) {
            let loc = context.loc(tm);
            let (count, _): &mut (usize, Location) = occ_nums.entry(v.as_str()).or_insert((0, loc));
            *count += 1;
        }
    }
    for (name, (n, loc)) in occ_nums.into_iter() {
        if n == 1 {
            return Err(CompileError::VariableOccursOnlyOnce {
                name: name.into(),
                location: loc,
            });
        }
    }
    Ok(())
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
    check_then_defined_var(rule)?;
    let types = infer_types(symbols, rule)?;
    check_var_case(rule)?;
    check_vars_occur_twice(rule)?;
    check_if_after_then(rule)?;
    Ok(CheckedRule { types, decl: rule })
}

pub fn check_eqlog(
    eqlog: &Eqlog,
    _identifiers: &BTreeMap<String, Ident>,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    check_epic(eqlog, locations)?;
    check_then_defined_variable(eqlog, locations)?;

    let first_error: Option<CompileError> =
        iter_surjectivity_errors(eqlog, locations).min_by_key(|err| err.primary_location().1);

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(())
    }
}
