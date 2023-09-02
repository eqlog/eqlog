mod check_epic;
mod symbol_table;
mod type_inference;

use check_epic::*;
use convert_case::Case;
use convert_case::Casing;
pub use symbol_table::*;
use type_inference::*;

use crate::ast::*;
use crate::error::*;
use crate::unification::*;

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

pub fn check_rule<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<TermMap<&'a str>, CompileError> {
    check_then_defined_var(rule)?;
    check_epic(rule)?;
    let types = infer_types(symbols, rule)?;
    check_var_case(rule)?;
    Ok(types)
}
