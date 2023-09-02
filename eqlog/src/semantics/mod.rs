mod check_epic;
mod symbol_table;
mod type_inference;

use check_epic::*;
pub use symbol_table::*;
use type_inference::*;

use crate::ast::*;
use crate::error::*;
use crate::unification::*;

pub fn check_rule<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<TermMap<&'a str>, CompileError> {
    check_epic(rule)?;
    let types = infer_types(symbols, rule)?;
    Ok(types)
}
