mod symbol_table;
mod type_inference;

pub use symbol_table::*;
use type_inference::*;

use crate::ast::*;
use crate::error::*;
use crate::unification::*;

pub fn check_rule<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<TermMap<&'a str>, CompileError> {
    let types = infer_types(symbols, rule)?;
    Ok(types)
}
