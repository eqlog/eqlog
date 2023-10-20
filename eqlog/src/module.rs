use crate::ast::*;
use crate::error::*;
use crate::semantics::*;

#[derive(Clone, PartialEq, Eq)]
pub struct ModuleWrapper<'a> {
    pub symbols: SymbolTable<'a>,
}

impl<'a> ModuleWrapper<'a> {
    pub fn new(module: &'a Module) -> Result<Self, CompileError> {
        let symbols = SymbolTable::from_module(module);
        let module_wrapper = ModuleWrapper { symbols };
        Ok(module_wrapper)
    }
}
