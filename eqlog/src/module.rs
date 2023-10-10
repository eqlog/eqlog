use crate::ast::*;
use crate::error::*;
use crate::semantics::*;

#[derive(Clone, PartialEq, Eq)]
pub struct ModuleWrapper<'a> {
    pub symbols: SymbolTable<'a>,
}

impl<'a> ModuleWrapper<'a> {
    pub fn new(module: &'a Module) -> Result<Self, CompileError> {
        let symbols = SymbolTable::from_module(module)?;
        let mut module_wrapper = ModuleWrapper { symbols };
        for decl in module.0.iter() {
            if let Decl::Rule(rule) = decl {
                module_wrapper.add_rule(rule.clone())?;
            }
        }
        Ok(module_wrapper)
    }
}

impl<'a> ModuleWrapper<'a> {
    fn add_rule(&mut self, rule: RuleDecl) -> Result<(), CompileError> {
        check_rule(&self.symbols, &rule)?;
        Ok(())
    }
}
