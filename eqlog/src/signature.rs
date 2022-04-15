use crate::ast::*;
use crate::error::*;
use convert_case::{Case, Casing};
use std::collections::HashMap;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    symbols: HashMap<String, Symbol>,
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            symbols: HashMap::new(),
        }
    }

    pub fn get_symbol_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Symbol, CompileError> {
        self.symbols
            .get(name)
            .ok_or_else(|| CompileError::UndeclaredSymbol {
                name: name.into(),
                location,
            })
    }
    fn bad_symbol_kind(
        symbol: &Symbol,
        expected: SymbolKind,
        used_location: Option<Location>,
    ) -> CompileError {
        CompileError::BadSymbolKind {
            name: symbol.name().into(),
            expected,
            found: symbol.kind(),
            used_location: used_location,
            declared_location: symbol.location(),
        }
    }
    pub fn get_sort_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Sort, CompileError> {
        let symbol = self.get_symbol_at(name, location)?;
        if let Symbol::Sort(s) = symbol {
            Ok(s)
        } else {
            Err(Self::bad_symbol_kind(symbol, SymbolKind::Sort, location))
        }
    }
    pub fn get_predicate_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Predicate, CompileError> {
        let symbol = self.get_symbol_at(name, location)?;
        if let Symbol::Predicate(p) = symbol {
            Ok(p)
        } else {
            Err(Self::bad_symbol_kind(
                symbol,
                SymbolKind::Predicate,
                location,
            ))
        }
    }
    pub fn get_function_at(
        &self,
        name: &str,
        location: Option<Location>,
    ) -> Result<&Function, CompileError> {
        let symbol = self.get_symbol_at(name, location)?;
        if let Symbol::Function(f) = symbol {
            Ok(f)
        } else {
            Err(Self::bad_symbol_kind(
                symbol,
                SymbolKind::Function,
                location,
            ))
        }
    }

    pub fn iter_sorts(&self) -> impl Iterator<Item = &Sort> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Sort(s) => Some(s),
            _ => None,
        })
    }
    pub fn iter_predicates(&self) -> impl Iterator<Item = &Predicate> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Predicate(p) => Some(p),
            _ => None,
        })
    }
    pub fn iter_functions(&self) -> impl Iterator<Item = &Function> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Function(f) => Some(f),
            _ => None,
        })
    }

    pub fn relations(&self) -> impl Iterator<Item = (&str, Vec<&str>)> {
        let pred_rels = self.iter_predicates().map(|pred| {
            let name = pred.name.as_str();
            let arity: Vec<&str> = pred.arity.iter().map(|s| s.as_str()).collect();
            (name, arity)
        });
        let func_rels = self.iter_functions().map(|func| {
            let name = func.name.as_str();
            let arity: Vec<&str> = func
                .dom
                .iter()
                .chain(once(&func.cod))
                .map(|s| s.as_str())
                .collect();
            (name, arity)
        });
        pred_rels.chain(func_rels)
    }

    pub fn arity(&self, relation: &str) -> Option<Vec<&str>> {
        match self.symbols.get(relation)? {
            Symbol::Sort(_) => None,
            Symbol::Predicate(Predicate { arity, .. }) => {
                Some(arity.iter().map(|s| s.as_str()).collect())
            }
            Symbol::Function(Function { dom, cod, .. }) => {
                Some(dom.iter().chain(once(cod)).map(|s| s.as_str()).collect())
            }
        }
    }

    fn insert_symbol(&mut self, symbol: Symbol) -> Result<(), CompileError> {
        if symbol.name().to_case(Case::UpperCamel) != *symbol.name() {
            return Err(CompileError::SymbolNotCamelCase {
                name: symbol.name().into(),
                location: symbol.location(),
            });
        }

        let second_location = symbol.location();
        if let Some(prev_symbol) = self.symbols.insert(symbol.name().into(), symbol) {
            return Err(CompileError::SymbolDeclaredTwice {
                name: prev_symbol.name().into(),
                first_declaration: prev_symbol.location(),
                second_declaration: second_location,
            });
        }

        Ok(())
    }

    pub fn add_sort(&mut self, sort: Sort) -> Result<(), CompileError> {
        self.insert_symbol(Symbol::Sort(sort))
    }
    pub fn add_predicate(&mut self, pred: Predicate) -> Result<(), CompileError> {
        for s in pred.arity.iter() {
            self.get_sort_at(s, pred.location)?;
        }
        self.insert_symbol(Symbol::Predicate(pred))
    }
    pub fn add_function(&mut self, func: Function) -> Result<(), CompileError> {
        for s in func.dom.iter().chain(once(&func.cod)) {
            self.get_sort_at(s, func.location)?;
        }
        self.insert_symbol(Symbol::Function(func))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sorts_predicates_functions() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();
        th.add_sort(Sort::new(t())).unwrap();

        th.add_predicate(Predicate::new("Q".to_string(), vec![s(), t()]))
            .unwrap();
        th.add_predicate(Predicate::new("P".to_string(), vec![s(), s(), s()]))
            .unwrap();

        th.add_function(Function::new("F".to_string(), vec![s(), t()], t()))
            .unwrap();
        th.add_function(Function::new("G".to_string(), vec![t(), s()], t()))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_duplicate_sort() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();
        th.add_sort(Sort::new(t())).unwrap();
        th.add_sort(Sort::new(s())).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_duplicate_predicate() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();
        th.add_sort(Sort::new(t())).unwrap();

        th.add_predicate(Predicate::new("Q".to_string(), vec![s(), t()]))
            .unwrap();
        th.add_predicate(Predicate::new("P".to_string(), vec![s(), s(), s()]))
            .unwrap();
        th.add_predicate(Predicate::new("Q".to_string(), vec![t(), s()]))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_duplicate_function() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();
        th.add_sort(Sort::new(t())).unwrap();

        th.add_function(Function::new("F".to_string(), vec![s(), t()], t()))
            .unwrap();
        th.add_function(Function::new("G".to_string(), vec![t(), s()], t()))
            .unwrap();
        th.add_function(Function::new("F".to_string(), vec![s(), t()], t()))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_predicate_bad_arity() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();

        th.add_predicate(Predicate::new("Q".to_string(), vec![s(), t()]))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_function_bad_dom() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();

        th.add_function(Function::new("F".to_string(), vec![s(), s()], t()))
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_function_bad_cod() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort::new(s())).unwrap();

        th.add_function(Function::new("F".to_string(), vec![s(), t(), s()], s()))
            .unwrap();
    }
}
