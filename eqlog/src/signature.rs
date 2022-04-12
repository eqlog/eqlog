use crate::ast::*;
use crate::error::*;
use std::collections::HashMap;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Symbol {
    Sort(Sort),
    Predicate(Predicate),
    Function(Function),
}

impl Symbol {
    fn name(&self) -> &str {
        use Symbol::*;
        match self {
            Sort(s) => &s.name,
            Predicate(p) => &p.name,
            Function(f) => &f.name,
        }
    }
    fn location(&self) -> Option<Location> {
        match self {
            Symbol::Sort(Sort { location, .. }) => *location,
            Symbol::Predicate(Predicate { location, .. }) => *location,
            Symbol::Function(Function { location, .. }) => *location,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    symbols: HashMap<String, Symbol>,
    predicates: HashMap<String, Predicate>,
    functions: HashMap<String, Function>,
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            symbols: HashMap::new(),
            predicates: HashMap::new(),
            functions: HashMap::new(),
        }
    }
    pub fn iter_sorts(&self) -> impl Iterator<Item = &Sort> {
        self.symbols.values().filter_map(|symbol| match symbol {
            Symbol::Sort(s) => Some(s),
            _ => None,
        })
    }
    pub fn predicates(&self) -> &HashMap<String, Predicate> {
        &self.predicates
    }
    pub fn functions(&self) -> &HashMap<String, Function> {
        &self.functions
    }
    pub fn relations(&self) -> impl Iterator<Item = (&str, Vec<&str>)> {
        let pred_rels = self.predicates().values().map(|pred| {
            let name = pred.name.as_str();
            let arity: Vec<&str> = pred.arity.iter().map(|s| s.as_str()).collect();
            (name, arity)
        });
        let func_rels = self.functions().values().map(|func| {
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
        if let Some(Predicate { arity, .. }) = self.predicates.get(relation) {
            return Some(arity.iter().map(|s| s.as_str()).collect());
        }
        if let Some(Function { dom, cod, .. }) = self.functions.get(relation) {
            return Some(dom.iter().chain(once(cod)).map(|s| s.as_str()).collect());
        }
        None
    }

    fn insert_symbol(&mut self, symbol: Symbol) -> Result<(), CompileError> {
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
    fn get_symbol(&mut self, name: &str) -> Option<&Symbol> {
        self.symbols.get(name)
    }

    pub fn add_sort(&mut self, sort: Sort) -> Result<(), CompileError> {
        self.insert_symbol(Symbol::Sort(sort))
    }
    pub fn add_predicate(&mut self, pred: Predicate) -> Result<(), CompileError> {
        self.predicates.insert(pred.name.clone(), pred.clone());
        for s in pred.arity.iter() {
            match self.get_symbol(s) {
                None => {
                    return Err(CompileError::UndeclaredSymbol {
                        name: s.clone(),
                        location: pred.location,
                    });
                }
                Some(Symbol::Sort { .. }) => (),
                Some(_) => panic!("Is not sort"),
            }
        }
        self.insert_symbol(Symbol::Predicate(pred))
    }
    pub fn add_function(&mut self, func: Function) -> Result<(), CompileError> {
        self.functions.insert(func.name.clone(), func.clone());
        for s in func.dom.iter().chain(once(&func.cod)) {
            match self.get_symbol(s) {
                None => {
                    return Err(CompileError::UndeclaredSymbol {
                        name: s.clone(),
                        location: func.location,
                    });
                }
                Some(Symbol::Sort { .. }) => (),
                Some(_) => panic!("Is not sort"),
            }
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
