use crate::ast::*;
use crate::error::*;
use std::collections::HashMap;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    sorts: HashMap<String, Sort>,
    predicates: HashMap<String, Predicate>,
    functions: HashMap<String, Function>,
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            sorts: HashMap::new(),
            predicates: HashMap::new(),
            functions: HashMap::new(),
        }
    }
    pub fn sorts(&self) -> &HashMap<String, Sort> {
        &self.sorts
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

    pub fn add_sort(&mut self, sort: Sort) -> Result<(), CompileError> {
        let sort_location = sort.location;
        if let Some(prev_sort) = self.sorts.insert(sort.name.clone(), sort) {
            return Err(CompileError::SymbolDeclaredTwice {
                name: prev_sort.name.clone(),
                first_declaration: prev_sort.location,
                second_declaration: sort_location,
            });
        }
        Ok(())
    }
    pub fn add_predicate(&mut self, pred: Predicate) -> Result<(), CompileError> {
        for s in pred.arity.iter() {
            if !self.sorts.contains_key(s) {
                return Err(CompileError::UndeclaredSymbol {
                    name: s.clone(),
                    location: pred.location,
                });
            }
        }
        let pred_location = pred.location;
        if let Some(prev_pred) = self.predicates.insert(pred.name.clone(), pred) {
            return Err(CompileError::SymbolDeclaredTwice {
                name: prev_pred.name.clone(),
                first_declaration: prev_pred.location,
                second_declaration: pred_location,
            });
        }
        Ok(())
    }
    pub fn add_function(&mut self, func: Function) -> Result<(), CompileError> {
        for s in func.dom.iter().chain(once(&func.cod)) {
            if !self.sorts.contains_key(s) {
                return Err(CompileError::UndeclaredSymbol {
                    name: s.clone(),
                    location: func.location,
                });
            }
        }
        let func_location = func.location;
        if let Some(prev_func) = self.functions.insert(func.name.clone(), func) {
            return Err(CompileError::SymbolDeclaredTwice {
                name: prev_func.name.clone(),
                first_declaration: prev_func.location,
                second_declaration: func_location,
            });
        }
        Ok(())
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
        th.add_function(Function::new("G".to_string(), vec![t(), s()], t()));
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
