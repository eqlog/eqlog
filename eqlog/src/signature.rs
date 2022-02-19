use std::collections::HashMap;
use crate::direct_ast::*;
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
    pub fn sorts(&self) -> &HashMap<String, Sort> { &self.sorts }
    pub fn predicates(&self) -> &HashMap<String, Predicate> { &self.predicates }
    pub fn functions(&self) -> &HashMap<String, Function> { &self.functions }

    pub fn add_sort(&mut self, sort: Sort) {
        match self.sorts.insert(sort.0.clone(), sort) {
            None => (),
            Some(prev_sort) => panic!("Duplicate declaration of sort {}", prev_sort.0)
        }
    }
    pub fn add_predicate(&mut self, pred: Predicate) {
        for s in pred.arity.iter() {
            if !self.sorts.contains_key(s) {
                panic!("Undeclared sort {}", s)
            }
        }
        match self.predicates.insert(pred.name.clone(), pred) {
            None => (),
            Some(prev_pred) => {
                panic!("Duplicate declaration of predicate {}", prev_pred.name)
            }
        }
    }
    pub fn add_function(&mut self, func: Function) {
        for s in func.dom.iter().chain(once(&func.cod)) {
            if !self.sorts.contains_key(s) {
                panic!("Undeclared sort {}", s)
            }
        }
        match self.functions.insert(func.name.clone(), func) {
            None => (),
            Some(prev_func) => {
                panic!("Duplicate declaration of function {}", prev_func.name)
            }
        }
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
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));

        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![s(), t()]});
        th.add_predicate(Predicate{name: "P".to_string(), arity: vec![s(), s(), s()]});

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t()], cod: t()});
        th.add_function(Function{name: "G".to_string(), dom: vec![t(), s()], cod: t()});
    }

    #[test] #[should_panic]
    fn test_duplicate_sort() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));
        th.add_sort(Sort(s()));
    }

    #[test] #[should_panic]
    fn test_duplicate_predicate() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));

        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![s(), t()]});
        th.add_predicate(Predicate{name: "P".to_string(), arity: vec![s(), s(), s()]});
        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![t(), s()]});
    }

    #[test] #[should_panic]
    fn test_duplicate_function() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t()], cod: t()});
        th.add_function(Function{name: "G".to_string(), dom: vec![t(), s()], cod: t()});
        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t()], cod: t()});
    }

    #[test] #[should_panic]
    fn test_predicate_bad_arity() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));

        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![s(), t()]});
    }

    #[test] #[should_panic]
    fn test_function_bad_dom() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), s()], cod: t()});
    }

    #[test] #[should_panic]
    fn test_function_bad_cod() {
        let mut th = Signature::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t(), s()], cod: s()});
    }
}
