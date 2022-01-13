use std::collections::{HashSet, HashMap};
use super::error::{SymbolType, SortCheckError, SortCheckResult};
use std::iter::once;

use SortCheckError::*;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    pub sorts: HashSet<String>,
    pub preds: HashMap<String, Vec<String>>,
    pub funcs: HashMap<String, (Vec<String>, String)>,
}

enum Symbol<'a> {
    Sort(&'a str),
    Pred(&'a str, &'a [String]),
    Func(&'a str, &'a [String], &'a str),
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            sorts: HashSet::new(),
            preds: HashMap::new(),
            funcs: HashMap::new(),
        }
    }

    fn lookup<'a, 'b>(&'a self, symbol: &'b str) -> Option<Symbol<'a>> {
        use Symbol::*;
        if let Some(sort) = self.sorts.get(symbol) {
            return Some(Sort(sort));
        }
        if let Some((pred, arity)) = self.preds.get_key_value(symbol) {
            return Some(Pred(pred, arity));
        }
        if let Some((func, (dom, cod))) = self.funcs.get_key_value(symbol) {
            return Some(Func(func, dom, cod));
        }

        None
    }

    pub fn lookup_sort<'a>(&'a self, symbol: &str) -> SortCheckResult<&'a str> {
        use Symbol::*;
        match self.lookup(symbol) {
            Some(Sort(s)) => Ok(s),
            Some(Pred(_, _)) => Err(WrongSymbolType { expected: SymbolType::Sort, got: SymbolType::Pred }),
            Some(Func(_, _, _)) => Err(WrongSymbolType { expected: SymbolType::Sort, got: SymbolType::Func }),
            None => Err(UndefinedSymbol),
        }
    }

    pub fn lookup_pred<'a>(&'a self, symbol: &str) -> SortCheckResult<(&'a str, &'a [String])> {
        use Symbol::*;
        match self.lookup(symbol) {
            Some(Sort(_)) => Err(WrongSymbolType { expected: SymbolType::Pred, got: SymbolType::Sort }),
            Some(Pred(pred, arity)) => Ok((pred, arity)),
            Some(Func(_, _, _)) => Err(WrongSymbolType { expected: SymbolType::Pred, got: SymbolType::Func }),
            None => Err(UndefinedSymbol),
        }
    }

    pub fn lookup_func<'a>(&'a self, symbol: &str) -> SortCheckResult<(&'a str, &'a [String], &'a str)> {
        use Symbol::*;
        match self.lookup(symbol) {
            Some(Sort(_)) => Err(WrongSymbolType { expected: SymbolType::Func, got: SymbolType::Sort }),
            Some(Pred(_, _)) => Err(WrongSymbolType { expected: SymbolType::Func, got: SymbolType::Pred }),
            Some(Func(func, dom, cod)) => Ok((func, dom, cod)),
            None => Err(UndefinedSymbol),
        }
    }

    pub fn insert_sort(&mut self, symbol: String) -> SortCheckResult<()> {
        if self.lookup(&symbol).is_some() { return Err(RedefinedSymbol); }
        self.sorts.insert(symbol);
        Ok(())
    }

    pub fn insert_pred(&mut self, symbol: String, arity: Vec<String>) -> SortCheckResult<()> {
        if self.lookup(&symbol).is_some() { return Err(RedefinedSymbol); }
        for sort in arity.iter() {
            self.lookup_sort(sort)?;
        }
        self.preds.insert(symbol, arity);
        Ok(())
    }

    pub fn insert_func(&mut self, symbol: String, dom: Vec<String>, cod: String) -> SortCheckResult<()> {
        if self.lookup(&symbol).is_some() { return Err(RedefinedSymbol); }
        for sort in dom.iter().chain(once(&cod)) {
            self.lookup_sort(sort)?;
        }
        self.funcs.insert(symbol, (dom, cod));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_signature() {
        let mut signature = Signature::new();
        signature.insert_sort("S".to_string()).unwrap();
        signature.insert_sort("T".to_string()).unwrap();
        signature.insert_pred(
            "P".to_string(),
            vec!["S".to_string(), "T".to_string()],
        ).unwrap();
        signature.insert_func(
            "F".to_string(),
            vec!["T".to_string()],
            "S".to_string(),
        ).unwrap();
    }

    #[test]
    fn duplicate_symbol() {
        let mut signature = Signature::new();
        signature.insert_sort("S".to_string()).unwrap();
        signature.insert_pred("P".to_string(), vec![]).unwrap();
        signature.insert_func("F".to_string(), vec![], "S".to_string()).unwrap();

        assert!(signature.insert_sort("S".to_string()).is_err());
        assert!(signature.insert_pred("S".to_string(), vec![]).is_err());
        assert!(signature.insert_func("S".to_string(), vec![], "S".to_string()).is_err());

        assert!(signature.insert_sort("P".to_string()).is_err());
        assert!(signature.insert_pred("P".to_string(), vec![]).is_err());
        assert!(signature.insert_func("P".to_string(), vec![], "S".to_string()).is_err());

        assert!(signature.insert_sort("F".to_string()).is_err());
        assert!(signature.insert_pred("F".to_string(), vec![]).is_err());
        assert!(signature.insert_func("F".to_string(), vec![], "S".to_string()).is_err());
    }

    #[test]
    fn invalid_arg() {
        let mut signature = Signature::new();
        signature.insert_sort("S".to_string()).unwrap();
        assert!(signature.insert_pred("P".to_string(), vec!["T".to_string()]).is_err());
        assert!(signature.insert_func("F".to_string(), vec!["T".to_string()], "S".to_string()).is_err());
        assert!(signature.insert_func("F".to_string(), vec![], "T".to_string()).is_err());
    }
}
