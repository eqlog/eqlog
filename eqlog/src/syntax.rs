use crate::signature::*;

use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(String),
    Operation(RelationId, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Atom {
    Equal(Term, Term),
    Defined(Term),
    Predicate(RelationId, Vec<Term>),
}

pub struct Formula(Vec<Atom>);

pub enum Sequent {
    Implication(Formula, Formula),
    Reduction(Term, Term),
}

pub struct Theory {
    pub signature: Signature,
    pub sort_names: HashMap<String, SortId>,
    pub predicate_names: HashMap<String, RelationId>,
    pub operation_names: HashMap<String, RelationId>,
    pub sequents: Vec<Sequent>,
}

impl Theory {
    pub fn add_sort(&mut self, name: String) -> SortId {
        let s = SortId(self.signature.sort_number);
        let v = self.sort_names.insert(name, s);
        assert!(v.is_none()); // assert that name was not already in sort_names
        self.signature.sort_number += 1;
        s
    }
    pub fn add_predicate(&mut self, name: String, arity: Vec<SortId>) -> RelationId {
        assert!(
            !self.predicate_names.contains_key(&name) &&
            !self.operation_names.contains_key(&name)
        );
        assert!(arity.iter().all(|SortId(s)| *s < self.signature.sort_number));
        let r = RelationId(self.signature.relation_arities.len());
        self.predicate_names.insert(name, r);
        self.signature.relation_arities.push(arity);
        r
    }
    pub fn add_operation(&mut self, name: String, domain: Vec<SortId>, codomain: SortId) -> RelationId {
        let mut arity = domain;
        arity.push(codomain);
        assert!(arity.iter().all(|SortId(s)| *s < self.signature.sort_number));
        assert!(
            !self.predicate_names.contains_key(&name) &&
            !self.operation_names.contains_key(&name)
        );
        let r = RelationId(self.signature.relation_arities.len());
        self.operation_names.insert(name, r);
        self.signature.relation_arities.push(arity);
        r
    }
}
