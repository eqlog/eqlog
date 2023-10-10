use crate::ast::TermContext;
pub use crate::ast::{Term, TermData};
use crate::source_display::Location;
use itertools::Itertools;
use std::fmt::{self, Debug};

pub type TermUniverse = TermContext;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sort {
    pub name: String,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Predicate {
    pub name: String,
    pub arity: Vec<String>,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Function {
    pub name: String,
    pub dom: Vec<String>,
    pub cod: String,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AtomData {
    Equal(Term, Term),
    Defined(Term, Option<String>),
    Predicate(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Atom {
    pub data: AtomData,
    pub location: Option<Location>,
}

impl Atom {
    pub fn iter_subterms<'a>(
        &'a self,
        universe: &'a TermUniverse,
    ) -> impl 'a + Iterator<Item = Term> {
        use AtomData::*;
        let top_tms = match &self.data {
            Equal(lhs, rhs) => vec![*lhs, *rhs],
            Defined(tm, _) => vec![*tm],
            Predicate(_, args) => args.clone(),
        };
        top_tms
            .into_iter()
            .map(move |tm| universe.iter_subterms(tm))
            .flatten()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SequentData {
    Implication {
        premise: Vec<Atom>,
        conclusion: Vec<Atom>,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Sequent {
    pub universe: TermUniverse,
    pub data: SequentData,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Axiom {
    pub sequent: Sequent,
    pub location: Option<Location>,
}
