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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Axiom {
    pub sequent: Sequent,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct QueryArgument {
    pub variable: Term,
    pub sort: Option<String>,
    pub location: Option<Location>,
}

// Debug printing of AST. Each AST node type N that is relative to a TermUniverse gets a struct
// NDebug that bundles the node with the TermUniverse it belongs to, and this struct implements
// Debug such that it will recursively print the whole tree structure of the node .

#[derive(Copy, Clone)]
struct TermDebug<'a> {
    term: Term,
    universe: &'a TermUniverse,
}

impl<'a> Debug for TermDebug<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let TermDebug { term, universe } = *self;
        use TermData::*;
        match universe.data(term) {
            Variable(name) => f.write_str(name),
            Wildcard => write!(f, "_{}", term.0),
            Application { func, args } => {
                let args_displ = args.iter().copied().format_with(", ", |arg, f| {
                    f(&format_args!(
                        "{:?}",
                        TermDebug {
                            term: arg,
                            universe
                        }
                    ))
                });
                write!(f, "{func}({args_displ})")
            }
        }
    }
}

impl Term {
    #[allow(dead_code)]
    pub fn debug<'a>(self, universe: &'a TermUniverse) -> impl 'a + Debug + Copy + Clone {
        TermDebug {
            term: self,
            universe,
        }
    }
}

#[derive(Clone)]
pub struct AtomDebug<'a> {
    atom: &'a Atom,
    universe: &'a TermUniverse,
}

impl<'a> Debug for AtomDebug<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let AtomDebug { atom, universe } = self;
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                let lhs = lhs.debug(universe);
                let rhs = rhs.debug(universe);
                write!(f, "{lhs:?} = {rhs:?}")?;
            }
            Defined(tm, sort) => {
                let tm = tm.debug(universe);
                match sort {
                    Some(sort) => write!(f, "{tm:?}: {sort}")?,
                    None => write!(f, "{tm:?}!")?,
                }
            }
            Predicate(pred, args) => {
                let args_displ = args.iter().copied().format_with(", ", |arg, f| {
                    f(&format_args!(
                        "{:?}",
                        TermDebug {
                            term: arg,
                            universe
                        }
                    ))
                });
                write!(f, "{pred}({args_displ})")?;
            }
        }
        Ok(())
    }
}

impl Atom {
    #[allow(dead_code)]
    pub fn debug<'a>(&'a self, universe: &'a mut TermUniverse) -> AtomDebug<'a> {
        AtomDebug {
            atom: self,
            universe,
        }
    }
}

pub struct FormulaDebug<'a> {
    atoms: &'a [Atom],
    universe: &'a TermUniverse,
}

impl<'a> Debug for FormulaDebug<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let FormulaDebug { atoms, universe } = self;
        let atoms = atoms.into_iter().format_with(" & ", |atom, f| {
            f(&format_args!("{:?}", AtomDebug { atom, universe }))
        });
        write!(f, "{atoms}")?;
        Ok(())
    }
}

pub fn formula_debug<'a>(atoms: &'a [Atom], universe: &'a TermUniverse) -> FormulaDebug<'a> {
    FormulaDebug { atoms, universe }
}

impl Debug for Sequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Sequent { universe, data } = self;
        use SequentData::*;
        match data {
            Implication {
                premise,
                conclusion,
            } => {
                let premise = formula_debug(premise.as_slice(), universe);
                let conclusion = formula_debug(conclusion.as_slice(), universe);
                write!(f, "{premise:?} => {conclusion:?}")?;
            }
        }
        Ok(())
    }
}
