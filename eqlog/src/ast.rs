use crate::source_display::Location;
use itertools::Itertools;
use std::fmt::{self, Display};
use std::slice::from_ref;

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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Term(pub usize);
impl From<usize> for Term {
    fn from(n: usize) -> Term {
        Term(n)
    }
}
impl Into<usize> for Term {
    fn into(self) -> usize {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermData {
    Variable(String),
    Wildcard,
    Application(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TermUniverse(Vec<(TermData, Option<Location>)>);

impl TermUniverse {
    pub fn new() -> TermUniverse {
        TermUniverse(Vec::new())
    }
    pub fn new_term(&mut self, data: TermData, location: Option<Location>) -> Term {
        let tm = Term(self.0.len());
        self.0.push((data, location));
        tm
    }
    pub fn data(&self, tm: Term) -> &TermData {
        &self.0[tm.0].0
    }
    pub fn location(&self, tm: Term) -> Option<Location> {
        self.0[tm.0].1
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter_terms(&self) -> impl Iterator<Item = Term> {
        (0..self.0.len()).map(Term)
    }
}

struct SubtermIterator<'a> {
    universe: &'a TermUniverse,
    stack: Vec<(Term, usize)>,
}

impl<'a> Iterator for SubtermIterator<'a> {
    type Item = Term;

    fn next(&mut self) -> Option<Self::Item> {
        let (tm, next_child) = match self.stack.pop() {
            Some(top) => top,
            None => return None,
        };

        use TermData::*;
        let mut child = match self.universe.data(tm) {
            Variable(_) | Wildcard => return Some(tm),
            Application(_, args) if args.len() == next_child => return Some(tm),
            Application(_, args) => {
                debug_assert!(next_child < args.len());
                args[next_child]
            }
        };

        self.stack.push((tm, next_child + 1));
        while let Application(_, args) = self.universe.data(child) {
            match args.first() {
                None => break,
                Some(arg) => {
                    self.stack.push((child, 1));
                    child = *arg;
                }
            }
        }
        Some(child)
    }
}

impl TermUniverse {
    pub fn iter_subterms(&self, tm: Term) -> impl '_ + Iterator<Item = Term> {
        SubtermIterator {
            universe: self,
            stack: vec![(tm, 0)],
        }
    }
}

#[derive(Copy, Clone)]
struct TermDisplay<'a> {
    term: Term,
    universe: &'a TermUniverse,
}

impl<'a> Display for TermDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let TermDisplay { term, universe } = *self;
        use TermData::*;
        match universe.data(term) {
            Variable(name) => f.write_str(name),
            Wildcard => write!(f, "_{}", term.0),
            Application(func, args) => {
                let args_displ = args.iter().copied().format_with(", ", |arg, f| {
                    f(&format_args!(
                        "{}",
                        TermDisplay {
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
    pub fn display<'a>(self, universe: &'a TermUniverse) -> impl 'a + Display + Copy + Clone {
        TermDisplay {
            term: self,
            universe,
        }
    }
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
    Reduction {
        premise: Vec<Atom>,
        from: Term,
        to: Term,
    },
    Bireduction {
        premise: Vec<Atom>,
        lhs: Term,
        rhs: Term,
    },
}

impl SequentData {
    pub fn iter_atoms<'a>(&'a self) -> impl 'a + Iterator<Item = &'a Atom> {
        use SequentData::*;
        let result: Box<dyn 'a + Iterator<Item = &'a Atom>> = match self {
            Implication {
                premise,
                conclusion,
            } => Box::new(premise.iter().chain(conclusion)),
            Reduction { premise, .. } => Box::new(premise.iter()),
            Bireduction { premise, .. } => Box::new(premise.iter()),
        };
        result
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum QueryResult {
    NoResult,
    SingleResult(Term),
    TupleResult(Vec<Term>),
}

impl QueryResult {
    pub fn iter_result_terms(&self) -> impl Iterator<Item = Term> + '_ {
        use QueryResult::*;
        let slice: &[Term] = match self {
            NoResult => &[],
            SingleResult(tm) => from_ref(tm),
            TupleResult(tms) => tms.as_slice(),
        };
        slice.iter().copied()
    }
    pub fn iter_subterms<'a>(
        &'a self,
        universe: &'a TermUniverse,
    ) -> impl Iterator<Item = Term> + 'a {
        self.iter_result_terms()
            .map(move |tm| universe.iter_subterms(tm))
            .flatten()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct UserQuery {
    pub universe: TermUniverse,
    pub name: String,
    pub arguments: Vec<QueryArgument>,
    pub result: QueryResult,
    pub where_formula: Option<Vec<Atom>>,
    pub location: Option<Location>,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum SymbolKind {
    Sort,
    Predicate,
    Function,
    Query,
}

impl Display for SymbolKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SymbolKind::*;
        f.write_str(match self {
            Sort => "sort",
            Predicate => "predicate",
            Function => "function",
            Query => "query",
        })
    }
}
