use std::iter::once;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Location(pub usize, pub usize);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sort {
    pub name: String,
    pub location: Option<Location>,
}

impl Sort {
    #[cfg(test)]
    pub fn new(name: String) -> Sort {
        Sort {
            name,
            location: None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Predicate {
    pub name: String,
    pub arity: Vec<String>,
    pub location: Option<Location>,
}

impl Predicate {
    #[cfg(test)]
    pub fn new(name: String, arity: Vec<String>) -> Predicate {
        Predicate {
            name,
            arity,
            location: None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Function {
    pub name: String,
    pub dom: Vec<String>,
    pub cod: String,
    pub location: Option<Location>,
}

impl Function {
    #[cfg(test)]
    pub fn new(name: String, dom: Vec<String>, cod: String) -> Function {
        Function {
            name,
            dom,
            cod,
            location: None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
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
    #[cfg(test)]
    pub fn without_locations(&self) -> TermUniverse {
        TermUniverse(self.0.iter().cloned().map(|(tm, _)| (tm, None)).collect())
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
    #[cfg(test)]
    pub fn without_locations(&self) -> Self {
        Atom {
            data: self.data.clone(),
            location: None,
        }
    }

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
pub struct Sequent {
    pub universe: TermUniverse,
    pub premise: Vec<Atom>,
    pub conclusion: Vec<Atom>,
}

impl Sequent {
    pub fn new_implication(
        universe: TermUniverse,
        premise: Vec<Atom>,
        conclusion: Vec<Atom>,
    ) -> Sequent {
        Sequent {
            universe,
            premise,
            conclusion,
        }
    }
    pub fn new_reduction(
        universe: TermUniverse,
        mut premise: Vec<Atom>,
        from: Term,
        to: Term,
    ) -> Sequent {
        use TermData::*;
        let from_args = match universe.data(from) {
            Application(_, args) => args,
            _ => panic!("Reduction with source Term::Variable or Term:Wildcard"),
        };

        premise.extend(from_args.iter().copied().chain(once(to)).map(|tm| Atom {
            data: AtomData::Defined(tm, None),
            location: None,
        }));
        let conclusion = vec![Atom {
            data: AtomData::Equal(from, to),
            location: None,
        }];
        Sequent {
            universe,
            premise,
            conclusion,
        }
    }
    #[cfg(test)]
    pub fn without_locations(&self) -> Self {
        Sequent {
            universe: self.universe.without_locations(),
            premise: self
                .premise
                .iter()
                .map(|atom| atom.without_locations())
                .collect(),
            conclusion: self
                .conclusion
                .iter()
                .map(|atom| atom.without_locations())
                .collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Axiom {
    pub sequent: Sequent,
    pub location: Option<Location>,
}
