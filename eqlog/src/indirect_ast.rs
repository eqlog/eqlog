use crate::direct_ast;
pub use crate::direct_ast::{Function, Location, Predicate, Sort};

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
pub struct Formula {
    pub atoms: Vec<Atom>,
    pub location: Option<Location>,
}

impl Formula {
    #[cfg(test)]
    pub fn without_locations(&self) -> Self {
        Formula {
            atoms: self.atoms.iter().map(|a| a.without_locations()).collect(),
            location: None,
        }
    }

    pub fn iter_subterms<'a>(
        &'a self,
        universe: &'a TermUniverse,
    ) -> impl 'a + Iterator<Item = Term> {
        self.atoms
            .iter()
            .map(move |atom| atom.iter_subterms(universe))
            .flatten()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sequent {
    pub universe: TermUniverse,
    pub premise: Formula,
    pub conclusion: Formula,
}

fn translate_term(term: &direct_ast::Term, universe: &mut TermUniverse) -> Term {
    match &term.data {
        direct_ast::TermData::Variable(name) => {
            universe.new_term(TermData::Variable(name.clone()), term.location)
        }
        direct_ast::TermData::Wildcard => universe.new_term(TermData::Wildcard, term.location),
        direct_ast::TermData::Application(f, args) => {
            let translated_args = args
                .iter()
                .map(|arg| translate_term(arg, universe))
                .collect();
            universe.new_term(
                TermData::Application(f.clone(), translated_args),
                term.location,
            )
        }
    }
}

fn translate_atom(atom: &direct_ast::Atom, universe: &mut TermUniverse) -> Atom {
    let data = match &atom.data {
        direct_ast::AtomData::Equal(lhs, rhs) => {
            let translated_lhs = translate_term(lhs, universe);
            let translated_rhs = translate_term(rhs, universe);
            AtomData::Equal(translated_lhs, translated_rhs)
        }
        direct_ast::AtomData::Defined(tm, sort) => {
            let translated_tm = translate_term(tm, universe);
            AtomData::Defined(translated_tm, sort.clone())
        }
        direct_ast::AtomData::Predicate(pred, args) => {
            let translated_args = args
                .iter()
                .map(|arg| translate_term(arg, universe))
                .collect();
            AtomData::Predicate(pred.clone(), translated_args)
        }
    };
    Atom {
        data,
        location: atom.location,
    }
}

fn translate_formula(universe: &mut TermUniverse, formula: &direct_ast::Formula) -> Formula {
    let atoms = formula
        .atoms
        .iter()
        .map(|atom| translate_atom(atom, universe))
        .collect();
    Formula {
        atoms,
        location: formula.location,
    }
}

impl Sequent {
    pub fn new(sequent: &direct_ast::Sequent) -> Sequent {
        let mut universe = TermUniverse::new();

        use direct_ast::Sequent::*;
        match sequent {
            Implication(premise, conclusion) => Sequent {
                premise: translate_formula(&mut universe, premise),
                conclusion: translate_formula(&mut universe, conclusion),
                universe,
            },
            Reduction { premise, from, to } => {
                // Translate premise atoms.
                let mut premise: Formula = match premise {
                    Some(premise) => translate_formula(&mut universe, premise),
                    None => Formula {
                        atoms: Vec::new(),
                        location: None,
                    },
                };

                let (from_func, from_args) = match &from.data {
                    direct_ast::TermData::Application(func, args) => (func, args),
                    _ => panic!("Reduction from variable or wildcard term"),
                };

                // Add `from_arg[0]! & from_arg[1]! & ...`  to premise.
                let from_args: Vec<Term> = from_args
                    .iter()
                    .map(|arg| {
                        let arg = translate_term(arg, &mut universe);
                        let data = AtomData::Defined(arg, None);
                        premise.atoms.push(Atom {
                            data,
                            location: None,
                        });
                        arg
                    })
                    .collect();

                // Add `to!` to premise.
                let to = translate_term(to, &mut universe);
                let data = AtomData::Defined(to, None);
                premise.atoms.push(Atom {
                    data,
                    location: None,
                });

                // Build conclusion: `from = to`. Only `from` is not defined yet.
                let from_data = TermData::Application(from_func.clone(), from_args);
                let from = universe.new_term(from_data, from.location);
                let eq = Atom {
                    data: AtomData::Equal(from, to),
                    location: None,
                };
                let conclusion = Formula {
                    atoms: vec![eq],
                    location: None,
                };

                Sequent {
                    premise,
                    conclusion,
                    universe,
                }
            }
        }
    }
}
