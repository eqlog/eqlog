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
    pub fn iter_terms(&self) -> impl Iterator<Item = (Term, &TermData)> {
        self.0
            .iter()
            .enumerate()
            .map(|(i, (data, _))| (Term(i), data))
    }
    #[cfg(test)]
    pub fn without_locations(&self) -> TermUniverse {
        TermUniverse(self.0.iter().cloned().map(|(tm, _)| (tm, None)).collect())
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
    pub terms_begin: Term,
    pub terms_end: Term,
    pub location: Option<Location>,
}

impl Atom {
    #[cfg(test)]
    pub fn without_locations(&self) -> Self {
        Atom {
            data: self.data.clone(),
            terms_begin: self.terms_begin,
            terms_end: self.terms_end,
            location: None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Formula {
    pub atoms: Vec<Atom>,
    pub terms_begin: Term,
    pub terms_end: Term,
    pub location: Option<Location>,
}

impl Formula {
    #[cfg(test)]
    pub fn without_locations(&self) -> Self {
        Formula {
            atoms: self.atoms.iter().map(|a| a.without_locations()).collect(),
            terms_begin: self.terms_begin,
            terms_end: self.terms_end,
            location: None,
        }
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
    let terms_begin = Term(universe.len());
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
    let terms_end = Term(universe.len());
    Atom {
        data,
        terms_begin,
        terms_end,
        location: atom.location,
    }
}

fn translate_formula(universe: &mut TermUniverse, formula: &direct_ast::Formula) -> Formula {
    let terms_begin = Term(universe.len());
    let atoms = formula
        .atoms
        .iter()
        .map(|atom| translate_atom(atom, universe))
        .collect();
    let terms_end = Term(universe.len());
    Formula {
        atoms,
        terms_begin,
        terms_end,
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
                        terms_begin: Term(0),
                        terms_end: Term(0),
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
                        let terms_begin = Term(universe.len());
                        let arg = translate_term(arg, &mut universe);
                        let terms_end = Term(universe.len());
                        let data = AtomData::Defined(arg, None);
                        premise.atoms.push(Atom {
                            terms_begin,
                            terms_end,
                            data,
                            location: None,
                        });
                        arg
                    })
                    .collect();

                // Add `to!` to premise.
                let terms_begin = Term(universe.len());
                let to = translate_term(to, &mut universe);
                let terms_end = Term(universe.len());
                let data = AtomData::Defined(to, None);
                premise.atoms.push(Atom {
                    terms_begin,
                    terms_end,
                    data,
                    location: None,
                });

                premise.terms_end = terms_end;

                // Build conclusion: `from = to`. Only `from` is not defined yet.
                let from_data = TermData::Application(from_func.clone(), from_args);
                let from = universe.new_term(from_data, from.location);
                let eq = Atom {
                    terms_begin: Term(0),
                    terms_end: Term(universe.len()),
                    data: AtomData::Equal(from, to),
                    location: None,
                };
                let conclusion = Formula {
                    terms_begin: eq.terms_begin,
                    terms_end: eq.terms_end,
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
