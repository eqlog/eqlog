pub use crate::direct_ast::{Sort, Predicate, Function};
use crate::direct_ast;

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
pub struct TermUniverse(Vec<TermData>);

impl TermUniverse {
    pub fn new() -> TermUniverse {
        TermUniverse(Vec::new())
    }
    pub fn new_term(&mut self, data: TermData) -> Term {
        let tm = Term(self.0.len());
        self.0.push(data);
        tm
    }
    pub fn data(&self, tm: Term) -> &TermData {
        &self.0[tm.0]
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter_terms(&self) -> impl Iterator<Item=(Term, &TermData)> {
        self.0.iter().enumerate().map(|(i, data)| (Term(i), data))
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
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Formula(pub Vec<Atom>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SequentData {
    SurjectiveImplication(Formula, Formula),
    GeneralImplication(Formula, Formula),
    Reduction(Term, Term),
    ConditionalReduction(Formula, Term, Term),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sequent {
    pub data: SequentData,
    pub universe: TermUniverse,
    pub first_conclusion_term: Term,
}

fn translate_term(term: &direct_ast::Term, universe: &mut TermUniverse) -> Term {
    match term {
        direct_ast::Term::Variable(name) => {
            universe.new_term(TermData::Variable(name.clone()))
        },
        direct_ast::Term::Wildcard => {
            universe.new_term(TermData::Wildcard)
        },
        direct_ast::Term::Application(f, args) => {
            let translated_args = args.iter().map(|arg| translate_term(arg, universe)).collect();
            universe.new_term(TermData::Application(f.clone(), translated_args))
        },
    }
}

fn translate_atom(atom: &direct_ast::Atom, universe: &mut TermUniverse) -> Atom {
    let terms_begin = Term(universe.len());
    let data = match atom {
        direct_ast::Atom::Equal(lhs, rhs) => {
            let translated_lhs = translate_term(lhs, universe);
            let translated_rhs = translate_term(rhs, universe);
            AtomData::Equal(translated_lhs, translated_rhs)
        },
        direct_ast::Atom::Defined(tm, sort) => {
            let translated_tm = translate_term(tm, universe);
            AtomData::Defined(translated_tm, sort.clone())
        },
        direct_ast::Atom::Predicate(pred, args) => {
            let translated_args = args.iter().map(|arg| translate_term(arg, universe)).collect();
            AtomData::Predicate(pred.clone(), translated_args)
        },
    };
    let terms_end = Term(universe.len());
    Atom{data, terms_begin, terms_end}
}

fn translate_formula(formula: &direct_ast::Formula, universe: &mut TermUniverse) -> Formula {
    Formula(formula.0.iter().map(|atom| translate_atom(atom, universe)).collect())
}

pub fn direct_to_indirect(seq: &direct_ast::Sequent) -> Sequent {
    let mut universe = TermUniverse::new();
    use SequentData::*;
    let (data, first_conclusion_term) = match seq {
        direct_ast::Sequent::SurjectiveImplication(premise, conclusion) => {
            let premise = translate_formula(premise, &mut universe);
            let first_conclusion_term = Term(universe.len());
            let conclusion = translate_formula(conclusion, &mut universe);
            (SurjectiveImplication(premise, conclusion), first_conclusion_term)
        },
        direct_ast::Sequent::GeneralImplication(premise, conclusion) => {
            let premise = translate_formula(premise, &mut universe);
            let first_conclusion_term = Term(universe.len());
            let conclusion = translate_formula(conclusion, &mut universe);
            (GeneralImplication(premise, conclusion), first_conclusion_term)
        },
        direct_ast::Sequent::Reduction(from, to) => {
            use direct_ast::Term::*;
            let from_data: Option<(String, Vec<Term>)> = match from {
                Variable(_) | Wildcard => None,
                Application(name, args) => {
                    let args = args.iter().map(|arg| translate_term(arg, &mut universe)).collect();
                    Some((name.to_string(), args))
                },
            };
            let to = translate_term(to, &mut universe);
            let first_conclusion_term = Term(universe.len());
            let from = match from_data {
                None => translate_term(from, &mut universe),
                Some((name, args)) => universe.new_term(TermData::Application(name, args)),
            };
            (Reduction(from, to), first_conclusion_term)
        },
        direct_ast::Sequent::ConditionalReduction(premise, from, to) => {
            let premise = translate_formula(premise, &mut universe);
            use direct_ast::Term::*;
            let from_data: Option<(String, Vec<Term>)> = match from {
                Variable(_) | Wildcard => None,
                Application(name, args) => {
                    let args = args.iter().map(|arg| translate_term(arg, &mut universe)).collect();
                    Some((name.to_string(), args))
                },
            };
            let to = translate_term(to, &mut universe);
            let first_conclusion_term = Term(universe.len());
            let from = match from_data {
                None => translate_term(from, &mut universe),
                Some((name, args)) => universe.new_term(TermData::Application(name, args)),
            };
            (ConditionalReduction(premise, from, to), first_conclusion_term)
        },
    };
    Sequent{data, universe, first_conclusion_term}
}
