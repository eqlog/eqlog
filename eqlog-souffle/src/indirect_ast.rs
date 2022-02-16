pub use crate::direct_ast::{Sort, Predicate, Function};
use crate::direct_ast;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term(pub usize);

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
pub enum Atom {
    Equal(Term, Term),
    Defined(Term, Option<String>),
    Predicate(String, Vec<Term>),
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
    match atom {
        direct_ast::Atom::Equal(lhs, rhs) => {
            let translated_lhs = translate_term(lhs, universe);
            let translated_rhs = translate_term(rhs, universe);
            Atom::Equal(translated_lhs, translated_rhs)
        },
        direct_ast::Atom::Defined(tm, sort) => {
            let translated_tm = translate_term(tm, universe);
            Atom::Defined(translated_tm, sort.clone())
        },
        direct_ast::Atom::Predicate(pred, args) => {
            let translated_args = args.iter().map(|arg| translate_term(arg, universe)).collect();
            Atom::Predicate(pred.clone(), translated_args)
        },
    }
}

fn translate_formula(formula: &direct_ast::Formula, universe: &mut TermUniverse) -> Formula {
    Formula(formula.0.iter().map(|atom| translate_atom(atom, universe)).collect())
}

pub fn direct_to_indirect(seq: &direct_ast::Sequent) -> Sequent {
    let mut universe = TermUniverse::new();
    use SequentData::*;
    let data = match seq {
        direct_ast::Sequent::SurjectiveImplication(premise, conclusion) => {
            let translated_premise = translate_formula(premise, &mut universe);
            let translated_conclusion = translate_formula(conclusion, &mut universe);
            SurjectiveImplication(translated_premise, translated_conclusion)
        },
        direct_ast::Sequent::GeneralImplication(premise, conclusion) => {
            let translated_premise = translate_formula(premise, &mut universe);
            let translated_conclusion = translate_formula(conclusion, &mut universe);
            GeneralImplication(translated_premise, translated_conclusion)
        },
        direct_ast::Sequent::Reduction(from, to) => {
            let translated_from = translate_term(from, &mut universe);
            let translated_to = translate_term(to, &mut universe);
            Reduction(translated_from, translated_to)
        },
        direct_ast::Sequent::ConditionalReduction(premise, from, to) => {
            let translated_premise = translate_formula(premise, &mut universe);
            let translated_from = translate_term(from, &mut universe);
            let translated_to = translate_term(to, &mut universe);
            ConditionalReduction(translated_premise, translated_from, translated_to)
        },
    };
    Sequent{data, universe}
}
