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
pub struct Formula {
    pub atoms: Vec<Atom>,
    pub terms_begin: Term,
    pub terms_end: Term,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sequent {
    pub universe: TermUniverse,
    pub premise: Formula,
    pub conclusion: Formula,
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

fn translate_formula(universe: &mut TermUniverse, formula_atoms: &[direct_ast::Atom]) -> Formula {
    let terms_begin = Term(universe.len());
    let atoms = formula_atoms.iter().map(|atom| translate_atom(atom, universe)).collect();
    let terms_end = Term(universe.len());
    Formula{atoms, terms_begin, terms_end}
}

impl Sequent {
    pub fn new(sequent: &direct_ast::Sequent) -> Sequent {
        let mut universe = TermUniverse::new();

        use direct_ast::Sequent::*;
        match sequent {
            Implication(premise, conclusion) => Sequent {
                premise: translate_formula(&mut universe, &premise.0),
                conclusion: translate_formula(&mut universe, &conclusion.0),
                universe
            },
            Reduction{premise, from_function, from_args, to} => {
                // Translate premise atoms.
                let mut premise = translate_formula(&mut universe, &premise.0);

                // Add
                //     !from_arg[0] & !from_arg[1] & ...
                // to premise.
                let from_args: Vec<Term> =
                    from_args.iter()
                    .map(|arg| {
                        let terms_begin = Term(universe.len());
                        let arg = translate_term(arg, &mut universe);
                        let terms_end = Term(universe.len());
                        let data = AtomData::Defined(arg, None);
                        premise.atoms.push(Atom{terms_begin, terms_end, data});
                        arg
                    })
                    .collect();

                // Add
                //     !to
                // to premise.
                let terms_begin = Term(universe.len());
                let to = translate_term(to, &mut universe);
                let terms_end = Term(universe.len());
                let data = AtomData::Defined(to, None);
                premise.atoms.push(Atom{terms_begin, terms_end, data});

                // Update terms_end of premise.
                premise.terms_end = terms_end;

                // Build conclusion: from = to. Only "from" is not yet defined.
                let terms_begin = Term(universe.len());
                let from = universe.new_term(TermData::Application(from_function.to_string(), from_args));
                let terms_end = Term(universe.len());
                // TODO: Think about terms_begin and terms_end here. Shouldn't this encompass all
                // arg terms and descendants?
                let eq = Atom{terms_begin, terms_end, data: AtomData::Equal(from, to)};
                let conclusion = Formula{terms_begin, terms_end, atoms: vec![eq]};

                Sequent{premise, conclusion, universe}
            },
        }
    }
}
