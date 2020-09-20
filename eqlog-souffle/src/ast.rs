#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PredicateSignature {  
    pub name: String,
    pub arity: Vec<String>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FunctionSignature {
    pub name: String,
    pub domain: Vec<String>,
    pub codomain: String,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(String),
    Wildcard(Option<usize>),
    Application(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Atom {
    Equal(Term, Term),
    Defined(Term),
    Predicate(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Formula(pub Vec<Atom>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sequent {
    SurjectiveImplication(Formula, Formula),
    Implication(Formula, Formula),
    Reduction(Term, Term),
    ConditionalReduction(Formula, Term, Term),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Declaration {
    Sort(String),
    Predicate(PredicateSignature),
    Function(FunctionSignature),
    Axiom(Sequent),
}
