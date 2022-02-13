use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Machine {
    pub sorts: Vec<String>,
    pub relations: HashMap<String, Vec<String>>,
}

type Program = Vec<Statement>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(String),
    MakeTuple(Vec<Term>),
    TupleProjection(Box<Term>, usize),
    NewElement(String),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Age {
    Old, New
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Query {
    relation: String,
    age: Age,
    filter: Vec<(usize, Term)>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Statement {
    Insert{term: Term, relation: String},
    Equate(Term, Term),
    For{loop_variable: String, query: Query, body: Vec<Statement>},
    Choose{choice_variable: String, query: Query, body: Vec<Statement>},
}
