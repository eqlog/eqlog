#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Location(pub usize, pub usize);

impl Location {
    pub fn slice(self, source: &str) -> &str {
        let Location(a, b) = self;
        &source[a..b]
    }
}

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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermData {
    Variable(String),
    Wildcard,
    Application(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term {
    pub data: TermData,
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Formula {
    pub atoms: Vec<Atom>,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SequentData {
    Implication(Formula, Formula),
    Reduction {
        premise: Option<Formula>,
        from_function: String,
        from_args: Vec<Term>,
        to: Term,
    },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sequent {
    pub data: SequentData,
    pub location: Option<Location>,
}
