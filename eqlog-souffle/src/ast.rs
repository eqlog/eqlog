//#[derive(Clone, PartialEq, Eq, Hash, Debug)]
//pub struct PredicateArity {  
//    pub name: String,
//    pub arity: Vec<String>,
//}
//
//#[derive(Clone, PartialEq, Eq, Hash, Debug)]
//pub struct FunctionArity {
//    pub name: String,
//    pub domain: Vec<String>,
//    pub codomain: String,
//}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(String),
    Wildcard(Option<usize>),
    Application(String, Vec<Term>),
    // Typed(Box<Term>, String),
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
pub enum Sequent {
    Implication(Formula, Formula),
    //Introduction(Formula, Term),
    Reduction(Term, Term),
    ConditionalReduction(Formula, Term, Term),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Declaration {
    Sort(String),
    Predicate { name: String, arity: Vec<String> },
    Function { name: String, dom: Vec<String>, cod: String },
    Axiom(Sequent),
}

pub trait Ast {
    fn for_each_subterm<'a, F: FnMut(&'a Term)>(&'a self, fun: F);
    fn for_each_subterm_mut<F: for<'a> FnMut(&'a mut Term)>(&mut self, fun: F);
}

fn for_each_subterm_term_impl<'a, F: FnMut(&'a Term)>(tm: &'a Term, fun: &mut F) {
    use Term::*;
    match tm {
        Variable(_) => (),
        Wildcard(_) => (),
        Application(_, args) => {
            for arg in args {
                for_each_subterm_term_impl(arg, fun);
            }
        }
    }
    fun(tm);
}

fn for_each_subterm_mut_term_impl<F: for<'a> FnMut(&'a mut Term)>(tm: &mut Term, fun: &mut F) {
    use Term::*;
    match tm {
        Variable(_) => (),
        Wildcard(_) => (),
        Application(_, args) => {
            for arg in args {
                for_each_subterm_mut_term_impl(arg, fun);
            }
        }
    }
    fun(tm);
}

impl Ast for Term {
    fn for_each_subterm<'a, F: FnMut(&'a Term)>(&'a self, mut fun: F) {
        for_each_subterm_term_impl(self, &mut fun);
    }
    fn for_each_subterm_mut<F: for<'a> FnMut(&'a mut Term)>(&mut self, mut fun: F) {
        for_each_subterm_mut_term_impl(self, &mut fun);
    }
}

impl Ast for Atom {
    fn for_each_subterm<'a, F: FnMut(&'a Term)>(&'a self, mut fun: F) {
        use Atom::*;
        match self {
            Equal(lhs, rhs) => {
                lhs.for_each_subterm(&mut fun);
                rhs.for_each_subterm(&mut fun);
            },
            Defined(tm, _) => {
                tm.for_each_subterm(fun);
            },
            Predicate(_, args) => {
                for tm in args {
                    tm.for_each_subterm(&mut fun);
                }
            },
        }
    }
    fn for_each_subterm_mut<F: for<'a> FnMut(&'a mut Term)>(&mut self, mut fun: F) {
        use Atom::*;
        match self {
            Equal(lhs, rhs) => {
                lhs.for_each_subterm_mut(&mut fun);
                rhs.for_each_subterm_mut(&mut fun);
            },
            Defined(tm, _) => {
                tm.for_each_subterm_mut(fun);
            },
            Predicate(_, args) => {
                for tm in args {
                    tm.for_each_subterm_mut(&mut fun);
                }
            },
        }
    }
}

impl Ast for Formula {
    fn for_each_subterm<'a, F: FnMut(&'a Term)>(&'a self, mut fun: F) {
        for atom in self.0.iter() {
            atom.for_each_subterm(&mut fun);
        }
    }
    fn for_each_subterm_mut<F: for<'a> FnMut(&'a mut Term)>(&mut self, mut fun: F) {
        for atom in self.0.iter_mut() {
            atom.for_each_subterm_mut(&mut fun);
        }
    }
}

impl Ast for Sequent {
    fn for_each_subterm<'a, F: FnMut(&'a Term)>(&'a self, mut fun: F) {
        use Sequent::*;
        match self {
            Implication(prem, conc) => {
                prem.for_each_subterm(&mut fun);
                conc.for_each_subterm(&mut fun);
            },
            //Introduction(prem, conc) => {
            //    prem.for_each_subterm(&mut fun);
            //    conc.for_each_subterm(&mut fun);
            //},
            Reduction(from, to) => {
                from.for_each_subterm(&mut fun);
                to.for_each_subterm(&mut fun);
            },
            ConditionalReduction(prem, from, to) => {
                prem.for_each_subterm(&mut fun);
                from.for_each_subterm(&mut fun);
                to.for_each_subterm(&mut fun);
            }
        }
    }
    fn for_each_subterm_mut<F: for<'a> FnMut(&'a mut Term)>(&mut self, mut fun: F) {
        use Sequent::*;
        match self {
            Implication(prem, conc) => {
                prem.for_each_subterm_mut(&mut fun);
                conc.for_each_subterm_mut(&mut fun);
            },
            //Introduction(prem, conc) => {
            //    prem.for_each_subterm_mut(&mut fun);
            //    conc.for_each_subterm_mut(&mut fun);
            //},
            Reduction(from, to) => {
                from.for_each_subterm_mut(&mut fun);
                to.for_each_subterm_mut(&mut fun);
            },
            ConditionalReduction(prem, from, to) => {
                prem.for_each_subterm_mut(&mut fun);
                from.for_each_subterm_mut(&mut fun);
                to.for_each_subterm_mut(&mut fun);
            }
        }
    }
}
