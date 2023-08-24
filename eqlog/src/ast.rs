use crate::source_display::Location;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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
    Application { func: String, args: Vec<Term> },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TermContext(Vec<(TermData, Location)>);

impl TermContext {
    pub fn new() -> TermContext {
        TermContext(Vec::new())
    }
    pub fn new_term(&mut self, data: TermData, location: Location) -> Term {
        let tm = Term(self.0.len());
        self.0.push((data, location));
        tm
    }
    pub fn data(&self, tm: Term) -> &TermData {
        &self.0[tm.0].0
    }
    pub fn location(&self, tm: Term) -> Location {
        self.0[tm.0].1
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter_terms(&self) -> impl Iterator<Item = Term> {
        (0..self.0.len()).map(Term)
    }
}

struct SubtermIterator<'a> {
    context: &'a TermContext,
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
        let mut child = match self.context.data(tm) {
            Variable(_) | Wildcard => return Some(tm),
            Application { func: _, args } if args.len() == next_child => return Some(tm),
            Application { func: _, args } => {
                debug_assert!(next_child < args.len());
                args[next_child]
            }
        };

        self.stack.push((tm, next_child + 1));
        while let Application { func: _, args } = self.context.data(child) {
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

impl TermContext {
    pub fn iter_subterms(&self, tm: Term) -> impl '_ + Iterator<Item = Term> {
        SubtermIterator {
            context: self,
            stack: vec![(tm, 0)],
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum IfAtomData {
    Equal(Term, Term),
    Defined(Term),
    Pred { pred: String, args: Vec<Term> },
    Var { term: Term, typ: String },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ThenAtomData {
    Equal(Term, Term),
    Defined { var: Option<Term>, term: Term },
    Pred { name: String, args: Vec<Term> },
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct IfAtom {
    pub data: IfAtomData,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ThenAtom {
    pub data: ThenAtomData,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum StmtData {
    If(IfAtom),
    Then(ThenAtom),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Stmt {
    pub data: StmtData,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct RuleDecl {
    pub name: Option<String>,
    pub body: Vec<Stmt>,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TypeDecl {
    pub name: String,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ArgDecl {
    pub name: String,
    pub typ: String,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ArgDeclList {
    pub arg_decls: Vec<ArgDecl>,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PredDecl {
    pub name: String,
    pub args: ArgDeclList,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FuncDecl {
    pub name: String,
    pub args: ArgDeclList,
    pub result: String,
    pub loc: Location,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Decl {
    Type(TypeDecl),
    Func(FuncDecl),
    Pred(PredDecl),
    Rule(RuleDecl),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Module(Vec<Decl>);
