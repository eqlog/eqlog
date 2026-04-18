use crate::grammar_util::Location;

#[derive(Clone, Debug)]
pub struct Module {
    pub loc: Location,
    pub decls: Vec<Decl>,
}

#[derive(Clone, Debug)]
pub enum Decl {
    Type(TypeDecl),
    Pred(PredDecl),
    Func(FuncDecl),
    Rule(RuleDecl),
    Enum(EnumDecl),
    Model(ModelDecl),
}

#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub loc: Location,
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct PredDecl {
    pub loc: Location,
    pub name: String,
    pub args: ArgDeclList,
}

#[derive(Clone, Debug)]
pub struct FuncDecl {
    pub loc: Location,
    pub name: String,
    pub args: ArgDeclList,
    pub result: TypeExpr,
}

#[derive(Clone, Debug)]
pub struct RuleDecl {
    pub loc: Location,
    pub name: Option<String>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub struct EnumDecl {
    pub loc: Location,
    pub name: String,
    pub ctors: Vec<CtorDecl>,
}

#[derive(Clone, Debug)]
pub struct ModelDecl {
    pub loc: Location,
    pub name: String,
    pub body: Vec<Decl>,
}

#[derive(Clone, Debug)]
pub struct CtorDecl {
    pub loc: Location,
    pub name: String,
    pub args: ArgDeclList,
}

#[derive(Clone, Debug)]
pub struct ArgDecl {
    pub loc: Location,
    pub name: Option<String>,
    pub typ: TypeExpr,
}

#[derive(Clone, Debug)]
pub struct ArgDeclList {
    pub loc: Location,
    pub args: Vec<ArgDecl>,
}

#[derive(Clone, Debug)]
pub struct Term {
    pub loc: Location,
    pub kind: TermKind,
}

#[derive(Clone, Debug)]
pub enum TermKind {
    Var(String),
    Wildcard,
    App { func: FuncExpr, args: TermList },
    Dom(Box<Term>),
    Cod(Box<Term>),
    MorApp { mor: Box<Term>, arg: Box<Term> },
}

#[derive(Clone, Debug)]
pub struct TermList {
    pub loc: Location,
    pub terms: Vec<Term>,
}

#[derive(Clone, Debug)]
pub struct TypeExpr {
    pub loc: Location,
    pub kind: TypeExprKind,
}

#[derive(Clone, Debug)]
pub enum TypeExprKind {
    Ambient(String),
    Member { term: Box<Term>, name: String },
    Mor(String),
}

#[derive(Clone, Debug)]
pub struct PredExpr {
    pub loc: Location,
    pub kind: PredExprKind,
}

#[derive(Clone, Debug)]
pub enum PredExprKind {
    Ambient(String),
    Member { term: Box<Term>, name: String },
}

#[derive(Clone, Debug)]
pub struct FuncExpr {
    pub loc: Location,
    pub kind: FuncExprKind,
}

#[derive(Clone, Debug)]
pub enum FuncExprKind {
    Ambient(String),
    Member { term: Box<Term>, name: String },
}

#[derive(Clone, Debug)]
pub struct IfAtom {
    pub loc: Location,
    pub kind: IfAtomKind,
}

#[derive(Clone, Debug)]
pub enum IfAtomKind {
    Equal(Term, Term),
    Defined(Term),
    Pred { pred: PredExpr, args: TermList },
    Var { term: Term, typ: TypeExpr },
}

#[derive(Clone, Debug)]
pub struct ThenAtom {
    pub loc: Location,
    pub kind: ThenAtomKind,
}

#[derive(Clone, Debug)]
pub enum ThenAtomKind {
    Equal(Term, Term),
    Defined { var: Option<Term>, term: Term },
    Pred { pred: PredExpr, args: TermList },
}

#[derive(Clone, Debug)]
pub struct MatchCase {
    pub loc: Location,
    pub pattern: Term,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub loc: Location,
    pub kind: StmtKind,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    If(IfAtom),
    Then(ThenAtom),
    Branch(Vec<Vec<Stmt>>),
    Match { term: Term, cases: Vec<MatchCase> },
}
