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
    pub data: TermData,
}

#[derive(Clone, Debug)]
pub enum TermData {
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
    pub data: TypeExprData,
}

#[derive(Clone, Debug)]
pub enum TypeExprData {
    Ambient(String),
    Member { term: Box<Term>, name: String },
    Mor(String),
}

#[derive(Clone, Debug)]
pub struct PredExpr {
    pub loc: Location,
    pub data: PredExprData,
}

#[derive(Clone, Debug)]
pub enum PredExprData {
    Ambient(String),
    Member { term: Box<Term>, name: String },
}

#[derive(Clone, Debug)]
pub struct FuncExpr {
    pub loc: Location,
    pub data: FuncExprData,
}

#[derive(Clone, Debug)]
pub enum FuncExprData {
    Ambient(String),
    Member { term: Box<Term>, name: String },
}

#[derive(Clone, Debug)]
pub struct IfAtom {
    pub loc: Location,
    pub data: IfAtomData,
}

#[derive(Clone, Debug)]
pub enum IfAtomData {
    Equal(Term, Term),
    Defined(Term),
    Pred { pred: PredExpr, args: TermList },
    Var { term: Term, typ: TypeExpr },
}

#[derive(Clone, Debug)]
pub struct ThenAtom {
    pub loc: Location,
    pub data: ThenAtomData,
}

#[derive(Clone, Debug)]
pub enum ThenAtomData {
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
    pub data: StmtData,
}

#[derive(Clone, Debug)]
pub enum StmtData {
    If(IfAtom),
    Then(ThenAtom),
    Branch(Vec<Vec<Stmt>>),
    Match { term: Term, cases: Vec<MatchCase> },
}
