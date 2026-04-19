use crate::grammar_util::Location;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(usize);

macro_rules! typed_id {
    ($name:ident) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $name(NodeId);

        impl From<$name> for NodeId {
            fn from(id: $name) -> NodeId {
                id.0
            }
        }
    };
}

typed_id!(ModuleId);
typed_id!(TypeDeclId);
typed_id!(PredDeclId);
typed_id!(FuncDeclId);
typed_id!(RuleDeclId);
typed_id!(EnumDeclId);
typed_id!(ModelDeclId);
typed_id!(CtorDeclId);
typed_id!(ArgDeclId);
typed_id!(ArgDeclListId);
typed_id!(TermId);
typed_id!(TermListId);
typed_id!(TypeExprId);
typed_id!(PredExprId);
typed_id!(FuncExprId);
typed_id!(IfAtomId);
typed_id!(ThenAtomId);
typed_id!(MatchCaseId);
typed_id!(StmtId);

#[derive(Clone, Debug)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Clone, Debug)]
pub enum Decl {
    Type(TypeDeclId),
    Pred(PredDeclId),
    Func(FuncDeclId),
    Rule(RuleDeclId),
    Enum(EnumDeclId),
    Model(ModelDeclId),
}

#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct PredDecl {
    pub name: String,
    pub args: ArgDeclListId,
}

#[derive(Clone, Debug)]
pub struct FuncDecl {
    pub name: String,
    pub args: ArgDeclListId,
    pub result: TypeExprId,
}

#[derive(Clone, Debug)]
pub struct RuleDecl {
    pub name: Option<String>,
    pub body: Vec<StmtId>,
}

#[derive(Clone, Debug)]
pub struct EnumDecl {
    pub name: String,
    pub ctors: Vec<CtorDeclId>,
}

#[derive(Clone, Debug)]
pub struct ModelDecl {
    pub name: String,
    pub body: Vec<Decl>,
}

#[derive(Clone, Debug)]
pub struct CtorDecl {
    pub name: String,
    pub args: ArgDeclListId,
}

#[derive(Clone, Debug)]
pub struct ArgDecl {
    pub name: Option<String>,
    pub typ: TypeExprId,
}

#[derive(Clone, Debug)]
pub struct ArgDeclList {
    pub args: Vec<ArgDeclId>,
}

#[derive(Clone, Debug)]
pub enum Term {
    Var(String),
    Wildcard,
    App { func: FuncExprId, args: TermListId },
    Dom(TermId),
    Cod(TermId),
    MorApp { mor: TermId, arg: TermId },
}

#[derive(Clone, Debug)]
pub struct TermList {
    pub terms: Vec<TermId>,
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    Ambient(String),
    Member { term: TermId, name: String },
    Mor(String),
}

#[derive(Clone, Debug)]
pub enum PredExpr {
    Ambient(String),
    Member { term: TermId, name: String },
}

#[derive(Clone, Debug)]
pub enum FuncExpr {
    Ambient(String),
    Member { term: TermId, name: String },
}

#[derive(Clone, Debug)]
pub enum IfAtom {
    Equal(TermId, TermId),
    Defined(TermId),
    Pred { pred: PredExprId, args: TermListId },
    Var { term: TermId, typ: TypeExprId },
}

#[derive(Clone, Debug)]
pub enum ThenAtom {
    Equal(TermId, TermId),
    Defined { var: Option<TermId>, term: TermId },
    Pred { pred: PredExprId, args: TermListId },
}

#[derive(Clone, Debug)]
pub struct MatchCase {
    pub pattern: TermId,
    pub body: Vec<StmtId>,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    If(IfAtomId),
    Then(ThenAtomId),
    Branch(Vec<Vec<StmtId>>),
    Match {
        term: TermId,
        cases: Vec<MatchCaseId>,
    },
}

#[derive(Clone, Debug)]
pub enum Node {
    Module(Module),
    TypeDecl(TypeDecl),
    PredDecl(PredDecl),
    FuncDecl(FuncDecl),
    RuleDecl(RuleDecl),
    EnumDecl(EnumDecl),
    ModelDecl(ModelDecl),
    CtorDecl(CtorDecl),
    ArgDecl(ArgDecl),
    ArgDeclList(ArgDeclList),
    Term(Term),
    TermList(TermList),
    TypeExpr(TypeExpr),
    PredExpr(PredExpr),
    FuncExpr(FuncExpr),
    IfAtom(IfAtom),
    ThenAtom(ThenAtom),
    MatchCase(MatchCase),
    Stmt(Stmt),
}

#[derive(Clone, Debug, Default)]
pub struct Ast {
    nodes: Vec<(Location, Node)>,
}

impl Ast {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn loc(&self, id: impl Into<NodeId>) -> Location {
        self.nodes[id.into().0].0
    }
}

macro_rules! accessor {
    ($getter:ident, $pusher:ident, $id:ident, $kind:ident) => {
        impl Ast {
            pub fn $getter(&self, id: $id) -> &$kind {
                match &self.nodes[(id.0).0].1 {
                    Node::$kind(d) => d,
                    other => panic!(
                        "expected {} at {:?}, got {:?}",
                        stringify!($kind),
                        id,
                        other
                    ),
                }
            }

            pub fn $pusher(&mut self, loc: Location, data: $kind) -> $id {
                let id = NodeId(self.nodes.len());
                self.nodes.push((loc, Node::$kind(data)));
                $id(id)
            }
        }
    };
}

accessor!(module, push_module, ModuleId, Module);
accessor!(type_decl, push_type_decl, TypeDeclId, TypeDecl);
accessor!(pred_decl, push_pred_decl, PredDeclId, PredDecl);
accessor!(func_decl, push_func_decl, FuncDeclId, FuncDecl);
accessor!(rule_decl, push_rule_decl, RuleDeclId, RuleDecl);
accessor!(enum_decl, push_enum_decl, EnumDeclId, EnumDecl);
accessor!(model_decl, push_model_decl, ModelDeclId, ModelDecl);
accessor!(ctor_decl, push_ctor_decl, CtorDeclId, CtorDecl);
accessor!(arg_decl, push_arg_decl, ArgDeclId, ArgDecl);
accessor!(
    arg_decl_list,
    push_arg_decl_list,
    ArgDeclListId,
    ArgDeclList
);
accessor!(term, push_term, TermId, Term);
accessor!(term_list, push_term_list, TermListId, TermList);
accessor!(type_expr, push_type_expr, TypeExprId, TypeExpr);
accessor!(pred_expr, push_pred_expr, PredExprId, PredExpr);
accessor!(func_expr, push_func_expr, FuncExprId, FuncExpr);
accessor!(if_atom, push_if_atom, IfAtomId, IfAtom);
accessor!(then_atom, push_then_atom, ThenAtomId, ThenAtom);
accessor!(match_case, push_match_case, MatchCaseId, MatchCase);
accessor!(stmt, push_stmt, StmtId, Stmt);
