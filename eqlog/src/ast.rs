//! Flat, id-based AST.
//!
//! All nodes live in a single `Vec<(Location, Node)>` arena on [`Ast`], and
//! children are referenced by index rather than owned or borrowed. Each node
//! kind has a typed id (e.g. [`TermId`], [`IfAtomId`]) that wraps a [`NodeId`];
//! `ast.term(id)` returns the payload and panics if the id points at a node of
//! the wrong kind.
//!
//! The arena representation lets downstream passes key side tables by id
//! without caring about pointer stability or borrow lifetimes.

use crate::grammar_util::Location;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(usize);

macro_rules! typed_id {
    ($name:ident) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(NodeId);

        impl From<$name> for NodeId {
            fn from(id: $name) -> NodeId {
                id.0
            }
        }
    };
}

typed_id!(ModuleId);
typed_id!(DeclId);
typed_id!(TypeDeclId);
typed_id!(PredDeclId);
typed_id!(FuncDeclId);
typed_id!(ConstDeclId);
typed_id!(RuleDeclId);
typed_id!(EnumDeclId);
typed_id!(ModelDeclId);
typed_id!(CtorDeclId);
typed_id!(ArgDeclId);
typed_id!(ArgDeclListId);

typed_id!(TermId);
typed_id!(IdentTermId);
typed_id!(AppTermId);
typed_id!(MemberConstTermId);
typed_id!(DomTermId);
typed_id!(CodTermId);
typed_id!(MorAppTermId);

typed_id!(TermListId);

typed_id!(BinderId);
typed_id!(BinderIdentId);

typed_id!(TypeExprId);
typed_id!(AmbientTypeExprId);
typed_id!(MemberTypeExprId);
typed_id!(MorTypeExprId);

typed_id!(PredExprId);
typed_id!(AmbientPredExprId);
typed_id!(MemberPredExprId);

typed_id!(FuncExprId);
typed_id!(AmbientFuncExprId);
typed_id!(MemberFuncExprId);

typed_id!(IfAtomId);
typed_id!(ThenAtomId);
typed_id!(EqualAtomId);
typed_id!(PredAtomId);
typed_id!(DefinedIfAtomId);
typed_id!(VarIfAtomId);
typed_id!(DefinedThenAtomId);

typed_id!(MatchCaseId);

typed_id!(StmtId);
typed_id!(IfStmtId);
typed_id!(ThenStmtId);
typed_id!(BranchStmtId);
typed_id!(MatchStmtId);

#[derive(Clone, Debug)]
pub struct Module {
    pub decls: Vec<DeclId>,
}

#[derive(Copy, Clone, Debug)]
pub enum Decl {
    Type(TypeDeclId),
    Pred(PredDeclId),
    Func(FuncDeclId),
    Const(ConstDeclId),
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
pub struct ConstDecl {
    pub name: String,
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
    pub body: Vec<DeclId>,
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
pub struct IdentTerm {
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub struct AppTerm {
    pub func: FuncExprId,
    pub args: TermListId,
}

#[derive(Copy, Clone, Debug)]
pub struct MemberConstTerm {
    pub receiver: TermId,
    pub name: IdentTermId,
}

#[derive(Copy, Clone, Debug)]
pub struct DomTerm {
    pub arg: TermId,
}

#[derive(Copy, Clone, Debug)]
pub struct CodTerm {
    pub arg: TermId,
}

#[derive(Copy, Clone, Debug)]
pub struct MorAppTerm {
    pub mor: TermId,
    pub arg: TermId,
}

#[derive(Copy, Clone, Debug)]
pub enum Term {
    Ident(IdentTermId),
    Wildcard,
    App(AppTermId),
    MemberConst(MemberConstTermId),
    Dom(DomTermId),
    Cod(CodTermId),
    MorApp(MorAppTermId),
}

#[derive(Clone, Debug)]
pub struct TermList {
    pub terms: Vec<TermId>,
}

#[derive(Clone, Debug)]
pub struct BinderIdent {
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub enum Binder {
    Ident(BinderIdentId),
    Wildcard,
}

#[derive(Clone, Debug)]
pub struct AmbientTypeExpr {
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct MemberTypeExpr {
    pub term: TermId,
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct MorTypeExpr {
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub enum TypeExpr {
    Ambient(AmbientTypeExprId),
    Member(MemberTypeExprId),
    Mor(MorTypeExprId),
}

#[derive(Clone, Debug)]
pub struct AmbientPredExpr {
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct MemberPredExpr {
    pub term: TermId,
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub enum PredExpr {
    Ambient(AmbientPredExprId),
    Member(MemberPredExprId),
}

#[derive(Clone, Debug)]
pub struct AmbientFuncExpr {
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct MemberFuncExpr {
    pub term: TermId,
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub enum FuncExpr {
    Ambient(AmbientFuncExprId),
    Member(MemberFuncExprId),
}

#[derive(Copy, Clone, Debug)]
pub struct EqualAtom {
    pub lhs: TermId,
    pub rhs: TermId,
}

#[derive(Copy, Clone, Debug)]
pub struct PredAtom {
    pub pred: PredExprId,
    pub args: TermListId,
}

#[derive(Copy, Clone, Debug)]
pub struct DefinedIfAtom {
    pub term: TermId,
}

#[derive(Copy, Clone, Debug)]
pub struct VarIfAtom {
    pub binder: BinderId,
    pub typ: TypeExprId,
}

#[derive(Copy, Clone, Debug)]
pub struct DefinedThenAtom {
    pub binder: Option<BinderId>,
    pub term: TermId,
}

#[derive(Copy, Clone, Debug)]
pub enum IfAtom {
    Equal(EqualAtomId),
    Defined(DefinedIfAtomId),
    Pred(PredAtomId),
    Var(VarIfAtomId),
}

#[derive(Copy, Clone, Debug)]
pub enum ThenAtom {
    Equal(EqualAtomId),
    Defined(DefinedThenAtomId),
    Pred(PredAtomId),
}

#[derive(Clone, Debug)]
pub struct MatchCase {
    pub pattern: TermId,
    pub body: Vec<StmtId>,
}

#[derive(Copy, Clone, Debug)]
pub struct IfStmt {
    pub atom: IfAtomId,
}

#[derive(Copy, Clone, Debug)]
pub struct ThenStmt {
    pub atom: ThenAtomId,
}

#[derive(Clone, Debug)]
pub struct BranchStmt {
    pub blocks: Vec<Vec<StmtId>>,
}

#[derive(Clone, Debug)]
pub struct MatchStmt {
    pub term: TermId,
    pub cases: Vec<MatchCaseId>,
}

#[derive(Copy, Clone, Debug)]
pub enum Stmt {
    If(IfStmtId),
    Then(ThenStmtId),
    Branch(BranchStmtId),
    Match(MatchStmtId),
}

#[derive(Clone, Debug)]
pub enum Node {
    Module(Module),
    Decl(Decl),
    TypeDecl(TypeDecl),
    PredDecl(PredDecl),
    FuncDecl(FuncDecl),
    ConstDecl(ConstDecl),
    RuleDecl(RuleDecl),
    EnumDecl(EnumDecl),
    ModelDecl(ModelDecl),
    CtorDecl(CtorDecl),
    ArgDecl(ArgDecl),
    ArgDeclList(ArgDeclList),
    Term(Term),
    IdentTerm(IdentTerm),
    AppTerm(AppTerm),
    MemberConstTerm(MemberConstTerm),
    DomTerm(DomTerm),
    CodTerm(CodTerm),
    MorAppTerm(MorAppTerm),
    TermList(TermList),
    Binder(Binder),
    BinderIdent(BinderIdent),
    TypeExpr(TypeExpr),
    AmbientTypeExpr(AmbientTypeExpr),
    MemberTypeExpr(MemberTypeExpr),
    MorTypeExpr(MorTypeExpr),
    PredExpr(PredExpr),
    AmbientPredExpr(AmbientPredExpr),
    MemberPredExpr(MemberPredExpr),
    FuncExpr(FuncExpr),
    AmbientFuncExpr(AmbientFuncExpr),
    MemberFuncExpr(MemberFuncExpr),
    IfAtom(IfAtom),
    ThenAtom(ThenAtom),
    EqualAtom(EqualAtom),
    PredAtom(PredAtom),
    DefinedIfAtom(DefinedIfAtom),
    VarIfAtom(VarIfAtom),
    DefinedThenAtom(DefinedThenAtom),
    MatchCase(MatchCase),
    Stmt(Stmt),
    IfStmt(IfStmt),
    ThenStmt(ThenStmt),
    BranchStmt(BranchStmt),
    MatchStmt(MatchStmt),
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
accessor!(decl, push_decl, DeclId, Decl);
accessor!(type_decl, push_type_decl, TypeDeclId, TypeDecl);
accessor!(pred_decl, push_pred_decl, PredDeclId, PredDecl);
accessor!(func_decl, push_func_decl, FuncDeclId, FuncDecl);
accessor!(const_decl, push_const_decl, ConstDeclId, ConstDecl);
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
accessor!(ident_term, push_ident_term, IdentTermId, IdentTerm);
accessor!(app_term, push_app_term, AppTermId, AppTerm);
accessor!(
    member_const_term,
    push_member_const_term,
    MemberConstTermId,
    MemberConstTerm
);
accessor!(dom_term, push_dom_term, DomTermId, DomTerm);
accessor!(cod_term, push_cod_term, CodTermId, CodTerm);
accessor!(mor_app_term, push_mor_app_term, MorAppTermId, MorAppTerm);
accessor!(term_list, push_term_list, TermListId, TermList);
accessor!(binder, push_binder, BinderId, Binder);
accessor!(binder_ident, push_binder_ident, BinderIdentId, BinderIdent);
accessor!(type_expr, push_type_expr, TypeExprId, TypeExpr);
accessor!(
    ambient_type_expr,
    push_ambient_type_expr,
    AmbientTypeExprId,
    AmbientTypeExpr
);
accessor!(
    member_type_expr,
    push_member_type_expr,
    MemberTypeExprId,
    MemberTypeExpr
);
accessor!(
    mor_type_expr,
    push_mor_type_expr,
    MorTypeExprId,
    MorTypeExpr
);
accessor!(pred_expr, push_pred_expr, PredExprId, PredExpr);
accessor!(
    ambient_pred_expr,
    push_ambient_pred_expr,
    AmbientPredExprId,
    AmbientPredExpr
);
accessor!(
    member_pred_expr,
    push_member_pred_expr,
    MemberPredExprId,
    MemberPredExpr
);
accessor!(func_expr, push_func_expr, FuncExprId, FuncExpr);
accessor!(
    ambient_func_expr,
    push_ambient_func_expr,
    AmbientFuncExprId,
    AmbientFuncExpr
);
accessor!(
    member_func_expr,
    push_member_func_expr,
    MemberFuncExprId,
    MemberFuncExpr
);
accessor!(if_atom, push_if_atom, IfAtomId, IfAtom);
accessor!(then_atom, push_then_atom, ThenAtomId, ThenAtom);
accessor!(equal_atom, push_equal_atom, EqualAtomId, EqualAtom);
accessor!(pred_atom, push_pred_atom, PredAtomId, PredAtom);
accessor!(
    defined_if_atom,
    push_defined_if_atom,
    DefinedIfAtomId,
    DefinedIfAtom
);
accessor!(var_if_atom, push_var_if_atom, VarIfAtomId, VarIfAtom);
accessor!(
    defined_then_atom,
    push_defined_then_atom,
    DefinedThenAtomId,
    DefinedThenAtom
);
accessor!(match_case, push_match_case, MatchCaseId, MatchCase);
accessor!(stmt, push_stmt, StmtId, Stmt);
accessor!(if_stmt, push_if_stmt, IfStmtId, IfStmt);
accessor!(then_stmt, push_then_stmt, ThenStmtId, ThenStmt);
accessor!(branch_stmt, push_branch_stmt, BranchStmtId, BranchStmt);
accessor!(match_stmt, push_match_stmt, MatchStmtId, MatchStmt);
