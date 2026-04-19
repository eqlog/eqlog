//! Flat, id-based AST.
//!
//! All nodes live in a single `Vec<(Location, Node)>` arena on [`Ast`], and
//! children are referenced by index rather than owned or borrowed. Each node
//! kind has a typed id (e.g. [`VarTermId`], [`EqualAtomId`]) that wraps a
//! [`NodeId`]; `ast.var_term(id)` returns the payload and panics if the id
//! points at a node of the wrong kind.
//!
//! Sum-type nodes like [`Term`], [`IfAtom`] or [`Stmt`] do not live in the
//! arena themselves. Instead, each variant is its own arena node, and the
//! sum-type enum simply wraps a typed variant id. A "generic" id such as
//! [`TermId`] is a variant-agnostic handle; `ast.term(id)` dispatches on the
//! node discriminant and returns the matching enum. Variant ids convert back
//! to the generic id via [`From`], so code can hand a specific id to an API
//! that asks for the generic one.
//!
//! Equality and predicate atoms are shared between [`IfAtom`] and
//! [`ThenAtom`]: the same [`EqualAtomId`] or [`PredAtomId`] can appear in
//! either context, and the enclosing [`IfStmt`] or [`ThenStmt`] records which.

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

/// Defines a variant id that is interchangeable with a generic "parent" id.
macro_rules! variant_id {
    ($variant:ident, $generic:ident) => {
        typed_id!($variant);

        impl From<$variant> for $generic {
            fn from(id: $variant) -> $generic {
                $generic(id.0)
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
variant_id!(VarTermId, TermId);
variant_id!(WildcardTermId, TermId);
variant_id!(AppTermId, TermId);
variant_id!(DomTermId, TermId);
variant_id!(CodTermId, TermId);
variant_id!(MorAppTermId, TermId);

typed_id!(TermListId);

typed_id!(TypeExprId);
variant_id!(AmbientTypeExprId, TypeExprId);
variant_id!(MemberTypeExprId, TypeExprId);
variant_id!(MorTypeExprId, TypeExprId);

typed_id!(PredExprId);
variant_id!(AmbientPredExprId, PredExprId);
variant_id!(MemberPredExprId, PredExprId);

typed_id!(FuncExprId);
variant_id!(AmbientFuncExprId, FuncExprId);
variant_id!(MemberFuncExprId, FuncExprId);

typed_id!(EqualAtomId);
typed_id!(PredAtomId);
typed_id!(DefinedIfAtomId);
typed_id!(VarIfAtomId);
typed_id!(DefinedThenAtomId);

typed_id!(MatchCaseId);

typed_id!(StmtId);
variant_id!(IfStmtId, StmtId);
variant_id!(ThenStmtId, StmtId);
variant_id!(BranchStmtId, StmtId);
variant_id!(MatchStmtId, StmtId);

#[derive(Clone, Debug)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Copy, Clone, Debug)]
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
pub struct VarTerm {
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub struct WildcardTerm;

#[derive(Copy, Clone, Debug)]
pub struct AppTerm {
    pub func: FuncExprId,
    pub args: TermListId,
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
    Var(VarTermId),
    // `WildcardTerm` has no payload, so nothing reads the id; kept for symmetry with the other
    // variants so that callers can still refer to a specific wildcard term node.
    Wildcard(#[allow(dead_code)] WildcardTermId),
    App(AppTermId),
    Dom(DomTermId),
    Cod(CodTermId),
    MorApp(MorAppTermId),
}

#[derive(Clone, Debug)]
pub struct TermList {
    pub terms: Vec<TermId>,
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
    pub term: TermId,
    pub typ: TypeExprId,
}

#[derive(Copy, Clone, Debug)]
pub struct DefinedThenAtom {
    pub var: Option<TermId>,
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
    pub atom: IfAtom,
}

#[derive(Copy, Clone, Debug)]
pub struct ThenStmt {
    pub atom: ThenAtom,
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
    TypeDecl(TypeDecl),
    PredDecl(PredDecl),
    FuncDecl(FuncDecl),
    RuleDecl(RuleDecl),
    EnumDecl(EnumDecl),
    ModelDecl(ModelDecl),
    CtorDecl(CtorDecl),
    ArgDecl(ArgDecl),
    ArgDeclList(ArgDeclList),
    VarTerm(VarTerm),
    WildcardTerm(WildcardTerm),
    AppTerm(AppTerm),
    DomTerm(DomTerm),
    CodTerm(CodTerm),
    MorAppTerm(MorAppTerm),
    TermList(TermList),
    AmbientTypeExpr(AmbientTypeExpr),
    MemberTypeExpr(MemberTypeExpr),
    MorTypeExpr(MorTypeExpr),
    AmbientPredExpr(AmbientPredExpr),
    MemberPredExpr(MemberPredExpr),
    AmbientFuncExpr(AmbientFuncExpr),
    MemberFuncExpr(MemberFuncExpr),
    EqualAtom(EqualAtom),
    PredAtom(PredAtom),
    DefinedIfAtom(DefinedIfAtom),
    VarIfAtom(VarIfAtom),
    DefinedThenAtom(DefinedThenAtom),
    MatchCase(MatchCase),
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
            #[allow(dead_code)]
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
accessor!(var_term, push_var_term, VarTermId, VarTerm);
accessor!(
    wildcard_term,
    push_wildcard_term,
    WildcardTermId,
    WildcardTerm
);
accessor!(app_term, push_app_term, AppTermId, AppTerm);
accessor!(dom_term, push_dom_term, DomTermId, DomTerm);
accessor!(cod_term, push_cod_term, CodTermId, CodTerm);
accessor!(mor_app_term, push_mor_app_term, MorAppTermId, MorAppTerm);
accessor!(term_list, push_term_list, TermListId, TermList);
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
accessor!(if_stmt, push_if_stmt, IfStmtId, IfStmt);
accessor!(then_stmt, push_then_stmt, ThenStmtId, ThenStmt);
accessor!(branch_stmt, push_branch_stmt, BranchStmtId, BranchStmt);
accessor!(match_stmt, push_match_stmt, MatchStmtId, MatchStmt);

impl Ast {
    pub fn term(&self, id: TermId) -> Term {
        match &self.nodes[(id.0).0].1 {
            Node::VarTerm(_) => Term::Var(VarTermId(id.0)),
            Node::WildcardTerm(_) => Term::Wildcard(WildcardTermId(id.0)),
            Node::AppTerm(_) => Term::App(AppTermId(id.0)),
            Node::DomTerm(_) => Term::Dom(DomTermId(id.0)),
            Node::CodTerm(_) => Term::Cod(CodTermId(id.0)),
            Node::MorAppTerm(_) => Term::MorApp(MorAppTermId(id.0)),
            other => panic!("expected Term at {:?}, got {:?}", id, other),
        }
    }

    pub fn type_expr(&self, id: TypeExprId) -> TypeExpr {
        match &self.nodes[(id.0).0].1 {
            Node::AmbientTypeExpr(_) => TypeExpr::Ambient(AmbientTypeExprId(id.0)),
            Node::MemberTypeExpr(_) => TypeExpr::Member(MemberTypeExprId(id.0)),
            Node::MorTypeExpr(_) => TypeExpr::Mor(MorTypeExprId(id.0)),
            other => panic!("expected TypeExpr at {:?}, got {:?}", id, other),
        }
    }

    pub fn pred_expr(&self, id: PredExprId) -> PredExpr {
        match &self.nodes[(id.0).0].1 {
            Node::AmbientPredExpr(_) => PredExpr::Ambient(AmbientPredExprId(id.0)),
            Node::MemberPredExpr(_) => PredExpr::Member(MemberPredExprId(id.0)),
            other => panic!("expected PredExpr at {:?}, got {:?}", id, other),
        }
    }

    pub fn func_expr(&self, id: FuncExprId) -> FuncExpr {
        match &self.nodes[(id.0).0].1 {
            Node::AmbientFuncExpr(_) => FuncExpr::Ambient(AmbientFuncExprId(id.0)),
            Node::MemberFuncExpr(_) => FuncExpr::Member(MemberFuncExprId(id.0)),
            other => panic!("expected FuncExpr at {:?}, got {:?}", id, other),
        }
    }

    pub fn stmt(&self, id: StmtId) -> Stmt {
        match &self.nodes[(id.0).0].1 {
            Node::IfStmt(_) => Stmt::If(IfStmtId(id.0)),
            Node::ThenStmt(_) => Stmt::Then(ThenStmtId(id.0)),
            Node::BranchStmt(_) => Stmt::Branch(BranchStmtId(id.0)),
            Node::MatchStmt(_) => Stmt::Match(MatchStmtId(id.0)),
            other => panic!("expected Stmt at {:?}, got {:?}", id, other),
        }
    }
}
