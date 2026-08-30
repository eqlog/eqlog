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
typed_id!(AppHeadId);
typed_id!(AppHeadMemberId);
typed_id!(TermMemberId);
typed_id!(DomTermId);
typed_id!(CodTermId);

typed_id!(TermListId);

typed_id!(TypeExprId);
typed_id!(AmbientTypeExprId);
typed_id!(MorTypeExprId);

typed_id!(PredExprId);
typed_id!(AmbientPredExprId);

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
    pub head: AppHeadId,
    pub args: TermListId,
}

#[derive(Copy, Clone, Debug)]
pub enum AppHead {
    Ident(IdentTermId),
    Member(AppHeadMemberId),
    Term(TermId),
}

#[derive(Clone, Debug)]
pub struct AppHeadMember {
    pub receiver: TermId,
    pub names: Vec<IdentTermId>,
}

#[derive(Copy, Clone, Debug)]
pub struct TermMember {
    pub term: TermId,
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
pub enum Term {
    Ident(IdentTermId),
    Wildcard,
    App(AppTermId),
    Member(TermMemberId),
    Dom(DomTermId),
    Cod(CodTermId),
}

pub(crate) enum ParsedTerm {
    Ident(IdentTermId),
    Term(TermId),
    Parenthesized(Box<ParsedPostfixTerm>),
}

pub(crate) enum TermPostfix {
    Member(IdentTermId),
    Apply(TermListId),
}

pub(crate) struct ParsedPostfixTerm {
    pub start: usize,
    pub parsed: ParsedTerm,
    pub names: Vec<IdentTermId>,
}

pub(crate) enum ParsedNamePath {
    Ambient(IdentTermId),
    Member(TermMemberId),
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
pub struct MorTypeExpr {
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub enum TypeExpr {
    Ambient(AmbientTypeExprId),
    Member(TermMemberId),
    Mor(MorTypeExprId),
}

#[derive(Clone, Debug)]
pub struct AmbientPredExpr {
    pub name: String,
}

#[derive(Copy, Clone, Debug)]
pub enum PredExpr {
    Ambient(AmbientPredExprId),
    Member(TermMemberId),
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
    AppHead(AppHead),
    AppHeadMember(AppHeadMember),
    TermMember(TermMember),
    DomTerm(DomTerm),
    CodTerm(CodTerm),
    TermList(TermList),
    TypeExpr(TypeExpr),
    AmbientTypeExpr(AmbientTypeExpr),
    MorTypeExpr(MorTypeExpr),
    PredExpr(PredExpr),
    AmbientPredExpr(AmbientPredExpr),
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
accessor!(app_head, push_app_head, AppHeadId, AppHead);
accessor!(
    app_head_member,
    push_app_head_member,
    AppHeadMemberId,
    AppHeadMember
);
accessor!(term_member, push_term_member, TermMemberId, TermMember);
accessor!(dom_term, push_dom_term, DomTermId, DomTerm);
accessor!(cod_term, push_cod_term, CodTermId, CodTerm);
accessor!(term_list, push_term_list, TermListId, TermList);
accessor!(type_expr, push_type_expr, TypeExprId, TypeExpr);
accessor!(
    ambient_type_expr,
    push_ambient_type_expr,
    AmbientTypeExprId,
    AmbientTypeExpr
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

#[cfg(test)]
mod tests {
    use super::{AppHead, Ast, Decl, IfAtom, Node, Stmt, Term};
    use crate::grammar::ModuleParser;

    fn parse_equal_rhs(source: &str) -> (Ast, super::TermId) {
        let mut ast = Ast::default();
        let module = match ModuleParser::new().parse(&mut ast, source) {
            Ok(module) => module,
            Err(_) => panic!("module did not parse"),
        };
        let Decl::Rule(rule) = *ast.decl(ast.module(module).decls[0]) else {
            panic!("expected rule")
        };
        let Stmt::If(if_stmt) = *ast.stmt(ast.rule_decl(rule).body[0]) else {
            panic!("expected if statement")
        };
        let IfAtom::Equal(equal) = *ast.if_atom(ast.if_stmt(if_stmt).atom) else {
            panic!("expected equality")
        };
        let rhs = ast.equal_atom(equal).rhs;
        (ast, rhs)
    }

    #[test]
    fn named_application_head_is_not_a_term() {
        let (ast, rhs) = parse_equal_rhs("rule { if x = foo(x); }");
        let Term::App(app) = *ast.term(rhs) else {
            panic!("expected application")
        };
        let AppHead::Ident(foo) = *ast.app_head(ast.app_term(app).head) else {
            panic!("expected named application head")
        };
        assert_eq!(ast.ident_term(foo).name, "foo");
        assert!(!ast.nodes.iter().any(|(_, node)| {
            let Node::Term(Term::Ident(ident)) = node else {
                return false;
            };
            ast.ident_term(*ident).name == "foo"
        }));
    }

    #[test]
    fn computed_application_head_retains_its_term() {
        let (ast, rhs) = parse_equal_rhs("rule { if x = foo(x)(x); }");
        let Term::App(outer) = *ast.term(rhs) else {
            panic!("expected outer application")
        };
        let AppHead::Term(inner) = *ast.app_head(ast.app_term(outer).head) else {
            panic!("expected computed application head")
        };
        assert!(matches!(ast.term(inner), Term::App(_)));
    }

    #[test]
    fn member_application_head_does_not_materialize_prefix_terms() {
        for source in [
            "rule { if x = foo.bar.p(x); }",
            "rule { if x = (foo.bar).p(x); }",
        ] {
            let (ast, rhs) = parse_equal_rhs(source);
            let Term::App(app) = *ast.term(rhs) else {
                panic!("expected application")
            };
            let AppHead::Member(member) = *ast.app_head(ast.app_term(app).head) else {
                panic!("expected member application head")
            };
            let member = ast.app_head_member(member);
            assert_eq!(
                member
                    .names
                    .iter()
                    .map(|name| ast.ident_term(*name).name.as_str())
                    .collect::<Vec<_>>(),
                ["bar", "p"]
            );
            assert!(matches!(ast.term(member.receiver), Term::Ident(_)));
            assert!(!ast.nodes.iter().any(|(_, node)| {
                let Node::Term(Term::Member(member)) = node else {
                    return false;
                };
                ast.ident_term(ast.term_member(*member).name).name == "bar"
            }));
        }
    }

    #[test]
    fn non_type_term_reports_a_parse_error() {
        let mut ast = Ast::default();
        assert!(ModuleParser::new().parse(&mut ast, "const x: _;").is_err());
    }

    #[test]
    fn type_and_predicate_paths_do_not_create_final_terms() {
        let source = "model M { type T; pred p(x: T); } rule { if m: M; if x: m.T; if m.p(x); }";
        let mut ast = Ast::default();
        assert!(ModuleParser::new().parse(&mut ast, source).is_ok());

        assert!(!ast.nodes.iter().any(|(_, node)| {
            let Node::Term(Term::Ident(ident)) = node else {
                return false;
            };
            matches!(ast.ident_term(*ident).name.as_str(), "T" | "p")
        }));
        assert!(!ast.nodes.iter().any(|(_, node)| {
            let Node::Term(Term::Member(member)) = node else {
                return false;
            };
            matches!(
                ast.ident_term(ast.term_member(*member).name).name.as_str(),
                "T" | "p"
            )
        }));
    }
}
