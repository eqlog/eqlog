//! Scope resolution pass.
//!
//! Builds a graph of [`Scope`]s over the AST and associates each AST node with
//! the scope it participates in. Two side tables are maintained depending on
//! the scoping discipline of the node:
//!
//! * Unordered nodes (modules, models, decls): a single [`ScopeId`] is
//!   associated via [`Scopes::flat`]. Within an unordered scope, declaration
//!   order does not affect which names are visible.
//! * Ordered nodes (rule-body descendants and arg-list descendants): an
//!   `entry` and an `exit` [`ScopeId`] are associated via [`Scopes::entry`]
//!   and [`Scopes::exit`]. Sibling nodes chain so that names bound in an
//!   earlier sibling are visible in a later one.
//!
//! Every variable term occurrence and every named arg declaration extends the
//! current scope with a fresh child scope that contains the corresponding
//! [`Symbol`]. Lookups walk the `parent` chain, so later occurrences shadow
//! earlier ones, and ambient global symbols are reachable from the innermost
//! scope via the chain out into the surrounding flat scope.

use std::collections::BTreeMap;

use crate::ast::*;
use crate::error::CompileError;
use crate::grammar_util::Location;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopeId(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Symbol {
    Type(TypeDeclId),
    Pred(PredDeclId),
    Func(FuncDeclId),
    Enum(EnumDeclId),
    Ctor(CtorDeclId),
    Model(ModelDeclId),
    Rule(RuleDeclId),
    Arg(ArgDeclId),
    Var(VarTermId),
}

#[derive(Clone, Debug)]
pub struct Scope {
    #[allow(dead_code)]
    pub parent: Option<ScopeId>,
    pub symbols: BTreeMap<String, Symbol>,
}

#[derive(Copy, Clone, Debug)]
pub enum UnorderedNodeId {
    Module(ModuleId),
    Decl(DeclId),
    TypeDecl(TypeDeclId),
    PredDecl(PredDeclId),
    FuncDecl(FuncDeclId),
    EnumDecl(EnumDeclId),
    CtorDecl(CtorDeclId),
    ModelDecl(ModelDeclId),
    RuleDecl(RuleDeclId),
}

#[derive(Copy, Clone, Debug)]
pub enum OrderedNodeId {
    ArgDecl(ArgDeclId),
    ArgDeclList(ArgDeclListId),
    Stmt(StmtId),
    IfStmt(IfStmtId),
    ThenStmt(ThenStmtId),
    BranchStmt(BranchStmtId),
    MatchStmt(MatchStmtId),
    MatchCase(MatchCaseId),
    IfAtom(IfAtomId),
    ThenAtom(ThenAtomId),
    EqualAtom(EqualAtomId),
    PredAtom(PredAtomId),
    DefinedIfAtom(DefinedIfAtomId),
    VarIfAtom(VarIfAtomId),
    DefinedThenAtom(DefinedThenAtomId),
    Term(TermId),
    VarTerm(VarTermId),
    AppTerm(AppTermId),
    DomTerm(DomTermId),
    CodTerm(CodTermId),
    MorAppTerm(MorAppTermId),
    TermList(TermListId),
    TypeExpr(TypeExprId),
    AmbientTypeExpr(AmbientTypeExprId),
    MemberTypeExpr(MemberTypeExprId),
    MorTypeExpr(MorTypeExprId),
    PredExpr(PredExprId),
    AmbientPredExpr(AmbientPredExprId),
    MemberPredExpr(MemberPredExprId),
    FuncExpr(FuncExprId),
    AmbientFuncExpr(AmbientFuncExprId),
    MemberFuncExpr(MemberFuncExprId),
}

macro_rules! unordered_from {
    ($id:ty, $variant:ident) => {
        impl From<$id> for UnorderedNodeId {
            fn from(id: $id) -> UnorderedNodeId {
                UnorderedNodeId::$variant(id)
            }
        }
    };
}

unordered_from!(ModuleId, Module);
unordered_from!(DeclId, Decl);
unordered_from!(TypeDeclId, TypeDecl);
unordered_from!(PredDeclId, PredDecl);
unordered_from!(FuncDeclId, FuncDecl);
unordered_from!(EnumDeclId, EnumDecl);
unordered_from!(CtorDeclId, CtorDecl);
unordered_from!(ModelDeclId, ModelDecl);
unordered_from!(RuleDeclId, RuleDecl);

impl From<UnorderedNodeId> for NodeId {
    fn from(id: UnorderedNodeId) -> NodeId {
        match id {
            UnorderedNodeId::Module(i) => i.into(),
            UnorderedNodeId::Decl(i) => i.into(),
            UnorderedNodeId::TypeDecl(i) => i.into(),
            UnorderedNodeId::PredDecl(i) => i.into(),
            UnorderedNodeId::FuncDecl(i) => i.into(),
            UnorderedNodeId::EnumDecl(i) => i.into(),
            UnorderedNodeId::CtorDecl(i) => i.into(),
            UnorderedNodeId::ModelDecl(i) => i.into(),
            UnorderedNodeId::RuleDecl(i) => i.into(),
        }
    }
}

macro_rules! ordered_from {
    ($id:ty, $variant:ident) => {
        impl From<$id> for OrderedNodeId {
            fn from(id: $id) -> OrderedNodeId {
                OrderedNodeId::$variant(id)
            }
        }
    };
}

ordered_from!(ArgDeclId, ArgDecl);
ordered_from!(ArgDeclListId, ArgDeclList);
ordered_from!(StmtId, Stmt);
ordered_from!(IfStmtId, IfStmt);
ordered_from!(ThenStmtId, ThenStmt);
ordered_from!(BranchStmtId, BranchStmt);
ordered_from!(MatchStmtId, MatchStmt);
ordered_from!(MatchCaseId, MatchCase);
ordered_from!(IfAtomId, IfAtom);
ordered_from!(ThenAtomId, ThenAtom);
ordered_from!(EqualAtomId, EqualAtom);
ordered_from!(PredAtomId, PredAtom);
ordered_from!(DefinedIfAtomId, DefinedIfAtom);
ordered_from!(VarIfAtomId, VarIfAtom);
ordered_from!(DefinedThenAtomId, DefinedThenAtom);
ordered_from!(TermId, Term);
ordered_from!(VarTermId, VarTerm);
ordered_from!(AppTermId, AppTerm);
ordered_from!(DomTermId, DomTerm);
ordered_from!(CodTermId, CodTerm);
ordered_from!(MorAppTermId, MorAppTerm);
ordered_from!(TermListId, TermList);
ordered_from!(TypeExprId, TypeExpr);
ordered_from!(AmbientTypeExprId, AmbientTypeExpr);
ordered_from!(MemberTypeExprId, MemberTypeExpr);
ordered_from!(MorTypeExprId, MorTypeExpr);
ordered_from!(PredExprId, PredExpr);
ordered_from!(AmbientPredExprId, AmbientPredExpr);
ordered_from!(MemberPredExprId, MemberPredExpr);
ordered_from!(FuncExprId, FuncExpr);
ordered_from!(AmbientFuncExprId, AmbientFuncExpr);
ordered_from!(MemberFuncExprId, MemberFuncExpr);

impl From<OrderedNodeId> for NodeId {
    fn from(id: OrderedNodeId) -> NodeId {
        match id {
            OrderedNodeId::ArgDecl(i) => i.into(),
            OrderedNodeId::ArgDeclList(i) => i.into(),
            OrderedNodeId::Stmt(i) => i.into(),
            OrderedNodeId::IfStmt(i) => i.into(),
            OrderedNodeId::ThenStmt(i) => i.into(),
            OrderedNodeId::BranchStmt(i) => i.into(),
            OrderedNodeId::MatchStmt(i) => i.into(),
            OrderedNodeId::MatchCase(i) => i.into(),
            OrderedNodeId::IfAtom(i) => i.into(),
            OrderedNodeId::ThenAtom(i) => i.into(),
            OrderedNodeId::EqualAtom(i) => i.into(),
            OrderedNodeId::PredAtom(i) => i.into(),
            OrderedNodeId::DefinedIfAtom(i) => i.into(),
            OrderedNodeId::VarIfAtom(i) => i.into(),
            OrderedNodeId::DefinedThenAtom(i) => i.into(),
            OrderedNodeId::Term(i) => i.into(),
            OrderedNodeId::VarTerm(i) => i.into(),
            OrderedNodeId::AppTerm(i) => i.into(),
            OrderedNodeId::DomTerm(i) => i.into(),
            OrderedNodeId::CodTerm(i) => i.into(),
            OrderedNodeId::MorAppTerm(i) => i.into(),
            OrderedNodeId::TermList(i) => i.into(),
            OrderedNodeId::TypeExpr(i) => i.into(),
            OrderedNodeId::AmbientTypeExpr(i) => i.into(),
            OrderedNodeId::MemberTypeExpr(i) => i.into(),
            OrderedNodeId::MorTypeExpr(i) => i.into(),
            OrderedNodeId::PredExpr(i) => i.into(),
            OrderedNodeId::AmbientPredExpr(i) => i.into(),
            OrderedNodeId::MemberPredExpr(i) => i.into(),
            OrderedNodeId::FuncExpr(i) => i.into(),
            OrderedNodeId::AmbientFuncExpr(i) => i.into(),
            OrderedNodeId::MemberFuncExpr(i) => i.into(),
        }
    }
}

#[derive(Clone, Debug, Default)]
#[allow(dead_code)]
pub struct Scopes {
    scopes: Vec<Scope>,
    flat: BTreeMap<NodeId, ScopeId>,
    entry: BTreeMap<NodeId, ScopeId>,
    exit: BTreeMap<NodeId, ScopeId>,
}

#[allow(dead_code)]
impl Scopes {
    pub fn scope(&self, id: ScopeId) -> &Scope {
        &self.scopes[id.0]
    }

    pub fn flat(&self, id: impl Into<UnorderedNodeId>) -> ScopeId {
        let unordered: UnorderedNodeId = id.into();
        let node: NodeId = unordered.into();
        *self
            .flat
            .get(&node)
            .expect("flat scope was not populated for node")
    }

    pub fn entry(&self, id: impl Into<OrderedNodeId>) -> ScopeId {
        let ordered: OrderedNodeId = id.into();
        let node: NodeId = ordered.into();
        *self
            .entry
            .get(&node)
            .expect("entry scope was not populated for node")
    }

    pub fn exit(&self, id: impl Into<OrderedNodeId>) -> ScopeId {
        let ordered: OrderedNodeId = id.into();
        let node: NodeId = ordered.into();
        *self
            .exit
            .get(&node)
            .expect("exit scope was not populated for node")
    }

    pub fn lookup(&self, scope: ScopeId, name: &str) -> Option<Symbol> {
        let mut cur = Some(scope);
        while let Some(id) = cur {
            let s = &self.scopes[id.0];
            if let Some(sym) = s.symbols.get(name) {
                return Some(*sym);
            }
            cur = s.parent;
        }
        None
    }
}

/// Builds scopes for `ast` rooted at `module`.
///
/// Returns the populated [`Scopes`] along with any errors detected during the
/// pass. Errors do not abort population; the scope graph is always fully
/// populated.
pub fn resolve_scopes(ast: &Ast, module: ModuleId) -> (Scopes, Vec<CompileError>) {
    let mut builder = ScopeBuilder {
        ast,
        scopes: Vec::new(),
        flat: BTreeMap::new(),
        entry: BTreeMap::new(),
        exit: BTreeMap::new(),
        errors: Vec::new(),
    };
    let module_scope = builder.new_scope(None);
    builder
        .flat
        .insert(NodeId::from(UnorderedNodeId::from(module)), module_scope);
    let decls = ast.module(module).decls.clone();
    builder.populate_flat(module_scope, &decls);
    let ScopeBuilder {
        scopes,
        flat,
        entry,
        exit,
        errors,
        ..
    } = builder;
    (
        Scopes {
            scopes,
            flat,
            entry,
            exit,
        },
        errors,
    )
}

struct ScopeBuilder<'a> {
    ast: &'a Ast,
    scopes: Vec<Scope>,
    flat: BTreeMap<NodeId, ScopeId>,
    entry: BTreeMap<NodeId, ScopeId>,
    exit: BTreeMap<NodeId, ScopeId>,
    errors: Vec<CompileError>,
}

fn symbol_location(ast: &Ast, sym: Symbol) -> Location {
    match sym {
        Symbol::Type(id) => ast.loc(id),
        Symbol::Pred(id) => ast.loc(id),
        Symbol::Func(id) => ast.loc(id),
        Symbol::Enum(id) => ast.loc(id),
        Symbol::Ctor(id) => ast.loc(id),
        Symbol::Model(id) => ast.loc(id),
        Symbol::Rule(id) => ast.loc(id),
        Symbol::Arg(id) => ast.loc(id),
        Symbol::Var(id) => ast.loc(id),
    }
}

impl<'a> ScopeBuilder<'a> {
    fn new_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope {
            parent,
            symbols: BTreeMap::new(),
        });
        id
    }

    fn insert_flat<I: Into<UnorderedNodeId>>(&mut self, id: I, scope: ScopeId) {
        let node: NodeId = id.into().into();
        self.flat.insert(node, scope);
    }

    fn insert_entry<I: Into<OrderedNodeId>>(&mut self, id: I, scope: ScopeId) {
        let node: NodeId = id.into().into();
        self.entry.insert(node, scope);
    }

    fn insert_exit<I: Into<OrderedNodeId>>(&mut self, id: I, scope: ScopeId) {
        let node: NodeId = id.into().into();
        self.exit.insert(node, scope);
    }

    /// Insert a decl-level symbol into `scope`, or emit [`CompileError::SymbolDeclaredTwice`].
    fn insert_decl_symbol(&mut self, scope: ScopeId, name: &str, sym: Symbol) {
        let second_declaration = symbol_location(self.ast, sym);
        if let Some(existing) = self.scopes[scope.0].symbols.get(name).copied() {
            let first_declaration = symbol_location(self.ast, existing);
            self.errors.push(CompileError::SymbolDeclaredTwice {
                name: name.to_string(),
                first_declaration,
                second_declaration,
            });
            return;
        }
        self.scopes[scope.0].symbols.insert(name.to_string(), sym);
    }

    /// Populate `scope` with the symbols directly declared in `decls`, then
    /// dispatch children that own further scopes (model bodies) or switch to
    /// ordered scoping (rule bodies, arg lists).
    fn populate_flat(&mut self, scope: ScopeId, decls: &[DeclId]) {
        // Pass A: finalize `scope`.
        for decl in decls {
            self.insert_flat(*decl, scope);
            match *self.ast.decl(*decl) {
                Decl::Type(id) => {
                    self.insert_flat(id, scope);
                    let name = self.ast.type_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &name, Symbol::Type(id));
                }
                Decl::Pred(id) => {
                    self.insert_flat(id, scope);
                    let name = self.ast.pred_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &name, Symbol::Pred(id));
                }
                Decl::Func(id) => {
                    self.insert_flat(id, scope);
                    let name = self.ast.func_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &name, Symbol::Func(id));
                }
                Decl::Rule(id) => {
                    self.insert_flat(id, scope);
                    if let Some(name) = self.ast.rule_decl(id).name.clone() {
                        self.insert_decl_symbol(scope, &name, Symbol::Rule(id));
                    }
                }
                Decl::Enum(id) => {
                    self.insert_flat(id, scope);
                    let enum_name = self.ast.enum_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &enum_name, Symbol::Enum(id));
                    let ctors = self.ast.enum_decl(id).ctors.clone();
                    for ctor in &ctors {
                        self.insert_flat(*ctor, scope);
                        let ctor_name = self.ast.ctor_decl(*ctor).name.clone();
                        self.insert_decl_symbol(scope, &ctor_name, Symbol::Ctor(*ctor));
                    }
                }
                Decl::Model(id) => {
                    let model_name = self.ast.model_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &model_name, Symbol::Model(id));
                    // The model node itself maps to its own body scope,
                    // allocated below in pass B.
                }
            }
        }

        // Pass B: dispatch children against the now-finalized `scope`.
        for decl in decls {
            match *self.ast.decl(*decl) {
                Decl::Type(_) => {}
                Decl::Pred(id) => {
                    let args = self.ast.pred_decl(id).args;
                    self.walk_arg_decl_list(scope, args);
                }
                Decl::Func(id) => {
                    let FuncDecl { args, result, .. } = *self.ast.func_decl(id);
                    let after_args = self.walk_arg_decl_list(scope, args);
                    self.walk_type_expr(after_args, result);
                }
                Decl::Rule(id) => {
                    let body = self.ast.rule_decl(id).body.clone();
                    self.walk_stmt_block(scope, &body);
                }
                Decl::Enum(id) => {
                    let ctors = self.ast.enum_decl(id).ctors.clone();
                    for ctor in &ctors {
                        let args = self.ast.ctor_decl(*ctor).args;
                        self.walk_arg_decl_list(scope, args);
                    }
                }
                Decl::Model(id) => {
                    let body = self.ast.model_decl(id).body.clone();
                    let body_scope = self.new_scope(Some(scope));
                    self.insert_flat(id, body_scope);
                    self.populate_flat(body_scope, &body);
                }
            }
        }
    }

    fn walk_arg_decl_list(&mut self, current: ScopeId, list: ArgDeclListId) -> ScopeId {
        self.insert_entry(list, current);
        let args = self.ast.arg_decl_list(list).args.clone();
        let mut cur = current;
        for arg in &args {
            cur = self.walk_arg_decl(cur, *arg);
        }
        self.insert_exit(list, cur);
        cur
    }

    fn walk_arg_decl(&mut self, current: ScopeId, arg: ArgDeclId) -> ScopeId {
        self.insert_entry(arg, current);
        let ArgDecl { name, typ } = self.ast.arg_decl(arg);
        let name = name.clone();
        let typ = *typ;
        let after_type = self.walk_type_expr(current, typ);
        let exit = match name {
            Some(arg_name) => {
                let new_scope = self.new_scope(Some(after_type));
                self.scopes[new_scope.0]
                    .symbols
                    .insert(arg_name, Symbol::Arg(arg));
                new_scope
            }
            None => after_type,
        };
        self.insert_exit(arg, exit);
        exit
    }

    fn walk_stmt_block(&mut self, enclosing: ScopeId, stmts: &[StmtId]) -> ScopeId {
        let mut cur = enclosing;
        for stmt in stmts {
            cur = self.walk_stmt(cur, *stmt);
        }
        cur
    }

    fn walk_stmt(&mut self, current: ScopeId, stmt: StmtId) -> ScopeId {
        self.insert_entry(stmt, current);
        let exit = match *self.ast.stmt(stmt) {
            Stmt::If(id) => {
                self.insert_entry(id, current);
                let atom = self.ast.if_stmt(id).atom;
                let after = self.walk_if_atom(current, atom);
                self.insert_exit(id, after);
                after
            }
            Stmt::Then(id) => {
                self.insert_entry(id, current);
                let atom = self.ast.then_stmt(id).atom;
                let after = self.walk_then_atom(current, atom);
                self.insert_exit(id, after);
                after
            }
            Stmt::Branch(id) => {
                self.insert_entry(id, current);
                let blocks = self.ast.branch_stmt(id).blocks.clone();
                for block in &blocks {
                    self.walk_stmt_block(current, block);
                }
                self.insert_exit(id, current);
                current
            }
            Stmt::Match(id) => {
                self.insert_entry(id, current);
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                let after_term = self.walk_term(current, term);
                for case in &cases {
                    self.walk_match_case(after_term, *case);
                }
                self.insert_exit(id, after_term);
                after_term
            }
        };
        self.insert_exit(stmt, exit);
        exit
    }

    fn walk_match_case(&mut self, enclosing: ScopeId, case: MatchCaseId) -> ScopeId {
        self.insert_entry(case, enclosing);
        let MatchCase { pattern, body } = self.ast.match_case(case);
        let pattern = *pattern;
        let body = body.clone();
        let after_pattern = self.walk_term(enclosing, pattern);
        self.walk_stmt_block(after_pattern, &body);
        self.insert_exit(case, enclosing);
        enclosing
    }

    fn walk_if_atom(&mut self, current: ScopeId, atom: IfAtomId) -> ScopeId {
        self.insert_entry(atom, current);
        let exit = match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                self.insert_entry(id, current);
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let after_lhs = self.walk_term(current, lhs);
                let after_rhs = self.walk_term(after_lhs, rhs);
                self.insert_exit(id, after_rhs);
                after_rhs
            }
            IfAtom::Defined(id) => {
                self.insert_entry(id, current);
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                let after = self.walk_term(current, term);
                self.insert_exit(id, after);
                after
            }
            IfAtom::Pred(id) => {
                self.insert_entry(id, current);
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                let after_pred = self.walk_pred_expr(current, pred);
                let after_args = self.walk_term_list(after_pred, args);
                self.insert_exit(id, after_args);
                after_args
            }
            IfAtom::Var(id) => {
                self.insert_entry(id, current);
                let VarIfAtom { term, typ } = *self.ast.var_if_atom(id);
                // The type expression is walked before the bound term so that
                // the variable being introduced is not in scope within its
                // own type annotation.
                let after_type = self.walk_type_expr(current, typ);
                let after_term = self.walk_term(after_type, term);
                self.insert_exit(id, after_term);
                after_term
            }
        };
        self.insert_exit(atom, exit);
        exit
    }

    fn walk_then_atom(&mut self, current: ScopeId, atom: ThenAtomId) -> ScopeId {
        self.insert_entry(atom, current);
        let exit = match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                self.insert_entry(id, current);
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let after_lhs = self.walk_term(current, lhs);
                let after_rhs = self.walk_term(after_lhs, rhs);
                self.insert_exit(id, after_rhs);
                after_rhs
            }
            ThenAtom::Defined(id) => {
                self.insert_entry(id, current);
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                let after_var = match var {
                    Some(var_term) => self.walk_term(current, var_term),
                    None => current,
                };
                let after_term = self.walk_term(after_var, term);
                self.insert_exit(id, after_term);
                after_term
            }
            ThenAtom::Pred(id) => {
                self.insert_entry(id, current);
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                let after_pred = self.walk_pred_expr(current, pred);
                let after_args = self.walk_term_list(after_pred, args);
                self.insert_exit(id, after_args);
                after_args
            }
        };
        self.insert_exit(atom, exit);
        exit
    }

    fn walk_term(&mut self, current: ScopeId, term: TermId) -> ScopeId {
        self.insert_entry(term, current);
        let exit = match *self.ast.term(term) {
            Term::Var(id) => {
                self.insert_entry(id, current);
                let name = self.ast.var_term(id).name.clone();
                let new_scope = self.new_scope(Some(current));
                self.scopes[new_scope.0]
                    .symbols
                    .insert(name, Symbol::Var(id));
                self.insert_exit(id, new_scope);
                new_scope
            }
            Term::Wildcard => current,
            Term::App(id) => {
                self.insert_entry(id, current);
                let AppTerm { func, args } = *self.ast.app_term(id);
                let after_func = self.walk_func_expr(current, func);
                let after_args = self.walk_term_list(after_func, args);
                self.insert_exit(id, after_args);
                after_args
            }
            Term::Dom(id) => {
                self.insert_entry(id, current);
                let DomTerm { arg } = *self.ast.dom_term(id);
                let after = self.walk_term(current, arg);
                self.insert_exit(id, after);
                after
            }
            Term::Cod(id) => {
                self.insert_entry(id, current);
                let CodTerm { arg } = *self.ast.cod_term(id);
                let after = self.walk_term(current, arg);
                self.insert_exit(id, after);
                after
            }
            Term::MorApp(id) => {
                self.insert_entry(id, current);
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                let after_mor = self.walk_term(current, mor);
                let after_arg = self.walk_term(after_mor, arg);
                self.insert_exit(id, after_arg);
                after_arg
            }
        };
        self.insert_exit(term, exit);
        exit
    }

    fn walk_term_list(&mut self, current: ScopeId, list: TermListId) -> ScopeId {
        self.insert_entry(list, current);
        let terms = self.ast.term_list(list).terms.clone();
        let mut cur = current;
        for term in &terms {
            cur = self.walk_term(cur, *term);
        }
        self.insert_exit(list, cur);
        cur
    }

    fn walk_type_expr(&mut self, current: ScopeId, type_expr: TypeExprId) -> ScopeId {
        self.insert_entry(type_expr, current);
        let exit = match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                self.insert_entry(id, current);
                self.insert_exit(id, current);
                current
            }
            TypeExpr::Member(id) => {
                self.insert_entry(id, current);
                let MemberTypeExpr { term, .. } = self.ast.member_type_expr(id);
                let term = *term;
                let after = self.walk_term(current, term);
                self.insert_exit(id, after);
                after
            }
            TypeExpr::Mor(id) => {
                self.insert_entry(id, current);
                self.insert_exit(id, current);
                current
            }
        };
        self.insert_exit(type_expr, exit);
        exit
    }

    fn walk_pred_expr(&mut self, current: ScopeId, pred_expr: PredExprId) -> ScopeId {
        self.insert_entry(pred_expr, current);
        let exit = match *self.ast.pred_expr(pred_expr) {
            PredExpr::Ambient(id) => {
                self.insert_entry(id, current);
                self.insert_exit(id, current);
                current
            }
            PredExpr::Member(id) => {
                self.insert_entry(id, current);
                let MemberPredExpr { term, .. } = self.ast.member_pred_expr(id);
                let term = *term;
                let after = self.walk_term(current, term);
                self.insert_exit(id, after);
                after
            }
        };
        self.insert_exit(pred_expr, exit);
        exit
    }

    fn walk_func_expr(&mut self, current: ScopeId, func_expr: FuncExprId) -> ScopeId {
        self.insert_entry(func_expr, current);
        let exit = match *self.ast.func_expr(func_expr) {
            FuncExpr::Ambient(id) => {
                self.insert_entry(id, current);
                self.insert_exit(id, current);
                current
            }
            FuncExpr::Member(id) => {
                self.insert_entry(id, current);
                let MemberFuncExpr { term, .. } = self.ast.member_func_expr(id);
                let term = *term;
                let after = self.walk_term(current, term);
                self.insert_exit(id, after);
                after
            }
        };
        self.insert_exit(func_expr, exit);
        exit
    }
}
