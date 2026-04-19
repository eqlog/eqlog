//! Scope resolution pass. See [`resolve_scopes`] for the entry point.

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedNodeId(NodeId);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OrderedNodeId(NodeId);

impl From<UnorderedNodeId> for NodeId {
    fn from(id: UnorderedNodeId) -> NodeId {
        id.0
    }
}

impl From<OrderedNodeId> for NodeId {
    fn from(id: OrderedNodeId) -> NodeId {
        id.0
    }
}

macro_rules! unordered_from {
    ($id:ty) => {
        impl From<$id> for UnorderedNodeId {
            fn from(id: $id) -> UnorderedNodeId {
                UnorderedNodeId(id.into())
            }
        }
    };
}

unordered_from!(ModuleId);
unordered_from!(DeclId);
unordered_from!(TypeDeclId);
unordered_from!(PredDeclId);
unordered_from!(FuncDeclId);
unordered_from!(EnumDeclId);
unordered_from!(CtorDeclId);
unordered_from!(ModelDeclId);
unordered_from!(RuleDeclId);

macro_rules! ordered_from {
    ($id:ty) => {
        impl From<$id> for OrderedNodeId {
            fn from(id: $id) -> OrderedNodeId {
                OrderedNodeId(id.into())
            }
        }
    };
}

ordered_from!(ArgDeclId);
ordered_from!(ArgDeclListId);
ordered_from!(StmtId);
ordered_from!(IfStmtId);
ordered_from!(ThenStmtId);
ordered_from!(BranchStmtId);
ordered_from!(MatchStmtId);
ordered_from!(MatchCaseId);
ordered_from!(IfAtomId);
ordered_from!(ThenAtomId);
ordered_from!(EqualAtomId);
ordered_from!(PredAtomId);
ordered_from!(DefinedIfAtomId);
ordered_from!(VarIfAtomId);
ordered_from!(DefinedThenAtomId);
ordered_from!(TermId);
ordered_from!(VarTermId);
ordered_from!(AppTermId);
ordered_from!(DomTermId);
ordered_from!(CodTermId);
ordered_from!(MorAppTermId);
ordered_from!(TermListId);
ordered_from!(TypeExprId);
ordered_from!(AmbientTypeExprId);
ordered_from!(MemberTypeExprId);
ordered_from!(MorTypeExprId);
ordered_from!(PredExprId);
ordered_from!(AmbientPredExprId);
ordered_from!(MemberPredExprId);
ordered_from!(FuncExprId);
ordered_from!(AmbientFuncExprId);
ordered_from!(MemberFuncExprId);

/// A graph of [`Scope`]s keyed by AST node, with `parent` pointers for
/// ancestor lookup.
///
/// Two side tables are maintained depending on the scoping discipline of the
/// node:
///
/// * Unordered nodes (modules, models, decls): a single [`ScopeId`] via
///   [`Scopes::unordered`]. Declaration order within an unordered scope does
///   not affect which names are visible.
/// * Ordered nodes (rule-body descendants and arg-list descendants): an
///   [`OrderedScopes`] via [`Scopes::ordered`] giving the entry and exit
///   scopes of the node. Sibling nodes chain so that names bound in an
///   earlier sibling are visible in a later one.
///
/// Every variable term occurrence and every named arg declaration extends
/// the current scope with a fresh child scope that contains the
/// corresponding [`Symbol`]. [`Scopes::lookup`] walks the `parent` chain, so
/// later occurrences shadow earlier ones, and ambient global symbols are
/// reachable from the innermost scope via the chain out into the surrounding
/// unordered scope.
#[derive(Clone, Debug, Default)]
#[allow(dead_code)]
pub struct Scopes {
    scopes: Vec<Scope>,
    unordered: BTreeMap<UnorderedNodeId, ScopeId>,
    ordered: BTreeMap<OrderedNodeId, OrderedScopes>,
}

/// The entry and exit scopes of an ordered AST node.
///
/// `entry` is the scope visible immediately before the node's subtree, and
/// `exit` is the scope that follows it (possibly extended with bindings
/// introduced by the subtree).
#[derive(Copy, Clone, Debug)]
pub struct OrderedScopes {
    pub entry: ScopeId,
    pub exit: ScopeId,
}

#[allow(dead_code)]
impl Scopes {
    pub fn scope(&self, id: ScopeId) -> &Scope {
        &self.scopes[id.0]
    }

    pub fn unordered(&self, id: impl Into<UnorderedNodeId>) -> ScopeId {
        *self
            .unordered
            .get(&id.into())
            .expect("unordered scope was not populated for node")
    }

    pub fn ordered(&self, id: impl Into<OrderedNodeId>) -> OrderedScopes {
        *self
            .ordered
            .get(&id.into())
            .expect("ordered scopes were not populated for node")
    }

    pub fn entry(&self, id: impl Into<OrderedNodeId>) -> ScopeId {
        self.ordered(id).entry
    }

    pub fn exit(&self, id: impl Into<OrderedNodeId>) -> ScopeId {
        self.ordered(id).exit
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
        unordered: BTreeMap::new(),
        ordered: BTreeMap::new(),
        errors: Vec::new(),
    };
    let module_scope = builder.new_scope(None);
    builder
        .unordered
        .insert(UnorderedNodeId::from(module), module_scope);
    let decls = ast.module(module).decls.clone();
    builder.populate_unordered(module_scope, &decls);
    let ScopeBuilder {
        scopes,
        unordered,
        ordered,
        errors,
        ..
    } = builder;
    (
        Scopes {
            scopes,
            unordered,
            ordered,
        },
        errors,
    )
}

struct ScopeBuilder<'a> {
    ast: &'a Ast,
    scopes: Vec<Scope>,
    unordered: BTreeMap<UnorderedNodeId, ScopeId>,
    ordered: BTreeMap<OrderedNodeId, OrderedScopes>,
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

    fn insert_unordered<I: Into<UnorderedNodeId>>(&mut self, id: I, scope: ScopeId) {
        self.unordered.insert(id.into(), scope);
    }

    fn insert_ordered<I: Into<OrderedNodeId>>(&mut self, id: I, entry: ScopeId, exit: ScopeId) {
        self.ordered
            .insert(id.into(), OrderedScopes { entry, exit });
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
    fn populate_unordered(&mut self, scope: ScopeId, decls: &[DeclId]) {
        // Pass A: finalize `scope`.
        for decl in decls {
            self.insert_unordered(*decl, scope);
            match *self.ast.decl(*decl) {
                Decl::Type(id) => {
                    self.insert_unordered(id, scope);
                    let name = self.ast.type_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &name, Symbol::Type(id));
                }
                Decl::Pred(id) => {
                    self.insert_unordered(id, scope);
                    let name = self.ast.pred_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &name, Symbol::Pred(id));
                }
                Decl::Func(id) => {
                    self.insert_unordered(id, scope);
                    let name = self.ast.func_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &name, Symbol::Func(id));
                }
                Decl::Rule(id) => {
                    self.insert_unordered(id, scope);
                    if let Some(name) = self.ast.rule_decl(id).name.clone() {
                        self.insert_decl_symbol(scope, &name, Symbol::Rule(id));
                    }
                }
                Decl::Enum(id) => {
                    self.insert_unordered(id, scope);
                    let enum_name = self.ast.enum_decl(id).name.clone();
                    self.insert_decl_symbol(scope, &enum_name, Symbol::Enum(id));
                    let ctors = self.ast.enum_decl(id).ctors.clone();
                    for ctor in &ctors {
                        self.insert_unordered(*ctor, scope);
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
                    self.insert_unordered(id, body_scope);
                    self.populate_unordered(body_scope, &body);
                }
            }
        }
    }

    fn walk_arg_decl_list(&mut self, current: ScopeId, list: ArgDeclListId) -> ScopeId {
        let args = self.ast.arg_decl_list(list).args.clone();
        let mut cur = current;
        for arg in &args {
            cur = self.walk_arg_decl(cur, *arg);
        }
        self.insert_ordered(list, current, cur);
        cur
    }

    fn walk_arg_decl(&mut self, current: ScopeId, arg: ArgDeclId) -> ScopeId {
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
        self.insert_ordered(arg, current, exit);
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
        let exit = match *self.ast.stmt(stmt) {
            Stmt::If(id) => {
                let atom = self.ast.if_stmt(id).atom;
                let after = self.walk_if_atom(current, atom);
                self.insert_ordered(id, current, after);
                after
            }
            Stmt::Then(id) => {
                let atom = self.ast.then_stmt(id).atom;
                let after = self.walk_then_atom(current, atom);
                self.insert_ordered(id, current, after);
                after
            }
            Stmt::Branch(id) => {
                let blocks = self.ast.branch_stmt(id).blocks.clone();
                for block in &blocks {
                    self.walk_stmt_block(current, block);
                }
                self.insert_ordered(id, current, current);
                current
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                let after_term = self.walk_term(current, term);
                for case in &cases {
                    self.walk_match_case(after_term, *case);
                }
                self.insert_ordered(id, current, after_term);
                after_term
            }
        };
        self.insert_ordered(stmt, current, exit);
        exit
    }

    fn walk_match_case(&mut self, enclosing: ScopeId, case: MatchCaseId) -> ScopeId {
        let MatchCase { pattern, body } = self.ast.match_case(case);
        let pattern = *pattern;
        let body = body.clone();
        let after_pattern = self.walk_term(enclosing, pattern);
        self.walk_stmt_block(after_pattern, &body);
        self.insert_ordered(case, enclosing, enclosing);
        enclosing
    }

    fn walk_if_atom(&mut self, current: ScopeId, atom: IfAtomId) -> ScopeId {
        let exit = match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let after_lhs = self.walk_term(current, lhs);
                let after_rhs = self.walk_term(after_lhs, rhs);
                self.insert_ordered(id, current, after_rhs);
                after_rhs
            }
            IfAtom::Defined(id) => {
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                let after = self.walk_term(current, term);
                self.insert_ordered(id, current, after);
                after
            }
            IfAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                let after_pred = self.walk_pred_expr(current, pred);
                let after_args = self.walk_term_list(after_pred, args);
                self.insert_ordered(id, current, after_args);
                after_args
            }
            IfAtom::Var(id) => {
                let VarIfAtom { term, typ } = *self.ast.var_if_atom(id);
                // The type expression is walked before the bound term so that
                // the variable being introduced is not in scope within its
                // own type annotation.
                let after_type = self.walk_type_expr(current, typ);
                let after_term = self.walk_term(after_type, term);
                self.insert_ordered(id, current, after_term);
                after_term
            }
        };
        self.insert_ordered(atom, current, exit);
        exit
    }

    fn walk_then_atom(&mut self, current: ScopeId, atom: ThenAtomId) -> ScopeId {
        let exit = match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let after_lhs = self.walk_term(current, lhs);
                let after_rhs = self.walk_term(after_lhs, rhs);
                self.insert_ordered(id, current, after_rhs);
                after_rhs
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                let after_var = match var {
                    Some(var_term) => self.walk_term(current, var_term),
                    None => current,
                };
                let after_term = self.walk_term(after_var, term);
                self.insert_ordered(id, current, after_term);
                after_term
            }
            ThenAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                let after_pred = self.walk_pred_expr(current, pred);
                let after_args = self.walk_term_list(after_pred, args);
                self.insert_ordered(id, current, after_args);
                after_args
            }
        };
        self.insert_ordered(atom, current, exit);
        exit
    }

    fn walk_term(&mut self, current: ScopeId, term: TermId) -> ScopeId {
        let exit = match *self.ast.term(term) {
            Term::Var(id) => {
                let name = self.ast.var_term(id).name.clone();
                let new_scope = self.new_scope(Some(current));
                self.scopes[new_scope.0]
                    .symbols
                    .insert(name, Symbol::Var(id));
                self.insert_ordered(id, current, new_scope);
                new_scope
            }
            Term::Wildcard => current,
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                let after_func = self.walk_func_expr(current, func);
                let after_args = self.walk_term_list(after_func, args);
                self.insert_ordered(id, current, after_args);
                after_args
            }
            Term::Dom(id) => {
                let DomTerm { arg } = *self.ast.dom_term(id);
                let after = self.walk_term(current, arg);
                self.insert_ordered(id, current, after);
                after
            }
            Term::Cod(id) => {
                let CodTerm { arg } = *self.ast.cod_term(id);
                let after = self.walk_term(current, arg);
                self.insert_ordered(id, current, after);
                after
            }
            Term::MorApp(id) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                let after_mor = self.walk_term(current, mor);
                let after_arg = self.walk_term(after_mor, arg);
                self.insert_ordered(id, current, after_arg);
                after_arg
            }
        };
        self.insert_ordered(term, current, exit);
        exit
    }

    fn walk_term_list(&mut self, current: ScopeId, list: TermListId) -> ScopeId {
        let terms = self.ast.term_list(list).terms.clone();
        let mut cur = current;
        for term in &terms {
            cur = self.walk_term(cur, *term);
        }
        self.insert_ordered(list, current, cur);
        cur
    }

    fn walk_type_expr(&mut self, current: ScopeId, type_expr: TypeExprId) -> ScopeId {
        let exit = match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                self.insert_ordered(id, current, current);
                current
            }
            TypeExpr::Member(id) => {
                let MemberTypeExpr { term, .. } = self.ast.member_type_expr(id);
                let term = *term;
                let after = self.walk_term(current, term);
                self.insert_ordered(id, current, after);
                after
            }
            TypeExpr::Mor(id) => {
                self.insert_ordered(id, current, current);
                current
            }
        };
        self.insert_ordered(type_expr, current, exit);
        exit
    }

    fn walk_pred_expr(&mut self, current: ScopeId, pred_expr: PredExprId) -> ScopeId {
        let exit = match *self.ast.pred_expr(pred_expr) {
            PredExpr::Ambient(id) => {
                self.insert_ordered(id, current, current);
                current
            }
            PredExpr::Member(id) => {
                let MemberPredExpr { term, .. } = self.ast.member_pred_expr(id);
                let term = *term;
                let after = self.walk_term(current, term);
                self.insert_ordered(id, current, after);
                after
            }
        };
        self.insert_ordered(pred_expr, current, exit);
        exit
    }

    fn walk_func_expr(&mut self, current: ScopeId, func_expr: FuncExprId) -> ScopeId {
        let exit = match *self.ast.func_expr(func_expr) {
            FuncExpr::Ambient(id) => {
                self.insert_ordered(id, current, current);
                current
            }
            FuncExpr::Member(id) => {
                let MemberFuncExpr { term, .. } = self.ast.member_func_expr(id);
                let term = *term;
                let after = self.walk_term(current, term);
                self.insert_ordered(id, current, after);
                after
            }
        };
        self.insert_ordered(func_expr, current, exit);
        exit
    }
}
