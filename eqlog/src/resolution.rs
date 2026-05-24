//! Declaration scope and rule-body name resolution.
//!
//! [`resolve`] first builds declaration visibility with [`crate::scopes`],
//! then walks rule bodies in source order to decide whether every bare
//! identifier term denotes a local variable binding or a visible ambient
//! constant. Later passes consume this side table instead of re-checking
//! declaration scopes for identifier terms.

use std::collections::BTreeMap;

use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::{resolve_scopes, OrderedNodeId, Scopes, Symbol};

#[derive(Clone, Debug)]
pub struct Resolution {
    pub scopes: Scopes,
    pub names: NameResolution,
}

#[derive(Clone, Debug, Default)]
pub struct NameResolution {
    pub ident_terms: BTreeMap<IdentTermId, ResolvedIdentTerm>,
    var_bindings: Vec<String>,
    entries: BTreeMap<OrderedNodeId, VariableScope>,
    exits: BTreeMap<OrderedNodeId, VariableScope>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ResolvedIdentTerm {
    Var(VarBindingId),
    AmbientConst(ConstDeclId),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarBindingId(usize);

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VariableScope {
    bindings: Vec<(String, VarBindingId)>,
}

impl NameResolution {
    pub fn resolved_ident(&self, id: IdentTermId) -> ResolvedIdentTerm {
        *self
            .ident_terms
            .get(&id)
            .expect("identifier term was not resolved")
    }

    pub fn binding_name(&self, id: VarBindingId) -> &str {
        &self.var_bindings[id.0]
    }

    pub fn entry(&self, id: impl Into<OrderedNodeId>) -> &VariableScope {
        self.entries
            .get(&id.into())
            .expect("name-resolution entry scope was not populated for node")
    }

    #[allow(dead_code)]
    pub fn exit(&self, id: impl Into<OrderedNodeId>) -> &VariableScope {
        self.exits
            .get(&id.into())
            .expect("name-resolution exit scope was not populated for node")
    }
}

impl VariableScope {
    pub fn lookup(&self, name: &str) -> Option<VarBindingId> {
        self.bindings
            .iter()
            .rev()
            .find_map(|(n, id)| (n == name).then_some(*id))
    }

    fn insert(&mut self, name: String, binding: VarBindingId) {
        self.bindings.push((name, binding));
    }
}

pub fn resolve(ast: &Ast, module: ModuleId) -> Result<Resolution, CompileError> {
    let scopes = resolve_scopes(ast, module)?;
    let mut resolver = Resolver {
        ast,
        scopes: &scopes,
        names: NameResolution::default(),
    };
    resolver.walk_module(module);
    let names = resolver.names;
    Ok(Resolution { scopes, names })
}

struct Resolver<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
    names: NameResolution,
}

impl<'a> Resolver<'a> {
    fn walk_module(&mut self, module: ModuleId) {
        for decl in self.ast.module(module).decls.clone() {
            self.walk_decl(decl);
        }
    }

    fn walk_decl(&mut self, decl: DeclId) {
        match *self.ast.decl(decl) {
            Decl::Rule(id) => {
                let body = self.ast.rule_decl(id).body.clone();
                self.walk_stmt_block(VariableScope::default(), &body);
            }
            Decl::Model(id) => {
                for child in self.ast.model_decl(id).body.clone() {
                    self.walk_decl(child);
                }
            }
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Const(_) | Decl::Enum(_) => {}
        }
    }

    fn insert_ordered<I: Into<OrderedNodeId>>(
        &mut self,
        id: I,
        entry: VariableScope,
        exit: VariableScope,
    ) {
        let id = id.into();
        self.names.entries.insert(id, entry);
        self.names.exits.insert(id, exit);
    }

    fn push_binding(&mut self, name: String) -> VarBindingId {
        let id = VarBindingId(self.names.var_bindings.len());
        self.names.var_bindings.push(name);
        id
    }

    fn walk_stmt_block(&mut self, mut current: VariableScope, stmts: &[StmtId]) -> VariableScope {
        for stmt in stmts {
            current = self.walk_stmt(current, *stmt);
        }
        current
    }

    fn walk_stmt(&mut self, current: VariableScope, stmt: StmtId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.stmt(stmt) {
            Stmt::If(id) => {
                let atom = self.ast.if_stmt(id).atom;
                let after = self.walk_if_atom(current.clone(), atom);
                self.insert_ordered(id, current, after.clone());
                after
            }
            Stmt::Then(id) => {
                let atom = self.ast.then_stmt(id).atom;
                let after = self.walk_then_atom(current.clone(), atom);
                self.insert_ordered(id, current, after.clone());
                after
            }
            Stmt::Branch(id) => {
                for block in self.ast.branch_stmt(id).blocks.clone() {
                    self.walk_stmt_block(current.clone(), &block);
                }
                self.insert_ordered(id, current.clone(), current.clone());
                current
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                let after_term = self.walk_term(current.clone(), term);
                for case in cases {
                    self.walk_match_case(after_term.clone(), case);
                }
                self.insert_ordered(id, current, after_term.clone());
                after_term
            }
        };
        self.insert_ordered(stmt, entry, exit.clone());
        exit
    }

    fn walk_match_case(&mut self, current: VariableScope, case: MatchCaseId) -> VariableScope {
        let MatchCase { pattern, body } = self.ast.match_case(case);
        let pattern = *pattern;
        let body = body.clone();
        let after_pattern = self.walk_term(current.clone(), pattern);
        self.walk_stmt_block(after_pattern, &body);
        self.insert_ordered(case, current.clone(), current.clone());
        current
    }

    fn walk_if_atom(&mut self, current: VariableScope, atom: IfAtomId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let after_lhs = self.walk_term(current.clone(), lhs);
                let after_rhs = self.walk_term(after_lhs, rhs);
                self.insert_ordered(id, current, after_rhs.clone());
                after_rhs
            }
            IfAtom::Defined(id) => {
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                let after = self.walk_term(current.clone(), term);
                self.insert_ordered(id, current, after.clone());
                after
            }
            IfAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                let after_pred = self.walk_pred_expr(current.clone(), pred);
                let after_args = self.walk_term_list(after_pred, args);
                self.insert_ordered(id, current, after_args.clone());
                after_args
            }
            IfAtom::Var(id) => {
                let VarIfAtom { term, typ } = *self.ast.var_if_atom(id);
                // The annotation is resolved before the variable term so the
                // introduced variable is not visible inside its own type.
                let after_type = self.walk_type_expr(current.clone(), typ);
                let after_var = self.resolve_if_var_ref_or_create(after_type, term);
                self.insert_ordered(id, current, after_var.clone());
                after_var
            }
        };
        self.insert_ordered(atom, entry, exit.clone());
        exit
    }

    fn walk_then_atom(&mut self, current: VariableScope, atom: ThenAtomId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let after_lhs = self.walk_term(current.clone(), lhs);
                let after_rhs = self.walk_term(after_lhs, rhs);
                self.insert_ordered(id, current, after_rhs.clone());
                after_rhs
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                let after_term = self.walk_term(current.clone(), term);
                let exit = match var {
                    Some(var) => self.resolve_then_defined_var(current.clone(), after_term, var),
                    None => after_term,
                };
                self.insert_ordered(id, current, exit.clone());
                exit
            }
            ThenAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                let after_pred = self.walk_pred_expr(current.clone(), pred);
                let after_args = self.walk_term_list(after_pred, args);
                self.insert_ordered(id, current, after_args.clone());
                after_args
            }
        };
        self.insert_ordered(atom, entry, exit.clone());
        exit
    }

    fn walk_term(&mut self, current: VariableScope, term: TermId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.term(term) {
            Term::Ident(id) => {
                let exit = self.resolve_ident_term(current.clone(), id);
                self.insert_ordered(id, current, exit.clone());
                exit
            }
            Term::Wildcard => current.clone(),
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                let after_func = self.walk_func_expr(current.clone(), func);
                let after_args = self.walk_term_list(after_func, args);
                self.insert_ordered(id, current, after_args.clone());
                after_args
            }
            Term::MemberConst(id) => {
                let MemberConstTerm { receiver, name } = *self.ast.member_const_term(id);
                let after_receiver = self.walk_term(current.clone(), receiver);
                self.insert_ordered(name, after_receiver.clone(), after_receiver.clone());
                self.insert_ordered(id, current, after_receiver.clone());
                after_receiver
            }
            Term::Dom(id) => {
                let DomTerm { arg } = *self.ast.dom_term(id);
                let after = self.walk_term(current.clone(), arg);
                self.insert_ordered(id, current, after.clone());
                after
            }
            Term::Cod(id) => {
                let CodTerm { arg } = *self.ast.cod_term(id);
                let after = self.walk_term(current.clone(), arg);
                self.insert_ordered(id, current, after.clone());
                after
            }
            Term::MorApp(id) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                let after_mor = self.walk_term(current.clone(), mor);
                let after_arg = self.walk_term(after_mor, arg);
                self.insert_ordered(id, current, after_arg.clone());
                after_arg
            }
        };
        self.insert_ordered(term, entry, exit.clone());
        exit
    }

    fn walk_term_list(&mut self, current: VariableScope, list: TermListId) -> VariableScope {
        let mut cur = current.clone();
        for term in self.ast.term_list(list).terms.clone() {
            cur = self.walk_term(cur, term);
        }
        self.insert_ordered(list, current, cur.clone());
        cur
    }

    fn walk_type_expr(&mut self, current: VariableScope, type_expr: TypeExprId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                self.insert_ordered(id, current.clone(), current.clone());
                current
            }
            TypeExpr::Member(id) => {
                let term = self.ast.member_type_expr(id).term;
                let after = self.walk_term(current.clone(), term);
                self.insert_ordered(id, current, after.clone());
                after
            }
            TypeExpr::Mor(id) => {
                self.insert_ordered(id, current.clone(), current.clone());
                current
            }
        };
        self.insert_ordered(type_expr, entry, exit.clone());
        exit
    }

    fn walk_pred_expr(&mut self, current: VariableScope, pred_expr: PredExprId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.pred_expr(pred_expr) {
            PredExpr::Ambient(id) => {
                self.insert_ordered(id, current.clone(), current.clone());
                current
            }
            PredExpr::Member(id) => {
                let term = self.ast.member_pred_expr(id).term;
                let after = self.walk_term(current.clone(), term);
                self.insert_ordered(id, current, after.clone());
                after
            }
        };
        self.insert_ordered(pred_expr, entry, exit.clone());
        exit
    }

    fn walk_func_expr(&mut self, current: VariableScope, func_expr: FuncExprId) -> VariableScope {
        let entry = current.clone();
        let exit = match *self.ast.func_expr(func_expr) {
            FuncExpr::Ambient(id) => {
                self.insert_ordered(id, current.clone(), current.clone());
                current
            }
            FuncExpr::Member(id) => {
                let term = self.ast.member_func_expr(id).term;
                let after = self.walk_term(current.clone(), term);
                self.insert_ordered(id, current, after.clone());
                after
            }
        };
        self.insert_ordered(func_expr, entry, exit.clone());
        exit
    }

    fn resolve_ident_term(
        &mut self,
        mut current: VariableScope,
        ident: IdentTermId,
    ) -> VariableScope {
        let name = self.ast.ident_term(ident).name.clone();
        if let Some(binding) = current.lookup(&name) {
            self.names
                .ident_terms
                .insert(ident, ResolvedIdentTerm::Var(binding));
            return current;
        }

        let scope = self.scopes.entry(ident);
        if let Some(Symbol::Const(const_decl)) = self.scopes.lookup(scope, &name) {
            self.names
                .ident_terms
                .insert(ident, ResolvedIdentTerm::AmbientConst(const_decl));
            return current;
        }

        let binding = self.push_binding(name.clone());
        current.insert(name, binding);
        self.names
            .ident_terms
            .insert(ident, ResolvedIdentTerm::Var(binding));
        current
    }

    fn resolve_if_var_ref_or_create(
        &mut self,
        mut current: VariableScope,
        term: TermId,
    ) -> VariableScope {
        let entry = current.clone();
        match *self.ast.term(term) {
            Term::Ident(id) => {
                let ident_entry = current.clone();
                let name = self.ast.ident_term(id).name.clone();
                let binding = match current.lookup(&name) {
                    Some(binding) => binding,
                    None => {
                        let binding = self.push_binding(name.clone());
                        current.insert(name, binding);
                        binding
                    }
                };
                self.names
                    .ident_terms
                    .insert(id, ResolvedIdentTerm::Var(binding));
                self.insert_ordered(id, ident_entry, current.clone());
            }
            Term::Wildcard => {}
            Term::App(_) | Term::MemberConst(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
                unreachable!("if-var terms are checked by syntactic.rs")
            }
        }
        self.insert_ordered(term, entry, current.clone());
        current
    }

    fn resolve_then_defined_var(
        &mut self,
        before_term: VariableScope,
        mut after_term: VariableScope,
        term: TermId,
    ) -> VariableScope {
        let entry = after_term.clone();
        match *self.ast.term(term) {
            Term::Ident(id) => {
                let ident_entry = after_term.clone();
                let name = self.ast.ident_term(id).name.clone();
                let binding = match before_term.lookup(&name) {
                    Some(binding) => binding,
                    None => {
                        let binding = self.push_binding(name.clone());
                        after_term.insert(name, binding);
                        binding
                    }
                };
                self.names
                    .ident_terms
                    .insert(id, ResolvedIdentTerm::Var(binding));
                self.insert_ordered(id, ident_entry, after_term.clone());
            }
            Term::Wildcard => {}
            Term::App(_) | Term::MemberConst(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
                unreachable!("defined-then variable terms are checked by syntactic.rs")
            }
        }
        self.insert_ordered(term, entry, after_term.clone());
        after_term
    }
}
