//! Turns AST rule bodies into algebraic data.
//!
//! [`build_structures`] walks each rule body and assigns a before-structure
//! and an after-structure to every statement. The after-structure is produced
//! by cloning the before-structure and adding whatever the statement
//! contributes. Equality atoms and the `var := term` form of `then` defined
//! atoms are turned into calls to [`Structure::equate`]. Once a rule has
//! been walked in full, every structure it produced is closed in place via
//! [`Structure::close`] before moving on to the next rule.

use crate::algebra::signature::{Signature, TypeId};
use crate::algebra::structure::{ConcreteType, ElId, FuncApp, PredApp, Structure, Structures};
use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::{ScopeId, Scopes, Symbol};

/// Walks `ast` rooted at `module`, assigns a before-structure and an
/// after-structure to every statement in every rule, and closes each
/// structure. The accompanying errors collect every type conflict
/// discovered while closing.
pub fn build_structures(
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    module: ModuleId,
) -> (Structures, Vec<CompileError>) {
    let mut builder = Builder {
        ast,
        scopes,
        signature,
        structures: Structures::default(),
        errors: Vec::new(),
    };
    let decls = ast.module(module).decls.clone();
    builder.walk_decls(&decls, &[]);
    (builder.structures, builder.errors)
}

struct Builder<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
    signature: &'a Signature,
    structures: Structures,
    errors: Vec<CompileError>,
}

/// Per-rule state the stmt walker threads through recursive calls.
struct RuleState {
    /// Ambient model elements introduced by the rule's enclosing scopes,
    /// outermost first. Same length as the type parent chain. Used as the
    /// prefix for every El created in this rule and as the parents of any
    /// relation application we emit.
    ambient: Vec<ElId>,
}

impl<'a> Builder<'a> {
    fn walk_decls(&mut self, decls: &[DeclId], enclosing_models: &[TypeId]) {
        for decl in decls {
            match *self.ast.decl(*decl) {
                Decl::Rule(rid) => self.walk_rule(rid, enclosing_models),
                Decl::Model(mid) => {
                    let body = self.ast.model_decl(mid).body.clone();
                    let model_tid = self.signature.types_for_model_decl(mid).type_;
                    let mut nested = enclosing_models.to_vec();
                    nested.push(model_tid);
                    self.walk_decls(&body, &nested);
                }
                Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Enum(_) => {}
            }
        }
    }

    fn walk_rule(&mut self, rid: RuleDeclId, enclosing_models: &[TypeId]) {
        let start = self.structures.arena.len();

        let mut initial = Structure::default();
        let mut ambient: Vec<ElId> = Vec::new();
        for &model_tid in enclosing_models {
            let el_id = initial.push_el();
            initial.els.insert(
                el_id,
                Some(ConcreteType {
                    typ: model_tid,
                    parents: ambient.clone(),
                }),
            );
            ambient.push(el_id);
        }

        let initial_id = self.structures.push(initial.clone());
        self.structures.rule_initial.insert(rid, initial_id);

        let body = self.ast.rule_decl(rid).body.clone();
        let mut state = RuleState { ambient };
        self.walk_stmt_block(&body, initial, &mut state);

        // Close every structure that belongs to this rule before moving on.
        let end = self.structures.arena.len();
        for i in start..end {
            self.structures.arena[i].close(self.signature, self.ast, &mut self.errors);
        }
    }

    /// Walks `stmts` in order, threading structures so that each stmt's
    /// after-structure becomes the next stmt's before-structure. Returns
    /// the final after-structure (for the caller to use as its own after,
    /// if it wants to chain).
    fn walk_stmt_block(
        &mut self,
        stmts: &[StmtId],
        mut current: Structure,
        state: &mut RuleState,
    ) -> Structure {
        for stmt in stmts {
            let before_id = self.structures.push(current.clone());
            self.structures.stmt_before.insert(*stmt, before_id);

            current = self.walk_stmt(*stmt, current, state);

            let after_id = self.structures.push(current.clone());
            self.structures.stmt_after.insert(*stmt, after_id);
        }
        current
    }

    fn walk_stmt(
        &mut self,
        stmt: StmtId,
        mut current: Structure,
        state: &mut RuleState,
    ) -> Structure {
        match *self.ast.stmt(stmt) {
            Stmt::If(id) => {
                let atom = self.ast.if_stmt(id).atom;
                self.walk_if_atom(atom, &mut current, state);
            }
            Stmt::Then(id) => {
                let atom = self.ast.then_stmt(id).atom;
                self.walk_then_atom(atom, &mut current, state);
            }
            Stmt::Branch(id) => {
                let blocks = self.ast.branch_stmt(id).blocks.clone();
                for block in &blocks {
                    // Each block starts from the shared before-structure.
                    // We don't merge block afters back into `current` because
                    // that needs morphisms and this pass has none.
                    self.walk_stmt_block(block, current.clone(), state);
                }
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                // The scrutinee is evaluated once, before any case branches.
                self.walk_term(term, &mut current, state);
                for case in &cases {
                    let MatchCase { pattern, body } = self.ast.match_case(*case).clone();
                    let mut case_current = current.clone();
                    self.walk_term(pattern, &mut case_current, state);
                    self.walk_stmt_block(&body, case_current, state);
                }
            }
        }
        current
    }

    fn walk_if_atom(&mut self, atom: IfAtomId, current: &mut Structure, state: &mut RuleState) {
        match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let lhs_el = self.walk_term(lhs, current, state);
                let rhs_el = self.walk_term(rhs, current, state);
                current.equate(lhs_el, rhs_el);
            }
            IfAtom::Defined(id) => {
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                self.walk_term(term, current, state);
            }
            IfAtom::Pred(id) => {
                self.walk_pred_atom(id, current, state);
            }
            IfAtom::Var(id) => {
                let VarIfAtom { term, typ } = *self.ast.var_if_atom(id);
                let typ_id = self.resolve_type_expr(typ);
                let ct = self.concrete_type_for(typ_id, state);
                let el_id = current.push_el();
                current.els.insert(el_id, ct);
                current.semantic_el.insert(term, el_id);
                if let Term::Var(vid) = *self.ast.term(term) {
                    current.var_els.insert(vid, el_id);
                }
            }
        }
    }

    fn walk_then_atom(&mut self, atom: ThenAtomId, current: &mut Structure, state: &mut RuleState) {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let lhs_el = self.walk_term(lhs, current, state);
                let rhs_el = self.walk_term(rhs, current, state);
                current.equate(lhs_el, rhs_el);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                let var_el = var.map(|v| self.walk_term(v, current, state));
                let term_el = self.walk_term(term, current, state);
                if let Some(var_el) = var_el {
                    current.equate(var_el, term_el);
                }
            }
            ThenAtom::Pred(id) => {
                self.walk_pred_atom(id, current, state);
            }
        }
    }

    fn walk_pred_atom(&mut self, id: PredAtomId, current: &mut Structure, state: &mut RuleState) {
        let PredAtom { pred, args } = *self.ast.pred_atom(id);
        let arg_terms = self.ast.term_list(args).terms.clone();
        let arg_els: Vec<ElId> = arg_terms
            .iter()
            .map(|t| self.walk_term(*t, current, state))
            .collect();

        let resolved = match *self.ast.pred_expr(pred) {
            PredExpr::Ambient(aid) => {
                let scope = self.scopes.entry(aid);
                let name = self.ast.ambient_pred_expr(aid).name.clone();
                match self.scopes.lookup(scope, &name) {
                    Some(Symbol::Pred(pd)) => self.signature.pred_for_pred_decl(pd),
                    _ => None,
                }
            }
            PredExpr::Member(_) => None,
        };
        let Some(pred_id) = resolved else {
            return;
        };

        let parents = self.parents_prefix(self.signature.pred(pred_id).parents.len(), state);
        if arg_els.len() != self.signature.pred(pred_id).arity.len() {
            return;
        }

        current.pred_apps.insert(PredApp {
            pred: pred_id,
            parents,
            args: arg_els,
        });
    }

    /// Walks `term`, materialising any Els it needs in `current`, and
    /// returns the El that represents this term occurrence. Also records
    /// the mapping in `current.semantic_el`. Repeated variable occurrences
    /// resolve to the same El via `current.var_els`. Wildcards, app-term
    /// results, and dom/cod/mor-app results each produce a fresh El.
    fn walk_term(&mut self, term: TermId, current: &mut Structure, state: &mut RuleState) -> ElId {
        let el = match *self.ast.term(term) {
            Term::Var(vid) => {
                let entry_scope = self.scopes.entry(vid);
                let name = self.ast.var_term(vid).name.clone();
                let binding_id = match self.scopes.lookup(entry_scope, &name) {
                    Some(Symbol::Var(bid)) => bid,
                    // Var not yet bound at this scope: this is the binding
                    // occurrence. Use its own id as the key.
                    _ => vid,
                };
                if let Some(&el_id) = current.var_els.get(&binding_id) {
                    el_id
                } else {
                    let el_id = current.push_el();
                    current.var_els.insert(binding_id, el_id);
                    el_id
                }
            }
            Term::Wildcard => current.push_el(),
            Term::App(aid) => {
                let AppTerm { func, args } = *self.ast.app_term(aid);
                let arg_terms = self.ast.term_list(args).terms.clone();
                let arg_els: Vec<ElId> = arg_terms
                    .iter()
                    .map(|t| self.walk_term(*t, current, state))
                    .collect();
                self.emit_app(func, arg_els, current, state)
            }
            Term::Dom(did) => {
                let DomTerm { arg } = *self.ast.dom_term(did);
                self.walk_term(arg, current, state);
                current.push_el()
            }
            Term::Cod(cid) => {
                let CodTerm { arg } = *self.ast.cod_term(cid);
                self.walk_term(arg, current, state);
                current.push_el()
            }
            Term::MorApp(mid) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(mid);
                self.walk_term(mor, current, state);
                self.walk_term(arg, current, state);
                current.push_el()
            }
        };
        current.semantic_el.insert(term, el);
        el
    }

    /// Resolves the func expression and, on success, emits the [`FuncApp`]
    /// along with its result El. Always returns *some* El for the result, so
    /// callers can thread it; on resolution failure or arg-count mismatch
    /// the returned El has no type and no [`FuncApp`] is recorded.
    fn emit_app(
        &mut self,
        func: FuncExprId,
        arg_els: Vec<ElId>,
        current: &mut Structure,
        state: &mut RuleState,
    ) -> ElId {
        let resolved = match *self.ast.func_expr(func) {
            FuncExpr::Ambient(aid) => {
                let scope = self.scopes.entry(aid);
                let name = self.ast.ambient_func_expr(aid).name.clone();
                match self.scopes.lookup(scope, &name) {
                    Some(Symbol::Func(fd)) => self.signature.func_for_func_decl(fd),
                    Some(Symbol::Ctor(cd)) => self.signature.func_for_ctor_decl(cd),
                    _ => None,
                }
            }
            FuncExpr::Member(_) => None,
        };

        let Some(func_id) = resolved else {
            return current.push_el();
        };

        let func_data = self.signature.func(func_id);
        if arg_els.len() != func_data.domain.len() {
            return current.push_el();
        }

        let parents = self.parents_prefix(func_data.parents.len(), state);
        let codomain = func_data.codomain;
        let result_ct = self.concrete_type_for(Some(codomain), state);
        let result_id = current.push_el();
        current.els.insert(result_id, result_ct);
        current.func_apps.insert(
            FuncApp {
                func: func_id,
                parents,
                args: arg_els,
            },
            result_id,
        );
        result_id
    }

    fn resolve_type_expr(&self, type_expr: TypeExprId) -> Option<TypeId> {
        let scope: ScopeId = self.scopes.entry(type_expr);
        match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                let name = &self.ast.ambient_type_expr(id).name;
                match self.scopes.lookup(scope, name) {
                    Some(Symbol::Type(td)) => Some(self.signature.type_for_type_decl(td)),
                    Some(Symbol::Enum(ed)) => Some(self.signature.type_for_enum_decl(ed)),
                    Some(Symbol::Model(md)) => Some(self.signature.types_for_model_decl(md).type_),
                    _ => None,
                }
            }
            TypeExpr::Mor(id) => {
                let name = &self.ast.mor_type_expr(id).name;
                match self.scopes.lookup(scope, name) {
                    Some(Symbol::Model(md)) => Some(self.signature.types_for_model_decl(md).mor),
                    _ => None,
                }
            }
            TypeExpr::Member(_) => None,
        }
    }

    /// Packages a known [`TypeId`] with the parent ambient-el prefix that
    /// matches its signature. Returns `None` when the type is unknown.
    fn concrete_type_for(&self, typ_id: Option<TypeId>, state: &RuleState) -> Option<ConcreteType> {
        let tid = typ_id?;
        Some(ConcreteType {
            typ: tid,
            parents: self.parents_for_type(Some(tid), state),
        })
    }

    /// Returns the ambient-model-el prefix to use as the `parents` of an El
    /// whose type is `typ_id`. If we don't know the type, or the ambient
    /// chain is too short to cover the type's parent list, returns empty.
    fn parents_for_type(&self, typ_id: Option<TypeId>, state: &RuleState) -> Vec<ElId> {
        let Some(tid) = typ_id else {
            return Vec::new();
        };
        let n = self.signature.type_(tid).parents.len();
        if n > state.ambient.len() {
            return Vec::new();
        }
        state.ambient[..n].to_vec()
    }

    fn parents_prefix(&self, needed: usize, state: &RuleState) -> Vec<ElId> {
        if needed > state.ambient.len() {
            Vec::new()
        } else {
            state.ambient[..needed].to_vec()
        }
    }
}
