//! Turns AST rule bodies into algebraic data.

use std::collections::BTreeMap;

use crate::algebra::signature::{Signature, TypeId};
use crate::algebra::structure::{
    ConcreteType, ElId, FuncApp, PredApp, Structure, TypeConflict,
};
use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::{ScopeId, Scopes, Symbol};

/// An index into one rule's flat arena of structures. Only valid within
/// the [`RuleStructures`] that produced it.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StructureId(pub usize);

/// All algebraic structures produced for one rule.
#[derive(Clone, Debug, Default)]
pub struct RuleStructures {
    pub structures: Vec<Structure>,
    /// Invariant: `semantic_els.len() == structures.len()`. Entry `i` is
    /// the term-to-element provenance map for `structures[i]`.
    pub semantic_els: Vec<BTreeMap<TermId, ElId>>,
    pub initial: StructureId,
    pub stmt_before: BTreeMap<StmtId, StructureId>,
    pub stmt_after: BTreeMap<StmtId, StructureId>,
}

impl RuleStructures {
    /// Appends a blank [`Structure`] with an empty `semantic_el` and
    /// returns its fresh [`StructureId`].
    fn push_blank(&mut self) -> StructureId {
        let id = StructureId(self.structures.len());
        self.structures.push(Structure::default());
        self.semantic_els.push(BTreeMap::new());
        id
    }

    /// Appends a clone of the entry at `id` and returns the fresh
    /// [`StructureId`]. Used when a walk is about to mutate an entry
    /// that is already committed to a before/after map.
    fn fork(&mut self, id: StructureId) -> StructureId {
        let new_id = StructureId(self.structures.len());
        self.structures.push(self.structures[id.0].clone());
        self.semantic_els.push(self.semantic_els[id.0].clone());
        new_id
    }
}

/// Walks `ast` rooted at `module`, builds a [`RuleStructures`] for every
/// rule and closes every structure it produced. The accompanying errors
/// collect every type conflict discovered while closing.
pub fn build_structures(
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    module: ModuleId,
) -> (BTreeMap<RuleDeclId, RuleStructures>, Vec<CompileError>) {
    let mut builder = Builder {
        ast,
        scopes,
        signature,
        rules: BTreeMap::new(),
        errors: Vec::new(),
    };
    let decls = ast.module(module).decls.clone();
    builder.walk_decls(&decls, &[]);
    (builder.rules, builder.errors)
}

struct Builder<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
    signature: &'a Signature,
    rules: BTreeMap<RuleDeclId, RuleStructures>,
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
        let mut rule = RuleStructures::default();
        let initial = rule.push_blank();
        rule.initial = initial;

        // Populate the initial structure with ambient-model elements.
        let mut ambient: Vec<ElId> = Vec::new();
        let init = &mut rule.structures[initial.0];
        for &model_tid in enclosing_models {
            let el_id = init.push_el();
            init.els.insert(
                el_id,
                Some(ConcreteType {
                    typ: model_tid,
                    parents: ambient.clone(),
                }),
            );
            init.ambient_model_els.insert(el_id);
            ambient.push(el_id);
        }

        let body = self.ast.rule_decl(rid).body.clone();
        let mut state = RuleState { ambient };
        self.walk_stmt_block(&body, initial, &mut rule, &mut state);

        // Close every structure in this rule and translate conflicts
        // using the matching semantic_el.
        let ast = self.ast;
        let signature = self.signature;
        let errors = &mut self.errors;
        for (structure, semantic_el) in
            rule.structures.iter_mut().zip(rule.semantic_els.iter())
        {
            let conflicts = structure.close(signature);
            for conflict in conflicts {
                errors.push(conflict_to_error(
                    ast,
                    signature,
                    structure,
                    semantic_el,
                    conflict,
                ));
            }
        }

        self.rules.insert(rid, rule);
    }

    /// Walks `stmts` in order. `current` is the id of the structure
    /// that represents state just before the next statement; each
    /// statement updates it to the id of its after-structure (typically
    /// a fork of the before-structure). Returns the final after-id.
    fn walk_stmt_block(
        &mut self,
        stmts: &[StmtId],
        mut current: StructureId,
        rule: &mut RuleStructures,
        state: &mut RuleState,
    ) -> StructureId {
        for stmt in stmts {
            rule.stmt_before.insert(*stmt, current);
            current = self.walk_stmt(*stmt, current, rule, state);
            rule.stmt_after.insert(*stmt, current);
        }
        current
    }

    fn walk_stmt(
        &mut self,
        stmt: StmtId,
        current: StructureId,
        rule: &mut RuleStructures,
        state: &mut RuleState,
    ) -> StructureId {
        match *self.ast.stmt(stmt) {
            Stmt::If(id) => {
                // Fork first: `current` is the committed before-structure
                // and must stay immutable.
                let fork = rule.fork(current);
                let atom = self.ast.if_stmt(id).atom;
                self.walk_if_atom(atom, fork, rule, state);
                fork
            }
            Stmt::Then(id) => {
                let fork = rule.fork(current);
                let atom = self.ast.then_stmt(id).atom;
                self.walk_then_atom(atom, fork, rule, state);
                fork
            }
            Stmt::Branch(id) => {
                let blocks = self.ast.branch_stmt(id).blocks.clone();
                for block in &blocks {
                    // Each block starts from a fork of the shared
                    // before-structure. Block afters are not merged back
                    // because that needs morphisms and this pass has none.
                    let fork = rule.fork(current);
                    self.walk_stmt_block(block, fork, rule, state);
                }
                current
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                // Scrutinee is evaluated once, before any case branches.
                let fork = rule.fork(current);
                self.walk_term(term, fork, rule, state);
                for case in &cases {
                    let MatchCase { pattern, body } = self.ast.match_case(*case).clone();
                    let case_fork = rule.fork(fork);
                    self.walk_term(pattern, case_fork, rule, state);
                    self.walk_stmt_block(&body, case_fork, rule, state);
                }
                fork
            }
        }
    }

    fn walk_if_atom(
        &mut self,
        atom: IfAtomId,
        current: StructureId,
        rule: &mut RuleStructures,
        state: &mut RuleState,
    ) {
        match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let lhs_el = self.walk_term(lhs, current, rule, state);
                let rhs_el = self.walk_term(rhs, current, rule, state);
                rule.structures[current.0].equate(lhs_el, rhs_el);
            }
            IfAtom::Defined(id) => {
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                self.walk_term(term, current, rule, state);
            }
            IfAtom::Pred(id) => {
                self.walk_pred_atom(id, current, rule, state);
            }
            IfAtom::Var(id) => {
                let VarIfAtom { term, typ } = *self.ast.var_if_atom(id);
                let typ_id = self.resolve_type_expr(typ);
                let ct = self.concrete_type_for(typ_id, state);
                let structure = &mut rule.structures[current.0];
                let el_id = structure.push_el();
                structure.els.insert(el_id, ct);
                rule.semantic_els[current.0].insert(term, el_id);
                if let Term::Var(vid) = *self.ast.term(term) {
                    let name = self.ast.var_term(vid).name.clone();
                    rule.structures[current.0].var_els.insert(name, el_id);
                }
            }
        }
    }

    fn walk_then_atom(
        &mut self,
        atom: ThenAtomId,
        current: StructureId,
        rule: &mut RuleStructures,
        state: &mut RuleState,
    ) {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                let lhs_el = self.walk_term(lhs, current, rule, state);
                let rhs_el = self.walk_term(rhs, current, rule, state);
                rule.structures[current.0].equate(lhs_el, rhs_el);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                let var_el = var.map(|v| self.walk_term(v, current, rule, state));
                let term_el = self.walk_term(term, current, rule, state);
                if let Some(var_el) = var_el {
                    rule.structures[current.0].equate(var_el, term_el);
                }
            }
            ThenAtom::Pred(id) => {
                self.walk_pred_atom(id, current, rule, state);
            }
        }
    }

    fn walk_pred_atom(
        &mut self,
        id: PredAtomId,
        current: StructureId,
        rule: &mut RuleStructures,
        state: &mut RuleState,
    ) {
        let PredAtom { pred, args } = *self.ast.pred_atom(id);
        let arg_terms = self.ast.term_list(args).terms.clone();
        let arg_els: Vec<ElId> = arg_terms
            .iter()
            .map(|t| self.walk_term(*t, current, rule, state))
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

        rule.structures[current.0].pred_apps.insert(PredApp {
            pred: pred_id,
            parents,
            args: arg_els,
        });
    }

    /// Walks `term`, materialising any Els it needs in the current
    /// structure, records `term -> el` in `semantic_el`, and returns
    /// the El. Repeated variable occurrences resolve to the same El
    /// via `var_els` (keyed by source name). Wildcards, app-term
    /// results, and dom/cod/mor-app results each produce a fresh El.
    fn walk_term(
        &mut self,
        term: TermId,
        current: StructureId,
        rule: &mut RuleStructures,
        state: &mut RuleState,
    ) -> ElId {
        let el = match *self.ast.term(term) {
            Term::Var(vid) => {
                let name = self.ast.var_term(vid).name.clone();
                let structure = &mut rule.structures[current.0];
                if let Some(&el_id) = structure.var_els.get(&name) {
                    el_id
                } else {
                    let el_id = structure.push_el();
                    structure.var_els.insert(name, el_id);
                    el_id
                }
            }
            Term::Wildcard => rule.structures[current.0].push_el(),
            Term::App(aid) => {
                let AppTerm { func, args } = *self.ast.app_term(aid);
                let arg_terms = self.ast.term_list(args).terms.clone();
                let arg_els: Vec<ElId> = arg_terms
                    .iter()
                    .map(|t| self.walk_term(*t, current, rule, state))
                    .collect();
                self.emit_app(func, arg_els, current, rule, state)
            }
            Term::Dom(did) => {
                let DomTerm { arg } = *self.ast.dom_term(did);
                self.walk_term(arg, current, rule, state);
                rule.structures[current.0].push_el()
            }
            Term::Cod(cid) => {
                let CodTerm { arg } = *self.ast.cod_term(cid);
                self.walk_term(arg, current, rule, state);
                rule.structures[current.0].push_el()
            }
            Term::MorApp(mid) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(mid);
                self.walk_term(mor, current, rule, state);
                self.walk_term(arg, current, rule, state);
                rule.structures[current.0].push_el()
            }
        };
        rule.semantic_els[current.0].insert(term, el);
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
        current: StructureId,
        rule: &mut RuleStructures,
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
            return rule.structures[current.0].push_el();
        };

        let func_data = self.signature.func(func_id);
        if arg_els.len() != func_data.domain.len() {
            return rule.structures[current.0].push_el();
        }

        let parents = self.parents_prefix(func_data.parents.len(), state);
        let codomain = func_data.codomain;
        let result_ct = self.concrete_type_for(Some(codomain), state);
        let structure = &mut rule.structures[current.0];
        let result_id = structure.push_el();
        structure.els.insert(result_id, result_ct);
        structure.func_apps.insert(
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

/// Picks a term in `semantic_el` whose element shares a class with the
/// conflict's `el` and emits [`CompileError::ConflictingTermType`] at
/// that term's location. Panics if no such term exists; the message
/// distinguishes ambient model elements to help diagnose the invariant
/// violation.
fn conflict_to_error(
    ast: &Ast,
    signature: &Signature,
    structure: &Structure,
    semantic_el: &BTreeMap<TermId, ElId>,
    conflict: TypeConflict,
) -> CompileError {
    let TypeConflict { el, types } = conflict;
    let term_id = semantic_el
        .iter()
        .find(|(_, &e)| structure.unification.root_const(e) == el)
        .map(|(t, _)| *t)
        .unwrap_or_else(|| {
            let is_ambient = structure
                .ambient_model_els
                .iter()
                .any(|&e| structure.unification.root_const(e) == el);
            panic!(
                "type conflict on class {el:?} has no term in semantic_el \
                 (ambient model el: {is_ambient})"
            );
        });
    CompileError::ConflictingTermType {
        types: vec![
            signature.type_name(ast, types.0),
            signature.type_name(ast, types.1),
        ],
        location: ast.loc(term_id),
    }
}
