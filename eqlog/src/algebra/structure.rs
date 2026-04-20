//! Per-rule and per-statement structures.
//!
//! A [`Structure`] over a [`Signature`] records the elements ([`El`]), function
//! applications ([`FuncApp`]) and predicate applications ([`PredApp`]) that
//! exist at a given point in a rule. Elements carry an optional type and the
//! chain of parent model elements they live under. Function and predicate
//! applications are plain data, keyed by their own contents, so two calls with
//! identical parents and arguments collapse naturally.
//!
//! [`build_structures`] walks each rule body and assigns a before-structure
//! and an after-structure to every statement. The after-structure is produced
//! by cloning the before-structure and adding whatever the statement
//! contributes. This pass does no unification and no equating. `=` atoms are
//! only visited so their subterm Els materialise.

use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::*;
use crate::ast::*;
use crate::scopes::{ScopeId, Scopes, Symbol};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ElId(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructureId(usize);

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
pub struct El {
    /// The element's type, if known. `None` for fresh wildcards and for
    /// variable bindings without a `var: Type` annotation.
    pub typ: Option<TypeId>,
    /// Enclosing model elements, outermost first.
    pub parents: Vec<ElId>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PredApp {
    pub pred: PredId,
    pub parents: Vec<ElId>,
    pub args: Vec<ElId>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncApp {
    pub func: FuncId,
    pub parents: Vec<ElId>,
    pub args: Vec<ElId>,
}

#[derive(Clone, Debug, Default)]
pub struct Structure {
    pub els: Vec<El>,
    pub pred_apps: BTreeSet<PredApp>,
    pub func_apps: BTreeMap<FuncApp, ElId>,
}

impl Structure {
    pub fn push_el(&mut self, el: El) -> ElId {
        let id = ElId(self.els.len());
        self.els.push(el);
        id
    }
}

#[derive(Clone, Debug, Default)]
pub struct Structures {
    arena: Vec<Structure>,
    rule_initial: BTreeMap<RuleDeclId, StructureId>,
    stmt_before: BTreeMap<StmtId, StructureId>,
    stmt_after: BTreeMap<StmtId, StructureId>,
}

#[allow(dead_code)]
impl Structures {
    pub fn structure(&self, id: StructureId) -> &Structure {
        &self.arena[id.0]
    }

    pub fn rule_initial_structure(&self, id: RuleDeclId) -> StructureId {
        *self
            .rule_initial
            .get(&id)
            .expect("rule initial structure not populated")
    }

    pub fn stmt_before_structure(&self, id: StmtId) -> StructureId {
        *self
            .stmt_before
            .get(&id)
            .expect("stmt before-structure not populated")
    }

    pub fn stmt_after_structure(&self, id: StmtId) -> StructureId {
        *self
            .stmt_after
            .get(&id)
            .expect("stmt after-structure not populated")
    }

    fn push(&mut self, structure: Structure) -> StructureId {
        let id = StructureId(self.arena.len());
        self.arena.push(structure);
        id
    }
}

/// Walks `ast` rooted at `module` and assigns a before-structure and an
/// after-structure to every statement in every rule.
pub fn build_structures(
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    module: ModuleId,
) -> Structures {
    let mut builder = Builder {
        ast,
        scopes,
        signature,
        structures: Structures::default(),
    };
    let decls = ast.module(module).decls.clone();
    builder.walk_decls(&decls, &[]);
    builder.structures
}

struct Builder<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
    signature: &'a Signature,
    structures: Structures,
}

/// Per-rule state the stmt walker threads through recursive calls.
struct RuleState {
    /// Ambient model elements introduced by the rule's enclosing scopes,
    /// outermost first. Same length as the type parent chain. Used as the
    /// prefix for every El created in this rule and as the parents of any
    /// relation application we emit.
    ambient: Vec<ElId>,
    /// Resolves repeated variable occurrences to the same El. Keyed by the
    /// binding's VarTermId (which [`Scopes`] records as the `Symbol::Var`
    /// payload).
    var_els: BTreeMap<VarTermId, ElId>,
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
        let mut initial = Structure::default();
        let mut ambient: Vec<ElId> = Vec::new();
        for &model_tid in enclosing_models {
            let el = El {
                typ: Some(model_tid),
                parents: ambient.clone(),
            };
            ambient.push(initial.push_el(el));
        }

        let initial_id = self.structures.push(initial.clone());
        self.structures.rule_initial.insert(rid, initial_id);

        let body = self.ast.rule_decl(rid).body.clone();
        let mut state = RuleState {
            ambient,
            var_els: BTreeMap::new(),
        };
        self.walk_stmt_block(&body, initial, &mut state);
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
                self.walk_term(lhs, current, state);
                self.walk_term(rhs, current, state);
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
                let el = El {
                    typ: typ_id,
                    parents: self.parents_for_type(typ_id, state),
                };
                let el_id = current.push_el(el);
                if let Term::Var(vid) = *self.ast.term(term) {
                    state.var_els.insert(vid, el_id);
                }
            }
        }
    }

    fn walk_then_atom(&mut self, atom: ThenAtomId, current: &mut Structure, state: &mut RuleState) {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.walk_term(lhs, current, state);
                self.walk_term(rhs, current, state);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                if let Some(var) = var {
                    self.walk_term(var, current, state);
                }
                self.walk_term(term, current, state);
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

    /// Walks `term`, materialising any Els it needs in `current`, and returns
    /// the El that represents this term occurrence. Repeated variable
    /// occurrences resolve to the same El via `state.var_els`. Wildcards,
    /// app-term results, and dom/cod/mor-app results each produce a fresh El.
    fn walk_term(&mut self, term: TermId, current: &mut Structure, state: &mut RuleState) -> ElId {
        match *self.ast.term(term) {
            Term::Var(vid) => {
                let entry_scope = self.scopes.entry(vid);
                let name = self.ast.var_term(vid).name.clone();
                let binding_id = match self.scopes.lookup(entry_scope, &name) {
                    Some(Symbol::Var(bid)) => bid,
                    // Var not yet bound at this scope: this is the binding
                    // occurrence. Use its own id as the key.
                    _ => vid,
                };
                if let Some(&el_id) = state.var_els.get(&binding_id) {
                    return el_id;
                }
                let el = El {
                    typ: None,
                    parents: Vec::new(),
                };
                let el_id = current.push_el(el);
                state.var_els.insert(binding_id, el_id);
                el_id
            }
            Term::Wildcard => current.push_el(El {
                typ: None,
                parents: Vec::new(),
            }),
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
                current.push_el(El {
                    typ: None,
                    parents: Vec::new(),
                })
            }
            Term::Cod(cid) => {
                let CodTerm { arg } = *self.ast.cod_term(cid);
                self.walk_term(arg, current, state);
                current.push_el(El {
                    typ: None,
                    parents: Vec::new(),
                })
            }
            Term::MorApp(mid) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(mid);
                self.walk_term(mor, current, state);
                self.walk_term(arg, current, state);
                current.push_el(El {
                    typ: None,
                    parents: Vec::new(),
                })
            }
        }
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
            return current.push_el(El {
                typ: None,
                parents: Vec::new(),
            });
        };

        let func_data = self.signature.func(func_id);
        if arg_els.len() != func_data.domain.len() {
            return current.push_el(El {
                typ: None,
                parents: Vec::new(),
            });
        }

        let parents = self.parents_prefix(func_data.parents.len(), state);
        let codomain = func_data.codomain;
        let result_el = El {
            typ: Some(codomain),
            parents: self.parents_for_type(Some(codomain), state),
        };
        let result_id = current.push_el(result_el);
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
