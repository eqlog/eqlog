//! Walks an AST rule body to fill in a [`RuleStructures`].
//!
//! The walker is re-entrant: every call traverses the entire rule body and
//! re-attempts work that may now succeed thanks to type information learned
//! during a preceding [`StructureCat::close`]. Idempotency is achieved per
//! AST site rather than by short-circuiting: each statement, branch block,
//! match scrutinee, match case body and term reuses the structure or
//! element it produced previously instead of creating a fresh one. App
//! terms and predicate atoms are always re-walked so that a func or pred
//! reference whose resolution depended on type info gets a chance to
//! emit its [`FuncApp`] or [`PredApp`] on a later pass. [`walk_rule`]
//! returns true iff some allocation, insertion or non-trivial equate
//! happened during this call.

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;

use crate::algebra::signature::{Signature, TypeId};
use crate::algebra::structure::{
    ConcreteType, ElId, ElMap, FuncApp, PredApp, Structure, StructureCat, StructureId,
};
use crate::ast::*;
use crate::scopes::{ScopeId, Scopes, Symbol};

/// All algebraic structures produced for one rule. The initial structure
/// (state before any statement has executed) is `cat.structures[0]`.
#[derive(Clone, Debug, Default)]
pub struct RuleStructures {
    pub cat: StructureCat,
    /// Invariant: `semantic_els.len() == cat.structures.len()`. Entry `i`
    /// is the term-to-element provenance map for `cat.structures[i]`.
    pub semantic_els: Vec<BTreeMap<TermId, ElId>>,
    pub stmt_before: BTreeMap<StmtId, StructureId>,
    pub stmt_after: BTreeMap<StmtId, StructureId>,
    /// The cloned start structure of each block of a `branch` statement,
    /// keyed by `(branch, index_within_branch)`.
    pub branch_block_starts: BTreeMap<(BranchStmtId, usize), StructureId>,
    /// The post-scrutinee structure of each `match`, evaluated once per
    /// match before any case body.
    pub match_after_scrutinee: BTreeMap<MatchStmtId, StructureId>,
    /// The cloned start structure of each `match` case body.
    pub match_case_starts: BTreeMap<MatchCaseId, StructureId>,
}

impl RuleStructures {
    /// Appends a blank [`Structure`] with an empty `semantic_el` and
    /// returns its fresh [`StructureId`].
    fn push_blank(&mut self) -> StructureId {
        let id = self.cat.push(Structure::default());
        self.semantic_els.push(BTreeMap::new());
        id
    }

    /// Appends a clone of the structure at `id`, adds the identity
    /// inclusion morphism from `id` to the new structure, and returns the
    /// fresh [`StructureId`].
    fn clone_structure(&mut self, id: StructureId) -> StructureId {
        let clone = self.cat.structures[id.0].clone();
        let identity = identity_elmap(&clone);
        let new_id = self.cat.push(clone);
        self.semantic_els.push(self.semantic_els[id.0].clone());
        self.cat.add_morphism(id, new_id, identity);
        new_id
    }
}

/// Identity map on every element of `s`. Suitable for the inclusion
/// morphism into a clone of `s`, which shares the same [`ElId`]s.
fn identity_elmap(s: &Structure) -> ElMap {
    s.els.keys().map(|&el| (el, el)).collect()
}

/// Populates `rule` with the structures and term mappings derived from
/// walking rule `rid`'s body. `enclosing_models` is the chain of model
/// types the rule is nested inside, outermost first.
///
/// Returns true iff at least one site produced something it had not
/// produced on previous calls. A `false` return means the rule is at a
/// fixed point with respect to the current state of `rule.cat`.
pub fn walk_rule(
    rule: &mut RuleStructures,
    rid: RuleDeclId,
    enclosing_models: &[TypeId],
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> bool {
    let mut changed = false;
    let initial = if rule.cat.structures.is_empty() {
        changed = true;
        rule.push_blank()
    } else {
        StructureId(0)
    };
    if ensure_ambient_els(&mut rule.cat.structures[initial.0], enclosing_models) {
        changed = true;
    }

    let body = ast.rule_decl(rid).body.clone();
    let (_after, walk_changed) = walk_stmt_block(&body, initial, rule, ast, scopes, signature);
    changed || walk_changed
}

/// Walks `stmts` in order. `current` is the id of the structure that
/// represents state just before the next statement; each statement
/// updates it to the id of its after-structure. Always re-walks every
/// statement so a previously-blocked resolution gets another shot.
/// Returns `(final_after, changed)`.
fn walk_stmt_block(
    stmts: &[StmtId],
    mut current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> (StructureId, bool) {
    let mut changed = false;
    for stmt in stmts {
        let before = match rule.stmt_before.entry(*stmt) {
            Entry::Vacant(v) => {
                v.insert(current);
                changed = true;
                current
            }
            Entry::Occupied(o) => *o.get(),
        };
        debug_assert_eq!(
            before, current,
            "stmt_before for {stmt:?} drifted between populate calls"
        );
        let (after, stmt_changed) = walk_stmt(*stmt, before, rule, ast, scopes, signature);
        if stmt_changed {
            changed = true;
        }
        current = after;
    }
    (current, changed)
}

fn walk_stmt(
    stmt: StmtId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> (StructureId, bool) {
    match *ast.stmt(stmt) {
        Stmt::If(id) => {
            let (next, mut changed) = ensure_stmt_after(rule, stmt, current);
            let atom = ast.if_stmt(id).atom;
            if walk_if_atom(atom, next, rule, ast, scopes, signature) {
                changed = true;
            }
            (next, changed)
        }
        Stmt::Then(id) => {
            let (next, mut changed) = ensure_stmt_after(rule, stmt, current);
            let atom = ast.then_stmt(id).atom;
            if walk_then_atom(atom, next, rule, ast, scopes, signature) {
                changed = true;
            }
            (next, changed)
        }
        Stmt::Branch(id) => {
            let blocks = ast.branch_stmt(id).blocks.clone();
            let mut changed = false;
            for (idx, block) in blocks.iter().enumerate() {
                let (block_start, c1) = ensure_branch_block_start(rule, id, idx, current);
                if c1 {
                    changed = true;
                }
                let (_after, c2) =
                    walk_stmt_block(block, block_start, rule, ast, scopes, signature);
                if c2 {
                    changed = true;
                }
            }
            // The branch's after-structure is a separate clone of the
            // shared before-structure; it receives an inclusion from
            // `current` but is deliberately disconnected from the
            // individual branches.
            // TODO: after_stmt should get a morphism from the
            // intersection of the end structures in each branch.
            let (after, c3) = ensure_stmt_after(rule, stmt, current);
            if c3 {
                changed = true;
            }
            (after, changed)
        }
        Stmt::Match(id) => {
            let MatchStmt { term, cases } = ast.match_stmt(id);
            let term = *term;
            let cases = cases.clone();
            let (after_scrutinee, mut changed) = ensure_match_after_scrutinee(rule, id, current);
            let (_el, c1) = walk_term(term, after_scrutinee, rule, ast, scopes, signature);
            if c1 {
                changed = true;
            }
            for case in &cases {
                let MatchCase { pattern, body } = ast.match_case(*case).clone();
                let (case_start, c2) = ensure_match_case_start(rule, *case, after_scrutinee);
                if c2 {
                    changed = true;
                }
                let (_el, c3) = walk_term(pattern, case_start, rule, ast, scopes, signature);
                if c3 {
                    changed = true;
                }
                let (_after, c4) = walk_stmt_block(&body, case_start, rule, ast, scopes, signature);
                if c4 {
                    changed = true;
                }
            }
            // Likewise, the match's after-structure is a fresh clone of
            // `after_scrutinee` (so the scrutinee's effects carry through),
            // disconnected from the case bodies.
            // TODO: after_stmt should get a morphism from the intersection
            // of the end structures in each case.
            let (after, c5) = ensure_stmt_after(rule, stmt, after_scrutinee);
            if c5 {
                changed = true;
            }
            (after, changed)
        }
    }
}

/// Returns the structure recorded as `stmt_after[stmt]`, allocating a clone
/// of `src` for it on the first visit. The bool indicates whether a fresh
/// clone was created.
fn ensure_stmt_after(
    rule: &mut RuleStructures,
    stmt: StmtId,
    src: StructureId,
) -> (StructureId, bool) {
    if let Some(&id) = rule.stmt_after.get(&stmt) {
        return (id, false);
    }
    let id = rule.clone_structure(src);
    rule.stmt_after.insert(stmt, id);
    (id, true)
}

fn ensure_branch_block_start(
    rule: &mut RuleStructures,
    branch: BranchStmtId,
    idx: usize,
    src: StructureId,
) -> (StructureId, bool) {
    if let Some(&id) = rule.branch_block_starts.get(&(branch, idx)) {
        return (id, false);
    }
    let id = rule.clone_structure(src);
    rule.branch_block_starts.insert((branch, idx), id);
    (id, true)
}

fn ensure_match_after_scrutinee(
    rule: &mut RuleStructures,
    match_id: MatchStmtId,
    src: StructureId,
) -> (StructureId, bool) {
    if let Some(&id) = rule.match_after_scrutinee.get(&match_id) {
        return (id, false);
    }
    let id = rule.clone_structure(src);
    rule.match_after_scrutinee.insert(match_id, id);
    (id, true)
}

fn ensure_match_case_start(
    rule: &mut RuleStructures,
    case: MatchCaseId,
    src: StructureId,
) -> (StructureId, bool) {
    if let Some(&id) = rule.match_case_starts.get(&case) {
        return (id, false);
    }
    let id = rule.clone_structure(src);
    rule.match_case_starts.insert(case, id);
    (id, true)
}

fn walk_if_atom(
    atom: IfAtomId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> bool {
    match *ast.if_atom(atom) {
        IfAtom::Equal(id) => {
            let EqualAtom { lhs, rhs } = *ast.equal_atom(id);
            let (lhs_el, c1) = walk_term(lhs, current, rule, ast, scopes, signature);
            let (rhs_el, c2) = walk_term(rhs, current, rule, ast, scopes, signature);
            let eq = rule.cat.structures[current.0].equate(lhs_el, rhs_el);
            c1 || c2 || eq
        }
        IfAtom::Defined(id) => {
            let DefinedIfAtom { term } = *ast.defined_if_atom(id);
            let (_el, c) = walk_term(term, current, rule, ast, scopes, signature);
            c
        }
        IfAtom::Pred(id) => walk_pred_atom(id, current, rule, ast, scopes, signature),
        IfAtom::Var(id) => {
            let VarIfAtom { term, typ } = *ast.var_if_atom(id);
            // Idempotency: a second visit of the same VarIfAtom finds
            // its term already in semantic_els and skips both the el
            // allocation and the var_els insertion.
            if rule.semantic_els[current.0].contains_key(&term) {
                return false;
            }
            let typ_id = resolve_type_expr(typ, ast, scopes, signature);
            let structure = &mut rule.cat.structures[current.0];
            let ct = concrete_type_for(signature, typ_id, structure);
            let el_id = structure.push_el();
            structure.els.insert(el_id, ct);
            rule.semantic_els[current.0].insert(term, el_id);
            match *ast.term(term) {
                Term::Var(vid) => {
                    let name = ast.var_term(vid).name.clone();
                    rule.cat.structures[current.0].var_els.insert(name, el_id);
                }
                Term::Wildcard => {}
                // Rejected by check_syntactic::check_if_var_lhs.
                Term::App(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => unreachable!(
                    "VarIfAtom lhs must be a variable or wildcard; enforced by syntactic.rs"
                ),
            }
            true
        }
    }
}

fn walk_then_atom(
    atom: ThenAtomId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> bool {
    match *ast.then_atom(atom) {
        ThenAtom::Equal(id) => {
            let EqualAtom { lhs, rhs } = *ast.equal_atom(id);
            let (lhs_el, c1) = walk_term(lhs, current, rule, ast, scopes, signature);
            let (rhs_el, c2) = walk_term(rhs, current, rule, ast, scopes, signature);
            let eq = rule.cat.structures[current.0].equate(lhs_el, rhs_el);
            c1 || c2 || eq
        }
        ThenAtom::Defined(id) => {
            let DefinedThenAtom { var, term } = *ast.defined_then_atom(id);
            let mut changed = false;
            let var_el = if let Some(v) = var {
                let (e, c) = walk_term(v, current, rule, ast, scopes, signature);
                if c {
                    changed = true;
                }
                Some(e)
            } else {
                None
            };
            let (term_el, c) = walk_term(term, current, rule, ast, scopes, signature);
            if c {
                changed = true;
            }
            if let Some(var_el) = var_el {
                if rule.cat.structures[current.0].equate(var_el, term_el) {
                    changed = true;
                }
            }
            changed
        }
        ThenAtom::Pred(id) => walk_pred_atom(id, current, rule, ast, scopes, signature),
    }
}

fn walk_pred_atom(
    id: PredAtomId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> bool {
    let PredAtom { pred, args } = *ast.pred_atom(id);
    let arg_terms = ast.term_list(args).terms.clone();
    let mut changed = false;
    let arg_els: Vec<ElId> = arg_terms
        .iter()
        .map(|t| {
            let (e, c) = walk_term(*t, current, rule, ast, scopes, signature);
            if c {
                changed = true;
            }
            e
        })
        .collect();

    let resolved = match *ast.pred_expr(pred) {
        PredExpr::Ambient(aid) => {
            let scope = scopes.entry(aid);
            let name = ast.ambient_pred_expr(aid).name.clone();
            match scopes.lookup(scope, &name) {
                Some(Symbol::Pred(pd)) => signature.pred_for_pred_decl(pd),
                _ => None,
            }
        }
        PredExpr::Member(_) => None,
    };
    let Some(pred_id) = resolved else {
        return changed;
    };

    let pred_data = signature.pred(pred_id);
    if arg_els.len() != pred_data.arity.len() {
        return changed;
    }
    let structure = &mut rule.cat.structures[current.0];
    let parents: Vec<ElId> = structure
        .ambient_parents(&pred_data.parents)
        .into_iter()
        .map(|e| structure.unification.root(e))
        .collect();
    let canonical_args: Vec<ElId> = arg_els
        .iter()
        .map(|e| structure.unification.root(*e))
        .collect();
    if structure.pred_apps.insert(PredApp {
        pred: pred_id,
        parents,
        args: canonical_args,
    }) {
        changed = true;
    }
    changed
}

/// Walks `term`, materialising any Els it needs in the current
/// structure, records `term -> el` in `semantic_el`, and returns the El.
///
/// Idempotent at the el-identity level: `Var` and `Wildcard` terms reuse
/// the el they cached on the first walk. App terms always recurse into
/// their arguments and re-attempt resolution of the func reference, so
/// that a [`FuncApp`] missed on a previous pass (because the func was
/// unresolvable at the time) gets emitted now. The result el of an App is
/// still the cached one when present, so callers' chains remain stable.
fn walk_term(
    term: TermId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> (ElId, bool) {
    let cached = rule.semantic_els[current.0].get(&term).copied();
    let mut changed = false;
    let el = match *ast.term(term) {
        Term::Var(vid) => {
            if let Some(el) = cached {
                el
            } else {
                let name = ast.var_term(vid).name.clone();
                let structure = &mut rule.cat.structures[current.0];
                if let Some(&el_id) = structure.var_els.get(&name) {
                    el_id
                } else {
                    let el_id = structure.push_el();
                    structure.var_els.insert(name, el_id);
                    changed = true;
                    el_id
                }
            }
        }
        Term::Wildcard => {
            if let Some(el) = cached {
                el
            } else {
                changed = true;
                rule.cat.structures[current.0].push_el()
            }
        }
        Term::App(aid) => {
            let AppTerm { func, args } = *ast.app_term(aid);
            let arg_terms = ast.term_list(args).terms.clone();
            let arg_els: Vec<ElId> = arg_terms
                .iter()
                .map(|t| {
                    let (e, c) = walk_term(*t, current, rule, ast, scopes, signature);
                    if c {
                        changed = true;
                    }
                    e
                })
                .collect();
            let (e, c) = emit_app(func, arg_els, cached, current, rule, ast, scopes, signature);
            if c {
                changed = true;
            }
            e
        }
        Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
            // TODO: implement once dom/cod/@ operators are defined on
            // the structure side. The current pass was materialising a
            // fresh untyped El, which is wrong.
            todo!()
        }
    };
    if cached.is_none() {
        rule.semantic_els[current.0].insert(term, el);
        changed = true;
    }
    (el, changed)
}

/// Resolves `func` and, on success, ensures the corresponding [`FuncApp`]
/// is recorded in the current structure. `expected` is the result el the
/// caller has previously committed for this term, if any (from
/// `semantic_els`). When provided it is reused, possibly with an `equate`
/// against an existing entry; otherwise a fresh el is allocated. On
/// resolution failure or arg-count mismatch the caller's `expected` is
/// returned unchanged, or a fresh untyped el is allocated.
///
/// Returns `(result_el, changed)`. `changed` is true iff this call
/// allocated a new el, inserted a new func app, recorded a fresh
/// concrete type or enqueued a non-trivial equate.
fn emit_app(
    func: FuncExprId,
    arg_els: Vec<ElId>,
    expected: Option<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> (ElId, bool) {
    let resolved = match *ast.func_expr(func) {
        FuncExpr::Ambient(aid) => {
            let scope = scopes.entry(aid);
            let name = ast.ambient_func_expr(aid).name.clone();
            match scopes.lookup(scope, &name) {
                Some(Symbol::Func(fd)) => signature.func_for_func_decl(fd),
                Some(Symbol::Ctor(cd)) => signature.func_for_ctor_decl(cd),
                _ => None,
            }
        }
        FuncExpr::Member(_) => None,
    };

    let structure = &mut rule.cat.structures[current.0];

    let Some(func_id) = resolved else {
        return match expected {
            Some(el) => (el, false),
            None => (structure.push_el(), true),
        };
    };

    let func_data = signature.func(func_id);
    if arg_els.len() != func_data.domain.len() {
        return match expected {
            Some(el) => (el, false),
            None => (structure.push_el(), true),
        };
    }

    let codomain = func_data.codomain;
    let parents: Vec<ElId> = structure
        .ambient_parents(&func_data.parents)
        .into_iter()
        .map(|e| structure.unification.root(e))
        .collect();
    let canonical_args: Vec<ElId> = arg_els
        .iter()
        .map(|e| structure.unification.root(*e))
        .collect();
    let app_key = FuncApp {
        func: func_id,
        parents,
        args: canonical_args,
    };

    let mut changed = false;
    let result_id = match structure.func_apps.get(&app_key).copied() {
        Some(existing) => match expected {
            Some(exp) => {
                if exp != existing && structure.equate(exp, existing) {
                    changed = true;
                }
                exp
            }
            None => existing,
        },
        None => {
            let id = match expected {
                Some(el) => el,
                None => structure.push_el(),
            };
            let result_ct = concrete_type_for(signature, Some(codomain), structure);
            if let Some(ct) = result_ct {
                let entry = structure.els.entry(id).or_insert(None);
                if entry.is_none() {
                    *entry = Some(ct);
                }
            }
            structure.func_apps.insert(app_key, id);
            // Allocating an el, recording a fresh type or inserting a new
            // func_app entry is always observable change.
            changed = true;
            id
        }
    };
    (result_id, changed)
}

fn resolve_type_expr(
    type_expr: TypeExprId,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> Option<TypeId> {
    let scope: ScopeId = scopes.entry(type_expr);
    match *ast.type_expr(type_expr) {
        TypeExpr::Ambient(id) => {
            let name = &ast.ambient_type_expr(id).name;
            match scopes.lookup(scope, name) {
                Some(Symbol::Type(td)) => Some(signature.type_for_type_decl(td)),
                Some(Symbol::Enum(ed)) => Some(signature.type_for_enum_decl(ed)),
                Some(Symbol::Model(md)) => Some(signature.types_for_model_decl(md).type_),
                _ => None,
            }
        }
        TypeExpr::Mor(id) => {
            let name = &ast.mor_type_expr(id).name;
            match scopes.lookup(scope, name) {
                Some(Symbol::Model(md)) => Some(signature.types_for_model_decl(md).mor),
                _ => None,
            }
        }
        TypeExpr::Member(_) => None,
    }
}

/// Packages a known [`TypeId`] with the parent ambient els that its
/// signature requires, read off `structure.ambient_model_els`. Returns
/// `None` when the type is unknown.
fn concrete_type_for(
    signature: &Signature,
    typ_id: Option<TypeId>,
    structure: &Structure,
) -> Option<ConcreteType> {
    let tid = typ_id?;
    Some(ConcreteType {
        typ: tid,
        parents: structure.ambient_parents(&signature.type_(tid).parents),
    })
}

/// Ensures the initial structure carries one ambient model el per enclosing
/// model type. Returns true iff this call allocated any of them. Idempotent
/// via the count-equals-expected check.
fn ensure_ambient_els(init: &mut Structure, enclosing_models: &[TypeId]) -> bool {
    if init.ambient_model_els.len() == enclosing_models.len() {
        return false;
    }
    let mut parents: Vec<ElId> = Vec::new();
    for &model_tid in enclosing_models {
        let el_id = init.push_el();
        init.els.insert(
            el_id,
            Some(ConcreteType {
                typ: model_tid,
                parents: parents.clone(),
            }),
        );
        init.ambient_model_els.insert(model_tid, el_id);
        parents.push(el_id);
    }
    true
}
