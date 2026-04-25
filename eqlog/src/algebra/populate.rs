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

use crate::algebra::signature::{FuncId, PredId, Signature, TypeId};
use crate::algebra::structure::{
    ConcreteType, ElId, ElMap, FuncApp, PredApp, Structure, StructureCat, StructureId,
};
use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::{Scope, ScopeId, Scopes, Symbol};

/// All algebraic structures produced for one rule. The initial structure
/// (state before any statement has executed) is `cat.structures[0]`.
#[derive(Clone, Debug, Default)]
pub struct RuleStructures {
    pub cat: StructureCat,
    /// Invariant: `semantic_els.len() == cat.structures.len()`. Entry
    /// `i` maps each [`TermId`] whose lexical position lies inside the
    /// scope walked into `cat.structures[i]` to its [`ElId`]. Per-
    /// structure only; cross-structure el equality is reconstructed
    /// via morphisms.
    pub semantic_els: Vec<BTreeMap<TermId, ElId>>,
    pub stmt_before: BTreeMap<StmtId, StructureId>,
    pub stmt_after: BTreeMap<StmtId, StructureId>,
    /// The cloned start structure of each block of a `branch` statement,
    /// keyed by `(branch, index_within_branch)`. Distinct from the first
    /// statement's `stmt_before` because a block may be empty, leaving no
    /// statement to anchor the start structure to.
    pub branch_block_starts: BTreeMap<(BranchStmtId, usize), StructureId>,
    /// The post-scrutinee structure of each `match`, evaluated once per
    /// match before any case body.
    pub match_after_scrutinee: BTreeMap<MatchStmtId, StructureId>,
    /// The cloned start structure of each `match` case body. Same reason
    /// as `branch_block_starts`: an empty case body has no first
    /// statement to anchor the start structure to.
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
    /// inclusion morphism from `id` to the new structure, and returns
    /// the fresh [`StructureId`]. The new structure starts with an
    /// empty `semantic_els` map.
    fn clone_structure(&mut self, id: StructureId) -> StructureId {
        let clone = self.cat.structures[id.0].clone();
        let identity = identity_elmap(&clone);
        let new_id = self.cat.push(clone);
        self.semantic_els.push(BTreeMap::new());
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
/// types the rule is nested inside, outermost first. Argument-count
/// mismatches at resolved pred/func application sites are appended to
/// `errors`. The walker may emit duplicates across re-walks of the same
/// site.
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
    errors: &mut Vec<CompileError>,
) -> bool {
    let mut changed = false;
    let initial = if rule.cat.structures.is_empty() {
        changed = true;
        rule.push_blank()
    } else {
        StructureId(0)
    };
    changed |= ensure_ambient_els(&mut rule.cat.structures[initial.0], enclosing_models);

    let body = ast.rule_decl(rid).body.clone();
    let (_after, walk_changed) =
        walk_stmt_block(&body, initial, rule, ast, scopes, signature, errors);
    changed | walk_changed
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
    errors: &mut Vec<CompileError>,
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
        let (after, stmt_changed) = walk_stmt(*stmt, before, rule, ast, scopes, signature, errors);
        changed |= stmt_changed;
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
    errors: &mut Vec<CompileError>,
) -> (StructureId, bool) {
    match *ast.stmt(stmt) {
        Stmt::If(id) => {
            let (next, mut changed) = ensure_stmt_after(rule, stmt, current);
            let atom = ast.if_stmt(id).atom;
            changed |= walk_if_atom(atom, next, rule, ast, scopes, signature, errors);
            (next, changed)
        }
        Stmt::Then(id) => {
            let (next, mut changed) = ensure_stmt_after(rule, stmt, current);
            let atom = ast.then_stmt(id).atom;
            changed |= walk_then_atom(atom, next, rule, ast, scopes, signature, errors);
            (next, changed)
        }
        Stmt::Branch(id) => {
            let blocks = ast.branch_stmt(id).blocks.clone();
            let mut changed = false;
            for (idx, block) in blocks.iter().enumerate() {
                let (block_start, c1) = ensure_branch_block_start(rule, id, idx, current);
                changed |= c1;
                let (_after, c2) =
                    walk_stmt_block(block, block_start, rule, ast, scopes, signature, errors);
                changed |= c2;
            }
            // The branch's after-structure is a separate clone of the
            // shared before-structure; it receives an inclusion from
            // `current` but is deliberately disconnected from the
            // individual branches.
            // TODO: after_stmt should get a morphism from the
            // intersection of the end structures in each branch.
            let (after, c3) = ensure_stmt_after(rule, stmt, current);
            changed |= c3;
            (after, changed)
        }
        Stmt::Match(id) => {
            let MatchStmt { term, cases } = ast.match_stmt(id);
            let term = *term;
            let cases = cases.clone();
            let (after_scrutinee, mut changed) = ensure_match_after_scrutinee(rule, id, current);
            let (_el, c1) = walk_term(term, after_scrutinee, rule, ast, scopes, signature, errors);
            changed |= c1;
            for case in &cases {
                let MatchCase { pattern, body } = ast.match_case(*case).clone();
                let (case_start, c2) = ensure_match_case_start(rule, *case, after_scrutinee);
                changed |= c2;
                let (_el, c3) =
                    walk_term(pattern, case_start, rule, ast, scopes, signature, errors);
                changed |= c3;
                let (_after, c4) =
                    walk_stmt_block(&body, case_start, rule, ast, scopes, signature, errors);
                changed |= c4;
            }
            // Likewise, the match's after-structure is a fresh clone of
            // `after_scrutinee` (so the scrutinee's effects carry through),
            // disconnected from the case bodies.
            // TODO: after_stmt should get a morphism from the intersection
            // of the end structures in each case.
            let (after, c5) = ensure_stmt_after(rule, stmt, after_scrutinee);
            changed |= c5;
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
    errors: &mut Vec<CompileError>,
) -> bool {
    match *ast.if_atom(atom) {
        IfAtom::Equal(id) => {
            let EqualAtom { lhs, rhs } = *ast.equal_atom(id);
            let (lhs_el, c1) = walk_term(lhs, current, rule, ast, scopes, signature, errors);
            let (rhs_el, c2) = walk_term(rhs, current, rule, ast, scopes, signature, errors);
            let eq = rule.cat.structures[current.0].equate(lhs_el, rhs_el);
            c1 || c2 || eq
        }
        IfAtom::Defined(id) => {
            let DefinedIfAtom { term } = *ast.defined_if_atom(id);
            let (_el, c) = walk_term(term, current, rule, ast, scopes, signature, errors);
            c
        }
        IfAtom::Pred(id) => walk_pred_atom(id, current, rule, ast, scopes, signature, errors),
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
    errors: &mut Vec<CompileError>,
) -> bool {
    match *ast.then_atom(atom) {
        ThenAtom::Equal(id) => {
            let EqualAtom { lhs, rhs } = *ast.equal_atom(id);
            let (lhs_el, c1) = walk_term(lhs, current, rule, ast, scopes, signature, errors);
            let (rhs_el, c2) = walk_term(rhs, current, rule, ast, scopes, signature, errors);
            let eq = rule.cat.structures[current.0].equate(lhs_el, rhs_el);
            c1 || c2 || eq
        }
        ThenAtom::Defined(id) => {
            let DefinedThenAtom { var, term } = *ast.defined_then_atom(id);
            let mut changed = false;
            let var_el = if let Some(v) = var {
                let (e, c) = walk_term(v, current, rule, ast, scopes, signature, errors);
                changed |= c;
                Some(e)
            } else {
                None
            };
            let (term_el, c) = walk_term(term, current, rule, ast, scopes, signature, errors);
            changed |= c;
            if let Some(var_el) = var_el {
                changed |= rule.cat.structures[current.0].equate(var_el, term_el);
            }
            changed
        }
        ThenAtom::Pred(id) => walk_pred_atom(id, current, rule, ast, scopes, signature, errors),
    }
}

fn walk_pred_atom(
    id: PredAtomId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> bool {
    let PredAtom { pred, args } = *ast.pred_atom(id);
    let arg_terms = ast.term_list(args).terms.clone();
    let mut changed = false;
    let arg_els: Vec<ElId> = arg_terms
        .iter()
        .map(|t| {
            let (e, c) = walk_term(*t, current, rule, ast, scopes, signature, errors);
            changed |= c;
            e
        })
        .collect();

    let (resolved, c) = resolve_pred_expr(pred, current, rule, ast, scopes, signature, errors);
    changed |= c;
    let Some((pred_id, parents)) = resolved else {
        return changed;
    };

    let pred_data = signature.pred(pred_id);
    if arg_els.len() != pred_data.arity.len() {
        errors.push(CompileError::PredicateArgumentNumber {
            expected: pred_data.arity.len(),
            got: arg_els.len(),
            location: ast.loc(id),
        });
        return changed;
    }
    let structure = &mut rule.cat.structures[current.0];
    let parents: Vec<ElId> = parents
        .into_iter()
        .map(|e| structure.unification.root(e))
        .collect();
    let canonical_args: Vec<ElId> = arg_els
        .iter()
        .map(|e| structure.unification.root(*e))
        .collect();
    changed |= structure.pred_apps.insert(PredApp {
        pred: pred_id,
        parents,
        args: canonical_args,
    });
    changed
}

/// Resolves a [`PredExpr`] to its [`PredId`] and the parent el chain to
/// emit alongside it on a [`PredApp`].
///
/// For ambient preds the chain comes from the rule's
/// [`Structure::ambient_model_els`], looked up by each parent type. The
/// pred's parent chain is always a sub-chain of the rule's enclosing
/// models — the pred has to be visible to the rule — but it may be
/// strictly shorter: a global pred used in a model rule, or a pred
/// declared on an outer model used in an inner-model rule, both have
/// fewer parents than the rule itself sits inside.
///
/// For member preds the chain is the parent el's [`ConcreteType`]
/// parents with the parent el itself appended, which matches the
/// signature's parent chain for any pred declared inside that model.
/// The bool component is true iff walking the parent term produced a
/// fresh allocation or insertion; ambient resolution never mutates, so
/// it always returns `false` there.
fn resolve_pred_expr(
    pred: PredExprId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> (Option<(PredId, Vec<ElId>)>, bool) {
    match *ast.pred_expr(pred) {
        PredExpr::Ambient(aid) => {
            let scope = scopes.entry(aid);
            let name = &ast.ambient_pred_expr(aid).name;
            let pred_id = match scopes.lookup(scope, name) {
                Some(Symbol::Pred(pd)) => signature.pred_for_pred_decl(pd),
                _ => None,
            };
            let resolved = pred_id.map(|pid| {
                let parents =
                    rule.cat.structures[current.0].ambient_parents(&signature.pred(pid).parents);
                (pid, parents)
            });
            (resolved, false)
        }
        PredExpr::Member(mid) => {
            let MemberPredExpr {
                term: parent_term,
                name,
            } = ast.member_pred_expr(mid).clone();
            let (parent_el, changed) =
                walk_term(parent_term, current, rule, ast, scopes, signature, errors);
            let resolved = member_scope_and_parents(rule, current, parent_el, scopes, signature)
                .and_then(|(body, parents)| {
                    let pd = match body.symbols.get(&name).copied()? {
                        Symbol::Pred(pd) => pd,
                        _ => return None,
                    };
                    let pid = signature.pred_for_pred_decl(pd)?;
                    Some((pid, parents))
                });
            (resolved, changed)
        }
    }
}

/// Walks `term`, materialising any Els it needs in the current
/// structure, records `term -> el` in `semantic_el`, and returns the El.
///
/// `prior_el` is the el this `(current, term)` resolved to on an earlier
/// pass, if any. Reusing it keeps el identity stable across re-walks.
/// `Var` and `Wildcard` reuse it directly; `App` recurses into its
/// arguments and re-attempts func resolution so a previously-unresolvable
/// [`FuncApp`] gets emitted now, while the result el still falls back to
/// `prior_el` when present.
fn walk_term(
    term: TermId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> (ElId, bool) {
    let prior_el = rule.semantic_els[current.0].get(&term).copied();
    let mut changed = false;
    let el = match *ast.term(term) {
        Term::Var(vid) => {
            if let Some(el) = prior_el {
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
            if let Some(el) = prior_el {
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
                    let (e, c) = walk_term(*t, current, rule, ast, scopes, signature, errors);
                    changed |= c;
                    e
                })
                .collect();
            let (e, c) = emit_app(
                aid, func, arg_els, prior_el, current, rule, ast, scopes, signature, errors,
            );
            changed |= c;
            e
        }
        Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
            // TODO: implement once dom/cod/@ operators are defined on
            // the structure side. The current pass was materialising a
            // fresh untyped El, which is wrong.
            todo!()
        }
    };
    if prior_el.is_none() {
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
    app: AppTermId,
    func: FuncExprId,
    arg_els: Vec<ElId>,
    expected: Option<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> (ElId, bool) {
    let (resolved, mut changed) =
        resolve_func_expr(func, current, rule, ast, scopes, signature, errors);

    let Some((func_id, parents)) = resolved else {
        let structure = &mut rule.cat.structures[current.0];
        return match expected {
            Some(el) => (el, changed),
            None => (structure.push_el(), true),
        };
    };

    let func_data = signature.func(func_id);
    if arg_els.len() != func_data.domain.len() {
        errors.push(CompileError::FunctionArgumentNumber {
            expected: func_data.domain.len(),
            got: arg_els.len(),
            location: ast.loc(app),
        });
        let structure = &mut rule.cat.structures[current.0];
        return match expected {
            Some(el) => (el, changed),
            None => (structure.push_el(), true),
        };
    }

    let structure = &mut rule.cat.structures[current.0];

    let parents: Vec<ElId> = parents
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

    let result_id = match structure.func_apps.get(&app_key).copied() {
        Some(existing) => match expected {
            Some(exp) => {
                if exp != existing {
                    changed |= structure.equate(exp, existing);
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
            structure.func_apps.insert(app_key, id);
            // Allocating an el or inserting a new func_app entry is
            // always observable change.
            changed = true;
            id
        }
    };
    (result_id, changed)
}

/// Like [`resolve_pred_expr`] but for [`FuncExpr`]. Member ctors are
/// accepted alongside member funcs; the resulting [`FuncId`] either way
/// is what the [`FuncApp`] should reference.
fn resolve_func_expr(
    func: FuncExprId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> (Option<(FuncId, Vec<ElId>)>, bool) {
    match *ast.func_expr(func) {
        FuncExpr::Ambient(aid) => {
            let scope = scopes.entry(aid);
            let name = &ast.ambient_func_expr(aid).name;
            let func_id = match scopes.lookup(scope, name) {
                Some(Symbol::Func(fd)) => signature.func_for_func_decl(fd),
                Some(Symbol::Ctor(cd)) => signature.func_for_ctor_decl(cd),
                _ => None,
            };
            let resolved = func_id.map(|fid| {
                let parents =
                    rule.cat.structures[current.0].ambient_parents(&signature.func(fid).parents);
                (fid, parents)
            });
            (resolved, false)
        }
        FuncExpr::Member(mid) => {
            let MemberFuncExpr {
                term: parent_term,
                name,
            } = ast.member_func_expr(mid).clone();
            let (parent_el, changed) =
                walk_term(parent_term, current, rule, ast, scopes, signature, errors);
            let resolved = member_scope_and_parents(rule, current, parent_el, scopes, signature)
                .and_then(|(body, parents)| {
                    let fid = match body.symbols.get(&name).copied()? {
                        Symbol::Func(fd) => signature.func_for_func_decl(fd)?,
                        Symbol::Ctor(cd) => signature.func_for_ctor_decl(cd)?,
                        _ => return None,
                    };
                    Some((fid, parents))
                });
            (resolved, changed)
        }
    }
}

/// Looks up `parent_el`'s [`ConcreteType`], resolves it to a model body
/// scope and builds the parent el chain to emit on a member [`PredApp`]
/// or [`FuncApp`]. The chain is the parent el's [`ConcreteType`] parents
/// with the parent el itself appended, matching the signature's
/// enclosing-models chain for any pred/func declared inside that model.
///
/// Returns `None` when `parent_el`'s type is not yet known, or is not a
/// model type. Member resolution failures further down (the model has
/// no symbol of that name, or the symbol is the wrong kind) are the
/// caller's job to report by inspecting the returned [`Scope`].
fn member_scope_and_parents<'a>(
    rule: &RuleStructures,
    current: StructureId,
    parent_el: ElId,
    scopes: &'a Scopes,
    signature: &Signature,
) -> Option<(&'a Scope, Vec<ElId>)> {
    let structure = &rule.cat.structures[current.0];
    let root = structure.unification.root_const(parent_el);
    let ct = structure.els.get(&root)?.clone()?;
    let model_decl = signature.model_decl_for_type(ct.typ)?;
    let body_scope = scopes.unordered(model_decl);
    let mut parents = ct.parents;
    parents.push(parent_el);
    Some((scopes.scope(body_scope), parents))
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
