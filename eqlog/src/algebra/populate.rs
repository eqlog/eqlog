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
use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::{FuncId, PredId, Signature, TypeId, TypeKind};
use crate::algebra::structure::{
    ConcreteType, ElId, ElMap, FuncApp, PredApp, Structure, StructureCat, StructureId,
};
use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::{Scope, ScopeId, Scopes, Symbol};

/// Origin tag for the morphism associated with a statement. Mirrors
/// `if_morphism`, `surj_then_morphism`, `non_surj_then_morphism` and
/// `noop_morphism` in `eqlog.eql`. A property of how the morphism arose
/// from the AST, not an algebraic property of the morphism itself.
/// Surjectivity in particular is not essentially-algebraic.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MorphismKind {
    /// `if`-stmt morphism. Source embeds into target. Target may have
    /// new elements (existentially quantified).
    If,
    /// `then`-equal or `then`-pred atom morphism. Target shares the
    /// source's elements. Only equalities and predicate insertions
    /// distinguish them.
    SurjThen,
    /// `then`-defined atom morphism. Target may introduce one new
    /// element (the result of the defined term).
    NonSurjThen,
    /// `branch`-stmt or `match`-stmt after-morphism. A clone-with-identity
    /// from `top` to `meet`; the saturation pass driven by
    /// `StructureCat::under_prods` is what actually fills `meet`.
    Noop,
}

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
    /// Intermediate member prefixes in application heads are not terms, but
    /// valid constant prefixes still denote elements during algebraization.
    pub app_head_els: Vec<BTreeMap<(AppHeadMemberId, usize), ElId>>,
    pub stmt_before: BTreeMap<StmtId, StructureId>,
    pub stmt_after: BTreeMap<StmtId, StructureId>,
    /// Origin tag for each statement's morphism, keyed by the
    /// `(stmt_before, stmt_after)` endpoints that index into
    /// `cat.morphisms`. Only statement-level morphisms appear here.
    /// The auxiliary morphisms into `branch_block_starts`,
    /// `match_after_scrutinee` and `match_case_starts` are deliberately
    /// untagged (they have no analogue in `eqlog.eql`'s tagging).
    pub morphism_kinds: BTreeMap<(StructureId, StructureId), MorphismKind>,
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
        self.app_head_els.push(BTreeMap::new());
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
        self.app_head_els.push(BTreeMap::new());
        self.cat.add_morphism(id, new_id, identity);
        new_id
    }
}

/// Identity map on every element of `s`. Suitable for the inclusion
/// morphism into a clone of `s`, which shares the same [`ElId`]s.
fn identity_elmap(s: &Structure) -> ElMap {
    s.els.keys().map(|&el| (el, el)).collect()
}

/// Registers the projection morphisms `meet -> end_i` and the
/// [`UnderProd`] entry that ties `meet` to its `top` and the `end_i`s.
/// Each projection starts as the identity on `meet`'s elements: both
/// sides descend from `top` via clones so their inherited [`ElId`]s
/// coincide.
fn register_under_prod_projections(
    rule: &mut RuleStructures,
    top: StructureId,
    meet: StructureId,
    ends: &[StructureId],
) {
    for &end in ends {
        let map = identity_elmap(&rule.cat.structures[meet.0]);
        rule.cat.add_morphism(meet, end, map);
    }
    rule.cat.add_under_prod(top, meet, ends.to_vec());
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
            let (next, mut changed) = ensure_stmt_after(rule, stmt, current, MorphismKind::If);
            let atom = ast.if_stmt(id).atom;
            changed |= walk_if_atom(atom, next, rule, ast, scopes, signature, errors);
            (next, changed)
        }
        Stmt::Then(id) => {
            let atom = ast.then_stmt(id).atom;
            let kind = match *ast.then_atom(atom) {
                ThenAtom::Equal(_) | ThenAtom::Pred(_) => MorphismKind::SurjThen,
                ThenAtom::Defined(_) => MorphismKind::NonSurjThen,
            };
            let (next, mut changed) = ensure_stmt_after(rule, stmt, current, kind);
            changed |= walk_then_atom(atom, next, rule, ast, scopes, signature, errors);
            (next, changed)
        }
        Stmt::Branch(id) => {
            let blocks = ast.branch_stmt(id).blocks.clone();
            // Pre-allocate the after-structure before walking the blocks
            // so its arena id precedes each block-end's. This satisfies
            // the forward-pointing invariant for the projection morphisms
            // `after -> block_end_i` registered below.
            let (after, after_was_new) = ensure_stmt_after(rule, stmt, current, MorphismKind::Noop);
            let mut changed = after_was_new;
            let mut block_ends: Vec<StructureId> = Vec::with_capacity(blocks.len());
            for (idx, block) in blocks.iter().enumerate() {
                let (block_start, c1) = ensure_branch_block_start(rule, id, idx, current);
                changed |= c1;
                let (block_end, c2) =
                    walk_stmt_block(block, block_start, rule, ast, scopes, signature, errors);
                changed |= c2;
                block_ends.push(block_end);
            }
            if after_was_new {
                register_under_prod_projections(rule, current, after, &block_ends);
            }
            (after, changed)
        }
        Stmt::Match(id) => {
            let MatchStmt { term, cases } = ast.match_stmt(id);
            let term = *term;
            let cases = cases.clone();
            let (after_scrutinee, mut changed) = ensure_match_after_scrutinee(rule, id, current);
            let (term_el, c1) =
                walk_term(term, after_scrutinee, rule, ast, scopes, signature, errors);
            changed |= c1;
            // Same pre-allocation pattern as for `Branch`: the match's
            // after-structure must precede every case-end in arena order
            // so the projection morphisms point forward.
            let (after, after_was_new) =
                ensure_stmt_after(rule, stmt, after_scrutinee, MorphismKind::Noop);
            changed |= after_was_new;
            let mut case_ends: Vec<StructureId> = Vec::with_capacity(cases.len());
            for case in &cases {
                let MatchCase { pattern, body } = ast.match_case(*case).clone();
                let (case_start, c2) = ensure_match_case_start(rule, *case, after_scrutinee);
                changed |= c2;
                let (pattern_el, c3) =
                    walk_term(pattern, case_start, rule, ast, scopes, signature, errors);
                changed |= c3;
                changed |= rule.cat.structures[case_start.0].equate(term_el, pattern_el);
                let (case_end, c4) =
                    walk_stmt_block(&body, case_start, rule, ast, scopes, signature, errors);
                changed |= c4;
                case_ends.push(case_end);
            }
            if after_was_new {
                register_under_prod_projections(rule, after_scrutinee, after, &case_ends);
            }
            (after, changed)
        }
    }
}

/// Returns the structure recorded as `stmt_after[stmt]`, allocating a clone
/// of `src` for it on the first visit and tagging the resulting morphism
/// with `kind`. The bool indicates whether a fresh clone was created.
fn ensure_stmt_after(
    rule: &mut RuleStructures,
    stmt: StmtId,
    src: StructureId,
    kind: MorphismKind,
) -> (StructureId, bool) {
    if let Some(&id) = rule.stmt_after.get(&stmt) {
        return (id, false);
    }
    let id = rule.clone_structure(src);
    rule.stmt_after.insert(stmt, id);
    rule.morphism_kinds.insert((src, id), kind);
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
            // Resolve the annotation first: a member type expr walks its
            // parent term, which must run on every pass so it gets re-tried
            // once the parent's type becomes known. Ambient/Mor cases
            // resolve immediately and don't mutate the structure.
            let (cts, mut changed) =
                walk_var_type_expr(typ, current, rule, ast, scopes, signature, errors);
            let (el_id, c) = walk_term(term, current, rule, ast, scopes, signature, errors);
            changed |= c;
            // Queue the annotations for the close pass to apply. A member
            // annotation may stay unresolved until a later pass settles
            // its parent's type; until then the el simply has no concrete
            // type, like any unannotated el.
            for ct in cts {
                changed |= rule.cat.structures[current.0].impose_type(el_id, ct);
            }
            changed
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
            let var_el = if let Some(var) = var {
                let (e, c) = walk_term(var, current, rule, ast, scopes, signature, errors);
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
    if resolved.is_empty() {
        return changed;
    }

    for (pred_id, parents) in resolved {
        let pred_data = signature.pred(pred_id);
        if arg_els.len() != pred_data.arity.len() {
            errors.push(CompileError::PredicateArgumentNumber {
                expected: pred_data.arity.len(),
                got: arg_els.len(),
                location: ast.loc(id),
            });
            continue;
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
    }
    changed
}

/// Resolves a [`PredExpr`] to the [`PredId`] and parent el chain candidates
/// to emit alongside it on [`PredApp`]s.
///
/// For ambient preds the chain comes from the rule's
/// [`Structure::ambient_model_els`], looked up by each parent type. The
/// pred's parent chain is always a sub-chain of the rule's enclosing
/// models — the pred has to be visible to the rule — but it may be
/// strictly shorter: a global pred used in a model rule, or a pred
/// declared on an outer model used in an inner-model rule, both have
/// fewer parents than the rule itself sits inside.
///
/// For member preds each chain is the parent el's [`ConcreteType`]
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
) -> (Vec<(PredId, Vec<ElId>)>, bool) {
    match *ast.pred_expr(pred) {
        PredExpr::Ambient(aid) => {
            let scope = scopes.entry(aid);
            let name = &ast.ambient_pred_expr(aid).name;
            let pred_id = match lookup_decl(scopes, scope, name) {
                Some(Symbol::Pred(pd)) => signature.pred_for_pred_decl(pd),
                _ => None,
            };
            let resolved = pred_id
                .map(|pid| {
                    let parents = rule.cat.structures[current.0]
                        .ambient_parents(&signature.pred(pid).parents);
                    vec![(pid, parents)]
                })
                .unwrap_or_default();
            (resolved, false)
        }
        PredExpr::Member(mid) => {
            let TermMember {
                term: parent_term,
                name,
            } = *ast.term_member(mid);
            let name = ast.ident_term(name).name.clone();
            let (parent_el, changed) =
                walk_term(parent_term, current, rule, ast, scopes, signature, errors);
            let resolved = member_scopes_and_parents(rule, current, parent_el, scopes, signature)
                .into_iter()
                .filter_map(|(body, parents)| {
                    let pd = match body.symbols.get(&name).copied()? {
                        Symbol::Pred(pd) => pd,
                        _ => return None,
                    };
                    let pid = signature.pred_for_pred_decl(pd)?;
                    Some((pid, parents))
                })
                .collect();
            (resolved, changed)
        }
    }
}

/// Walks `term`, materialising any Els it needs in the current
/// structure, records `term -> el` in `semantic_el`, and returns the El.
///
/// `prior_el` is the el this `(current, term)` resolved to on an earlier
/// pass, if any. Reusing it keeps el identity stable across re-walks.
/// Identifier terms resolve through [`Scopes`] to either a variable binding
/// or ambient const app. `Wildcard` reuses `prior_el` directly; `App`
/// recurses into its arguments and re-attempts func resolution so a
/// previously-unresolvable [`FuncApp`] gets emitted now, while the result el
/// still falls back to `prior_el` when present.
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
        Term::Ident(id) => {
            let name = &ast.ident_term(id).name;
            match scopes.lookup(scopes.exit(term), name) {
                Some(Symbol::Var(binding)) => {
                    let (el, c) = ensure_var_binding_el(binding, current, rule, ast);
                    changed |= c;
                    el
                }
                Some(Symbol::Const(const_decl)) => {
                    let Some(func_id) = signature.func_for_const_decl(const_decl) else {
                        let (e, c) = expected_or_fresh(prior_el, current, rule);
                        changed |= c;
                        return (e, changed);
                    };
                    let parents = rule.cat.structures[current.0]
                        .ambient_parents(&signature.func(func_id).parents);
                    let (e, c) =
                        emit_known_app(func_id, parents, Vec::new(), prior_el, current, rule);
                    changed |= c;
                    e
                }
                _ => {
                    let (e, c) = expected_or_fresh(prior_el, current, rule);
                    changed |= c;
                    e
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
            let AppTerm { head, args } = *ast.app_term(aid);
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
                aid, head, arg_els, prior_el, current, rule, ast, scopes, signature, errors,
            );
            changed |= c;
            e
        }
        Term::Member(mid) => {
            let TermMember {
                term: receiver,
                name,
            } = *ast.term_member(mid);
            let (receiver_el, c) =
                walk_term(receiver, current, rule, ast, scopes, signature, errors);
            changed |= c;
            let const_name = ast.ident_term(name).name.clone();
            let candidates =
                member_scopes_and_parents(rule, current, receiver_el, scopes, signature)
                    .into_iter()
                    .filter_map(|(body, parents)| {
                        let Symbol::Const(const_decl) = body.symbols.get(&const_name).copied()?
                        else {
                            return None;
                        };
                        let fid = signature.func_for_const_decl(const_decl)?;
                        Some((fid, parents))
                    })
                    .collect();
            match emit_known_apps(candidates, Vec::new(), prior_el, current, rule) {
                Some((e, c)) => {
                    changed |= c;
                    e
                }
                None => {
                    let (e, c) = expected_or_fresh(prior_el, current, rule);
                    changed |= c;
                    e
                }
            }
        }
        Term::Dom(did) => {
            let DomTerm { arg } = *ast.dom_term(did);
            let (arg_el, c) = walk_term(arg, current, rule, ast, scopes, signature, errors);
            changed |= c;
            let candidates = resolve_mor_projection_apps(
                MorProjection::Dom,
                arg_el,
                prior_el,
                current,
                rule,
                signature,
            );
            match emit_known_apps(candidates, vec![arg_el], prior_el, current, rule) {
                Some((e, c)) => {
                    changed |= c;
                    e
                }
                None => {
                    let (e, c) = expected_or_fresh(prior_el, current, rule);
                    changed |= c;
                    e
                }
            }
        }
        Term::Cod(cid) => {
            let CodTerm { arg } = *ast.cod_term(cid);
            let (arg_el, c) = walk_term(arg, current, rule, ast, scopes, signature, errors);
            changed |= c;
            let candidates = resolve_mor_projection_apps(
                MorProjection::Cod,
                arg_el,
                prior_el,
                current,
                rule,
                signature,
            );
            match emit_known_apps(candidates, vec![arg_el], prior_el, current, rule) {
                Some((e, c)) => {
                    changed |= c;
                    e
                }
                None => {
                    let (e, c) = expected_or_fresh(prior_el, current, rule);
                    changed |= c;
                    e
                }
            }
        }
    };
    if prior_el.is_none() {
        rule.semantic_els[current.0].insert(term, el);
        changed = true;
    }
    (el, changed)
}

fn ensure_var_binding_el(
    binding: IdentTermId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
) -> (ElId, bool) {
    let name = &ast.ident_term(binding).name;
    let structure = &mut rule.cat.structures[current.0];
    if let Some(&el_id) = structure.var_els.get(name) {
        return (el_id, false);
    }

    let el_id = structure.push_el();
    structure.var_els.insert(name.clone(), el_id);
    (el_id, true)
}

#[derive(Copy, Clone)]
enum MorProjection {
    Dom,
    Cod,
}

/// Resolves every generated `dom`/`cod` function currently implied for a
/// term. The projection can be determined either from the argument's known
/// `Mor<M>` types or from the result element's known model types.
fn resolve_mor_projection_apps(
    projection: MorProjection,
    arg_el: ElId,
    result_el: Option<ElId>,
    current: StructureId,
    rule: &RuleStructures,
    signature: &Signature,
) -> Vec<(FuncId, Vec<ElId>)> {
    let mut apps = BTreeSet::new();
    for ct in concrete_types_of_el(rule, current, arg_el) {
        if let TypeKind::Mor(model_tid) = signature.type_(ct.typ).kind {
            let Some(ids) = signature.ids_for_model_type(model_tid) else {
                continue;
            };
            let func = match projection {
                MorProjection::Dom => ids.dom,
                MorProjection::Cod => ids.cod,
            };
            apps.insert((func, ct.parents));
        }
    }

    if let Some(result_el) = result_el {
        for ct in concrete_types_of_el(rule, current, result_el) {
            let Some(ids) = signature.ids_for_model_type(ct.typ) else {
                continue;
            };
            let func = match projection {
                MorProjection::Dom => ids.dom,
                MorProjection::Cod => ids.cod,
            };
            apps.insert((func, ct.parents));
        }
    }

    apps.into_iter().collect()
}

pub(crate) fn mor_type_component(
    scopes: &Scopes,
    signature: &Signature,
    receiver_typ: TypeId,
    name: &str,
) -> Option<TypeId> {
    let TypeKind::Mor(model_tid) = signature.type_(receiver_typ).kind else {
        return None;
    };
    let model_decl = signature.model_decl_for_type(model_tid)?;
    let body = scopes.scope(scopes.unordered(model_decl));
    match body.symbols.get(name).copied()? {
        Symbol::Type(td) => Some(signature.type_for_type_decl(td)),
        Symbol::Enum(ed) => Some(signature.type_for_enum_decl(ed)),
        Symbol::Model(md) => Some(signature.ids_for_model_decl(md).type_),
        Symbol::Pred(_)
        | Symbol::Func(_)
        | Symbol::Const(_)
        | Symbol::Ctor(_)
        | Symbol::Rule(_)
        | Symbol::Arg(_)
        | Symbol::Var(_) => None,
    }
}

pub(crate) fn mor_type_path_component(
    scopes: &Scopes,
    signature: &Signature,
    receiver_typ: TypeId,
    names: &[&str],
) -> Option<TypeId> {
    let mut model_tid = match signature.type_(receiver_typ).kind {
        TypeKind::Mor(model_tid) => model_tid,
        TypeKind::Plain | TypeKind::Model | TypeKind::Enum => return None,
    };
    let mut resolved = None;
    for (index, name) in names.iter().enumerate() {
        let model_decl = signature.model_decl_for_type(model_tid)?;
        let body = scopes.scope(scopes.unordered(model_decl));
        let typ = match body.symbols.get(*name).copied()? {
            Symbol::Type(td) => signature.type_for_type_decl(td),
            Symbol::Enum(ed) => signature.type_for_enum_decl(ed),
            Symbol::Model(md) => signature.ids_for_model_decl(md).type_,
            Symbol::Pred(_)
            | Symbol::Func(_)
            | Symbol::Const(_)
            | Symbol::Ctor(_)
            | Symbol::Rule(_)
            | Symbol::Arg(_)
            | Symbol::Var(_) => return None,
        };
        resolved = Some(typ);
        if index + 1 < names.len() {
            match signature.type_(typ).kind {
                TypeKind::Model => model_tid = typ,
                TypeKind::Plain | TypeKind::Enum | TypeKind::Mor(_) => return None,
            }
        }
    }
    resolved
}

fn concrete_types_of_el(
    rule: &RuleStructures,
    current: StructureId,
    el: ElId,
) -> Vec<ConcreteType> {
    rule.cat.structures[current.0].concrete_types_of(el)
}

fn expected_or_fresh(
    expected: Option<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
) -> (ElId, bool) {
    match expected {
        Some(el) => (el, false),
        None => (rule.cat.structures[current.0].push_el(), true),
    }
}

/// Emits an application of a generated function whose id and parent chain have
/// already been resolved.
fn emit_known_app(
    func_id: FuncId,
    parents: Vec<ElId>,
    arg_els: Vec<ElId>,
    expected: Option<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
) -> (ElId, bool) {
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

    match structure.func_apps.get(&app_key).copied() {
        Some(existing) => match expected {
            Some(exp) => {
                let changed = exp != existing && structure.equate(exp, existing);
                (exp, changed)
            }
            None => (existing, false),
        },
        None => {
            let (result, _allocated) = expected_or_fresh(expected, current, rule);
            rule.cat.structures[current.0]
                .func_apps
                .insert(app_key, result);
            (result, true)
        }
    }
}

fn emit_known_apps(
    candidates: Vec<(FuncId, Vec<ElId>)>,
    arg_els: Vec<ElId>,
    expected: Option<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
) -> Option<(ElId, bool)> {
    if candidates.is_empty() {
        return None;
    }

    let mut result = expected;
    let mut changed = false;
    for (func_id, parents) in candidates {
        let (el, c) = emit_known_app(func_id, parents, arg_els.clone(), result, current, rule);
        changed |= c;
        if result.is_none() {
            result = Some(el);
        }
    }

    result.map(|el| (el, changed))
}

/// Resolves the application of `head` to `arg_els` and emits the corresponding
/// [`FuncApp`]s.
///
/// Non-callee heads are still walked so nested terms are populated.
///
/// `expected` is the result el previously committed for this term, if any.
/// Returns `(result_el, changed)`.
fn emit_app(
    app: AppTermId,
    head: AppHeadId,
    arg_els: Vec<ElId>,
    expected: Option<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> (ElId, bool) {
    let mut changed = false;
    let mut func_candidates: Vec<(FuncId, Vec<ElId>)> = Vec::new();
    let mut mor_candidates: BTreeSet<(FuncId, Vec<ElId>)> = BTreeSet::new();
    let mut mor_el: Option<ElId> = None;

    match *ast.app_head(head) {
        AppHead::Ident(id) => {
            let name = &ast.ident_term(id).name;
            // Use exit scope: head idents never introduce bindings, so entry
            // and exit coincide, but exit is the canonical lookup site for
            // value names elsewhere.
            let func_id = match scopes.lookup(scopes.exit(head), name) {
                Some(Symbol::Func(fd)) => signature.func_for_func_decl(fd),
                Some(Symbol::Ctor(cd)) => signature.func_for_ctor_decl(cd),
                Some(Symbol::Var(_))
                | Some(Symbol::Const(_))
                | Some(Symbol::Arg(_))
                | Some(Symbol::Type(_))
                | Some(Symbol::Pred(_))
                | Some(Symbol::Enum(_))
                | Some(Symbol::Model(_))
                | Some(Symbol::Rule(_))
                | None => None,
            };
            if let Some(fid) = func_id {
                let parents =
                    rule.cat.structures[current.0].ambient_parents(&signature.func(fid).parents);
                func_candidates.push((fid, parents));
            }
        }
        AppHead::Member(mid) => {
            let member = ast.app_head_member(mid);
            let receiver_el = walk_term(
                member.receiver,
                current,
                rule,
                ast,
                scopes,
                signature,
                errors,
            );
            changed |= receiver_el.1;
            let mut receiver_el = receiver_el.0;
            let receiver_types = concrete_types_of_el(rule, current, receiver_el);
            let unresolved_path = member.names.len() > 1 && receiver_types.is_empty();
            let path_names: Vec<&str> = member
                .names
                .iter()
                .map(|name| ast.ident_term(*name).name.as_str())
                .collect();
            for ct in receiver_types {
                let parent_model = match signature.type_(ct.typ).kind {
                    TypeKind::Mor(parent_model) => parent_model,
                    TypeKind::Plain | TypeKind::Model | TypeKind::Enum => continue,
                };
                let Some(type_tid) =
                    mor_type_path_component(scopes, signature, ct.typ, path_names.as_slice())
                else {
                    continue;
                };
                let Some(fid) = signature.mor_app_func(parent_model, type_tid) else {
                    continue;
                };
                mor_candidates.insert((fid, ct.parents));
                mor_el = Some(receiver_el);
            }
            if mor_candidates.is_empty() && !unresolved_path {
                for (index, &prefix_name) in
                    member.names[..member.names.len() - 1].iter().enumerate()
                {
                    let const_name = &ast.ident_term(prefix_name).name;
                    let candidates =
                        member_scopes_and_parents(rule, current, receiver_el, scopes, signature)
                            .into_iter()
                            .filter_map(|(body, parents)| {
                                let const_decl = match body.symbols.get(const_name).copied()? {
                                    Symbol::Const(const_decl) => const_decl,
                                    Symbol::Type(_)
                                    | Symbol::Pred(_)
                                    | Symbol::Func(_)
                                    | Symbol::Enum(_)
                                    | Symbol::Ctor(_)
                                    | Symbol::Model(_)
                                    | Symbol::Rule(_)
                                    | Symbol::Arg(_)
                                    | Symbol::Var(_) => return None,
                                };
                                let fid = signature.func_for_const_decl(const_decl)?;
                                Some((fid, parents))
                            })
                            .collect();
                    let key = (mid, index);
                    let prior = rule.app_head_els[current.0].get(&key).copied();
                    let (prefix_el, c) =
                        match emit_known_apps(candidates, Vec::new(), prior, current, rule) {
                            Some(result) => result,
                            None => expected_or_fresh(prior, current, rule),
                        };
                    changed |= c;
                    if prior.is_none() {
                        rule.app_head_els[current.0].insert(key, prefix_el);
                        changed = true;
                    }
                    receiver_el = prefix_el;
                }
                let name = *member.names.last().expect("member head without a name");
                let name = &ast.ident_term(name).name;
                for (body, parents) in
                    member_scopes_and_parents(rule, current, receiver_el, scopes, signature)
                {
                    let func_id = match body.symbols.get(name).copied() {
                        Some(Symbol::Func(fd)) => signature.func_for_func_decl(fd),
                        Some(Symbol::Ctor(cd)) => signature.func_for_ctor_decl(cd),
                        Some(Symbol::Const(_))
                        | Some(Symbol::Type(_))
                        | Some(Symbol::Pred(_))
                        | Some(Symbol::Enum(_))
                        | Some(Symbol::Model(_))
                        | Some(Symbol::Rule(_))
                        | Some(Symbol::Arg(_))
                        | Some(Symbol::Var(_))
                        | None => None,
                    };
                    if let Some(fid) = func_id {
                        func_candidates.push((fid, parents));
                    }
                }
                for ct in concrete_types_of_el(rule, current, receiver_el) {
                    let Some(type_tid) = mor_type_component(scopes, signature, ct.typ, name) else {
                        continue;
                    };
                    let Some(fid) = signature.mor_app_func_for_type(type_tid) else {
                        continue;
                    };
                    mor_candidates.insert((fid, ct.parents));
                    mor_el = Some(receiver_el);
                }
            }
        }
        AppHead::Term(term) => {
            let (_, c) = walk_term(term, current, rule, ast, scopes, signature, errors);
            changed |= c;
        }
    }

    let mut result = expected;
    for (func_id, parents) in func_candidates {
        let func_data = signature.func(func_id);
        if arg_els.len() != func_data.domain.len() {
            errors.push(CompileError::FunctionArgumentNumber {
                expected: func_data.domain.len(),
                got: arg_els.len(),
                location: ast.loc(app),
            });
            continue;
        }

        let (el, c) = emit_known_app(func_id, parents, arg_els.clone(), result, current, rule);
        changed |= c;
        if result.is_none() {
            result = Some(el);
        }
    }

    if !mor_candidates.is_empty() {
        if arg_els.len() != 1 {
            errors.push(CompileError::MorphismArgumentNumber {
                got: arg_els.len(),
                location: ast.loc(app),
            });
        } else if let Some(mor_el) = mor_el {
            if let Some((el, c)) = emit_known_apps(
                mor_candidates.into_iter().collect(),
                vec![mor_el, arg_els[0]],
                result,
                current,
                rule,
            ) {
                changed |= c;
                if result.is_none() {
                    result = Some(el);
                }
            }
        }
    }

    let (el, c) = expected_or_fresh(result, current, rule);
    (el, changed | c)
}

/// Looks up every model [`ConcreteType`] on `parent_el`, resolves each to a
/// model body scope, and builds the parent el chain to emit on a member
/// [`PredApp`] or [`FuncApp`]. Each chain is the parent el's
/// [`ConcreteType`] parents with the parent el itself appended, matching
/// the signature's enclosing-models chain for any pred/func declared inside
/// that model.
///
/// Returns no entries when `parent_el`'s type is not yet known, or is not a
/// model type. Member resolution failures further down (the model has
/// no symbol of that name, or the symbol is the wrong kind) are the
/// caller's job to report by inspecting the returned [`Scope`].
fn member_scopes_and_parents<'a>(
    rule: &RuleStructures,
    current: StructureId,
    parent_el: ElId,
    scopes: &'a Scopes,
    signature: &Signature,
) -> Vec<(&'a Scope, Vec<ElId>)> {
    let structure = &rule.cat.structures[current.0];
    structure
        .concrete_types_of(parent_el)
        .into_iter()
        .filter_map(|ct| {
            let model_decl = signature.model_decl_for_type(ct.typ)?;
            let body_scope = scopes.unordered(model_decl);
            let mut parents = ct.parents;
            parents.push(parent_el);
            Some((scopes.scope(body_scope), parents))
        })
        .collect()
}

/// Resolves a [`TypeExprId`] in a var-if-atom annotation position to the
/// [`ConcreteType`]s it imposes on the annotated el. Returns no entries when
/// resolution fails or, for a member type, when the parent's type is
/// not yet known. The bool reports whether walking the parent term
/// produced an allocation.
fn walk_var_type_expr(
    type_expr: TypeExprId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) -> (Vec<ConcreteType>, bool) {
    let scope: ScopeId = scopes.entry(type_expr);
    match *ast.type_expr(type_expr) {
        TypeExpr::Ambient(id) => {
            let name = &ast.ambient_type_expr(id).name;
            let tid = match lookup_decl(scopes, scope, name) {
                Some(Symbol::Type(td)) => Some(signature.type_for_type_decl(td)),
                Some(Symbol::Enum(ed)) => Some(signature.type_for_enum_decl(ed)),
                Some(Symbol::Model(md)) => Some(signature.ids_for_model_decl(md).type_),
                _ => None,
            };
            let structure = &rule.cat.structures[current.0];
            (
                concrete_type_for(signature, tid, structure)
                    .into_iter()
                    .collect(),
                false,
            )
        }
        TypeExpr::Mor(id) => {
            let name = &ast.mor_type_expr(id).name;
            let tid = match lookup_decl(scopes, scope, name) {
                Some(Symbol::Model(md)) => Some(signature.ids_for_model_decl(md).mor),
                _ => None,
            };
            let structure = &rule.cat.structures[current.0];
            (
                concrete_type_for(signature, tid, structure)
                    .into_iter()
                    .collect(),
                false,
            )
        }
        TypeExpr::Member(mid) => {
            let TermMember {
                term: parent_term,
                name,
            } = *ast.term_member(mid);
            let name = ast.ident_term(name).name.clone();
            let (parent_el, changed) =
                walk_term(parent_term, current, rule, ast, scopes, signature, errors);
            let resolved = member_scopes_and_parents(rule, current, parent_el, scopes, signature)
                .into_iter()
                .filter_map(|(body, parents)| {
                    let tid = match body.symbols.get(&name).copied()? {
                        Symbol::Type(td) => signature.type_for_type_decl(td),
                        Symbol::Enum(ed) => signature.type_for_enum_decl(ed),
                        Symbol::Model(md) => signature.ids_for_model_decl(md).type_,
                        _ => return None,
                    };
                    Some(ConcreteType { typ: tid, parents })
                })
                .collect();
            (resolved, changed)
        }
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

fn lookup_decl(scopes: &Scopes, scope: ScopeId, name: &str) -> Option<Symbol> {
    scopes.lookup(scope, name)
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
        init.insert_concrete_type_fact(
            el_id,
            ConcreteType {
                typ: model_tid,
                parents: parents.clone(),
            },
        );
        init.ambient_model_els.insert(model_tid, el_id);
        parents.push(el_id);
    }
    true
}
