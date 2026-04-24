//! Walks an AST rule body to fill in a [`RuleStructures`].
//!
//! The walker is idempotent at the statement and term level: if a
//! statement already has an entry in `stmt_after`, its walk is skipped;
//! if a term already has an entry in `semantic_els` for the current
//! structure, the cached element is returned. The initial structure's
//! ambient-model elements are set up on first populate and reused on
//! subsequent calls.

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
    /// fresh [`StructureId`]. Used when a walk is about to mutate an
    /// entry that is already committed to a before/after map.
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
/// morphism into a clone of `s`, which shares the same [`ElId`]s. At
/// populate time no [`Structure::close`] has run yet, so `els` still has
/// one entry per allocated element.
fn identity_elmap(s: &Structure) -> ElMap {
    s.els.keys().map(|&el| (el, el)).collect()
}

/// Populates `rule` with the structures and term mappings derived from
/// walking rule `rid`'s body. `enclosing_models` is the chain of model
/// types the rule is nested inside, outermost first.
pub fn walk_rule(
    rule: &mut RuleStructures,
    rid: RuleDeclId,
    enclosing_models: &[TypeId],
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) {
    let initial = if rule.cat.structures.is_empty() {
        rule.push_blank()
    } else {
        StructureId(0)
    };
    ensure_ambient_els(&mut rule.cat.structures[initial.0], enclosing_models);

    let body = ast.rule_decl(rid).body.clone();
    walk_stmt_block(&body, initial, rule, ast, scopes, signature);
}

/// Walks `stmts` in order. `current` is the id of the structure that
/// represents state just before the next statement; each statement
/// updates it to the id of its after-structure. Skips statements that
/// have already been walked (i.e. already have a `stmt_after`
/// recorded). Returns the final after-id.
fn walk_stmt_block(
    stmts: &[StmtId],
    mut current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> StructureId {
    for stmt in stmts {
        if let Some(&after) = rule.stmt_after.get(stmt) {
            current = after;
            continue;
        }
        let before = *rule.stmt_before.entry(*stmt).or_insert(current);
        let after = walk_stmt(*stmt, before, rule, ast, scopes, signature);
        rule.stmt_after.insert(*stmt, after);
        current = after;
    }
    current
}

fn walk_stmt(
    stmt: StmtId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> StructureId {
    match *ast.stmt(stmt) {
        Stmt::If(id) => {
            // Clone first: `current` is the committed before-structure
            // and must stay immutable.
            let next = rule.clone_structure(current);
            let atom = ast.if_stmt(id).atom;
            walk_if_atom(atom, next, rule, ast, scopes, signature);
            next
        }
        Stmt::Then(id) => {
            let next = rule.clone_structure(current);
            let atom = ast.then_stmt(id).atom;
            walk_then_atom(atom, next, rule, ast, scopes, signature);
            next
        }
        Stmt::Branch(id) => {
            let blocks = ast.branch_stmt(id).blocks.clone();
            for block in &blocks {
                // Each block starts from a clone of the shared
                // before-structure, inclusion from `current`.
                let block_start = rule.clone_structure(current);
                walk_stmt_block(block, block_start, rule, ast, scopes, signature);
            }
            // The after-structure is a separate clone of the
            // before-structure; it receives an inclusion from `current`
            // but is deliberately disconnected from the individual
            // branches.
            // TODO: after_stmt should get a morphism from the
            // intersection of the end structures in each branch.
            rule.clone_structure(current)
        }
        Stmt::Match(id) => {
            let MatchStmt { term, cases } = ast.match_stmt(id);
            let term = *term;
            let cases = cases.clone();
            // Scrutinee is evaluated once, before any case branches.
            let after_scrutinee = rule.clone_structure(current);
            walk_term(term, after_scrutinee, rule, ast, scopes, signature);
            for case in &cases {
                let MatchCase { pattern, body } = ast.match_case(*case).clone();
                let case_start = rule.clone_structure(after_scrutinee);
                walk_term(pattern, case_start, rule, ast, scopes, signature);
                walk_stmt_block(&body, case_start, rule, ast, scopes, signature);
            }
            // Likewise, the match's after-structure is a fresh clone of
            // `after_scrutinee` (so the scrutinee's effects carry through),
            // disconnected from the case bodies.
            // TODO: after_stmt should get a morphism from the intersection
            // of the end structures in each case.
            rule.clone_structure(after_scrutinee)
        }
    }
}

fn walk_if_atom(
    atom: IfAtomId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) {
    match *ast.if_atom(atom) {
        IfAtom::Equal(id) => {
            let EqualAtom { lhs, rhs } = *ast.equal_atom(id);
            let lhs_el = walk_term(lhs, current, rule, ast, scopes, signature);
            let rhs_el = walk_term(rhs, current, rule, ast, scopes, signature);
            rule.cat.structures[current.0].equate(lhs_el, rhs_el);
        }
        IfAtom::Defined(id) => {
            let DefinedIfAtom { term } = *ast.defined_if_atom(id);
            walk_term(term, current, rule, ast, scopes, signature);
        }
        IfAtom::Pred(id) => {
            walk_pred_atom(id, current, rule, ast, scopes, signature);
        }
        IfAtom::Var(id) => {
            let VarIfAtom { term, typ } = *ast.var_if_atom(id);
            // Idempotency: a second visit of the same VarIfAtom finds
            // its term already in semantic_els and skips both the el
            // allocation and the var_els insertion.
            if rule.semantic_els[current.0].contains_key(&term) {
                return;
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
) {
    match *ast.then_atom(atom) {
        ThenAtom::Equal(id) => {
            let EqualAtom { lhs, rhs } = *ast.equal_atom(id);
            let lhs_el = walk_term(lhs, current, rule, ast, scopes, signature);
            let rhs_el = walk_term(rhs, current, rule, ast, scopes, signature);
            rule.cat.structures[current.0].equate(lhs_el, rhs_el);
        }
        ThenAtom::Defined(id) => {
            let DefinedThenAtom { var, term } = *ast.defined_then_atom(id);
            let var_el = var.map(|v| walk_term(v, current, rule, ast, scopes, signature));
            let term_el = walk_term(term, current, rule, ast, scopes, signature);
            if let Some(var_el) = var_el {
                rule.cat.structures[current.0].equate(var_el, term_el);
            }
        }
        ThenAtom::Pred(id) => {
            walk_pred_atom(id, current, rule, ast, scopes, signature);
        }
    }
}

fn walk_pred_atom(
    id: PredAtomId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) {
    let PredAtom { pred, args } = *ast.pred_atom(id);
    let arg_terms = ast.term_list(args).terms.clone();
    let arg_els: Vec<ElId> = arg_terms
        .iter()
        .map(|t| walk_term(*t, current, rule, ast, scopes, signature))
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
        return;
    };

    let pred_data = signature.pred(pred_id);
    if arg_els.len() != pred_data.arity.len() {
        return;
    }
    let structure = &mut rule.cat.structures[current.0];
    let parents = structure.ambient_parents(&pred_data.parents);
    structure.pred_apps.insert(PredApp {
        pred: pred_id,
        parents,
        args: arg_els,
    });
}

/// Walks `term`, materialising any Els it needs in the current
/// structure, records `term -> el` in `semantic_el`, and returns
/// the El. Idempotent: if `term` is already in `semantic_el` for
/// the current structure, returns the cached El without walking
/// sub-terms or touching the structure.
fn walk_term(
    term: TermId,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> ElId {
    if let Some(&el) = rule.semantic_els[current.0].get(&term) {
        return el;
    }
    let el = match *ast.term(term) {
        Term::Var(vid) => {
            let name = ast.var_term(vid).name.clone();
            let structure = &mut rule.cat.structures[current.0];
            if let Some(&el_id) = structure.var_els.get(&name) {
                el_id
            } else {
                let el_id = structure.push_el();
                structure.var_els.insert(name, el_id);
                el_id
            }
        }
        Term::Wildcard => rule.cat.structures[current.0].push_el(),
        Term::App(aid) => {
            let AppTerm { func, args } = *ast.app_term(aid);
            let arg_terms = ast.term_list(args).terms.clone();
            let arg_els: Vec<ElId> = arg_terms
                .iter()
                .map(|t| walk_term(*t, current, rule, ast, scopes, signature))
                .collect();
            emit_app(func, arg_els, current, rule, ast, scopes, signature)
        }
        Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
            // TODO: implement once dom/cod/@ operators are defined on
            // the structure side. The current pass was materialising a
            // fresh untyped El, which is wrong.
            todo!()
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
    func: FuncExprId,
    arg_els: Vec<ElId>,
    current: StructureId,
    rule: &mut RuleStructures,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
) -> ElId {
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

    let Some(func_id) = resolved else {
        return rule.cat.structures[current.0].push_el();
    };

    let func_data = signature.func(func_id);
    if arg_els.len() != func_data.domain.len() {
        return rule.cat.structures[current.0].push_el();
    }

    let codomain = func_data.codomain;
    let structure = &mut rule.cat.structures[current.0];
    let parents = structure.ambient_parents(&func_data.parents);
    let result_ct = concrete_type_for(signature, Some(codomain), structure);
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
/// model type. Idempotent via the count-equals-expected check.
fn ensure_ambient_els(init: &mut Structure, enclosing_models: &[TypeId]) {
    if init.ambient_model_els.len() == enclosing_models.len() {
        return;
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
}
