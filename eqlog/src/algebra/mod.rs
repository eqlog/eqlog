//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! [`signature`] builds the dependent signature (types, preds, funcs) from
//! the AST. [`structure`] holds the per-rule and per-statement structure
//! data, including the close pass that saturates it under functionality and
//! signature-imposed typing. [`populate`] walks the AST rule bodies to fill
//! in each [`RuleStructures`]. Future passes (morphism construction) will
//! live alongside them.

pub mod populate;
pub mod signature;
pub mod structure;

use std::collections::BTreeMap;

use crate::algebra::populate::{walk_rule, RuleStructures};
use crate::algebra::signature::{Signature, TypeId};
use crate::algebra::structure::{ConcreteType, ElId, Structure, TypeConflict};
use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::Scopes;

/// One rule declaration together with the chain of model types it is
/// nested inside, outermost first.
struct RuleNode {
    rid: RuleDeclId,
    enclosing_models: Vec<TypeId>,
}

/// Builds and closes a [`RuleStructures`] for every rule reachable from
/// `module`. Bails on the first rule whose close pass reports conflicts.
pub fn build_structures(
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    module: ModuleId,
) -> Result<BTreeMap<RuleDeclId, RuleStructures>, Vec<CompileError>> {
    let mut rule_nodes = Vec::new();
    let decls = ast.module(module).decls.clone();
    collect_rules(ast, signature, &decls, &[], &mut rule_nodes);

    let mut rules = BTreeMap::new();
    for RuleNode {
        rid,
        enclosing_models,
    } in rule_nodes
    {
        let mut rule = RuleStructures::default();
        let mut last_conflicts;
        loop {
            let walk_changed = walk_rule(&mut rule, rid, &enclosing_models, ast, scopes, signature);
            let (close_changed, conflicts) = rule.cat.close(signature);
            last_conflicts = conflicts;
            if !walk_changed && !close_changed {
                break;
            }
        }

        if !last_conflicts.is_empty() {
            let errors: Vec<CompileError> = last_conflicts
                .into_iter()
                .map(|(sid, conflict)| {
                    conflict_to_error(
                        ast,
                        signature,
                        &rule.cat.structures[sid.0],
                        &rule.semantic_els[sid.0],
                        conflict,
                    )
                })
                .collect();
            return Err(errors);
        }

        let prev = rules.insert(rid, rule);
        assert!(prev.is_none(), "rule {rid:?} visited twice in decl tree");
    }
    Ok(rules)
}

/// Walks `decls` and appends one [`RuleNode`] per rule declaration
/// encountered, in source order. Recurses into nested model bodies,
/// extending `enclosing_models` with each model's type.
fn collect_rules(
    ast: &Ast,
    signature: &Signature,
    decls: &[DeclId],
    enclosing_models: &[TypeId],
    out: &mut Vec<RuleNode>,
) {
    for decl in decls {
        match *ast.decl(*decl) {
            Decl::Rule(rid) => out.push(RuleNode {
                rid,
                enclosing_models: enclosing_models.to_vec(),
            }),
            Decl::Model(mid) => {
                let body = ast.model_decl(mid).body.clone();
                let model_tid = signature.types_for_model_decl(mid).type_;
                let mut nested = enclosing_models.to_vec();
                nested.push(model_tid);
                collect_rules(ast, signature, &body, &nested, out);
            }
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Enum(_) => {}
        }
    }
}

/// Lowers a [`TypeConflict`] to a user-facing [`CompileError`].
///
/// When the two [`ConcreteType`]s disagree on [`TypeId`] the result is
/// [`CompileError::ConflictingTermType`], anchored on the term in
/// `semantic_el` whose element shares a class with `conflict.el`. When
/// the [`TypeId`]s agree but parents diverge, the result is
/// [`CompileError::ConflictingParentEl`], anchored on the two terms
/// whose elements share classes with the innermost differing pair of
/// parent elements (last index in the parent list, since parents are
/// outermost first).
///
/// Panics if no term backs the chosen elements; the message
/// distinguishes ambient model elements to help diagnose the invariant
/// violation.
fn conflict_to_error(
    ast: &Ast,
    signature: &Signature,
    structure: &Structure,
    semantic_el: &BTreeMap<TermId, ElId>,
    conflict: TypeConflict,
) -> CompileError {
    let TypeConflict { el, a, b } = conflict;
    if a.typ != b.typ {
        let term_id = find_term(structure, semantic_el, el);
        return CompileError::ConflictingTermType {
            types: vec![
                signature.type_name(ast, a.typ),
                signature.type_name(ast, b.typ),
            ],
            location: ast.loc(term_id),
        };
    }

    let (pa, pb) = innermost_differing_parents(structure, &a, &b)
        .expect("parent-mismatch conflict has no differing parent");
    let pa_term = find_term(structure, semantic_el, structure.unification.root_const(pa));
    let pb_term = find_term(structure, semantic_el, structure.unification.root_const(pb));
    CompileError::ConflictingParentEl {
        type_name: signature.type_name(ast, a.typ),
        parent_locations: (ast.loc(pa_term), ast.loc(pb_term)),
    }
}

/// Returns the deepest (highest-index) pair of parents whose classes
/// disagree under `structure`'s unification, or `None` if all
/// overlapping positions agree. Parents are outermost first, so the
/// highest index is the innermost ambient model — usually the most
/// useful place to anchor a diagnostic.
fn innermost_differing_parents(
    structure: &Structure,
    a: &ConcreteType,
    b: &ConcreteType,
) -> Option<(ElId, ElId)> {
    let n = a.parents.len().min(b.parents.len());
    (0..n).rev().find_map(|i| {
        let ra = structure.unification.root_const(a.parents[i]);
        let rb = structure.unification.root_const(b.parents[i]);
        (ra != rb).then_some((a.parents[i], b.parents[i]))
    })
}

/// Locates a term whose element shares a class with `target` under
/// `structure`'s unification. Panics if no such term exists, with a
/// message that flags ambient model elements to help diagnose the
/// invariant violation.
fn find_term(structure: &Structure, semantic_el: &BTreeMap<TermId, ElId>, target: ElId) -> TermId {
    let target_root = structure.unification.root_const(target);
    semantic_el
        .iter()
        .find(|(_, &e)| structure.unification.root_const(e) == target_root)
        .map(|(t, _)| *t)
        .unwrap_or_else(|| {
            let is_ambient = structure
                .ambient_model_els
                .values()
                .any(|&e| structure.unification.root_const(e) == target_root);
            panic!(
                "conflict on class {target:?} has no term in semantic_el \
                 (ambient model el: {is_ambient})"
            );
        })
}
