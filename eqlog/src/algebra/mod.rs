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

use std::collections::{BTreeMap, BTreeSet};

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
                        &rule.native_terms[sid.0],
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
/// Always emits [`CompileError::ConflictingTermType`], anchored on a
/// term native to the conflict's structure whose element shares a
/// class with `conflict.el`. Restricting to native terms avoids
/// pointing at terms inherited via cloning from earlier structures —
/// those live at unrelated source locations. Each [`ConcreteType`] is
/// rendered as `TypeName` for global types or `parent_name.TypeName`
/// for member types, matching the format the eqlog-side conflict pass
/// uses.
///
/// Panics if no native term backs `el`; the message distinguishes
/// ambient model elements to help diagnose the invariant violation.
fn conflict_to_error(
    ast: &Ast,
    signature: &Signature,
    structure: &Structure,
    semantic_el: &BTreeMap<TermId, ElId>,
    native_terms: &BTreeSet<TermId>,
    conflict: TypeConflict,
) -> CompileError {
    let TypeConflict { el, a, b } = conflict;
    let term_id = find_term(structure, semantic_el, native_terms, el);
    CompileError::ConflictingTermType {
        types: vec![
            concrete_type_to_string(ast, signature, structure, &a),
            concrete_type_to_string(ast, signature, structure, &b),
        ],
        location: ast.loc(term_id),
    }
}

/// Renders a [`ConcreteType`] for a diagnostic message. Global types
/// render as just the type name. Member types render as
/// `parent_name.TypeName`, where `parent_name` is the source name of
/// the innermost parent (read off `structure.var_els` by class), or
/// `?` for parents not bound to any variable (e.g. ambient model els
/// introduced by enclosing-model scopes).
fn concrete_type_to_string(
    ast: &Ast,
    signature: &Signature,
    structure: &Structure,
    ct: &ConcreteType,
) -> String {
    let type_name = signature.type_name(ast, ct.typ);
    let Some(&parent) = ct.parents.last() else {
        return type_name;
    };
    let parent_root = structure.unification.root_const(parent);
    let parent_name = structure
        .var_els
        .iter()
        .find_map(|(name, &el)| {
            (structure.unification.root_const(el) == parent_root).then_some(name.as_str())
        })
        .unwrap_or("?");
    format!("{parent_name}.{type_name}")
}

/// Locates a native term whose element shares a class with `target`
/// under `structure`'s unification. Considers only terms in
/// `native_terms` so the diagnostic anchors at source recorded by this
/// structure's own walk, not at terms inherited from a cloned earlier
/// structure. Panics if no such term exists, with a message that flags
/// ambient model elements to help diagnose the invariant violation.
fn find_term(
    structure: &Structure,
    semantic_el: &BTreeMap<TermId, ElId>,
    native_terms: &BTreeSet<TermId>,
    target: ElId,
) -> TermId {
    let target_root = structure.unification.root_const(target);
    native_terms
        .iter()
        .copied()
        .find(|t| {
            semantic_el
                .get(t)
                .map(|&e| structure.unification.root_const(e) == target_root)
                .unwrap_or(false)
        })
        .unwrap_or_else(|| {
            let is_ambient = structure
                .ambient_model_els
                .values()
                .any(|&e| structure.unification.root_const(e) == target_root);
            panic!(
                "conflict on class {target:?} has no native term in semantic_el \
                 (ambient model el: {is_ambient})"
            );
        })
}
