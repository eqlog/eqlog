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
use crate::algebra::structure::{ElId, Structure, TypeConflict};
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
        walk_rule(&mut rule, rid, &enclosing_models, ast, scopes, signature);

        let conflicts = rule.cat.close(signature);
        if !conflicts.is_empty() {
            let errors: Vec<CompileError> = conflicts
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
                .values()
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
