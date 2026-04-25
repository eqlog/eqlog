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
use crate::algebra::structure::{ConcreteType, ElId, Structure, StructureId, TypeConflict};
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
        let mut last_arg_num_errors;
        loop {
            // Per-iteration reset. The walker re-visits every site, so the
            // final iteration's Vec is the ground truth at convergence.
            // Earlier iterations would just contribute stale duplicates.
            last_arg_num_errors = Vec::new();
            let walk_changed = walk_rule(
                &mut rule,
                rid,
                &enclosing_models,
                ast,
                scopes,
                signature,
                &mut last_arg_num_errors,
            );
            let (close_changed, conflicts) = rule.cat.close(signature);
            last_conflicts = conflicts;
            if !walk_changed && !close_changed {
                break;
            }
        }

        let mut errors: Vec<CompileError> = last_conflicts
            .into_iter()
            .map(|(sid, conflict)| conflict_to_error(ast, signature, &rule, sid, conflict))
            .collect();
        errors.extend(last_arg_num_errors);
        if !errors.is_empty() {
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

/// Lowers a [`TypeConflict`] to a [`CompileError::ConflictingTermType`],
/// anchored on a term whose element shares a class with `conflict.el`
/// (located via [`find_term`]). Each [`ConcreteType`] renders as
/// `TypeName` for global types or `parent_name.TypeName` for member
/// types.
///
/// Panics if no term backs `el` in any reachable structure.
fn conflict_to_error(
    ast: &Ast,
    signature: &Signature,
    rule: &RuleStructures,
    sid: StructureId,
    conflict: TypeConflict,
) -> CompileError {
    let TypeConflict { el, a, b } = conflict;
    let structure = &rule.cat.structures[sid.0];
    let term_id = find_term(rule, sid, el);
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

/// Locates a term whose element shares a class with `target` in the
/// structure at `sid`. Conflicts can surface in a structure that
/// received `target` only as a morphism image, so on miss in
/// `semantic_els[sid]` the search expands through incoming morphisms
/// to preimages in source structures.
///
/// Panics if no reachable structure backs the class with a term.
fn find_term(rule: &RuleStructures, sid: StructureId, target: ElId) -> TermId {
    let start_root = rule.cat.structures[sid.0].unification.root_const(target);
    let mut visited: BTreeSet<(StructureId, ElId)> = BTreeSet::new();
    let mut worklist: Vec<(StructureId, ElId)> = vec![(sid, start_root)];

    while let Some((s, el_root)) = worklist.pop() {
        if !visited.insert((s, el_root)) {
            continue;
        }

        let s_st = &rule.cat.structures[s.0];
        if let Some((&term, _)) = rule.semantic_els[s.0]
            .iter()
            .find(|(_, &e)| s_st.unification.root_const(e) == el_root)
        {
            return term;
        }

        for (&(src, tgt), elmap) in &rule.cat.morphisms {
            if tgt != s {
                continue;
            }
            let src_st = &rule.cat.structures[src.0];
            for (&src_el, &tgt_el) in elmap {
                if s_st.unification.root_const(tgt_el) != el_root {
                    continue;
                }
                let src_root = src_st.unification.root_const(src_el);
                if !visited.contains(&(src, src_root)) {
                    worklist.push((src, src_root));
                }
            }
        }
    }

    let is_ambient_at_sid = rule.cat.structures[sid.0]
        .ambient_model_els
        .values()
        .any(|&e| rule.cat.structures[sid.0].unification.root_const(e) == start_root);
    panic!(
        "conflict on class {target:?} at {sid:?} has no term in any reachable structure \
         (ambient model el at sid: {is_ambient_at_sid})"
    );
}
