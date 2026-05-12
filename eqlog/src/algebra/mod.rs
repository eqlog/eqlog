//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! [`signature`] builds the dependent signature (types, preds, funcs) from
//! the AST. [`structure`] holds the per-rule and per-statement structure
//! data, including the close pass that saturates it under functionality and
//! signature-imposed typing. [`populate`] walks the AST rule bodies to fill
//! in each [`RuleStructures`]. Future passes (morphism construction) will
//! live alongside them.

pub mod match_check;
pub mod populate;
pub mod signature;
pub mod structure;

use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::match_check::check_rule_matches;
use crate::algebra::populate::{walk_rule, MorphismKind, RuleStructures};
use crate::algebra::signature::{Signature, TypeId, TypeKind};
use crate::algebra::structure::{ConcreteType, ElId, Structure, StructureId, TypeConflict};
use crate::ast::*;
use crate::error::CompileError;
use crate::grammar_util::Location;
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
            .iter()
            .cloned()
            .map(|(sid, conflict)| conflict_to_error(ast, signature, &rule, sid, conflict))
            .collect();
        errors.extend(last_arg_num_errors);
        errors.extend(morphism_application_errors(ast, signature, &rule));
        errors.extend(undetermined_type_errors(ast, &rule));
        // Only run the surjectivity check when the structures are at a
        // settled, conflict-free state. Type conflicts can leave the
        // morphisms in shapes that would produce noisy false positives.
        if errors.is_empty() {
            errors.extend(surjectivity_errors(ast, &rule));
        }
        check_rule_matches(rid, ast, scopes, signature, &mut errors);
        if !errors.is_empty() {
            return Err(errors);
        }

        let prev = rules.insert(rid, rule);
        assert!(prev.is_none(), "rule {rid:?} visited twice in decl tree");
    }
    Ok(rules)
}

fn morphism_application_errors(
    ast: &Ast,
    signature: &Signature,
    rule: &RuleStructures,
) -> Vec<CompileError> {
    let mut errors = Vec::new();
    let mut reported_non_mors = BTreeSet::new();
    let mut reported_non_members = BTreeSet::new();

    for (sid, semantic_els) in rule.semantic_els.iter().enumerate() {
        let sid = StructureId(sid);
        for &term in semantic_els.keys() {
            let Term::MorApp(mor_app) = *ast.term(term) else {
                continue;
            };
            let MorAppTerm { mor, arg } = *ast.mor_app_term(mor_app);

            check_morphism_application(
                ast,
                signature,
                rule,
                sid,
                mor,
                arg,
                &mut reported_non_mors,
                &mut reported_non_members,
                &mut errors,
            );
        }
    }

    errors
}

fn check_morphism_application(
    ast: &Ast,
    signature: &Signature,
    rule: &RuleStructures,
    sid: StructureId,
    mor: TermId,
    arg: TermId,
    reported_non_mors: &mut BTreeSet<TermId>,
    reported_non_members: &mut BTreeSet<TermId>,
    errors: &mut Vec<CompileError>,
) {
    let Some(mor_types) = concrete_types_of_term(rule, sid, mor) else {
        return;
    };

    let mor_models: BTreeSet<TypeId> = mor_types
        .iter()
        .filter_map(|ct| match signature.type_(ct.typ).kind {
            TypeKind::Mor(model_tid) => Some(model_tid),
            _ => None,
        })
        .collect();

    if mor_models.is_empty() {
        if reported_non_mors.insert(mor) {
            errors.push(CompileError::NonMorphismAppliedAsMorphism {
                location: ast.loc(mor),
            });
        }
        return;
    }

    let Some(arg_types) = concrete_types_of_term(rule, sid, arg) else {
        return;
    };
    for model_tid in mor_models {
        let arg_is_member = arg_types
            .iter()
            .any(|ct| member_model_type(signature, ct) == Some(model_tid));
        if !arg_is_member {
            if reported_non_members.insert(arg) {
                errors.push(CompileError::MorphismAppliedToNonMember {
                    location: ast.loc(arg),
                });
            }
            break;
        }
    }
}

/// Reports every surface term whose semantic element still has no concrete
/// type after the rule's populate/close fixed point has settled.
fn undetermined_type_errors(ast: &Ast, rule: &RuleStructures) -> Vec<CompileError> {
    let mut reported_terms = BTreeSet::new();
    let mut errors = Vec::new();

    for (sid, semantic_els) in rule.semantic_els.iter().enumerate() {
        let structure = &rule.cat.structures[sid];
        for (&term, &el) in semantic_els {
            let root = structure.unification.root_const(el);
            let has_type = structure.els.get(&root).is_some_and(|cts| !cts.is_empty());
            if !has_type && reported_terms.insert(term) {
                errors.push(CompileError::UndeterminedTermType {
                    location: ast.loc(term),
                });
            }
        }
    }

    errors
}

fn concrete_types_of_term(
    rule: &RuleStructures,
    sid: StructureId,
    term: TermId,
) -> Option<BTreeSet<ConcreteType>> {
    // Type information is not always materialised in cloned successor
    // structures immediately, so recover types from incoming preimages too.
    let start_structure = &rule.cat.structures[sid.0];
    let start_el = *rule.semantic_els[sid.0].get(&term)?;
    let start_root = start_structure.unification.root_const(start_el);
    let mut types = BTreeSet::new();

    let mut visited = BTreeSet::new();
    let mut worklist = vec![(sid, start_root)];
    while let Some((current_sid, root)) = worklist.pop() {
        if !visited.insert((current_sid, root)) {
            continue;
        }

        let structure = &rule.cat.structures[current_sid.0];
        types.extend(structure.concrete_types_of(root));

        for (&(src, tgt), elmap) in &rule.cat.morphisms {
            if tgt != current_sid {
                continue;
            }
            let src_structure = &rule.cat.structures[src.0];
            for (&src_el, &tgt_el) in elmap {
                if structure.unification.root_const(tgt_el) != root {
                    continue;
                }
                let src_root = src_structure.unification.root_const(src_el);
                if !visited.contains(&(src, src_root)) {
                    worklist.push((src, src_root));
                }
            }
        }
    }

    (!types.is_empty()).then_some(types)
}

fn member_model_type(signature: &Signature, ct: &ConcreteType) -> Option<TypeId> {
    signature.type_(ct.typ).parents.last().copied()
}

/// Reports surjectivity violations for `then`-atom morphisms. A
/// `SurjThen` morphism (from a `then`-equal or `then`-pred atom) must be
/// surjective on elements: every element of the target structure must
/// have a preimage under the morphism. A `NonSurjThen` morphism (from a
/// `then`-defined atom) has the same requirement, except the element
/// backing the defined-then atom's term is exempt.
///
/// Mirrors eqlog.eql's `el_should_be_surjective_ok` /
/// `el_is_surjective_ok` rules. The diagnostic is anchored on a term
/// in the target structure whose semantic el is the offender.
fn surjectivity_errors(ast: &Ast, rule: &RuleStructures) -> Vec<CompileError> {
    let mut errors = Vec::new();
    for (&stmt_id, &tgt) in &rule.stmt_after {
        let Some(&src) = rule.stmt_before.get(&stmt_id) else {
            continue;
        };
        let kind = match rule.morphism_kinds.get(&(src, tgt)) {
            Some(k) => *k,
            None => continue,
        };
        let exempt = match (kind, *ast.stmt(stmt_id)) {
            (MorphismKind::SurjThen, _) => None,
            (MorphismKind::NonSurjThen, Stmt::Then(then_id)) => {
                let atom = ast.then_stmt(then_id).atom;
                let ThenAtom::Defined(def_id) = *ast.then_atom(atom) else {
                    unreachable!("NonSurjThen morphism must come from a defined-then atom")
                };
                let term = ast.defined_then_atom(def_id).term;
                rule.semantic_els[tgt.0]
                    .get(&term)
                    .copied()
                    .map(|e| rule.cat.structures[tgt.0].unification.root_const(e))
            }
            _ => continue,
        };

        let Some(elmap) = rule.cat.morphisms.get(&(src, tgt)) else {
            continue;
        };
        let tgt_st = &rule.cat.structures[tgt.0];
        let img: BTreeSet<ElId> = elmap
            .values()
            .map(|&e| tgt_st.unification.root_const(e))
            .collect();

        for &el_root in tgt_st.els.keys() {
            if img.contains(&el_root) {
                continue;
            }
            if exempt == Some(el_root) {
                continue;
            }
            let term = find_term_at(rule, tgt, el_root);
            errors.push(CompileError::SurjectivityViolation {
                location: ast.loc(term),
            });
        }
    }
    errors
}

/// Locates a term in `rule.semantic_els[sid]` whose el shares a class
/// with `target` under the structure's unification. Every newly-introduced
/// element in a then-stmt's target structure must back at least one
/// surface term, so this never fails on inputs from
/// [`surjectivity_errors`].
fn find_term_at(rule: &RuleStructures, sid: StructureId, target: ElId) -> TermId {
    let st = &rule.cat.structures[sid.0];
    let target_root = st.unification.root_const(target);
    rule.semantic_els[sid.0]
        .iter()
        .find(|(_, &e)| st.unification.root_const(e) == target_root)
        .map(|(&t, _)| t)
        .expect("surjectivity-offending el should back a term in the target structure")
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
                let model_tid = signature.ids_for_model_decl(mid).type_;
                let mut nested = enclosing_models.to_vec();
                nested.push(model_tid);
                collect_rules(ast, signature, &body, &nested, out);
            }
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Enum(_) => {}
        }
    }
}

/// Lowers a [`TypeConflict`] to a [`CompileError::ConflictingTermType`],
/// anchored on the earliest reachable term whose element shares a class
/// with `conflict.el`. Each [`ConcreteType`] renders as `TypeName` for
/// global types or `parent_name.TypeName` for member types.
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
    let term_id = find_earliest_term(ast, rule, sid, el);
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

/// Locates the earliest source term reachable from `target` by walking
/// incoming morphisms.
fn find_earliest_term(ast: &Ast, rule: &RuleStructures, sid: StructureId, target: ElId) -> TermId {
    let start_root = rule.cat.structures[sid.0].unification.root_const(target);
    let mut visited: BTreeSet<(StructureId, ElId)> = BTreeSet::new();
    let mut worklist: Vec<(StructureId, ElId)> = vec![(sid, start_root)];
    let mut best: Option<(Location, TermId)> = None;

    while let Some((s, el_root)) = worklist.pop() {
        if !visited.insert((s, el_root)) {
            continue;
        }

        let s_st = &rule.cat.structures[s.0];
        for (&term, &e) in &rule.semantic_els[s.0] {
            if s_st.unification.root_const(e) != el_root {
                continue;
            }
            let loc = ast.loc(term);
            if best.is_none_or(|(best_loc, _)| (loc.1, loc.0) < (best_loc.1, best_loc.0)) {
                best = Some((loc, term));
            }
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

    if let Some((_, term)) = best {
        return term;
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
