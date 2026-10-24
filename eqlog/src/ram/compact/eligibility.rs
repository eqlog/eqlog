use std::collections::BTreeSet;

use super::{supports_member, CompactRejection};
use crate::algebra::signature::{Signature, TypeId, TypeKind};
use crate::flat_eqlog::{
    category_rules, functionality_anchor, iter_flat_rels, use_rels_with_diagonals, FlatInRel,
    FlatOutRel, FlatRel, FlatRule, FlatVar, IndexSelection, IndexSpec, RuleSchedule, RuleScope,
};
use crate::options::ModelMode;
use crate::ram::RamFunction;

type RuleBody = (
    Vec<(FlatInRel, Vec<FlatVar>)>,
    Vec<(FlatOutRel, Vec<FlatVar>)>,
);

fn body(rule: &FlatRule) -> RuleBody {
    let mut premise: Vec<_> = rule
        .premise
        .iter()
        .map(|stmt| (stmt.rel.clone(), stmt.args.clone()))
        .collect();
    let mut conclusion: Vec<_> = rule
        .conclusion
        .iter()
        .map(|stmt| (stmt.rel, stmt.args.clone()))
        .collect();
    premise.sort();
    conclusion.sort();
    (premise, conclusion)
}

fn has_members(types: impl IntoIterator<Item = TypeId>, members: &BTreeSet<TypeId>) -> bool {
    types.into_iter().any(|typ| members.contains(&typ))
}

fn full_permutation(index: &IndexSpec, arity: usize) -> bool {
    let mut order = index.order.to_vec();
    order.sort_unstable();
    order.into_iter().eq(0..arity)
}

fn is_member_action(rel: FlatRel, members: &BTreeSet<TypeId>, signature: &Signature) -> bool {
    match rel {
        FlatRel::Func(func) => signature
            .types_for_mor_app_func(func)
            .is_some_and(|types| members.contains(&types.member_type)),
        FlatRel::Pred(_) | FlatRel::ModelMember(_) => false,
    }
}

fn builtin_member_rule(
    rule: &FlatRule,
    members: &BTreeSet<TypeId>,
    signature: &Signature,
    categories: &BTreeSet<RuleBody>,
) -> bool {
    if categories.contains(&body(rule)) {
        return true;
    }
    if functionality_anchor(rule).is_none() {
        return false;
    }
    match &rule.premise[0].rel {
        FlatInRel::Rel(rel) => is_member_action(*rel, members, signature),
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => {
            false
        }
    }
}

fn same_owner(
    rel: FlatRel,
    args: &[FlatVar],
    owner: &FlatVar,
    model: TypeId,
    signature: &Signature,
) -> bool {
    rel.parent_model_type(signature) == Some(model) && args.first() == Some(owner)
}

/// Scope conversions need every compact member variable in one owner coordinate space.
/// Built-in category rules keep their ordinary UID path; runtime graph guards must
/// materialize unsupported morphism operations before those rules can execute.
pub(super) fn rejection_reason(
    model: TypeId,
    modules: &[RamFunction],
    schedule: &RuleSchedule,
    selection: &IndexSelection,
    signature: &Signature,
    mode: ModelMode,
) -> Option<CompactRejection> {
    match mode {
        ModelMode::Native => {}
        ModelMode::Desugared => return Some(CompactRejection::NativeRequired),
    }
    match signature.type_(model).kind {
        TypeKind::Model => {}
        TypeKind::Plain | TypeKind::Enum | TypeKind::Mor(_) => {
            return Some(CompactRejection::NotModel(model));
        }
    }
    if !signature.type_(model).parents.is_empty() {
        return Some(CompactRejection::EnclosingCoordinates(model));
    }
    let mut members = BTreeSet::new();
    for typ in signature.iter_types() {
        let parents = &signature.type_(typ).parents;
        if !parents.contains(&model) {
            continue;
        }
        if parents.as_slice() != [model] || !supports_member(signature, mode, typ) {
            return Some(CompactRejection::UnsupportedMember { model, member: typ });
        }
        members.insert(typ);
    }
    if members.is_empty() {
        return Some(CompactRejection::NoMembers(model));
    }

    for rel in iter_flat_rels(signature) {
        let arity = rel.arity(signature);
        if rel.parent_model_type(signature) == Some(model) {
            for (column, &typ) in arity.iter().enumerate().skip(1) {
                if signature.type_(typ).parents.is_empty() {
                    continue;
                }
                if !members.contains(&typ) || !rel.column_maps_under(signature, column, model) {
                    return Some(CompactRejection::ForeignColumn { rel, column });
                }
            }
        } else if has_members(arity, &members) && !is_member_action(rel, &members, signature) {
            return Some(CompactRejection::OutsideOwner { rel, model });
        }
    }

    for (rel, index) in selection.current_indices() {
        match rel {
            FlatInRel::Rel(relation) => {
                if relation.parent_model_type(signature) != Some(model) {
                    continue;
                }
                let arity = relation.arity(signature);
                if !full_permutation(index, arity.len()) {
                    return Some(CompactRejection::IncompleteIndex(*relation));
                }
                if has_members(arity, &members) && index.order.first() != Some(&0) {
                    return Some(CompactRejection::NonleadingIndex(*relation));
                }
            }
            FlatInRel::RelWithDiagonals { rel, .. } => {
                if rel.parent_model_type(signature) == Some(model)
                    && has_members(rel.arity(signature), &members)
                {
                    return Some(CompactRejection::DiagonalIndex(*rel));
                }
            }
            FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => {}
        }
    }

    // Ages and join orders vary across generated routines; the logical bodies
    // identify built-ins without trusting names that user rules could imitate.
    let categories: BTreeSet<_> = category_rules(signature)
        .into_iter()
        .map(|mut rule| {
            use_rels_with_diagonals(&mut rule);
            body(&rule)
        })
        .collect();
    for (module_index, module) in modules.iter().enumerate() {
        for routine in &module.rules {
            let rule = &routine.flat_rule;
            if !rule
                .premise
                .iter()
                .flat_map(|stmt| &stmt.args)
                .chain(rule.conclusion.iter().flat_map(|stmt| &stmt.args))
                .any(|var| members.contains(&var.typ))
                || builtin_member_rule(rule, &members, signature, &categories)
            {
                continue;
            }
            let name = rule.name.clone();
            let owner = match &rule.scope {
                RuleScope::Model {
                    model: scope,
                    owners,
                } if *scope == model && owners.len() == 1 && owners[0].typ == model => &owners[0],
                RuleScope::Model { .. } | RuleScope::Global => {
                    return Some(CompactRejection::RuleScope { name, model });
                }
            };
            let strata: Vec<_> = schedule
                .strata
                .iter()
                .filter(|stratum| stratum.groups.contains(&module_index))
                .collect();
            if strata.is_empty() || strata.iter().any(|stratum| stratum.model != Some(model)) {
                return Some(CompactRejection::ExecutionScope(name));
            }
            for stmt in &rule.premise {
                if !stmt.args.iter().any(|var| members.contains(&var.typ)) {
                    continue;
                }
                let valid = match &stmt.rel {
                    FlatInRel::Rel(rel) => same_owner(*rel, &stmt.args, owner, model, signature),
                    FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::Equality(_)
                    | FlatInRel::TypeSet(_) => false,
                };
                if !valid {
                    return Some(CompactRejection::ReadScope(name));
                }
            }
            for stmt in &rule.conclusion {
                if !stmt.args.iter().any(|var| members.contains(&var.typ)) {
                    continue;
                }
                let valid = match stmt.rel {
                    FlatOutRel::Rel(rel) => same_owner(rel, &stmt.args, owner, model, signature),
                    FlatOutRel::FuncDomain(func) => {
                        same_owner(FlatRel::Func(func), &stmt.args, owner, model, signature)
                    }
                    FlatOutRel::Equality(typ) => members.contains(&typ),
                };
                if !valid {
                    return Some(CompactRejection::WriteScope(name));
                }
            }
            for (rel, index) in routine.input_indices() {
                if !has_members(rel.arity(signature), &members) {
                    continue;
                }
                let valid = match &rel {
                    FlatInRel::Rel(relation) => {
                        relation.parent_model_type(signature) == Some(model)
                            && full_permutation(&index, rel.arity(signature).len())
                            && index.order.first() == Some(&0)
                    }
                    FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::Equality(_)
                    | FlatInRel::TypeSet(_) => false,
                };
                if !valid {
                    return Some(CompactRejection::InputIndex(name));
                }
            }
        }
    }
    None
}
