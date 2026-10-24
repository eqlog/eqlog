use std::collections::BTreeSet;

use super::supports_member;
use crate::algebra::signature::{Signature, TypeId};
use crate::flat_eqlog::{FlatInRel, FlatOutRel, FlatRel, FlatRule, RuleScope};
use crate::options::ModelMode;
use crate::ram::RamFunction;

fn invariant_key(
    model: TypeId,
    rule: &FlatRule,
    signature: &Signature,
    mode: ModelMode,
) -> Option<(FlatRel, usize)> {
    let owner = match &rule.scope {
        RuleScope::Model {
            model: scope,
            owners,
        } if *scope == model && owners.len() == 1 => &owners[0],
        RuleScope::Model { .. } | RuleScope::Global => return None,
    };
    let atoms: Vec<_> = rule
        .premise
        .iter()
        .filter_map(|stmt| match stmt.rel {
            FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::Func(_)) => Some(stmt),
            FlatInRel::Rel(FlatRel::ModelMember(_))
            | FlatInRel::RelWithDiagonals { .. }
            | FlatInRel::Equality(_)
            | FlatInRel::TypeSet(_) => None,
        })
        .collect();
    let [first, second] = atoms.as_slice() else {
        return None;
    };
    let relation = match first.rel {
        FlatInRel::Rel(relation) => relation,
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => {
            return None
        }
    };
    if second.rel != first.rel
        || relation.parent_model_type(signature) != Some(model)
        || first.args.first() != Some(owner)
        || second.args.first() != Some(owner)
    {
        return None;
    }
    let arity = relation.arity(signature);
    let member_columns: Vec<_> = arity
        .iter()
        .enumerate()
        .skip(1)
        .filter(|(_, typ)| !signature.type_(**typ).parents.is_empty())
        .map(|(column, _)| column)
        .collect();
    let [column] = member_columns.as_slice() else {
        return None;
    };
    let column = *column;
    let member = arity[column];
    if !supports_member(signature, mode, member)
        || signature.type_(member).parents.as_slice() != [model]
        || !relation.column_maps_under(signature, column, model)
        || first.args.len() != arity.len()
        || second.args.len() != arity.len()
        || first.args.iter().collect::<BTreeSet<_>>().len() != arity.len()
        || second.args.iter().collect::<BTreeSet<_>>().len() != arity.len()
    {
        return None;
    }
    let left = &first.args[column];
    let right = &second.args[column];
    if left == right
        || first
            .args
            .iter()
            .zip(&second.args)
            .enumerate()
            .any(|(index, (left, right))| index != column && left != right)
    {
        return None;
    }

    // Typing premises follow from these relation rows. Other premises would
    // make uniqueness conditional on facts that an inherited row cannot prove.
    for stmt in &rule.premise {
        let implied = match &stmt.rel {
            FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::Func(_)) => true,
            FlatInRel::Rel(FlatRel::ModelMember(typ)) => {
                *typ == member
                    && stmt.args.len() == 2
                    && &stmt.args[0] == owner
                    && (&stmt.args[1] == left || &stmt.args[1] == right)
            }
            FlatInRel::TypeSet(typ) => {
                stmt.args.len() == 1
                    && stmt.args[0].typ == *typ
                    && (first.args.contains(&stmt.args[0]) || second.args.contains(&stmt.args[0]))
            }
            FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) => false,
        };
        if !implied {
            return None;
        }
    }
    rule.conclusion
        .iter()
        .any(|stmt| match stmt.rel {
            FlatOutRel::Equality(typ) => {
                typ == member
                    && stmt.args.len() == 2
                    && ((&stmt.args[0] == left && &stmt.args[1] == right)
                        || (&stmt.args[0] == right && &stmt.args[1] == left))
            }
            FlatOutRel::Rel(_) | FlatOutRel::FuncDomain(_) => false,
        })
        .then_some((relation, column))
}

/// A transported row with an invariant key proves its member image unique.
/// Recognizing the logical constraint also covers predicate uniqueness rules.
pub(super) fn invariant_keys(
    model: TypeId,
    modules: &[RamFunction],
    signature: &Signature,
    mode: ModelMode,
) -> Vec<(FlatRel, usize)> {
    modules
        .iter()
        .flat_map(RamFunction::flat_rules)
        .filter_map(|rule| invariant_key(model, rule, signature, mode))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}
