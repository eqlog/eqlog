use crate::algebra::signature::{Signature, TypeId};

use super::{FlatInRel, FlatOutRel, FlatRel, FlatRule, FlatRuleGroup, FlatVar, RuleScope};

// Scope is inferred after equality elimination so owner aliases agree, including
// rules written outside a model with an explicit receiver.
pub fn infer_rule_scopes(groups: &mut [FlatRuleGroup], signature: &Signature) {
    for group in groups {
        for rule in &mut group.rules {
            rule.scope = infer_scope(rule, signature);
        }
    }
}

fn infer_scope(rule: &FlatRule, signature: &Signature) -> RuleScope {
    let Some(output) = rule.conclusion.first() else {
        return RuleScope::Global;
    };
    let candidate = match output.rel {
        FlatOutRel::Rel(rel) => rel
            .parent_model_type(signature)
            .map(|model| (model, output.args.clone())),
        FlatOutRel::FuncDomain(func) => FlatRel::Func(func)
            .parent_model_type(signature)
            .map(|model| (model, output.args.clone())),
        FlatOutRel::Equality(typ) => signature.type_(typ).parents.last().and_then(|&model| {
            rule.premise.iter().find_map(|stmt| {
                let (rel, args) = premise_relation(&stmt.rel, &stmt.args)?;
                (rel.parent_model_type(signature) == Some(model)).then_some((model, args))
            })
        }),
    };
    let Some((model, args)) = candidate else {
        return RuleScope::Global;
    };
    let count = signature.type_(model).parents.len() + 1;
    let owners = &args[..count];
    for stmt in &rule.conclusion {
        let rel = match stmt.rel {
            FlatOutRel::Rel(rel) => rel,
            FlatOutRel::FuncDomain(func) => FlatRel::Func(func),
            FlatOutRel::Equality(typ) => {
                if !ordinary_member(typ, model, signature) {
                    return RuleScope::Global;
                }
                continue;
            }
        };
        if rel.parent_model_type(signature) != Some(model) || stmt.args[..count] != *owners {
            return RuleScope::Global;
        }
    }
    for stmt in &rule.premise {
        let Some((rel, args)) = premise_relation(&stmt.rel, &stmt.args) else {
            continue;
        };
        let Some(parent) = rel.parent_model_type(signature) else {
            continue;
        };
        if parent != model
            && !signature.type_(parent).parents.contains(&model)
            && !signature.type_(model).parents.contains(&parent)
        {
            return RuleScope::Global;
        }
        let prefix = (signature.type_(parent).parents.len() + 1).min(count);
        if args[..prefix] != owners[..prefix] {
            return RuleScope::Global;
        }
    }
    RuleScope::Model {
        model,
        owners: owners.to_vec(),
    }
}

fn ordinary_member(typ: TypeId, model: TypeId, signature: &Signature) -> bool {
    // A traversal keeps its owner keys and graph topology until its next visit.
    signature.type_(typ).parents.last() == Some(&model)
        && signature
            .iter_model_decls()
            .all(|(_, ids)| typ != ids.type_ && typ != ids.mor)
}

fn premise_relation(rel: &FlatInRel, args: &[FlatVar]) -> Option<(FlatRel, Vec<FlatVar>)> {
    match rel {
        FlatInRel::Rel(rel) => Some((*rel, args.to_vec())),
        FlatInRel::RelWithDiagonals { rel, equalities } => {
            let columns: Vec<_> = equalities
                .iter()
                .enumerate()
                .filter_map(|(i, &j)| (i == j).then_some(i))
                .collect();
            let args = equalities
                .iter()
                .map(|j| args[columns.binary_search(j).unwrap()].clone())
                .collect();
            Some((*rel, args))
        }
        FlatInRel::TypeSet(_) => None,
        FlatInRel::Equality(_) => unreachable!("scope follows equality elimination"),
    }
}
