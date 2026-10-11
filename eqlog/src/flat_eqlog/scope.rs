use crate::algebra::signature::Signature;

use super::{FlatInRel, FlatOutRel, FlatRel, FlatRule, FlatRuleGroup, RuleScope};

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
    let rel = match output.rel {
        FlatOutRel::Rel(rel) => rel,
        FlatOutRel::FuncDomain(func) => FlatRel::Func(func),
        // Equality can affect occurrences outside this owner, including graphs.
        FlatOutRel::Equality(_) => return RuleScope::Global,
    };
    let Some(model) = rel.parent_model_type(signature) else {
        return RuleScope::Global;
    };
    let count = signature.type_(model).parents.len() + 1;
    let owners = &output.args[..count];
    for stmt in &rule.conclusion {
        let rel = match stmt.rel {
            FlatOutRel::Rel(rel) => rel,
            FlatOutRel::FuncDomain(func) => FlatRel::Func(func),
            FlatOutRel::Equality(_) => return RuleScope::Global,
        };
        if rel.parent_model_type(signature) != Some(model) || stmt.args[..count] != *owners {
            return RuleScope::Global;
        }
    }
    for stmt in &rule.premise {
        let (rel, args) = match &stmt.rel {
            FlatInRel::Rel(rel) => (*rel, stmt.args.clone()),
            FlatInRel::RelWithDiagonals { rel, equalities } => {
                let columns: Vec<_> = equalities
                    .iter()
                    .enumerate()
                    .filter_map(|(i, &j)| (i == j).then_some(i))
                    .collect();
                let args = equalities
                    .iter()
                    .map(|j| stmt.args[columns.binary_search(j).unwrap()].clone())
                    .collect();
                (*rel, args)
            }
            FlatInRel::TypeSet(_) => continue,
            FlatInRel::Equality(_) => unreachable!("scope follows equality elimination"),
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
