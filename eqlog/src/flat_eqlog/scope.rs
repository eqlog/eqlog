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
        let prefix = signature.type_(parent).parents.len() + 1;
        if prefix > count || args[..prefix] != owners[..prefix] {
            return RuleScope::Global;
        }
    }
    RuleScope::Model {
        model,
        owners: owners.to_vec(),
    }
}

#[cfg(test)]
mod tests {
    use crate::algebra::build_structures;
    use crate::algebra::signature::build_signature;
    use crate::ast::Ast;
    use crate::flatten::{flatten, FlattenCtx};
    use crate::grammar::ModuleParser;
    use crate::options::CompileOptions;
    use crate::scopes::resolve_scopes;
    use indoc::indoc;

    use super::infer_rule_scopes;

    #[test]
    fn scopes_follow_receivers_and_reject_cross_model_writes_and_reads() {
        let mut ast = Ast::default();
        let module = ModuleParser::new()
            .parse(
                &mut ast,
                indoc! {"
            type Atom;
            model Box { pred p(Atom); pred q(Atom); }
            pred ambient(Atom);
            rule local { if b: Box; if b.p(x); then b.q(x); }
            rule cross { if a: Box; if b: Box; if a.p(x); then b.q(x); }
            rule read_ambient { if b: Box; if ambient(x); then b.q(x); }
            rule write_ambient { if b: Box; if b.p(x); then ambient(x); }
        "},
            )
            .unwrap();
        let scopes = resolve_scopes(&ast, module).unwrap();
        let (signature, errors) = build_signature(&ast, &scopes, module);
        assert!(errors.is_empty());
        let (structures, errors) = build_structures(&ast, &scopes, &signature, module);
        assert!(errors.is_empty());
        let ctx = FlattenCtx::new(&ast, module, &signature, &structures);
        let mut groups = flatten(&ctx, &CompileOptions::default());
        infer_rule_scopes(&mut groups, &signature);
        for (name, local) in [
            ("local", true),
            ("cross", false),
            ("read_ambient", true),
            ("write_ambient", false),
        ] {
            let group = groups.iter().find(|group| group.name == name).unwrap();
            assert!(
                group
                    .rules
                    .iter()
                    .all(|rule| rule.scope.model().is_some() == local),
                "{name}"
            );
        }
    }
}
