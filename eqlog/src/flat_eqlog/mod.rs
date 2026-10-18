mod ast;
mod category;
mod diagonals;
mod index_selection;
mod morphisms;
mod schedule;
mod scope;
mod semi_naive;
mod sort;

use std::{iter::once, sync::Arc};

use crate::algebra::signature::{FuncId, Signature};
use crate::options::EvaluationMode;

pub use ast::*;
pub use category::*;
pub use diagonals::*;
pub use index_selection::*;
pub use morphisms::*;
pub use schedule::*;
pub use scope::*;
pub use semi_naive::*;
pub use sort::*;

pub fn functionality_anchor(rule: &FlatRule) -> Option<&FlatVar> {
    let [first, second] = rule.premise.as_slice() else {
        return None;
    };
    let [output] = rule.conclusion.as_slice() else {
        return None;
    };
    match first.rel {
        FlatInRel::Rel(FlatRel::Func(_)) => {}
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
        | FlatInRel::RelWithDiagonals { .. }
        | FlatInRel::TypeSet(_)
        | FlatInRel::Equality(_) => return None,
    }
    match (first.age, second.age) {
        (QueryAge::New | QueryAge::All, QueryAge::All) => {}
        (QueryAge::Old, QueryAge::All)
        | (QueryAge::New | QueryAge::All | QueryAge::Old, QueryAge::New | QueryAge::Old) => {
            return None;
        }
    }
    if first.rel != second.rel {
        return None;
    }
    let (first_result, first_domain) = first.args.split_last()?;
    let (second_result, second_domain) = second.args.split_last()?;
    if first_domain != second_domain
        || first_result == second_result
        || first_domain.contains(first_result)
        || first_domain.contains(second_result)
    {
        return None;
    }
    match output.rel {
        FlatOutRel::Equality(typ) if typ == first_result.typ && typ == second_result.typ => {}
        FlatOutRel::Equality(_) | FlatOutRel::Rel(_) | FlatOutRel::FuncDomain(_) => return None,
    }
    let [lhs, rhs] = output.args.as_slice() else {
        return None;
    };
    ((lhs == first_result && rhs == second_result) || (lhs == second_result && rhs == first_result))
        .then_some(second_result)
}

pub fn functionality_rule(
    func: FuncId,
    signature: &Signature,
    rule_name: impl Into<String>,
    evaluation_mode: EvaluationMode,
) -> FlatRule {
    let domain = flat_domain(func, signature);
    let codomain = signature.func(func).codomain;

    let func_rel = FlatInRel::Rel(FlatRel::Func(func));

    let func_args: Vec<FlatVar> = (0..domain.len())
        .map(|i| {
            let typ = domain[i];
            let name = Arc::from(format!("arg{i}"));
            FlatVar { name, typ }
        })
        .collect();

    let result0 = FlatVar {
        name: Arc::from("result0".to_string()),
        typ: codomain,
    };
    let result1 = FlatVar {
        name: Arc::from("result1".to_string()),
        typ: codomain,
    };

    let rel_args0: Vec<FlatVar> = func_args
        .iter()
        .cloned()
        .chain(once(result0.clone()))
        .collect();
    let rel_args1: Vec<FlatVar> = func_args.into_iter().chain(once(result1.clone())).collect();

    let premise = vec![
        FlatIfStmt {
            rel: func_rel.clone(),
            args: rel_args0,
            age: match evaluation_mode {
                EvaluationMode::Naive => QueryAge::All,
                EvaluationMode::SemiNaive => QueryAge::New,
            },
        },
        FlatIfStmt {
            rel: func_rel.clone(),
            args: rel_args1,
            age: QueryAge::All,
        },
    ];

    let conclusion = vec![FlatThenStmt {
        rel: FlatOutRel::Equality(codomain),
        args: vec![result0, result1],
    }];

    FlatRule {
        scope: RuleScope::Global,
        name: rule_name.into(),
        premise,
        conclusion,
    }
}
