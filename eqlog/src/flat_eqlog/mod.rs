mod ast;
mod diagonals;
mod index_selection;
mod semi_naive;
mod sort;

use std::{iter::once, sync::Arc};

use crate::algebra::signature::{FuncId, Signature};

pub use ast::*;
pub use diagonals::*;
pub use index_selection::*;
pub use semi_naive::*;
pub use sort::*;

pub fn semi_naive_functionality(
    func: FuncId,
    signature: &Signature,
    rule_name: impl Into<String>,
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
            age: QueryAge::New,
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
        name: rule_name.into(),
        premise,
        conclusion,
    }
}
