mod ast;
mod semi_naive;

use std::{iter::once, sync::Arc};

use crate::eqlog_util::*;
use eqlog_eqlog::*;

pub use ast::*;
pub use semi_naive::*;

pub fn semi_naive_functionality(func: Func, eqlog: &Eqlog) -> FlatRule {
    let domain = type_list_vec(
        eqlog
            .flat_domain(func)
            .expect("flat_domain should be total"),
        eqlog,
    );
    let codomain = eqlog.codomain(func).expect("codomain should be total");

    let func_rel = FlatInRel::EqlogRel(eqlog.func_rel(func).expect("func_rel should be total"));

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
            rel: func_rel,
            args: rel_args0,
            age: QueryAge::New,
        },
        FlatIfStmt {
            rel: func_rel,
            args: rel_args1,
            age: QueryAge::All,
        },
    ];

    let conclusion = vec![FlatThenStmt {
        rel: FlatOutRel::Equality(codomain),
        args: vec![result0, result1],
    }];

    let name = format!("functionality_{}", func.0);

    FlatRule {
        name,
        premise,
        conclusion,
    }
}
