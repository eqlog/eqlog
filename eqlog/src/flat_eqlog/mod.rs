mod ast;
//mod index_selection;
//mod range;
//mod resolve_age_all_queries;
//mod slice_group_by;
//mod sort_if_stmts;
//mod var_info;

use std::{
    iter::once,
    sync::Arc,
};

use crate::eqlog_util::*;
pub use ast::*;
use eqlog_eqlog::*;
//pub use index_selection::*;
//pub use range::*;
//pub use resolve_age_all_queries::*;
//pub use sort_if_stmts::*;
//use var_info::*;
//pub use var_info::{CanAssumeFunctionality, RelationInfo};

pub fn functionality(func: Func, eqlog: &Eqlog) -> FlatRule {
    let domain = type_list_vec(
        eqlog
            .flat_domain(func)
            .expect("flat_domain should be total"),
        eqlog,
    );
    let codomain = eqlog.codomain(func).expect("codomain should be total");

    let func_rel = FlatInRel::EqlogRel(
        eqlog.func_rel(func).expect("func_rel should be total"),
    );


    let func_args: Vec<FlatVar> = (0..domain.len()).map(|i| {
        let typ = domain[i];
        let name = Arc::from(format!("arg{i}"));
        FlatVar { name, typ }
    }).collect();

    let result0 = FlatVar {
        name: Arc::from("result0".to_string()),
        typ: codomain,
    };
    let result1 = FlatVar {
        name: Arc::from("result1".to_string()),
        typ: codomain,
    };

    let rel_args0: Vec<FlatVar> = func_args.iter().cloned().chain(once(result0.clone())).collect();
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

    let conclusion = vec![
        FlatThenStmt {
            rel: FlatOutRel::Equality(codomain),
            args: vec![result0, result1],
        }
    ];

    let name = format!("functionality_{}", func.0);

    FlatRule {
        name,
        premise,
        conclusion,
    }
}

//pub struct FlatRuleAnalysis<'a> {
//    /// The name of the [FlatRule].
//    pub rule_name: &'a str,
//    /// The types of [FlatVar]s.
//    ///
//    /// This is currently just a reference to the corresponding field in [FlatRule], but perhaps
//    /// this field should live here instead.
//    pub var_types: &'a BTreeMap<FlatVar, Type>,
//    /// A map that assigns to each suffix of consecutive statements in a rule the set of variables
//    /// that are already bound before those statements.
//    // TODO: Why isn't this ever used?
//    #[allow(unused)]
//    pub fixed_vars: BTreeMap<ByAddress<&'a [FlatStmt]>, BTreeSet<FlatVar>>,
//    /// A map that assigns to each [FlatIfStmtRelation] in a rule some additional information.
//    pub if_stmt_rel_infos: BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo>,
//
//    pub used_rels: Vec<Rel>,
//    pub used_types: Vec<Type>,
//    pub used_queries: Vec<(Rel, QuerySpec)>,
//}
//
//fn collect_used_rels(rule: &FlatRule, eqlog: &Eqlog) -> Vec<Rel> {
//    let mut used_rels = BTreeSet::new();
//
//    for func in &rule.funcs {
//        for stmt in &func.body {
//            match stmt {
//                FlatStmt::If(stmt) => match stmt {
//                    FlatIfStmt::Relation(stmt) => {
//                        used_rels.insert(stmt.rel);
//                    }
//                    FlatIfStmt::Equal(_) | FlatIfStmt::Type(_) => {}
//                    FlatIfStmt::Range(_) => todo!(),
//                },
//                FlatStmt::SurjThen(stmt) => match stmt {
//                    FlatSurjThenStmt::Relation(stmt) => {
//                        used_rels.insert(stmt.rel);
//                    }
//                    FlatSurjThenStmt::Equal(_) => {}
//                },
//                FlatStmt::NonSurjThen(stmt) => {
//                    used_rels.insert(eqlog.func_rel(stmt.func).unwrap());
//                }
//                FlatStmt::Call { .. } => {}
//                FlatStmt::DefineRange(_) => todo!(),
//            }
//        }
//    }
//
//    used_rels.into_iter().collect()
//}
//
//fn collect_non_surj_then_queries<'a>(
//    rule: &FlatRule,
//    non_surj_then_queries: &mut BTreeSet<(Rel, QuerySpec)>,
//    eqlog: &Eqlog,
//) {
//    for func in &rule.funcs {
//        for stmt in func.body.iter() {
//            match stmt {
//                FlatStmt::If(_) | FlatStmt::SurjThen(_) | FlatStmt::Call { .. } => {}
//                FlatStmt::DefineRange(_) => todo!(),
//                FlatStmt::NonSurjThen(non_surj_then_stmt) => {
//                    let specs = QuerySpec::eval_func(non_surj_then_stmt.func, eqlog);
//                    let func_rel = eqlog.func_rel(non_surj_then_stmt.func).unwrap();
//                    non_surj_then_queries.extend(specs.into_iter().map(|spec| (func_rel, spec)));
//                }
//            }
//        }
//    }
//}
//
//impl<'a> FlatRuleAnalysis<'a> {
//    pub fn new(
//        rule: &'a FlatRule,
//        can_assume_functionality: CanAssumeFunctionality,
//        eqlog: &Eqlog,
//    ) -> Self {
//        let fixed_vars = fixed_vars(rule);
//        let if_stmt_rel_infos = if_stmt_rel_infos(rule, can_assume_functionality, &fixed_vars);
//
//        let mut used_queries = if_stmt_rel_infos
//            .iter()
//            .map(|(_, info)| {
//                let rel = info.rel;
//                let spec = QuerySpec {
//                    projections: info.in_projections.keys().copied().collect(),
//                    diagonals: info.diagonals.clone(),
//                    age: info.age,
//                };
//                (rel, spec)
//            })
//            .collect();
//
//        collect_non_surj_then_queries(rule, &mut used_queries, eqlog);
//        let used_queries: Vec<(Rel, QuerySpec)> = used_queries.into_iter().collect();
//
//        let used_rels = collect_used_rels(rule, eqlog);
//        let used_types: BTreeSet<Type> = rule.var_types.values().copied().collect();
//        let used_types: Vec<Type> = used_types.into_iter().collect();
//
//        Self {
//            rule_name: rule.name.as_str(),
//            var_types: &rule.var_types,
//            fixed_vars,
//            if_stmt_rel_infos,
//            used_queries,
//            used_rels,
//            used_types,
//        }
//    }
//}
