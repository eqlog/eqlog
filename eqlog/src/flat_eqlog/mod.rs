mod ast;
mod index_selection;
mod resolve_age_all_queries;
mod slice_group_by;
mod sort_if_stmts;
mod var_info;

use std::{
    collections::{BTreeMap, BTreeSet},
    iter::once,
};

use crate::eqlog_util::*;
pub use ast::*;
use by_address::ByAddress;
use eqlog_eqlog::*;
pub use index_selection::*;
pub use resolve_age_all_queries::*;
pub use sort_if_stmts::*;
use var_info::*;
pub use var_info::{CanAssumeFunctionality, RelationInfo};

pub fn functionality_v2(func: Func, eqlog: &Eqlog) -> FlatRule {
    let domain = type_list_vec(
        eqlog
            .flat_domain(func)
            .expect("flat_domain should be total"),
        eqlog,
    );
    let codomain = eqlog.codomain(func).expect("codomain should be total");

    let rel = eqlog.func_rel(func).unwrap();
    let func_args: Vec<FlatVar> = (0..domain.len()).map(FlatVar).collect();
    let result0 = FlatVar(domain.len());
    let result1 = FlatVar(domain.len() + 1);

    let rel_args0: Vec<FlatVar> = func_args.iter().copied().chain(once(result0)).collect();
    let rel_args1: Vec<FlatVar> = func_args.iter().copied().chain(once(result1)).collect();

    let dirty_rel = FlatIfStmtRelation {
        rel,
        args: rel_args0,
        age: QueryAge::New,
    };
    let non_dirty_rel = FlatIfStmtRelation {
        rel,
        args: rel_args1,
        age: QueryAge::All,
    };
    let eq = FlatStmtEqual {
        lhs: result0,
        rhs: result1,
    };

    let stmts = vec![
        FlatStmt::If(FlatIfStmt::Relation(dirty_rel)),
        FlatStmt::If(FlatIfStmt::Relation(non_dirty_rel)),
        FlatStmt::SurjThen(FlatSurjThenStmt::Equal(eq)),
    ];

    let flat_func = FlatFunc {
        name: FlatFuncName(0),
        args: Vec::new(),
        body: stmts,
    };
    let var_types: BTreeMap<FlatVar, Type> = func_args
        .iter()
        .copied()
        .zip(domain)
        .chain([(result0, codomain), (result1, codomain)])
        .collect();
    let name = format!("implicit_functionality_{}", func.0);

    FlatRule {
        funcs: vec![flat_func],
        var_types,
        name,
    }
}

pub struct FlatRuleAnalysis<'a> {
    /// The name of the [FlatRule].
    pub rule_name: &'a str,
    /// The types of [FlatVar]s.
    ///
    /// This is currently just a reference to the corresponding field in [FlatRule], but perhaps
    /// this field should live here instead.
    pub var_types: &'a BTreeMap<FlatVar, Type>,
    /// A map that assigns to each suffix of consecutive statements in a rule the set of variables
    /// that are already bound before those statements.
    // TODO: Why isn't this ever used?
    #[allow(unused)]
    pub fixed_vars: BTreeMap<ByAddress<&'a [FlatStmt]>, BTreeSet<FlatVar>>,
    /// A map that assigns to each [FlatIfStmtRelation] in a rule some additional information.
    pub if_stmt_rel_infos: BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo>,

    pub used_rels: Vec<Rel>,
    pub used_types: Vec<Type>,
    pub used_queries: Vec<(Rel, QuerySpec)>,
}

fn collect_used_rels(rule: &FlatRule, eqlog: &Eqlog) -> Vec<Rel> {
    let mut used_rels = BTreeSet::new();

    for func in &rule.funcs {
        for stmt in &func.body {
            match stmt {
                FlatStmt::If(stmt) => match stmt {
                    FlatIfStmt::Relation(stmt) => {
                        used_rels.insert(stmt.rel);
                    }
                    FlatIfStmt::Equal(_) | FlatIfStmt::Type(_) => {}
                    FlatIfStmt::Range(_) => todo!(),
                },
                FlatStmt::SurjThen(stmt) => match stmt {
                    FlatSurjThenStmt::Relation(stmt) => {
                        used_rels.insert(stmt.rel);
                    }
                    FlatSurjThenStmt::Equal(_) => {}
                },
                FlatStmt::NonSurjThen(stmt) => {
                    used_rels.insert(eqlog.func_rel(stmt.func).unwrap());
                }
                FlatStmt::Call { .. } => {}
                FlatStmt::DefineRange(_) => todo!(),
            }
        }
    }

    used_rels.into_iter().collect()
}

fn collect_non_surj_then_queries<'a>(
    rule: &FlatRule,
    non_surj_then_queries: &mut BTreeSet<(Rel, QuerySpec)>,
    eqlog: &Eqlog,
) {
    for func in &rule.funcs {
        for stmt in func.body.iter() {
            match stmt {
                FlatStmt::If(_) | FlatStmt::SurjThen(_) | FlatStmt::Call { .. } => {}
                FlatStmt::DefineRange(_) => todo!(),
                FlatStmt::NonSurjThen(non_surj_then_stmt) => {
                    let specs = QuerySpec::eval_func(non_surj_then_stmt.func, eqlog);
                    let func_rel = eqlog.func_rel(non_surj_then_stmt.func).unwrap();
                    non_surj_then_queries.extend(specs.into_iter().map(|spec| (func_rel, spec)));
                }
            }
        }
    }
}

impl<'a> FlatRuleAnalysis<'a> {
    pub fn new(
        rule: &'a FlatRule,
        can_assume_functionality: CanAssumeFunctionality,
        eqlog: &Eqlog,
    ) -> Self {
        let fixed_vars = fixed_vars(rule);
        let if_stmt_rel_infos = if_stmt_rel_infos(rule, can_assume_functionality, &fixed_vars);

        let mut used_queries = if_stmt_rel_infos
            .iter()
            .map(|(_, info)| {
                let rel = info.rel;
                let spec = QuerySpec {
                    projections: info.in_projections.keys().copied().collect(),
                    diagonals: info.diagonals.clone(),
                    age: info.age,
                };
                (rel, spec)
            })
            .collect();

        collect_non_surj_then_queries(rule, &mut used_queries, eqlog);
        let used_queries: Vec<(Rel, QuerySpec)> = used_queries.into_iter().collect();

        let used_rels = collect_used_rels(rule, eqlog);
        let used_types: BTreeSet<Type> = rule.var_types.values().copied().collect();
        let used_types: Vec<Type> = used_types.into_iter().collect();

        Self {
            rule_name: rule.name.as_str(),
            var_types: &rule.var_types,
            fixed_vars,
            if_stmt_rel_infos,
            used_queries,
            used_rels,
            used_types,
        }
    }
}
