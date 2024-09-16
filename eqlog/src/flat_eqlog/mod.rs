mod ast;
mod index_selection;
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
pub use sort_if_stmts::sort_if_stmts;
use var_info::*;
pub use var_info::{CanAssumeFunctionality, RelationInfo};

pub fn functionality_v2(func: Func, eqlog: &Eqlog) -> FlatRule {
    if let None = eqlog.domain(func) {
        let semantic_arg_types: Vec<_> = eqlog.iter_semantic_arg_types().collect();
        indoc::printdoc! {"
            semantic_arg_types = {semantic_arg_types:?}
        "}
    }
    let domain = type_list_vec(eqlog.domain(func).expect("domain should be total"), eqlog);
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
        only_dirty: true,
    };
    let non_dirty_rel = FlatIfStmtRelation {
        rel,
        args: rel_args1,
        only_dirty: false,
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
}

impl<'a> FlatRuleAnalysis<'a> {
    pub fn new(rule: &'a FlatRule, can_assume_functionality: CanAssumeFunctionality) -> Self {
        let fixed_vars = fixed_vars(rule);
        let if_stmt_rel_infos = if_stmt_rel_infos(rule, can_assume_functionality, &fixed_vars);

        Self {
            rule_name: rule.name.as_str(),
            var_types: &rule.var_types,
            fixed_vars,
            if_stmt_rel_infos,
        }
    }
}
