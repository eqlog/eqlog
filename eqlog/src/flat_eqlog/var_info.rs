#![allow(dead_code)]

use super::ast::*;
use by_address::ByAddress;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};

fn fixed_vars_rec<'a>(
    stmts: &'a [FlatStmt],
    mut current_fixed_vars: BTreeSet<FlatVar>,
    all_fixed_vars: &mut BTreeMap<ByAddress<&'a [FlatStmt]>, BTreeSet<FlatVar>>,
) {
    for i in 0..stmts.len() {
        let suffix = &stmts[i..];
        all_fixed_vars.insert(ByAddress(suffix), current_fixed_vars.clone());

        let stmt = &stmts[i];
        match stmt {
            FlatStmt::If(_)
            | FlatStmt::SurjThen(_)
            | FlatStmt::NonSurjThen(_)
            | FlatStmt::Call { .. } => {
                current_fixed_vars.extend(stmt.iter_vars());
            }
        }
    }
    let empty_suffix = &stmts[stmts.len()..];
    all_fixed_vars.insert(ByAddress(empty_suffix), current_fixed_vars);
}

pub fn fixed_vars<'a>(
    rule: &'a FlatRule,
) -> BTreeMap<ByAddress<&'a [FlatStmt]>, BTreeSet<FlatVar>> {
    let mut all_fixed_vars = BTreeMap::new();
    for func in rule.funcs.iter() {
        let current_fixed_vars = func.args.iter().copied().collect();
        fixed_vars_rec(
            func.body.as_slice(),
            current_fixed_vars,
            &mut all_fixed_vars,
        );
    }
    all_fixed_vars
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Quantifier {
    All,
    Any,
}

/// Annotation of a [FlatIfStmt] that takes the context of the statement into account.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RelationInfo {
    /// The set of non-trivial diagonals among arguments.
    ///
    /// A diagonal is a maximal set of argument indices in which the same variable is passed. The
    /// diagonal is non-trivial if it has more than one element.
    pub diagonals: BTreeSet<BTreeSet<usize>>,

    /// The set of argument indices where an already fixed variable is passed.
    pub in_projections: BTreeMap<usize, FlatVar>,

    /// The list of new (i.e., not already fixed) variables among arguments. A [FlatVar] must not
    /// occur twice; in case of a diagonal any one entry should be in the map.
    pub out_projections: BTreeMap<usize, FlatVar>,

    /// Whether it suffices to consider one match of the variables in the rel statement
    /// ([Quantifier::Any]), or if all matches must be considered ([Quantifier::All]).
    pub quantifier: Quantifier,
}

fn diagonals(args: &[FlatVar]) -> BTreeSet<BTreeSet<usize>> {
    let mut enumerated_args: Vec<(usize, FlatVar)> = args.iter().copied().enumerate().collect();
    enumerated_args.sort_by_key(|(_, tm)| *tm);

    enumerated_args
        .iter()
        .group_by(|(_, tm)| tm)
        .into_iter()
        .map(|(_, group)| -> BTreeSet<usize> { group.map(|(i, _)| *i).collect() })
        .filter(|diagonal| diagonal.len() > 1)
        .collect()
}

fn in_projections(args: &[FlatVar], fixed_vars: &BTreeSet<FlatVar>) -> BTreeMap<usize, FlatVar> {
    args.iter()
        .copied()
        .enumerate()
        .filter(|(_, var)| fixed_vars.contains(var))
        .collect()
}

fn out_projections(args: &[FlatVar], fixed_vars: &BTreeSet<FlatVar>) -> BTreeMap<usize, FlatVar> {
    let out_projs: BTreeMap<FlatVar, usize> = args
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(i, var)| (!fixed_vars.contains(&var)).then_some((var, i)))
        .collect();
    out_projs.into_iter().map(|(var, i)| (i, var)).collect()
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum CanAssumeFunctionality {
    Yes,
    No,
}

fn quantifier(
    rel: Rel,
    args: &[FlatVar],
    can_assume_functionality: CanAssumeFunctionality,
    fixed_vars: &BTreeSet<FlatVar>,
) -> Quantifier {
    let all_args_fixed = args.iter().all(|arg| fixed_vars.contains(&arg));
    if all_args_fixed {
        return Quantifier::Any;
    }

    if can_assume_functionality == CanAssumeFunctionality::Yes && matches!(rel, Rel::Func(_)) {
        assert!(
            args.len() >= 1,
            "A function relation must have at least one argument"
        );
        let func_args = &args[0..args.len() - 1];
        let all_func_args_fixed = func_args.iter().all(|arg| fixed_vars.contains(&arg));
        if all_func_args_fixed {
            return Quantifier::Any;
        }
    }
    return Quantifier::All;
}

pub fn relation_info_rec<'a>(
    stmts: &'a [FlatStmt],
    can_assume_functionality: CanAssumeFunctionality,
    infos: &mut BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo>,
    fixed_vars: &BTreeMap<ByAddress<&'a [FlatStmt]>, BTreeSet<FlatVar>>,
) {
    for i in 0..stmts.len() {
        let stmt = &stmts[i];
        let tail = &stmts[i..];
        match stmt {
            FlatStmt::If(if_stmt) => match if_stmt {
                FlatIfStmt::Equal(_) | FlatIfStmt::Type(_) => (),
                FlatIfStmt::Relation(rel_if_stmt) => {
                    let fixed_vars = fixed_vars.get(&ByAddress(tail)).unwrap();
                    let FlatIfStmtRelation {
                        rel,
                        args,
                        only_dirty: _,
                    } = rel_if_stmt;

                    let info = RelationInfo {
                        diagonals: diagonals(args.as_slice()),
                        in_projections: in_projections(args.as_slice(), fixed_vars),
                        out_projections: out_projections(args.as_slice(), fixed_vars),
                        quantifier: quantifier(
                            *rel,
                            args.as_slice(),
                            can_assume_functionality,
                            fixed_vars,
                        ),
                    };
                    infos.insert(ByAddress(rel_if_stmt), info);
                }
            },
            FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) | FlatStmt::Call { .. } => (),
        }
    }
}

pub fn if_stmt_rel_infos<'a>(
    rule: &'a FlatRule,
    can_assume_functionality: CanAssumeFunctionality,
    fixed_vars: &BTreeMap<ByAddress<&'a [FlatStmt]>, BTreeSet<FlatVar>>,
) -> BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo> {
    let mut infos = BTreeMap::new();

    for func in rule.funcs.iter() {
        relation_info_rec(
            func.body.as_slice(),
            can_assume_functionality,
            &mut infos,
            fixed_vars,
        );
    }
    infos
}
