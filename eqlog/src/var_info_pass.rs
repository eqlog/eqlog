#![allow(dead_code)]

use crate::flat_eqlog::*;
use by_address::ByAddress;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};

pub struct FixedVars<'a>(pub BTreeMap<ByAddress<&'a FlatStmt>, BTreeSet<FlatVar>>);

pub fn fixed_vars_rec<'a>(
    stmts: &'a [FlatStmt],
    mut current_fixed_vars: BTreeSet<FlatVar>,
    all_fixed_vars: &mut FixedVars<'a>,
) {
    for stmt in stmts {
        all_fixed_vars
            .0
            .insert(ByAddress(stmt), current_fixed_vars.clone());
        match stmt {
            FlatStmt::If(_) | FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) => {
                current_fixed_vars.extend(stmt.iter_vars());
            }
            FlatStmt::Fork(fork_stmt) => {
                for stmts in fork_stmt.blocks.iter() {
                    fixed_vars_rec(stmts, current_fixed_vars.clone(), all_fixed_vars);
                }
                let shared_used_vars = fork_stmt
                    .blocks
                    .iter()
                    .map(|block_stmts| -> BTreeSet<FlatVar> {
                        block_stmts
                            .iter()
                            .map(|stmt| stmt.iter_vars())
                            .flatten()
                            .collect()
                    })
                    .reduce(|lhs, rhs| lhs.intersection(&rhs).copied().collect())
                    .expect("There should be at least one block");
                current_fixed_vars.extend(shared_used_vars);
            }
        }
    }
}

pub fn fixed_vars_pass<'a>(rules: impl Iterator<Item = &'a FlatRule>) -> FixedVars<'a> {
    let mut all_fixed_vars = FixedVars(BTreeMap::new());
    for rule in rules {
        let current_fixed_vars = BTreeSet::new();
        fixed_vars_rec(&rule.stmts, current_fixed_vars, &mut all_fixed_vars);
    }
    all_fixed_vars
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum Quantifier {
    All,
    Any,
}

/// Annotation of a [FlatIfStmt] that takes the context of the statement into account.
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
}

pub struct RelationInfos<'a>(pub BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo>);

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
    infos: &mut RelationInfos<'a>,
    fixed_vars: &FixedVars<'a>,
) {
    for stmt in stmts {
        match stmt {
            FlatStmt::If(if_stmt) => match if_stmt {
                FlatIfStmt::Equal(_) | FlatIfStmt::Type(_) => (),
                FlatIfStmt::Relation(rel_if_stmt) => {
                    let fixed_vars = fixed_vars.0.get(&ByAddress(stmt)).unwrap();
                    let FlatIfStmtRelation {
                        rel,
                        args,
                        only_dirty: _,
                    } = rel_if_stmt;

                    let _quantifier =
                        quantifier(*rel, args.as_slice(), can_assume_functionality, fixed_vars);

                    let info = RelationInfo {
                        diagonals: diagonals(args.as_slice()),
                        in_projections: in_projections(args.as_slice(), fixed_vars),
                        out_projections: out_projections(args.as_slice(), fixed_vars),
                    };
                    infos.0.insert(ByAddress(rel_if_stmt), info);
                }
            },
            FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) => (),
            FlatStmt::Fork(fork_stmt) => {
                for block in fork_stmt.blocks.iter() {
                    relation_info_rec(block, can_assume_functionality, infos, fixed_vars);
                }
            }
        }
    }
}

pub fn relation_info_pass<'a>(
    rules: impl Iterator<Item = (&'a FlatRule, CanAssumeFunctionality)>,
    fixed_vars: &FixedVars<'a>,
) -> RelationInfos<'a> {
    let mut infos = RelationInfos(BTreeMap::new());
    for (rule, can_assume_functionality) in rules {
        relation_info_rec(
            rule.stmts.as_slice(),
            can_assume_functionality,
            &mut infos,
            fixed_vars,
        );
    }
    infos
}
