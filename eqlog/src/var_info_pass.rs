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
            FlatStmt::Fork(blocks) => {
                for stmts in blocks {
                    fixed_vars_rec(stmts, current_fixed_vars.clone(), all_fixed_vars);
                }
                let shared_used_vars = blocks
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

pub fn fixed_vars_pass<'a>(rule: &'a FlatRule) -> FixedVars<'a> {
    let current_fixed_vars = BTreeSet::new();
    let mut all_fixed_vars = FixedVars(BTreeMap::new());
    fixed_vars_rec(&rule.stmts, current_fixed_vars, &mut all_fixed_vars);
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
    diagonals: BTreeSet<BTreeSet<usize>>,

    /// The set of argument indices where an already fixed variable is passed.
    in_projections: BTreeMap<usize, FlatVar>,

    /// The set of new (not already fixed) variables among the arguments, and one argument index
    /// where the new variable occurs.
    out_projections: BTreeMap<FlatVar, usize>,

    /// Whether it suffices to consider a single match for the relation ([Quantifier::Any]), or
    /// whether all matches must be considered ([Quantifier::All]).
    quantifier: Quantifier,
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

fn out_projections(args: &[FlatVar], fixed_vars: &BTreeSet<FlatVar>) -> BTreeMap<FlatVar, usize> {
    args.iter()
        .copied()
        .enumerate()
        .filter_map(|(i, var)| (!fixed_vars.contains(&var)).then_some((var, i)))
        .collect()
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum CanAssumeFunctionality {
    Yes,
    No,
}

fn quantifier(
    rel: Rel,
    args: &[FlatVar],
    func_assumption: CanAssumeFunctionality,
    fixed_vars: &BTreeSet<FlatVar>,
) -> Quantifier {
    let all_args_fixed = args.iter().all(|arg| fixed_vars.contains(&arg));
    if all_args_fixed {
        return Quantifier::Any;
    }

    if func_assumption == CanAssumeFunctionality::Yes && matches!(rel, Rel::Func(_)) {
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

pub fn relation_info_pass<'a>(
    func_assumption: CanAssumeFunctionality,
    fixed_vars: &FixedVars<'a>,
) -> RelationInfos<'a> {
    let mut infos = RelationInfos(BTreeMap::new());
    for (ByAddress(stmt), fixed_vars) in fixed_vars.0.iter() {
        let stmt = match stmt {
            FlatStmt::If(FlatIfStmt::Relation(stmt)) => stmt,
            _ => {
                continue;
            }
        };
        let FlatIfStmtRelation {
            rel,
            args,
            only_dirty: _,
        } = stmt;
        let info = RelationInfo {
            diagonals: diagonals(args.as_slice()),
            in_projections: in_projections(args.as_slice(), fixed_vars),
            out_projections: out_projections(args.as_slice(), fixed_vars),
            quantifier: quantifier(*rel, args.as_slice(), func_assumption, fixed_vars),
        };
        infos.0.insert(ByAddress(stmt), info);
    }
    infos
}
