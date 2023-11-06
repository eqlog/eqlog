use itertools::Itertools;
use std::collections::BTreeSet;

use crate::flat_eqlog::*;
use crate::slice_group_by::*;

#[derive(Default, Copy, Clone, PartialEq, Eq)]
struct IfStmtGoodness {
    is_equal: bool,
    only_dirty: bool,
    new_variables: usize,
}

impl Ord for IfStmtGoodness {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // True is better than false.
        let is_equal = self.is_equal.cmp(&other.is_equal);
        // True is better than false.
        let only_dirty = self.only_dirty.cmp(&other.only_dirty);
        // Smaller is better than greater.
        let new_variables = self.new_variables.cmp(&other.new_variables).reverse();

        is_equal.then(only_dirty).then(new_variables)
    }
}

impl PartialOrd for IfStmtGoodness {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[test]
fn equal_is_better() {
    let is_equal = IfStmtGoodness {
        is_equal: true,
        new_variables: 2,
        ..IfStmtGoodness::default()
    };
    let is_not_equal = IfStmtGoodness {
        is_equal: false,
        ..IfStmtGoodness::default()
    };
    assert!(is_equal > is_not_equal);
}

#[test]
fn only_dirty_is_better() {
    let only_dirty = IfStmtGoodness {
        only_dirty: true,
        new_variables: 2,
        ..IfStmtGoodness::default()
    };
    let arbitrary = IfStmtGoodness {
        only_dirty: false,
        ..IfStmtGoodness::default()
    };
    assert!(only_dirty > arbitrary);
}

#[test]
fn less_variables_is_better() {
    let few_vars = IfStmtGoodness {
        new_variables: 2,
        ..IfStmtGoodness::default()
    };
    let many_vars = IfStmtGoodness {
        new_variables: 3,
        ..IfStmtGoodness::default()
    };
    assert!(few_vars > many_vars);
}

fn if_stmt_goodness(stmt: &FlatIfStmt, fixed_vars: &BTreeSet<FlatVar>) -> IfStmtGoodness {
    let is_equal = matches!(stmt, FlatIfStmt::Equal(_));
    let only_dirty = match stmt {
        FlatIfStmt::Equal(_) => false,
        FlatIfStmt::Relation(FlatIfStmtRelation { only_dirty, .. }) => *only_dirty,
        FlatIfStmt::Type(FlatIfStmtType { only_dirty, .. }) => *only_dirty,
    };
    let new_variables = stmt
        .iter_vars()
        .unique()
        .filter(|var| !fixed_vars.contains(&var))
        .count();
    IfStmtGoodness {
        is_equal,
        only_dirty,
        new_variables,
    }
}

fn find_best_index(stmts: &[FlatIfStmt], fixed_vars: &BTreeSet<FlatVar>) -> Option<usize> {
    (0..stmts.len()).max_by_key(|i| if_stmt_goodness(&stmts[*i], fixed_vars))
}

fn sort_if_block<'a>(if_stmts: &mut [FlatIfStmt], fixed_vars: &mut BTreeSet<FlatVar>) {
    for sorted_until in 0..if_stmts.len() {
        let best_index = sorted_until
            + find_best_index(&if_stmts[sorted_until..], fixed_vars)
                .expect("a non-empty slice of if statements should have a best element");
        fixed_vars.extend(if_stmts[best_index].iter_vars());
        if_stmts.swap(sorted_until, best_index);
    }
}

fn if_stmt(stmt: &FlatStmt) -> Option<&FlatIfStmt> {
    match stmt {
        FlatStmt::If(if_stmt) => Some(if_stmt),
        FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) | FlatStmt::Fork(_) => None,
    }
}

/// Recursively optimize the order of consecutive [FlatIfStmt] occurring in `stmts`.
///
/// `fixed_vars` should be the set of variables that are already fixed by prior statements.
/// This function extends `fixed_vars` by the variables that occur in `stmts`.
fn sort_if_stmts_rec<'a>(stmts: &mut [FlatStmt], fixed_vars: &mut BTreeSet<FlatVar>) {
    let stmt_groups = slice_group_by_mut(stmts, |before, after| {
        if_stmt(before).is_some() == if_stmt(after).is_some()
    });
    for stmt_group in stmt_groups {
        let first_stmt = stmt_group.first().expect("Groups should be non-empty");
        let is_if_group = if_stmt(&first_stmt).is_some();
        if is_if_group {
            let mut if_stmts: Vec<FlatIfStmt> = stmt_group
                .iter()
                .map(|stmt| if_stmt(stmt).expect("Stmts in if stmt group should be if stmts"))
                .cloned()
                .collect();
            sort_if_block(if_stmts.as_mut_slice(), fixed_vars);
            assert_eq!(
                stmt_group.len(),
                if_stmts.len(),
                "Sorting an if block should not change its length"
            );
            for (stmt, if_stmt) in stmt_group.iter_mut().zip(if_stmts) {
                *stmt = FlatStmt::If(if_stmt);
            }
        } else {
            for stmt in stmt_group {
                match stmt {
                    FlatStmt::If(_) => {
                        panic!("An if statement should not occur in a non-if stmt group")
                    }
                    FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) => {
                        fixed_vars.extend(stmt.iter_vars());
                    }
                    FlatStmt::Fork(blocks) => {
                        for block in blocks.iter_mut() {
                            sort_if_stmts_rec(block.as_mut_slice(), &mut fixed_vars.clone());
                        }
                        fixed_vars.extend(stmt.iter_vars());
                    }
                }
            }
        }
    }
}

/// A pass that optimizes the order of  consecutive [FlatIfStmt] in `rule`.
pub fn sort_if_stmts_pass<'a>(rule: &mut FlatRule) {
    let mut fixed_vars = BTreeSet::new();
    sort_if_stmts_rec(&mut rule.stmts, &mut fixed_vars);
}
