use itertools::Itertools;
use std::collections::BTreeSet;

use super::ast::*;

#[derive(Copy, Clone, PartialEq, Eq)]
struct IfStmtGoodness {
    is_equal: bool,
    age: QueryAge,
    new_variables: usize,
    restrained_variables: usize,
}

impl Default for IfStmtGoodness {
    fn default() -> Self {
        IfStmtGoodness {
            is_equal: false,
            age: QueryAge::All,
            new_variables: 0,
            restrained_variables: 0,
        }
    }
}

fn cmp_age_goodness(lhs: QueryAge, rhs: QueryAge) -> std::cmp::Ordering {
    let lhs_is_new = matches!(lhs, QueryAge::New);
    let rhs_is_new = matches!(rhs, QueryAge::New);
    lhs_is_new.cmp(&rhs_is_new)
}

impl Ord for IfStmtGoodness {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // True is better than false.
        let is_equal = self.is_equal.cmp(&other.is_equal);
        // True is better than false.
        let age_goodness = cmp_age_goodness(self.age, other.age);
        // Smaller is better than greater.
        let new_variables = self.new_variables.cmp(&other.new_variables).reverse();
        // Greater is better than smaller.
        let restrained_variables = self.restrained_variables.cmp(&other.restrained_variables);

        is_equal
            .then(age_goodness)
            .then(new_variables)
            .then(restrained_variables)
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
        age: QueryAge::New,
        new_variables: 2,
        ..IfStmtGoodness::default()
    };
    let arbitrary = IfStmtGoodness {
        age: QueryAge::All,
        ..IfStmtGoodness::default()
    };
    assert!(only_dirty > arbitrary);
}

#[test]
fn less_new_variables_is_better() {
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

#[test]
fn more_restrained_variables_is_better() {
    let few_vars = IfStmtGoodness {
        restrained_variables: 2,
        ..IfStmtGoodness::default()
    };
    let many_vars = IfStmtGoodness {
        restrained_variables: 3,
        ..IfStmtGoodness::default()
    };
    assert!(many_vars > few_vars);
}

fn if_stmt_goodness(stmt: &FlatIfStmt, fixed_vars: &BTreeSet<FlatVar>) -> IfStmtGoodness {
    let is_equal = match stmt.rel {
        FlatInRel::Equality(_) => true,
        FlatInRel::EqlogRel(_)
        | FlatInRel::TypeSet(_)
        | FlatInRel::EqlogRelWithDiagonals { .. } => false,
    };
    let age = stmt.age;
    let new_variables = stmt
        .args
        .iter()
        .unique()
        .filter(|var| !fixed_vars.contains(var))
        .count();
    let restrained_variables = stmt
        .args
        .iter()
        .unique()
        .filter(|var| fixed_vars.contains(var))
        .count();
    IfStmtGoodness {
        is_equal,
        age,
        new_variables,
        restrained_variables,
    }
}

fn find_best_index(stmts: &[FlatIfStmt], fixed_vars: &BTreeSet<FlatVar>) -> Option<usize> {
    (0..stmts.len()).max_by_key(|i| if_stmt_goodness(&stmts[*i], fixed_vars))
}

/// A pass that optimizes the order of [FlatIfStmt]s in the premise of a [FlatRule].
pub fn sort_premise<'a>(rule: &mut FlatRule) {
    let premise = &mut rule.premise;
    let mut fixed_vars: BTreeSet<FlatVar> = BTreeSet::new();
    for sorted_until in 0..premise.len() {
        let best_index = sorted_until
            + find_best_index(&premise[sorted_until..], &fixed_vars)
                .expect("a non-empty slice of if statements should have a best element");
        fixed_vars.extend(premise[best_index].args.iter().cloned());
        premise.swap(sorted_until, best_index);
    }
}
