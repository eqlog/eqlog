use itertools::Itertools;
use std::collections::BTreeSet;

use super::ast::*;

#[derive(Copy, Clone, PartialEq, Eq)]
struct IfStmtGoodness {
    is_equal: bool,
    age: QueryAge,
    bounded: bool,
    new_variables: usize,
    free_inputs: usize,
    restrained_variables: usize,
    consumed_result: bool,
}

impl Default for IfStmtGoodness {
    fn default() -> Self {
        IfStmtGoodness {
            is_equal: false,
            age: QueryAge::All,
            bounded: false,
            new_variables: 0,
            free_inputs: 0,
            restrained_variables: 0,
            consumed_result: false,
        }
    }
}

fn cmp_age_goodness(lhs: QueryAge, rhs: QueryAge) -> std::cmp::Ordering {
    let is_new = |age| match age {
        QueryAge::New => true,
        QueryAge::Old | QueryAge::All => false,
    };
    is_new(lhs).cmp(&is_new(rhs))
}

impl Ord for IfStmtGoodness {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // True is better than false.
        let is_equal = self.is_equal.cmp(&other.is_equal);
        // True is better than false.
        let age_goodness = cmp_age_goodness(self.age, other.age);
        let bounded = self.bounded.cmp(&other.bounded);
        // Smaller is better than greater.
        let new_variables = self.new_variables.cmp(&other.new_variables).reverse();
        // Greater is better than smaller.
        let restrained_variables = self.restrained_variables.cmp(&other.restrained_variables);
        let free_inputs = self.free_inputs.cmp(&other.free_inputs).reverse();
        let consumed_result = self.consumed_result.cmp(&other.consumed_result);

        is_equal
            .then(age_goodness)
            .then(bounded)
            .then(restrained_variables)
            .then(free_inputs)
            .then(new_variables)
            .then(consumed_result)
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

fn if_stmt_goodness(
    stmt: &FlatIfStmt,
    remaining: &[FlatIfStmt],
    fixed_vars: &BTreeSet<FlatVar>,
) -> IfStmtGoodness {
    let is_equal = match stmt.rel {
        FlatInRel::Equality(_) => true,
        FlatInRel::Rel(_) | FlatInRel::TypeSet(_) | FlatInRel::RelWithDiagonals { .. } => false,
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
    let free_inputs = match &stmt.rel {
        FlatInRel::Rel(FlatRel::Func(_)) => stmt.args[..stmt.args.len() - 1]
            .iter()
            .unique()
            .filter(|var| !fixed_vars.contains(var))
            .count(),
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
        | FlatInRel::RelWithDiagonals { .. }
        | FlatInRel::TypeSet(_)
        | FlatInRel::Equality(_) => new_variables,
    };
    // Bound domains are lookups. For remaining joins, prefer existing keys to
    // introducing an independent range whose size is hidden by a short tuple.
    let bounded = free_inputs == 0;
    // Prefer a computed join key to a terminal value when both queries bind
    // the same number of variables. Terminal values cannot constrain the join.
    let consumed_result = match &stmt.rel {
        FlatInRel::Rel(FlatRel::Func(_)) => stmt.args.last().is_some_and(|result| {
            !fixed_vars.contains(result)
                && remaining
                    .iter()
                    .any(|other| !std::ptr::eq(stmt, other) && other.args.contains(result))
        }),
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
        | FlatInRel::RelWithDiagonals { .. }
        | FlatInRel::TypeSet(_)
        | FlatInRel::Equality(_) => false,
    };
    IfStmtGoodness {
        is_equal,
        age,
        bounded,
        new_variables,
        free_inputs,
        restrained_variables,
        consumed_result,
    }
}

fn find_best_index(stmts: &[FlatIfStmt], fixed_vars: &BTreeSet<FlatVar>) -> Option<usize> {
    (0..stmts.len()).max_by_key(|i| if_stmt_goodness(&stmts[*i], stmts, fixed_vars))
}

/// A pass that optimizes the order of [FlatIfStmt]s in the premise of a [FlatRule].
pub fn sort_premise<'a>(rule: &mut FlatRule) {
    let premise = &mut rule.premise;
    let mut fixed_vars: BTreeSet<FlatVar> = rule.scope.owners().iter().cloned().collect();
    for sorted_until in 0..premise.len() {
        let best_index = sorted_until
            + find_best_index(&premise[sorted_until..], &fixed_vars)
                .expect("a non-empty slice of if statements should have a best element");
        fixed_vars.extend(premise[best_index].args.iter().cloned());
        premise.swap(sorted_until, best_index);
    }
}
