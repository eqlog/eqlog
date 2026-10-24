use std::cmp::Reverse;
use std::collections::BTreeSet;

use crate::flat_eqlog::*;
use crate::options::ModelMode;
use crate::ram::*;

use super::flat_rule_to_ram;

fn query(stmt: &FlatIfStmt, fixed: &BTreeSet<FlatVar>) -> QuerySpec {
    QuerySpec {
        age: stmt.age,
        projections: stmt
            .args
            .iter()
            .enumerate()
            .filter_map(|(column, var)| fixed.contains(var).then_some(column))
            .collect(),
    }
}

fn available(rule: &FlatRule, indices: &IndexSelection) -> bool {
    let mut fixed: BTreeSet<_> = rule.scope.owners().iter().cloned().collect();
    rule.premise.iter().all(|stmt| {
        let available = indices
            .existing_query(&stmt.rel, &query(stmt, &fixed))
            .is_some();
        fixed.extend(stmt.args.iter().cloned());
        available
    })
}

fn alternative(
    rule: &FlatRule,
    indices: &IndexSelection,
    mode: ModelMode,
) -> Option<(FlatRule, usize)> {
    if rule.premise.len() < 3 || rule.premise[0].age != QueryAge::New {
        return None;
    }
    let fixed: BTreeSet<_> = rule
        .scope
        .owners()
        .iter()
        .chain(&rule.premise[0].args)
        .cloned()
        .collect();
    let start = rule
        .premise
        .iter()
        .position(|stmt| stmt.args.iter().any(|var| !fixed.contains(var)))?;
    let first = &rule.premise[start];
    let free = first.args.len() - query(first, &fixed).projections.len();
    // A bound function result need not bound the number of matching arguments.
    let inverts_function = match &first.rel {
        FlatInRel::Rel(FlatRel::Func(_)) => first
            .args
            .last()
            .is_some_and(|result| fixed.contains(result)),
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
        | FlatInRel::RelWithDiagonals { .. }
        | FlatInRel::TypeSet(_)
        | FlatInRel::Equality(_) => false,
    };
    let max_remaining = match mode {
        ModelMode::Desugared if inverts_function => usize::MAX,
        ModelMode::Native | ModelMode::Desugared if free < 2 => return None,
        ModelMode::Native | ModelMode::Desugared => free,
    };
    let mut candidates: Vec<_> = rule.premise[start + 1..]
        .iter()
        .enumerate()
        .filter_map(|(offset, stmt)| {
            let query = query(stmt, &fixed);
            let bound = query.projections.len();
            let remaining = stmt.args.len() - bound;
            (bound > 0
                && remaining > 0
                && remaining <= max_remaining
                && indices.existing_query(&stmt.rel, &query).is_some())
            .then_some((remaining, Reverse(bound), offset + start + 1))
        })
        .collect();
    candidates.sort_unstable();
    for (_, _, selected) in candidates {
        let mut result = rule.clone();
        result.premise.swap(start, selected);
        sort_premise_from(&mut result, start + 1);
        if available(&result, indices) {
            result.name.push_str("_residual");
            return Some((result, start));
        }
    }
    None
}

fn probe(
    stmts: &mut Vec<QueryOp>,
    stmt: &FlatIfStmt,
    fixed: &BTreeSet<FlatVar>,
    indices: &IndexSelection,
    stmt_index: usize,
) -> Vec<SetVar> {
    let query = query(stmt, fixed);
    indices
        .existing_query(&stmt.rel, &query)
        .unwrap()
        .into_iter()
        .map(|index| {
            let mut set = SetVar {
                name: SetVarName {
                    stmt_index,
                    rel: stmt.rel.clone(),
                    index: index.clone(),
                    restricted: 0,
                },
                arity: stmt.args.len(),
                strictness: Strictness::Strict,
            };
            stmts.push(QueryOp::DefineSet(DefineSetStmt {
                defined_var: set.clone(),
                expr: InSetExpr::GetIndex(GetIndexExpr {
                    rel: stmt.rel.clone(),
                    index_spec: index.clone(),
                }),
            }));
            for &column in &index.order[..query.projections.len()] {
                assert!(query.projections.contains(&column));
                let expr = InSetExpr::Restrict(RestrictExpr {
                    set: set.clone(),
                    first_column_var: ElVar {
                        name: stmt.args[column].name.clone(),
                    },
                });
                set.name.restricted += 1;
                set.arity -= 1;
                stmts.push(QueryOp::DefineSet(DefineSetStmt {
                    defined_var: set.clone(),
                    expr,
                }));
            }
            set
        })
        .collect()
}

fn residual_plans(rule: FlatRule, indices: &IndexSelection, mode: ModelMode) -> Vec<QueryPlan> {
    let Some((other, start)) = alternative(&rule, indices, mode) else {
        return vec![flat_rule_to_ram(rule, indices)];
    };
    let fixed: BTreeSet<_> = rule
        .scope
        .owners()
        .iter()
        .chain(&rule.premise[0].args)
        .cloned()
        .collect();
    let mut probes = Vec::new();
    let original = probe(
        &mut probes,
        &rule.premise[start],
        &fixed,
        indices,
        rule.premise.len(),
    );
    let alternative = probe(
        &mut probes,
        &other.premise[start],
        &fixed,
        indices,
        rule.premise.len() + 1,
    );
    // The same seed-bound choice partitions matches across the two routines.
    [rule, other]
        .into_iter()
        .enumerate()
        .map(|(choice, rule)| {
            let mut routine = flat_rule_to_ram(rule, indices);
            let after_seed = routine
                .stmts
                .iter()
                .position(|stmt| match stmt {
                    QueryOp::DefineSet(stmt) => stmt.defined_var.name.stmt_index != 0,
                    QueryOp::Iter(stmt) => stmt.loop_var_set.name.stmt_index != 0,
                    QueryOp::GuardInhabited(stmt) => stmt.sets[0].name.stmt_index != 0,
                    QueryOp::Insert(_) => true,
                    QueryOp::GuardPlan(_) => unreachable!("plans are added after lowering"),
                })
                .unwrap();
            let guard = QueryOp::GuardPlan(GuardPlanStmt {
                original: original.clone(),
                alternative: alternative.clone(),
                select_alternative: choice != 0,
                probe_rows: false,
            });
            routine.stmts.splice(
                after_seed..after_seed,
                probes.iter().cloned().chain(std::iter::once(guard)),
            );
            routine
        })
        .collect()
}

fn owner_alternative(rule: &FlatRule, indices: &IndexSelection) -> Option<FlatRule> {
    if rule.scope.owners().is_empty()
        || rule.premise.len() < 3
        || rule.premise[0].age != QueryAge::New
        || functionality_anchor(rule).is_some()
    {
        return None;
    }
    let fixed: BTreeSet<_> = rule.scope.owners().iter().cloned().collect();
    let seed_query = query(&rule.premise[0], &fixed);
    if seed_query.projections.len() == rule.premise[0].args.len()
        || indices
            .existing_query(&rule.premise[0].rel, &seed_query)
            .is_none()
    {
        return None;
    }
    let mut candidates: Vec<_> = rule
        .premise
        .iter()
        .enumerate()
        .skip(1)
        .filter_map(|(i, stmt)| {
            let query = query(stmt, &fixed);
            let free: BTreeSet<_> = stmt
                .args
                .iter()
                .filter(|arg| !fixed.contains(*arg))
                .collect();
            let arguments = match stmt.rel {
                FlatInRel::Rel(FlatRel::Func(_)) => &stmt.args[..stmt.args.len() - 1],
                FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
                | FlatInRel::RelWithDiagonals { .. }
                | FlatInRel::TypeSet(_)
                | FlatInRel::Equality(_) => stmt.args.as_slice(),
            };
            let inputs: BTreeSet<_> = arguments
                .iter()
                .filter(|arg| !fixed.contains(*arg))
                .collect();
            (!query.projections.is_empty()
                && !free.is_empty()
                && indices.existing_query(&stmt.rel, &query).is_some())
            .then_some((Reverse(inputs.len()), Reverse(free.len()), i))
        })
        .collect();
    candidates.sort_unstable();
    for (_, _, selected) in candidates {
        let mut other = rule.clone();
        let first = other.premise.remove(selected);
        other.premise.insert(0, first);
        // Age determines match ownership, but need not determine lookup order.
        sort_premise_lookup_first_from(&mut other, 1);
        if available(&other, indices) {
            other.name.push_str("_owner_bound");
            return Some(other);
        }
    }
    None
}

pub(super) fn plans(rule: FlatRule, indices: &IndexSelection, mode: ModelMode) -> Vec<QueryPlan> {
    let other = match mode {
        ModelMode::Native => owner_alternative(&rule, indices),
        ModelMode::Desugared => None,
    };
    let Some(other) = other else {
        return residual_plans(rule, indices, mode);
    };
    let fixed: BTreeSet<_> = rule.scope.owners().iter().cloned().collect();
    let mut probes = Vec::new();
    let original = probe(
        &mut probes,
        &rule.premise[0],
        &fixed,
        indices,
        rule.premise.len() + 2,
    );
    let alternative = probe(
        &mut probes,
        &other.premise[0],
        &fixed,
        indices,
        rule.premise.len() + 3,
    );
    let mut routines = residual_plans(rule, indices, mode);
    for routine in &mut routines {
        let guard = QueryOp::GuardPlan(GuardPlanStmt {
            original: original.clone(),
            alternative: alternative.clone(),
            select_alternative: false,
            probe_rows: true,
        });
        routine
            .stmts
            .splice(0..0, probes.iter().cloned().chain(std::iter::once(guard)));
    }
    let mut alternative_routine = flat_rule_to_ram(other, indices);
    let guard = QueryOp::GuardPlan(GuardPlanStmt {
        original,
        alternative,
        select_alternative: true,
        probe_rows: true,
    });
    alternative_routine
        .stmts
        .splice(0..0, probes.into_iter().chain(std::iter::once(guard)));
    routines.push(alternative_routine);
    routines
}
