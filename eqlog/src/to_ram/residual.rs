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
    // Inverting a function by its result can range over arbitrarily many
    // arguments even for a single free column, such as all arrows into a
    // context compared to the factorizations of one arrow.
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
    stmts: &mut Vec<RamStmt>,
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
            stmts.push(RamStmt::DefineSet(DefineSetStmt {
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
                stmts.push(RamStmt::DefineSet(DefineSetStmt {
                    defined_var: set.clone(),
                    expr,
                }));
            }
            set
        })
        .collect()
}

pub(super) fn plans(rule: FlatRule, indices: &IndexSelection, mode: ModelMode) -> Vec<RamRoutine> {
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
                    RamStmt::DefineSet(stmt) => stmt.defined_var.name.stmt_index != 0,
                    RamStmt::Iter(stmt) => stmt.loop_var_set.name.stmt_index != 0,
                    RamStmt::GuardInhabited(stmt) => stmt.sets[0].name.stmt_index != 0,
                    RamStmt::Insert(_) => true,
                    RamStmt::GuardPlan(_) => unreachable!("plans are added after lowering"),
                })
                .unwrap();
            let guard = RamStmt::GuardPlan(GuardPlanStmt {
                original: original.clone(),
                alternative: alternative.clone(),
                select_alternative: choice != 0,
            });
            routine.stmts.splice(
                after_seed..after_seed,
                probes.iter().cloned().chain(std::iter::once(guard)),
            );
            routine
        })
        .collect()
}
