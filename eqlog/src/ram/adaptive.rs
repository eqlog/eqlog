use std::collections::BTreeMap;

use crate::flat_eqlog::{FlatInRel, FlatRel, FlatRule, QueryAge};

use super::{InSetExpr, RamStmt, SetVar, SetVarName};

fn is_function_result(set: &SetVar) -> bool {
    let result_is_last = match &set.name.rel {
        FlatInRel::Rel(rel) => match rel {
            FlatRel::Func(_) => true,
            FlatRel::Pred(_) | FlatRel::ModelMember(_) => false,
        },
        FlatInRel::RelWithDiagonals { rel, equalities } => match rel {
            FlatRel::Func(_) => equalities.last().copied() == Some(equalities.len() - 1),
            FlatRel::Pred(_) | FlatRel::ModelMember(_) => false,
        },
        FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => false,
    };
    result_is_last
        && set.arity == 1
        && set.name.index.order.last().copied() == Some(set.name.index.order.len() - 1)
}

pub fn add_adaptive_lookup_joins(stmts: &mut [RamStmt], rule: &FlatRule) {
    let has_delta_seed = rule
        .premise
        .first()
        .is_some_and(|premise| premise.age == QueryAge::New);
    let definitions: BTreeMap<&SetVarName, usize> = stmts
        .iter()
        .enumerate()
        .filter_map(|(i, stmt)| match stmt {
            RamStmt::DefineSet(stmt) => Some((&stmt.defined_var.name, i)),
            RamStmt::Iter(stmt) => Some((&stmt.loop_var_set.name, i)),
            RamStmt::Insert(_) | RamStmt::GuardInhabited(_) | RamStmt::GuardPlan(_) => None,
        })
        .collect();
    let mut drivers = vec![Vec::new(); stmts.len()];
    for (i, stmt) in stmts.iter().enumerate() {
        let iter = match stmt {
            RamStmt::Iter(stmt) => stmt,
            RamStmt::DefineSet(_)
            | RamStmt::Insert(_)
            | RamStmt::GuardInhabited(_)
            | RamStmt::GuardPlan(_) => continue,
        };
        if iter.first_only
            || iter.sets.iter().all(is_function_result)
            || has_delta_seed && iter.sets.iter().all(|set| set.name.stmt_index == 0)
        {
            continue;
        }
        for later in &stmts[i + 1..] {
            let guard = match later {
                RamStmt::GuardInhabited(stmt) => stmt,
                // A later guard cannot remove outputs already emitted by this loop.
                RamStmt::Insert(_) => break,
                RamStmt::DefineSet(_) | RamStmt::Iter(_) | RamStmt::GuardPlan(_) => continue,
            };
            let candidate: Option<Vec<SetVar>> = guard
                .sets
                .iter()
                .map(|set| {
                    let definition = definitions[&set.name];
                    let restriction = match &stmts[definition] {
                        RamStmt::DefineSet(stmt) => match &stmt.expr {
                            InSetExpr::Restrict(expr) => expr,
                            InSetExpr::GetIndex(_) => return None,
                        },
                        RamStmt::Iter(_)
                        | RamStmt::Insert(_)
                        | RamStmt::GuardInhabited(_)
                        | RamStmt::GuardPlan(_) => {
                            return None;
                        }
                    };
                    let parent = &restriction.set;
                    (restriction.first_column_var == iter.loop_var_el
                        && definitions[&parent.name] < i
                        && !iter.sets.iter().any(|set| set.name == parent.name))
                    .then(|| parent.clone())
                })
                .collect();
            if let Some(candidate) = candidate.filter(|sets| !sets.is_empty()) {
                drivers[i] = candidate;
                break;
            }
        }
    }
    for (stmt, drivers) in stmts.iter_mut().zip(drivers) {
        match stmt {
            RamStmt::Iter(stmt) => stmt.lookup_drivers = drivers,
            RamStmt::DefineSet(_)
            | RamStmt::Insert(_)
            | RamStmt::GuardInhabited(_)
            | RamStmt::GuardPlan(_) => {}
        }
    }
}
