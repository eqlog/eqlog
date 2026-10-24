use std::collections::BTreeMap;

use crate::flat_eqlog::{FlatInRel, FlatRel, FlatRule, QueryAge};

use super::{InSetExpr, QueryOp, SetVar, SetVarName};

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

pub fn add_adaptive_lookup_joins(stmts: &mut [QueryOp], rule: &FlatRule) {
    let has_delta_seed = rule
        .premise
        .first()
        .is_some_and(|premise| premise.age == QueryAge::New);
    let definitions: BTreeMap<&SetVarName, usize> = stmts
        .iter()
        .enumerate()
        .filter_map(|(i, stmt)| match stmt {
            QueryOp::DefineSet(stmt) => Some((&stmt.defined_var.name, i)),
            QueryOp::Iter(stmt) => Some((&stmt.loop_var_set.name, i)),
            QueryOp::Insert(_) | QueryOp::GuardInhabited(_) | QueryOp::GuardPlan(_) => None,
        })
        .collect();
    let mut drivers = vec![Vec::new(); stmts.len()];
    for (i, stmt) in stmts.iter().enumerate() {
        let iter = match stmt {
            QueryOp::Iter(stmt) => stmt,
            QueryOp::DefineSet(_)
            | QueryOp::Insert(_)
            | QueryOp::GuardInhabited(_)
            | QueryOp::GuardPlan(_) => continue,
        };
        if iter.first_only
            || iter.sets.iter().all(is_function_result)
            || has_delta_seed && iter.sets.iter().all(|set| set.name.stmt_index == 0)
        {
            continue;
        }
        for later in &stmts[i + 1..] {
            let guard = match later {
                QueryOp::GuardInhabited(stmt) => stmt,
                // A later guard cannot remove outputs already emitted by this loop.
                QueryOp::Insert(_) => break,
                QueryOp::DefineSet(_) | QueryOp::Iter(_) | QueryOp::GuardPlan(_) => continue,
            };
            let candidate: Option<Vec<SetVar>> = guard
                .sets
                .iter()
                .map(|set| {
                    let definition = definitions[&set.name];
                    let restriction = match &stmts[definition] {
                        QueryOp::DefineSet(stmt) => match &stmt.expr {
                            InSetExpr::Restrict(expr) => expr,
                            InSetExpr::GetIndex(_) => return None,
                        },
                        QueryOp::Iter(_)
                        | QueryOp::Insert(_)
                        | QueryOp::GuardInhabited(_)
                        | QueryOp::GuardPlan(_) => {
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
            QueryOp::Iter(stmt) => stmt.lookup_drivers = drivers,
            QueryOp::DefineSet(_)
            | QueryOp::Insert(_)
            | QueryOp::GuardInhabited(_)
            | QueryOp::GuardPlan(_) => {}
        }
    }
}
