mod residual;

use crate::algebra::signature::Signature;
use crate::flat_eqlog::*;
use crate::options::ModelMode;
use crate::ram::*;
use std::collections::{BTreeMap, BTreeSet};

fn functionality_seed_indices(
    rule: &FlatRule,
    selection: &IndexSelection,
    fixed: &BTreeSet<usize>,
) -> Option<Vec<IndexSpec>> {
    functionality_anchor(rule)?;
    let first = &rule.premise[0];
    let query = QuerySpec {
        age: QueryAge::All,
        projections: (0..first.args.len() - 1).collect(),
    };
    let indices = &selection.queries[&(first.rel.clone(), query)];
    if indices[0].order[..fixed.len()]
        .iter()
        .any(|column| !fixed.contains(column))
    {
        return None;
    }
    // Group new results by their domain so the representative lookup can be
    // shared across all equalities for that domain.
    Some(
        indices
            .iter()
            .filter(|index| match first.age {
                QueryAge::New => index.age == IndexAge::New,
                QueryAge::Old => index.age == IndexAge::Old,
                QueryAge::All => true,
            })
            .cloned()
            .collect(),
    )
}

fn flat_rule_to_ram(flat_rule: FlatRule, index_selection: &IndexSelection) -> RamRoutine {
    let mut stmts: Vec<RamStmt> = Vec::new();
    let anchor = functionality_anchor(&flat_rule);
    let mut occurrences = BTreeMap::new();
    for var in flat_rule.premise.iter().flat_map(|stmt| &stmt.args) {
        *occurrences.entry(var).or_insert(0) += 1;
    }
    let output_vars: BTreeSet<_> = flat_rule
        .conclusion
        .iter()
        .flat_map(|stmt| &stmt.args)
        .collect();
    let private_vars: BTreeSet<_> = occurrences
        .into_iter()
        .filter_map(|(var, count)| (count == 1 && !output_vars.contains(var)).then_some(var))
        .collect();
    let mut defined_vars: BTreeMap<FlatVar, ElVar> = flat_rule
        .scope
        .owners()
        .iter()
        .map(|owner| {
            (
                owner.clone(),
                ElVar {
                    name: owner.name.clone(),
                },
            )
        })
        .collect();

    for (stmt_index, flat_stmt) in flat_rule.premise.iter().enumerate() {
        let arg_set: BTreeSet<FlatVar> = flat_stmt.args.iter().cloned().collect();
        assert_eq!(
            arg_set.len(),
            flat_stmt.args.len(),
            "Diagonals should have been transformed in an earlier pass"
        );
        let fixed_args: BTreeMap<usize, ElVar> = flat_stmt
            .args
            .iter()
            .enumerate()
            .filter_map(|(column, flat_arg)| {
                let ram_arg = defined_vars.get(flat_arg)?;
                Some((column, ram_arg.clone()))
            })
            .collect();
        let fixed_columns: BTreeSet<usize> = fixed_args.keys().copied().collect();
        let functionality_indices = if stmt_index == 0 {
            functionality_seed_indices(&flat_rule, index_selection, &fixed_columns)
        } else {
            None
        };
        let query_spec = QuerySpec {
            age: flat_stmt.age,
            projections: fixed_columns,
        };

        let indices = functionality_indices.unwrap_or_else(|| {
            index_selection
                .existing_query(&flat_stmt.rel, &query_spec)
                .expect("Index for query in flat rule should exist")
        });
        for index1 in &indices[1..] {
            assert_eq!(
                indices[0].order, index1.order,
                "All indices for a query must have the same order"
            );
        }
        // ALL scans can produce OLD suffixes under a NEW-named variable.
        let canonical_filter = indices.iter().any(|index| match index.age {
            IndexAge::Old | IndexAge::All => true,
            IndexAge::New => false,
        });
        let order = &indices[0].order;
        let mut arity = order.len();

        let mut set_names: Vec<SetVarName> = indices
            .iter()
            .map(|index| SetVarName {
                stmt_index,
                rel: flat_stmt.rel.clone(),
                index: index.clone(),
                restricted: 0,
            })
            .collect();

        // Get the full indices and define variables for them.
        for (index_spec, set_name) in indices.iter().zip(set_names.iter()) {
            let rel = flat_stmt.rel.clone();
            stmts.push(RamStmt::DefineSet(DefineSetStmt {
                defined_var: SetVar {
                    name: set_name.clone(),
                    arity,
                    strictness: Strictness::Strict,
                },
                expr: InSetExpr::GetIndex(GetIndexExpr {
                    rel,
                    index_spec: index_spec.clone(),
                }),
            }));
        }

        if !fixed_args.is_empty() {
            stmts.push(RamStmt::GuardInhabited(GuardInhabitedStmt {
                sets: set_names
                    .iter()
                    .map(|name| SetVar {
                        name: name.clone(),
                        arity,
                        strictness: Strictness::Strict,
                    })
                    .collect(),
            }));
        }

        // Restrict the indices according to fixed args.
        for column in order[..fixed_args.len()].iter() {
            let var = fixed_args
                .get(column)
                .expect("Fixed args must be prefix in selected index order");

            for set_name in set_names.iter_mut() {
                let expr = InSetExpr::Restrict(RestrictExpr {
                    set: SetVar {
                        name: set_name.clone(),
                        arity,
                        strictness: Strictness::Strict,
                    },
                    first_column_var: var.clone(),
                });
                set_name.restricted += 1;
                stmts.push(RamStmt::DefineSet(DefineSetStmt {
                    defined_var: SetVar {
                        name: set_name.clone(),
                        arity: arity - 1,
                        strictness: Strictness::Strict,
                    },
                    expr,
                }));
            }

            arity -= 1;

            if fixed_args.len() < order.len() {
                // Reject a missing join prefix before unrelated loops expand it.
                stmts.push(RamStmt::GuardInhabited(GuardInhabitedStmt {
                    sets: set_names
                        .iter()
                        .map(|name| SetVar {
                            name: name.clone(),
                            arity,
                            strictness: Strictness::Strict,
                        })
                        .collect(),
                }));
            }
        }

        let free_columns = &order[fixed_args.len()..];
        let used_columns = free_columns
            .iter()
            .rposition(|column| !private_vars.contains(&flat_stmt.args[*column]))
            .map_or(0, |last| last + 1);
        if used_columns == 0 {
            // We don't need to retrieve any new variables, but we still have to check that the set
            // is not empty.
            stmts.push(RamStmt::GuardInhabited(GuardInhabitedStmt {
                sets: set_names
                    .iter()
                    .map(|name| SetVar {
                        name: name.clone(),
                        arity,
                        strictness: Strictness::Strict,
                    })
                    .collect(),
            }));
        } else {
            // Iterate over the sets to retrieve the other columns.
            for column in &free_columns[..used_columns] {
                let flat_var = &flat_stmt.args[*column];
                let ram_var = ElVar {
                    name: flat_var.name.clone(),
                };
                let prev_ram_var = defined_vars.insert(flat_var.clone(), ram_var.clone());
                // This should've been taken care of in the diagonal pass on flat eqlog.
                assert!(prev_ram_var.is_none(), "Free variable must not occur twice");

                let next_set_name = SetVarName {
                    restricted: set_names[0].restricted + 1,
                    ..set_names[0].clone()
                };

                let first_only = stmt_index == 1 && anchor == Some(flat_var);
                let mut sets: Vec<_> = set_names
                    .iter()
                    .map(|name| SetVar {
                        name: name.clone(),
                        arity,
                        strictness: Strictness::Strict,
                    })
                    .collect();
                if first_only {
                    assert_eq!(arity, 1, "functionality anchors require the full domain");
                    // New results must join an old representative when one
                    // exists, or a singleton delta could select itself.
                    sets.sort_by_key(|set| match set.name.index.age {
                        IndexAge::Old | IndexAge::All => 0,
                        IndexAge::New => 1,
                    });
                }
                let iter_stmt = IterStmt {
                    sets,
                    lookup_drivers: Vec::new(),
                    loop_var_el: ram_var,
                    loop_var_set: SetVar {
                        name: next_set_name.clone(),
                        arity: arity - 1,
                        strictness: Strictness::Strict,
                    },
                    first_only,
                    canonical_filter,
                };
                arity -= 1;
                stmts.push(RamStmt::Iter(iter_stmt));
                set_names = vec![next_set_name];
            }
            if arity > 0 {
                // Private suffix variables witness the premise but cannot
                // distinguish matches in another premise or the conclusion.
                stmts.push(RamStmt::GuardInhabited(GuardInhabitedStmt {
                    sets: set_names
                        .iter()
                        .map(|name| SetVar {
                            name: name.clone(),
                            arity,
                            strictness: Strictness::Strict,
                        })
                        .collect(),
                }));
            }
        }
    }

    for flat_stmt in flat_rule.conclusion.iter() {
        let args = flat_stmt
            .args
            .iter()
            .map(|flat_arg| {
                defined_vars
                    .get(flat_arg)
                    .expect("All conclusion args must be defined in premise")
                    .clone()
            })
            .collect();
        let insert_stmt = InsertStmt {
            rel: flat_stmt.rel.clone(),
            args,
        };
        stmts.push(RamStmt::Insert(insert_stmt));
    }

    RamRoutine {
        name: flat_rule.name.clone(),
        flat_rule,
        stmts,
    }
}

/// Desugared tables answer a premise of age all through one view, so its
/// old and new sets merge into a single set of that age.
fn merge_all_age_sets(routine: &mut RamRoutine) {
    let mut all: BTreeSet<usize> = routine
        .flat_rule
        .premise
        .iter()
        .enumerate()
        .filter_map(|(i, stmt)| match stmt.age {
            QueryAge::All => Some(i),
            QueryAge::New | QueryAge::Old => None,
        })
        .collect();
    // Plan probes follow the premises; a probe of a premise of age all reads
    // both an old and a new set.
    let mut probe_ages: BTreeMap<usize, BTreeSet<IndexAge>> = BTreeMap::new();
    for stmt in &routine.stmts {
        match stmt {
            RamStmt::DefineSet(define) => {
                let name = &define.defined_var.name;
                if name.stmt_index >= routine.flat_rule.premise.len() {
                    probe_ages
                        .entry(name.stmt_index)
                        .or_default()
                        .insert(name.index.age);
                }
            }
            RamStmt::Iter(_)
            | RamStmt::Insert(_)
            | RamStmt::GuardInhabited(_)
            | RamStmt::GuardPlan(_) => {}
        }
    }
    all.extend(probe_ages.into_iter().filter_map(|(probe, ages)| {
        (ages.contains(&IndexAge::Old) && ages.contains(&IndexAge::New)).then_some(probe)
    }));
    let rename = |name: &mut SetVarName| {
        if all.contains(&name.stmt_index) {
            name.index.age = IndexAge::All;
        }
    };
    let merge = |sets: &mut Vec<SetVar>| {
        for set in sets.iter_mut() {
            rename(&mut set.name);
        }
        let mut seen = BTreeSet::new();
        sets.retain(|set| seen.insert(set.name.clone()));
    };
    let mut defined = BTreeSet::new();
    let mut stmts = Vec::new();
    for mut stmt in std::mem::take(&mut routine.stmts) {
        match &mut stmt {
            RamStmt::DefineSet(define) => {
                rename(&mut define.defined_var.name);
                match &mut define.expr {
                    InSetExpr::GetIndex(get) => {
                        get.index_spec = define.defined_var.name.index.clone();
                    }
                    InSetExpr::Restrict(restrict) => rename(&mut restrict.set.name),
                }
                if !defined.insert(define.defined_var.name.clone()) {
                    continue;
                }
            }
            RamStmt::Iter(iter) => {
                merge(&mut iter.sets);
                merge(&mut iter.lookup_drivers);
                rename(&mut iter.loop_var_set.name);
            }
            RamStmt::GuardInhabited(guard) => merge(&mut guard.sets),
            RamStmt::GuardPlan(plan) => {
                merge(&mut plan.original);
                merge(&mut plan.alternative);
            }
            RamStmt::Insert(_) => {}
        }
        stmts.push(stmt);
    }
    routine.stmts = stmts;
}

/// Plan probes and premises can restrict the same view by the same
/// variables; later such sets reuse the first one instead of repeating its
/// lookups. Earlier statements enclose all later ones, so the first
/// definition is in scope wherever the others are used.
fn share_equal_sets(routine: &mut RamRoutine) {
    let mut definitions: BTreeMap<InSetExpr, SetVar> = BTreeMap::new();
    let mut aliases: BTreeMap<SetVarName, SetVar> = BTreeMap::new();
    let alias = |set: &mut SetVar, aliases: &BTreeMap<SetVarName, SetVar>| {
        if let Some(target) = aliases.get(&set.name) {
            *set = target.clone();
        }
    };
    let dedup = |sets: &mut Vec<SetVar>| {
        let mut seen = BTreeSet::new();
        sets.retain(|set| seen.insert(set.name.clone()));
    };
    let mut stmts = Vec::new();
    for mut stmt in std::mem::take(&mut routine.stmts) {
        match &mut stmt {
            RamStmt::DefineSet(define) => {
                match &mut define.expr {
                    InSetExpr::GetIndex(_) => {}
                    InSetExpr::Restrict(restrict) => alias(&mut restrict.set, &aliases),
                }
                if let Some(existing) = definitions.get(&define.expr) {
                    aliases.insert(define.defined_var.name.clone(), existing.clone());
                    continue;
                }
                definitions.insert(define.expr.clone(), define.defined_var.clone());
            }
            RamStmt::Iter(iter) => {
                for set in iter.sets.iter_mut().chain(&mut iter.lookup_drivers) {
                    alias(set, &aliases);
                }
                dedup(&mut iter.sets);
                dedup(&mut iter.lookup_drivers);
            }
            RamStmt::GuardInhabited(guard) => {
                for set in &mut guard.sets {
                    alias(set, &aliases);
                }
                dedup(&mut guard.sets);
            }
            RamStmt::GuardPlan(plan) => {
                for set in plan.original.iter_mut().chain(&mut plan.alternative) {
                    alias(set, &aliases);
                }
            }
            RamStmt::Insert(_) => {}
        }
        stmts.push(stmt);
    }
    routine.stmts = stmts;
}

fn flat_rule_group_to_ram(
    flat_rule_group: FlatRuleGroup,
    index_selection: &IndexSelection,
    mode: ModelMode,
) -> RamModule {
    let routines = flat_rule_group
        .rules
        .into_iter()
        .flat_map(|flat_rule| residual::plans(flat_rule, index_selection))
        .map(|mut routine| {
            match mode {
                ModelMode::Native => {}
                ModelMode::Desugared => {
                    merge_all_age_sets(&mut routine);
                    share_equal_sets(&mut routine);
                }
            }
            make_ram_lazy(routine.stmts.as_mut_slice());
            let parameters = routine
                .flat_rule
                .scope
                .owners()
                .iter()
                .map(|owner| owner.name.clone())
                .collect();
            routine.stmts = sort_ram_stmts(routine.stmts.as_slice(), &parameters);
            add_adaptive_lookup_joins(&mut routine.stmts, &routine.flat_rule);
            routine
        })
        .collect();
    RamModule {
        name: flat_rule_group.name.clone(),
        routines,
    }
}

pub fn flat_rule_groups_to_ram(
    groups: Vec<FlatRuleGroup>,
    schedule: RuleSchedule,
    index_selection: &IndexSelection,
    signature: &Signature,
    mode: ModelMode,
) -> RamProgram {
    let modules: Vec<_> = groups
        .into_iter()
        .map(|group| flat_rule_group_to_ram(group, index_selection, mode))
        .collect();
    let (preparations, model_preparations, native_indices) =
        plan_index_preparation(&modules, &schedule, index_selection, signature, mode);
    RamProgram {
        modules,
        schedule,
        preparations,
        model_preparations,
        native_indices,
    }
}
