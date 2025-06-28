use crate::flat_eqlog::*;
use crate::ram::*;
use std::collections::{btree_map, BTreeMap, BTreeSet};
use std::sync::Arc;

pub fn to_ram(flat_rule: &FlatRule, index_selection: &IndexSelection) -> RamRoutine {
    let mut stmts: Vec<RamStmt> = Vec::new();
    let mut defined_vars: BTreeMap<FlatVar, ElVar> = BTreeMap::new();

    for (stmt_index, flat_stmt) in flat_rule.premise.iter().enumerate() {
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
        let query_spec = QuerySpec {
            age: flat_stmt.age,
            projections: fixed_columns,
        };

        let indices = index_selection
            .get(&(flat_stmt.rel.clone(), query_spec.clone()))
            .expect("Index for query in flat rule should exist");
        for index1 in &indices[1..] {
            assert_eq!(
                indices[0].order, index1.order,
                "All indices for a query must have the same order"
            );
        }
        let order = &indices[0].order;

        let mut set_names: Vec<Arc<str>> = indices
            .iter()
            .enumerate()
            .map(|(index_index, index)| format!("set_stmt{stmt_index}_index{index_index}").into())
            .collect();

        // Get the full indices and define variables for them.
        for (index_spec, set_name) in indices.iter().zip(set_names.iter()) {
            let rel = flat_stmt.rel.clone();
            stmts.push(RamStmt::DefineSet(DefineSetStmt {
                defined_var: SetVar {
                    name: set_name.clone(),
                },
                expr: InSetExpr::GetIndex(GetIndexExpr {
                    rel,
                    index_spec: index_spec.clone(),
                }),
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
                    },
                    first_column_var: var.clone(),
                });
                *set_name = format!("{set_name}_r{column}").into();
                stmts.push(RamStmt::DefineSet(DefineSetStmt {
                    defined_var: SetVar {
                        name: set_name.clone(),
                    },
                    expr,
                }));
            }
        }

        // Iterate over the sets to retrieve the other columns.
        for column in order[fixed_args.len()..].iter() {
            let flat_var = &flat_stmt.args[*column];
            let ram_var = ElVar {
                name: flat_var.name.clone(),
            };
            let prev_ram_var = defined_vars.insert(flat_var.clone(), ram_var.clone());
            // This should've been taken care of in the diagonal pass on flat eqlog.
            assert!(prev_ram_var.is_none(), "Free variable must not occur twice");

            let next_set_name: Arc<str> = format!("{}_r{column}", set_names[0]).into();

            let iter_stmt = IterStmt {
                sets: set_names
                    .iter()
                    .map(|name| SetVar { name: name.clone() })
                    .collect(),
                loop_var_el: ram_var,
                loop_var_set: SetVar {
                    name: next_set_name.clone(),
                },
            };
            set_names = vec![next_set_name];
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
        stmts,
    }
}
