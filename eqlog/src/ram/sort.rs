use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::ram::*;

use super::RamStmt;

fn collect_stmt_dependencies(stmts: &[RamStmt]) -> Vec<BTreeSet<usize>> {
    let mut set_var_def_sites: BTreeMap<SetVarName, usize> = BTreeMap::new();
    let mut el_var_def_sites: BTreeMap<Arc<str>, usize> = BTreeMap::new();

    let mut dependencies: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); stmts.len()];

    for (i, stmt) in stmts.iter().enumerate() {
        let dependencies = &mut dependencies[i];
        match stmt {
            RamStmt::DefineSet(DefineSetStmt { defined_var, expr }) => {
                let prev_def_site = set_var_def_sites.insert(defined_var.name.clone(), i);
                assert!(
                    prev_def_site.is_none(),
                    "Multiple definitions of a variable are not allowed"
                );

                match expr {
                    InSetExpr::GetIndex(_) => {}
                    InSetExpr::Restrict(RestrictExpr {
                        set,
                        first_column_var,
                    }) => {
                        let set_def_site = *set_var_def_sites
                            .get(&set.name)
                            .expect("Variable must be defined before use");
                        dependencies.insert(set_def_site);

                        let el_def_site = *el_var_def_sites
                            .get(&first_column_var.name)
                            .expect("Variable must be defined before use");
                        dependencies.insert(el_def_site);
                    }
                }
            }
            RamStmt::Iter(IterStmt {
                sets,
                loop_var_el,
                loop_var_set,
            }) => {
                for set in sets {
                    let set_def_site = *set_var_def_sites
                        .get(&set.name)
                        .expect("Variable must be defined before use");
                    dependencies.insert(set_def_site);
                }

                el_var_def_sites.insert(loop_var_el.name.clone(), i);
                set_var_def_sites.insert(loop_var_set.name.clone(), i);
            }
            RamStmt::Insert(InsertStmt { rel: _, args: _ }) => {
                for (j, prev_stmt) in stmts[..i].iter().enumerate() {
                    let depends_on_j = match prev_stmt {
                        RamStmt::DefineSet(_) => true,
                        RamStmt::Iter(_) => true,
                        RamStmt::Insert(_) => false,
                        RamStmt::GuardInhabited(_) => true,
                    };
                    if depends_on_j {
                        dependencies.insert(j);
                    }
                }
            }
            RamStmt::GuardInhabited(GuardInhabitedStmt { sets }) => {
                for set in sets {
                    let set_def_site = *set_var_def_sites
                        .get(&set.name)
                        .expect("Variable must be defined before use");
                    dependencies.insert(set_def_site);
                }
            }
        }
    }

    dependencies
}

fn ram_stmt_cost(stmt: &RamStmt) -> usize {
    match stmt {
        RamStmt::GuardInhabited(_) => 1,
        RamStmt::Insert(_) => 2,
        RamStmt::DefineSet(DefineSetStmt { defined_var, expr }) => match expr {
            InSetExpr::GetIndex(_) => 0,
            InSetExpr::Restrict(_) => match defined_var.strictness {
                Strictness::Lazy => 3,
                Strictness::Strict => 4,
            },
        },
        RamStmt::Iter(_) => 5,
    }
}

pub fn sort_ram_stmts(stmts: &[RamStmt]) -> Vec<RamStmt> {
    let mut dependencies = collect_stmt_dependencies(stmts);

    let mut reverse_dependencies = vec![Vec::new(); stmts.len()];
    for i in 0..stmts.len() {
        for j in dependencies[i].iter().copied() {
            reverse_dependencies[j].push(i);
        }
    }

    let mut open_stmts: Vec<usize> = dependencies
        .iter()
        .enumerate()
        .filter_map(|(i, deps)| if deps.is_empty() { Some(i) } else { None })
        .collect();

    let mut result_stmts: Vec<RamStmt> = Vec::new();

    while result_stmts.len() != stmts.len() {
        assert!(
            !open_stmts.is_empty(),
            "The dependency graph must not contain cycles"
        );

        let mut stmts: Vec<&RamStmt> = open_stmts.iter().copied().map(|i| &stmts[i]).collect();
        stmts.sort_by_key(|stmt| ram_stmt_cost(*stmt));

        result_stmts.extend(stmts.into_iter().cloned());

        let mut new_open_stmts = Vec::new();
        for i in open_stmts.into_iter() {
            for j in reverse_dependencies[i].iter().copied() {
                dependencies[j].retain(|i0| *i0 != i);
                if dependencies[j].is_empty() {
                    new_open_stmts.push(j);
                }
            }
            reverse_dependencies[i].clear();
        }
        open_stmts = new_open_stmts;
    }

    result_stmts
}
