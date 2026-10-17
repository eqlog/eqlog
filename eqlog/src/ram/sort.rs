use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::ram::*;

use super::RamStmt;

fn collect_stmt_dependencies(
    stmts: &[RamStmt],
    parameters: &BTreeSet<Arc<str>>,
) -> Vec<BTreeSet<usize>> {
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

                        if let Some(&el_def_site) = el_var_def_sites.get(&first_column_var.name) {
                            dependencies.insert(el_def_site);
                        } else {
                            assert!(
                                parameters.contains(&first_column_var.name),
                                "Variable must be defined before use"
                            );
                        }
                    }
                }
            }
            RamStmt::Iter(IterStmt {
                sets,
                loop_var_el,
                loop_var_set,
                first_only: _,
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

pub fn sort_ram_stmts(stmts: &[RamStmt], parameters: &BTreeSet<Arc<str>>) -> Vec<RamStmt> {
    let mut dependencies = collect_stmt_dependencies(stmts, parameters);

    let mut reverse_dependencies = vec![Vec::new(); stmts.len()];
    for i in 0..stmts.len() {
        for j in dependencies[i].iter().copied() {
            reverse_dependencies[j].push(i);
        }
    }

    let mut open_stmts: BTreeSet<(usize, usize)> = dependencies
        .iter()
        .enumerate()
        .filter_map(|(i, deps)| deps.is_empty().then(|| (ram_stmt_cost(&stmts[i]), i)))
        .collect();

    let mut result_stmts: Vec<RamStmt> = Vec::new();

    while result_stmts.len() != stmts.len() {
        let (_, i) = open_stmts
            .pop_first()
            .expect("The dependency graph must not contain cycles");
        result_stmts.push(stmts[i].clone());

        // A newly enabled guard can reject this branch before another loop
        // expands it. Reconsider priorities after every dependency is satisfied.
        for &j in &reverse_dependencies[i] {
            dependencies[j].remove(&i);
            if dependencies[j].is_empty() {
                open_stmts.insert((ram_stmt_cost(&stmts[j]), j));
            }
        }
    }

    result_stmts
}
