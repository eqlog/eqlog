use super::ast::*;
use crate::unification::Unification;
use std::cmp::Ordering;
use std::collections::{btree_map, BTreeMap};

pub fn eliminate_equalities_ifs(flat_rule: &FlatRule) -> FlatRule {
    let mut var_index: BTreeMap<FlatVar, u32> = BTreeMap::new();
    let mut index_var: Vec<FlatVar> = Vec::new();
    for var in flat_rule.premise.iter().flat_map(|stmt| &stmt.args) {
        let len: u32 = var_index.len().try_into().unwrap();
        match var_index.entry(var.clone()) {
            btree_map::Entry::Vacant(e) => {
                e.insert(len);
                index_var.push(var.clone());
            }
            btree_map::Entry::Occupied(_) => {}
        }
    }
    assert_eq!(var_index.len(), index_var.len());

    let mut unification = Unification::new();
    unification.increase_size_to(var_index.len());

    for stmt in &flat_rule.premise {
        if let FlatInRel::Equality(_) = stmt.rel {
            assert_eq!(
                stmt.args.len(),
                2,
                "Equality statements must have exactly two variables."
            );
            let lhs = var_index[&stmt.args[0]];
            let rhs = var_index[&stmt.args[1]];

            let lhs = unification.root(lhs);
            let rhs = unification.root(rhs);

            unification.union_roots_into(lhs, rhs);
        }
    }

    let mut map_var = |var: FlatVar| -> FlatVar {
        let index = var_index.get(&var).unwrap();
        let index = unification.root(*index);
        index_var.get(index as usize).unwrap().clone()
    };

    let premise: Vec<FlatIfStmt> = flat_rule
        .premise
        .iter()
        .filter_map(|stmt| {
            if let FlatInRel::Equality(_) = stmt.rel {
                return None;
            }

            let args: Vec<FlatVar> = stmt.args.iter().cloned().map(|arg| map_var(arg)).collect();
            Some(FlatIfStmt {
                rel: stmt.rel.clone(),
                args,
                age: stmt.age,
            })
        })
        .collect();
    let conclusion: Vec<FlatThenStmt> = flat_rule
        .conclusion
        .iter()
        .map(|stmt| {
            let args: Vec<FlatVar> = stmt.args.iter().cloned().map(|arg| map_var(arg)).collect();
            FlatThenStmt {
                rel: stmt.rel,
                args,
            }
        })
        .collect();

    FlatRule {
        premise,
        conclusion,
        name: flat_rule.name.clone(),
    }
}

pub fn to_semi_naive(flat_rule: &FlatRule) -> Vec<FlatRule> {
    assert!(
        flat_rule
            .premise
            .iter()
            .all(|if_stmt| if_stmt.age == QueryAge::All),
        "to_semi_naive requires all premise statements to have QueryAge::All"
    );

    let original_name = flat_rule.name.as_str();

    (0..flat_rule.premise.len())
        .map(|i| {
            let premise = flat_rule
                .premise
                .iter()
                .enumerate()
                .map(|(j, stmt)| {
                    let age = match i.cmp(&j) {
                        Ordering::Less => QueryAge::Old,
                        Ordering::Equal => QueryAge::New,
                        Ordering::Greater => QueryAge::All,
                    };

                    FlatIfStmt {
                        age,
                        args: stmt.args.clone(),
                        rel: stmt.rel.clone(),
                    }
                })
                .collect();

            FlatRule {
                premise,
                conclusion: flat_rule.conclusion.clone(),
                name: format!("{original_name}_{}", i),
            }
        })
        .collect()
}
