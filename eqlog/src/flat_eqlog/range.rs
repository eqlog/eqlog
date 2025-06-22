use super::ast::*;
use super::index_selection::*;
use super::var_info::*;
use crate::eqlog_util::{display_rel, type_list_vec};
use by_address::ByAddress;
use eqlog_eqlog::*;
use std::cmp::max;
use std::collections::btree_map;
use std::collections::{BTreeMap, BTreeSet};

fn resolve_if_rel_stmts_func<'a>(
    func: &'a FlatFunc,
    if_stmt_rel_infos: &BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo>,
    index_selection: &IndexSelection,
    eqlog: &Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    fresh_range_vars: &mut impl Iterator<Item = FlatRangeVar>,
) -> FlatFunc {
    let mut body: Vec<FlatStmt> = Vec::new();

    for stmt in func.body.iter() {
        let rel_if_stmt = match stmt {
            FlatStmt::Call { .. }
            | FlatStmt::NonSurjThen(_)
            | FlatStmt::SurjThen(_)
            | FlatStmt::DefineRange(_) => {
                body.push(stmt.clone());
                continue;
            }
            FlatStmt::If(if_stmt) => match if_stmt {
                FlatIfStmt::Equal(_) | FlatIfStmt::Range(_) | FlatIfStmt::Type(_) => {
                    body.push(stmt.clone());
                    continue;
                }
                FlatIfStmt::Relation(rel_if_stmt) => rel_if_stmt,
            },
        };

        let rel = rel_if_stmt.rel;
        let age = rel_if_stmt.age;
        let RelationInfo {
            diagonals,
            in_projections,
            out_projections,
            rel: _,
            age: _,
        } = if_stmt_rel_infos.get(&ByAddress(rel_if_stmt)).unwrap();

        let query = QuerySpec {
            diagonals: diagonals.clone(),
            projections: in_projections.keys().copied().collect(),
            age,
        };
        let index = index_selection
            .get(&display_rel(rel, eqlog, identifiers).to_string())
            .unwrap()
            .get(&query)
            .unwrap();

        let range_vars: Vec<FlatRangeVar> =
            fresh_range_vars.take(1 + in_projections.len()).collect();

        body.push(FlatStmt::DefineRange(FlatDefineRangeStmt {
            defined_var: range_vars[0],
            expression: FlatRangeExpr::Index(FlatIndexRangeExpr {
                rel,
                index: index.clone(),
            }),
        }));

        let fixed_arg_len = in_projections.len();

        index.order[..fixed_arg_len]
            .iter()
            .copied()
            .zip(range_vars.iter().copied())
            .zip(range_vars[1..].iter().copied())
            .for_each(|((proj_column, prev_range_var), next_range_var)| {
                let proj_var = *in_projections.get(&proj_column).unwrap();
                let restriction_expr = FlatRangeRestrictionExpr {
                    range_var: prev_range_var,
                    first_projection: proj_var,
                };
                body.push(FlatStmt::DefineRange(FlatDefineRangeStmt {
                    defined_var: next_range_var,
                    expression: FlatRangeExpr::Restriction(restriction_expr),
                }));
            });

        let if_stmt_range_vars: Vec<Option<FlatVar>> = index.order[fixed_arg_len..]
            .iter()
            .map(|i| out_projections.get(i).copied())
            .collect();

        body.push(FlatStmt::If(FlatIfStmt::Range(FlatIfStmtRange {
            range_var: *range_vars.last().unwrap(),
            args: if_stmt_range_vars,
        })));
    }

    FlatFunc {
        args: func.args.clone(),
        range_args: func.range_args.clone(),
        name: func.name.clone(),
        body,
    }
}

fn make_range_var_type_map(
    funcs: &[FlatFunc],
    eqlog: &Eqlog,
) -> BTreeMap<FlatRangeVar, FlatRangeType> {
    let mut range_var_types: BTreeMap<FlatRangeVar, FlatRangeType> = BTreeMap::new();

    for func in funcs {
        for stmt in func.body.iter() {
            if let FlatStmt::DefineRange(define_range_stmt) = stmt {
                let range_type = match &define_range_stmt.expression {
                    FlatRangeExpr::Index(FlatIndexRangeExpr { rel, index: _ }) => {
                        let arity_len = type_list_vec(eqlog.flat_arity(*rel).unwrap(), eqlog).len();
                        FlatRangeType { arity_len }
                    }
                    FlatRangeExpr::Restriction(FlatRangeRestrictionExpr {
                        range_var,
                        first_projection: _,
                    }) => {
                        let super_range_type = range_var_types.get(range_var).unwrap();
                        assert!(
                            super_range_type.arity_len > 0,
                            "Restriction is not allowed on arity 0 range"
                        );
                        FlatRangeType {
                            arity_len: super_range_type.arity_len - 1,
                        }
                    }
                };

                if let Some(prev_range_type) =
                    range_var_types.insert(define_range_stmt.defined_var, range_type)
                {
                    assert_eq!(prev_range_type, range_type, "Conflicting range types");
                }
            }
        }
    }

    range_var_types
}

/// Replace all relation if statements by range definitions and iterations over them.
pub fn resolve_if_rel_stmts<'a>(
    rule: &'a FlatRule,
    if_stmt_rel_infos: &BTreeMap<ByAddress<&'a FlatIfStmtRelation>, RelationInfo>,
    index_selection: &IndexSelection,
    eqlog: &Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> FlatRule {
    let mut fresh_range_vars = (0..).map(FlatRangeVar);

    let funcs: Vec<FlatFunc> = rule
        .funcs
        .iter()
        .map(|func| {
            resolve_if_rel_stmts_func(
                func,
                &if_stmt_rel_infos,
                index_selection,
                eqlog,
                identifiers,
                &mut fresh_range_vars,
            )
        })
        .collect();

    let range_var_types = make_range_var_type_map(funcs.as_slice(), eqlog);

    FlatRule {
        funcs,
        name: rule.name.clone(),
        var_types: rule.var_types.clone(),
        range_var_types,
    }
}

fn bubble_up_range_defs_within_func(func: &FlatFunc) -> FlatFunc {
    let mut body: Vec<FlatStmt> = Vec::new();

    let mut range_var_defined_before: BTreeMap<FlatRangeVar, usize> = BTreeMap::new();
    let mut var_defined_before: BTreeMap<FlatVar, usize> = BTreeMap::new();

    for arg in func.args.iter() {
        var_defined_before.insert(*arg, 0);
    }

    for range_arg in func.range_args.iter() {
        range_var_defined_before.insert(*range_arg, 0);
    }

    for stmt in func.body.iter() {
        match stmt {
            FlatStmt::If(if_stmt) => {
                body.push(stmt.clone());

                for var in if_stmt.iter_vars() {
                    match var_defined_before.entry(var) {
                        btree_map::Entry::Occupied(_) => {}
                        btree_map::Entry::Vacant(entry) => {
                            entry.insert(body.len());
                        }
                    }
                }
            }
            FlatStmt::DefineRange(define_range_stmt) => match &define_range_stmt.expression {
                FlatRangeExpr::Index(_) => {
                    body.insert(0, stmt.clone());
                    for index in range_var_defined_before
                        .values_mut()
                        .chain(var_defined_before.values_mut())
                    {
                        *index += 1;
                    }
                    range_var_defined_before.insert(define_range_stmt.defined_var, 1);
                }
                FlatRangeExpr::Restriction(restriction_expr) => {
                    let FlatRangeRestrictionExpr {
                        range_var,
                        first_projection,
                    } = restriction_expr;

                    let insert_index = max(
                        *range_var_defined_before.get(&range_var).unwrap(),
                        *var_defined_before.get(&first_projection).unwrap(),
                    );
                    body.insert(insert_index, stmt.clone());
                    for index in range_var_defined_before
                        .values_mut()
                        .chain(var_defined_before.values_mut())
                    {
                        if *index > insert_index {
                            *index += 1;
                        }
                    }
                    range_var_defined_before
                        .insert(define_range_stmt.defined_var, insert_index + 1);
                }
            },
            FlatStmt::SurjThen(_) => {
                body.push(stmt.clone());
            }
            FlatStmt::NonSurjThen(non_surj_then_stmt) => {
                body.push(stmt.clone());
                var_defined_before.insert(non_surj_then_stmt.result, body.len());
            }
            FlatStmt::Call { .. } => {
                body.push(stmt.clone());
            }
        }
    }

    FlatFunc {
        args: func.args.clone(),
        range_args: func.range_args.clone(),
        name: func.name.clone(),
        body,
    }
}

fn range_definitions_prefix<'a>(stmts: &'a [FlatStmt]) -> Vec<FlatDefineRangeStmt> {
    stmts
        .iter()
        .map_while(|stmt| {
            if let FlatStmt::DefineRange(define_range_stmt) = stmt {
                Some(define_range_stmt.clone())
            } else {
                None
            }
        })
        .collect()
}

fn bubble_up_range_defs_to_caller(rule: &mut FlatRule, func_name: FlatFuncName) -> bool {
    let func = &mut rule.funcs[func_name.0];
    let range_defs = range_definitions_prefix(func.body.as_slice());
    if range_defs.is_empty() {
        return false;
    }

    func.body = func.body.drain(..).skip(range_defs.len()).collect();
    func.range_args.extend(
        range_defs
            .iter()
            .map(|define_range_stmt| define_range_stmt.defined_var),
    );

    // Fix all call-sites of the function:
    for func in rule.funcs.iter_mut() {
        let mut already_defined_range_vars: BTreeSet<FlatRangeVar> =
            func.range_args.iter().cloned().collect();
        func.body = func
            .body
            .drain(..)
            .flat_map(|stmt| {
                let (call_args, mut call_range_args) = match &stmt {
                    FlatStmt::Call {
                        func_name: name,
                        args,
                        range_args,
                    } if *name == func_name => (args.clone(), range_args.clone()),
                    FlatStmt::DefineRange(define_range_stmt) => {
                        already_defined_range_vars.insert(define_range_stmt.defined_var);
                        return vec![stmt];
                    }
                    _ => {
                        return vec![stmt];
                    }
                };

                call_range_args.extend(
                    range_defs
                        .iter()
                        .map(|define_range_stmt| define_range_stmt.defined_var),
                );

                let stmts: Vec<FlatStmt> = range_defs
                    .iter()
                    .filter_map(|define_range_stmt| {
                        if !already_defined_range_vars.insert(define_range_stmt.defined_var) {
                            return None; // Already defined, skip
                        }
                        Some(FlatStmt::DefineRange(define_range_stmt.clone()))
                    })
                    .chain([FlatStmt::Call {
                        func_name,
                        args: call_args,
                        range_args: call_range_args,
                    }])
                    .collect();
                stmts
            })
            .collect();
    }

    true
}

pub fn bubble_up_range_defs(rule: &mut FlatRule) {
    let mut did_change = true;
    while did_change {
        did_change = false;

        for func in rule.funcs.iter_mut() {
            let new_func = bubble_up_range_defs_within_func(func);
            if new_func != *func {
                *func = new_func;
                did_change = true;
            }
        }

        for i in 1..rule.funcs.len() {
            let func_name = FlatFuncName(i);
            if bubble_up_range_defs_to_caller(rule, func_name) {
                did_change = true;
            }
        }
    }
}
