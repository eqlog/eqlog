use super::ast::*;
use super::index_selection::*;
use super::var_info::*;
use crate::eqlog_util::display_rel;
use by_address::ByAddress;
use eqlog_eqlog::*;
use std::collections::BTreeMap;

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
        name: func.name.clone(),
        body,
    }
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

    FlatRule {
        funcs,
        name: rule.name.clone(),
        var_types: rule.var_types.clone(),
    }
}
