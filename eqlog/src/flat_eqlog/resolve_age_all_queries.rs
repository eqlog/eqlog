use std::iter::once;

use super::ast::*;

/// Resolves all queries with age `QueryAge::All` in the given rule by splitting them into
/// QueryAge::New and QueryAge::Old queries.
pub fn resolve_age_all_queries(rule: &mut FlatRule) {
    // Strategy: Loop over all functions in the order they appear in the rule.
    // If the function contains a query with age `QueryAge::All`:
    // 1. Identify the first such query.
    // 2. Introduce two continuation functions, one for `QueryAge::New` and one for
    //    `QueryAge::Old`.
    // 3. Replace the original query and every statement after it with a call to the new and old
    //    continuation functions.
    // 4. The first statement in each of the continuation functions is given by the original query,
    //    but with the age changed to `QueryAge::New` and `QueryAge::Old`, respectively.
    // 5. The rest of the statements in the continuation functions are the statements after the
    //    query in the original function.
    //
    // Note that by appending the continuation functions as last functions in the rule, we process
    // them again in the loop. This is also required, since they might still contain queries with
    // QueryAge::All, which needs to be resolved as well.
    let funcs = &mut rule.funcs;
    // Invariant: funcs[..func_index] do not contain any queries with age `QueryAge::All`.
    for func_index in 0.. {
        if func_index >= funcs.len() {
            break;
        }

        let func = &funcs[func_index];

        let age_all_query_index = func.body.iter().position(|stmt| match stmt {
            FlatStmt::If(FlatIfStmt::Relation(if_rel_stmt)) => if_rel_stmt.age == QueryAge::All,
            FlatStmt::If(FlatIfStmt::Type(if_type_stmt)) => if_type_stmt.age == QueryAge::All,
            _ => false,
        });

        let age_all_query_index = match age_all_query_index {
            Some(i) => i,
            None => {
                continue;
            }
        };

        let init_stmts = &func.body[..age_all_query_index];
        let tail_stmts = &func.body[age_all_query_index + 1..];

        let mut cont_args = func.args.clone();
        for var in init_stmts.iter().flat_map(|stmt| stmt.iter_vars()) {
            // This is an O(n) operation, but it's probably OK in practice since the number of
            // variables is in the tens.
            if !cont_args.contains(&var) {
                cont_args.push(var.clone());
            }
        }

        let (if_new_stmt, if_old_stmt) = match &func.body[age_all_query_index] {
            FlatStmt::If(FlatIfStmt::Relation(if_rel_stmt)) => {
                let mut if_rel_stmt_new = if_rel_stmt.clone();
                if_rel_stmt_new.age = QueryAge::New;

                let mut if_rel_stmt_old = if_rel_stmt.clone();
                if_rel_stmt_old.age = QueryAge::Old;

                (
                    FlatStmt::If(FlatIfStmt::Relation(if_rel_stmt_new)),
                    FlatStmt::If(FlatIfStmt::Relation(if_rel_stmt_old)),
                )
            }
            FlatStmt::If(FlatIfStmt::Type(if_type_stmt)) => {
                let mut if_type_stmt_new = if_type_stmt.clone();
                if_type_stmt_new.age = QueryAge::New;

                let mut if_type_stmt_old = if_type_stmt.clone();
                if_type_stmt_old.age = QueryAge::Old;

                (
                    FlatStmt::If(FlatIfStmt::Type(if_type_stmt_new)),
                    FlatStmt::If(FlatIfStmt::Type(if_type_stmt_old)),
                )
            }
            _ => unreachable!("Impossible by construction of age_all_query_index"),
        };

        let new_cont_name = FlatFuncName(funcs.len());
        let old_cont_name = FlatFuncName(funcs.len() + 1);

        assert!(
            func.range_args.is_empty(),
            "Range arguments are not supposed to be present in this pass"
        );
        let query_new_cont = FlatFunc {
            name: new_cont_name,
            args: cont_args.clone(),
            range_args: Vec::new(),
            body: once(if_new_stmt)
                .chain(tail_stmts.iter().cloned())
                .collect(),
        };
        let query_old_cont = FlatFunc {
            name: old_cont_name,
            args: cont_args.clone(),
            range_args: Vec::new(),
            body: once(if_old_stmt)
                .chain(tail_stmts.iter().cloned())
                .collect(),
        };

        funcs.push(query_new_cont);
        funcs.push(query_old_cont);

        let func = &mut funcs[func_index];
        func.body.truncate(age_all_query_index);
        func.body.push(FlatStmt::Call {
            func_name: new_cont_name,
            args: cont_args.clone(),
            range_args: Vec::new(),
        });
        func.body.push(FlatStmt::Call {
            func_name: old_cont_name,
            args: cont_args.clone(),
            range_args: Vec::new(),
        });
    }
}
