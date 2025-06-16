use std::iter::once;

use super::ast::*;

pub fn resolve_age_all_queries(original: FlatRule) -> FlatRule {
    let mut funcs = original.funcs;
    let funcs_len = funcs.len();
    let mut additional_funcs = Vec::new();

    for (func_idx, func) in funcs.iter_mut().enumerate() {
        let mut new_stmts = Vec::new();
        let mut found_any = false;

        for (stmt_idx, stmt) in func.body.iter().enumerate() {
            if let FlatStmt::If(FlatIfStmt::Relation(relation_stmt)) = stmt {
                if relation_stmt.age == QueryAge::All {
                    found_any = true;

                    // Prepare New and Old modified statements
                    let mut new_relation = relation_stmt.clone();
                    new_relation.age = QueryAge::New;

                    let mut old_relation = relation_stmt.clone();
                    old_relation.age = QueryAge::Old;

                    // Create New function
                    let new_func_name = FlatFuncName(funcs_len + additional_funcs.len());
                    let new_func_body: Vec<FlatStmt> =
                        func.body[stmt_idx + 1..].iter().cloned().collect();

                    let new_func = FlatFunc {
                        name: new_func_name,
                        args: func.args.clone(),
                        body: once(FlatStmt::If(FlatIfStmt::Relation(new_relation)))
                            .chain(new_func_body.clone())
                            .collect(),
                    };
                    additional_funcs.push(new_func);

                    // Create Old function
                    let old_func_name = FlatFuncName(funcs_len + additional_funcs.len());
                    let old_func = FlatFunc {
                        name: old_func_name,
                        args: func.args.clone(),
                        body: once(FlatStmt::If(FlatIfStmt::Relation(old_relation)))
                            .chain(new_func_body)
                            .collect(),
                    };
                    additional_funcs.push(old_func);

                    // Add calls to the New and Old functions
                    new_stmts.push(FlatStmt::Call {
                        func_name: new_func_name,
                        args: func.args.clone(),
                    });
                    new_stmts.push(FlatStmt::Call {
                        func_name: old_func_name,
                        args: func.args.clone(),
                    });

                    // Stop processing the current function at the point of replacement
                    break;
                }
            }
            new_stmts.push(stmt.clone());
        }

        if found_any {
            func.body = new_stmts;
        }
    }

    funcs.extend(additional_funcs);

    // Return the modified FlatRule
    FlatRule {
        funcs,
        ..original // Keep other fields like name and var_types unchanged
    }
}
