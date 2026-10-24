use std::collections::BTreeSet;

use super::ast::*;

pub fn make_ram_lazy(ram_stmts: &mut [QueryOp]) {
    let mut lazy_vars: BTreeSet<SetVarName> = BTreeSet::new();

    for stmt in ram_stmts.iter_mut() {
        match stmt {
            QueryOp::DefineSet(define_set) => match &define_set.expr {
                InSetExpr::Restrict(_) => {
                    lazy_vars.insert(define_set.defined_var.name.clone());
                    define_set.defined_var.strictness = Strictness::Lazy;
                }
                InSetExpr::GetIndex(_) => {}
            },
            QueryOp::Iter(iter_stmt) => {
                for set_var in iter_stmt
                    .sets
                    .iter_mut()
                    .chain(&mut iter_stmt.lookup_drivers)
                {
                    if lazy_vars.contains(&set_var.name) {
                        set_var.strictness = Strictness::Lazy;
                    }
                }

                if lazy_vars.contains(&iter_stmt.loop_var_set.name) {
                    iter_stmt.loop_var_set.strictness = Strictness::Lazy;
                }
            }
            QueryOp::Insert(_) => {}
            QueryOp::GuardPlan(plan) => {
                for set in plan.original.iter_mut().chain(&mut plan.alternative) {
                    if lazy_vars.contains(&set.name) {
                        set.strictness = Strictness::Lazy;
                    }
                }
            }
            QueryOp::GuardInhabited(guard_inhabited_stmt) => {
                for set_var in guard_inhabited_stmt.sets.iter_mut() {
                    if lazy_vars.contains(&set_var.name) {
                        set_var.strictness = Strictness::Lazy;
                    }
                }
            }
        }
    }
}
