use std::collections::BTreeSet;

use super::ast::*;
use crate::flat_eqlog::IndexSelection;

pub fn make_ram_lazy(ram_stmts: &mut [RamStmt], indices: &IndexSelection) {
    let mut lazy_vars: BTreeSet<SetVarName> = BTreeSet::new();

    for stmt in ram_stmts.iter_mut() {
        match stmt {
            RamStmt::DefineSet(define_set) => match &define_set.expr {
                InSetExpr::Restrict(_) => {
                    lazy_vars.insert(define_set.defined_var.name.clone());
                    define_set.defined_var.strictness = Strictness::Lazy;
                }
                InSetExpr::GetIndex(index) => {
                    if !indices.is_primary(&index.rel, &index.index_spec) {
                        lazy_vars.insert(define_set.defined_var.name.clone());
                        define_set.defined_var.strictness = Strictness::Lazy;
                    }
                }
            },
            RamStmt::Iter(iter_stmt) => {
                for set_var in iter_stmt.sets.iter_mut() {
                    if lazy_vars.contains(&set_var.name) {
                        set_var.strictness = Strictness::Lazy;
                    }
                }

                if lazy_vars.contains(&iter_stmt.loop_var_set.name) {
                    iter_stmt.loop_var_set.strictness = Strictness::Lazy;
                }
            }
            RamStmt::Insert(_) => {}
            RamStmt::GuardInhabited(guard_inhabited_stmt) => {
                for set_var in guard_inhabited_stmt.sets.iter_mut() {
                    if lazy_vars.contains(&set_var.name) {
                        set_var.strictness = Strictness::Lazy;
                    }
                }
            }
        }
    }
}
