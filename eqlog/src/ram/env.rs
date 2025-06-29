use crate::flat_eqlog::{FlatInRel, FlatOutRel, IndexSpec};
use crate::ram::ast::{InSetExpr, RamModule, RamStmt};
use std::collections::{BTreeMap, BTreeSet};

pub struct ModuleEnvFields {
    pub indices: BTreeMap<(FlatInRel, IndexSpec), ()>,
    /// A unique version of the keys in `indices` where EqlogWithRelDiagonals { ... } is instead
    /// represented as EqlogRel(_).
    /// This is here because we need to know which "table modules" a ram module depends on.
    pub in_rels_modulo_diagonals: BTreeSet<FlatInRel>,
    pub out_rels: BTreeSet<FlatOutRel>,
}

impl ModuleEnvFields {
    pub fn from_module(module: &RamModule) -> Self {
        let mut indices = BTreeMap::new();
        let mut in_rels_modulo_diagonals = BTreeSet::new();
        let mut out_rels = BTreeSet::new();

        for routine in &module.routines {
            for stmt in &routine.stmts {
                match stmt {
                    RamStmt::DefineSet(define_set) => {
                        if let InSetExpr::GetIndex(get_index) = &define_set.expr {
                            indices
                                .insert((get_index.rel.clone(), get_index.index_spec.clone()), ());

                            // Convert EqlogRelWithDiagonals to EqlogRel for in_rels_modulo_diagonals
                            let rel_modulo_diagonals = match &get_index.rel {
                                FlatInRel::EqlogRelWithDiagonals { rel, .. } => {
                                    FlatInRel::EqlogRel(*rel)
                                }
                                other => other.clone(),
                            };
                            in_rels_modulo_diagonals.insert(rel_modulo_diagonals);
                        }
                    }
                    RamStmt::Insert(insert) => {
                        out_rels.insert(insert.rel.clone());
                    }
                    RamStmt::Iter(_) => {}
                }
            }
        }

        Self {
            indices,
            in_rels_modulo_diagonals,
            out_rels,
        }
    }
}
