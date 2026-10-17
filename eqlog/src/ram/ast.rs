use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, FlatOutRel, FlatRel, FlatRule, IndexSpec, RuleSchedule};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Strictness {
    Lazy,
    Strict,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct SetVarName {
    pub stmt_index: usize,
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub restricted: usize,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct SetVar {
    pub name: SetVarName,
    pub arity: usize,
    pub strictness: Strictness,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct ElVar {
    pub name: Arc<str>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct GetIndexExpr {
    pub rel: FlatInRel,
    pub index_spec: IndexSpec,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RestrictExpr {
    pub set: SetVar,
    pub first_column_var: ElVar,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum InSetExpr {
    GetIndex(GetIndexExpr),
    Restrict(RestrictExpr),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct DefineSetStmt {
    pub defined_var: SetVar,
    pub expr: InSetExpr,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IterStmt {
    pub sets: Vec<SetVar>,
    pub loop_var_el: ElVar,
    pub loop_var_set: SetVar,
    pub first_only: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct InsertStmt {
    pub rel: FlatOutRel,
    pub args: Vec<ElVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct GuardInhabitedStmt {
    pub sets: Vec<SetVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamStmt {
    DefineSet(DefineSetStmt),
    Iter(IterStmt),
    Insert(InsertStmt),
    GuardInhabited(GuardInhabitedStmt),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RamRoutine {
    pub name: String,
    pub flat_rule: FlatRule,
    pub stmts: Vec<RamStmt>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RamModule {
    pub name: String,
    pub routines: Vec<RamRoutine>,
}

pub struct RamProgram {
    // Keep group order through lowering so the schedule also indexes modules.
    pub modules: Vec<RamModule>,
    pub schedule: RuleSchedule,
    pub preparations: Vec<IndexPreparation>,
    pub model_preparations: BTreeMap<TypeId, NativePreparation>,
    pub native_indices: Vec<NativeIndexPreparation>,
}

pub struct IndexPreparation {
    pub indices: BTreeSet<(FlatInRel, IndexSpec)>,
    pub membership_only: BTreeSet<(FlatInRel, IndexSpec)>,
    // Owner-scoped traversal can leave other slices pending, so only a full
    // preparation permits deriving native indices from the primary relation.
    pub native_indices_from_primary: BTreeSet<usize>,
    pub native: NativePreparation,
    pub stable: Option<NativePreparation>,
}

pub struct NativePreparation {
    pub native_indices: BTreeSet<usize>,
    pub support_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    pub propagation: PropagationPlan,
    pub descendants: BTreeSet<TypeId>,
}

impl IndexPreparation {
    pub fn reads_descendants(&self) -> bool {
        !self.native.descendants.is_empty()
            || self
                .stable
                .as_ref()
                .is_some_and(|plan| !plan.descendants.is_empty())
    }

    pub fn native_indices(&self) -> impl Iterator<Item = &usize> {
        self.native
            .native_indices
            .iter()
            .chain(self.stable.iter().flat_map(|plan| &plan.native_indices))
    }
}

#[derive(Default)]
pub struct PropagationPlan {
    pub relations: BTreeSet<FlatRel>,
    pub models: BTreeSet<TypeId>,
    pub graph_indices: BTreeMap<TypeId, BTreeSet<(FlatInRel, IndexSpec)>>,
    pub map_indices: BTreeMap<(TypeId, FlatInRel), BTreeSet<(FlatInRel, IndexSpec)>>,
}

pub struct NativeIndexPreparation {
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub models: Vec<TypeId>,
    pub support_indices: BTreeSet<(FlatInRel, IndexSpec)>,
}

impl RamModule {
    pub fn owner_count(&self) -> usize {
        self.routines
            .first()
            .map_or(0, |routine| routine.flat_rule.scope.owners().len())
    }

    pub fn input_indices(&self) -> BTreeSet<(FlatInRel, IndexSpec)> {
        self.routines
            .iter()
            .flat_map(RamRoutine::input_indices)
            .collect()
    }
}

impl RamRoutine {
    pub fn input_indices(&self) -> BTreeSet<(FlatInRel, IndexSpec)> {
        self.stmts
            .iter()
            .filter_map(|stmt| match stmt {
                RamStmt::DefineSet(stmt) => match &stmt.expr {
                    InSetExpr::GetIndex(index) => {
                        Some((index.rel.clone(), index.index_spec.clone()))
                    }
                    InSetExpr::Restrict(_) => None,
                },
                RamStmt::Iter(_) | RamStmt::Insert(_) | RamStmt::GuardInhabited(_) => None,
            })
            .collect()
    }
}
