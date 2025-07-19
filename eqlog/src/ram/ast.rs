use crate::flat_eqlog::{FlatInRel, FlatOutRel, FlatRule, IndexSpec};
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
