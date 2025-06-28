use crate::flat_eqlog::{FlatInRel, FlatOutRel, IndexSpec};
use std::sync::Arc;

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct SetVar {
    pub name: Arc<str>,
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
pub struct RestrictProjectExpr {
    pub set: SetVar,
    pub first_column_var: ElVar,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum InSetExpr {
    GetIndex(GetIndexExpr),
    RestrictProject(RestrictProjectExpr),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct DefineSetStmt {
    pub defined_var: SetVar,
    pub expr: InSetExpr,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IterStmt {
    pub rel: FlatInRel,
    pub first_column_var: ElVar,
    pub other_columns_var: SetVar,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct InsertStmt {
    pub rel: FlatOutRel,
    pub args: Vec<ElVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamStmt {
    DefineSet(DefineSetStmt),
    Iter(IterStmt),
    Insert(InsertStmt),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RamRoutine {
    pub name: Arc<str>,
    pub stmts: Vec<RamStmt>,
}
