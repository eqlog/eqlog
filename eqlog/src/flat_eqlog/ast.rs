use std::sync::Arc;

use eqlog_eqlog::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatInRel {
    EqlogRel(Rel),
    Equality(Type),
    TypeSet(Type),
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatOutRel {
    EqlogRel(Rel),
    Equality(Type),
    FuncDomain(Func),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatVar {
    pub name: Arc<str>,
    pub typ: Type,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum QueryAge {
    New,
    Old,
    All,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatIfStmt {
    pub rel: FlatInRel,
    pub args: Vec<FlatVar>,
    pub age: QueryAge,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatThenStmt {
    pub rel: FlatOutRel,
    pub args: Vec<FlatVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatRule {
    pub name: String,
    pub premise: Vec<FlatIfStmt>,
    pub conclusion: Vec<FlatThenStmt>,
}
