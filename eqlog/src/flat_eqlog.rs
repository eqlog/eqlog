#![allow(dead_code)]

use eqlog_eqlog::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatVar(pub usize);

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatStmtEqual {
    pub lhs: FlatVar,
    pub rhs: FlatVar,
    pub typ: Type,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Rel {
    Pred(Pred),
    Func(Func),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatIfRelArg {
    pub var: FlatVar,
    pub typ: Type,
    pub fresh: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatIfStmtRelation {
    pub rel: Rel,
    pub args: Vec<FlatIfRelArg>,
    pub only_dirty: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatIfStmtType {
    pub var: FlatVar,
    pub typ: Type,
    pub only_dirty: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatIfStmt {
    Equal(FlatStmtEqual),
    Relation(FlatIfStmtRelation),
    Type(FlatIfStmtType),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatThenRelArg {
    pub var: FlatVar,
    pub typ: Type,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatThenStmtRelation {
    pub rel: Rel,
    pub args: Vec<FlatThenRelArg>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatThenStmtType {
    pub var: FlatVar,
    pub typ: Type,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatSurjThenStmt {
    Equal(FlatStmtEqual),
    Relation(FlatThenStmtRelation),
    Type(FlatThenStmtType),
}

pub type FlatNonSurjThenStmt = FlatThenStmtRelation;

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatStmt {
    If(FlatIfStmt),
    SurjThen(FlatSurjThenStmt),
    NonSurjThen(FlatNonSurjThenStmt),
    Fork(Vec<Vec<FlatStmt>>),
}
