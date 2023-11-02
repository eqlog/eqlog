#![allow(dead_code)]

use eqlog_eqlog::*;

pub struct FlatVar(pub usize);

pub struct FlatStmtEqual {
    pub lhs: FlatVar,
    pub rhs: FlatVar,
    pub typ: Type,
}

pub enum Rel {
    Pred(Pred),
    Func(Func),
}

pub struct FlatIfRelArg {
    pub var: FlatVar,
    pub typ: Type,
    pub fresh: bool,
}

pub struct FlatIfStmtRelation {
    pub rel: Rel,
    pub args: Vec<FlatIfRelArg>,
    pub only_dirty: bool,
}

pub struct FlatIfStmtType {
    pub var: FlatVar,
    pub typ: Type,
    pub only_dirty: bool,
}

pub enum FlatIfStmt {
    Equal(FlatStmtEqual),
    Relation(FlatIfStmtRelation),
    Type(FlatIfStmtType),
}

pub struct FlatThenRelArg {
    pub var: FlatVar,
    pub typ: Type,
}

pub struct FlatThenStmtRelation {
    pub rel: Rel,
    pub args: Vec<FlatThenRelArg>,
}

pub struct FlatThenStmtType {
    pub var: FlatVar,
    pub typ: Type,
}

pub enum FlatSurjThenStmt {
    Equal(FlatStmtEqual),
    Relation(FlatThenStmtRelation),
    Type(FlatThenStmtType),
}

pub type FlatNonSurjThenStmt = FlatThenStmtRelation;

pub enum FlatStmt {
    If(FlatIfStmt),
    SurjThen(FlatSurjThenStmt),
    NonSurjThen(FlatNonSurjThenStmt),
    Fork(Vec<Vec<FlatStmt>>),
}
