use std::{collections::BTreeMap, fmt::Display, iter::once};

use eqlog_eqlog::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatVar(pub usize);

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatFuncName(pub usize);

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatStmtEqual {
    pub lhs: FlatVar,
    pub rhs: FlatVar,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Rel {
    Pred(Pred),
    Func(Func),
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum QueryAge {
    New,
    Old,
    All,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatIfStmtRelation {
    pub rel: Rel,
    pub args: Vec<FlatVar>,
    pub age: QueryAge,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatIfStmtType {
    pub var: FlatVar,
    pub age: QueryAge,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatIfStmt {
    Equal(FlatStmtEqual),
    Relation(FlatIfStmtRelation),
    Type(FlatIfStmtType),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatSurjThenStmtRelation {
    pub rel: Rel,
    pub args: Vec<FlatVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatThenStmtType {
    pub var: FlatVar,
    pub typ: Type,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatSurjThenStmt {
    Equal(FlatStmtEqual),
    Relation(FlatSurjThenStmtRelation),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatNonSurjThenStmt {
    pub func: Func,
    pub func_args: Vec<FlatVar>,
    pub result: FlatVar,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatStmt {
    If(FlatIfStmt),
    SurjThen(FlatSurjThenStmt),
    NonSurjThen(FlatNonSurjThenStmt),
    Call {
        func_name: FlatFuncName,
        args: Vec<FlatVar>,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatFunc {
    pub name: FlatFuncName,
    pub args: Vec<FlatVar>,
    pub body: Vec<FlatStmt>,
}

impl FlatStmtEqual {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let FlatStmtEqual { lhs, rhs } = *self;
        [lhs, rhs].into_iter()
    }
}

impl FlatIfStmtRelation {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let FlatIfStmtRelation {
            rel: _,
            args,
            age: _,
        } = self;
        args.iter().copied()
    }
}

impl FlatIfStmtType {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let FlatIfStmtType { var, age: _ } = self;
        once(*var)
    }
}

impl FlatIfStmt {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let mut result = Vec::new();
        match self {
            FlatIfStmt::Equal(eq) => {
                result.extend(eq.iter_vars());
            }
            FlatIfStmt::Relation(rel) => {
                result.extend(rel.iter_vars());
            }
            FlatIfStmt::Type(typ) => {
                result.extend(typ.iter_vars());
            }
        }
        result.into_iter()
    }
}

impl FlatSurjThenStmtRelation {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let FlatSurjThenStmtRelation { rel: _, args } = self;
        args.iter().copied()
    }
}

impl FlatSurjThenStmt {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let mut result = Vec::new();
        match self {
            FlatSurjThenStmt::Equal(eq) => {
                result.extend(eq.iter_vars());
            }
            FlatSurjThenStmt::Relation(rel) => {
                result.extend(rel.iter_vars());
            }
        }
        result.into_iter()
    }
}

impl FlatNonSurjThenStmt {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let FlatNonSurjThenStmt {
            func: _,
            func_args,
            result,
        } = self;
        func_args.iter().copied().chain(once(*result))
    }
}

impl FlatStmt {
    pub fn iter_vars<'a>(&'a self) -> impl 'a + Iterator<Item = FlatVar> {
        let mut vars: Vec<FlatVar> = Vec::new();
        match self {
            FlatStmt::If(if_stmt) => {
                vars.extend(if_stmt.iter_vars());
            }
            FlatStmt::SurjThen(surj_then_stmt) => {
                vars.extend(surj_then_stmt.iter_vars());
            }
            FlatStmt::NonSurjThen(non_surj_then_stmt) => {
                vars.extend(non_surj_then_stmt.iter_vars());
            }
            FlatStmt::Call { func_name: _, args } => {
                vars.extend(args.iter().copied());
            }
        };

        vars.into_iter()
    }
}

pub struct FlatRule {
    pub name: String,
    pub funcs: Vec<FlatFunc>,
    pub var_types: BTreeMap<FlatVar, Type>,
}

impl Rel {
    pub fn display<'a>(
        &'a self,
        eqlog: &'a Eqlog,
        identifiers: &'a BTreeMap<Ident, String>,
    ) -> impl 'a + Display {
        let ident = match *self {
            Rel::Pred(pred) => eqlog
                .iter_semantic_pred()
                .find_map(|(ident, pred0)| eqlog.are_equal_pred(pred0, pred).then_some(ident))
                .expect("semantic_pred should be surjective"),
            Rel::Func(func) => eqlog
                .iter_semantic_func()
                .find_map(|(ident, func0)| eqlog.are_equal_func(func0, func).then_some(ident))
                .expect("semantic_func should be surjective"),
        };
        identifiers.get(&ident).unwrap().as_str()
    }
}
