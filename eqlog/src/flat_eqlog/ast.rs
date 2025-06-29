use crate::eqlog_util::*;
use std::sync::Arc;

use eqlog_eqlog::*;

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatInRel {
    EqlogRel(Rel),
    EqlogRelWithDiagonals {
        rel: Rel,
        // We must have: equalities.len() == rel.flat_arity().len()
        // equalities[i] = j if j is the smallest index such that rel[i] == rel[j]
        // for this diagonal.
        equalities: Arc<[usize]>,
    },
    Equality(Type),
    TypeSet(Type),
}

impl FlatInRel {
    pub fn arity(&self, eqlog: &Eqlog) -> Vec<Type> {
        match self {
            FlatInRel::EqlogRel(rel) => type_list_vec(eqlog.flat_arity(*rel).unwrap(), eqlog),
            FlatInRel::EqlogRelWithDiagonals { rel, equalities } => {
                let arity = type_list_vec(eqlog.flat_arity(*rel).unwrap(), eqlog);
                assert_eq!(equalities.len(), arity.len());

                arity
                    .into_iter()
                    .zip(equalities.iter().copied())
                    .enumerate()
                    .filter_map(|(i, (typ, j))| if i == j { Some(typ) } else { None })
                    .collect()
            }
            FlatInRel::Equality(typ) => vec![*typ, *typ],
            FlatInRel::TypeSet(typ) => {
                vec![*typ]
            }
        }
    }
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

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatRuleGroup {
    pub name: String,
    pub rules: Vec<FlatRule>,
}
