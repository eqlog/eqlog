use crate::algebra::signature::{FuncId, PredId, Signature, TypeId};
use std::sync::Arc;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatRel {
    Pred(PredId),
    Func(FuncId),
    ModelMember(TypeId),
}

impl FlatRel {
    pub fn column_maps_under(&self, signature: &Signature, column: usize, model: TypeId) -> bool {
        let typ = self.arity(signature)[column];
        let depth = signature.type_(model).parents.len();
        if signature.type_(typ).parents.get(depth) != Some(&model) {
            return false;
        }
        self.parent_columns(signature)
            .map_or(true, |columns| columns[column].get(depth) == Some(&depth))
    }

    pub fn parent_columns<'a>(&self, signature: &'a Signature) -> Option<&'a [Vec<usize>]> {
        match self {
            FlatRel::Pred(pred) => signature.pred_parent_columns(*pred),
            FlatRel::Func(func) => signature.func_parent_columns(*func),
            FlatRel::ModelMember(_) => None,
        }
    }

    pub fn arity(&self, signature: &Signature) -> Vec<TypeId> {
        match self {
            FlatRel::Pred(pred) => {
                let pred = signature.pred(*pred);
                flat_args(&pred.parents, &pred.arity)
            }
            FlatRel::Func(func) => {
                let func = signature.func(*func);
                let mut arity = flat_args(&func.parents, &func.domain);
                arity.push(func.codomain);
                arity
            }
            FlatRel::ModelMember(typ) => {
                let parents = &signature.type_(*typ).parents;
                assert!(
                    !parents.is_empty(),
                    "model-member relation requires a member type"
                );
                let mut arity = parents.clone();
                arity.push(*typ);
                arity
            }
        }
    }

    pub fn parent_model_type(&self, signature: &Signature) -> Option<TypeId> {
        match self {
            FlatRel::Pred(pred) => signature.pred(*pred).parents.last().copied(),
            FlatRel::Func(func) => signature.func(*func).parents.last().copied(),
            FlatRel::ModelMember(member_type) => {
                signature.type_(*member_type).parents.last().copied()
            }
        }
    }

    pub fn is_model_membership_relation(self) -> bool {
        matches!(self, FlatRel::ModelMember(_))
    }
}

pub fn flat_domain(func: FuncId, signature: &Signature) -> Vec<TypeId> {
    let func = signature.func(func);
    flat_args(&func.parents, &func.domain)
}

fn flat_args(parents: &[TypeId], args: &[TypeId]) -> Vec<TypeId> {
    let mut flat_args = Vec::with_capacity(parents.len() + args.len());
    flat_args.extend(parents.iter().copied());
    flat_args.extend(args.iter().copied());
    flat_args
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum FlatInRel {
    Rel(FlatRel),
    RelWithDiagonals {
        rel: FlatRel,
        // We must have: equalities.len() == relation arity.
        // equalities[i] = j if j is the smallest index such that rel[i] == rel[j]
        // for this diagonal.
        equalities: Arc<[usize]>,
    },
    Equality(TypeId),
    TypeSet(TypeId),
}

impl FlatInRel {
    pub fn arity(&self, signature: &Signature) -> Vec<TypeId> {
        match self {
            FlatInRel::Rel(rel) => rel.arity(signature),
            FlatInRel::RelWithDiagonals { rel, equalities } => {
                let arity = rel.arity(signature);
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
    Rel(FlatRel),
    Equality(TypeId),
    FuncDomain(FuncId),
}

impl FlatOutRel {
    pub fn arity(&self, signature: &Signature) -> Vec<TypeId> {
        match self {
            FlatOutRel::Rel(rel) => rel.arity(signature),
            FlatOutRel::Equality(typ) => {
                vec![*typ, *typ]
            }
            FlatOutRel::FuncDomain(func) => flat_domain(*func, signature),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatVar {
    pub name: Arc<str>,
    pub typ: TypeId,
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
pub enum RuleScope {
    Global,
    Model { model: TypeId, owners: Vec<FlatVar> },
}

impl RuleScope {
    pub fn owners(&self) -> &[FlatVar] {
        match self {
            Self::Global => &[],
            Self::Model { owners, .. } => owners,
        }
    }

    pub fn model(&self) -> Option<TypeId> {
        match self {
            Self::Global => None,
            Self::Model { model, .. } => Some(*model),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatRule {
    pub name: String,
    pub scope: RuleScope,
    pub premise: Vec<FlatIfStmt>,
    pub conclusion: Vec<FlatThenStmt>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatRuleGroup {
    pub name: String,
    pub rules: Vec<FlatRule>,
}
