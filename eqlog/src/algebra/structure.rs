//! Data types for per-rule and per-statement structures.
//!
//! A [`Structure`] over a [`crate::algebra::signature::Signature`] records the
//! elements ([`El`]), function applications ([`FuncApp`]) and predicate
//! applications ([`PredApp`]) that exist at a given point in a rule. Elements
//! carry an optional type and the chain of parent model elements they live
//! under. Function and predicate applications are plain data, keyed by their
//! own contents, so two calls with identical parents and arguments collapse
//! naturally.
//!
//! [`Structures`] holds a flat arena of snapshots plus side tables from
//! [`RuleDeclId`] and [`StmtId`] to those snapshots. The
//! [`crate::algebra::build_structure`] module populates it.

use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::{FuncId, PredId, TypeId};
use crate::ast::{RuleDeclId, StmtId, VarTermId};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ElId(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructureId(usize);

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
pub struct El {
    /// The element's type, if known. `None` for fresh wildcards and for
    /// variable bindings without a `var: Type` annotation.
    pub typ: Option<TypeId>,
    /// Enclosing model elements, outermost first.
    pub parents: Vec<ElId>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PredApp {
    pub pred: PredId,
    pub parents: Vec<ElId>,
    pub args: Vec<ElId>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FuncApp {
    pub func: FuncId,
    pub parents: Vec<ElId>,
    pub args: Vec<ElId>,
}

#[derive(Clone, Debug, Default)]
pub struct Structure {
    pub els: Vec<El>,
    pub pred_apps: BTreeSet<PredApp>,
    pub func_apps: BTreeMap<FuncApp, ElId>,
    /// Variable bindings that have entered scope in this structure, keyed by
    /// the binding's [`VarTermId`] (which [`crate::scopes::Scopes`] records as
    /// the `Symbol::Var` payload). Analogous to
    /// `var(Structure, ElName) -> El` in eqlog.eql.
    pub var_els: BTreeMap<VarTermId, ElId>,
}

impl Structure {
    pub fn push_el(&mut self, el: El) -> ElId {
        let id = ElId(self.els.len());
        self.els.push(el);
        id
    }
}

#[derive(Clone, Debug, Default)]
pub struct Structures {
    pub(super) arena: Vec<Structure>,
    pub(super) rule_initial: BTreeMap<RuleDeclId, StructureId>,
    pub(super) stmt_before: BTreeMap<StmtId, StructureId>,
    pub(super) stmt_after: BTreeMap<StmtId, StructureId>,
}

#[allow(dead_code)]
impl Structures {
    pub fn structure(&self, id: StructureId) -> &Structure {
        &self.arena[id.0]
    }

    pub fn rule_initial_structure(&self, id: RuleDeclId) -> StructureId {
        *self
            .rule_initial
            .get(&id)
            .expect("rule initial structure not populated")
    }

    pub fn stmt_before_structure(&self, id: StmtId) -> StructureId {
        *self
            .stmt_before
            .get(&id)
            .expect("stmt before-structure not populated")
    }

    pub fn stmt_after_structure(&self, id: StmtId) -> StructureId {
        *self
            .stmt_after
            .get(&id)
            .expect("stmt after-structure not populated")
    }

    pub(super) fn push(&mut self, structure: Structure) -> StructureId {
        let id = StructureId(self.arena.len());
        self.arena.push(structure);
        id
    }
}
