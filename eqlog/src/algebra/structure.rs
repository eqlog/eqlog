//! Data types for per-rule and per-statement structures.
//!
//! A [`Structure`] over a [`crate::algebra::signature::Signature`] records the
//! elements ([`ElId`]), function applications ([`FuncApp`]) and predicate
//! applications ([`PredApp`]) that exist at a given point in a rule. Elements
//! either have a known [`ConcreteType`] (a non-optional [`TypeId`] together
//! with the element's parent model els) or none at all, and equality between
//! elements is tracked by an embedded
//! [`eqlog_runtime::Unification`]. Function and predicate applications are
//! plain data, keyed by their own contents, so two calls with identical
//! parents and arguments collapse naturally.
//!
//! [`Structures`] holds a flat arena of snapshots plus side tables from
//! [`RuleDeclId`] and [`StmtId`] to those snapshots. The
//! [`crate::algebra::algebraize`] module populates it.

use std::collections::{BTreeMap, BTreeSet};

use eqlog_runtime::Unification;

use crate::algebra::signature::{FuncId, PredId, TypeId};
use crate::ast::{RuleDeclId, StmtId, VarTermId};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ElId(pub(super) usize);

impl From<u32> for ElId {
    fn from(x: u32) -> Self {
        ElId(x as usize)
    }
}

impl From<ElId> for u32 {
    fn from(el: ElId) -> Self {
        debug_assert!(el.0 <= u32::MAX as usize);
        el.0 as u32
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructureId(usize);

/// A fully-known type for an [`ElId`]: the element's [`TypeId`] together with
/// the parent-model elements the type depends on. Parents are outermost first
/// and have the same length as `signature.type_(typ).parents` in a well-formed
/// program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteType {
    pub typ: TypeId,
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

#[derive(Clone, Debug)]
pub struct Structure {
    /// Live elements, keyed by [`ElId`]. `None` means the element's type has
    /// not been determined yet. After [`Structure::close`] only equivalence
    /// class roots remain as keys.
    pub els: BTreeMap<ElId, Option<ConcreteType>>,
    pub pred_apps: BTreeSet<PredApp>,
    pub func_apps: BTreeMap<FuncApp, ElId>,
    /// Variable bindings that have entered scope in this structure, keyed by
    /// the binding's [`VarTermId`] (which [`crate::scopes::Scopes`] records as
    /// the `Symbol::Var` payload). Analogous to
    /// `var(Structure, ElName) -> El` in eqlog.eql.
    pub var_els: BTreeMap<VarTermId, ElId>,
    /// Equivalence relation on [`ElId`]s. New ElIds start out in their own
    /// class; [`Structure::close`] may merge classes under functionality.
    pub unification: Unification<ElId>,
}

impl Default for Structure {
    fn default() -> Self {
        Self {
            els: BTreeMap::new(),
            pred_apps: BTreeSet::new(),
            func_apps: BTreeMap::new(),
            var_els: BTreeMap::new(),
            unification: Unification::new(),
        }
    }
}

impl Structure {
    /// Allocates a fresh [`ElId`] with the given (possibly unknown) concrete
    /// type and registers it with the unification.
    pub fn push_el(&mut self, ct: Option<ConcreteType>) -> ElId {
        let id = ElId(self.unification.len());
        self.unification.increase_size_to(id.0 + 1);
        self.els.insert(id, ct);
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
