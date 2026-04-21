//! Data types for per-rule and per-statement structures, plus the saturation
//! pass that closes a [`Structure`] under functionality and signature typing.
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

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use eqlog_runtime::Unification;

use crate::algebra::signature::{FuncId, PredId, Signature, TypeId};
use crate::ast::{RuleDeclId, StmtId, TermId, VarTermId};

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
    /// Many-to-one map from term occurrences to the element they evaluate
    /// to. Used to attribute locations when reporting errors about an
    /// element. Analogous to `semantic_el(TermNode, Structure) -> El` in
    /// eqlog.eql.
    pub semantic_el: BTreeMap<TermId, ElId>,
    /// Elements introduced as ambient model instances by the rule's
    /// enclosing-model scopes. Every entry here has a fixed [`ConcreteType`]
    /// for the corresponding model type; these elements have no
    /// [`TermId`] in `semantic_el` and should never legitimately take part
    /// in a type conflict.
    pub ambient_model_els: BTreeSet<ElId>,
    /// Equivalence relation on [`ElId`]s. New ElIds start out in their own
    /// class; [`Structure::close`] may merge classes under functionality.
    pub unification: Unification<ElId>,
    /// Equalities that have been declared (via [`Structure::equate`]) or
    /// derived internally (from functionality, typing, or parent matching)
    /// but whose effects on the rest of the structure have not yet been
    /// drained. Always empty after [`Structure::close`] returns.
    pub(super) pending_equalities: Vec<(ElId, ElId)>,
}

impl Default for Structure {
    fn default() -> Self {
        Self {
            els: BTreeMap::new(),
            pred_apps: BTreeSet::new(),
            func_apps: BTreeMap::new(),
            var_els: BTreeMap::new(),
            semantic_el: BTreeMap::new(),
            ambient_model_els: BTreeSet::new(),
            unification: Unification::new(),
            pending_equalities: Vec::new(),
        }
    }
}

/// A type disagreement discovered during [`Structure::close`]: two
/// incompatible [`TypeId`]s got assigned to the same equivalence class
/// rooted at `cls`. The caller is responsible for turning this into a
/// user-facing [`crate::error::CompileError`]; typically it looks up a
/// term in [`Structure::semantic_el`] whose element falls in `cls` and
/// emits `ConflictingTermType` at that term's location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeConflict {
    pub cls: ElId,
    pub types: (TypeId, TypeId),
}

impl Structure {
    /// Allocates a fresh [`ElId`], registers it with the unification and
    /// records it in `els` with no concrete type yet. Callers that know a
    /// type up front write it into `els` after the call.
    pub fn push_el(&mut self) -> ElId {
        let id = ElId(self.unification.len());
        self.unification.increase_size_to(id.0 + 1);
        self.els.insert(id, None);
        id
    }

    /// Declares that `a` and `b` are equal. Just enqueues the pair on
    /// `pending_equalities`; the actual class merge and any cascading
    /// parent unifications happen during [`Structure::close`].
    pub fn equate(&mut self, a: ElId, b: ElId) {
        self.pending_equalities.push((a, b));
    }

    /// Closes the structure under functionality and signature-imposed typing.
    ///
    /// Runs the naive fixed point of two passes until both settle:
    ///
    ///   - `functionality`: canonicalise every [`FuncApp`] key and merge
    ///     duplicates by unioning their result elements.
    ///   - `typing`: walk every [`FuncApp`] and [`PredApp`] and impose the
    ///     type each argument (and the result, for funcs) is required to
    ///     have by the signature. If an element already has an incompatible
    ///     type, record a [`TypeConflict`]; otherwise enqueue the
    ///     corresponding parent pairs onto `pending_equalities`.
    ///   - `drain_equalities`: pop pairs from `pending_equalities`, union
    ///     their classes and merge their `els` entries (which may enqueue
    ///     further parent pairs until it settles).
    ///
    /// The fixed point terminates because the number of equivalence classes
    /// plus the size of `pending_equalities` strictly decreases across
    /// iterations that do any work.
    ///
    /// After the loop exits, `pending_equalities` is empty and every
    /// remaining reference in `pred_apps`, `var_els` and in [`ConcreteType`]
    /// parents is rewritten to the root of its class, with non-root entries
    /// dropped from `els`. Callers translate the returned [`TypeConflict`]s
    /// into user-facing errors, typically by picking a term in
    /// `semantic_el` whose class matches.
    pub fn close(&mut self, signature: &Signature) -> Vec<TypeConflict> {
        let mut conflicts = Vec::new();
        loop {
            let drained = self.drain_equalities(&mut conflicts);
            let func_changed = self.functionality();
            let type_changed = self.typing(signature, &mut conflicts);
            if !drained && !func_changed && !type_changed {
                break;
            }
        }
        self.canonicalise_refs();
        conflicts
    }

    /// Drains `pending_equalities` down to empty, performing the union and
    /// merging `els` entries for each pair. Records conflicts and enqueues
    /// further pairs as parent lists of matching types are reconciled.
    /// Returns true iff at least one class merge happened.
    fn drain_equalities(&mut self, conflicts: &mut Vec<TypeConflict>) -> bool {
        let mut changed = false;
        while let Some((a, b)) = self.pending_equalities.pop() {
            let a = self.root(a);
            let b = self.root(b);
            if a == b {
                continue;
            }
            changed = true;

            // Deterministic winner: smaller id stays root.
            let (keep, drop) = if a.0 <= b.0 { (a, b) } else { (b, a) };
            self.unification.union_roots_into(drop, keep);

            let drop_ct = self.els.remove(&drop).flatten();
            let keep_ct = self.els.remove(&keep).flatten();
            let merged = match (keep_ct, drop_ct) {
                (None, None) => None,
                (Some(x), None) | (None, Some(x)) => Some(x),
                (Some(k), Some(d)) => {
                    if k.typ != d.typ {
                        conflicts.push(TypeConflict {
                            cls: keep,
                            types: (k.typ, d.typ),
                        });
                        Some(k)
                    } else {
                        let n = k.parents.len().min(d.parents.len());
                        for i in 0..n {
                            self.pending_equalities.push((k.parents[i], d.parents[i]));
                        }
                        Some(ConcreteType {
                            typ: k.typ,
                            parents: k.parents,
                        })
                    }
                }
            };
            self.els.insert(keep, merged);
        }
        changed
    }

    /// Rebuilds `func_apps` with canonical keys and enqueues an equality on
    /// `pending_equalities` for every pair of duplicates. Returns true iff
    /// at least one duplicate was found.
    fn functionality(&mut self) -> bool {
        let old = mem::take(&mut self.func_apps);
        let mut new: BTreeMap<FuncApp, ElId> = BTreeMap::new();
        let mut changed = false;
        for (app, result) in old {
            let canon_app = FuncApp {
                func: app.func,
                parents: app.parents.into_iter().map(|e| self.root(e)).collect(),
                args: app.args.into_iter().map(|e| self.root(e)).collect(),
            };
            let canon_result = self.root(result);
            match new.entry(canon_app) {
                Entry::Vacant(v) => {
                    v.insert(canon_result);
                }
                Entry::Occupied(o) => {
                    let existing = *o.get();
                    if existing != canon_result {
                        self.pending_equalities.push((existing, canon_result));
                        changed = true;
                    }
                }
            }
        }
        self.func_apps = new;
        changed
    }

    /// Walks each func/pred application and propagates the type the
    /// signature demands for every argument (and for the result of a func).
    /// Returns true iff anything changed (either a fresh type got recorded
    /// or a parent pair got enqueued on `pending_equalities`).
    fn typing(&mut self, signature: &Signature, conflicts: &mut Vec<TypeConflict>) -> bool {
        let mut changed = false;

        let apps: Vec<(FuncApp, ElId)> = self
            .func_apps
            .iter()
            .map(|(a, r)| (a.clone(), *r))
            .collect();
        for (app, result) in apps {
            let func_data = signature.func(app.func);
            if let Some(ct) = concrete_type_at(signature, func_data.codomain, &app.parents) {
                if self.impose_concrete_type(result, ct, conflicts) {
                    changed = true;
                }
            }
            for (i, &arg) in app.args.iter().enumerate() {
                let Some(&dom_tid) = func_data.domain.get(i) else {
                    break;
                };
                if let Some(ct) = concrete_type_at(signature, dom_tid, &app.parents) {
                    if self.impose_concrete_type(arg, ct, conflicts) {
                        changed = true;
                    }
                }
            }
        }

        let pred_apps: Vec<PredApp> = self.pred_apps.iter().cloned().collect();
        for app in pred_apps {
            let pred_data = signature.pred(app.pred);
            for (i, &arg) in app.args.iter().enumerate() {
                let Some(&arity_tid) = pred_data.arity.get(i) else {
                    break;
                };
                if let Some(ct) = concrete_type_at(signature, arity_tid, &app.parents) {
                    if self.impose_concrete_type(arg, ct, conflicts) {
                        changed = true;
                    }
                }
            }
        }

        changed
    }

    /// Asserts that `el`'s type is `ct`. On mismatch emits a conflict error
    /// and leaves the existing entry in place. On match, enqueues the
    /// pairwise parent equalities onto `pending_equalities`. Returns true
    /// iff the entry was freshly populated or at least one parent pair was
    /// enqueued.
    fn impose_concrete_type(
        &mut self,
        el: ElId,
        ct: ConcreteType,
        conflicts: &mut Vec<TypeConflict>,
    ) -> bool {
        let root = self.root(el);
        match self.els.get(&root).cloned().flatten() {
            None => {
                self.els.insert(root, Some(ct));
                true
            }
            Some(existing) => {
                if existing.typ != ct.typ {
                    conflicts.push(TypeConflict {
                        cls: root,
                        types: (existing.typ, ct.typ),
                    });
                    return false;
                }
                let n = existing.parents.len().min(ct.parents.len());
                let mut changed = false;
                for i in 0..n {
                    let a = self.root(existing.parents[i]);
                    let b = self.root(ct.parents[i]);
                    if a != b {
                        self.pending_equalities.push((a, b));
                        changed = true;
                    }
                }
                changed
            }
        }
    }

    /// Final pass: rewrite every remaining reference (pred app parents and
    /// args, var-el values, semantic-el values, [`ConcreteType`] parents)
    /// to the root of its current class, and drop non-root entries from
    /// `els`.
    fn canonicalise_refs(&mut self) {
        let old_pred_apps = mem::take(&mut self.pred_apps);
        for app in old_pred_apps {
            self.pred_apps.insert(PredApp {
                pred: app.pred,
                parents: app.parents.into_iter().map(|e| self.root(e)).collect(),
                args: app.args.into_iter().map(|e| self.root(e)).collect(),
            });
        }

        let values: Vec<(VarTermId, ElId)> = self.var_els.iter().map(|(k, v)| (*k, *v)).collect();
        for (k, v) in values {
            self.var_els.insert(k, self.root(v));
        }

        let sem: Vec<(TermId, ElId)> = self.semantic_el.iter().map(|(k, v)| (*k, *v)).collect();
        for (k, v) in sem {
            self.semantic_el.insert(k, self.root(v));
        }

        let old_els = mem::take(&mut self.els);
        for (id, ct) in old_els {
            let root = self.root(id);
            if root != id {
                continue;
            }
            let ct = ct.map(|ct| ConcreteType {
                typ: ct.typ,
                parents: ct.parents.into_iter().map(|e| self.root(e)).collect(),
            });
            self.els.insert(id, ct);
        }
    }

    fn root(&self, id: ElId) -> ElId {
        self.unification.root_const(id)
    }
}

/// Materialises the [`ConcreteType`] a given [`TypeId`] has inside a relation
/// application whose enclosing-model elements are `parents`. Returns `None`
/// if `parents` is too short to cover the type's parent chain, which only
/// happens for malformed programs.
fn concrete_type_at(signature: &Signature, tid: TypeId, parents: &[ElId]) -> Option<ConcreteType> {
    let n = signature.type_(tid).parents.len();
    if n > parents.len() {
        return None;
    }
    Some(ConcreteType {
        typ: tid,
        parents: parents[..n].to_vec(),
    })
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
