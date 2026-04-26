//! Per-rule algebraic data and the saturation pass that closes it
//! under functionality and signature typing.
//!
//! A [`Structure`] over a [`crate::algebra::signature::Signature`] records
//! the elements ([`ElId`]), function applications ([`FuncApp`]) and
//! predicate applications ([`PredApp`]) that exist at a given point in a
//! rule. Elements either have a known [`ConcreteType`] (a non-optional
//! [`TypeId`] together with the element's parent model els) or none at
//! all, and equality between elements is tracked by an embedded
//! [`eqlog_runtime::Unification`]. Function and predicate applications
//! are plain data, keyed by their own contents, so two calls with
//! identical parents and arguments collapse naturally.
//!
//! A [`StructureCat`] bundles an indexed family of structures together
//! with a forward-only set of morphisms between them. The entailed close
//! pass settles each structure in turn, pushing shared data forward along
//! outgoing morphisms, and then walks backward to pull type information
//! from codomains into domains.
//!
//! Grouping structures by rule, mapping AST nodes to structures and
//! tracking `semantic_el` provenance all live in [`crate::algebra`] and
//! [`crate::algebra::populate`], not here. This module has no AST
//! dependency by design.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use eqlog_runtime::Unification;

use crate::algebra::signature::{FuncId, PredId, Signature, TypeId};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ElId(pub(super) usize);

/// Index into a [`StructureCat`]'s flat arena of structures.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StructureId(pub usize);

/// A mathematical function on [`ElId`]s sending elements of a domain
/// structure to elements of a codomain structure. After
/// [`StructureCat::close`], keys are all roots of the domain's
/// unification and values are all roots of the codomain's.
pub type ElMap = BTreeMap<ElId, ElId>;

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
    /// Live elements, keyed by [`ElId`]. `None` means the element's type
    /// has not been determined yet. After [`Structure::close`] only
    /// equivalence class roots remain as keys.
    pub els: BTreeMap<ElId, Option<ConcreteType>>,
    pub pred_apps: BTreeSet<PredApp>,
    pub func_apps: BTreeMap<FuncApp, ElId>,
    /// Variable bindings that have entered scope in this structure, keyed
    /// by the variable's source name. Analogous to
    /// `var(Structure, ElName) -> El` in eqlog.eql. Within a single rule
    /// body distinct names always denote distinct bindings, so name-keying
    /// is equivalent to binding-id-keying.
    pub var_els: BTreeMap<String, ElId>,
    /// Elements introduced as ambient model instances by the rule's
    /// enclosing-model scopes, keyed by the model type. These elements
    /// have a fixed [`ConcreteType`] for the corresponding model type;
    /// they are never referenced by any surface term.
    pub ambient_model_els: BTreeMap<TypeId, ElId>,
    /// Equivalence relation on [`ElId`]s. New ElIds start out in their own
    /// class; [`Structure::close`] may merge classes under functionality.
    pub unification: Unification<ElId>,
    /// Equalities that have been declared (via [`Structure::equate`]) or
    /// derived internally (from functionality) but whose effects on the
    /// rest of the structure have not yet been drained. Always empty
    /// after [`Structure::close`] returns.
    pub(super) pending_equalities: Vec<(ElId, ElId)>,
    /// Pending [`Structure::impose_type`] assertions. Persists across
    /// `close` calls; canonicalised alongside `els`.
    pub(super) pending_type_impositions: Vec<(ElId, ConcreteType)>,
}

/// A parent-disagreement observation queued by
/// [`Structure::drain_equalities`] or [`Structure::impose_concrete_type`]
/// for re-evaluation once no further equates can fire. The two
/// [`ConcreteType`]s share a [`TypeId`] — only the parent lists are in
/// question. `el` is the equivalence-class root they were assigned to
/// at observation time; later resolution canonicalises through the
/// unification's current root.
#[derive(Clone, Debug, PartialEq, Eq)]
struct DeferredParentCheck {
    el: ElId,
    a: ConcreteType,
    b: ConcreteType,
}

impl Default for Structure {
    fn default() -> Self {
        Self {
            els: BTreeMap::new(),
            pred_apps: BTreeSet::new(),
            func_apps: BTreeMap::new(),
            var_els: BTreeMap::new(),
            ambient_model_els: BTreeMap::new(),
            unification: Unification::new(),
            pending_equalities: Vec::new(),
            pending_type_impositions: Vec::new(),
        }
    }
}

/// A type disagreement discovered during [`Structure::close`]: two
/// incompatible [`ConcreteType`]s got assigned to the equivalence class
/// rooted at `el`. Either `a.typ != b.typ`, or the [`TypeId`]s agree but
/// some parent of `a` falls in a different equivalence class than the
/// corresponding parent of `b`.
///
/// Parents inside `a` and `b` are not canonicalised; the caller compares
/// them through the [`Structure`]'s unification when it needs class
/// identity.
///
/// The caller is responsible for turning this into a user-facing
/// [`crate::error::CompileError`]; typically it looks up a term in
/// [`Structure::semantic_el`] whose element falls in `el`'s class (for
/// type mismatches) or in a differing parent's class (for parent
/// mismatches).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeConflict {
    pub el: ElId,
    pub a: ConcreteType,
    pub b: ConcreteType,
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

    /// Declares that `el` should have concrete type `ct`. Applied at the
    /// end of [`Structure::close`], after inferred typing has settled, so
    /// a disagreement surfaces as a [`TypeConflict`] with the inferred
    /// type in `a` and `ct` in `b`. Returns true iff a fresh entry was
    /// queued; idempotent on `(el, ct)` already enqueued.
    pub fn impose_type(&mut self, el: ElId, mut ct: ConcreteType) -> bool {
        // Canonicalise to the current roots before comparing. Existing
        // entries were canonicalised at the end of the previous `close`,
        // and no equates have been drained since (callers run during
        // populate), so this puts the new entry on the same footing.
        let el = self.unification.root_const(el);
        for p in ct.parents.iter_mut() {
            *p = self.unification.root_const(*p);
        }
        if self
            .pending_type_impositions
            .iter()
            .any(|(e, c)| *e == el && c == &ct)
        {
            return false;
        }
        self.pending_type_impositions.push((el, ct));
        true
    }

    /// Declares that `a` and `b` are equal. Just enqueues the pair on
    /// `pending_equalities`; the actual class merge and any cascading
    /// parent unifications happen during [`Structure::close`].
    ///
    /// Returns true iff `a` and `b` currently live in distinct equivalence
    /// classes, i.e. the eventual drain has work to do. Callers that drive
    /// an outer fixed point use this to avoid spinning on no-op equates.
    pub fn equate(&mut self, a: ElId, b: ElId) -> bool {
        let ra = self.unification.root(a);
        let rb = self.unification.root(b);
        self.pending_equalities.push((a, b));
        ra != rb
    }

    /// Looks up one ambient el per entry in `parent_types`. Panics if
    /// any type is missing from `ambient_model_els`.
    pub fn ambient_parents(&self, parent_types: &[TypeId]) -> Vec<ElId> {
        parent_types
            .iter()
            .map(|tid| {
                *self
                    .ambient_model_els
                    .get(tid)
                    .expect("ambient model el missing for type")
            })
            .collect()
    }

    /// Saturates the structure under functionality and signature-imposed
    /// typing, canonicalises every reference to its class root, and
    /// returns any [`TypeConflict`]s observed along the way.
    ///
    /// `changed` is true iff at least one inner pass did work, so callers
    /// driving an outer populate/close fixed point can stop when both
    /// report no change.
    pub fn close(&mut self, signature: &Signature) -> (bool, Vec<TypeConflict>) {
        let mut conflicts = Vec::new();
        let mut parent_checks: Vec<DeferredParentCheck> = Vec::new();
        let mut changed = false;
        loop {
            let drained = self.drain_equalities(&mut conflicts, &mut parent_checks);
            let func_changed = self.functionality();
            let type_changed = self.typing(signature, &mut conflicts, &mut parent_checks);
            if !drained && !func_changed && !type_changed {
                break;
            }
            changed = true;
        }
        // Apply pending type impositions after the equality/functionality/
        // typing fixed point has settled. This puts any inferred type into
        // the `existing` slot of `impose_concrete_type`, so a conflict with
        // an annotation surfaces as `a = inferred, b = annotated`.
        changed |= self.apply_pending_type_impositions(&mut conflicts, &mut parent_checks);
        self.resolve_parent_checks(parent_checks, &mut conflicts);
        self.canonicalise_refs();
        (changed, conflicts)
    }

    /// Imposes every `(el, ct)` queued via [`Structure::impose_type`] on the
    /// corresponding equivalence class, accumulating any
    /// [`TypeConflict`]s and parent-disagreement deferrals. The queue is
    /// not drained: the same impositions are reapplied on every `close`
    /// so a conflict that materialises only after a later equate still
    /// surfaces. Returns true iff any imposition recorded a fresh
    /// concrete type.
    fn apply_pending_type_impositions(
        &mut self,
        conflicts: &mut Vec<TypeConflict>,
        parent_checks: &mut Vec<DeferredParentCheck>,
    ) -> bool {
        let impositions = self.pending_type_impositions.clone();
        let mut changed = false;
        for (el, ct) in impositions {
            if self.impose_concrete_type(el, ct, conflicts, parent_checks) {
                changed = true;
            }
        }
        changed
    }

    /// Walks `parent_checks`. For each entry that still has a parent
    /// disagreement under the unification's current state, pushes a
    /// [`TypeConflict`]. Entries whose parents have since been put into
    /// the same class are silently discarded.
    fn resolve_parent_checks(
        &self,
        parent_checks: Vec<DeferredParentCheck>,
        conflicts: &mut Vec<TypeConflict>,
    ) {
        for check in parent_checks {
            if !parents_match(&self.unification, &check.a.parents, &check.b.parents) {
                conflicts.push(TypeConflict {
                    el: self.root(check.el),
                    a: check.a,
                    b: check.b,
                });
            }
        }
    }

    /// Drains `pending_equalities` down to empty, performing the union
    /// and merging `els` entries for each pair. Records a
    /// [`TypeConflict`] when the merged entries disagree on [`TypeId`].
    /// Parent disagreements are queued on `parent_checks` for
    /// re-evaluation after the close fixed point converges, since a
    /// still-pending equate may yet put the disagreeing parents into the
    /// same class. Returns true iff at least one class merge happened.
    fn drain_equalities(
        &mut self,
        conflicts: &mut Vec<TypeConflict>,
        parent_checks: &mut Vec<DeferredParentCheck>,
    ) -> bool {
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
                            el: keep,
                            a: k.clone(),
                            b: d,
                        });
                    } else if !parents_match(&self.unification, &k.parents, &d.parents) {
                        parent_checks.push(DeferredParentCheck {
                            el: keep,
                            a: k.clone(),
                            b: d,
                        });
                    }
                    Some(k)
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
    /// Domain types are imposed before codomain types so a conflicting
    /// el attributes the codomain as the new arrival. Returns true iff a
    /// fresh concrete type got recorded.
    fn typing(
        &mut self,
        signature: &Signature,
        conflicts: &mut Vec<TypeConflict>,
        parent_checks: &mut Vec<DeferredParentCheck>,
    ) -> bool {
        let mut changed = false;

        let apps: Vec<(FuncApp, ElId)> = self
            .func_apps
            .iter()
            .map(|(a, r)| (a.clone(), *r))
            .collect();
        for (app, _result) in &apps {
            let func_data = signature.func(app.func);
            for (i, &arg) in app.args.iter().enumerate() {
                let Some(&dom_tid) = func_data.domain.get(i) else {
                    break;
                };
                if let Some(ct) = concrete_type_at(signature, dom_tid, &app.parents) {
                    if self.impose_concrete_type(arg, ct, conflicts, parent_checks) {
                        changed = true;
                    }
                }
            }
        }

        let pred_apps: Vec<PredApp> = self.pred_apps.iter().cloned().collect();
        for app in &pred_apps {
            let pred_data = signature.pred(app.pred);
            for (i, &arg) in app.args.iter().enumerate() {
                let Some(&arity_tid) = pred_data.arity.get(i) else {
                    break;
                };
                if let Some(ct) = concrete_type_at(signature, arity_tid, &app.parents) {
                    if self.impose_concrete_type(arg, ct, conflicts, parent_checks) {
                        changed = true;
                    }
                }
            }
        }

        for (app, result) in apps {
            let func_data = signature.func(app.func);
            if let Some(ct) = concrete_type_at(signature, func_data.codomain, &app.parents) {
                if self.impose_concrete_type(result, ct, conflicts, parent_checks) {
                    changed = true;
                }
            }
        }

        changed
    }

    /// Asserts that `el`'s type is `ct`. Records a [`TypeConflict`] when
    /// the existing entry's [`TypeId`] differs. When the [`TypeId`]s
    /// match but some parent element falls in a different class than the
    /// corresponding entry in `ct.parents`, queues a
    /// [`DeferredParentCheck`] on `parent_checks` for re-evaluation
    /// after the surrounding fixed point converges, since a still-queued
    /// equate may yet put the disagreeing parents into the same class.
    /// Returns true iff a fresh concrete type was recorded.
    fn impose_concrete_type(
        &mut self,
        el: ElId,
        ct: ConcreteType,
        conflicts: &mut Vec<TypeConflict>,
        parent_checks: &mut Vec<DeferredParentCheck>,
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
                        el: root,
                        a: existing,
                        b: ct,
                    });
                } else if !parents_match(&self.unification, &existing.parents, &ct.parents) {
                    parent_checks.push(DeferredParentCheck {
                        el: root,
                        a: existing,
                        b: ct,
                    });
                }
                false
            }
        }
    }

    /// Final pass: rewrite every remaining reference (pred app parents and
    /// args, var-el values, [`ConcreteType`] parents) to the root of its
    /// current class, and drop non-root entries from `els`.
    fn canonicalise_refs(&mut self) {
        let old_pred_apps = mem::take(&mut self.pred_apps);
        for app in old_pred_apps {
            self.pred_apps.insert(PredApp {
                pred: app.pred,
                parents: app.parents.into_iter().map(|e| self.root(e)).collect(),
                args: app.args.into_iter().map(|e| self.root(e)).collect(),
            });
        }

        for v in self.var_els.values_mut() {
            *v = self.unification.root_const(*v);
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

        for (el, ct) in self.pending_type_impositions.iter_mut() {
            *el = self.unification.root_const(*el);
            for p in ct.parents.iter_mut() {
                *p = self.unification.root_const(*p);
            }
        }
    }

    fn root(&self, id: ElId) -> ElId {
        self.unification.root_const(id)
    }
}

/// A finite direct category of [`Structure`]s: a flat arena of structures
/// with a set of morphisms between them that always point forward in the
/// arena (the domain's [`StructureId`] is strictly smaller than the
/// codomain's).
///
/// Each morphism is stored as an [`ElMap`] on elements; the [`Structure`]
/// invariants (preserving `pred_apps`, `func_apps`, `var_els` and
/// `ambient_model_els` under the map) are maintained by
/// [`StructureCat::close`] rather than baked into the data structure.
#[derive(Clone, Debug, Default)]
pub struct StructureCat {
    pub structures: Vec<Structure>,
    /// Keyed by `(domain, codomain)`. `domain.0 < codomain.0` always.
    pub morphisms: BTreeMap<(StructureId, StructureId), ElMap>,
}

impl StructureCat {
    /// Appends `structure` and returns its fresh [`StructureId`].
    pub fn push(&mut self, structure: Structure) -> StructureId {
        let id = StructureId(self.structures.len());
        self.structures.push(structure);
        id
    }

    /// Registers a morphism from `src` to `tgt` with element map `map`.
    /// Panics if `src.0 >= tgt.0` or if a morphism with the same endpoints
    /// already exists.
    pub fn add_morphism(&mut self, src: StructureId, tgt: StructureId, map: ElMap) {
        assert!(
            src.0 < tgt.0,
            "morphisms must point forward: {src:?} -> {tgt:?}"
        );
        let prev = self.morphisms.insert((src, tgt), map);
        assert!(prev.is_none(), "duplicate morphism {src:?} -> {tgt:?}");
    }

    /// Closes every structure under functionality and typing and propagates
    /// shared data along the morphisms.
    ///
    /// Two passes:
    ///
    ///   - Forward: walk structures in arena order. Close each structure,
    ///     then push its `pred_apps`, `func_apps`, `var_els` and
    ///     `ambient_model_els` along every outgoing morphism, canonicalising
    ///     the [`ElMap`]'s keys under the now-settled domain unification and
    ///     enqueueing equalities on the codomain when two keys collapse to
    ///     the same root or when a pushed entry clashes with an existing
    ///     one in the codomain. The codomain is not re-closed eagerly; it
    ///     will be closed when its own iteration arrives.
    ///
    ///   - Backward: walk structures in reverse. For each outgoing morphism,
    ///     pull type information from the codomain back into the domain for
    ///     every mapped element whose [`ConcreteType`] parents are all
    ///     ambient model elements (so their preimages in the domain are
    ///     unambiguous — the domain's own ambient els of the same types).
    ///     Equality, predicate and function data are not propagated
    ///     backwards. Re-close the domain afterwards so any equalities
    ///     induced by newly imposed types settle. Because only type info
    ///     flows backwards — and only into the domain, whose forward
    ///     outputs have already been consumed — no second forward pass is
    ///     needed.
    ///
    /// After both passes a final canonicalisation rewrites every
    /// [`ElMap`]'s keys and values to their respective roots.
    ///
    /// Returns `(changed, conflicts)`. `conflicts` is every
    /// [`TypeConflict`] discovered, tagged with the [`StructureId`] of the
    /// structure in which it occurred, so callers can attribute diagnostics.
    /// `changed` is true iff at least one structure-level close, push or
    /// pull observed work, so an enclosing populate/close fixed point can
    /// stop when both report no change.
    pub fn close(&mut self, signature: &Signature) -> (bool, Vec<(StructureId, TypeConflict)>) {
        let mut conflicts: Vec<(StructureId, TypeConflict)> = Vec::new();
        let mut changed = false;
        let n = self.structures.len();

        for i in 0..n {
            let id = StructureId(i);
            let (c_changed, cs) = self.structures[i].close(signature);
            changed |= c_changed;
            for c in cs {
                conflicts.push((id, c));
            }
            changed |= self.push_forward(id);
        }

        for i in (0..n).rev() {
            let id = StructureId(i);
            changed |= self.pull_types_backward(id, &mut conflicts);
            let (c_changed, cs) = self.structures[i].close(signature);
            changed |= c_changed;
            for c in cs {
                conflicts.push((id, c));
            }
        }

        self.canonicalise_morphisms();
        (changed, conflicts)
    }

    /// Lists every outgoing morphism codomain for `src` in ascending order.
    fn outgoing(&self, src: StructureId) -> Vec<StructureId> {
        self.morphisms
            .keys()
            .filter_map(|&(a, b)| (a == src).then_some(b))
            .collect()
    }

    /// Pushes shared data from `src` along every outgoing morphism. Returns
    /// true iff at least one morphism observed any logical insertion or
    /// non-trivial equate.
    fn push_forward(&mut self, src: StructureId) -> bool {
        let mut changed = false;
        for tgt in self.outgoing(src) {
            changed |= self.push_morphism(src, tgt);
        }
        changed
    }

    /// Carries data from `src` into `tgt` along the `(src, tgt)` morphism.
    /// Rewrites the [`ElMap`]'s keys to their roots in `src`, enqueues
    /// equalities on `tgt` when two keys collapse, and inserts the images
    /// of `src`'s `pred_apps`, `func_apps`, `var_els` and
    /// `ambient_model_els` into `tgt`.
    ///
    /// Returns true iff a previously-absent entry was inserted into `tgt`,
    /// or an equate was enqueued on `tgt` whose pair lives in distinct
    /// equivalence classes. Idempotent re-runs that only re-canonicalise
    /// the morphism's keys report false.
    fn push_morphism(&mut self, src: StructureId, tgt: StructureId) -> bool {
        let StructureCat {
            structures,
            morphisms,
        } = self;
        let (left, right) = structures.split_at_mut(tgt.0);
        let src_st = &left[src.0];
        let tgt_st = &mut right[0];
        let map = morphisms
            .get_mut(&(src, tgt))
            .expect("morphism disappeared");

        let mut changed = false;

        let old = mem::take(map);
        for (k, v) in old {
            let root_k = src_st.unification.root_const(k);
            match map.entry(root_k) {
                Entry::Vacant(vac) => {
                    vac.insert(v);
                }
                Entry::Occupied(occ) => {
                    let existing = *occ.get();
                    if existing != v && tgt_st.equate(existing, v) {
                        changed = true;
                    }
                }
            }
        }

        let image = |e: ElId| -> ElId {
            *map.get(&src_st.unification.root_const(e))
                .expect("morphism not defined on element")
        };

        for pa in &src_st.pred_apps {
            changed |= tgt_st.pred_apps.insert(PredApp {
                pred: pa.pred,
                parents: pa.parents.iter().copied().map(image).collect(),
                args: pa.args.iter().copied().map(image).collect(),
            });
        }

        let src_func_apps: Vec<(FuncApp, ElId)> = src_st
            .func_apps
            .iter()
            .map(|(a, r)| (a.clone(), *r))
            .collect();
        for (fa, result) in src_func_apps {
            let mapped = FuncApp {
                func: fa.func,
                parents: fa.parents.iter().copied().map(image).collect(),
                args: fa.args.iter().copied().map(image).collect(),
            };
            let mapped_result = image(result);
            match tgt_st.func_apps.entry(mapped) {
                Entry::Vacant(vac) => {
                    vac.insert(mapped_result);
                    changed = true;
                }
                Entry::Occupied(occ) => {
                    let existing = *occ.get();
                    if existing != mapped_result {
                        changed |= tgt_st.equate(existing, mapped_result);
                    }
                }
            }
        }

        let src_var_els: Vec<(String, ElId)> = src_st
            .var_els
            .iter()
            .map(|(n, e)| (n.clone(), *e))
            .collect();
        for (name, el) in src_var_els {
            let mapped_el = image(el);
            match tgt_st.var_els.entry(name) {
                Entry::Vacant(vac) => {
                    vac.insert(mapped_el);
                    changed = true;
                }
                Entry::Occupied(occ) => {
                    let existing = *occ.get();
                    if existing != mapped_el {
                        changed |= tgt_st.equate(existing, mapped_el);
                    }
                }
            }
        }

        let src_ambient: Vec<(TypeId, ElId)> = src_st
            .ambient_model_els
            .iter()
            .map(|(t, e)| (*t, *e))
            .collect();
        for (typ, el) in src_ambient {
            let mapped_el = image(el);
            match tgt_st.ambient_model_els.entry(typ) {
                Entry::Vacant(vac) => {
                    vac.insert(mapped_el);
                    changed = true;
                }
                Entry::Occupied(occ) => {
                    let existing = *occ.get();
                    if existing != mapped_el {
                        changed |= tgt_st.equate(existing, mapped_el);
                    }
                }
            }
        }

        changed
    }

    /// For each outgoing morphism `(src, tgt)`, imposes on `src` the type
    /// of every mapped codomain element whose parents are all ambient
    /// model elements in `tgt`. The preimages of those parents in `src`
    /// are read off `src.ambient_model_els` by type. Returns true iff at
    /// least one such imposition recorded a fresh type or enqueued a
    /// parent equality on `src`.
    fn pull_types_backward(
        &mut self,
        src: StructureId,
        conflicts: &mut Vec<(StructureId, TypeConflict)>,
    ) -> bool {
        let mut changed = false;
        for tgt in self.outgoing(src) {
            changed |= self.pull_morphism_types(src, tgt, conflicts);
        }
        changed
    }

    fn pull_morphism_types(
        &mut self,
        src: StructureId,
        tgt: StructureId,
        conflicts: &mut Vec<(StructureId, TypeConflict)>,
    ) -> bool {
        let StructureCat {
            structures,
            morphisms,
        } = self;
        let (left, right) = structures.split_at_mut(tgt.0);
        let src_st = &mut left[src.0];
        let tgt_st = &right[0];
        let map = morphisms.get(&(src, tgt)).expect("morphism disappeared");

        let mut changed = false;

        // Index tgt's ambient els by root for quick type lookup.
        let tgt_ambient_by_root: BTreeMap<ElId, TypeId> = tgt_st
            .ambient_model_els
            .iter()
            .map(|(t, e)| (tgt_st.unification.root_const(*e), *t))
            .collect();

        for (&src_el, &tgt_el) in map.iter() {
            let tgt_root = tgt_st.unification.root_const(tgt_el);
            let Some(Some(ct)) = tgt_st.els.get(&tgt_root) else {
                continue;
            };

            let parent_types: Option<Vec<TypeId>> = ct
                .parents
                .iter()
                .map(|p| {
                    tgt_ambient_by_root
                        .get(&tgt_st.unification.root_const(*p))
                        .copied()
                })
                .collect();
            let Some(parent_types) = parent_types else {
                continue;
            };

            let new_parents: Option<Vec<ElId>> = parent_types
                .iter()
                .map(|t| src_st.ambient_model_els.get(t).copied())
                .collect();
            let Some(new_parents) = new_parents else {
                continue;
            };

            let new_ct = ConcreteType {
                typ: ct.typ,
                parents: new_parents,
            };
            let mut local_conflicts = Vec::new();
            let mut local_parent_checks = Vec::new();
            changed |= src_st.impose_concrete_type(
                src_el,
                new_ct,
                &mut local_conflicts,
                &mut local_parent_checks,
            );
            // No equates pending on `src_st` at this point (callers run
            // pull_types_backward only after a full close), so no later
            // unification can rescue a queued parent disagreement —
            // resolve immediately.
            src_st.resolve_parent_checks(local_parent_checks, &mut local_conflicts);
            for c in local_conflicts {
                conflicts.push((src, c));
            }
        }
        changed
    }

    /// Rewrites every [`ElMap`] so its keys are roots in the domain's
    /// unification and its values are roots in the codomain's. Collapses
    /// colliding keys by dropping duplicates — by the time this runs the
    /// values for those collisions have already been unified, so dropping
    /// is safe.
    fn canonicalise_morphisms(&mut self) {
        let keys: Vec<(StructureId, StructureId)> = self.morphisms.keys().copied().collect();
        for (src, tgt) in keys {
            let StructureCat {
                structures,
                morphisms,
            } = self;
            let src_st = &structures[src.0];
            let tgt_st = &structures[tgt.0];
            let map = morphisms.get_mut(&(src, tgt)).unwrap();
            let old = mem::take(map);
            for (k, v) in old {
                let root_k = src_st.unification.root_const(k);
                let root_v = tgt_st.unification.root_const(v);
                map.insert(root_k, root_v);
            }
        }
    }
}

/// Reports whether two parent lists agree class-by-class up to their shorter
/// length under `unification`. A length mismatch only happens for malformed
/// programs and is treated as a match (so the conflict, if any, originates
/// from the [`TypeId`] check the caller has already performed).
fn parents_match(unification: &Unification<ElId>, lhs: &[ElId], rhs: &[ElId]) -> bool {
    let n = lhs.len().min(rhs.len());
    for i in 0..n {
        if unification.root_const(lhs[i]) != unification.root_const(rhs[i]) {
            return false;
        }
    }
    true
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
