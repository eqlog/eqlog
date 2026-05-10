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
//! pass settles each structure in turn, pushing shared data and concrete
//! types forward along outgoing morphisms, and then walks backward to
//! pull missing type information from codomains into domains.
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
    /// Parent disagreements observed in an earlier close cycle. They are
    /// rechecked on later cycles because a later equality can still make
    /// the parent lists agree.
    deferred_parent_checks: Vec<DeferredParentCheck>,
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
    origin: TypeConflictOrigin,
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
            deferred_parent_checks: Vec::new(),
        }
    }
}

/// How a type conflict was first observed. Callers use this to tune
/// source attribution without losing the existing/new type ordering of
/// ordinary impositions.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TypeConflictOrigin {
    Equality,
    Imposition,
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
    pub origin: TypeConflictOrigin,
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
        let mut parent_checks: Vec<DeferredParentCheck> =
            mem::take(&mut self.deferred_parent_checks);
        let mut changed = false;
        loop {
            let drained = self.drain_equalities(&mut conflicts, &mut parent_checks);
            let func_changed = self.functionality();
            let type_changed = self.typing(signature, &mut conflicts, &mut parent_checks);
            let mor_app_changed =
                self.morphism_app_constraints(signature, &mut conflicts, &mut parent_checks);
            if !drained && !func_changed && !type_changed && !mor_app_changed {
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
        &mut self,
        parent_checks: Vec<DeferredParentCheck>,
        conflicts: &mut Vec<TypeConflict>,
    ) {
        let mut unresolved = Vec::new();
        for check in parent_checks {
            let check = self.canonical_parent_check(check);
            if !parents_match(&self.unification, &check.a.parents, &check.b.parents)
                && !unresolved.contains(&check)
            {
                conflicts.push(TypeConflict {
                    el: check.el,
                    a: check.a.clone(),
                    b: check.b.clone(),
                    origin: check.origin,
                });
                unresolved.push(check);
            }
        }
        self.deferred_parent_checks = unresolved;
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
            let lhs = self.root(a);
            let rhs = self.root(b);
            if lhs == rhs {
                continue;
            }
            changed = true;

            // Deterministic winner: smaller id stays root.
            let (keep, drop) = if lhs.0 <= rhs.0 {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            let lhs_ct = self.els.get(&lhs).cloned().flatten();
            let rhs_ct = self.els.get(&rhs).cloned().flatten();
            self.unification.union_roots_into(drop, keep);

            self.els.remove(&drop);
            self.els.remove(&keep);
            let merged = match (lhs_ct, rhs_ct) {
                (None, None) => None,
                (Some(x), None) | (None, Some(x)) => Some(x),
                (Some(lhs_ct), Some(rhs_ct)) => {
                    if lhs_ct.typ != rhs_ct.typ {
                        conflicts.push(TypeConflict {
                            el: keep,
                            a: lhs_ct.clone(),
                            b: rhs_ct,
                            origin: TypeConflictOrigin::Equality,
                        });
                    } else if !parents_match(&self.unification, &lhs_ct.parents, &rhs_ct.parents) {
                        parent_checks.push(DeferredParentCheck {
                            el: keep,
                            a: lhs_ct.clone(),
                            b: rhs_ct,
                            origin: TypeConflictOrigin::Equality,
                        });
                    }
                    Some(lhs_ct)
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
            for (i, &arg) in app.args.iter().enumerate() {
                if let Some(ct) = func_domain_type_at(signature, app, i) {
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
            if let Some(ct) = func_codomain_type_at(signature, &app) {
                if self.impose_concrete_type(result, ct, conflicts, parent_checks) {
                    changed = true;
                }
            }
        }

        changed
    }

    /// Enforces the dependent typing laws that are specific to generated
    /// morphism-application functions. A `mor_app<T>(f, x)` application is
    /// represented as an ordinary [`FuncApp`], but its argument and result
    /// types depend on the generated `dom(f)` and `cod(f)` projections:
    ///
    /// - if `x : d.T`, record `dom(f) = d`;
    /// - if `mor_app<T>(f, x) : c.T`, record `cod(f) = c`;
    /// - if either projection is known, impose the corresponding member type.
    fn morphism_app_constraints(
        &mut self,
        signature: &Signature,
        conflicts: &mut Vec<TypeConflict>,
        parent_checks: &mut Vec<DeferredParentCheck>,
    ) -> bool {
        let apps: Vec<(FuncApp, ElId)> = self
            .func_apps
            .iter()
            .map(|(a, r)| (a.clone(), *r))
            .collect();
        let mut changed = false;

        for (app, result) in apps {
            let Some(member_tid) = signature.type_for_mor_app_func(app.func) else {
                continue;
            };
            let Some(&parent_model_tid) = signature.type_(member_tid).parents.last() else {
                continue;
            };
            let Some(model_ids) = signature.ids_for_model_type(parent_model_tid) else {
                continue;
            };
            if app.args.len() != 2 {
                continue;
            }

            let mor_el = self.root(app.args[0]);
            let arg_el = self.root(app.args[1]);
            let result = self.root(result);
            let outer_parents: Vec<ElId> = app.parents.iter().map(|p| self.root(*p)).collect();

            let dom_app = FuncApp {
                func: model_ids.dom,
                parents: outer_parents.clone(),
                args: vec![mor_el],
            };
            let cod_app = FuncApp {
                func: model_ids.cod,
                parents: outer_parents.clone(),
                args: vec![mor_el],
            };

            if let Some(domain_el) = self.member_parent_from_type(arg_el, member_tid) {
                changed |= self.insert_func_app_or_equate(dom_app.clone(), domain_el);
            }
            if let Some(codomain_el) = self.member_parent_from_type(result, member_tid) {
                changed |= self.insert_func_app_or_equate(cod_app.clone(), codomain_el);
            }

            if let Some(&domain_el) = self.func_apps.get(&dom_app) {
                let mut parents = outer_parents.clone();
                parents.push(self.root(domain_el));
                if self.impose_concrete_type(
                    arg_el,
                    ConcreteType {
                        typ: member_tid,
                        parents,
                    },
                    conflicts,
                    parent_checks,
                ) {
                    changed = true;
                }
            }

            if let Some(&codomain_el) = self.func_apps.get(&cod_app) {
                let mut parents = outer_parents.clone();
                parents.push(self.root(codomain_el));
                if self.impose_concrete_type(
                    result,
                    ConcreteType {
                        typ: member_tid,
                        parents,
                    },
                    conflicts,
                    parent_checks,
                ) {
                    changed = true;
                }
            }
        }

        changed
    }

    /// Returns the innermost parent of `el` when it already has type
    /// `member_tid`.
    fn member_parent_from_type(&self, el: ElId, member_tid: TypeId) -> Option<ElId> {
        let ct = self.concrete_type_of(el)?;
        if ct.typ != member_tid {
            return None;
        }
        let member_parent = *ct.parents.last()?;
        Some(self.root(member_parent))
    }

    fn concrete_type_of(&self, el: ElId) -> Option<ConcreteType> {
        let root = self.root(el);
        let mut ct = self.els.get(&root)?.clone()?;
        for parent in &mut ct.parents {
            *parent = self.root(*parent);
        }
        Some(ct)
    }

    fn insert_func_app_or_equate(&mut self, app: FuncApp, result: ElId) -> bool {
        let canon_app = FuncApp {
            func: app.func,
            parents: app.parents.into_iter().map(|e| self.root(e)).collect(),
            args: app.args.into_iter().map(|e| self.root(e)).collect(),
        };
        let result = self.root(result);
        match self.func_apps.get(&canon_app).copied() {
            Some(existing) => existing != result && self.equate(existing, result),
            None => {
                self.func_apps.insert(canon_app, result);
                true
            }
        }
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
                        origin: TypeConflictOrigin::Imposition,
                    });
                } else if !parents_match(&self.unification, &existing.parents, &ct.parents) {
                    parent_checks.push(DeferredParentCheck {
                        el: root,
                        a: existing,
                        b: ct,
                        origin: TypeConflictOrigin::Imposition,
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

        let checks = mem::take(&mut self.deferred_parent_checks);
        self.deferred_parent_checks = checks
            .into_iter()
            .map(|check| self.canonical_parent_check(check))
            .collect();
    }

    fn canonical_parent_check(&self, mut check: DeferredParentCheck) -> DeferredParentCheck {
        check.el = self.root(check.el);
        for p in check.a.parents.iter_mut() {
            *p = self.root(*p);
        }
        for p in check.b.parents.iter_mut() {
            *p = self.root(*p);
        }
        check
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
/// invariants (preserving concrete types, `pred_apps`, `func_apps`,
/// `var_els` and `ambient_model_els` under the map) are maintained by
/// [`StructureCat::close`] rather than baked into the data structure.
///
/// `under_prods` is a separate registry of "wide pullback" relationships
/// among the structures. It does not own morphisms; the formal
/// `top -> meet` and `meet -> end_i` morphisms live in `morphisms`. The
/// registry is what tells [`StructureCat::close`] which structures are
/// meant to receive saturated facts (equalities, pred_apps, func_apps)
/// that hold in every `end_i`.
#[derive(Clone, Debug, Default)]
pub struct StructureCat {
    pub structures: Vec<Structure>,
    /// Keyed by `(domain, codomain)`. `domain.0 < codomain.0` always.
    pub morphisms: BTreeMap<(StructureId, StructureId), ElMap>,
    pub under_prods: Vec<UnderProd>,
}

/// A "product in the under-category over `top`": the universal structure
/// `meet` extending `top` and embedding into every `end_i`. This is the
/// after-structure of a `branch`/`match` statement: it captures the data
/// that holds no matter which branch was taken.
///
/// `top` is recorded for traceability only. The saturation pass driving
/// `meet` only consults `meet` and the `end_i`s; the `top -> meet`
/// morphism in [`StructureCat::morphisms`] is what keeps `top`'s data
/// flowing into `meet` via the ordinary forward push.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnderProd {
    pub top: StructureId,
    pub meet: StructureId,
    pub ends: Vec<StructureId>,
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

    /// Records a wide-pullback relationship among already-existing
    /// structures: `meet` is to be saturated by facts holding in every
    /// `end_i`. The caller is responsible for having allocated `top`,
    /// `meet` and the `end_i`s and for having registered the appropriate
    /// `top -> meet` and `meet -> end_i` morphisms in `morphisms`.
    pub fn add_under_prod(&mut self, top: StructureId, meet: StructureId, ends: Vec<StructureId>) {
        self.under_prods.push(UnderProd { top, meet, ends });
    }

    /// Closes every structure under functionality and typing and propagates
    /// shared data along the morphisms, iterating to a fixed point.
    ///
    /// Each cycle consists of:
    ///
    ///   - Forward: walk structures in arena order. Close each structure,
    ///     then push its concrete types, `pred_apps`, `func_apps`,
    ///     `var_els` and `ambient_model_els` along every outgoing morphism,
    ///     canonicalising
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
    ///     backwards by this step. Re-close the domain afterwards so any
    ///     equalities induced by newly imposed types settle.
    ///
    ///   - Under-prod saturation: for each registered [`UnderProd`], pull
    ///     equalities, pred_apps and func_apps that hold in every `end_i`
    ///     back into `meet`.
    ///
    /// The cycle repeats until none of the three steps reports any change.
    /// A final canonicalisation rewrites every [`ElMap`]'s keys and values
    /// to their respective roots.
    ///
    /// Returns `(changed, conflicts)`. `conflicts` is every
    /// [`TypeConflict`] discovered, tagged with the [`StructureId`] of the
    /// structure in which it occurred, so callers can attribute diagnostics.
    /// `changed` is true iff at least one cycle observed work, so an
    /// enclosing populate/close fixed point can stop when both report no
    /// change.
    pub fn close(&mut self, signature: &Signature) -> (bool, Vec<(StructureId, TypeConflict)>) {
        let mut conflicts: Vec<(StructureId, TypeConflict)> = Vec::new();
        let mut changed = false;
        let n = self.structures.len();

        loop {
            let mut cycle = false;

            for i in 0..n {
                let id = StructureId(i);
                let (c_changed, cs) = self.structures[i].close(signature);
                cycle |= c_changed;
                for c in cs {
                    conflicts.push((id, c));
                }
                cycle |= self.push_forward(id, &mut conflicts);
            }

            for i in (0..n).rev() {
                let id = StructureId(i);
                cycle |= self.pull_types_backward(id);
                let (c_changed, cs) = self.structures[i].close(signature);
                cycle |= c_changed;
                for c in cs {
                    conflicts.push((id, c));
                }
            }

            cycle |= self.saturate_under_prods();

            changed |= cycle;
            if !cycle {
                break;
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
    fn push_forward(
        &mut self,
        src: StructureId,
        conflicts: &mut Vec<(StructureId, TypeConflict)>,
    ) -> bool {
        let mut changed = false;
        for tgt in self.outgoing(src) {
            changed |= self.push_morphism(src, tgt, conflicts);
        }
        changed
    }

    /// Carries data from `src` into `tgt` along the `(src, tgt)` morphism.
    /// Rewrites the [`ElMap`]'s keys to their roots in `src` and its
    /// values to their roots in `tgt`, enqueues equalities on `tgt` when
    /// two keys collapse, and inserts the images of `src`'s concrete
    /// types, `pred_apps`, `func_apps`, `var_els` and `ambient_model_els`
    /// into `tgt`.
    ///
    /// Returns true iff a previously-absent entry was inserted into `tgt`,
    /// or an equate was enqueued on `tgt` whose pair lives in distinct
    /// equivalence classes. Idempotent re-runs that only re-canonicalise
    /// the morphism's keys and values report false.
    fn push_morphism(
        &mut self,
        src: StructureId,
        tgt: StructureId,
        conflicts: &mut Vec<(StructureId, TypeConflict)>,
    ) -> bool {
        let StructureCat {
            structures,
            morphisms,
            ..
        } = self;
        let (left, right) = structures.split_at_mut(tgt.0);
        let src_st = &left[src.0];
        let tgt_st = &mut right[0];
        let map = morphisms
            .get_mut(&(src, tgt))
            .expect("morphism disappeared");

        let mut changed = false;

        // Canonicalise both keys (under src's unification) and values
        // (under tgt's unification) so the entries seen below — and the
        // images derived from them — match `tgt`'s post-close form.
        // Without canonicalising values, repeated push calls would keep
        // inserting pred_app/func_app entries with stale element ids,
        // each time reporting `changed = true`.
        let old = mem::take(map);
        for (k, v) in old {
            let root_k = src_st.unification.root_const(k);
            let root_v = tgt_st.unification.root_const(v);
            match map.entry(root_k) {
                Entry::Vacant(vac) => {
                    vac.insert(root_v);
                }
                Entry::Occupied(occ) => {
                    let existing = *occ.get();
                    if existing != root_v && tgt_st.equate(existing, root_v) {
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

        let src_typed_els: Vec<(ElId, ConcreteType)> = src_st
            .els
            .iter()
            .filter_map(|(&e, ct)| ct.clone().map(|ct| (e, ct)))
            .collect();
        for (el, ct) in src_typed_els {
            let mapped_el = image(el);
            let mapped_ct = ConcreteType {
                typ: ct.typ,
                parents: ct.parents.iter().copied().map(image).collect(),
            };
            let mut local_conflicts = Vec::new();
            let mut local_parent_checks = Vec::new();
            changed |= tgt_st.impose_concrete_type(
                mapped_el,
                mapped_ct,
                &mut local_conflicts,
                &mut local_parent_checks,
            );
            tgt_st.deferred_parent_checks.extend(local_parent_checks);
            for c in local_conflicts {
                conflicts.push((tgt, c));
            }
        }

        changed
    }

    /// For each outgoing morphism `(src, tgt)`, reflects missing type
    /// information from mapped codomain elements whose parents are all
    /// ambient model elements in `tgt`. The preimages of those parents in
    /// `src` are read off `src.ambient_model_els` by type. Existing source
    /// types are left alone when they disagree; the downstream structure
    /// that witnessed the disagreement reports the conflict.
    fn pull_types_backward(&mut self, src: StructureId) -> bool {
        let mut changed = false;
        for tgt in self.outgoing(src) {
            changed |= self.pull_morphism_types(src, tgt);
        }
        changed
    }

    fn pull_morphism_types(&mut self, src: StructureId, tgt: StructureId) -> bool {
        let StructureCat {
            structures,
            morphisms,
            ..
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
            match src_st.concrete_type_of(src_el) {
                None => {
                    let mut local_conflicts = Vec::new();
                    let mut local_parent_checks = Vec::new();
                    changed |= src_st.impose_concrete_type(
                        src_el,
                        new_ct,
                        &mut local_conflicts,
                        &mut local_parent_checks,
                    );
                    debug_assert!(local_conflicts.is_empty());
                    debug_assert!(local_parent_checks.is_empty());
                }
                Some(existing)
                    if existing.typ == new_ct.typ
                        && parents_match(
                            &src_st.unification,
                            &existing.parents,
                            &new_ct.parents,
                        ) => {}
                Some(_) => {
                    continue;
                }
            }
        }
        changed
    }

    /// Saturates each registered [`UnderProd`]'s `meet` with equalities,
    /// pred_apps and func_apps that hold in every `end_i`. Each call
    /// processes every under-prod once; the surrounding fixed-point loop
    /// in [`Self::close`] re-runs as long as any cycle reports change.
    fn saturate_under_prods(&mut self) -> bool {
        let mut changed = false;
        let n = self.under_prods.len();
        for i in 0..n {
            let up = self.under_prods[i].clone();
            changed |= self.saturate_one_under_prod(&up);
        }
        changed
    }

    fn saturate_one_under_prod(&mut self, up: &UnderProd) -> bool {
        if up.ends.is_empty() {
            return false;
        }
        for &end_id in &up.ends {
            if !self.morphisms.contains_key(&(up.meet, end_id)) {
                return false;
            }
        }
        let mut changed = false;
        changed |= self.saturate_under_prod_equalities(up);
        changed |= self.saturate_under_prod_pred_apps(up);
        changed |= self.saturate_under_prod_func_apps(up);
        changed
    }

    /// Equates pairs of meet elements whose canonical images coincide in
    /// every `end_i`. Computed by partitioning meet's roots by the tuple
    /// `(root in end_1, root in end_2, …)` and equating within each
    /// resulting group.
    fn saturate_under_prod_equalities(&mut self, up: &UnderProd) -> bool {
        let groups = self.group_meet_roots_by_end_images(up);
        let mut changed = false;
        let meet_st = &mut self.structures[up.meet.0];
        for (_, members) in groups {
            if members.len() < 2 {
                continue;
            }
            let first = members[0];
            for &m in &members[1..] {
                if meet_st.equate(first, m) {
                    changed = true;
                }
            }
        }
        changed
    }

    fn group_meet_roots_by_end_images(&self, up: &UnderProd) -> BTreeMap<Vec<ElId>, Vec<ElId>> {
        let meet_st = &self.structures[up.meet.0];
        let mut groups: BTreeMap<Vec<ElId>, Vec<ElId>> = BTreeMap::new();
        for &m in meet_st.els.keys() {
            if meet_st.unification.root_const(m) != m {
                continue;
            }
            let mut key = Vec::with_capacity(up.ends.len());
            let mut ok = true;
            for &end_id in &up.ends {
                let map = self.morphisms.get(&(up.meet, end_id)).unwrap();
                let Some(&img) = map.get(&m) else {
                    ok = false;
                    break;
                };
                key.push(self.structures[end_id.0].unification.root_const(img));
            }
            if ok {
                groups.entry(key).or_default().push(m);
            }
        }
        groups
    }

    /// Inserts into `meet` every pred_app of `end_0` that translates back
    /// through the projection and is matched in every other end. When
    /// several meet roots project to the same `end_0` root,
    /// [`Self::invert_projection`] keeps only the smallest, so a few
    /// pred_apps may go unsaturated; nothing wrong is ever added.
    fn saturate_under_prod_pred_apps(&mut self, up: &UnderProd) -> bool {
        let end_0 = up.ends[0];
        let inv = self.invert_projection(up.meet, end_0);
        let candidates: Vec<PredApp> = self.structures[end_0.0].pred_apps.iter().cloned().collect();

        let mut to_insert: Vec<PredApp> = Vec::new();
        for pa in &candidates {
            let Some(meet_parents) = self.preimage_seq(end_0, &inv, &pa.parents) else {
                continue;
            };
            let Some(meet_args) = self.preimage_seq(end_0, &inv, &pa.args) else {
                continue;
            };

            let mut all_ends_have = true;
            for &end_j in &up.ends[1..] {
                let Some(translated_parents) = self.project_seq(up.meet, end_j, &meet_parents)
                else {
                    all_ends_have = false;
                    break;
                };
                let Some(translated_args) = self.project_seq(up.meet, end_j, &meet_args) else {
                    all_ends_have = false;
                    break;
                };
                let candidate = PredApp {
                    pred: pa.pred,
                    parents: translated_parents,
                    args: translated_args,
                };
                if !self.structures[end_j.0].pred_apps.contains(&candidate) {
                    all_ends_have = false;
                    break;
                }
            }

            if all_ends_have {
                to_insert.push(PredApp {
                    pred: pa.pred,
                    parents: meet_parents,
                    args: meet_args,
                });
            }
        }

        let mut changed = false;
        let meet_st = &mut self.structures[up.meet.0];
        for pa in to_insert {
            let canon = PredApp {
                pred: pa.pred,
                parents: pa
                    .parents
                    .iter()
                    .map(|e| meet_st.unification.root_const(*e))
                    .collect(),
                args: pa
                    .args
                    .iter()
                    .map(|e| meet_st.unification.root_const(*e))
                    .collect(),
            };
            if meet_st.pred_apps.insert(canon) {
                changed = true;
            }
        }
        changed
    }

    /// Inserts into `meet` every func_app of `end_0` that translates back
    /// through the projection and matches in every other end. When the
    /// translated key has no result yet in `meet`, allocates a fresh one
    /// and extends each `meet -> end_j` projection with the freshly
    /// allocated element pointing at the corresponding end's result.
    fn saturate_under_prod_func_apps(&mut self, up: &UnderProd) -> bool {
        let end_0 = up.ends[0];
        let inv = self.invert_projection(up.meet, end_0);
        let candidates: Vec<(FuncApp, ElId)> = self.structures[end_0.0]
            .func_apps
            .iter()
            .map(|(a, r)| (a.clone(), *r))
            .collect();

        let mut to_add: Vec<(FuncApp, Vec<ElId>)> = Vec::new();
        for (fa, r0) in &candidates {
            let Some(meet_parents) = self.preimage_seq(end_0, &inv, &fa.parents) else {
                continue;
            };
            let Some(meet_args) = self.preimage_seq(end_0, &inv, &fa.args) else {
                continue;
            };

            let mut end_results: Vec<ElId> = Vec::with_capacity(up.ends.len());
            end_results.push(self.structures[end_0.0].unification.root_const(*r0));

            let mut ok = true;
            for &end_j in &up.ends[1..] {
                let Some(translated_parents) = self.project_seq(up.meet, end_j, &meet_parents)
                else {
                    ok = false;
                    break;
                };
                let Some(translated_args) = self.project_seq(up.meet, end_j, &meet_args) else {
                    ok = false;
                    break;
                };
                let candidate = FuncApp {
                    func: fa.func,
                    parents: translated_parents,
                    args: translated_args,
                };
                match self.structures[end_j.0].func_apps.get(&candidate) {
                    Some(&r) => {
                        end_results.push(self.structures[end_j.0].unification.root_const(r));
                    }
                    None => {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                to_add.push((
                    FuncApp {
                        func: fa.func,
                        parents: meet_parents,
                        args: meet_args,
                    },
                    end_results,
                ));
            }
        }

        let mut changed = false;
        for (meet_app, end_results) in to_add {
            let canon_app = {
                let meet_st = &self.structures[up.meet.0];
                FuncApp {
                    func: meet_app.func,
                    parents: meet_app
                        .parents
                        .iter()
                        .map(|e| meet_st.unification.root_const(*e))
                        .collect(),
                    args: meet_app
                        .args
                        .iter()
                        .map(|e| meet_st.unification.root_const(*e))
                        .collect(),
                }
            };
            if self.structures[up.meet.0]
                .func_apps
                .contains_key(&canon_app)
            {
                continue;
            }
            let r = self.structures[up.meet.0].push_el();
            self.structures[up.meet.0].func_apps.insert(canon_app, r);
            changed = true;
            for (j, &end_id) in up.ends.iter().enumerate() {
                let map = self
                    .morphisms
                    .get_mut(&(up.meet, end_id))
                    .expect("projection missing");
                map.insert(r, end_results[j]);
            }
        }
        changed
    }

    /// Inverts a `meet -> end` projection: each end-root maps to the
    /// smallest meet-root that projects to it. Multi-preimage entries
    /// keep only the smallest meet-root, so saturations that would have
    /// required a different preimage are silently skipped — soundness is
    /// preserved (we only add facts that the projection witnesses).
    fn invert_projection(&self, meet: StructureId, end: StructureId) -> BTreeMap<ElId, ElId> {
        let map = self
            .morphisms
            .get(&(meet, end))
            .expect("projection missing");
        let meet_st = &self.structures[meet.0];
        let end_st = &self.structures[end.0];
        let mut inv: BTreeMap<ElId, ElId> = BTreeMap::new();
        for (&m, &e) in map {
            let canon_m = meet_st.unification.root_const(m);
            let canon_e = end_st.unification.root_const(e);
            inv.entry(canon_e)
                .and_modify(|cur| {
                    if canon_m < *cur {
                        *cur = canon_m;
                    }
                })
                .or_insert(canon_m);
        }
        inv
    }

    /// Translates a sequence of end-side elements back to meet-side
    /// elements through `inv`. Returns `None` if any element has no
    /// preimage.
    fn preimage_seq(
        &self,
        end: StructureId,
        inv: &BTreeMap<ElId, ElId>,
        xs: &[ElId],
    ) -> Option<Vec<ElId>> {
        let end_st = &self.structures[end.0];
        xs.iter()
            .map(|e| inv.get(&end_st.unification.root_const(*e)).copied())
            .collect()
    }

    /// Projects a sequence of meet-side elements forward through the
    /// `meet -> end` projection. Returns `None` if any element has no
    /// image in the projection map.
    fn project_seq(&self, meet: StructureId, end: StructureId, xs: &[ElId]) -> Option<Vec<ElId>> {
        let map = self.morphisms.get(&(meet, end))?;
        let meet_st = &self.structures[meet.0];
        let end_st = &self.structures[end.0];
        xs.iter()
            .map(|m| {
                let canon_m = meet_st.unification.root_const(*m);
                let img = map.get(&canon_m).copied()?;
                Some(end_st.unification.root_const(img))
            })
            .collect()
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
                ..
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

/// Materialises the ordinary domain type of `app.args[index]`.
///
/// Generated `mor_app<T>` functions are not ordinary in their second
/// argument: its type is `dom(f).T`, depending on the first argument.
/// [`Structure::morphism_app_constraints`] handles that case explicitly.
fn func_domain_type_at(signature: &Signature, app: &FuncApp, index: usize) -> Option<ConcreteType> {
    if signature.type_for_mor_app_func(app.func).is_some() && index > 0 {
        return None;
    }
    let tid = *signature.func(app.func).domain.get(index)?;
    concrete_type_at(signature, tid, &app.parents)
}

/// Materialises the ordinary codomain type of `app`.
///
/// Generated `mor_app<T>` functions are not ordinary in their result type:
/// the result is `cod(f).T`, depending on the first argument.
/// [`Structure::morphism_app_constraints`] handles that case explicitly.
fn func_codomain_type_at(signature: &Signature, app: &FuncApp) -> Option<ConcreteType> {
    if signature.type_for_mor_app_func(app.func).is_some() {
        return None;
    }
    concrete_type_at(signature, signature.func(app.func).codomain, &app.parents)
}

/// Materialises the [`ConcreteType`] a given [`TypeId`] has in a relation
/// application whose enclosing-model elements are `parents`. Returns `None`
/// when those parents do not instantiate the type's full parent chain.
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
