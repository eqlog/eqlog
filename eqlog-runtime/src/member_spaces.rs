use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use crate::wbtree::map::WBTreeMap;
use crate::wbtree::set::WBTreeSet;
use crate::Unification;

#[derive(Clone, Copy)]
struct Parent {
    origin: u32,
    rank: u32,
}

#[derive(Clone)]
struct Partition {
    parents: WBTreeMap<Parent>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemberMerge {
    pub loser: u32,
    pub winner: u32,
}

pub struct MemberRefresh {
    pub source: MemberSnapshot,
    pub merges: Vec<MemberMerge>,
}

impl Partition {
    fn new() -> Self {
        Self {
            parents: WBTreeMap::new(),
        }
    }

    fn root(&self, mut origin: u32) -> u32 {
        while let Some(parent) = self.parents.get(&origin) {
            if parent.origin == origin {
                break;
            }
            origin = parent.origin;
        }
        origin
    }

    fn equate(&mut self, lhs: u32, rhs: u32) -> Option<MemberMerge> {
        let mut lhs = self.root(lhs);
        let mut rhs = self.root(rhs);
        if lhs == rhs {
            return None;
        }
        let mut left_rank = self.parents.get(&lhs).map_or(0, |parent| parent.rank);
        let mut right_rank = self.parents.get(&rhs).map_or(0, |parent| parent.rank);
        if left_rank < right_rank {
            std::mem::swap(&mut lhs, &mut rhs);
            std::mem::swap(&mut left_rank, &mut right_rank);
        }
        self.parents.insert(
            rhs,
            Parent {
                origin: lhs,
                rank: right_rank,
            },
        );
        if left_rank == right_rank {
            self.parents.insert(
                lhs,
                Parent {
                    origin: lhs,
                    rank: left_rank + 1,
                },
            );
        }
        Some(MemberMerge {
            loser: rhs,
            winner: lhs,
        })
    }
}

/// Reserved coordinates can include holes belonging to unrelated owners.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemberBlock {
    pub owner: u32,
    pub first_origin: u32,
    pub first_handle: u32,
    pub len: u64,
}

impl MemberBlock {
    fn origin(self, handle: u32) -> Option<u32> {
        let offset = handle.checked_sub(self.first_handle)?;
        (u64::from(offset) < self.len).then(|| self.first_origin + offset)
    }

    fn handle(self, origin: u32) -> Option<u32> {
        let offset = origin.checked_sub(self.first_origin)?;
        (u64::from(offset) < self.len).then(|| self.first_handle + offset)
    }
}

/// A persistent owner-local domain, quotient, and global handle interpretation.
///
/// Cloning a snapshot shares tree roots. Later allocation, refresh, and equality
/// cannot change either its membership or its representatives.
#[derive(Clone)]
pub struct MemberSnapshot {
    owner: u32,
    domain: WBTreeSet,
    canonical_domain: WBTreeSet,
    partition: Partition,
    witnesses: WBTreeMap<u64>,
    by_origin: WBTreeMap<MemberBlock>,
    by_handle: WBTreeMap<MemberBlock>,
    extent: u64,
    revision: u64,
}

impl MemberSnapshot {
    fn new(owner: u32) -> Self {
        Self {
            owner,
            domain: WBTreeSet::new(),
            canonical_domain: WBTreeSet::new(),
            partition: Partition::new(),
            witnesses: WBTreeMap::new(),
            by_origin: WBTreeMap::new(),
            by_handle: WBTreeMap::new(),
            extent: 0,
            revision: 0,
        }
    }

    pub fn owner(&self) -> u32 {
        self.owner
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn domain(&self) -> &WBTreeSet {
        &self.domain
    }

    pub fn canonical_domain(&self) -> &WBTreeSet {
        &self.canonical_domain
    }

    pub fn root_origin(&self, origin: u32) -> Option<u32> {
        self.domain
            .contains(&origin)
            .then(|| self.partition.root(origin))
    }

    pub fn origin(&self, handle: u32) -> Option<u32> {
        let (_, block) = self.by_handle.floor_entry(handle)?;
        let origin = block.origin(handle)?;
        self.domain.contains(&origin).then_some(origin)
    }

    pub fn handle(&self, origin: u32) -> Option<u32> {
        if !self.domain.contains(&origin) {
            return None;
        }
        self.by_origin.floor_entry(origin)?.1.handle(origin)
    }

    pub fn contains(&self, handle: u32) -> bool {
        self.origin(handle).is_some()
    }

    pub fn root(&self, handle: u32) -> Option<u32> {
        self.handle(self.partition.root(self.origin(handle)?))
    }

    /// Includes noncanonical handles, without allocating an enumeration buffer.
    pub fn members(&self) -> impl Iterator<Item = u32> + '_ {
        self.domain
            .iter()
            .map(|origin| self.handle(origin).expect("members have reserved handles"))
    }

    /// Enumerating the semantic domain is proportional to its expanded size.
    pub fn iter(&self) -> impl Iterator<Item = u32> + '_ {
        self.canonical_domain
            .iter()
            .map(|origin| self.handle(origin).expect("roots have reserved handles"))
    }

    pub fn blocks(&self) -> impl Iterator<Item = MemberBlock> + '_ {
        self.by_origin.iter().map(|(_, block)| *block)
    }

    pub fn shares_domain_with(&self, other: &Self) -> bool {
        self.domain.shares_root(&other.domain)
    }

    pub fn shares_partition_with(&self, other: &Self) -> bool {
        self.partition.parents.shares_root(&other.partition.parents)
    }
}

struct Inheritance {
    source: u32,
    revision: u64,
    domain: WBTreeSet,
}

/// Positional access keeps a batched proof linear in the number of inputs.
pub struct MemberInheritedInputs<'a> {
    primary: Option<&'a Inheritance>,
    additional: &'a [Inheritance],
}

impl<'a> MemberInheritedInputs<'a> {
    pub fn get(&self, position: usize) -> Option<(u32, u64, &'a WBTreeSet)> {
        let input = if position == 0 {
            self.primary?
        } else {
            self.additional.get(position - 1)?
        };
        Some((input.source, input.revision, &input.domain))
    }
}

#[derive(Clone)]
struct SharedMembers {
    domain: WBTreeSet,
    witnesses: WBTreeMap<u64>,
    extent: u64,
}

/// Prepared separately so every member type can prove its images before any
/// type installs them. A plan is valid only while its participating snapshots
/// remain unchanged.
pub struct SharedInheritance {
    identity: Rc<()>,
    sources: Vec<u32>,
    target: u32,
    target_revision: u64,
    inputs: Vec<(u32, u64)>,
    members: SharedMembers,
}

struct MemberSpace {
    snapshot: MemberSnapshot,
    local_domain: WBTreeSet,
    local_equations: Vec<(u32, u32)>,
    local_merges: Vec<MemberMerge>,
    local_witnesses: WBTreeMap<u64>,
    inherited: Option<Inheritance>,
    inherited_witnesses: WBTreeMap<u64>,
    additional: Vec<Inheritance>,
    shared_members: Option<Box<SharedMembers>>,
    component: u32,
    children: WBTreeSet,
}

/// Storage counts distinguish reserved numeric IDs from allocated member data.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemberSpaceStats {
    pub owners: usize,
    pub owned_origins: u64,
    pub handle_blocks: usize,
    pub reserved_handles: u64,
    pub local_equations: usize,
    pub replayed_equations: u64,
}

/// Compact total inheritance with shared, proved intersections at DAG merges.
///
/// The explicit partial-map evaluator does not use this opt-in representation.
/// Refresh shares the source domain and union-by-rank partition, then reapplies
/// this owner's local members and equations. Thus refresh costs depend on local
/// history as well as logarithmic tree updates; they are not constant in the
/// number of local waves. A partition lookup uses at most logarithmically many
/// persistent tree lookups. Virtual handle reservations still consume the u32
/// address space, including holes, without allocating one entry per handle.
/// Additional sources require equal witness tokens on overlapping origins and
/// empty partitions. The evaluator materializes unsupported quotients before
/// mutation; unrelated paths never acquire equality merely from shared origins.
pub struct MemberSpaces {
    identity: Rc<()>,
    owners: BTreeMap<u32, MemberSpace>,
    blocks: BTreeMap<u32, MemberBlock>,
    components: Unification<u32>,
    next_origin: u64,
    next_handle: u64,
    adoption_bound: u64,
    owned_origins: u64,
    replayed_equations: u64,
    next_witness: u64,
    multiple_sources: bool,
}

impl Default for MemberSpaces {
    fn default() -> Self {
        Self::new()
    }
}

impl MemberSpaces {
    pub fn new() -> Self {
        Self::with_handle_bound(0)
    }

    /// Existing handles below `bound` can be adopted before enabling inheritance.
    /// They remain valid aliases, while canonical handles use fresh namespaces.
    pub fn with_handle_bound(bound: u64) -> Self {
        assert!(
            bound <= u64::from(u32::MAX) + 1,
            "invalid member handle bound"
        );
        Self {
            identity: Rc::new(()),
            owners: BTreeMap::new(),
            blocks: BTreeMap::new(),
            components: Unification::new(),
            next_origin: bound,
            next_handle: bound,
            adoption_bound: bound,
            owned_origins: 0,
            replayed_equations: 0,
            next_witness: 0,
            multiple_sources: false,
        }
    }

    /// Adopting retains callers' handles without disrupting arithmetic maps.
    /// Canonical representatives can change when the compact path is enabled.
    pub fn adopt(&mut self, owner: u32, handle: u32) -> u32 {
        assert!(
            u64::from(handle) < self.adoption_bound,
            "handle is not reserved for adoption"
        );
        assert!(self.has_owner(owner), "unknown owner");
        assert!(
            !self.blocks.contains_key(&handle),
            "handle was already adopted"
        );
        assert!(
            self.owners[&owner].inherited.is_none(),
            "adopt before installing inheritance"
        );
        let alias = MemberBlock {
            owner,
            first_origin: handle,
            first_handle: handle,
            len: 1,
        };
        self.reserve(owner, u64::from(handle) + 1);
        self.blocks.insert(handle, alias);
        let space = self.owners.get_mut(&owner).unwrap();
        space.snapshot.by_handle.insert(handle, alias);
        space.snapshot.domain.insert(handle);
        space.snapshot.canonical_domain.insert(handle);
        space.local_domain.insert(handle);
        space.snapshot.revision += 1;
        self.owned_origins += 1;
        space.snapshot.handle(handle).unwrap()
    }

    pub fn create_owner(&mut self, owner: u32) {
        assert!(!self.owners.contains_key(&owner), "owner already exists");
        let component = u32::try_from(self.components.len()).expect("too many owners");
        self.components.increase_size_to(self.components.len() + 1);
        self.owners.insert(
            owner,
            MemberSpace {
                snapshot: MemberSnapshot::new(owner),
                local_domain: WBTreeSet::new(),
                local_equations: Vec::new(),
                local_merges: Vec::new(),
                local_witnesses: WBTreeMap::new(),
                inherited: None,
                inherited_witnesses: WBTreeMap::new(),
                additional: Vec::new(),
                shared_members: None,
                component,
                children: WBTreeSet::new(),
            },
        );
    }

    pub fn has_owner(&self, owner: u32) -> bool {
        self.owners.contains_key(&owner)
    }

    pub fn owners(&self) -> impl Iterator<Item = u32> + '_ {
        self.owners.keys().copied()
    }

    pub fn handle_bound(&self) -> u64 {
        self.next_handle
    }

    pub fn canonical_handles(&self) -> impl Iterator<Item = u32> + '_ {
        self.owners.values().flat_map(|space| space.snapshot.iter())
    }

    /// Dynamic export explicitly pays for the complete numeric handle space.
    pub fn export_equalities(&self) -> Unification<u32> {
        let mut equalities = Unification::new();
        equalities.increase_size_to(usize::try_from(self.next_handle).unwrap());
        for space in self.owners.values() {
            for member in space.snapshot.members() {
                let root = space.snapshot.root(member).unwrap();
                equalities.union_roots_into(member, root);
            }
        }
        for alias in 0..self.adoption_bound {
            let alias = u32::try_from(alias).unwrap();
            if let Some(root) = self.root(alias) {
                equalities.union_roots_into(alias, root);
            }
        }
        let members = self
            .owners
            .values()
            .flat_map(|space| space.snapshot.members());
        let aliases = (0..self.adoption_bound)
            .map(|alias| u32::try_from(alias).unwrap())
            .filter(|&alias| self.owner(alias).is_some());
        equalities.restrict_to(members.chain(aliases));
        equalities
    }

    pub fn source(&self, owner: u32) -> Option<u32> {
        self.owners
            .get(&owner)?
            .inherited
            .as_ref()
            .map(|inherited| inherited.source)
    }

    /// A source can grow without changing relation rows, so matching baselines
    /// also need the member snapshot revision last adopted by this owner.
    pub fn source_revision(&self, owner: u32) -> Option<u64> {
        self.owners
            .get(&owner)?
            .inherited
            .as_ref()
            .map(|inherited| inherited.revision)
    }

    /// These domains and revisions describe adopted inputs, including stale
    /// snapshots when a source has advanced without reaching this owner.
    pub fn inherited_inputs(&self, owner: u32) -> Option<MemberInheritedInputs<'_>> {
        let space = self.owners.get(&owner)?;
        Some(MemberInheritedInputs {
            primary: space.inherited.as_ref(),
            additional: &space.additional,
        })
    }

    /// A witness identifies one fact whose invariant key determines this member.
    /// Copying its token proves equality between images of that fact, without
    /// assuming that unrelated paths through a model graph commute.
    pub fn witness(&mut self, owner: u32, origin: u32) {
        let space = self.owners.get_mut(&owner).expect("unknown owner");
        assert!(space.snapshot.domain.contains(&origin), "unknown origin");
        if space.snapshot.witnesses.get(&origin).is_some() {
            return;
        }
        let token = self.next_witness;
        self.next_witness = token.checked_add(1).expect("witness space exhausted");
        space.local_witnesses.insert(origin, token);
        space.snapshot.witnesses.insert(origin, token);
        space.snapshot.revision += 1;
    }

    pub fn has_multiple_sources(&self) -> bool {
        self.multiple_sources
    }

    /// Pending edges participate in cycle checks before their images exist.
    pub fn register_edge(&mut self, source: u32, target: u32) {
        assert!(self.has_owner(source), "unknown source owner");
        assert!(self.has_owner(target), "unknown target owner");
        if self.owners[&source].children.contains(&target) {
            return;
        }
        let source_component = self.components.root(self.owners[&source].component);
        let target_component = self.components.root(self.owners[&target].component);
        if source_component == target_component {
            assert_ne!(source, target, "cyclic member inheritance");
            let mut pending: Vec<_> = self.owners[&target].children.iter().collect();
            let mut visited = BTreeSet::new();
            while let Some(owner) = pending.pop() {
                assert_ne!(owner, source, "cyclic member inheritance");
                if visited.insert(owner) {
                    pending.extend(self.owners[&owner].children.iter());
                }
            }
        } else {
            self.components
                .union_roots_into(target_component, source_component);
        }
        self.owners
            .get_mut(&source)
            .unwrap()
            .children
            .insert(target);
    }

    fn inputs_current(&self, space: &MemberSpace) -> bool {
        let Some(inherited) = &space.inherited else {
            return false;
        };
        inherited.revision == self.owners[&inherited.source].snapshot.revision
            && space
                .additional
                .iter()
                .all(|input| input.revision == self.owners[&input.source].snapshot.revision)
    }

    fn shared_inputs(&self, target: u32, additional: &[u32]) -> Option<SharedMembers> {
        let space = &self.owners[&target];
        let source = space.inherited.as_ref()?.source;
        let source = &self.owners[&source].snapshot;
        if !source.partition.parents.is_empty() || !space.local_equations.is_empty() {
            return None;
        }
        // Local proofs cannot establish equality between two incoming images.
        // Only the previously proved incoming aggregate can extend a proof.
        let cached = space
            .shared_members
            .as_deref()
            .filter(|_| self.inputs_current(space));
        let mut result = if let Some(cached) = cached {
            cached.clone()
        } else {
            SharedMembers {
                domain: source.domain.clone(),
                witnesses: source.witnesses.clone(),
                extent: source.extent,
            }
        };
        let sources = space
            .additional
            .iter()
            .skip(if cached.is_some() {
                space.additional.len()
            } else {
                0
            })
            .map(|input| input.source)
            .chain(additional.iter().copied());
        for source in sources {
            let next = &self.owners[&source].snapshot;
            if !next.partition.parents.is_empty() {
                return None;
            }
            let overlap = result.domain.intersection(&next.domain);
            let proved = result.witnesses.intersection_shared(
                &next.witnesses,
                |_, left, right| (left == right).then_some(*left),
                |left, right| left == right,
            );
            if overlap.len() != proved.len() {
                return None;
            }
            result.domain = result.domain.union(&next.domain);
            result.witnesses = result
                .witnesses
                .union_shared(&next.witnesses, |_, left, _| left);
            result.extent = result.extent.max(next.extent);
        }
        Some(result)
    }

    /// Unsupported overlap must be materialized before changing any snapshot.
    pub fn can_share_inheritance(&self, source: u32, target: u32) -> bool {
        self.shared_inputs(target, &[source]).is_some()
    }

    pub fn prepare_shared_inheritance(
        &self,
        source: u32,
        target: u32,
    ) -> Option<SharedInheritance> {
        self.prepare_shared_inheritance_many(&[source], target)
    }

    /// Prove the complete extension before any incoming edge changes the target.
    /// Existing sources without an extension use the ordinary refresh path.
    pub fn prepare_shared_inheritance_many(
        &self,
        sources: &[u32],
        target: u32,
    ) -> Option<SharedInheritance> {
        if sources.is_empty() {
            return None;
        }
        let members = self.shared_inputs(target, sources)?;
        let space = &self.owners[&target];
        let inputs = std::iter::once(space.inherited.as_ref()?.source)
            .chain(space.additional.iter().map(|input| input.source))
            .chain(sources.iter().copied())
            .map(|source| (source, self.owners[&source].snapshot.revision))
            .collect();
        Some(SharedInheritance {
            identity: self.identity.clone(),
            sources: sources.to_vec(),
            target,
            target_revision: space.snapshot.revision,
            inputs,
            members,
        })
    }

    pub fn can_refresh(&self, owner: u32) -> bool {
        let space = &self.owners[&owner];
        if space.additional.is_empty() {
            return true;
        }
        // Source revisions retain the overlap proof, but target equations still
        // require materialization even when every source is unchanged.
        if space.local_equations.is_empty() && self.inputs_current(space) {
            return true;
        }
        self.shared_inputs(owner, &[]).is_some()
    }

    pub fn inherit_shared_members(&mut self, source: u32, target: u32) -> bool {
        let prepared = self
            .prepare_shared_inheritance(source, target)
            .expect("unproved shared images");
        self.install_shared_inheritance(prepared)
    }

    pub fn install_shared_inheritance(&mut self, prepared: SharedInheritance) -> bool {
        assert!(
            Rc::ptr_eq(&self.identity, &prepared.identity),
            "shared inheritance proof belongs to another member space"
        );
        let SharedInheritance {
            identity: _,
            sources,
            target,
            target_revision,
            inputs,
            members,
        } = prepared;
        let space = &self.owners[&target];
        assert_eq!(
            space.snapshot.revision, target_revision,
            "stale shared inheritance target"
        );
        assert!(
            std::iter::once(space.inherited.as_ref().unwrap().source)
                .chain(space.additional.iter().map(|input| input.source))
                .chain(sources.iter().copied())
                .eq(inputs.iter().map(|&(source, _)| source)),
            "stale shared inheritance inputs"
        );
        for (source, revision) in inputs {
            assert_eq!(
                self.owners[&source].snapshot.revision, revision,
                "stale shared inheritance source"
            );
        }
        for &source in &sources {
            self.register_edge(source, target);
        }
        self.owners
            .get_mut(&target)
            .unwrap()
            .additional
            .extend(sources.into_iter().map(|source| Inheritance {
                source,
                revision: u64::MAX,
                domain: WBTreeSet::new(),
            }));
        self.multiple_sources = true;
        self.refresh_with_shared(target, Some(members), |_| {})
            .is_some()
    }

    pub fn get_snapshot(&self, owner: u32) -> Option<&MemberSnapshot> {
        self.owners.get(&owner).map(|space| &space.snapshot)
    }

    /// A relation can need rebasing even when its source partition is unchanged.
    /// These events are relative to the source snapshot last adopted by refresh.
    pub fn local_merges(&self, owner: u32) -> &[MemberMerge] {
        &self.owners.get(&owner).expect("unknown owner").local_merges
    }

    fn reserve(&mut self, owner: u32, extent: u64) {
        let previous = self.owners[&owner].snapshot.extent;
        if extent <= previous {
            return;
        }
        let len = extent - previous;
        let end = self.next_handle + len;
        assert!(
            end <= u64::from(u32::MAX) + 1,
            "member handle space exhausted"
        );
        let block = MemberBlock {
            owner,
            first_origin: u32::try_from(previous).expect("origin space exhausted"),
            first_handle: u32::try_from(self.next_handle).expect("member handle space exhausted"),
            len,
        };
        self.blocks.insert(block.first_handle, block);
        let snapshot = &mut self.owners.get_mut(&owner).unwrap().snapshot;
        snapshot.by_origin.insert(block.first_origin, block);
        snapshot.by_handle.insert(block.first_handle, block);
        snapshot.extent = extent;
        self.next_handle = end;
    }

    pub fn allocate(&mut self, owner: u32) -> u32 {
        assert!(self.has_owner(owner), "unknown owner");
        let origin = u32::try_from(self.next_origin).expect("member origin space exhausted");
        self.reserve(owner, self.next_origin + 1);
        self.next_origin += 1;
        self.owned_origins += 1;
        let space = self.owners.get_mut(&owner).unwrap();
        space.local_domain.insert(origin);
        space.snapshot.domain.insert(origin);
        space.snapshot.canonical_domain.insert(origin);
        space.snapshot.revision += 1;
        space.snapshot.handle(origin).unwrap()
    }

    /// Installs live total inheritance. Source changes appear after refresh.
    ///
    /// The target can already contain local members and equations. Existing
    /// handles remain stable, including after later source allocation.
    pub fn inherit_total_members(&mut self, source: u32, target: u32) -> bool {
        self.install_inheritance(source, target);
        self.refresh(target)
    }

    pub fn inherit_total_members_with_merges(
        &mut self,
        source: u32,
        target: u32,
    ) -> Option<MemberRefresh> {
        self.install_inheritance(source, target);
        self.refresh_with_merges(target)
    }

    fn install_inheritance(&mut self, source: u32, target: u32) {
        assert!(self.has_owner(source), "unknown source owner");
        assert!(self.has_owner(target), "unknown target owner");
        if let Some(inherited) = &self.owners[&target].inherited {
            assert!(
                inherited.source == source,
                "owner already has another source"
            );
            return;
        }
        self.register_edge(source, target);
        self.owners.get_mut(&target).unwrap().inherited = Some(Inheritance {
            source,
            revision: u64::MAX,
            domain: WBTreeSet::new(),
        });
    }

    /// The source must already be current; descendants can be visited in order.
    pub fn refresh(&mut self, owner: u32) -> bool {
        self.refresh_with(owner, |_| {}).is_some()
    }

    pub fn refresh_with_merges(&mut self, owner: u32) -> Option<MemberRefresh> {
        let mut merges = Vec::new();
        let source = self.refresh_with(owner, |merge| merges.push(merge))?;
        Some(MemberRefresh { source, merges })
    }

    fn refresh_with(
        &mut self,
        owner: u32,
        on_merge: impl FnMut(MemberMerge),
    ) -> Option<MemberSnapshot> {
        self.refresh_with_shared(owner, None, on_merge)
    }

    fn refresh_with_shared(
        &mut self,
        owner: u32,
        shared: Option<SharedMembers>,
        mut on_merge: impl FnMut(MemberMerge),
    ) -> Option<MemberSnapshot> {
        let space = self.owners.get(&owner).expect("unknown owner");
        let Some(inherited) = &space.inherited else {
            return None;
        };
        let source = &self.owners[&inherited.source].snapshot;
        if self.inputs_current(space) {
            return None;
        }
        let shared = if space.additional.is_empty() {
            None
        } else {
            Some(Box::new(shared.unwrap_or_else(|| {
                self.shared_inputs(owner, &[])
                    .expect("unproved shared images")
            })))
        };
        let (mut domain, mut canonical_domain, witnesses, extent) = if space.additional.is_empty() {
            (
                source.domain.clone(),
                source.canonical_domain.clone(),
                source.witnesses.clone(),
                source.extent,
            )
        } else {
            let combined = shared.as_ref().unwrap();
            (
                combined.domain.clone(),
                combined.domain.clone(),
                combined.witnesses.clone(),
                combined.extent,
            )
        };
        for origin in space.local_domain.iter() {
            domain.insert(origin);
            canonical_domain.insert(origin);
        }
        // Equality can advance the source revision without changing its proofs.
        // The current snapshot already includes any newly added local proofs.
        let witnesses = if space.additional.is_empty()
            && space.inherited_witnesses.shares_root(&source.witnesses)
        {
            space.snapshot.witnesses.clone()
        } else {
            witnesses.union_shared(&space.local_witnesses, |_, left, _| left)
        };
        let mut partition = source.partition.clone();
        let mut local_merges = Vec::new();
        for &(lhs, rhs) in &space.local_equations {
            if let Some(merge) = partition.equate(lhs, rhs) {
                canonical_domain.remove(&merge.loser);
                local_merges.push(merge);
                on_merge(merge);
            }
        }
        self.replayed_equations += u64::try_from(space.local_equations.len()).unwrap();
        let revision = source.revision;
        let source = source.clone();
        let additional_snapshots: Vec<_> = space
            .additional
            .iter()
            .map(|input| {
                let snapshot = &self.owners[&input.source].snapshot;
                (snapshot.revision, snapshot.domain.clone())
            })
            .collect();
        self.reserve(owner, extent);
        let space = self.owners.get_mut(&owner).unwrap();
        space.snapshot.domain = domain;
        space.snapshot.canonical_domain = canonical_domain;
        space.snapshot.partition = partition;
        space.snapshot.witnesses = witnesses;
        space.local_merges = local_merges;
        space.snapshot.revision += 1;
        let inherited = space.inherited.as_mut().unwrap();
        inherited.revision = revision;
        inherited.domain = source.domain.clone();
        space.inherited_witnesses = source.witnesses.clone();
        space.shared_members = shared;
        for (input, (revision, domain)) in space.additional.iter_mut().zip(additional_snapshots) {
            input.revision = revision;
            input.domain = domain;
        }
        Some(source)
    }

    pub fn refresh_descendants(&mut self, owner: u32) -> usize {
        let children = &self.owners.get(&owner).expect("unknown owner").children;
        let mut discover: Vec<_> = children.iter().collect();
        let mut incoming = BTreeMap::<u32, usize>::new();
        while let Some(next) = discover.pop() {
            if incoming.insert(next, 0).is_none() {
                discover.extend(self.owners[&next].children.iter());
            }
        }
        let descendants: Vec<_> = incoming.keys().copied().collect();
        for source in descendants {
            for child in self.owners[&source].children.iter() {
                *incoming.get_mut(&child).unwrap() += 1;
            }
        }
        let mut pending: VecDeque<_> = incoming
            .iter()
            .filter_map(|(&owner, &count)| (count == 0).then_some(owner))
            .collect();
        let mut changed = 0;
        while let Some(next) = pending.pop_front() {
            if self.refresh(next) {
                changed += 1;
            }
            for child in self.owners[&next].children.iter() {
                let count = incoming.get_mut(&child).unwrap();
                *count -= 1;
                if *count == 0 {
                    pending.push_back(child);
                }
            }
        }
        changed
    }

    pub fn equate(&mut self, owner: u32, lhs: u32, rhs: u32) -> bool {
        self.equate_with_merge(owner, lhs, rhs).is_some()
    }

    pub fn equate_with_merge(&mut self, owner: u32, lhs: u32, rhs: u32) -> Option<MemberMerge> {
        let space = self.owners.get_mut(&owner).expect("unknown owner");
        let lhs = space
            .snapshot
            .origin(lhs)
            .expect("left member has another owner");
        let rhs = space
            .snapshot
            .origin(rhs)
            .expect("right member has another owner");
        let merge = space.snapshot.partition.equate(lhs, rhs)?;
        space.snapshot.canonical_domain.remove(&merge.loser);
        space.local_equations.push((lhs, rhs));
        space.local_merges.push(merge);
        space.snapshot.revision += 1;
        Some(merge)
    }

    pub fn snapshot(&self, owner: u32) -> MemberSnapshot {
        self.owners
            .get(&owner)
            .expect("unknown owner")
            .snapshot
            .clone()
    }

    pub fn owner(&self, handle: u32) -> Option<u32> {
        let (_, block) = self.blocks.range(..=handle).next_back()?;
        let origin = block.origin(handle)?;
        self.owners[&block.owner]
            .snapshot
            .domain
            .contains(&origin)
            .then_some(block.owner)
    }

    pub fn contains(&self, owner: u32, handle: u32) -> bool {
        self.owners
            .get(&owner)
            .is_some_and(|space| space.snapshot.contains(handle))
    }

    pub fn root(&self, handle: u32) -> Option<u32> {
        self.owners[&self.owner(handle)?].snapshot.root(handle)
    }

    /// A noncanonical source handle still denotes its original mapped member.
    pub fn image(&self, source_handle: u32, target: u32) -> Option<u32> {
        let target = self.owners.get(&target)?;
        let source = self.owner(source_handle)?;
        let origin = self.owners[&source].snapshot.origin(source_handle)?;
        let inherited = target.inherited.as_ref()?;
        if !std::iter::once(inherited)
            .chain(&target.additional)
            .any(|input| input.source == source && input.domain.contains(&origin))
        {
            return None;
        }
        let image = target.snapshot.handle(origin)?;
        target.snapshot.root(image)
    }

    pub fn iter(&self, owner: u32) -> impl Iterator<Item = u32> + '_ {
        self.owners
            .get(&owner)
            .expect("unknown owner")
            .snapshot
            .iter()
    }

    pub fn stats(&self) -> MemberSpaceStats {
        MemberSpaceStats {
            owners: self.owners.len(),
            owned_origins: self.owned_origins,
            handle_blocks: self.blocks.len(),
            reserved_handles: self.next_handle,
            local_equations: self
                .owners
                .values()
                .map(|space| space.local_equations.len())
                .sum(),
            replayed_equations: self.replayed_equations,
        }
    }
}
