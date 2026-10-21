use std::collections::{BTreeMap, VecDeque};

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

    fn equate(&mut self, lhs: u32, rhs: u32) -> bool {
        let mut lhs = self.root(lhs);
        let mut rhs = self.root(rhs);
        if lhs == rhs {
            return false;
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
        true
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
    partition: Partition,
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
            partition: Partition::new(),
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
        self.domain
            .iter()
            .filter(|&origin| self.partition.root(origin) == origin)
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
}

struct MemberSpace {
    snapshot: MemberSnapshot,
    local_domain: WBTreeSet,
    local_equations: Vec<(u32, u32)>,
    inherited: Option<Inheritance>,
    component: u32,
    children: Vec<u32>,
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

/// Compact total inheritance with one incoming lineage per owner.
///
/// The explicit partial-map evaluator does not use this opt-in representation.
/// Refresh shares the source domain and union-by-rank partition, then reapplies
/// this owner's local members and equations. Thus refresh costs depend on local
/// history as well as logarithmic tree updates; they are not constant in the
/// number of local waves. A partition lookup uses at most logarithmically many
/// persistent tree lookups. Virtual handle reservations still consume the u32
/// address space, including holes, without allocating one entry per handle.
pub struct MemberSpaces {
    owners: BTreeMap<u32, MemberSpace>,
    blocks: BTreeMap<u32, MemberBlock>,
    components: Unification<u32>,
    next_origin: u64,
    next_handle: u64,
    adoption_bound: u64,
    owned_origins: u64,
    replayed_equations: u64,
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
            owners: BTreeMap::new(),
            blocks: BTreeMap::new(),
            components: Unification::new(),
            next_origin: bound,
            next_handle: bound,
            adoption_bound: bound,
            owned_origins: 0,
            replayed_equations: 0,
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
                inherited: None,
                component,
                children: Vec::new(),
            },
        );
    }

    pub fn has_owner(&self, owner: u32) -> bool {
        self.owners.contains_key(&owner)
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
        space.snapshot.revision += 1;
        space.snapshot.handle(origin).unwrap()
    }

    /// Installs live total inheritance. Source changes appear after refresh.
    ///
    /// The target can already contain local members and equations. Existing
    /// handles remain stable, including after later source allocation.
    pub fn inherit_total_members(&mut self, source: u32, target: u32) -> bool {
        assert!(self.has_owner(source), "unknown source owner");
        assert!(self.has_owner(target), "unknown target owner");
        if let Some(inherited) = &self.owners[&target].inherited {
            assert!(
                inherited.source == source,
                "owner already has another source"
            );
            return self.refresh(target);
        }
        let source_component = self.components.root(self.owners[&source].component);
        let target_component = self.components.root(self.owners[&target].component);
        assert!(
            source_component != target_component,
            "cyclic member inheritance"
        );
        self.components
            .union_roots_into(target_component, source_component);
        self.owners.get_mut(&source).unwrap().children.push(target);
        self.owners.get_mut(&target).unwrap().inherited = Some(Inheritance {
            source,
            revision: u64::MAX,
        });
        self.refresh(target)
    }

    /// The source must already be current; descendants can be visited in order.
    pub fn refresh(&mut self, owner: u32) -> bool {
        let space = self.owners.get(&owner).expect("unknown owner");
        let Some(inherited) = &space.inherited else {
            return false;
        };
        let source = &self.owners[&inherited.source].snapshot;
        if inherited.revision == source.revision {
            return false;
        }
        let mut domain = source.domain.clone();
        for origin in space.local_domain.iter() {
            domain.insert(origin);
        }
        let mut partition = source.partition.clone();
        for &(lhs, rhs) in &space.local_equations {
            partition.equate(lhs, rhs);
        }
        self.replayed_equations += u64::try_from(space.local_equations.len()).unwrap();
        let revision = source.revision;
        let extent = source.extent;
        self.reserve(owner, extent);
        let space = self.owners.get_mut(&owner).unwrap();
        space.snapshot.domain = domain;
        space.snapshot.partition = partition;
        space.snapshot.revision += 1;
        space.inherited.as_mut().unwrap().revision = revision;
        true
    }

    pub fn refresh_descendants(&mut self, owner: u32) -> usize {
        let children = &self.owners.get(&owner).expect("unknown owner").children;
        let mut pending: VecDeque<_> = children.iter().copied().collect();
        let mut changed = 0;
        while let Some(next) = pending.pop_front() {
            if self.refresh(next) {
                changed += 1;
            }
            pending.extend(self.owners[&next].children.iter().copied());
        }
        changed
    }

    pub fn equate(&mut self, owner: u32, lhs: u32, rhs: u32) -> bool {
        let space = self.owners.get_mut(&owner).expect("unknown owner");
        let lhs = space
            .snapshot
            .origin(lhs)
            .expect("left member has another owner");
        let rhs = space
            .snapshot
            .origin(rhs)
            .expect("right member has another owner");
        if !space.snapshot.partition.equate(lhs, rhs) {
            return false;
        }
        space.local_equations.push((lhs, rhs));
        space.snapshot.revision += 1;
        true
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
        let source = target.inherited.as_ref()?.source;
        let origin = self.owners[&source].snapshot.origin(source_handle)?;
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
