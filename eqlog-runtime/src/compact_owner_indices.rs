use std::collections::{BTreeMap, BTreeSet};

use crate::origin_relations::{OriginRelation, OriginRewriteStats};
use crate::table::Table;
use crate::wbtree::set::WBTreeSet;
use crate::Unification;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompactIndexSpec {
    pub relation: u32,
    /// A full permutation of the owner-free relation signature.
    pub order: Vec<usize>,
    /// Signature-order partition labels; global columns have no label.
    pub member_types: Vec<Option<u32>>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CompactRecordResult {
    pub inserted: bool,
    pub retained_support: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CompactRebaseStats {
    pub refreshed: bool,
    /// Child indexes whose parent rows and applicable quotient stayed unchanged.
    pub reused_indices: usize,
    /// Signature-order support rows, counted once per relation.
    pub local_rows_replayed: usize,
    /// Incidence work is counted separately in each selected index.
    pub rewrite: OriginRewriteStats,
}

#[derive(Clone, Debug)]
pub struct CompactOwnerSnapshot {
    current: Vec<OriginRelation>,
    local: BTreeMap<u32, Table>,
    source: Option<u32>,
    source_revision: Option<u64>,
    revision: u64,
}

impl CompactOwnerSnapshot {
    pub fn rows(&self, index: usize) -> &Table {
        self.current
            .get(index)
            .expect("unknown compact index")
            .rows()
    }

    pub fn local_rows(&self, relation: u32) -> &Table {
        self.local.get(&relation).expect("unknown compact relation")
    }

    pub fn source(&self) -> Option<u32> {
        self.source
    }

    pub fn source_revision(&self) -> Option<u64> {
        self.source_revision
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    fn changed(&mut self) {
        self.revision = self
            .revision
            .checked_add(1)
            .expect("index revision overflow");
    }
}

struct RelationLayout {
    member_types: Vec<Option<u32>>,
    indices: Vec<usize>,
}

struct Owner {
    snapshot: CompactOwnerSnapshot,
    source_rows: Vec<Table>,
    component: u32,
    children: WBTreeSet,
    additional: Vec<(u32, u64)>,
    shared_rows: Vec<Vec<Table>>,
}

/// Separate local support lets a new parent snapshot replace inherited history.
///
/// The caller owns member partitions, canonicalizes incoming rows, and supplies
/// ordered local merge events when rebasing. All selected indexes are full
/// permutations, so their row-presence checks agree without enumerating rows.
pub struct CompactOwnerIndices {
    specs: Vec<CompactIndexSpec>,
    relations: BTreeMap<u32, RelationLayout>,
    owners: BTreeMap<u32, Owner>,
    components: Unification<u32>,
}

fn add_rewrite(total: &mut OriginRewriteStats, next: OriginRewriteStats) {
    total.visited_rows += next.visited_rows;
    total.rewritten_rows += next.rewritten_rows;
    total.merged_rows += next.merged_rows;
}

fn project(tuple: &[u32], order: &[usize]) -> Vec<u32> {
    order.iter().map(|&column| tuple[column]).collect()
}

impl CompactOwnerIndices {
    pub fn new(specs: Vec<CompactIndexSpec>) -> Self {
        let mut relations = BTreeMap::<u32, RelationLayout>::new();
        for (index, spec) in specs.iter().enumerate() {
            let mut order = spec.order.clone();
            order.sort_unstable();
            assert!(
                order.iter().copied().eq(0..spec.member_types.len()),
                "compact indexes require a full signature permutation"
            );
            let relation = relations
                .entry(spec.relation)
                .or_insert_with(|| RelationLayout {
                    member_types: spec.member_types.clone(),
                    indices: Vec::new(),
                });
            assert_eq!(
                relation.member_types, spec.member_types,
                "inconsistent relation signature"
            );
            relation.indices.push(index);
        }
        Self {
            specs,
            relations,
            owners: BTreeMap::new(),
            components: Unification::new(),
        }
    }

    pub fn create_owner(&mut self, owner: u32) {
        assert!(
            !self.owners.contains_key(&owner),
            "compact owner already exists"
        );
        let component = u32::try_from(self.components.len()).expect("too many compact owners");
        self.components.increase_size_to(self.components.len() + 1);
        let current = self
            .specs
            .iter()
            .map(|spec| {
                let columns: Vec<_> = spec
                    .order
                    .iter()
                    .map(|&column| spec.member_types[column])
                    .collect();
                OriginRelation::new(&columns)
            })
            .collect();
        let local = self
            .relations
            .iter()
            .map(|(&relation, layout)| (relation, Table::new(layout.member_types.len())))
            .collect();
        self.owners.insert(
            owner,
            Owner {
                snapshot: CompactOwnerSnapshot {
                    current,
                    local,
                    source: None,
                    source_revision: None,
                    revision: 0,
                },
                source_rows: Vec::new(),
                component,
                children: WBTreeSet::new(),
                additional: Vec::new(),
                shared_rows: Vec::new(),
            },
        );
    }

    fn owner(&self, owner: u32) -> &Owner {
        self.owners.get(&owner).expect("unknown compact owner")
    }

    pub fn has_owner(&self, owner: u32) -> bool {
        self.owners.contains_key(&owner)
    }

    pub fn owners(&self) -> impl Iterator<Item = u32> + '_ {
        self.owners.keys().copied()
    }

    pub fn rows(&self, owner: u32, index: usize) -> &Table {
        self.owner(owner).snapshot.rows(index)
    }

    /// Identifies the parent rows whose proved properties survive this rebase.
    /// One incoming source supplies this baseline: combining sources would hide
    /// joins that become possible only after their facts meet at the target.
    pub fn inherited_rows(&self, owner: u32, index: usize) -> Option<&Table> {
        self.owner(owner).source_rows.get(index)
    }

    pub fn local_rows(&self, owner: u32, relation: u32) -> &Table {
        self.owner(owner).snapshot.local_rows(relation)
    }

    pub fn revision(&self, owner: u32) -> u64 {
        self.owner(owner).snapshot.revision()
    }

    pub fn source(&self, owner: u32) -> Option<u32> {
        self.owner(owner).snapshot.source()
    }

    pub fn source_revision(&self, owner: u32) -> Option<u64> {
        self.owner(owner).snapshot.source_revision()
    }

    pub fn snapshot(&self, owner: u32) -> CompactOwnerSnapshot {
        self.owner(owner).snapshot.clone()
    }

    /// Checking pending edges at registration avoids revisiting future branches
    /// when their rows are eventually transported in topological order.
    pub fn register_edge(&mut self, source: u32, target: u32) {
        if self.owner(source).children.contains(&target) {
            return;
        }
        let source_root = self.components.root(self.owner(source).component);
        let target_root = self.components.root(self.owner(target).component);
        if source_root == target_root {
            assert_ne!(source, target, "cyclic compact inheritance");
            let mut pending: Vec<_> = self.owner(target).children.iter().collect();
            let mut visited = BTreeSet::new();
            while let Some(owner) = pending.pop() {
                assert_ne!(owner, source, "cyclic compact inheritance");
                if visited.insert(owner) {
                    pending.extend(self.owner(owner).children.iter());
                }
            }
        } else {
            self.components.union_roots_into(target_root, source_root);
        }
        self.owners
            .get_mut(&source)
            .unwrap()
            .children
            .insert(target);
    }

    /// The caller has proved that common origin coordinates denote equal images.
    pub fn inherit_shared(&mut self, target: u32, source: u32) -> CompactRebaseStats {
        assert!(
            self.source(target).is_some(),
            "shared inheritance needs a primary source"
        );
        self.register_edge(source, target);
        self.owners
            .get_mut(&target)
            .unwrap()
            .additional
            .push((source, u64::MAX));
        self.rebase_shared(target, true)
    }

    fn rebase_shared(&mut self, target: u32, force: bool) -> CompactRebaseStats {
        let owner = self.owner(target);
        let source = owner.snapshot.source.unwrap();
        let source_revision = self.revision(source);
        if !force
            && owner.snapshot.source_revision == Some(source_revision)
            && owner
                .additional
                .iter()
                .all(|&(source, revision)| self.revision(source) == revision)
        {
            return CompactRebaseStats::default();
        }
        let sources: Vec<_> = std::iter::once(source)
            .chain(owner.additional.iter().map(|&(source, _)| source))
            .collect();
        let shared_rows: Vec<Vec<_>> = sources
            .iter()
            .map(|&source| {
                self.owner(source)
                    .snapshot
                    .current
                    .iter()
                    .map(|index| index.rows().clone())
                    .collect()
            })
            .collect();
        let reused: Vec<_> = (0..self.specs.len())
            .map(|index| {
                !force
                    && owner.shared_rows.len() == shared_rows.len()
                    && owner
                        .shared_rows
                        .iter()
                        .zip(&shared_rows)
                        .all(|(old, new)| old[index].shares_storage_with(&new[index]))
            })
            .collect();
        let mut current: Vec<_> = self
            .specs
            .iter()
            .enumerate()
            .map(|(index, _)| {
                if reused[index] {
                    return owner.snapshot.current[index].clone();
                }
                let mut result = self.owner(source).snapshot.current[index].clone();
                for &source in &sources[1..] {
                    result = result.union(&self.owner(source).snapshot.current[index]);
                }
                result
            })
            .collect();
        let mut stats = CompactRebaseStats {
            refreshed: true,
            reused_indices: reused.iter().filter(|&&reuse| reuse).count(),
            ..CompactRebaseStats::default()
        };
        for (&relation, local) in &owner.snapshot.local {
            let layout = &self.relations[&relation];
            if layout.indices.iter().all(|&index| reused[index]) {
                continue;
            }
            for tuple in local.iter() {
                stats.local_rows_replayed += 1;
                for &index in &layout.indices {
                    if !reused[index] {
                        current[index].insert(&project(&tuple, &self.specs[index].order));
                    }
                }
            }
        }
        let additional: Vec<_> = owner
            .additional
            .iter()
            .map(|&(source, _)| (source, self.revision(source)))
            .collect();
        let owner = self.owners.get_mut(&target).unwrap();
        owner.source_rows = shared_rows[0].clone();
        owner.shared_rows = shared_rows;
        owner.additional = additional;
        let snapshot = &mut owner.snapshot;
        if current
            .iter()
            .zip(&snapshot.current)
            .any(|(new, old)| !new.rows().shares_storage_with(old.rows()))
        {
            snapshot.changed();
        }
        snapshot.current = current;
        snapshot.source_revision = Some(source_revision);
        stats
    }

    /// Redundant derived facts need no local support; explicit facts can retain it.
    pub fn record(
        &mut self,
        owner: u32,
        relation: u32,
        origin_row: &[u32],
        retain_support: bool,
    ) -> CompactRecordResult {
        let layout = self
            .relations
            .get(&relation)
            .expect("unknown compact relation");
        assert_eq!(origin_row.len(), layout.member_types.len(), "tuple arity");
        let snapshot = &mut self
            .owners
            .get_mut(&owner)
            .expect("unknown compact owner")
            .snapshot;
        let mut inserted = None;
        for &index in &layout.indices {
            let tuple = project(origin_row, &self.specs[index].order);
            let current_inserted = snapshot.current[index].insert(&tuple);
            if let Some(previous) = inserted {
                assert_eq!(previous, current_inserted, "compact indexes disagree");
            }
            inserted = Some(current_inserted);
        }
        let inserted = inserted.expect("relations have selected indexes");
        let retained_support = (inserted || retain_support)
            && snapshot
                .local
                .get_mut(&relation)
                .expect("relation support exists")
                .insert(origin_row);
        if inserted {
            snapshot.changed();
        }
        CompactRecordResult {
            inserted,
            retained_support,
        }
    }

    /// Local support keeps its original coordinates for future parent replacement.
    pub fn rewrite(
        &mut self,
        owner: u32,
        member_type: u32,
        loser: u32,
        winner: u32,
    ) -> OriginRewriteStats {
        let snapshot = &mut self
            .owners
            .get_mut(&owner)
            .expect("unknown compact owner")
            .snapshot;
        let mut stats = OriginRewriteStats::default();
        for index in &mut snapshot.current {
            add_rewrite(
                &mut stats,
                index.replace_representative(member_type, loser, winner),
            );
        }
        if stats.visited_rows > 0 {
            snapshot.changed();
        }
        stats
    }

    /// Partition changes without parent row changes require `force`.
    ///
    /// Normalize local support in the parent's partition before replaying the
    /// target's local merges. Neither old nor new inherited rows are enumerated.
    pub fn rebase(
        &mut self,
        target: u32,
        source: u32,
        force: bool,
        mut normalize_parent: impl FnMut(u32, u32) -> u32,
        merges: &[(u32, u32, u32)],
    ) -> CompactRebaseStats {
        let source_revision = self.owner(source).snapshot.revision;
        let target_owner = self.owner(target);
        if let Some(previous) = target_owner.snapshot.source {
            assert_eq!(previous, source, "compact owner already has another source");
            if !target_owner.additional.is_empty() {
                assert!(
                    merges.is_empty(),
                    "shared inheritance requires an unchanged partition"
                );
                return self.rebase_shared(target, force);
            }
            if !force && target_owner.snapshot.source_revision == Some(source_revision) {
                return CompactRebaseStats::default();
            }
        } else {
            self.register_edge(source, target);
        }
        let parent = &self.owner(source).snapshot.current;
        let target_owner = self.owner(target);
        // Stable roots let rule checkpoints skip unrelated inherited relations.
        let reused: Vec<_> =
            self.specs
                .iter()
                .enumerate()
                .map(|(index, spec)| {
                    (!force || spec.member_types.iter().all(Option::is_none))
                        && target_owner.source_rows.get(index).is_some_and(|previous| {
                            previous.shares_storage_with(parent[index].rows())
                        })
                })
                .collect();
        let mut current: Vec<_> = parent
            .iter()
            .enumerate()
            .map(|(index, parent)| {
                if reused[index] {
                    target_owner.snapshot.current[index].clone()
                } else {
                    parent.clone()
                }
            })
            .collect();
        let source_rows = parent.iter().map(|index| index.rows().clone()).collect();
        let mut stats = CompactRebaseStats {
            refreshed: true,
            reused_indices: reused.iter().filter(|&&reuse| reuse).count(),
            ..CompactRebaseStats::default()
        };
        for (&relation, local) in &self.owner(target).snapshot.local {
            let layout = &self.relations[&relation];
            if layout.indices.iter().all(|&index| reused[index]) {
                continue;
            }
            for mut tuple in local.iter() {
                stats.local_rows_replayed += 1;
                for (&member_type, origin) in layout.member_types.iter().zip(&mut tuple) {
                    if let Some(member_type) = member_type {
                        *origin = normalize_parent(member_type, *origin);
                    }
                }
                for &index in &layout.indices {
                    if !reused[index] {
                        current[index].insert(&project(&tuple, &self.specs[index].order));
                    }
                }
            }
        }
        for &(member_type, loser, winner) in merges {
            for (index, current) in current.iter_mut().enumerate() {
                if !reused[index] {
                    add_rewrite(
                        &mut stats.rewrite,
                        current.replace_representative(member_type, loser, winner),
                    );
                }
            }
        }
        let target_owner = self.owners.get_mut(&target).unwrap();
        target_owner.source_rows = source_rows;
        let snapshot = &mut target_owner.snapshot;
        if current
            .iter()
            .zip(&snapshot.current)
            .any(|(new, previous)| !new.rows().shares_storage_with(previous.rows()))
        {
            snapshot.changed();
        }
        snapshot.current = current;
        snapshot.source = Some(source);
        snapshot.source_revision = Some(source_revision);
        stats
    }
}
