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
    /// Row updates are counted separately in each selected index.
    pub rewrite: OriginRewriteStats,
}

#[derive(Clone, Debug)]
enum OwnerIndex {
    Incidence(OriginRelation),
    Rows(Table),
}

impl OwnerIndex {
    fn rows(&self) -> &Table {
        match self {
            Self::Incidence(relation) => relation.rows(),
            Self::Rows(rows) => rows,
        }
    }

    fn insert(&mut self, tuple: &[u32]) -> bool {
        match self {
            Self::Incidence(relation) => relation.insert(tuple),
            Self::Rows(rows) => !rows.contains(tuple) && rows.insert(tuple),
        }
    }

    fn union(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Incidence(left), Self::Incidence(right)) => Self::Incidence(left.union(right)),
            (Self::Rows(left), Self::Rows(right)) => Self::Rows(left.union(right)),
            (Self::Incidence(_), Self::Rows(_)) | (Self::Rows(_), Self::Incidence(_)) => {
                unreachable!("each index retains its incidence role")
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompactOwnerSnapshot {
    current: Vec<OwnerIndex>,
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
    incidence: usize,
    incidence_positions: Vec<usize>,
}

struct Owner {
    snapshot: CompactOwnerSnapshot,
    source_rows: Vec<Table>,
    component: u32,
    children: WBTreeSet,
    additional: Vec<(u32, u64)>,
    shared_rows: Vec<Vec<Table>>,
    // Rewritten rows cannot replace the raw support used by shared rebases.
    is_raw_union: bool,
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

fn reuse_relations(reused: &mut [bool], relations: &BTreeMap<u32, RelationLayout>) {
    for layout in relations.values() {
        // A full permutation certifies the relation, even if another index changed shape.
        let reuse = reused[layout.incidence];
        for &index in &layout.indices {
            reused[index] = reuse;
        }
    }
}

fn rewrite_relation(
    current: &mut [OwnerIndex],
    specs: &[CompactIndexSpec],
    layout: &RelationLayout,
    member_type: u32,
    loser: u32,
    winner: u32,
) -> OriginRewriteStats {
    let (before, remainder) = current.split_at_mut(layout.incidence);
    let (primary, after) = remainder.split_first_mut().unwrap();
    let primary = match primary {
        OwnerIndex::Incidence(primary) => primary,
        OwnerIndex::Rows(_) => unreachable!("the selected incidence owner has incidence"),
    };
    let mut total = OriginRewriteStats::default();
    let primary_stats = primary.replace_representative_with(member_type, loser, winner, |row| {
        for &index in &layout.indices {
            if index == layout.incidence {
                continue;
            }
            let selected = if index < layout.incidence {
                &mut before[index]
            } else {
                &mut after[index - layout.incidence - 1]
            };
            let rows = match selected {
                OwnerIndex::Rows(rows) => rows,
                OwnerIndex::Incidence(_) => unreachable!("a relation has one incidence owner"),
            };
            let spec = &specs[index];
            let mut tuple: Vec<_> = spec
                .order
                .iter()
                .map(|&column| row[layout.incidence_positions[column]])
                .collect();
            assert!(rows.remove(&tuple), "selected indices disagree");
            for (&column, origin) in spec.order.iter().zip(&mut tuple) {
                if layout.member_types[column] == Some(member_type) && *origin == loser {
                    *origin = winner;
                }
            }
            let inserted = rows.insert(&tuple);
            total.visited_rows += 1;
            total.rewritten_rows += usize::from(inserted);
            total.merged_rows += usize::from(!inserted);
        }
    });
    add_rewrite(&mut total, primary_stats);
    total
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
                    incidence: index,
                    incidence_positions: Vec::new(),
                });
            assert_eq!(
                relation.member_types, spec.member_types,
                "inconsistent relation signature"
            );
            relation.indices.push(index);
        }
        for layout in relations.values_mut() {
            layout.incidence = *layout
                .indices
                .iter()
                .min_by_key(|&&index| {
                    !specs[index]
                        .order
                        .first()
                        .is_some_and(|&column| layout.member_types[column].is_some())
                })
                .unwrap();
            layout.incidence_positions = vec![0; layout.member_types.len()];
            for (position, &column) in specs[layout.incidence].order.iter().enumerate() {
                layout.incidence_positions[column] = position;
            }
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
            .enumerate()
            .map(|(index, spec)| {
                let columns: Vec<_> = spec
                    .order
                    .iter()
                    .map(|&column| spec.member_types[column])
                    .collect();
                if self.relations[&spec.relation].incidence == index {
                    OwnerIndex::Incidence(OriginRelation::new(&columns))
                } else {
                    OwnerIndex::Rows(Table::new(columns.len()))
                }
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
                is_raw_union: true,
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
        self.inherit_shared_many(target, &[source])
    }

    /// The caller has proved that common origins denote equal images.
    /// Batches avoid revisiting old inputs for every new edge.
    pub fn inherit_shared_many(&mut self, target: u32, sources: &[u32]) -> CompactRebaseStats {
        let owner = self.owner(target);
        if sources.is_empty() {
            return CompactRebaseStats::default();
        }
        let primary = owner
            .snapshot
            .source
            .expect("shared inheritance needs a primary source");
        let extend = owner.is_raw_union
            && owner.snapshot.source_revision == Some(self.revision(primary))
            && owner
                .additional
                .iter()
                .all(|&(source, revision)| self.revision(source) == revision);
        for &source in sources {
            self.register_edge(source, target);
        }
        if !extend {
            self.owners
                .get_mut(&target)
                .unwrap()
                .additional
                .extend(sources.iter().map(|&source| (source, u64::MAX)));
            return self.rebase_shared(target, true);
        }
        let mut current = self.owner(target).snapshot.current.clone();
        let mut additional = Vec::with_capacity(sources.len());
        let mut shared_rows = Vec::with_capacity(sources.len());
        for &source in sources {
            let incoming = &self.owner(source).snapshot;
            additional.push((source, incoming.revision));
            shared_rows.push(
                incoming
                    .current
                    .iter()
                    .map(|index| index.rows().clone())
                    .collect(),
            );
            for (index, incoming) in current.iter_mut().zip(&incoming.current) {
                *index = index.union(incoming);
            }
        }
        let owner = self.owners.get_mut(&target).unwrap();
        if owner.additional.is_empty() {
            owner.shared_rows.push(owner.source_rows.clone());
        }
        owner.additional.extend(additional);
        owner.shared_rows.extend(shared_rows);
        let snapshot = &mut owner.snapshot;
        if current
            .iter()
            .zip(&snapshot.current)
            .any(|(new, old)| !new.rows().shares_storage_with(old.rows()))
        {
            snapshot.changed();
        }
        snapshot.current = current;
        CompactRebaseStats {
            refreshed: true,
            ..CompactRebaseStats::default()
        }
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
        let mut reused: Vec<_> = (0..self.specs.len())
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
        reuse_relations(&mut reused, &self.relations);
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
        let is_raw_union = owner.is_raw_union || reused.iter().all(|&reused| !reused);
        let owner = self.owners.get_mut(&target).unwrap();
        owner.source_rows = shared_rows[0].clone();
        owner.shared_rows = shared_rows;
        owner.additional = additional;
        owner.is_raw_union = is_raw_union;
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
        let owner = self.owners.get_mut(&owner).expect("unknown compact owner");
        let snapshot = &mut owner.snapshot;
        let mut stats = OriginRewriteStats::default();
        for layout in self.relations.values() {
            add_rewrite(
                &mut stats,
                rewrite_relation(
                    &mut snapshot.current,
                    &self.specs,
                    layout,
                    member_type,
                    loser,
                    winner,
                ),
            );
        }
        if stats.visited_rows > 0 {
            snapshot.changed();
            owner.is_raw_union = false;
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
        let mut reused: Vec<_> =
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
        reuse_relations(&mut reused, &self.relations);
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
        let mut is_raw_union = target_owner.is_raw_union || reused.iter().all(|&reused| !reused);
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
                        let previous = *origin;
                        *origin = normalize_parent(member_type, *origin);
                        is_raw_union &= *origin == previous;
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
            for layout in self.relations.values() {
                if !reused[layout.incidence] {
                    add_rewrite(
                        &mut stats.rewrite,
                        rewrite_relation(
                            &mut current,
                            &self.specs,
                            layout,
                            member_type,
                            loser,
                            winner,
                        ),
                    );
                }
            }
        }
        let target_owner = self.owners.get_mut(&target).unwrap();
        target_owner.source_rows = source_rows;
        target_owner.is_raw_union = is_raw_union && stats.rewrite.visited_rows == 0;
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
