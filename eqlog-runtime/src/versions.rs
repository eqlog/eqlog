use std::collections::BTreeMap;
use std::rc::Rc;

use crate::lazy_index::{IndexSeed, SnapshotIndices};
use crate::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

pub trait SnapshotSet: Clone {
    type Row: Copy;
    fn empty() -> Self;
    fn is_empty(&self) -> bool;
    fn shares_root(&self, other: &Self) -> bool;
    fn union(&self, other: &Self) -> Self;
    fn difference(&self, other: &Self) -> Self;
    fn visit_difference(&self, other: &Self, visit: &mut impl FnMut(Self::Row));
    fn insert_row(&mut self, row: Self::Row);
    fn remove_row(&mut self, row: Self::Row);
}

macro_rules! snapshot_set {
    ($tree:ident, $arity:literal, $left:ident, $right:ident, $shares:expr) => {
        impl SnapshotSet for $tree {
            type Row = [u32; $arity];
            fn visit_difference(&self, other: &Self, visit: &mut impl FnMut(Self::Row)) {
                self.visit_difference(other, visit);
            }
            fn insert_row(&mut self, row: Self::Row) {
                self.insert(row);
            }
            fn remove_row(&mut self, row: Self::Row) {
                self.remove(row);
            }
            fn empty() -> Self {
                Self::new()
            }
            fn is_empty(&self) -> bool {
                self.is_empty()
            }
            fn shares_root(&self, other: &Self) -> bool {
                let $left = self;
                let $right = other;
                $shares
            }
            fn union(&self, other: &Self) -> Self {
                self.union(other)
            }
            fn difference(&self, other: &Self) -> Self {
                self.difference(other)
            }
        }
    };
}

snapshot_set!(PrefixTree0, 0, left, right, left.0 == right.0);
snapshot_set!(
    PrefixTree1,
    1,
    left,
    right,
    left.set.shares_root(&right.set)
);
snapshot_set!(
    PrefixTree2,
    2,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree3,
    3,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree4,
    4,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree5,
    5,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree6,
    6,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree7,
    7,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree8,
    8,
    left,
    right,
    left.map.shares_root(&right.map)
);
snapshot_set!(
    PrefixTree9,
    9,
    left,
    right,
    left.map.shares_root(&right.map)
);

struct Version<T> {
    id: u64,
    rows: T,
    indices: SnapshotIndices,
}

#[derive(Clone)]
pub struct RelationView<T> {
    pub old: T,
    pub new: T,
    old_indices: SnapshotIndices,
    new_indices: SnapshotIndices,
}

impl<T: SnapshotSet> RelationView<T> {
    pub fn old_index<I: SnapshotSet + 'static>(
        &self,
        id: usize,
        seed: &mut IndexSeed<T, I>,
        project: impl Fn(T::Row) -> Option<I::Row>,
    ) -> I {
        self.old_indices.get(id, &self.old, seed, project)
    }

    pub fn new_index<I: SnapshotSet + 'static>(
        &self,
        id: usize,
        seed: &mut IndexSeed<T, I>,
        project: impl Fn(T::Row) -> Option<I::Row>,
    ) -> I {
        self.new_indices.get(id, &self.new, seed, project)
    }
}

/// Consumers advance to shared published roots, never to independently updated copies.
pub struct RelationVersions<T> {
    current: Rc<Version<T>>,
    empty: Rc<Version<T>>,
    seen: BTreeMap<usize, Rc<Version<T>>>,
    views: BTreeMap<u64, RelationView<T>>,
}

impl<T: SnapshotSet> RelationVersions<T> {
    pub fn new() -> Self {
        let current = Rc::new(Version {
            id: 0,
            rows: T::empty(),
            indices: SnapshotIndices::default(),
        });
        Self {
            empty: current.clone(),
            seen: BTreeMap::new(),
            current,
            views: BTreeMap::new(),
        }
    }

    /// Storage maintenance can rebuild an equal tree or move rows between ages.
    /// Only actual differences may fork the published root and its subtrees.
    pub fn publish(&mut self, old: &T, new: &T) {
        let candidate = if new.is_empty() {
            old.clone()
        } else if old.is_empty() {
            new.clone()
        } else {
            old.union(new)
        };
        if self.current.rows.shares_root(&candidate) {
            return;
        }
        let mut changed = false;
        let rows = if self.current.rows.is_empty() {
            changed = !candidate.is_empty();
            candidate
        } else {
            let mut rows = self.current.rows.clone();
            self.current.rows.visit_difference(&candidate, &mut |row| {
                changed = true;
                rows.remove_row(row);
            });
            candidate.visit_difference(&self.current.rows, &mut |row| {
                changed = true;
                rows.insert_row(row);
            });
            rows
        };
        if !changed {
            return;
        }
        self.current = Rc::new(Version {
            id: self
                .current
                .id
                .checked_add(1)
                .expect("relation version overflow"),
            rows,
            indices: SnapshotIndices::default(),
        });
        self.views.clear();
    }

    /// The caller must commit the resulting work before allowing an early exit.
    pub fn consume(&mut self, consumer: usize) -> RelationView<T> {
        let seen = self.seen.get(&consumer).unwrap_or(&self.empty);
        let view = self
            .views
            .entry(seen.id)
            .or_insert_with(|| {
                // Removing obsolete IDs is safe; replacing them by their roots here
                // would hide joins that only became possible after an equality.
                let mut old = seen.rows.clone();
                let mut removed = false;
                seen.rows.visit_difference(&self.current.rows, &mut |row| {
                    removed = true;
                    old.remove_row(row);
                });
                let (new, new_indices) = if seen.rows.is_empty() {
                    (self.current.rows.clone(), self.current.indices.clone())
                } else {
                    // Rules need this tree, and difference can reuse whole added subtrees.
                    (
                        self.current.rows.difference(&seen.rows),
                        SnapshotIndices::default(),
                    )
                };
                RelationView {
                    old,
                    new,
                    old_indices: if removed {
                        SnapshotIndices::default()
                    } else {
                        seen.indices.clone()
                    },
                    new_indices,
                }
            })
            .clone();
        self.seen.insert(consumer, self.current.clone());
        view
    }
}
