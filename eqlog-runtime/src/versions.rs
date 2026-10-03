use std::collections::BTreeMap;
use std::rc::Rc;

use crate::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

pub trait SnapshotSet: Clone {
    fn empty() -> Self;
    fn is_empty(&self) -> bool;
    fn shares_root(&self, other: &Self) -> bool;
    fn union(&self, other: &Self) -> Self;
    fn difference(&self, other: &Self) -> Self;
    fn remove_rows(&mut self, rows: &Self);
    fn insert_rows(&mut self, rows: &Self);
}

macro_rules! snapshot_set {
    ($tree:ident, $left:ident, $right:ident, $shares:expr) => {
        impl SnapshotSet for $tree {
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
            fn remove_rows(&mut self, rows: &Self) {
                for row in rows.iter() {
                    self.remove(row);
                }
            }
            fn insert_rows(&mut self, rows: &Self) {
                for row in rows.iter() {
                    self.insert(row);
                }
            }
        }
    };
}

snapshot_set!(PrefixTree0, left, right, left.0 == right.0);
snapshot_set!(PrefixTree1, left, right, left.set.shares_root(&right.set));
snapshot_set!(PrefixTree2, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree3, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree4, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree5, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree6, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree7, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree8, left, right, left.map.shares_root(&right.map));
snapshot_set!(PrefixTree9, left, right, left.map.shares_root(&right.map));

struct Version<T> {
    id: u64,
    rows: T,
}

#[derive(Clone)]
pub struct RelationView<T> {
    pub old: T,
    pub new: T,
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
        let removed = self.current.rows.difference(&candidate);
        let added = candidate.difference(&self.current.rows);
        if removed.is_empty() && added.is_empty() {
            return;
        }
        let rows = if self.current.rows.is_empty() {
            candidate
        } else {
            let mut rows = self.current.rows.clone();
            rows.remove_rows(&removed);
            rows.insert_rows(&added);
            rows
        };
        self.current = Rc::new(Version {
            id: self
                .current
                .id
                .checked_add(1)
                .expect("relation version overflow"),
            rows,
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
                let removed = seen.rows.difference(&self.current.rows);
                let mut old = seen.rows.clone();
                if !removed.is_empty() {
                    old.remove_rows(&removed);
                }
                RelationView {
                    old,
                    new: self.current.rows.difference(&seen.rows),
                }
            })
            .clone();
        self.seen.insert(consumer, self.current.clone());
        view
    }
}
