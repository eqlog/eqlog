use std::collections::BTreeMap;
use std::rc::Rc;

use crate::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

pub trait SnapshotSet: Clone {
    type Row: Copy;
    fn empty() -> Self;
    fn is_empty(&self) -> bool;
    fn shares_root(&self, other: &Self) -> bool;
    fn is_subset(&self, other: &Self) -> bool;
    fn difference(&self, other: &Self) -> Self;
    fn visit_difference(&self, other: &Self, visit: &mut impl FnMut(Self::Row));
    fn insert_row(&mut self, row: Self::Row);
    fn remove_row(&mut self, row: Self::Row);
}

macro_rules! snapshot_set {
    ($tree:ident, $arity:literal, $left:ident, $right:ident, $shares:expr) => {
        impl SnapshotSet for $tree {
            type Row = [u32; $arity];
            fn is_subset(&self, other: &Self) -> bool {
                self.is_subset(other)
            }
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
}

#[derive(Clone)]
pub struct RelationView<T> {
    pub old: T,
    pub new: T,
}

/// Consumers advance to shared published roots, never to independently updated copies.
pub struct RelationVersions<T, Consumer = usize> {
    current: Rc<Version<T>>,
    empty: Rc<Version<T>>,
    seen: BTreeMap<Consumer, Rc<Version<T>>>,
    views: BTreeMap<u64, RelationView<Option<T>>>,
}

impl<T: SnapshotSet, Consumer: Ord> RelationVersions<T, Consumer> {
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

    pub fn current(&self) -> &T {
        &self.current.rows
    }

    pub fn retain_consumers(&mut self, mut retain: impl FnMut(&Consumer) -> bool) {
        self.seen.retain(|consumer, _| retain(consumer));
    }

    /// Keep supplied trees shared with storage and other consumers. Equal rebuilt
    /// trees retain the previous published root so checkpoints do not diverge.
    pub fn publish(&mut self, rows: &T) {
        if self.current.rows.shares_root(rows) {
            return;
        }
        if self.current.rows.is_subset(rows) && rows.is_subset(&self.current.rows) {
            return;
        }
        self.current = Rc::new(Version {
            id: self
                .current
                .id
                .checked_add(1)
                .expect("relation version overflow"),
            rows: rows.clone(),
        });
        self.views.clear();
    }

    /// The caller must commit the resulting work before allowing an early exit.
    pub fn consume(&mut self, consumer: Consumer) -> RelationView<T> {
        self.consume_required::<true, true>(consumer)
    }

    /// An unused age need not materialize a difference tree.
    pub fn consume_required<const OLD: bool, const NEW: bool>(
        &mut self,
        consumer: Consumer,
    ) -> RelationView<T> {
        let seen = self.seen.get(&consumer).unwrap_or(&self.empty);
        if Rc::ptr_eq(seen, &self.current) {
            return RelationView {
                old: if OLD {
                    self.current.rows.clone()
                } else {
                    T::empty()
                },
                new: T::empty(),
            };
        }
        let view = self.views.entry(seen.id).or_insert_with(|| RelationView {
            old: None,
            new: None,
        });
        let old = if OLD {
            view.old
                .get_or_insert_with(|| {
                    // Removing obsolete IDs is safe; replacing them by their roots here
                    // would hide joins that only became possible after an equality.
                    let mut old = seen.rows.clone();
                    seen.rows.visit_difference(&self.current.rows, &mut |row| {
                        old.remove_row(row);
                    });
                    old
                })
                .clone()
        } else {
            T::empty()
        };
        let new = if NEW {
            view.new
                .get_or_insert_with(|| {
                    if seen.rows.is_empty() {
                        self.current.rows.clone()
                    } else {
                        // Rules need this tree, and difference can reuse whole added subtrees.
                        self.current.rows.difference(&seen.rows)
                    }
                })
                .clone()
        } else {
            T::empty()
        };
        self.seen.insert(consumer, self.current.clone());
        RelationView { old, new }
    }
}
