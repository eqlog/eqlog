use std::cell::OnceCell;

use crate::versions::SnapshotSet;
use crate::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

#[derive(Clone, Copy)]
enum Kind {
    All,
    Difference,
    Intersection,
}

/// Bound keys can discard inherited changes before any difference tree exists.
#[derive(Clone)]
pub struct AgeView<T> {
    current: T,
    checkpoint: T,
    kind: Kind,
    materialized: OnceCell<T>,
}

impl<T: SnapshotSet> AgeView<T> {
    pub fn empty() -> Self {
        Self::all(T::empty())
    }

    pub fn all(current: T) -> Self {
        Self {
            current,
            checkpoint: T::empty(),
            kind: Kind::All,
            materialized: OnceCell::new(),
        }
    }

    pub fn difference(current: T, checkpoint: T) -> Self {
        Self {
            current,
            checkpoint,
            kind: Kind::Difference,
            materialized: OnceCell::new(),
        }
    }

    pub fn intersection(current: T, checkpoint: T) -> Self {
        Self {
            current,
            checkpoint,
            kind: Kind::Intersection,
            materialized: OnceCell::new(),
        }
    }

    pub fn materialize(&self) -> &T {
        self.materialized.get_or_init(|| match self.kind {
            Kind::All => self.current.clone(),
            Kind::Difference => self.current.difference(&self.checkpoint),
            Kind::Intersection => self.current.intersection(&self.checkpoint),
        })
    }

    fn child<U: SnapshotSet>(&self, current: Option<&U>, checkpoint: Option<&U>) -> AgeView<U> {
        AgeView {
            current: current.cloned().unwrap_or_else(U::empty),
            checkpoint: checkpoint.cloned().unwrap_or_else(U::empty),
            kind: self.kind,
            materialized: OnceCell::new(),
        }
    }
}

impl AgeView<PrefixTree0> {
    pub fn is_empty(&self) -> bool {
        !self.contains([])
    }

    pub fn contains(&self, row: [u32; 0]) -> bool {
        self.current.contains(row)
            && match self.kind {
                Kind::All => true,
                Kind::Difference => !self.checkpoint.contains(row),
                Kind::Intersection => self.checkpoint.contains(row),
            }
    }

    pub fn key_count_up_to(&self, _limit: usize) -> usize {
        usize::from(!self.is_empty())
    }

    pub fn row_count_up_to(&self, limit: usize) -> usize {
        self.key_count_up_to(limit)
    }
}

impl PrefixTree0 {
    pub fn key_count_up_to(&self, _limit: usize) -> usize {
        usize::from(!self.is_empty())
    }

    pub fn row_count_up_to(&self, limit: usize) -> usize {
        self.key_count_up_to(limit)
    }
}

impl AgeView<PrefixTree1> {
    pub fn is_empty(&self) -> bool {
        match self.kind {
            Kind::All => self.current.is_empty(),
            Kind::Difference => self.current.is_subset(&self.checkpoint),
            Kind::Intersection => self.key_count_up_to(0) == 0,
        }
    }

    pub fn contains(&self, row: [u32; 1]) -> bool {
        self.current.contains(row)
            && match self.kind {
                Kind::All => true,
                Kind::Difference => !self.checkpoint.contains(row),
                Kind::Intersection => self.checkpoint.contains(row),
            }
    }

    pub fn restrict(&self, key: u32) -> AgeView<PrefixTree0> {
        self.child(self.current.get(key), self.checkpoint.get(key))
    }

    pub fn get(&self, key: u32) -> Option<AgeView<PrefixTree0>> {
        let child = self.restrict(key);
        (!child.is_empty()).then_some(child)
    }

    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, AgeView<PrefixTree0>)> + '_ {
        self.materialize()
            .iter_restrictions()
            .map(|(key, child)| (key, AgeView::all(child)))
    }

    /// Return min(actual count, limit + 1), including sparse late additions.
    pub fn key_count_up_to(&self, limit: usize) -> usize {
        let stop = limit.saturating_add(1);
        match self.kind {
            Kind::All => self.current.set.len_up_to(stop),
            Kind::Difference => {
                let mut count = 0;
                self.current.set.all_difference(&self.checkpoint.set, |_| {
                    count += 1;
                    count < stop
                });
                count
            }
            Kind::Intersection => {
                let (small, large) = if self.current.set.len_upper_bound()
                    <= self.checkpoint.set.len_upper_bound()
                {
                    (&self.current.set, &self.checkpoint.set)
                } else {
                    (&self.checkpoint.set, &self.current.set)
                };
                small
                    .iter()
                    .filter(|key| large.contains(key))
                    .take(stop)
                    .count()
            }
        }
    }

    pub fn row_count_up_to(&self, limit: usize) -> usize {
        self.key_count_up_to(limit)
    }
}

impl PrefixTree1 {
    pub fn key_count_up_to(&self, limit: usize) -> usize {
        self.set.len_up_to(limit.saturating_add(1))
    }

    pub fn row_count_up_to(&self, limit: usize) -> usize {
        self.key_count_up_to(limit)
    }
}

macro_rules! age_views {
    ($(($tree:ident, $child:ident, $arity:literal)),*) => {$(
        impl AgeView<$tree> {
            pub fn is_empty(&self) -> bool {
                match self.kind {
                    Kind::All | Kind::Intersection => self.iter_restrictions().next().is_none(),
                    Kind::Difference => self.current.shares_root(&self.checkpoint)
                        || self.iter_restrictions().next().is_none(),
                }
            }

            pub fn contains(&self, row: [u32; $arity]) -> bool {
                self.current.contains(row)
                    && match self.kind {
                        Kind::All => true,
                        Kind::Difference => !self.checkpoint.contains(row),
                        Kind::Intersection => self.checkpoint.contains(row),
                    }
            }

            pub fn restrict(&self, key: u32) -> AgeView<$child> {
                self.child(self.current.get(key), self.checkpoint.get(key))
            }

            pub fn get(&self, key: u32) -> Option<AgeView<$child>> {
                let child = self.restrict(key);
                (!child.is_empty()).then_some(child)
            }

            pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, AgeView<$child>)> + '_ {
                let (plain, difference) = match self.kind {
                    Kind::All | Kind::Intersection => (true, false),
                    Kind::Difference => (false, true),
                };
                let plain = plain.then(|| self.current.iter_restrictions())
                    .into_iter().flatten().filter_map(move |(key, current)| {
                        let child = self.child(Some(current), self.checkpoint.get(key));
                        (!child.is_empty()).then_some((key, child))
                    });
                let difference = difference.then(|| {
                    self.current.map.difference_entries(&self.checkpoint.map)
                }).into_iter().flatten().filter_map(move |(key, current, checkpoint)| {
                    let child = self.child(Some(current), checkpoint);
                    (!child.is_empty()).then_some((key, child))
                });
                plain.chain(difference)
            }

            /// Return min(actual key count, limit + 1), without a delta tree.
            pub fn key_count_up_to(&self, limit: usize) -> usize {
                self.iter_restrictions().take(limit.saturating_add(1)).count()
            }

            /// Prefix fanout must not make a cheap-looking join probe unbounded.
            pub fn row_count_up_to(&self, limit: usize) -> usize {
                let mut count = 0;
                for (_, child) in self.iter_restrictions() {
                    let remaining = limit.saturating_sub(count);
                    let next = child.row_count_up_to(remaining);
                    if next > remaining {
                        return limit.saturating_add(1);
                    }
                    count += next;
                }
                count
            }
        }

        impl $tree {
            pub fn key_count_up_to(&self, limit: usize) -> usize {
                self.map.len_up_to(limit.saturating_add(1))
            }

            pub fn row_count_up_to(&self, limit: usize) -> usize {
                let mut count = 0;
                for (_, child) in self.iter_restrictions() {
                    let remaining = limit.saturating_sub(count);
                    let next = child.row_count_up_to(remaining);
                    if next > remaining {
                        return limit.saturating_add(1);
                    }
                    count += next;
                }
                count
            }
        }
    )*};
}

age_views!(
    (PrefixTree2, PrefixTree1, 2),
    (PrefixTree3, PrefixTree2, 3),
    (PrefixTree4, PrefixTree3, 4),
    (PrefixTree5, PrefixTree4, 5),
    (PrefixTree6, PrefixTree5, 6),
    (PrefixTree7, PrefixTree6, 7),
    (PrefixTree8, PrefixTree7, 8),
    (PrefixTree9, PrefixTree8, 9)
);
