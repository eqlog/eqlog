use std::cell::Cell;
use std::num::NonZeroUsize;
use std::rc::Rc;

use crate::table::Table;
use crate::wbtree::map::WBTreeMap;

/// Equality work counts rows mentioning one losing representative.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct OriginRewriteStats {
    pub visited_rows: usize,
    /// Newly inserted rows, excluding collisions with existing canonical rows.
    pub rewritten_rows: usize,
    pub merged_rows: usize,
}

/// Owner-local origin coordinates let inherited rows share their parent's trees.
///
/// Each member column names its partition; `None` columns are unaffected by
/// member equality. The caller supplies canonical insertion rows and applies
/// partition merges in order. No partition or per-owner handle map is stored.
#[derive(Clone, Debug)]
pub struct OriginRelation {
    member_types: Rc<[Option<u32>]>,
    rows: Table,
    incidence: WBTreeMap<WBTreeMap<Table>>,
    // The zero niche keeps a lazy cardinality in the space of an exact count.
    len: Cell<Option<NonZeroUsize>>,
}

fn auxiliary_references<'a>(
    member_types: &'a [Option<u32>],
    tuple: &'a [u32],
) -> impl Iterator<Item = (u32, u32)> + 'a {
    member_types
        .iter()
        .enumerate()
        // The row tree indexes the first column, including its repeated uses.
        .skip(1)
        .filter_map(move |(column, member_type)| {
            let member_type = (*member_type)?;
            let origin = tuple[column];
            let repeated = member_types[..column].iter().zip(&tuple[..column]).any(
                |(&previous_type, &previous)| {
                    previous_type == Some(member_type) && previous == origin
                },
            );
            (!repeated).then_some((member_type, origin))
        })
}

impl OriginRelation {
    pub fn new(member_types: &[Option<u32>]) -> Self {
        Self {
            member_types: Rc::from(member_types),
            rows: Table::new(member_types.len()),
            incidence: WBTreeMap::new(),
            len: Cell::new(Some(NonZeroUsize::MIN)),
        }
    }

    pub fn member_types(&self) -> &[Option<u32>] {
        &self.member_types
    }

    pub fn rows(&self) -> &Table {
        &self.rows
    }

    pub fn len(&self) -> usize {
        if let Some(len) = self.len.get() {
            return len.get() - 1;
        }
        let len = self.rows.iter().fold(NonZeroUsize::MIN, |len, _| {
            len.checked_add(1).expect("relation length overflow")
        });
        self.len.set(Some(len));
        len.get() - 1
    }

    fn change_len(&self, difference: isize) {
        self.len.set(self.len.get().map(|len| {
            let len = len
                .get()
                .checked_add_signed(difference)
                .expect("relation length overflow");
            NonZeroUsize::new(len).expect("relation length underflow")
        }));
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Shared ancestry remains shared in both rows and reverse incidence.
    pub fn union(&self, other: &Self) -> Self {
        assert_eq!(self.member_types, other.member_types);
        if self.shares_storage_with(other) || other.is_empty() {
            return self.clone();
        }
        if self.is_empty() {
            return other.clone();
        }
        Self {
            member_types: self.member_types.clone(),
            rows: self.rows.union(&other.rows),
            incidence: self
                .incidence
                .union_shared(&other.incidence, |_, left, right| {
                    left.union_shared(&right, |_, left, right| left.union(&right))
                }),
            len: Cell::new(None),
        }
    }

    pub fn contains(&self, tuple: &[u32]) -> bool {
        self.rows.contains(tuple)
    }

    /// The caller's current partitions must already canonicalize member columns.
    pub fn insert(&mut self, tuple: &[u32]) -> bool {
        if self.rows.contains(tuple) {
            return false;
        }
        assert!(self.rows.insert(tuple));
        self.change_len(1);
        let arity = self.member_types.len();
        for (member_type, origin) in auxiliary_references(&self.member_types, tuple) {
            let rows = self
                .incidence
                .entry(member_type)
                .or_insert_with(WBTreeMap::new)
                .entry(origin)
                .or_insert_with(|| Table::new(arity));
            assert!(rows.insert(tuple));
        }
        true
    }

    fn remove(&mut self, tuple: &[u32]) {
        assert!(self.rows.remove(tuple), "incidence refers to an absent row");
        self.change_len(-1);
        for (member_type, origin) in auxiliary_references(&self.member_types, tuple) {
            let origins = self
                .incidence
                .get_mut(&member_type)
                .expect("member columns have an incidence index");
            let rows = origins
                .get_mut(&origin)
                .expect("member origins have an incidence bucket");
            assert!(rows.remove(tuple), "incidence is missing a relation row");
            if rows.is_empty() {
                origins.remove(&origin).expect("the bucket exists");
            }
            if origins.is_empty() {
                self.incidence
                    .remove(&member_type)
                    .expect("the member index exists");
            }
        }
    }

    /// Apply one partition merge without scanning other rows or member domains.
    ///
    /// The merge direction is supplied by the caller's union-find. A row that
    /// mentions the loser repeatedly is visited once, and collisions retain one
    /// canonical row with all of its incidence entries.
    pub fn replace_representative(
        &mut self,
        member_type: u32,
        loser: u32,
        winner: u32,
    ) -> OriginRewriteStats {
        self.replace_representative_with(member_type, loser, winner, |_| {})
    }

    /// Selected permutations can reuse this incidence without storing copies.
    pub(crate) fn replace_representative_with(
        &mut self,
        member_type: u32,
        loser: u32,
        winner: u32,
        mut on_row: impl FnMut(&[u32]),
    ) -> OriginRewriteStats {
        if loser == winner {
            return OriginRewriteStats::default();
        }
        if self.member_types.len() == 1 {
            if self.member_types[0] != Some(member_type) || !self.rows.remove(&[loser]) {
                return OriginRewriteStats::default();
            }
            on_row(&[loser]);
            self.change_len(-1);
            let inserted = self.insert(&[winner]);
            return OriginRewriteStats {
                visited_rows: 1,
                rewritten_rows: usize::from(inserted),
                merged_rows: usize::from(!inserted),
            };
        }
        let prefix = if self.member_types.first() == Some(&Some(member_type)) {
            self.rows.first_column(loser)
        } else {
            None
        };
        let affected = self
            .incidence
            .get(&member_type)
            .and_then(|origins| origins.get(&loser))
            .cloned();
        let mut stats = OriginRewriteStats::default();
        let prefix_rows = prefix.iter().flat_map(|rows| rows.iter()).map(|mut tuple| {
            tuple.insert(0, loser);
            tuple
        });
        for mut tuple in prefix_rows.chain(affected.iter().flat_map(|rows| rows.iter())) {
            stats.visited_rows += 1;
            self.remove(&tuple);
            on_row(&tuple);
            for (column_type, origin) in self.member_types.iter().zip(&mut tuple) {
                if *column_type == Some(member_type) && *origin == loser {
                    *origin = winner;
                }
            }
            if self.insert(&tuple) {
                stats.rewritten_rows += 1;
            } else {
                stats.merged_rows += 1;
            }
        }
        stats
    }

    pub fn shares_storage_with(&self, other: &Self) -> bool {
        self.member_types == other.member_types
            && self.rows.shares_storage_with(&other.rows)
            && self.incidence.shares_root(&other.incidence)
    }
}
