use std::rc::Rc;

use crate::table::Table;
use crate::wbtree::map::WBTreeMap;

/// Equality work counts rows from one losing representative's incidence bucket.
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
    len: usize,
}

fn references<'a>(
    member_types: &'a [Option<u32>],
    tuple: &'a [u32],
) -> impl Iterator<Item = (u32, u32)> + 'a {
    member_types
        .iter()
        .enumerate()
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
            len: 0,
        }
    }

    pub fn member_types(&self) -> &[Option<u32>] {
        &self.member_types
    }

    pub fn rows(&self) -> &Table {
        &self.rows
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
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
        self.len += 1;
        let arity = self.member_types.len();
        for (member_type, origin) in references(&self.member_types, tuple) {
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
        self.len -= 1;
        for (member_type, origin) in references(&self.member_types, tuple) {
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
        if loser == winner {
            return OriginRewriteStats::default();
        }
        let affected = self
            .incidence
            .get(&member_type)
            .and_then(|origins| origins.get(&loser))
            .cloned();
        let Some(affected) = affected else {
            return OriginRewriteStats::default();
        };
        let mut stats = OriginRewriteStats::default();
        for mut tuple in affected.iter() {
            stats.visited_rows += 1;
            self.remove(&tuple);
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
