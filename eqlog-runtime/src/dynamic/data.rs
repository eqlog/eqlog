use std::collections::BTreeSet;

use super::table::Table;
use super::Error;
use crate::{PrefixTree1, Unification};

/// Stored equality and evaluation state for one sort.
#[derive(Clone, Debug)]
pub struct SortData {
    pub equalities: Unification<u32>,
    /// Representatives allocated since the last evaluation step.
    pub new: PrefixTree1,
    pub old: PrefixTree1,
    /// Per-element costs used to choose which representative survives a merge.
    pub weights: Vec<usize>,
    /// Former representatives whose relation rows may need rewriting.
    pub uprooted: Vec<u32>,
}

impl SortData {
    pub fn new() -> Self {
        Self {
            equalities: Unification::new(),
            new: PrefixTree1::new(),
            old: PrefixTree1::new(),
            weights: Vec::new(),
            uprooted: Vec::new(),
        }
    }
}

/// A relation index with its physical column order.
#[derive(Clone, Debug)]
pub struct RelationIndex {
    /// Maps each table column to a column in the relation's signature.
    pub order: Vec<usize>,
    pub table: Table,
}

impl RelationIndex {
    pub fn new(arity: usize) -> Self {
        Self {
            order: (0..arity).collect(),
            table: Table::new(arity),
        }
    }

    pub(super) fn check(&self, arity: usize) -> Result<(), Error> {
        if self.table.arity() != arity {
            return Err(Error::ArityMismatch {
                expected: arity,
                actual: self.table.arity(),
            });
        }
        if self.order.len() != arity
            || self.order.iter().copied().collect::<BTreeSet<_>>() != (0..arity).collect()
        {
            return Err(Error::InvalidModel(
                "index order is not a column permutation".into(),
            ));
        }
        Ok(())
    }

    /// Iterates stored rows in signature column order, without resolving aliases.
    pub fn tuples(&self) -> impl Iterator<Item = Vec<u32>> + '_ {
        self.table.iter().map(|row| {
            let mut tuple = vec![0; row.len()];
            for (&column, value) in self.order.iter().zip(row) {
                tuple[column] = value;
            }
            tuple
        })
    }

    pub(super) fn contains(&self, tuple: &[u32]) -> bool {
        self.table.contains(
            &self
                .order
                .iter()
                .map(|&column| tuple[column])
                .collect::<Vec<_>>(),
        )
    }

    pub(super) fn insert(&mut self, tuple: &[u32]) -> bool {
        self.table.insert(
            &self
                .order
                .iter()
                .map(|&column| tuple[column])
                .collect::<Vec<_>>(),
        )
    }
}

/// The new and old rows of a relation. Rows may contain equality aliases.
#[derive(Clone, Debug)]
pub struct RelationData {
    pub new: RelationIndex,
    pub old: RelationIndex,
    /// Cost per tuple column used to update element weights on insertion.
    pub weight: usize,
}

impl RelationData {
    pub fn new(arity: usize) -> Self {
        Self {
            new: RelationIndex::new(arity),
            old: RelationIndex::new(arity),
            weight: 1,
        }
    }

    /// Iterates both partitions without resolving aliases or removing duplicates.
    pub fn tuples(&self) -> impl Iterator<Item = Vec<u32>> + '_ {
        self.new.tuples().chain(self.old.tuples())
    }

    /// Builds an index over both partitions without changing element IDs.
    ///
    /// `equalities[i]` names the first column equal to column `i`. An empty slice
    /// imposes no equalities. `order` permutes the remaining columns after repeated
    /// columns are removed. Matching stored indices retain their shared tree nodes.
    pub fn reindex(&self, order: &[usize], equalities: &[usize]) -> Result<Table, Error> {
        let arity = self.new.table.arity();
        self.new.check(arity)?;
        self.old.check(arity)?;
        let columns: Vec<_> = if equalities.is_empty() {
            (0..arity).collect()
        } else {
            if equalities.len() != arity
                || equalities
                    .iter()
                    .enumerate()
                    .any(|(i, &column)| column > i || equalities[column] != column)
            {
                return Err(Error::InvalidModel("invalid diagonal columns".into()));
            }
            (0..arity).filter(|&i| equalities[i] == i).collect()
        };
        if order.len() != columns.len()
            || order.iter().copied().collect::<BTreeSet<_>>() != (0..columns.len()).collect()
        {
            return Err(Error::InvalidModel("invalid projected column order".into()));
        }
        let build = |index: &RelationIndex| {
            if columns.len() == arity && index.order == order {
                return index.table.clone();
            }
            let mut table = Table::new(columns.len());
            for tuple in index.tuples() {
                if equalities
                    .iter()
                    .enumerate()
                    .any(|(i, &column)| tuple[i] != tuple[column])
                {
                    continue;
                }
                let row: Vec<_> = order.iter().map(|&i| tuple[columns[i]]).collect();
                table.insert(&row);
            }
            table
        };
        Ok(build(&self.new).union(&build(&self.old)))
    }
}
