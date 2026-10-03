use std::any::Any;
use std::cell::{OnceCell, RefCell};
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::versions::SnapshotSet;

#[derive(Clone, Default)]
pub(crate) struct SnapshotIndices(Rc<RefCell<BTreeMap<usize, Box<dyn Any>>>>);

impl SnapshotIndices {
    pub(crate) fn get<P: SnapshotSet, I: SnapshotSet + 'static>(
        &self,
        id: usize,
        source: &P,
        seed: &mut IndexSeed<P, I>,
        project: impl Fn(P::Row) -> Option<I::Row>,
    ) -> I {
        let mut indices = self.0.borrow_mut();
        let index = indices
            .entry(id)
            .or_insert_with(|| Box::new(seed.update(source, project)))
            .downcast_ref::<I>()
            .expect("index IDs must have a unique type")
            .clone();
        seed.source = source.clone();
        seed.index = index.clone();
        index
    }
}

/// Retains the source alongside the index so skipped updates need no edit log.
pub struct IndexSeed<P, I> {
    source: P,
    index: I,
}

impl<P: SnapshotSet, I: SnapshotSet> IndexSeed<P, I> {
    pub fn new() -> Self {
        Self {
            source: P::empty(),
            index: I::empty(),
        }
    }

    /// The projection must be injective on rows for which it returns Some.
    pub fn update(&mut self, source: &P, project: impl Fn(P::Row) -> Option<I::Row>) -> I {
        if source.is_empty() {
            self.source = source.clone();
            self.index = I::empty();
            return self.index.clone();
        }
        if !self.source.shares_root(source) {
            self.source.visit_difference(source, &mut |row| {
                if let Some(row) = project(row) {
                    self.index.remove_row(row);
                }
            });
            source.visit_difference(&self.source, &mut |row| {
                if let Some(row) = project(row) {
                    self.index.insert_row(row);
                }
            });
            self.source = source.clone();
        }
        self.index.clone()
    }
}

/// A stable borrow for public iterators, with a warm seed surviving invalidation.
pub struct LazyIndex<P, I> {
    seed: RefCell<IndexSeed<P, I>>,
    current: OnceCell<I>,
}

impl<P: SnapshotSet, I: SnapshotSet> LazyIndex<P, I> {
    pub fn new() -> Self {
        Self {
            seed: RefCell::new(IndexSeed::new()),
            current: OnceCell::new(),
        }
    }

    pub fn get(&self, source: &P, project: impl Fn(P::Row) -> Option<I::Row>) -> &I {
        self.current
            .get_or_init(|| self.seed.borrow_mut().update(source, project))
    }

    /// Call whenever the primary may change, before any subsequent reads.
    pub fn invalidate(&mut self) {
        self.current.take();
    }
}
