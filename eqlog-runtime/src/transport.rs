use std::collections::BTreeSet;
use std::rc::Rc;

use crate::toposort::MorphismGraph;
use crate::versions::SnapshotSet;
use crate::{
    MorphismWithSignature, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5,
    PrefixTree6, PrefixTree7, PrefixTree8, PrefixTree9,
};

pub trait TransportPartitions: SnapshotSet {
    fn changed_partitions(&self, previous: &Self, changed: &mut BTreeSet<u32>);
}

impl TransportPartitions for PrefixTree1 {
    fn changed_partitions(&self, previous: &Self, changed: &mut BTreeSet<u32>) {
        self.visit_difference(previous, &mut |[owner]| {
            changed.insert(owner);
        });
    }
}

macro_rules! transport_partitions {
    ($($tree:ident),*) => {$(
        impl TransportPartitions for $tree {
            fn changed_partitions(&self, previous: &Self, changed: &mut BTreeSet<u32>) {
                for (owner, current, old) in self.map.difference_entries(&previous.map) {
                    if old.is_none_or(|old| !current.is_subset(old)) {
                        changed.insert(owner);
                    }
                }
            }
        }
    )*};
}

transport_partitions!(
    PrefixTree2,
    PrefixTree3,
    PrefixTree4,
    PrefixTree5,
    PrefixTree6,
    PrefixTree7,
    PrefixTree8,
    PrefixTree9
);

#[derive(Default)]
pub struct TransportWork {
    full: bool,
    owners: BTreeSet<u32>,
    morphisms: BTreeSet<u32>,
}

impl TransportWork {
    pub fn is_empty(&self) -> bool {
        !self.full && self.owners.is_empty() && self.morphisms.is_empty()
    }

    pub fn needs_visit(&self, morphism: &MorphismWithSignature) -> bool {
        self.full || self.owners.contains(&morphism.dom) || self.morphisms.contains(&morphism.morph)
    }

    pub fn mark_changed(&mut self, owner: u32) {
        if !self.full {
            self.owners.insert(owner);
        }
    }
}

/// Source, map, and graph rows must grow or undergo the same equality quotient.
#[derive(Clone)]
pub struct TransportFrontier<T, const M: usize> {
    source: T,
    maps: [PrefixTree3; M],
    graph: Option<Rc<MorphismGraph>>,
    retain_own: bool,
}

fn graph_additions(previous: &MorphismGraph, current: &MorphismGraph, changed: &mut BTreeSet<u32>) {
    if Rc::ptr_eq(&previous.signatures, &current.signatures) {
        return;
    }
    let mut previous = previous.signatures.iter().peekable();
    for edge in current.signatures.iter() {
        while previous.peek().is_some_and(|old| *old < edge) {
            previous.next();
        }
        if previous.peek().copied() == Some(edge) {
            previous.next();
            continue;
        }
        changed.insert(edge.0);
    }
}

impl<T: TransportPartitions, const M: usize> TransportFrontier<T, M> {
    pub fn new() -> Self {
        Self {
            source: T::empty(),
            maps: std::array::from_fn(|_| PrefixTree3::new()),
            graph: None,
            retain_own: false,
        }
    }

    pub fn prepare(
        &mut self,
        source: &T,
        maps: &[PrefixTree3; M],
        graph: &Rc<MorphismGraph>,
        retain_own: bool,
        work: &mut TransportWork,
    ) {
        if !work.full {
            work.full = self.retain_own != retain_own || self.graph.is_none();
            if !work.full {
                let previous = self.graph.as_ref().unwrap();
                if !Rc::ptr_eq(previous, graph) {
                    graph_additions(previous, graph, &mut work.morphisms);
                }
                source.changed_partitions(&self.source, &mut work.owners);
                for (current, previous) in maps.iter().zip(&self.maps) {
                    current.changed_partitions(previous, &mut work.morphisms);
                }
            }
        }
        self.source = source.clone();
        self.maps = maps.clone();
        self.graph = Some(Rc::clone(graph));
        self.retain_own = retain_own;
    }

    /// Commit only after saturating the graph without changing its edges or maps.
    pub fn finish(&mut self, source: &T) {
        self.source = source.clone();
    }
}

/// Checkpoints include the partial maps: a late image can transport old facts.
/// Sources, maps, and targets must only grow or undergo the same equality quotient.
pub struct TransportCheckpoint<T, const M: usize> {
    source: T,
    maps: [PrefixTree2; M],
    retain_own: bool,
}

impl<T: SnapshotSet, const M: usize> TransportCheckpoint<T, M> {
    pub fn new() -> Self {
        Self {
            source: T::empty(),
            maps: std::array::from_fn(|_| PrefixTree2::new()),
            retain_own: false,
        }
    }

    pub fn prepare(
        &mut self,
        source: &T,
        maps: &[PrefixTree2; M],
        retain_own: bool,
    ) -> (T, [PrefixTree2; M]) {
        let delta = if source.is_empty() || maps.iter().any(PrefixTree2::is_empty) {
            (T::empty(), std::array::from_fn(|_| PrefixTree2::new()))
        } else if self.retain_own == retain_own {
            (
                source.difference(&self.source),
                std::array::from_fn(|i| maps[i].difference(&self.maps[i])),
            )
        } else {
            (source.clone(), std::array::from_fn(|_| PrefixTree2::new()))
        };
        self.source = source.clone();
        self.maps = maps.clone();
        self.retain_own = retain_own;
        delta
    }
}
