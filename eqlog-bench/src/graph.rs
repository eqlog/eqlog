use std::collections::{BTreeSet, VecDeque};

use crate::Random;

#[derive(Clone, Debug)]
pub struct Graph {
    pub parents: Vec<Vec<usize>>,
    pub edges: Vec<(usize, usize)>,
}

impl Graph {
    pub fn new(parents: Vec<Vec<usize>>) -> Self {
        assert!(!parents.is_empty());
        let mut edges = Vec::new();
        for (target, sources) in parents.iter().enumerate() {
            assert!(sources.windows(2).all(|pair| pair[0] < pair[1]));
            for &source in sources {
                assert!(source < parents.len());
                edges.push((source, target));
            }
        }
        Self { parents, edges }
    }

    pub fn chain(vertices: usize) -> Self {
        Self::new(
            (0..vertices)
                .map(|owner| owner.checked_sub(1).into_iter().collect())
                .collect(),
        )
    }

    // Each component is consumed at most once, so member origins have unique
    // paths to a target without adding functionality or commutativity equations.
    pub fn merge(vertices: usize, seed: u64) -> Self {
        assert!(vertices > 0);
        let leaves = vertices / 2 + 1;
        let mut roots: Vec<_> = (0..leaves).collect();
        let mut parents = vec![Vec::new(); vertices];
        let mut random = Random::new(seed);
        random.shuffle(&mut roots);
        let mut roots: VecDeque<_> = roots.into();
        // Level-wise merges avoid rescanning fragmented carriers along an
        // unbalanced spine, which would obscure the intended COW baseline.
        for (owner, incoming) in parents.iter_mut().enumerate().skip(leaves) {
            let first = roots.pop_front().unwrap();
            let second = roots.pop_front().unwrap();
            *incoming = vec![first.min(second), first.max(second)];
            roots.push_back(owner);
        }
        Self::new(parents)
    }

    pub fn sparse(vertices: usize, fanin: usize, seed: u64) -> Self {
        assert!(vertices > 0 && fanin > 0);
        let mut random = Random::new(seed);
        let parents = (0..vertices)
            .map(|owner| {
                let count = fanin.min(owner);
                let mut selected = BTreeSet::new();
                // Floyd sampling avoids shuffling all earlier vertices when
                // only a bounded number of incoming edges is requested.
                for limit in owner - count..owner {
                    let candidate = random.below(limit + 1);
                    if !selected.insert(candidate) {
                        assert!(selected.insert(limit));
                    }
                }
                selected.into_iter().collect()
            })
            .collect();
        Self::new(parents)
    }

    pub fn dense(vertices: usize) -> Self {
        Self::new((0..vertices).map(|owner| (0..owner).collect()).collect())
    }

    pub fn cycle(vertices: usize) -> Self {
        assert!(vertices > 0);
        Self::new(
            (0..vertices)
                .map(|owner| vec![if owner == 0 { vertices - 1 } else { owner - 1 }])
                .collect(),
        )
    }

    // This deliberately independent traversal is an oracle, not timed work.
    pub fn ancestors(&self) -> Vec<BTreeSet<usize>> {
        (0..self.parents.len())
            .map(|owner| {
                let mut seen = BTreeSet::new();
                let mut pending = vec![owner];
                while let Some(node) = pending.pop() {
                    if seen.insert(node) {
                        pending.extend(self.parents[node].iter().copied());
                    }
                }
                seen
            })
            .collect()
    }
}
