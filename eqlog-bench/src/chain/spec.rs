use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::iter::Peekable;

use crate::Metrics;

use super::{Inputs, Job, SEEDS};

pub trait View {
    type Member: Copy + Debug + Ord;
    fn world_count(&self) -> usize;
    fn item_rows(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_>;
    fn members(&self) -> Box<dyn Iterator<Item = (usize, Self::Member)> + '_>;
    fn global_members(&self) -> Box<dyn Iterator<Item = Self::Member> + '_>;
    fn marks(&self) -> Box<dyn Iterator<Item = (usize, Self::Member)> + '_>;
    fn lookup(&self, owner: usize, key: u32) -> Option<Self::Member>;
    fn image(&self, edge: usize, source: Self::Member) -> Option<Self::Member>;
    fn image_rows(&self) -> Box<dyn Iterator<Item = (usize, Self::Member, Self::Member)> + '_>;
}

fn owner_rows<M: Copy + Debug + Ord>(
    rows: &mut Peekable<Box<dyn Iterator<Item = (usize, M)> + '_>>,
    owner: usize,
) -> BTreeSet<M> {
    let mut values = BTreeSet::new();
    while rows.peek().is_some_and(|&(next, _)| next == owner) {
        assert!(values.insert(rows.next().unwrap().1));
    }
    if let Some(&(next, _)) = rows.peek() {
        assert!(next > owner, "owner enumeration is ordered");
    }
    values
}

struct Oracle {
    roots: Vec<u32>,
    marked: BTreeSet<u32>,
}

impl Oracle {
    fn new(mask: u32) -> Self {
        Self {
            roots: (0..SEEDS).collect(),
            marked: (0..SEEDS).filter(|key| mask & (1 << key) != 0).collect(),
        }
    }

    fn apply(&mut self, job: Job, equation: bool) -> bool {
        assert_eq!(self.roots.len(), job.output as usize);
        self.roots.push(job.output);
        if !self.marked.contains(&self.roots[job.input as usize]) {
            return false;
        }
        assert!(self.marked.insert(job.output));
        if equation {
            let left = self.roots[job.left as usize];
            let right = self.roots[job.right as usize];
            assert_ne!(
                left, right,
                "each active equation merges new inherited classes"
            );
            let winner = left.min(right);
            let loser = left.max(right);
            for root in &mut self.roots {
                if *root == loser {
                    *root = winner;
                }
            }
            if self.marked.remove(&loser) {
                self.marked.insert(winner);
            }
        }
        true
    }
}

pub fn verify<V: View>(engine: &V, inputs: &Inputs, mask: u32, equation: bool) -> Metrics {
    assert_eq!(engine.world_count(), inputs.jobs.len());
    let mut items = engine.item_rows();
    let mut members = engine.members().peekable();
    let mut marks = engine.marks().peekable();
    let mut actual_images = engine.image_rows().peekable();
    let mut oracle = Oracle::new(mask);
    let mut previous = BTreeMap::new();
    let mut global = BTreeSet::new();
    let mut productive = 0;
    let mut checksum = 0xcbf29ce484222325u64;
    for (owner, &job) in inputs.jobs.iter().enumerate() {
        productive += usize::from(oracle.apply(job, equation));
        let mut classes = BTreeMap::new();
        let mut inverse = BTreeMap::new();
        for (key, &expected) in oracle.roots.iter().enumerate() {
            let (actual_owner, actual_key, actual) = items.next().unwrap();
            assert_eq!((actual_owner, actual_key as usize), (owner, key));
            if let Some(old) = classes.insert(expected, actual) {
                assert_eq!(old, actual, "missing equality at owner {owner}");
            }
            if let Some(old) = inverse.insert(actual, expected) {
                assert_eq!(old, expected, "unexpected equality at owner {owner}");
            }
            for value in [owner as u64, key as u64, u64::from(expected)] {
                checksum ^= value;
                checksum = checksum.wrapping_mul(0x100000001b3);
            }
        }
        let expected_members: BTreeSet<_> = classes.values().copied().collect();
        assert_eq!(owner_rows(&mut members, owner), expected_members);
        for &member in &expected_members {
            assert!(
                global.insert(member),
                "different owners retain different member identities"
            );
        }
        let expected_marks: BTreeSet<_> = oracle.marked.iter().map(|root| classes[root]).collect();
        assert_eq!(owner_rows(&mut marks, owner), expected_marks);
        for key in [job.input, job.output, job.left, job.right] {
            assert_eq!(
                engine.lookup(owner, key),
                Some(classes[&oracle.roots[key as usize]])
            );
        }
        if owner > 0 {
            let mut expected_rows = BTreeSet::new();
            for (&source_root, &source) in &previous {
                let expected = classes[&oracle.roots[source_root as usize]];
                assert_eq!(engine.image(owner - 1, source), Some(expected));
                assert!(expected_rows.insert((source, expected)));
            }
            let mut actual_rows = BTreeSet::new();
            while actual_images
                .peek()
                .is_some_and(|&(edge, _, _)| edge == owner - 1)
            {
                let (_, source, target) = actual_images.next().unwrap();
                assert!(
                    actual_rows.insert((source, target)),
                    "duplicate enumerated image"
                );
            }
            if let Some(&(edge, _, _)) = actual_images.peek() {
                assert!(edge > owner - 1, "image edges are ordered");
            }
            assert_eq!(
                actual_rows, expected_rows,
                "enumerated images differ before owner {owner}"
            );
        }
        previous = classes;
    }
    assert!(items.next().is_none());
    assert!(members.next().is_none());
    assert!(marks.next().is_none());
    let actual_global: Vec<_> = engine.global_members().collect();
    assert_eq!(actual_global.len(), global.len());
    assert_eq!(actual_global.into_iter().collect::<BTreeSet<_>>(), global);
    assert!(actual_images.next().is_none());
    let vertices = inputs.jobs.len();
    let local_members = SEEDS as usize + vertices;
    Metrics {
        worlds: vertices,
        morphisms: vertices - 1,
        owned_elements: local_members,
        local_size: 2 * local_members + (mask & 255).count_ones() as usize + productive,
        checksum,
    }
}
