use super::spec::View;
use super::{Evaluator, Inputs, Job, SEEDS};
use eqlog_runtime::wbtree::map::WBTreeMap;
use eqlog_runtime::{PrefixTree1, PrefixTree2};

#[derive(Clone, Copy)]
struct Parent {
    origin: u32,
    rank: u32,
}

#[derive(Clone)]
struct Partition {
    parents: WBTreeMap<Parent>,
}

impl Partition {
    fn new() -> Self {
        Self {
            parents: WBTreeMap::new(),
        }
    }

    fn root(&self, mut origin: u32) -> u32 {
        while let Some(parent) = self.parents.get(&origin) {
            if parent.origin == origin {
                break;
            }
            origin = parent.origin;
        }
        origin
    }

    fn equate(&mut self, lhs: u32, rhs: u32) -> (u32, u32) {
        let mut winner = self.root(lhs);
        let mut loser = self.root(rhs);
        assert_ne!(
            winner, loser,
            "each equation identifies distinct inherited classes"
        );
        let mut winner_rank = self.parents.get(&winner).map_or(0, |parent| parent.rank);
        let mut loser_rank = self.parents.get(&loser).map_or(0, |parent| parent.rank);
        if winner_rank < loser_rank {
            std::mem::swap(&mut winner, &mut loser);
            std::mem::swap(&mut winner_rank, &mut loser_rank);
        }
        self.parents.insert(
            loser,
            Parent {
                origin: winner,
                rank: loser_rank,
            },
        );
        if winner_rank == loser_rank {
            self.parents.insert(
                winner,
                Parent {
                    origin: winner,
                    rank: winner_rank + 1,
                },
            );
        }
        (loser, winner)
    }
}

#[derive(Clone)]
struct World {
    carrier: PrefixTree1,
    item: PrefixTree2,
    marked: PrefixTree1,
    partition: Partition,
}

impl World {
    fn empty() -> Self {
        Self {
            carrier: PrefixTree1::new(),
            item: PrefixTree2::new(),
            marked: PrefixTree1::new(),
            partition: Partition::new(),
        }
    }

    fn add_local(&mut self, key: u32, origin: u32) {
        assert!(self.carrier.insert([origin]));
        assert!(self.item.insert([key, origin]));
    }

    fn lookup(&self, key: u32) -> Option<u32> {
        let mut values = self.item.get(key)?.iter();
        let [origin] = values.next().unwrap();
        assert!(values.next().is_none());
        Some(self.partition.root(origin))
    }

    fn apply(&mut self, job: Job, equation: bool) {
        if !self.marked.contains([self.lookup(job.input).unwrap()]) {
            return;
        }
        assert!(self.marked.insert([self.lookup(job.output).unwrap()]));
        if equation {
            let left = self.lookup(job.left).unwrap();
            let right = self.lookup(job.right).unwrap();
            let (loser, winner) = self.partition.equate(left, right);
            assert!(self.carrier.set.remove(&loser));
            if self.marked.set.remove(&loser) {
                self.marked.insert([winner]);
            }
        }
    }
}

pub struct Engine<const EQUATION: bool> {
    local: Vec<World>,
    worlds: Vec<World>,
    jobs: Vec<Job>,
    closed: bool,
}

impl<const EQUATION: bool> Engine<EQUATION> {
    pub fn construct(inputs: &Inputs, mask: u32) -> Self {
        let local: Vec<_> = inputs
            .jobs
            .iter()
            .enumerate()
            .map(|(owner, job)| {
                let mut world = World::empty();
                let start = if owner == 0 { 0 } else { job.output };
                for key in start..=job.output {
                    world.add_local(key, key);
                }
                world
            })
            .collect();
        let mut engine = Self {
            worlds: local.clone(),
            local,
            jobs: inputs.jobs.clone(),
            closed: false,
        };
        engine.mark_seeds(mask);
        engine
    }

    fn mark_seeds(&mut self, mask: u32) {
        for origin in 0..SEEDS {
            if mask & (1 << origin) != 0 {
                self.local[0].marked.insert([origin]);
                self.worlds[0].marked.insert([origin]);
            }
        }
        self.closed = false;
    }
}

impl<const EQUATION: bool> Evaluator for Engine<EQUATION> {
    fn close(&mut self) {
        if self.closed {
            return;
        }
        for owner in 0..self.worlds.len() {
            let local = &self.local[owner];
            let mut world = if owner == 0 {
                local.clone()
            } else {
                let inherited = &self.worlds[owner - 1];
                World {
                    carrier: inherited.carrier.union(&local.carrier),
                    item: inherited.item.union(&local.item),
                    marked: inherited.marked.union(&local.marked),
                    partition: inherited.partition.clone(),
                }
            };
            world.apply(self.jobs[owner], EQUATION);
            self.worlds[owner] = world;
        }
        self.closed = true;
    }
}

impl<const EQUATION: bool> View for Engine<EQUATION> {
    type Member = (usize, u32);

    fn world_count(&self) -> usize {
        self.worlds.len()
    }

    fn item_rows(&self) -> Box<dyn Iterator<Item = (usize, u32, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .item
                .iter()
                .map(move |[key, origin]| (owner, key, (owner, world.partition.root(origin))))
        }))
    }

    fn members(&self) -> Box<dyn Iterator<Item = (usize, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .carrier
                .iter()
                .map(move |[origin]| (owner, (owner, origin)))
        }))
    }

    fn global_members(&self) -> Box<dyn Iterator<Item = Self::Member> + '_> {
        Box::new(self.members().map(|(_, member)| member))
    }

    fn marks(&self) -> Box<dyn Iterator<Item = (usize, Self::Member)> + '_> {
        Box::new(self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .marked
                .iter()
                .map(move |[origin]| (owner, (owner, origin)))
        }))
    }

    fn lookup(&self, owner: usize, key: u32) -> Option<Self::Member> {
        self.worlds[owner].lookup(key).map(|origin| (owner, origin))
    }

    fn image(&self, edge: usize, source: Self::Member) -> Option<Self::Member> {
        if source.0 != edge || !self.closed || !self.worlds[edge].carrier.contains([source.1]) {
            return None;
        }
        let target = &self.worlds[edge + 1];
        Some((edge + 1, target.partition.root(source.1)))
    }

    fn image_rows(&self) -> Box<dyn Iterator<Item = (usize, Self::Member, Self::Member)> + '_> {
        if !self.closed {
            return Box::new(std::iter::empty());
        }
        Box::new(
            self.worlds[..self.worlds.len() - 1]
                .iter()
                .enumerate()
                .flat_map(move |(edge, source)| {
                    let target = &self.worlds[edge + 1];
                    source.carrier.iter().map(move |[origin]| {
                        (
                            edge,
                            (edge, origin),
                            (edge + 1, target.partition.root(origin)),
                        )
                    })
                }),
        )
    }
}
