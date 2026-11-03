use eqlog_runtime::{PrefixTree1, PrefixTree2};

use crate::{Case, Metrics, Workload};

use super::spec::{self, View};
use super::{Input, Partition};

eqlog_runtime::eqlog_mod!(recursive_model);
use recursive_model::{El, Key, RecursiveModel, World, WorldMor};

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub vertices: usize,
    pub keys: usize,
    pub depth: usize,
}

pub struct Recursive {
    input: Input,
}

pub fn case(params: &Params) -> Recursive {
    Recursive {
        input: Input::new(params.vertices, params.keys, params.depth),
    }
}

pub struct Native<'a> {
    input: &'a Input,
    model: RecursiveModel,
    worlds: Vec<World>,
    keys: Vec<Key>,
    arrows: Vec<WorldMor>,
    local: Vec<Vec<El>>,
}

impl Case for Recursive {
    type Native<'a> = Native<'a>;
    type Cow<'a> = Cow<'a>;

    fn native(&self) -> Self::Native<'_> {
        let input = &self.input;
        let mut model = RecursiveModel::new();
        model.enable_compact_world();
        let worlds: Vec<_> = (0..input.vertices).map(|_| model.new_world()).collect();
        let keys: Vec<_> = (0..input.keys).map(|_| model.new_key()).collect();
        let arrows = (1..input.vertices)
            .map(|owner| {
                let arrow = model.new_world_mor();
                model.insert_world_mor_dom(arrow, worlds[owner - 1]);
                model.insert_world_mor_cod(arrow, worlds[owner]);
                assert!(model.inherit_total_world_members(arrow));
                arrow
            })
            .collect();
        let local = worlds
            .iter()
            .map(|&world| {
                let mut local = Vec::with_capacity(input.width());
                for &key in &keys {
                    let chain: Vec<_> = (0..=input.depth).map(|_| model.new_el(world)).collect();
                    model.insert_from_ambient(world, key, chain[0]);
                    for edge in chain.windows(2) {
                        model.insert_next(world, edge[0], edge[1]);
                    }
                    local.extend(chain);
                }
                local
            })
            .collect();
        Native {
            input,
            model,
            worlds,
            keys,
            arrows,
            local,
        }
    }

    fn cow(&self) -> Self::Cow<'_> {
        let input = &self.input;
        let worlds = (0..input.vertices)
            .map(|owner| {
                let mut world = CowWorld {
                    members: PrefixTree1::new(),
                    items: PrefixTree2::new(),
                    next: PrefixTree2::new(),
                    partition: Partition::new(),
                };
                for key in 0..input.keys {
                    world
                        .items
                        .insert([u32::try_from(key).unwrap(), input.origin(owner, key, 0)]);
                    for level in 0..=input.depth {
                        let member = input.origin(owner, key, level);
                        world.members.insert([member]);
                        if level < input.depth {
                            world
                                .next
                                .insert([member, input.origin(owner, key, level + 1)]);
                        }
                    }
                }
                world
            })
            .collect();
        Cow {
            input,
            worlds,
            closed: false,
        }
    }
}

impl Workload for Native<'_> {
    fn close(&mut self) {
        self.model.close();
    }
    fn verify(&self) -> Metrics {
        spec::exact(
            self.model.iter_world().map(|world| world.0),
            (0..u32::try_from(self.input.vertices).unwrap()).collect(),
        );
        spec::exact(
            self.model.iter_key().map(|key| key.0),
            (0..u32::try_from(self.input.keys).unwrap()).collect(),
        );
        spec::exact(
            self.model.iter_world_mor().map(|arrow| arrow.0),
            (0..u32::try_from(self.input.vertices - 1).unwrap()).collect(),
        );
        spec::exact(
            self.model
                .iter_world_mor_dom()
                .map(|(arrow, world)| (arrow.0, world.0)),
            (0..u32::try_from(self.input.vertices - 1).unwrap())
                .map(|edge| (edge, edge))
                .collect(),
        );
        spec::exact(
            self.model
                .iter_world_mor_cod()
                .map(|(arrow, world)| (arrow.0, world.0)),
            (0..u32::try_from(self.input.vertices - 1).unwrap())
                .map(|edge| (edge, edge + 1))
                .collect(),
        );
        spec::verify(self, self.input)
    }
}

impl View for Native<'_> {
    type Member = u32;
    fn item(&self, owner: usize, key: u32) -> Option<u32> {
        self.model
            .from_ambient(self.worlds[owner], self.keys[key as usize])
            .map(|member| member.0)
    }
    fn next(&self, owner: usize, member: u32) -> Option<u32> {
        self.model
            .next(self.worlds[owner], El(member))
            .map(|member| member.0)
    }
    fn local_root(&self, owner: usize, key: usize, level: usize) -> u32 {
        self.model
            .root_el(self.local[owner][key * (self.input.depth + 1) + level])
            .0
    }
    fn image(&self, edge: usize, member: u32) -> Option<u32> {
        self.model
            .el_mor_app(self.arrows[edge], El(member))
            .map(|member| member.0)
    }
    fn items(&self) -> impl Iterator<Item = (usize, u32, u32)> {
        self.model
            .iter_from_ambient()
            .map(|(w, k, e)| (w.0 as usize, k.0, e.0))
    }
    fn next_rows(&self) -> impl Iterator<Item = (usize, u32, u32)> {
        self.model
            .iter_next()
            .map(|(w, x, y)| (w.0 as usize, x.0, y.0))
    }
    fn members(&self) -> impl Iterator<Item = (usize, u32)> {
        self.model
            .iter_world_member_el()
            .map(|(w, e)| (w.0 as usize, e.0))
    }
    fn globals(&self) -> impl Iterator<Item = u32> {
        self.model.iter_el().map(|e| e.0)
    }
    fn images(&self) -> impl Iterator<Item = (usize, u32, u32)> {
        self.model
            .iter_el_mor_app()
            .map(|(m, x, y)| (m.0 as usize, x.0, y.0))
    }
}

#[derive(Clone)]
struct CowWorld {
    members: PrefixTree1,
    items: PrefixTree2,
    next: PrefixTree2,
    partition: Partition,
}

fn singleton(values: &PrefixTree1) -> u32 {
    let mut rows = values.iter();
    let [value] = rows.next().unwrap();
    assert!(rows.next().is_none());
    value
}

pub struct Cow<'a> {
    input: &'a Input,
    worlds: Vec<CowWorld>,
    closed: bool,
}

impl Workload for Cow<'_> {
    fn close(&mut self) {
        if self.closed {
            return;
        }
        // Each fresh member participates in one collision. Following successors
        // costs O(N K (D + 1) log(2 + N K (D + 1))) across all snapshots.
        for owner in 1..self.worlds.len() {
            let local = self.worlds[owner].clone();
            let mut world = self.worlds[owner - 1].clone();
            world.members = world.members.union(&local.members);
            world.next = world.next.union(&local.next);
            let mut pending = Vec::with_capacity(self.input.keys);
            for [key, member] in local.items.iter() {
                let inherited = singleton(world.items.get(key).unwrap());
                pending.push((inherited, member));
            }
            while let Some((left, right)) = pending.pop() {
                let Some((loser, winner)) = world.partition.equate(left, right) else {
                    continue;
                };
                assert!(world.members.set.remove(&loser));
                let winner_next = world.next.get(winner).map(singleton);
                let loser_next = world.next.map.remove(&loser).as_ref().map(singleton);
                match (winner_next, loser_next) {
                    (Some(left), Some(right)) => pending.push((left, right)),
                    (None, None) => {}
                    (Some(_), None) | (None, Some(_)) => {
                        panic!("congruent chains have equal depth")
                    }
                }
            }
            self.worlds[owner] = world;
        }
        self.closed = true;
    }
    fn verify(&self) -> Metrics {
        for (owner, world) in self.worlds.iter().enumerate() {
            for origin in 0..(owner + 1) * self.input.width() {
                assert_eq!(
                    world.partition.root(u32::try_from(origin).unwrap()),
                    u32::try_from(origin % self.input.width()).unwrap()
                );
            }
        }
        spec::verify(self, self.input)
    }
}

impl View for Cow<'_> {
    type Member = (usize, u32);
    fn item(&self, owner: usize, key: u32) -> Option<Self::Member> {
        self.worlds[owner]
            .items
            .get(key)
            .map(|values| (owner, singleton(values)))
    }
    fn next(&self, owner: usize, member: Self::Member) -> Option<Self::Member> {
        assert_eq!(owner, member.0);
        self.worlds[owner]
            .next
            .get(member.1)
            .map(|values| (owner, singleton(values)))
    }
    fn local_root(&self, owner: usize, key: usize, level: usize) -> Self::Member {
        (
            owner,
            self.worlds[owner]
                .partition
                .root(self.input.origin(owner, key, level)),
        )
    }
    fn image(&self, edge: usize, member: Self::Member) -> Option<Self::Member> {
        assert_eq!(edge, member.0);
        Some((edge + 1, self.worlds[edge + 1].partition.root(member.1)))
    }
    fn items(&self) -> impl Iterator<Item = (usize, u32, Self::Member)> {
        self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .items
                .iter()
                .map(move |[key, member]| (owner, key, (owner, member)))
        })
    }
    fn next_rows(&self) -> impl Iterator<Item = (usize, Self::Member, Self::Member)> {
        self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .next
                .iter()
                .map(move |[x, y]| (owner, (owner, x), (owner, y)))
        })
    }
    fn members(&self) -> impl Iterator<Item = (usize, Self::Member)> {
        self.worlds.iter().enumerate().flat_map(|(owner, world)| {
            world
                .members
                .iter()
                .map(move |[member]| (owner, (owner, member)))
        })
    }
    fn globals(&self) -> impl Iterator<Item = Self::Member> {
        self.members().map(|(_, member)| member)
    }
    fn images(&self) -> impl Iterator<Item = (usize, Self::Member, Self::Member)> {
        self.worlds
            .iter()
            .enumerate()
            .take(self.worlds.len() - 1)
            .flat_map(move |(edge, world)| {
                world.members.iter().map(move |[member]| {
                    (
                        edge,
                        (edge, member),
                        (edge + 1, self.worlds[edge + 1].partition.root(member)),
                    )
                })
            })
    }
}
