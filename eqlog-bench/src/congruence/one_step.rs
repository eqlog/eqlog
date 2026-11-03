use eqlog_runtime::{PrefixTree1, PrefixTree2};

use crate::{Case, Metrics, Workload};

use super::spec::{self, View};
use super::{Input, Partition};

eqlog_runtime::eqlog_mod!(one_step_model);
use one_step_model::{El, Key, OneStepModel, World, WorldMor};

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub vertices: usize,
    pub keys: usize,
}

pub struct OneStep {
    input: Input,
}

pub fn case(params: &Params) -> OneStep {
    OneStep {
        input: Input::new(params.vertices, params.keys, 0),
    }
}

pub struct Native<'a> {
    input: &'a Input,
    model: OneStepModel,
    worlds: Vec<World>,
    keys: Vec<Key>,
    arrows: Vec<WorldMor>,
    local: Vec<Vec<El>>,
}

impl Case for OneStep {
    type Native<'a> = Native<'a>;
    type Cow<'a> = Cow<'a>;

    fn native(&self) -> Self::Native<'_> {
        let input = &self.input;
        let mut model = OneStepModel::new();
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
                keys.iter()
                    .map(|&key| {
                        let member = model.new_el(world);
                        model.insert_from_ambient(world, key, member);
                        member
                    })
                    .collect()
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
                    partition: Partition::new(),
                };
                for key in 0..input.keys {
                    let member = input.origin(owner, key, 0);
                    world.members.insert([member]);
                    world.items.insert([u32::try_from(key).unwrap(), member]);
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
    fn next(&self, _owner: usize, _member: u32) -> Option<u32> {
        None
    }
    fn local_root(&self, owner: usize, key: usize, level: usize) -> u32 {
        assert_eq!(level, 0);
        self.model.root_el(self.local[owner][key]).0
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
        std::iter::empty()
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
    partition: Partition,
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
        for owner in 1..self.worlds.len() {
            let local = self.worlds[owner].clone();
            let mut world = self.worlds[owner - 1].clone();
            world.members = world.members.union(&local.members);
            for [key, member] in local.items.iter() {
                let [inherited] = world.items.get(key).unwrap().iter().next().unwrap();
                let (loser, _) = world.partition.equate(inherited, member).unwrap();
                assert!(world.members.set.remove(&loser));
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
        self.worlds[owner].items.get(key).map(|values| {
            let [member] = values.iter().next().unwrap();
            (owner, member)
        })
    }
    fn next(&self, _owner: usize, _member: Self::Member) -> Option<Self::Member> {
        None
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
        std::iter::empty()
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
