use eqlog_runtime::PrefixTree1;

use super::{verify, Input, Params};
use crate::graph::Graph;
use crate::{Case, Metrics, Workload};

eqlog_runtime::eqlog_mod!(carrier);
use carrier::Carrier;

pub struct Benchmark {
    input: Input,
}

impl Benchmark {
    pub fn new(params: &Params, graph: Graph) -> Self {
        let input = Input::new(params, graph);
        Self { input }
    }
}

impl Case for Benchmark {
    type Native<'a>
        = Native<'a>
    where
        Self: 'a;
    type Cow<'a>
        = Cow<'a>
    where
        Self: 'a;

    fn native(&self) -> Native<'_> {
        Native::new(self)
    }

    fn cow(&self) -> Cow<'_> {
        Cow::new(self)
    }
}

pub struct Native<'a> {
    case: &'a Benchmark,
    model: Carrier,
    local: Vec<Vec<u32>>,
}

impl<'a> Native<'a> {
    fn new(case: &'a Benchmark) -> Self {
        let input = &case.input;
        let mut model = Carrier::new();
        model.enable_compact_world();
        let worlds: Vec<_> = input
            .graph
            .parents
            .iter()
            .map(|_| model.new_world())
            .collect();
        for &(source, target) in &input.graph.edges {
            let morphism = model.new_world_mor();
            model.insert_world_mor_dom(morphism, worlds[source]);
            model.insert_world_mor_cod(morphism, worlds[target]);
            assert!(model.inherit_total_world_members(morphism));
        }
        let mut local = Vec::new();
        for (owner, &world) in worlds.iter().enumerate() {
            let mut members = Vec::new();
            for _ in input.local(owner) {
                let member = model.new_el(world);
                members.push(member.0);
            }
            local.push(members);
        }
        Self { case, model, local }
    }
}

impl Workload for Native<'_> {
    fn close(&mut self) {
        self.model.close();
    }

    fn verify(&self) -> Metrics {
        let input = &self.case.input;
        verify::topology(
            input,
            self.model.iter_world().map(|world| world.0),
            self.model.iter_world_mor().map(|morphism| morphism.0),
            self.model
                .iter_world_mor_dom()
                .map(|(morphism, world)| (morphism.0, world.0)),
            self.model
                .iter_world_mor_cod()
                .map(|(morphism, world)| (morphism.0, world.0)),
        );
        let members = verify::members(
            input,
            &self.local,
            self.model
                .iter_world_member_el()
                .map(|(owner, member)| (owner.0 as usize, member.0)),
            self.model.iter_el().map(|member| member.0),
            self.model
                .iter_el_mor_app()
                .map(|(edge, source, target)| (edge.0 as usize, source.0, target.0)),
        );
        members.metrics
    }
}

struct World {
    carrier: PrefixTree1,
}

pub struct Cow<'a> {
    case: &'a Benchmark,
    worlds: Vec<World>,
    closed: bool,
}

impl<'a> Cow<'a> {
    fn new(case: &'a Benchmark) -> Self {
        let input = &case.input;
        let worlds = (0..input.graph.parents.len())
            .map(|owner| {
                let mut world = World {
                    carrier: PrefixTree1::new(),
                };
                for origin in input.local(owner) {
                    world.carrier.insert([origin]);
                }
                world
            })
            .collect();
        Self {
            case,
            worlds,
            closed: false,
        }
    }
}

impl Workload for Cow<'_> {
    fn close(&mut self) {
        if self.closed {
            return;
        }
        for owner in 0..self.worlds.len() {
            let (previous, current) = self.worlds.split_at_mut(owner);
            let world = &mut current[0];
            for &parent in &self.case.input.graph.parents[owner] {
                world.carrier = world.carrier.union(&previous[parent].carrier);
            }
        }
        self.closed = true;
    }

    fn verify(&self) -> Metrics {
        let input = &self.case.input;
        let members = verify::cow_members(input, self.worlds.iter().map(|world| &world.carrier));
        members.metrics
    }
}
