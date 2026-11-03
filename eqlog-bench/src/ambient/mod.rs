use std::collections::BTreeSet;

use eqlog_runtime::{morphism_components, PrefixTree1, PrefixTree2};

use crate::graph::Graph;
use crate::{Case, Metrics, Workload};

eqlog_runtime::eqlog_mod!(propagation_model);
eqlog_runtime::eqlog_mod!(marking_model);

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub vertices: usize,
    pub members: usize,
}

struct Input {
    graph: Graph,
    members: usize,
    values: usize,
}

impl Input {
    fn new(params: &Params, graph: Graph) -> Self {
        assert!(params.vertices > 0 && params.members > 0);
        assert_eq!(params.vertices, graph.parents.len());
        let values = params.vertices.checked_mul(params.members).unwrap();
        u32::try_from(values).unwrap();
        Self {
            graph,
            members: params.members,
            values,
        }
    }

    fn local(&self, owner: usize) -> impl Iterator<Item = u32> + '_ {
        let start = owner * self.members;
        (start..start + self.members).map(|value| u32::try_from(value).unwrap())
    }

    fn expected(&self) -> BTreeSet<(usize, u32)> {
        self.graph
            .ancestors()
            .into_iter()
            .enumerate()
            .flat_map(|(owner, ancestors)| {
                ancestors
                    .into_iter()
                    .flat_map(move |source| self.local(source).map(move |value| (owner, value)))
            })
            .collect()
    }

    fn metrics(&self, expected: &BTreeSet<(usize, u32)>, relations: usize) -> Metrics {
        let mut checksum = 0xcbf29ce484222325_u64;
        for &(owner, value) in expected {
            for part in [owner as u64, u64::from(value)] {
                checksum ^= part;
                checksum = checksum.wrapping_mul(0x100000001b3);
            }
        }
        Metrics {
            worlds: self.graph.parents.len(),
            morphisms: self.graph.edges.len(),
            owned_elements: 0,
            local_size: relations * self.values,
            checksum,
        }
    }
}

fn exact<T: Ord + std::fmt::Debug>(rows: impl Iterator<Item = T>, expected: BTreeSet<T>) {
    let mut actual = BTreeSet::new();
    for row in rows {
        assert!(actual.insert(row), "duplicate public row");
    }
    assert_eq!(actual, expected);
}

fn check_rows(rows: impl Iterator<Item = (usize, u32)>, expected: &BTreeSet<(usize, u32)>) {
    let mut actual = BTreeSet::new();
    for row in rows {
        assert!(actual.insert(row), "duplicate public row");
    }
    assert_eq!(&actual, expected);
}

macro_rules! verify_carriers {
    ($model:expr, $input:expr) => {{
        let input = $input;
        exact(
            $model.iter_world().map(|world| world.0),
            (0..u32::try_from(input.graph.parents.len()).unwrap()).collect(),
        );
        exact(
            $model.iter_value().map(|value| value.0),
            (0..u32::try_from(input.values).unwrap()).collect(),
        );
        exact(
            $model.iter_world_mor().map(|arrow| arrow.0),
            (0..u32::try_from(input.graph.edges.len()).unwrap()).collect(),
        );
        exact(
            $model
                .iter_world_mor_dom()
                .map(|(arrow, world)| (arrow.0, world.0)),
            input
                .graph
                .edges
                .iter()
                .enumerate()
                .map(|(edge, &(source, _))| {
                    (u32::try_from(edge).unwrap(), u32::try_from(source).unwrap())
                })
                .collect(),
        );
        exact(
            $model
                .iter_world_mor_cod()
                .map(|(arrow, world)| (arrow.0, world.0)),
            input
                .graph
                .edges
                .iter()
                .enumerate()
                .map(|(edge, &(_, target))| {
                    (u32::try_from(edge).unwrap(), u32::try_from(target).unwrap())
                })
                .collect(),
        );
    }};
}

struct Transport {
    domains: PrefixTree2,
    codomains: PrefixTree2,
    objects: PrefixTree1,
}

impl Transport {
    fn new(input: &Input) -> Self {
        let mut domains = PrefixTree2::new();
        let mut codomains = PrefixTree2::new();
        let mut objects = PrefixTree1::new();
        for owner in 0..input.graph.parents.len() {
            objects.insert([u32::try_from(owner).unwrap()]);
        }
        for (edge, &(source, target)) in input.graph.edges.iter().enumerate() {
            let edge = u32::try_from(edge).unwrap();
            domains.insert([u32::try_from(source).unwrap(), edge]);
            codomains.insert([edge, u32::try_from(target).unwrap()]);
        }
        Self {
            domains,
            codomains,
            objects,
        }
    }

    fn close(&self, worlds: &mut [PrefixTree1]) {
        // Unioning an SCC's incoming and local rows closes the whole component
        // without propagating individual rows repeatedly around its cycles.
        for component in morphism_components(&self.domains, &self.codomains, &self.objects) {
            let mut rows = PrefixTree1::new();
            for &owner in &component.objects {
                rows = rows.union(&worlds[owner as usize]);
            }
            for &owner in &component.objects {
                worlds[owner as usize] = rows.clone();
            }
            for edge in component.outgoing {
                worlds[edge.cod as usize] = worlds[edge.cod as usize].union(&rows);
            }
        }
    }
}

fn local_rows(input: &Input) -> Vec<PrefixTree1> {
    (0..input.graph.parents.len())
        .map(|owner| {
            let mut rows = PrefixTree1::new();
            for value in input.local(owner) {
                rows.insert([value]);
            }
            rows
        })
        .collect()
}

pub struct Propagation {
    input: Input,
}

pub fn propagation(params: &Params, graph: Graph) -> Propagation {
    Propagation {
        input: Input::new(params, graph),
    }
}

pub struct NativePropagation<'a> {
    input: &'a Input,
    model: propagation_model::PropagationModel,
}

impl Case for Propagation {
    type Native<'a> = NativePropagation<'a>;
    type Cow<'a> = CowPropagation<'a>;

    fn native(&self) -> Self::Native<'_> {
        let input = &self.input;
        let mut model = propagation_model::PropagationModel::new();
        let worlds: Vec<_> = input
            .graph
            .parents
            .iter()
            .map(|_| model.new_world())
            .collect();
        let values: Vec<_> = (0..input.values).map(|_| model.new_value()).collect();
        for &(source, target) in &input.graph.edges {
            let edge = model.new_world_mor();
            model.insert_world_mor_dom(edge, worlds[source]);
            model.insert_world_mor_cod(edge, worlds[target]);
        }
        for (owner, &world) in worlds.iter().enumerate() {
            for value in input.local(owner) {
                model.insert_present(world, values[value as usize]);
            }
        }
        NativePropagation { input, model }
    }

    fn cow(&self) -> Self::Cow<'_> {
        CowPropagation {
            input: &self.input,
            worlds: local_rows(&self.input),
            transport: Transport::new(&self.input),
            closed: false,
        }
    }
}

impl Workload for NativePropagation<'_> {
    fn close(&mut self) {
        self.model.close();
    }

    fn verify(&self) -> Metrics {
        verify_carriers!(self.model, self.input);
        let expected = self.input.expected();
        check_rows(
            self.model
                .iter_present()
                .map(|(world, value)| (world.0 as usize, value.0)),
            &expected,
        );
        self.input.metrics(&expected, 1)
    }
}

pub struct CowPropagation<'a> {
    input: &'a Input,
    worlds: Vec<PrefixTree1>,
    transport: Transport,
    closed: bool,
}

impl Workload for CowPropagation<'_> {
    fn close(&mut self) {
        if self.closed {
            return;
        }
        self.transport.close(&mut self.worlds);
        self.closed = true;
    }

    fn verify(&self) -> Metrics {
        let expected = self.input.expected();
        check_rows(
            self.worlds
                .iter()
                .enumerate()
                .flat_map(|(owner, rows)| rows.iter().map(move |[value]| (owner, value))),
            &expected,
        );
        self.input.metrics(&expected, 1)
    }
}

pub struct Marking {
    input: Input,
}

pub fn marking(params: &Params, graph: Graph) -> Marking {
    Marking {
        input: Input::new(params, graph),
    }
}

pub struct NativeMarking<'a> {
    input: &'a Input,
    model: marking_model::MarkingModel,
}

impl Case for Marking {
    type Native<'a> = NativeMarking<'a>;
    type Cow<'a> = CowMarking<'a>;

    fn native(&self) -> Self::Native<'_> {
        let input = &self.input;
        let mut model = marking_model::MarkingModel::new();
        let worlds: Vec<_> = input
            .graph
            .parents
            .iter()
            .map(|_| model.new_world())
            .collect();
        let values: Vec<_> = (0..input.values).map(|_| model.new_value()).collect();
        for &(source, target) in &input.graph.edges {
            let edge = model.new_world_mor();
            model.insert_world_mor_dom(edge, worlds[source]);
            model.insert_world_mor_cod(edge, worlds[target]);
        }
        for (owner, &world) in worlds.iter().enumerate() {
            for value in input.local(owner) {
                model.insert_present(world, values[value as usize]);
            }
        }
        NativeMarking { input, model }
    }

    fn cow(&self) -> Self::Cow<'_> {
        CowMarking {
            input: &self.input,
            present: local_rows(&self.input),
            marked: vec![PrefixTree1::new(); self.input.graph.parents.len()],
            transport: Transport::new(&self.input),
            closed: false,
        }
    }
}

impl Workload for NativeMarking<'_> {
    fn close(&mut self) {
        self.model.close();
    }

    fn verify(&self) -> Metrics {
        verify_carriers!(self.model, self.input);
        let expected = self.input.expected();
        check_rows(
            self.model
                .iter_present()
                .map(|(world, value)| (world.0 as usize, value.0)),
            &expected,
        );
        check_rows(
            self.model
                .iter_marked()
                .map(|(world, value)| (world.0 as usize, value.0)),
            &expected,
        );
        self.input.metrics(&expected, 2)
    }
}

pub struct CowMarking<'a> {
    input: &'a Input,
    present: Vec<PrefixTree1>,
    marked: Vec<PrefixTree1>,
    transport: Transport,
    closed: bool,
}

impl Workload for CowMarking<'_> {
    fn close(&mut self) {
        if self.closed {
            return;
        }
        self.transport.close(&mut self.present);
        // The rule preserves its argument, so the completed result can share
        // the entire input tree instead of allocating one output row at a time.
        self.marked.clone_from(&self.present);
        self.closed = true;
    }

    fn verify(&self) -> Metrics {
        let expected = self.input.expected();
        for worlds in [&self.present, &self.marked] {
            check_rows(
                worlds
                    .iter()
                    .enumerate()
                    .flat_map(|(owner, rows)| rows.iter().map(move |[value]| (owner, value))),
                &expected,
            );
        }
        self.input.metrics(&expected, 2)
    }
}
