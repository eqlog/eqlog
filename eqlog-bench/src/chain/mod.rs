use std::collections::BTreeSet;

use crate::{Case, Metrics, Random, Workload};

mod cow;
mod native;
mod spec;

const SEEDS: u32 = 8;

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub vertices: usize,
    pub seed: u64,
    pub seed_mask: u32,
}

impl Default for Params {
    fn default() -> Self {
        Self {
            vertices: 64,
            seed: 17,
            seed_mask: 255,
        }
    }
}

#[derive(Clone, Copy)]
struct Job {
    input: u32,
    output: u32,
    left: u32,
    right: u32,
}

struct Inputs {
    jobs: Vec<Job>,
}

pub struct Chain<const EQUATION: bool> {
    inputs: Inputs,
    mask: u32,
}

trait Evaluator: spec::View {
    fn close(&mut self);
}

pub struct Fixture<'a, E, const EQUATION: bool> {
    engine: E,
    chain: &'a Chain<EQUATION>,
}

impl<E: Evaluator, const EQUATION: bool> Workload for Fixture<'_, E, EQUATION> {
    fn close(&mut self) {
        self.engine.close();
    }

    fn verify(&self) -> Metrics {
        spec::verify(&self.engine, &self.chain.inputs, self.chain.mask, EQUATION)
    }
}

impl Case for Chain<false> {
    type Native<'a> = Fixture<'a, native::plain::Engine, false>;
    type Cow<'a> = Fixture<'a, cow::Engine<false>, false>;

    fn native(&self) -> Self::Native<'_> {
        Fixture {
            engine: native::plain::Engine::construct(&self.inputs, self.mask),
            chain: self,
        }
    }

    fn cow(&self) -> Self::Cow<'_> {
        Fixture {
            engine: cow::Engine::construct(&self.inputs, self.mask),
            chain: self,
        }
    }
}

impl Case for Chain<true> {
    type Native<'a> = Fixture<'a, native::equation::Engine, true>;
    type Cow<'a> = Fixture<'a, cow::Engine<true>, true>;

    fn native(&self) -> Self::Native<'_> {
        Fixture {
            engine: native::equation::Engine::construct(&self.inputs, self.mask),
            chain: self,
        }
    }

    fn cow(&self) -> Self::Cow<'_> {
        Fixture {
            engine: cow::Engine::construct(&self.inputs, self.mask),
            chain: self,
        }
    }
}

pub fn plain(params: &Params) -> Chain<false> {
    generate(params)
}

pub fn equation(params: &Params) -> Chain<true> {
    generate(params)
}

fn generate<const EQUATION: bool>(config: &Params) -> Chain<EQUATION> {
    assert_eq!(config.seed_mask >> SEEDS, 0);
    assert!(config.vertices > 0);
    let end = SEEDS
        .checked_add(u32::try_from(config.vertices).unwrap())
        .unwrap();
    let mut random = Random::new(config.seed);
    let mut classes: BTreeSet<_> = (0..SEEDS).collect();
    let mut jobs = Vec::with_capacity(config.vertices);
    for output in SEEDS..end {
        let input = u32::try_from(random.below(output as usize)).unwrap();
        let inherited: Vec<_> = classes.iter().copied().collect();
        let left_index = random.below(inherited.len());
        let right_index = (left_index + 1 + random.below(inherited.len() - 1)) % inherited.len();
        let left = inherited[left_index];
        let right = inherited[right_index];
        jobs.push(Job {
            input,
            output,
            left,
            right,
        });
        // Choosing distinct classes after every possible equation also keeps
        // them distinct when a partial seed mask enables only some equations.
        assert!(classes.remove(&left.max(right)));
        assert!(classes.insert(output));
    }
    Chain {
        inputs: Inputs { jobs },
        mask: config.seed_mask,
    }
}
