use std::collections::BTreeSet;

use crate::{Case, Config, Engine, Metrics, Random, Workload};

mod cow;
mod native;
mod spec;

const SEEDS: u32 = 8;

#[derive(Clone, Copy)]
pub enum Variant {
    Plain,
    Equation,
}

impl Variant {
    fn equation(self) -> bool {
        match self {
            Self::Plain => false,
            Self::Equation => true,
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

struct Chain {
    inputs: Inputs,
    variant: Variant,
    mask: u32,
}

trait Evaluator: spec::View {
    fn close(&mut self);
}

struct Fixture<'a, E> {
    engine: E,
    chain: &'a Chain,
}

impl<E: Evaluator> Workload for Fixture<'_, E> {
    fn close(&mut self) {
        self.engine.close();
    }

    fn verify(&self) -> Metrics {
        spec::verify(
            &self.engine,
            &self.chain.inputs,
            self.chain.mask,
            self.chain.variant.equation(),
        )
    }
}

impl Chain {
    fn fixture<E: Evaluator + 'static>(&self, engine: E) -> Box<dyn Workload + '_> {
        Box::new(Fixture {
            engine,
            chain: self,
        })
    }
}

impl Case for Chain {
    fn prepare(&self, engine: Engine) -> Box<dyn Workload + '_> {
        match (engine, self.variant) {
            (Engine::Native, Variant::Plain) => {
                self.fixture(native::plain::Engine::construct(&self.inputs, self.mask))
            }
            (Engine::Native, Variant::Equation) => {
                self.fixture(native::equation::Engine::construct(&self.inputs, self.mask))
            }
            (Engine::Cow, Variant::Plain) => {
                self.fixture(cow::Engine::<false>::construct(&self.inputs, self.mask))
            }
            (Engine::Cow, Variant::Equation) => {
                self.fixture(cow::Engine::<true>::construct(&self.inputs, self.mask))
            }
        }
    }
}

pub fn case(config: &Config, variant: Variant) -> Box<dyn Case> {
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
    Box::new(Chain {
        inputs: Inputs { jobs },
        variant,
        mask: config.seed_mask,
    })
}
