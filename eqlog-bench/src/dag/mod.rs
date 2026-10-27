use crate::{Case, Config, Engine, Metrics, Random, Workload};

use self::spec::{Inputs, Node, Operation, SEED};

mod cow;
mod native;
mod spec;

#[derive(Clone, Copy)]
pub enum Variant {
    Forward,
    Layered,
    Wide,
    Comb,
    Chain,
}

fn sample(random: &mut Random, start: usize, end: usize, count: usize) -> Vec<usize> {
    let mut values: Vec<_> = (start..end).collect();
    random.shuffle(&mut values);
    values.truncate(count.min(values.len()));
    values.sort_unstable();
    values
}

fn generate(config: &Config, variant: Variant) -> Inputs {
    assert!(config.vertices > 0 && config.parents > 0 && config.width > 0);
    let bound = SEED
        .checked_add(u32::try_from(config.vertices).unwrap())
        .unwrap();
    let mut random = Random::new(config.seed);
    let mut outputs: Vec<_> = (SEED..bound).collect();
    random.shuffle(&mut outputs);
    let words = (bound as usize).div_ceil(64);
    let mut ancestors: Vec<Vec<u64>> = Vec::with_capacity(config.vertices);
    let mut nodes = Vec::with_capacity(config.vertices);
    for owner in 0..config.vertices {
        let parents = if owner == 0 {
            Vec::new()
        } else {
            match variant {
                Variant::Forward => sample(&mut random, 0, owner, config.parents),
                Variant::Layered => {
                    let layer = (owner - 1) / config.width;
                    if layer == 0 {
                        vec![0]
                    } else {
                        let start = 1 + (layer - 1) * config.width;
                        sample(&mut random, start, start + config.width, config.parents)
                    }
                }
                Variant::Wide => {
                    if owner + 1 == config.vertices && owner > 1 {
                        (1..owner).collect()
                    } else {
                        vec![0]
                    }
                }
                Variant::Comb => {
                    if owner == 1 {
                        vec![0]
                    } else {
                        vec![0, owner - 1]
                    }
                }
                Variant::Chain => vec![owner - 1],
            }
        };
        let mut inherited = vec![0_u64; words];
        inherited[0] = (1 << SEED) - 1;
        for &parent in &parents {
            for (word, source) in inherited.iter_mut().zip(&ancestors[parent]) {
                *word |= source;
            }
        }
        let operation = if parents.len() < 2 {
            let count = inherited
                .iter()
                .map(|word| word.count_ones() as usize)
                .sum();
            let mut nth = random.below(count);
            let mut origin = None;
            for (index, &word) in inherited.iter().enumerate() {
                let count = word.count_ones() as usize;
                if nth >= count {
                    nth -= count;
                    continue;
                }
                let mut remaining = word;
                for _ in 0..nth {
                    remaining &= remaining - 1;
                }
                origin = Some(u32::try_from(index * 64).unwrap() + remaining.trailing_zeros());
                break;
            }
            let origin = origin.unwrap();
            let input = if origin < SEED {
                origin
            } else {
                outputs[(origin - SEED) as usize]
            };
            Operation::Job { input }
        } else {
            let left = random.below(parents.len());
            let mut right = random.below(parents.len() - 1);
            if right >= left {
                right += 1;
            }
            Operation::Join {
                left: outputs[parents[left]],
                right: outputs[parents[right]],
            }
        };
        let origin = SEED as usize + owner;
        inherited[origin / 64] |= 1 << (origin % 64);
        ancestors.push(inherited);
        nodes.push(Node {
            parents,
            operation,
            output: outputs[owner],
        });
    }
    Inputs::new(nodes)
}

struct DagCase {
    inputs: Inputs,
    seed_mask: u32,
}

enum Evaluator {
    Native(native::Engine),
    Cow(cow::Engine),
}

struct DagWorkload<'a> {
    evaluator: Evaluator,
    case: &'a DagCase,
}

impl Case for DagCase {
    fn prepare(&self, engine: Engine) -> Box<dyn Workload + '_> {
        let evaluator = match engine {
            Engine::Native => {
                let mut model = native::Engine::construct(&self.inputs);
                model.mark_seeds(self.seed_mask);
                Evaluator::Native(model)
            }
            Engine::Cow => {
                let mut model = cow::Engine::construct(&self.inputs);
                model.mark_seeds(self.seed_mask);
                Evaluator::Cow(model)
            }
        };
        Box::new(DagWorkload {
            evaluator,
            case: self,
        })
    }
}

impl Workload for DagWorkload<'_> {
    fn close(&mut self) {
        match &mut self.evaluator {
            Evaluator::Native(model) => model.close(),
            Evaluator::Cow(model) => {
                model.close(&self.case.inputs);
            }
        }
    }

    fn verify(&self) -> Metrics {
        let inputs = &self.case.inputs;
        let mask = self.case.seed_mask;
        let metrics = match &self.evaluator {
            Evaluator::Native(model) => model.verify(inputs, mask),
            Evaluator::Cow(model) => cow::verify(model, inputs, mask),
        };
        Metrics {
            worlds: metrics.vertices,
            morphisms: metrics.edges,
            owned_elements: metrics.local_members,
            local_size: metrics.local_contribution_size,
            checksum: metrics.checksum,
        }
    }
}

pub fn case(config: &Config, variant: Variant) -> Box<dyn Case> {
    assert_eq!(config.seed_mask >> SEED, 0);
    Box::new(DagCase {
        inputs: generate(config, variant),
        seed_mask: config.seed_mask,
    })
}
