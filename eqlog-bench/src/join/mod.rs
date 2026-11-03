use crate::{Case, Metrics, Random, Workload};

use self::spec::{Element, Evaluator, Inputs, Node, Role};

mod cow;
mod native;
mod spec;

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub vertices: usize,
    pub parents: usize,
    pub width: usize,
    pub members: usize,
    pub seed: u64,
}

#[derive(Clone, Copy)]
pub enum Variant {
    Fanout,
    Overlap,
    Split,
    Diamonds,
    Layered,
    Comb,
    Chain,
}

pub fn case(config: &Params, variant: Variant) -> JoinCase {
    JoinCase {
        input: generate(config, variant),
    }
}

pub struct JoinCase {
    input: Inputs,
}

impl Case for JoinCase {
    type Native<'a> = Run<'a, native::Native>;
    type Cow<'a> = Run<'a, cow::Cow>;

    fn native(&self) -> Self::Native<'_> {
        Run {
            input: &self.input,
            engine: native::Native::new(&self.input),
        }
    }

    fn cow(&self) -> Self::Cow<'_> {
        Run {
            input: &self.input,
            engine: cow::Cow::new(&self.input),
        }
    }
}

pub struct Run<'a, E> {
    input: &'a Inputs,
    engine: E,
}

impl<E: Evaluator> Workload for Run<'_, E> {
    fn close(&mut self) {
        self.engine.close();
    }

    fn verify(&self) -> Metrics {
        spec::verify(&self.engine, self.input)
    }
}

fn parents(owner: usize, config: &Params, variant: Variant, random: &mut Random) -> Vec<usize> {
    match variant {
        Variant::Fanout | Variant::Overlap | Variant::Split => {
            if owner < config.parents {
                Vec::new()
            } else {
                (0..config.parents).collect()
            }
        }
        Variant::Chain => owner.checked_sub(1).into_iter().collect(),
        Variant::Comb => match owner {
            0 => Vec::new(),
            1 => vec![0],
            _ => vec![0, owner - 1],
        },
        Variant::Diamonds => {
            if owner == 0 {
                Vec::new()
            } else if owner % 3 == 0 {
                vec![owner - 2, owner - 1]
            } else {
                vec![3 * ((owner - 1) / 3)]
            }
        }
        Variant::Layered => {
            let layer = owner / config.width;
            if layer == 0 {
                return Vec::new();
            }
            let mut prior: Vec<_> = ((layer - 1) * config.width..layer * config.width).collect();
            random.shuffle(&mut prior);
            prior.truncate(config.parents.min(prior.len()));
            prior.sort_unstable();
            prior
        }
    }
}

fn generate(config: &Params, variant: Variant) -> Inputs {
    assert!(config.vertices > 0 && config.parents > 0 && config.width > 0 && config.members > 0);
    let mut random = Random::new(config.seed);
    let mut nodes = Vec::with_capacity(config.vertices);
    let mut edges = Vec::new();
    let mut elements = Vec::new();
    for owner in 0..config.vertices {
        let incoming = parents(owner, config, variant, &mut random);
        edges.extend(incoming.iter().map(|&parent| (parent, owner)));
        let mut local = vec![(0, Role::Spare)];
        let (group, count, both_sides) = match variant {
            Variant::Fanout => (
                owner,
                usize::from(owner < config.parents) * config.members,
                true,
            ),
            Variant::Overlap => (
                owner % 2,
                usize::from(owner < config.parents) * config.members,
                true,
            ),
            Variant::Split => (
                0,
                usize::from(owner < config.parents) * config.members,
                false,
            ),
            Variant::Chain | Variant::Comb => (0, usize::from(owner == 0) * config.members, true),
            Variant::Diamonds => {
                let count = if owner == 0 {
                    config.members
                } else {
                    usize::from(owner % 3 != 0)
                };
                (owner / 6, count, true)
            }
            Variant::Layered => (
                owner % (config.width / 2).max(1),
                if owner < config.width {
                    config.members
                } else {
                    1
                },
                true,
            ),
        };
        let group = u32::try_from(group).unwrap();
        for _ in 0..count {
            if both_sides {
                local.push((group, Role::Left));
                local.push((group, Role::Right));
            } else {
                local.push((
                    group,
                    if owner % 2 == 0 {
                        Role::Left
                    } else {
                        Role::Right
                    },
                ));
            }
        }
        let local: Vec<_> = local
            .into_iter()
            .map(|(group, role)| {
                let origin = u32::try_from(elements.len()).unwrap();
                let element = Element {
                    origin,
                    key: origin,
                    group,
                    role,
                };
                elements.push(element);
                element
            })
            .collect();
        nodes.push(Node {
            parents: incoming,
            local,
        });
    }
    let mut keys: Vec<_> = (0..u32::try_from(elements.len()).unwrap()).collect();
    random.shuffle(&mut keys);
    let mut key_origins = vec![0; elements.len()];
    for node in &mut nodes {
        for element in &mut node.local {
            element.key = keys[element.origin as usize];
            elements[element.origin as usize] = *element;
            key_origins[element.key as usize] = element.origin;
        }
    }
    let groups = elements
        .iter()
        .map(|element| element.group as usize)
        .max()
        .unwrap()
        + 1;
    Inputs {
        nodes,
        edges,
        elements,
        key_origins,
        groups,
    }
}
