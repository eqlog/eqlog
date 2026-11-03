use std::collections::BTreeSet;

use crate::graph::Graph;

pub mod carrier;
pub mod from_ambient;
pub mod marking;
pub mod member_function;
pub mod member_predicate;
pub mod mixed_predicate;
pub mod to_ambient;
mod verify;

#[derive(Clone, Debug)]
pub struct Params {
    pub vertices: usize,
    pub members: usize,
    pub seed: u64,
}

struct Input {
    graph: Graph,
    members: usize,
}

impl Input {
    fn new(params: &Params, graph: Graph) -> Self {
        assert!(params.vertices > 0 && params.members > 0);
        assert_eq!(graph.parents.len(), params.vertices);
        u32::try_from(params.vertices.checked_mul(params.members).unwrap()).unwrap();
        let ancestors = graph.ancestors();
        for (owner, parents) in graph.parents.iter().enumerate() {
            let mut inherited = BTreeSet::new();
            for &parent in parents {
                assert!(parent < owner);
                for &ancestor in &ancestors[parent] {
                    assert!(
                        inherited.insert(ancestor),
                        "member propagation requires disjoint incoming ancestry"
                    );
                }
            }
        }
        Self {
            graph,
            members: params.members,
        }
    }

    fn member_count(&self) -> usize {
        self.graph.parents.len() * self.members
    }

    fn local(&self, owner: usize) -> impl Iterator<Item = u32> {
        let start = owner.checked_mul(self.members).unwrap();
        let end = start.checked_add(self.members).unwrap();
        (start..end).map(|origin| u32::try_from(origin).unwrap())
    }
}

pub fn carrier(params: &Params, graph: Graph) -> carrier::Benchmark {
    carrier::Benchmark::new(params, graph)
}

pub fn member_predicate(params: &Params, graph: Graph) -> member_predicate::Benchmark {
    member_predicate::Benchmark::new(params, graph)
}

pub fn mixed_predicate(params: &Params, graph: Graph) -> mixed_predicate::Benchmark {
    mixed_predicate::Benchmark::new(params, graph)
}

pub fn from_ambient(params: &Params, graph: Graph) -> from_ambient::Benchmark {
    from_ambient::Benchmark::new(params, graph)
}

pub fn to_ambient(params: &Params, graph: Graph) -> to_ambient::Benchmark {
    to_ambient::Benchmark::new(params, graph)
}

pub fn member_function(params: &Params, graph: Graph) -> member_function::Benchmark {
    member_function::Benchmark::new(params, graph)
}

pub fn marking(params: &Params, graph: Graph) -> marking::Benchmark {
    marking::Benchmark::new(params, graph)
}
