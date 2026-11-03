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

pub use carrier::case as carrier;
pub use from_ambient::case as from_ambient;
pub use marking::case as marking;
pub use member_function::case as member_function;
pub use member_predicate::case as member_predicate;
pub use mixed_predicate::case as mixed_predicate;
pub use to_ambient::case as to_ambient;

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
