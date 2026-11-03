use super::spec::{oracle, Inputs, Metrics, Node, Operation, SEED};
use eqlog_runtime::{PrefixTree1, PrefixTree2};

#[derive(Clone)]
struct World {
    carrier: PrefixTree1,
    item: PrefixTree2,
    marked: PrefixTree1,
}

fn singleton(tree: &PrefixTree1) -> u32 {
    let mut iter = tree.iter();
    let [value] = iter.next().unwrap();
    assert!(iter.next().is_none(), "item must be functional");
    value
}

impl World {
    fn empty() -> Self {
        Self {
            carrier: PrefixTree1::new(),
            item: PrefixTree2::new(),
            marked: PrefixTree1::new(),
        }
    }

    fn lookup(&self, key: u32) -> u32 {
        singleton(self.item.get(key).unwrap())
    }

    fn add_local(&mut self, key: u32, element: u32) {
        assert!(self.carrier.insert([element]));
        assert!(self.item.insert([key, element]));
    }

    fn union_from(&mut self, other: &Self) {
        // A single origin per key makes functionality checks unnecessary.
        self.carrier = self.carrier.union(&other.carrier);
        self.item = self.item.union(&other.item);
        self.marked = self.marked.union(&other.marked);
    }

    fn add_node(&mut self, owner: usize, node: &Node) {
        if owner == 0 {
            for key in 0..SEED {
                self.add_local(key, key);
            }
        }
        self.add_local(node.output, SEED + owner as u32);
    }

    fn apply_rule(&mut self, node: &Node) {
        let ready = match node.operation {
            Operation::Job { input } => {
                let input = self.lookup(input);
                self.marked.contains([input])
            }
            Operation::Join { left, right } => {
                let left = self.lookup(left);
                let right = self.lookup(right);
                self.marked.contains([left]) && self.marked.contains([right])
            }
        };
        if ready {
            let output = self.lookup(node.output);
            self.marked.insert([output]);
        }
    }

    fn mark_seeds(&mut self, seed_mask: u32) {
        for key in 0..SEED {
            if seed_mask & (1 << key) != 0 {
                let element = self.lookup(key);
                self.marked.insert([element]);
            }
        }
    }
}

pub struct Engine {
    worlds: Vec<World>,
}

impl Engine {
    pub fn construct(inputs: &Inputs) -> Self {
        let worlds = inputs
            .nodes
            .iter()
            .enumerate()
            .map(|(owner, node)| {
                let mut world = World::empty();
                world.add_node(owner, node);
                world
            })
            .collect();
        Self { worlds }
    }

    pub fn mark_seeds(&mut self, seed_mask: u32) {
        self.worlds[0].mark_seeds(seed_mask);
    }

    pub fn close(&mut self, inputs: &Inputs) {
        // Input validation guarantees every parent precedes its child.
        for owner in 0..self.worlds.len() {
            let node = &inputs.nodes[owner];
            let mut world = self.worlds[owner].clone();
            for &parent in &node.parents {
                world.union_from(&self.worlds[parent]);
            }
            world.apply_rule(node);
            self.worlds[owner] = world;
        }
    }
}

pub fn verify(engine: &Engine, inputs: &Inputs, seed_mask: u32) -> Metrics {
    let expected = oracle(inputs, seed_mask);
    assert_eq!(engine.worlds.len(), inputs.nodes.len());
    for (owner, world) in engine.worlds.iter().enumerate() {
        assert!(
            world
                .carrier
                .iter()
                .eq(expected.origins(owner).map(|origin| [origin])),
            "carrier mismatch at {owner}"
        );
        assert!(
            world.item.iter().eq(expected
                .keys(owner)
                .map(|key| [key, inputs.key_origin(key)])),
            "item mismatch at {owner}"
        );
        assert!(
            world
                .marked
                .iter()
                .eq(expected.marked_origins(owner).map(|origin| [origin])),
            "marked mismatch at {owner}"
        );
    }
    for &(source, target) in &inputs.edges {
        for [key, element] in engine.worlds[source].item.iter() {
            assert!(engine.worlds[source].carrier.contains([element]));
            let image = engine.worlds[target].lookup(key);
            assert!(engine.worlds[target].carrier.contains([image]));
            if engine.worlds[source].marked.contains([element]) {
                assert!(engine.worlds[target].marked.contains([image]));
            }
        }
    }
    expected.metrics()
}
