use super::spec::{oracle, Inputs, Metrics, Node, Operation, SEED};
use eqlog_runtime::{PrefixTree1, PrefixTree2};
use std::collections::{BTreeMap, VecDeque};

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

fn root(parent: &BTreeMap<u32, u32>, mut value: u32) -> u32 {
    while let Some(&next) = parent.get(&value) {
        assert!(next < value);
        value = next;
    }
    value
}

fn remap_unary(tree: &PrefixTree1, parent: &BTreeMap<u32, u32>) -> PrefixTree1 {
    let mut result = PrefixTree1::new();
    for [value] in tree.iter() {
        result.insert([root(parent, value)]);
    }
    result
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
        let mut parent = BTreeMap::new();
        // Wide merges should not rescan all previously accumulated keys.
        let (probe, known) = if self.item.map.len() <= other.item.map.len() {
            (&self.item.map, &other.item.map)
        } else {
            (&other.item.map, &self.item.map)
        };
        assert!(
            probe.all_difference_entries(known, |_, incoming, existing| {
                if let Some(existing) = existing {
                    let left = root(&parent, singleton(incoming));
                    let right = root(&parent, singleton(existing));
                    if left != right {
                        parent.insert(left.max(right), left.min(right));
                    }
                }
                true
            })
        );
        self.carrier = self.carrier.union(&other.carrier);
        self.item = self.item.union(&other.item);
        self.marked = self.marked.union(&other.marked);
        if parent.is_empty() {
            return;
        }
        // Item collisions identify images arriving along different paths.
        self.carrier = remap_unary(&self.carrier, &parent);
        self.marked = remap_unary(&self.marked, &parent);
        let mut item = PrefixTree2::new();
        for [key, value] in self.item.iter() {
            item.insert([key, root(&parent, value)]);
        }
        self.item = item;
    }

    fn add_node(&mut self, owner: usize, node: &Node) {
        if owner == 0 {
            for key in 0..SEED {
                self.add_local(key, key);
            }
        }
        self.add_local(node.output, SEED + owner as u32);
    }

    fn apply_rule(&mut self, node: &Node) -> bool {
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
        if !ready {
            return false;
        }
        let output = self.lookup(node.output);
        self.marked.insert([output])
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

fn topological_order(inputs: &Inputs) -> Vec<usize> {
    let mut indegree: Vec<_> = inputs.nodes.iter().map(|node| node.parents.len()).collect();
    let mut successors = vec![Vec::new(); inputs.nodes.len()];
    for (owner, node) in inputs.nodes.iter().enumerate() {
        for &parent in &node.parents {
            successors[parent].push(owner);
        }
    }
    let mut ready: VecDeque<_> = indegree
        .iter()
        .enumerate()
        .filter_map(|(owner, &count)| (count == 0).then_some(owner))
        .collect();
    let mut order = Vec::with_capacity(inputs.nodes.len());
    while let Some(owner) = ready.pop_front() {
        order.push(owner);
        for &next in &successors[owner] {
            indegree[next] -= 1;
            if indegree[next] == 0 {
                ready.push_back(next);
            }
        }
    }
    assert_eq!(order.len(), inputs.nodes.len(), "graph must be acyclic");
    order
}

pub struct Engine {
    worlds: Vec<World>,
    order: Vec<usize>,
}

impl Engine {
    pub fn construct(inputs: &Inputs) -> Self {
        let order = topological_order(inputs);
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
        Self { worlds, order }
    }

    pub fn mark_seeds(&mut self, seed_mask: u32) {
        self.worlds[0].mark_seeds(seed_mask);
    }

    pub fn close(&mut self, inputs: &Inputs) {
        for &owner in &self.order {
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
