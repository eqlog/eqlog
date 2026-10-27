use super::spec::{oracle, Inputs, Metrics, Operation, SEED};

eqlog_runtime::eqlog_mod!(random_dag);
use random_dag::{El, Key, RandomDag, World, WorldMor};

#[path = "verify.rs"]
mod verify;

pub struct Engine {
    model: RandomDag,
    worlds: Vec<World>,
    keys: Vec<Key>,
    morphisms: Vec<WorldMor>,
    seeds: Vec<El>,
}

impl Engine {
    pub fn construct(inputs: &Inputs) -> Self {
        let mut model = RandomDag::new();
        model.enable_compact_world();
        let worlds: Vec<_> = inputs.nodes.iter().map(|_| model.new_world()).collect();
        let keys: Vec<_> = (0..SEED as usize + inputs.nodes.len())
            .map(|_| model.new_key())
            .collect();
        let mut morphisms = Vec::with_capacity(inputs.edges.len());
        let mut seeds = Vec::with_capacity(SEED as usize);
        for (owner, node) in inputs.nodes.iter().enumerate() {
            let world = worlds[owner];
            for &parent in &node.parents {
                let morphism = model.new_world_mor();
                model.insert_world_mor_dom(morphism, worlds[parent]);
                model.insert_world_mor_cod(morphism, world);
                assert!(model.inherit_total_world_members(morphism));
                morphisms.push(morphism);
            }
        }
        for (owner, node) in inputs.nodes.iter().enumerate() {
            let world = worlds[owner];
            if owner == 0 {
                for key in 0..SEED {
                    let element = model.new_el(world);
                    model.insert_item(world, keys[key as usize], element);
                    seeds.push(element);
                }
            }
            let element = model.new_el(world);
            model.insert_item(world, keys[node.output as usize], element);
            match node.operation {
                Operation::Job { input } => {
                    model.insert_job(world, keys[input as usize], keys[node.output as usize]);
                }
                Operation::Join { left, right } => {
                    model.insert_join(
                        world,
                        keys[left as usize],
                        keys[right as usize],
                        keys[node.output as usize],
                    );
                }
            }
        }
        Self {
            model,
            worlds,
            keys,
            morphisms,
            seeds,
        }
    }

    pub fn mark_seeds(&mut self, seed_mask: u32) {
        for key in 0..SEED {
            if seed_mask & (1 << key) != 0 {
                let element = self.seeds[key as usize];
                self.model.insert_marked(self.worlds[0], element);
            }
        }
    }

    pub fn close(&mut self) {
        self.model.close();
    }

    pub fn verify(&self, inputs: &Inputs, seed_mask: u32) -> Metrics {
        let expected = oracle(inputs, seed_mask);
        verify::verify(self, inputs, &expected)
    }
}
