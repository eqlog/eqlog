pub const SEED: u32 = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Job { input: u32 },
    Join { left: u32, right: u32 },
}

#[derive(Clone, Debug)]
pub struct Node {
    pub parents: Vec<usize>,
    pub operation: Operation,
    pub output: u32,
}

#[derive(Clone, Debug)]
pub struct Inputs {
    pub nodes: Vec<Node>,
    pub edges: Vec<(usize, usize)>,
    pub key_origins: Vec<u32>,
}

impl Inputs {
    pub fn new(nodes: Vec<Node>) -> Self {
        let member_count = SEED as usize + nodes.len();
        let origin_keys: Vec<u32> = (0..SEED)
            .chain(nodes.iter().map(|node| node.output))
            .collect();
        let mut key_origins = vec![u32::MAX; member_count];
        for (origin, &key) in origin_keys.iter().enumerate() {
            assert_eq!(key_origins[key as usize], u32::MAX, "duplicate output key");
            key_origins[key as usize] = u32::try_from(origin).unwrap();
        }
        let edges = nodes
            .iter()
            .enumerate()
            .flat_map(|(child, node)| node.parents.iter().map(move |&parent| (parent, child)))
            .collect();
        let inputs = Self {
            nodes,
            edges,
            key_origins,
        };
        validate_input(&inputs);
        inputs
    }

    pub fn key_origin(&self, key: u32) -> u32 {
        self.key_origins[key as usize]
    }
}

pub fn validate_input(inputs: &Inputs) {
    assert!(!inputs.nodes.is_empty());
    for (owner, node) in inputs.nodes.iter().enumerate() {
        assert_eq!(
            inputs.key_origin(node.output),
            SEED + u32::try_from(owner).unwrap()
        );
        assert_eq!(node.parents.is_empty(), owner == 0);
        assert!(node.parents.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(node.parents.iter().all(|&parent| parent < owner));
        match node.operation {
            Operation::Job { input } => {
                assert!(node.parents.len() <= 1);
                assert!(inputs.key_origin(input) < SEED + u32::try_from(owner).unwrap());
            }
            Operation::Join { left, right } => {
                assert!(node.parents.len() >= 2);
                assert_ne!(left, right);
                assert!(node
                    .parents
                    .iter()
                    .any(|&parent| inputs.nodes[parent].output == left));
                assert!(node
                    .parents
                    .iter()
                    .any(|&parent| inputs.nodes[parent].output == right));
            }
        }
    }
    let expected_edges: Vec<_> = inputs
        .nodes
        .iter()
        .enumerate()
        .flat_map(|(child, node)| node.parents.iter().map(move |&parent| (parent, child)))
        .collect();
    assert_eq!(inputs.edges, expected_edges);
    let available = oracle(inputs, 0);
    for (owner, node) in inputs.nodes.iter().enumerate() {
        match node.operation {
            Operation::Job { input } => assert!(available.contains_key(owner, input)),
            Operation::Join { left, right } => {
                assert!(available.contains_key(owner, left));
                assert!(available.contains_key(owner, right));
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Metrics {
    pub vertices: usize,
    pub edges: usize,
    pub local_members: usize,
    pub local_contribution_size: usize,
    pub elements: usize,
    pub member_rows: usize,
    pub images: usize,
    pub checksum: u64,
}

pub struct Oracle {
    ancestors: Vec<Vec<u64>>,
    origin_ancestors: Vec<Vec<u64>>,
    marked_keys: Vec<u64>,
    marked_origins: Vec<u64>,
    outputs: Vec<u32>,
    edges: Vec<(usize, usize)>,
    seed_mask: u32,
}

pub struct KeyIter<'a> {
    words: &'a [u64],
    filter: Option<&'a [u64]>,
    position: usize,
    remaining: u64,
}

impl Iterator for KeyIter<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        loop {
            if self.remaining != 0 {
                let bit = self.remaining.trailing_zeros();
                self.remaining &= self.remaining - 1;
                return Some(u32::try_from((self.position - 1) * 64).unwrap() + bit);
            }
            if self.position == self.words.len() {
                return None;
            }
            self.remaining = self.words[self.position];
            if let Some(filter) = self.filter {
                self.remaining &= filter[self.position];
            }
            self.position += 1;
        }
    }
}

impl Oracle {
    pub fn keys(&self, owner: usize) -> KeyIter<'_> {
        KeyIter {
            words: &self.ancestors[owner],
            filter: None,
            position: 0,
            remaining: 0,
        }
    }

    pub fn marked(&self, owner: usize) -> KeyIter<'_> {
        KeyIter {
            words: &self.ancestors[owner],
            filter: Some(&self.marked_keys),
            position: 0,
            remaining: 0,
        }
    }

    pub fn origins(&self, owner: usize) -> KeyIter<'_> {
        KeyIter {
            words: &self.origin_ancestors[owner],
            filter: None,
            position: 0,
            remaining: 0,
        }
    }

    pub fn marked_origins(&self, owner: usize) -> KeyIter<'_> {
        KeyIter {
            words: &self.origin_ancestors[owner],
            filter: Some(&self.marked_origins),
            position: 0,
            remaining: 0,
        }
    }

    pub fn contains_key(&self, owner: usize, key: u32) -> bool {
        let key = key as usize;
        self.ancestors[owner]
            .get(key / 64)
            .is_some_and(|word| word & (1 << (key % 64)) != 0)
    }

    pub fn contains_marked(&self, owner: usize, key: u32) -> bool {
        let index = key as usize;
        self.contains_key(owner, key) && self.marked_keys[index / 64] & (1 << (index % 64)) != 0
    }

    pub fn key_count(&self, owner: usize) -> usize {
        self.ancestors[owner]
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum()
    }

    pub fn metrics(&self) -> Metrics {
        let vertices = self.ancestors.len();
        let local_members = SEED as usize + vertices;
        let mut checksum = 0xcbf29ce484222325_u64;
        let mut elements = 0;
        let mut member_rows = 0;
        let mut productive = 0;
        for owner in 0..vertices {
            let key_count = self.key_count(owner);
            elements += key_count;
            member_rows += key_count + self.marked(owner).count();
            productive += usize::from(self.contains_marked(owner, self.outputs[owner]));
            for (relation, rows) in [self.keys(owner), self.marked(owner)]
                .into_iter()
                .enumerate()
            {
                for key in rows {
                    for value in [owner as u64, relation as u64, key as u64] {
                        checksum ^= value;
                        checksum = checksum.wrapping_mul(0x100000001b3);
                    }
                }
            }
        }
        Metrics {
            vertices,
            edges: self.edges.len(),
            local_members,
            local_contribution_size: 2 * local_members
                + self.seed_mask.count_ones() as usize
                + productive,
            elements,
            member_rows,
            images: self
                .edges
                .iter()
                .map(|&(parent, _)| self.key_count(parent))
                .sum(),
            checksum,
        }
    }
}

pub fn oracle(inputs: &Inputs, seed_mask: u32) -> Oracle {
    assert_eq!(seed_mask >> SEED, 0);
    let key_count = SEED as usize + inputs.nodes.len();
    let words = key_count.div_ceil(64);
    let mut ancestors: Vec<Vec<u64>> = Vec::with_capacity(inputs.nodes.len());
    let mut origin_ancestors: Vec<Vec<u64>> = Vec::with_capacity(inputs.nodes.len());
    let mut marked_keys = vec![0_u64; words];
    let mut marked_origins = vec![0_u64; words];
    marked_keys[0] = seed_mask as u64;
    marked_origins[0] = seed_mask as u64;
    for (owner, node) in inputs.nodes.iter().enumerate() {
        let mut keys = vec![0_u64; words];
        let mut origins = vec![0_u64; words];
        if owner == 0 {
            keys[0] = (1 << SEED) - 1;
            origins[0] = (1 << SEED) - 1;
        }
        for &parent in &node.parents {
            for (word, &source) in keys.iter_mut().zip(&ancestors[parent]) {
                *word |= source;
            }
            for (word, &source) in origins.iter_mut().zip(&origin_ancestors[parent]) {
                *word |= source;
            }
        }
        let enabled = match node.operation {
            Operation::Job { input } => marked_keys[input as usize / 64] & (1 << (input % 64)) != 0,
            Operation::Join { left, right } => {
                marked_keys[left as usize / 64] & (1 << (left % 64)) != 0
                    && marked_keys[right as usize / 64] & (1 << (right % 64)) != 0
            }
        };
        let output = node.output as usize;
        keys[output / 64] |= 1 << (output % 64);
        let origin = SEED as usize + owner;
        origins[origin / 64] |= 1 << (origin % 64);
        if enabled {
            marked_keys[output / 64] |= 1 << (output % 64);
            marked_origins[origin / 64] |= 1 << (origin % 64);
        }
        ancestors.push(keys);
        origin_ancestors.push(origins);
    }
    Oracle {
        ancestors,
        origin_ancestors,
        marked_keys,
        marked_origins,
        outputs: inputs.nodes.iter().map(|node| node.output).collect(),
        edges: inputs.edges.clone(),
        seed_mask,
    }
}
