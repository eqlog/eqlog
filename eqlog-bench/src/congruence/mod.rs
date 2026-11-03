use eqlog_runtime::wbtree::map::WBTreeMap;

pub mod one_step;
pub mod recursive;
mod spec;

struct Input {
    vertices: usize,
    keys: usize,
    depth: usize,
}

impl Input {
    fn new(vertices: usize, keys: usize, depth: usize) -> Self {
        assert!(vertices > 0 && keys > 0);
        let width = keys.checked_mul(depth.checked_add(1).unwrap()).unwrap();
        u32::try_from(vertices.checked_mul(width).unwrap()).unwrap();
        Self {
            vertices,
            keys,
            depth,
        }
    }

    fn width(&self) -> usize {
        self.keys * (self.depth + 1)
    }

    fn origin(&self, owner: usize, key: usize, level: usize) -> u32 {
        assert!(owner < self.vertices && key < self.keys && level <= self.depth);
        u32::try_from(owner * self.width() + key * (self.depth + 1) + level).unwrap()
    }
}

#[derive(Clone)]
struct Partition {
    parents: WBTreeMap<u32>,
}

impl Partition {
    fn new() -> Self {
        Self {
            parents: WBTreeMap::new(),
        }
    }

    fn root(&self, mut element: u32) -> u32 {
        while let Some(&parent) = self.parents.get(&element) {
            assert!(parent < element);
            element = parent;
        }
        element
    }

    fn equate(&mut self, left: u32, right: u32) -> Option<(u32, u32)> {
        let left = self.root(left);
        let right = self.root(right);
        if left == right {
            return None;
        }
        let (winner, loser) = (left.min(right), left.max(right));
        // Every collision pairs a fresh local member with an inherited root.
        // Keeping that root makes aliases one hop deep across all snapshots.
        self.parents.insert(loser, winner);
        Some((loser, winner))
    }
}
