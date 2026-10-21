use std::collections::BTreeMap;
use std::ops::{Index, IndexMut};

/// Ordinary handles stay dense; virtual IDs allocate only weights that change.
#[derive(Clone, Debug, Default)]
pub struct ElementWeights {
    dense: Vec<usize>,
    sparse: BTreeMap<usize, usize>,
    len: usize,
}

impl ElementWeights {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn push(&mut self, value: usize) {
        assert!(
            self.dense.len() == self.len,
            "dense allocation must precede virtual weights"
        );
        self.dense.push(value);
        self.len += 1;
    }

    pub fn increase_size_to(&mut self, len: usize) {
        assert!(len >= self.len, "weight address space cannot shrink");
        self.len = len;
    }

    pub fn stored_len(&self) -> usize {
        self.dense.len() + self.sparse.len()
    }

    /// Dynamic export may deliberately materialize the full handle address space.
    pub fn into_dense(mut self) -> Vec<usize> {
        self.dense.resize(self.len(), 0);
        for (index, value) in self.sparse {
            self.dense[index] = value;
        }
        self.dense
    }
}

impl From<Vec<usize>> for ElementWeights {
    fn from(dense: Vec<usize>) -> Self {
        Self {
            len: dense.len(),
            dense,
            sparse: BTreeMap::new(),
        }
    }
}

impl From<ElementWeights> for Vec<usize> {
    fn from(weights: ElementWeights) -> Self {
        weights.into_dense()
    }
}

impl Index<usize> for ElementWeights {
    type Output = usize;

    fn index(&self, index: usize) -> &usize {
        assert!(
            index < self.len,
            "weight index is outside the reserved address space"
        );
        self.dense
            .get(index)
            .or_else(|| self.sparse.get(&index))
            .unwrap_or(&0)
    }
}

impl IndexMut<usize> for ElementWeights {
    fn index_mut(&mut self, index: usize) -> &mut usize {
        assert!(
            index < self.len,
            "weight index is outside the reserved address space"
        );
        if index < self.dense.len() {
            &mut self.dense[index]
        } else {
            self.sparse.entry(index).or_default()
        }
    }
}
