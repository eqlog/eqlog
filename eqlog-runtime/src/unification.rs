use std::collections::BTreeMap;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Unification<T> {
    parents: Vec<T>,
    sizes: Vec<u32>,
    canonical: Vec<bool>,
    allocated: Option<Vec<bool>>,
}

impl<T: Copy + PartialEq + From<u32> + Into<u32>> Unification<T> {
    pub fn new() -> Self {
        Unification {
            parents: Vec::new(),
            sizes: Vec::new(),
            canonical: Vec::new(),
            allocated: None,
        }
    }
    pub fn root(&mut self, mut el: T) -> T {
        let mut parent = self.parents[el.into() as usize];
        while el != parent {
            self.parents[el.into() as usize] = self.parents[parent.into() as usize];
            el = parent;
            parent = self.parents[parent.into() as usize];
        }
        el
    }
    pub fn root_const(&self, mut el: T) -> T {
        let mut parent = self.parents[el.into() as usize];
        while el != parent {
            el = parent;
            parent = self.parents[el.into() as usize];
        }
        el
    }
    pub fn union_roots_into(&mut self, lhs: T, rhs: T) {
        assert!(self.is_allocated(lhs) && self.is_allocated(rhs));
        assert!(lhs == self.root(lhs));
        assert!(rhs == self.root(rhs));
        self.parents[lhs.into() as usize] = rhs;
        self.canonical[lhs.into() as usize] = lhs == rhs;
    }
    pub fn increase_size_to(&mut self, new_size: usize) {
        assert!(new_size >= self.len());
        assert!((u32::MAX as usize) > new_size);
        for i in self.len()..new_size {
            self.parents.push(T::from(i as u32));
            self.canonical.push(true);
            if let Some(allocated) = &mut self.allocated {
                allocated.push(true);
            }
        }
    }
    pub fn len(&self) -> usize {
        self.parents.len()
    }

    pub fn canonical_roots(&self) -> &[bool] {
        &self.canonical
    }

    pub fn is_allocated(&self, element: T) -> bool {
        let index = element.into() as usize;
        index < self.len()
            && self
                .allocated
                .as_ref()
                .is_none_or(|allocated| allocated[index])
    }

    /// Reserved numeric holes must not become elements during dynamic export.
    pub fn restrict_to(&mut self, elements: impl IntoIterator<Item = T>) {
        let mut allocated = vec![false; self.len()];
        for element in elements {
            assert!(
                self.is_allocated(element),
                "restricted elements were allocated"
            );
            allocated[element.into() as usize] = true;
        }
        for (index, &present) in allocated.iter().enumerate() {
            if present {
                let root = self.root_const(T::from(u32::try_from(index).unwrap()));
                assert!(
                    allocated[root.into() as usize],
                    "allocated elements retain their roots"
                );
            }
        }
        for (canonical, &present) in self.canonical.iter_mut().zip(&allocated) {
            *canonical &= present;
        }
        self.allocated = Some(allocated);
    }

    /// Copies the forest using another handle type, preserving all numeric IDs.
    pub fn retype<U: From<u32>>(&self) -> Unification<U> {
        Unification {
            parents: self.parents.iter().map(|&el| U::from(el.into())).collect(),
            sizes: self.sizes.clone(),
            canonical: self.canonical.clone(),
            allocated: self.allocated.clone(),
        }
    }
}

impl<T: Copy + PartialEq + From<u32> + Into<u32> + PartialOrd + Ord> Unification<T> {
    pub fn classes(&self) -> BTreeMap<T, Vec<T>> {
        let mut result = BTreeMap::new();
        for p in 0..self.parents.len() {
            let p = T::from(p as u32);
            if !self.is_allocated(p) {
                continue;
            }
            let root = self.root_const(p);

            // TODO: Eliminate one search once try_insert is stabilized.
            if !result.contains_key(&root) {
                result.insert(root, Vec::new());
            }
            let class_els = result.get_mut(&root).unwrap();

            if p != root {
                class_els.push(p);
            }
        }
        result
    }
}

impl<T: Copy + PartialEq + From<u32> + Into<u32> + PartialOrd + Ord + fmt::Display> Unification<T> {}
