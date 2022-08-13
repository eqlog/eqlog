use std::collections::BTreeMap;
use std::fmt;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Unification<T> {
    parents: Vec<T>,
    sizes: Vec<u32>,
}

impl<T: Copy + PartialEq + From<u32> + Into<u32>> Unification<T> {
    pub fn new() -> Self {
        Unification {
            parents: Vec::new(),
            sizes: Vec::new(),
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
        assert!(lhs == self.root(lhs));
        assert!(rhs == self.root(rhs));
        self.parents[lhs.into() as usize] = rhs;
    }
    pub fn increase_size_to(&mut self, new_size: usize) {
        assert!(new_size >= self.len());
        assert!((u32::MAX as usize) > new_size);
        for i in self.len()..new_size {
            self.parents.push(T::from(i as u32));
        }
    }
    pub fn len(&self) -> usize {
        self.parents.len()
    }
}

impl<T: Copy + PartialEq + From<u32> + Into<u32> + PartialOrd + Ord> Unification<T> {
    pub fn classes(&self) -> BTreeMap<T, Vec<T>> {
        let mut result = BTreeMap::new();
        for p in 0..self.parents.len() {
            let p = T::from(p as u32);
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
    pub fn class_table(&self) -> tabled::Table {
        let classes = self.classes();

        let mut tabled_builder = tabled::builder::Builder::new();
        for (root, children) in classes.iter() {
            let root: u32 = (*root).into();
            let children = children.iter().map(|el| {
                let el: u32 = (*el).into();
                el
            });
            tabled_builder.add_record(once(root).chain(children));
        }

        tabled_builder.build()
    }
}

impl<T: Copy + PartialEq + From<u32> + Into<u32> + PartialOrd + Ord + fmt::Display> Unification<T> {}
