use crate::collections::{BTreeMap, BTreeSet};

pub struct PrefixTree1 {
    set: BTreeSet<u32>,
}

impl PrefixTree1 {
    pub fn new() -> Self {
        Self {
            set: BTreeSet::new(),
        }
    }

    pub fn insert(&mut self, [el0]: [u32; 1]) {
        self.set.insert(el0);
    }

    pub fn contains(&self, [el0]: [u32; 1]) -> bool {
        self.set.contains(&el0)
    }

    pub fn remove(&mut self, [el0]: [u32; 1]) {
        self.set.remove(&el0);
    }

    pub fn iter(&self) -> impl Iterator<Item = [u32; 1]> + '_ {
        self.set.iter().map(|&x| [x])
    }

    pub fn get(&self, first_el: u32) -> Option<&Self> {
        if self.set.contains(&first_el) {
            Some(self)
        } else {
            None
        }
    }
}

pub struct PrefixTree2 {
    map: BTreeMap<u32, PrefixTree1>,
}

impl PrefixTree2 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, [el0, el1]: [u32; 2]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree1::new)
            .insert([el1]);
    }

    pub fn contains(&self, [el0, el1]: [u32; 2]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1]))
    }

    pub fn remove(&mut self, [el0, el1]: [u32; 2]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1]);
            if tree.set.is_empty() {
                self.map.remove(&el0);
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = [u32; 2]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x]| [k, x]))
    }

    pub fn get(&self, first_el: u32) -> Option<&PrefixTree1> {
        self.map.get(&first_el)
    }
}

pub struct PrefixTree3 {
    map: BTreeMap<u32, PrefixTree2>,
}

impl PrefixTree3 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, [el0, el1, el2]: [u32; 3]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree2::new)
            .insert([el1, el2]);
    }

    pub fn contains(&self, [el0, el1, el2]: [u32; 3]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1, el2]))
    }

    pub fn remove(&mut self, [el0, el1, el2]: [u32; 3]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = [u32; 3]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x, y]| [k, x, y]))
    }

    pub fn get(&self, first_el: u32) -> Option<&PrefixTree2> {
        self.map.get(&first_el)
    }
}
