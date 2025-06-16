use crate::collections::{BTreeMap, BTreeSet};

// type definitions
pub struct PrefixTree1 {
    set: BTreeSet<u32>,
}

pub struct PrefixTree2 {
    map: BTreeMap<u32, PrefixTree1>,
}

pub struct PrefixTree3 {
    map: BTreeMap<u32, PrefixTree2>,
}

// new methods
impl PrefixTree1 {
    pub fn new() -> Self {
        Self {
            set: BTreeSet::new(),
        }
    }
}

impl PrefixTree2 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl PrefixTree3 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

// insert methods.
impl PrefixTree1 {
    pub fn insert(&mut self, [el0]: [u32; 1]) {
        self.set.insert(el0);
    }
}

impl PrefixTree2 {
    pub fn insert(&mut self, [el0, el1]: [u32; 2]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree1::new)
            .insert([el1]);
    }
}
impl PrefixTree3 {
    pub fn insert(&mut self, [el0, el1, el2]: [u32; 3]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree2::new)
            .insert([el1, el2]);
    }
}

// contains methods.
impl PrefixTree1 {
    pub fn contains(&self, [el0]: [u32; 1]) -> bool {
        self.set.contains(&el0)
    }
}

impl PrefixTree2 {
    pub fn contains(&self, [el0, el1]: [u32; 2]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1]))
    }
}

impl PrefixTree3 {
    pub fn contains(&self, [el0, el1, el2]: [u32; 3]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1, el2]))
    }
}

// remove methods.
impl PrefixTree1 {
    pub fn remove(&mut self, [el0]: [u32; 1]) {
        self.set.remove(&el0);
    }
}

impl PrefixTree2 {
    pub fn remove(&mut self, [el0, el1]: [u32; 2]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1]);
            if tree.set.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

impl PrefixTree3 {
    pub fn remove(&mut self, [el0, el1, el2]: [u32; 3]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

// is_empty methods
impl PrefixTree1 {
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

impl PrefixTree2 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl PrefixTree3 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

// clear methods
impl PrefixTree1 {
    pub fn clear(&mut self) {
        self.set.clear();
    }
}

impl PrefixTree2 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl PrefixTree3 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

// iter methods
impl PrefixTree1 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 1]> + '_ {
        self.set.iter().map(|&x| [x])
    }
}

impl PrefixTree2 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 2]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x]| [k, x]))
    }
}

impl PrefixTree3 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 3]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x, y]| [k, x, y]))
    }
}

// get methods
impl PrefixTree1 {
    pub fn get(&self, first_el: u32) -> Option<&Self> {
        if self.set.contains(&first_el) {
            Some(self)
        } else {
            None
        }
    }
}

impl PrefixTree2 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree1> {
        self.map.get(&first_el)
    }
}

impl PrefixTree3 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree2> {
        self.map.get(&first_el)
    }
}
