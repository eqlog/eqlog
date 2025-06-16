use crate::collections::{BTreeMap, BTreeSet};

// type definitions
pub struct PrefixTree0(Option<()>);

pub struct PrefixTree1 {
    set: BTreeSet<u32>,
}

pub struct PrefixTree2 {
    map: BTreeMap<u32, PrefixTree1>,
}

pub struct PrefixTree3 {
    map: BTreeMap<u32, PrefixTree2>,
}

pub struct PrefixTree4 {
    map: BTreeMap<u32, PrefixTree3>,
}

pub struct PrefixTree5 {
    map: BTreeMap<u32, PrefixTree4>,
}

pub struct PrefixTree6 {
    map: BTreeMap<u32, PrefixTree5>,
}

pub struct PrefixTree7 {
    map: BTreeMap<u32, PrefixTree6>,
}

pub struct PrefixTree8 {
    map: BTreeMap<u32, PrefixTree7>,
}

pub struct PrefixTree9 {
    map: BTreeMap<u32, PrefixTree8>,
}

// new methods
impl PrefixTree0 {
    pub fn new() -> Self {
        PrefixTree0(None)
    }
}

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

impl PrefixTree4 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl PrefixTree5 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl PrefixTree6 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl PrefixTree7 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl PrefixTree8 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

impl PrefixTree9 {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

// insert methods.
impl PrefixTree0 {
    pub fn insert(&mut self, []: [u32; 0]) {
        self.0 = Some(());
    }
}
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

impl PrefixTree4 {
    pub fn insert(&mut self, [el0, el1, el2, el3]: [u32; 4]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree3::new)
            .insert([el1, el2, el3]);
    }
}

impl PrefixTree5 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4]: [u32; 5]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree4::new)
            .insert([el1, el2, el3, el4]);
    }
}

impl PrefixTree6 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5]: [u32; 6]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree5::new)
            .insert([el1, el2, el3, el4, el5]);
    }
}

impl PrefixTree7 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6]: [u32; 7]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree6::new)
            .insert([el1, el2, el3, el4, el5, el6]);
    }
}

impl PrefixTree8 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7]: [u32; 8]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree7::new)
            .insert([el1, el2, el3, el4, el5, el6, el7]);
    }
}

impl PrefixTree9 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 9]) {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree8::new)
            .insert([el1, el2, el3, el4, el5, el6, el7, el8]);
    }
}

// contains methods.
impl PrefixTree0 {
    pub fn contains(&self, []: [u32; 0]) -> bool {
        self.0.is_some()
    }
}

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

impl PrefixTree4 {
    pub fn contains(&self, [el0, el1, el2, el3]: [u32; 4]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1, el2, el3]))
    }
}

impl PrefixTree5 {
    pub fn contains(&self, [el0, el1, el2, el3, el4]: [u32; 5]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1, el2, el3, el4]))
    }
}

impl PrefixTree6 {
    pub fn contains(&self, [el0, el1, el2, el3, el4, el5]: [u32; 6]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1, el2, el3, el4, el5]))
    }
}

impl PrefixTree7 {
    pub fn contains(&self, [el0, el1, el2, el3, el4, el5, el6]: [u32; 7]) -> bool {
        self.map
            .get(&el0)
            .map_or(false, |tree| tree.contains([el1, el2, el3, el4, el5, el6]))
    }
}

impl PrefixTree8 {
    pub fn contains(&self, [el0, el1, el2, el3, el4, el5, el6, el7]: [u32; 8]) -> bool {
        self.map.get(&el0).map_or(false, |tree| {
            tree.contains([el1, el2, el3, el4, el5, el6, el7])
        })
    }
}

impl PrefixTree9 {
    pub fn contains(&self, [el0, el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 9]) -> bool {
        self.map.get(&el0).map_or(false, |tree| {
            tree.contains([el1, el2, el3, el4, el5, el6, el7, el8])
        })
    }
}

// remove methods.
impl PrefixTree0 {
    pub fn remove(&mut self, []: [u32; 0]) {
        self.0 = None;
    }
}
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

impl PrefixTree4 {
    pub fn remove(&mut self, [el0, el1, el2, el3]: [u32; 4]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2, el3]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

impl PrefixTree5 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4]: [u32; 5]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2, el3, el4]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

impl PrefixTree6 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5]: [u32; 6]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2, el3, el4, el5]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

impl PrefixTree7 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5, el6]: [u32; 7]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2, el3, el4, el5, el6]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

impl PrefixTree8 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7]: [u32; 8]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2, el3, el4, el5, el6, el7]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

impl PrefixTree9 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 9]) {
        if let Some(tree) = self.map.get_mut(&el0) {
            tree.remove([el1, el2, el3, el4, el5, el6, el7, el8]);
            if tree.map.is_empty() {
                self.map.remove(&el0);
            }
        }
    }
}

// is_empty methods
impl PrefixTree0 {
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
}

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

impl PrefixTree4 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl PrefixTree5 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl PrefixTree6 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl PrefixTree7 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl PrefixTree8 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl PrefixTree9 {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

// clear methods
impl PrefixTree0 {
    pub fn clear(&mut self) {
        self.0 = None;
    }
}

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

impl PrefixTree4 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl PrefixTree5 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl PrefixTree6 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl PrefixTree7 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl PrefixTree8 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl PrefixTree9 {
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

// iter methods
impl PrefixTree0 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 0]> + '_ {
        self.0.iter().map(|_| [])
    }
}

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

impl PrefixTree4 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 4]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x, y, z]| [k, x, y, z]))
    }
}

impl PrefixTree5 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 5]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x, y, z, a]| [k, x, y, z, a]))
    }
}

impl PrefixTree6 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 6]> + '_ {
        self.map
            .iter()
            .flat_map(|(&k, v)| v.iter().map(move |[x, y, z, a, b]| [k, x, y, z, a, b]))
    }
}

impl PrefixTree7 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 7]> + '_ {
        self.map.iter().flat_map(|(&k, v)| {
            v.iter()
                .map(move |[x, y, z, a, b, c]| [k, x, y, z, a, b, c])
        })
    }
}

impl PrefixTree8 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 8]> + '_ {
        self.map.iter().flat_map(|(&k, v)| {
            v.iter()
                .map(move |[x, y, z, a, b, c, d]| [k, x, y, z, a, b, c, d])
        })
    }
}

impl PrefixTree9 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 9]> + '_ {
        self.map.iter().flat_map(|(&k, v)| {
            v.iter()
                .map(move |[x, y, z, a, b, c, d, e]| [k, x, y, z, a, b, c, d, e])
        })
    }
}

// get methods
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

impl PrefixTree4 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree3> {
        self.map.get(&first_el)
    }
}

impl PrefixTree5 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree4> {
        self.map.get(&first_el)
    }
}

impl PrefixTree6 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree5> {
        self.map.get(&first_el)
    }
}

impl PrefixTree7 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree6> {
        self.map.get(&first_el)
    }
}

impl PrefixTree8 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree7> {
        self.map.get(&first_el)
    }
}

impl PrefixTree9 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree8> {
        self.map.get(&first_el)
    }
}
