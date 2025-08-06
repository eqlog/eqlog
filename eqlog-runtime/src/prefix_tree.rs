use crate::wbtree::{map, map::WBTreeMap, set::WBTreeSet};

// type definitions
#[derive(Clone)]
pub struct PrefixTree0(pub Option<()>);

#[derive(Clone)]
pub struct PrefixTree1 {
    pub set: WBTreeSet<'static, u32>,
}

#[derive(Clone)]
pub struct PrefixTree2 {
    pub map: WBTreeMap<'static, u32, PrefixTree1>,
}

#[derive(Clone)]
pub struct PrefixTree3 {
    pub map: WBTreeMap<'static, u32, PrefixTree2>,
}

#[derive(Clone)]
pub struct PrefixTree4 {
    pub map: WBTreeMap<'static, u32, PrefixTree3>,
}

#[derive(Clone)]
pub struct PrefixTree5 {
    pub map: WBTreeMap<'static, u32, PrefixTree4>,
}

#[derive(Clone)]
pub struct PrefixTree6 {
    pub map: WBTreeMap<'static, u32, PrefixTree5>,
}

#[derive(Clone)]
pub struct PrefixTree7 {
    pub map: WBTreeMap<'static, u32, PrefixTree6>,
}

#[derive(Clone)]
pub struct PrefixTree8 {
    pub map: WBTreeMap<'static, u32, PrefixTree7>,
}

#[derive(Clone)]
pub struct PrefixTree9 {
    pub map: WBTreeMap<'static, u32, PrefixTree8>,
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
            set: WBTreeSet::new(),
        }
    }
}

impl PrefixTree2 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree3 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree4 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree5 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree6 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree7 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree8 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

impl PrefixTree9 {
    pub fn new() -> Self {
        Self {
            map: WBTreeMap::new(),
        }
    }
}

// empty() methods
impl PrefixTree0 {
    fn non_empty() -> &'static Self {
        static NON_EMPTY: PrefixTree0 = PrefixTree0(Some(()));
        return &NON_EMPTY;
    }
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree0 = PrefixTree0(None);
        return &EMPTY;
    }
}
impl PrefixTree1 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree1 = PrefixTree1 {
            set: WBTreeSet::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree2 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree2 = PrefixTree2 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree3 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree3 = PrefixTree3 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree4 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree4 = PrefixTree4 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree5 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree5 = PrefixTree5 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree6 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree6 = PrefixTree6 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree7 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree7 = PrefixTree7 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree8 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree8 = PrefixTree8 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}
impl PrefixTree9 {
    pub fn empty() -> &'static Self {
        static EMPTY: PrefixTree9 = PrefixTree9 {
            map: WBTreeMap::new(),
        };
        return &EMPTY;
    }
}

// insert methods.
impl PrefixTree0 {
    pub fn insert(&mut self, []: [u32; 0]) -> bool {
        let was_empty = self.0.is_none();
        self.0 = Some(());
        was_empty
    }
}
impl PrefixTree1 {
    pub fn insert(&mut self, [el0]: [u32; 1]) -> bool {
        self.set.insert(el0)
    }
}

impl PrefixTree2 {
    pub fn insert(&mut self, [el0, el1]: [u32; 2]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree1::new)
            .insert([el1])
    }
}

impl PrefixTree3 {
    pub fn insert(&mut self, [el0, el1, el2]: [u32; 3]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree2::new)
            .insert([el1, el2])
    }
}

impl PrefixTree4 {
    pub fn insert(&mut self, [el0, el1, el2, el3]: [u32; 4]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree3::new)
            .insert([el1, el2, el3])
    }
}

impl PrefixTree5 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4]: [u32; 5]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree4::new)
            .insert([el1, el2, el3, el4])
    }
}

impl PrefixTree6 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5]: [u32; 6]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree5::new)
            .insert([el1, el2, el3, el4, el5])
    }
}

impl PrefixTree7 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6]: [u32; 7]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree6::new)
            .insert([el1, el2, el3, el4, el5, el6])
    }
}

impl PrefixTree8 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7]: [u32; 8]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree7::new)
            .insert([el1, el2, el3, el4, el5, el6, el7])
    }
}

impl PrefixTree9 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 9]) -> bool {
        self.map
            .entry(el0)
            .or_insert_with(PrefixTree8::new)
            .insert([el1, el2, el3, el4, el5, el6, el7, el8])
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

impl PrefixTree0 {
    pub fn remove(&mut self, []: [u32; 0]) -> bool {
        let was_present = self.0.is_some();
        self.0 = None;
        was_present
    }
}
impl PrefixTree1 {
    pub fn remove(&mut self, [el0]: [u32; 1]) -> bool {
        self.set.remove(&el0)
    }
}

impl PrefixTree2 {
    pub fn remove(&mut self, [el0, el1]: [u32; 2]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree3 {
    pub fn remove(&mut self, [el0, el1, el2]: [u32; 3]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree4 {
    pub fn remove(&mut self, [el0, el1, el2, el3]: [u32; 4]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2, el3]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree5 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4]: [u32; 5]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2, el3, el4]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree6 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5]: [u32; 6]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2, el3, el4, el5]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree7 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5, el6]: [u32; 7]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2, el3, el4, el5, el6]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree8 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7]: [u32; 8]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2, el3, el4, el5, el6, el7]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
        }
    }
}

impl PrefixTree9 {
    pub fn remove(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 9]) -> bool {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut entry) => {
                let tree = entry.get_mut();
                let was_present = tree.remove([el1, el2, el3, el4, el5, el6, el7, el8]);
                if tree.is_empty() {
                    entry.remove();
                }
                was_present
            }
            map::Entry::Vacant(_) => false,
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

// iter_restrictions methods
impl PrefixTree1 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, PrefixTree0)> + '_ {
        self.set.iter().map(|&x| (x, PrefixTree0(Some(()))))
    }
}
impl PrefixTree2 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree1)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree3 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree2)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree4 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree3)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree5 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree4)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree6 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree5)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree7 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree6)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree8 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree7)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree9 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree8)> + '_ {
        self.map.iter().map(|(&k, v)| (k, v))
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
impl PrefixTree1 {
    pub fn get(&self, first_el: u32) -> Option<&PrefixTree0> {
        if self.set.contains(&first_el) {
            Some(PrefixTree0::non_empty())
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
