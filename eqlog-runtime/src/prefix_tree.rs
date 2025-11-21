use crate::wbtree::{map, map::WBTreeMap, set::WBTreeSet};

// type definitions
#[derive(Clone, Debug)]
pub struct PrefixTree0(pub Option<()>);

#[derive(Clone, Debug)]
pub struct PrefixTree1 {
    pub set: WBTreeSet<u32>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree2 {
    pub map: WBTreeMap<u32, PrefixTree1>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree3 {
    pub map: WBTreeMap<u32, PrefixTree2>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree4 {
    pub map: WBTreeMap<u32, PrefixTree3>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree5 {
    pub map: WBTreeMap<u32, PrefixTree4>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree6 {
    pub map: WBTreeMap<u32, PrefixTree5>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree7 {
    pub map: WBTreeMap<u32, PrefixTree6>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree8 {
    pub map: WBTreeMap<u32, PrefixTree7>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree9 {
    pub map: WBTreeMap<u32, PrefixTree8>,
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

// This is here because our WBTreeSet uses Rcs internally, which are not Sync, hence statics of
// this types are not allowed. But empty WBTreeSets don't actually contain Rcs, so those can be
// shared across threads.
struct UnsafeSync<T>(T);
unsafe impl<T> Sync for UnsafeSync<T> {}

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
        static EMPTY: UnsafeSync<PrefixTree1> = UnsafeSync(PrefixTree1 {
            set: WBTreeSet::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree2 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree2> = UnsafeSync(PrefixTree2 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree3 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree3> = UnsafeSync(PrefixTree3 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree4 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree4> = UnsafeSync(PrefixTree4 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree5 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree5> = UnsafeSync(PrefixTree5 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree6 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree6> = UnsafeSync(PrefixTree6 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree7 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree7> = UnsafeSync(PrefixTree7 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree8 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree8> = UnsafeSync(PrefixTree8 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}
impl PrefixTree9 {
    pub fn empty() -> &'static Self {
        static EMPTY: UnsafeSync<PrefixTree9> = UnsafeSync(PrefixTree9 {
            map: WBTreeMap::new(),
        });
        return &EMPTY.0;
    }
}

// insert_restriction methods.
impl PrefixTree1 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree0) {
        if restriction.0.is_none() {
            return;
        }

        self.set.insert(el0);
    }
}
impl PrefixTree2 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree1) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree3 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree2) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree4 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree3) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree5 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree4) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree6 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree5) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree7 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree6) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree8 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree7) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
    }
}
impl PrefixTree9 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree8) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().union(&restriction);
            }
            map::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(restriction);
            }
        }
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

// iter_restrictions_mut methods
impl PrefixTree2 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree1)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree3 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree2)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree4 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree3)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree5 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree4)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree6 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree5)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree7 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree6)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree8 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree7)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
    }
}

impl PrefixTree9 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree8)> + '_ {
        self.map.iter_mut().map(|(&k, v)| (k, v))
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

// TODO: The maps in PrefixTrees should maintain the invariant that they map to non-empty sets.
// This can be violated using the get_mut fns atm. We should instead return some kind of
// smart-pointer kind of object that checks whether the restriction is empty in its drop impl, and
// if so removes the whole entry (with key) from the prefix tree.
//
// get_mut methods
impl PrefixTree2 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree1> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree3 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree2> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree4 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree3> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree5 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree4> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree6 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree5> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree7 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree6> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree8 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree7> {
        self.map.get_mut(&first_el)
    }
}

impl PrefixTree9 {
    pub fn get_mut(&mut self, first_el: u32) -> Option<&mut PrefixTree8> {
        self.map.get_mut(&first_el)
    }
}

// union methods
impl PrefixTree0 {
    pub fn union(&self, other: &PrefixTree0) -> PrefixTree0 {
        PrefixTree0(self.0.or(other.0))
    }
}

impl PrefixTree1 {
    pub fn union(&self, other: &Self) -> Self {
        Self {
            set: self.set.union(&other.set),
        }
    }
}

impl PrefixTree2 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree3 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree4 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree5 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree6 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree7 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree8 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree9 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

// difference methods
impl PrefixTree0 {
    pub fn difference(&self, other: &PrefixTree0) -> PrefixTree0 {
        match (self.0, other.0) {
            (Some(()), Some(())) => PrefixTree0(None), // Both have element, remove it
            (Some(()), None) => PrefixTree0(Some(())), // Only self has element, keep it
            (None, _) => PrefixTree0(None),            // Self doesn't have element, nothing to keep
        }
    }
}

impl PrefixTree1 {
    pub fn difference(&self, other: &Self) -> Self {
        Self {
            set: self.set.difference(&other.set),
        }
    }
}

impl PrefixTree2 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree3 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree4 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree5 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree6 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree7 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree8 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

impl PrefixTree9 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference(&other.map, |_key, val1, val2| {
            let diff_result = val1.difference(&val2);
            if diff_result.is_empty() {
                None
            } else {
                Some(diff_result)
            }
        });
        Self { map }
    }
}

// remove_restriction
impl PrefixTree1 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree0) {
        if restriction.0.is_none() {
            return;
        }

        self.set.remove(&el0);
    }
}

impl PrefixTree2 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree1) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree3 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree2) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree4 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree3) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree5 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree4) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree6 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree5) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree7 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree6) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree8 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree7) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

impl PrefixTree9 {
    pub fn remove_restriction(&mut self, el0: u32, restriction: &PrefixTree8) {
        match self.map.entry(el0) {
            map::Entry::Occupied(mut occupied_entry) => {
                *occupied_entry.get_mut() = occupied_entry.get_mut().difference(&restriction);
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

// mapped methods

// TODO: This currently clones the whole tree. Instead, we should use copy-on-write semantics here.
// The idea would be to introduce new type of node in WBTreeMap which represents applying a mapping
// to all keys and values under the mapping node.
// Things to consider:
// - The new node could be called something like MapNode, but that's ambiguous because the "Map"
//   here refers to the monotone mapping, not the map as in the WBTreeMap the node is part of.
// - The monotone mapping on keys should be represented as a WBTreeMap<K, K>, at least for now.
//   Introduce a type alias for it though; later on we want to transition to a more efficient
//   representation.
// - The new `Node` type should be an enum: Either the `Node` as it is currently (find an
//   appropriate name) or the new mapping node that represents a transformation of the subtree.
// - In terms of balancing, ignore the mapping nodes at first: mapping nodes shouldn't
//   contribute to the of a node/subtree. This might be close to the best thing that we can do,
//   as mapped subtrees will usually be shared with other trees, so allowing more imbalance in
//   order to avoid cloning might be a reasonable trade-off.
// - Balancing might require shifting mapping nodes around, cloning them, I'm not sure. Figure it
//   out.
// - The map on values should be given by an Fn(V) -> V. Use sometihg like an Rc<dyn Fn ...> to
//   hold it, the concrete type of the function shouldn't be part of WBTreeMap.
// - In principle you could imagine applying a mapping on keys separately from values, but this is
//   never actually used. So the mapping node should do both at the same time.
// - Keep in mind that there might be multiple mapping nodes on the way from the root node down to
//   some specific node. You'll need to apply multiple mappings, potentially.
// - When inserting a (key, value) pair, that (key, value) pair might belong somewhere under a
//   mapping node. But we don't have reverse mappings or something like that, and insertions
//   currently recreate the path from the root node anyway. So just continue doing that: Recreate
//   the path from the new root node. However, this might require splitting a subtree under a
//   mapping node, in which both parts of the split must be put under separate mapping node.
impl PrefixTree0 {
    pub fn mapped(&self) -> Self {
        self.clone()
    }
}

impl PrefixTree1 {
    pub fn mapped(&self, map0: Option<&WBTreeMap<u32, u32>>) -> Self {
        if let Some(map) = map0 {
            let mut result = Self::new();
            for el in self.set.iter() {
                let mapped = map
                    .get(el)
                    .expect("map undefined on value in prefix tree")
                    .clone();
                result.set.insert(mapped);
            }
            result
        } else {
            self.clone()
        }
    }
}

impl PrefixTree2 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree3 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree4 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
        map3: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2, map3);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree5 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
        map3: Option<&WBTreeMap<u32, u32>>,
        map4: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2, map3, map4);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree6 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
        map3: Option<&WBTreeMap<u32, u32>>,
        map4: Option<&WBTreeMap<u32, u32>>,
        map5: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2, map3, map4, map5);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree7 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
        map3: Option<&WBTreeMap<u32, u32>>,
        map4: Option<&WBTreeMap<u32, u32>>,
        map5: Option<&WBTreeMap<u32, u32>>,
        map6: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2, map3, map4, map5, map6);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree8 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
        map3: Option<&WBTreeMap<u32, u32>>,
        map4: Option<&WBTreeMap<u32, u32>>,
        map5: Option<&WBTreeMap<u32, u32>>,
        map6: Option<&WBTreeMap<u32, u32>>,
        map7: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2, map3, map4, map5, map6, map7);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}

impl PrefixTree9 {
    pub fn mapped(
        &self,
        map0: Option<&WBTreeMap<u32, u32>>,
        map1: Option<&WBTreeMap<u32, u32>>,
        map2: Option<&WBTreeMap<u32, u32>>,
        map3: Option<&WBTreeMap<u32, u32>>,
        map4: Option<&WBTreeMap<u32, u32>>,
        map5: Option<&WBTreeMap<u32, u32>>,
        map6: Option<&WBTreeMap<u32, u32>>,
        map7: Option<&WBTreeMap<u32, u32>>,
        map8: Option<&WBTreeMap<u32, u32>>,
    ) -> Self {
        let mut result = Self::new();
        for (k, v) in self.map.iter() {
            let new_k = if let Some(m) = map0 {
                m.get(k)
                    .expect("map undefined on value in prefix tree")
                    .clone()
            } else {
                k.clone()
            };
            let new_v = v.mapped(map1, map2, map3, map4, map5, map6, map7, map8);
            result.insert_restriction(new_k, new_v);
        }
        result
    }
}
