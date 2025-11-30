use super::map::*;
use std::fmt;

#[derive(Clone)]
pub struct WBTreeSet {
    map: WBTreeMap<()>,
}

impl WBTreeSet {
    pub const fn new() -> Self {
        WBTreeSet {
            map: WBTreeMap::new(),
        }
    }

    pub fn insert(&mut self, value: u32) -> bool {
        self.map.insert(value, ()).is_none()
    }

    pub fn contains(&self, value: &u32) -> bool {
        self.map.contains_key(value)
    }

    pub fn remove(&mut self, value: &u32) -> bool {
        self.map.remove(value).is_some()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    pub fn iter(&self) -> WBTreeSetIter<'_> {
        WBTreeSetIter {
            map_iter: self.map.iter(),
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        WBTreeSet {
            map: self.map.union(&other.map, |_element, (), ()| ()),
        }
    }

    pub fn difference(&self, other: &Self) -> Self {
        WBTreeSet {
            map: self.map.difference(&other.map, |_element, (), ()| None),
        }
    }
}

impl fmt::Debug for WBTreeSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// Iterator for WBTreeSet
pub struct WBTreeSetIter<'a> {
    map_iter: Iter<'a, ()>,
}

impl<'a> Iterator for WBTreeSetIter<'a> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        self.map_iter.next().map(|(k, _)| k)
    }
}
