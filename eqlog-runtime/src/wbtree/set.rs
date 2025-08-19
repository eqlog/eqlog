use super::map::*;
use std::fmt;

#[derive(Clone)]
pub struct WBTreeSet<V: Clone> {
    map: WBTreeMap<V, ()>,
}

impl<V: Ord + Clone> WBTreeSet<V> {
    pub const fn new() -> Self {
        WBTreeSet {
            map: WBTreeMap::new(),
        }
    }

    pub fn insert(&mut self, value: V) -> bool {
        self.map.insert(value, ()).is_none()
    }

    pub fn contains(&self, value: &V) -> bool {
        self.map.contains_key(value)
    }

    pub fn remove(&mut self, value: &V) -> bool {
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

    pub fn iter<'a>(&'a self) -> WBTreeSetIter<'a, V> {
        WBTreeSetIter {
            map_iter: self.map.iter(),
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        WBTreeSet {
            map: self.map.union(&other.map, |_element, (), ()| ()),
        }
    }
}

impl<V: fmt::Debug + Ord + Clone> fmt::Debug for WBTreeSet<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// Iterator for WBTreeSet
pub struct WBTreeSetIter<'a, V: Clone> {
    map_iter: Iter<'a, V, ()>,
}

impl<'a, V: Clone> Iterator for WBTreeSetIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.map_iter.next().map(|(k, _)| k)
    }
}
