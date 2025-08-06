use super::map::*;
use std::fmt;

pub struct WBTreeSet<V> {
    map: WBTreeMap<V, ()>,
}

impl<V: Ord> WBTreeSet<V> {
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

    pub fn iter(&self) -> WBTreeSetIter<'_, V> {
        WBTreeSetIter {
            map_iter: self.map.iter(),
        }
    }
}

impl<V: Ord> Default for WBTreeSet<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Ord + Clone> Clone for WBTreeSet<V> {
    fn clone(&self) -> Self {
        WBTreeSet {
            map: self.map.clone(),
        }
    }
}

impl<V: fmt::Debug + Ord> fmt::Debug for WBTreeSet<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// Iterator for WBTreeSet
pub struct WBTreeSetIter<'a, V> {
    map_iter: Iter<'a, V, ()>,
}

impl<'a, V> Iterator for WBTreeSetIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.map_iter.next().map(|(k, _)| k)
    }
}
