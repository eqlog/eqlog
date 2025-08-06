use super::map::*;
use std::fmt;

pub struct WBTreeSet<'a, V: Clone> {
    map: WBTreeMap<'a, V, ()>,
}

impl<'a, V: Ord + Clone> WBTreeSet<'a, V> {
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

    pub fn iter<'cow>(&'cow self) -> WBTreeSetIter<'cow, 'a, V> {
        WBTreeSetIter {
            map_iter: self.map.iter(),
        }
    }
}

impl<'a, V: Ord + Clone> Default for WBTreeSet<'a, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, V: Ord + Clone> Clone for WBTreeSet<'a, V> {
    fn clone(&self) -> Self {
        WBTreeSet {
            map: self.map.clone(),
        }
    }
}

impl<'a, V: fmt::Debug + Ord + Clone> fmt::Debug for WBTreeSet<'a, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// Iterator for WBTreeSet
pub struct WBTreeSetIter<'cow, 'base, V: Clone> {
    map_iter: Iter<'cow, 'base, V, ()>,
}

impl<'cow, 'base, V: Clone> Iterator for WBTreeSetIter<'cow, 'base, V> {
    type Item = &'cow V;

    fn next(&mut self) -> Option<Self::Item> {
        self.map_iter.next().map(|(k, _)| k)
    }
}
