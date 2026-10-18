use super::map::*;
use std::fmt;
use std::mem;

#[derive(Clone)]
pub struct WBTreeSet {
    storage: Storage,
}

#[derive(Clone)]
enum Storage {
    Empty,
    Singleton(u32),
    Tree(WBTreeMap<()>),
}

impl WBTreeSet {
    pub(crate) fn shares_root(&self, other: &Self) -> bool {
        match (&self.storage, &other.storage) {
            (Storage::Empty, Storage::Empty) => true,
            (Storage::Singleton(left), Storage::Singleton(right)) => left == right,
            (Storage::Tree(left), Storage::Tree(right)) => left.shares_root(right),
            (Storage::Empty, Storage::Singleton(_) | Storage::Tree(_))
            | (Storage::Singleton(_), Storage::Empty | Storage::Tree(_))
            | (Storage::Tree(_), Storage::Empty | Storage::Singleton(_)) => false,
        }
    }

    pub(crate) fn root_identity(&self) -> usize {
        match &self.storage {
            Storage::Empty => 0,
            Storage::Singleton(value) => usize::try_from(u64::from(*value) * 2 + 1)
                .expect("inline keys must fit tagged identities"),
            Storage::Tree(map) => map.root_identity(),
        }
    }

    pub const fn new() -> Self {
        Self {
            storage: Storage::Empty,
        }
    }

    fn singleton(value: u32) -> Self {
        // Odd identities cannot collide with aligned tree pointers. Large keys
        // stay allocated on platforms without room for the extra tag bit.
        let storage = if usize::try_from(u64::from(value) * 2 + 1).is_ok() {
            Storage::Singleton(value)
        } else {
            let mut map = WBTreeMap::new();
            map.insert(value, ());
            Storage::Tree(map)
        };
        Self { storage }
    }

    fn from_map(map: WBTreeMap<()>) -> Self {
        match map.len() {
            0 => Self::new(),
            1 => Self::singleton(map.iter().next().expect("singleton has one key").0),
            _ => Self {
                storage: Storage::Tree(map),
            },
        }
    }

    pub fn insert(&mut self, value: u32) -> bool {
        match &mut self.storage {
            Storage::Empty => {
                *self = Self::singleton(value);
                true
            }
            Storage::Singleton(existing) => {
                if *existing == value {
                    return false;
                }
                let mut map = WBTreeMap::new();
                map.insert(*existing, ());
                map.insert(value, ());
                self.storage = Storage::Tree(map);
                true
            }
            Storage::Tree(map) => map.insert(value, ()).is_none(),
        }
    }

    #[inline]
    pub fn contains(&self, value: &u32) -> bool {
        match &self.storage {
            Storage::Empty => false,
            Storage::Singleton(existing) => existing == value,
            Storage::Tree(map) => map.contains_key(value),
        }
    }

    pub fn remove(&mut self, value: &u32) -> bool {
        match &mut self.storage {
            Storage::Empty => false,
            Storage::Singleton(existing) => {
                if existing != value {
                    return false;
                }
                self.storage = Storage::Empty;
                true
            }
            Storage::Tree(map) => {
                let removed = map.remove(value).is_some();
                if removed && map.len() < 2 {
                    *self = Self::from_map(mem::replace(map, WBTreeMap::new()));
                }
                removed
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        match self.storage {
            Storage::Empty => true,
            Storage::Singleton(_) | Storage::Tree(_) => false,
        }
    }

    pub fn len(&self) -> usize {
        match &self.storage {
            Storage::Empty => 0,
            Storage::Singleton(_) => 1,
            Storage::Tree(map) => map.len(),
        }
    }

    pub(crate) fn len_upper_bound(&self) -> usize {
        self.len()
    }

    pub fn clear(&mut self) {
        self.storage = Storage::Empty;
    }

    pub fn iter(&self) -> WBTreeSetIter<'_> {
        let storage = match &self.storage {
            Storage::Empty => IterStorage::Inline(None),
            Storage::Singleton(value) => IterStorage::Inline(Some(*value)),
            Storage::Tree(map) => IterStorage::Tree(map.iter()),
        };
        WBTreeSetIter { storage }
    }

    pub fn union(&self, other: &Self) -> Self {
        match &self.storage {
            Storage::Empty => other.clone(),
            Storage::Singleton(value) => {
                let mut result = other.clone();
                result.insert(*value);
                result
            }
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => self.clone(),
                Storage::Singleton(value) => {
                    let mut result = self.clone();
                    result.insert(*value);
                    result
                }
                Storage::Tree(right) => {
                    Self::from_map(left.union_shared(right, |_element, (), ()| ()))
                }
            },
        }
    }

    pub fn intersection(&self, other: &Self) -> Self {
        match &self.storage {
            Storage::Empty => Self::new(),
            Storage::Singleton(value) => {
                if other.contains(value) {
                    self.clone()
                } else {
                    Self::new()
                }
            }
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => Self::new(),
                Storage::Singleton(value) => {
                    if left.contains_key(value) {
                        other.clone()
                    } else {
                        Self::new()
                    }
                }
                Storage::Tree(right) => Self::from_map(left.intersection_shared(
                    right,
                    |_key, (), ()| Some(()),
                    |(), ()| true,
                )),
            },
        }
    }

    pub fn difference(&self, other: &Self) -> Self {
        match &self.storage {
            Storage::Empty => Self::new(),
            Storage::Singleton(value) => {
                if other.contains(value) {
                    Self::new()
                } else {
                    self.clone()
                }
            }
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => self.clone(),
                Storage::Singleton(value) => {
                    let mut result = self.clone();
                    result.remove(value);
                    result
                }
                Storage::Tree(right) => Self::from_map(left.difference_shared(
                    right,
                    |_element, (), ()| None,
                    |(), ()| true,
                )),
            },
        }
    }

    pub(crate) fn all_difference(&self, other: &Self, mut visit: impl FnMut(u32) -> bool) -> bool {
        match &self.storage {
            Storage::Empty => true,
            Storage::Singleton(value) => other.contains(value) || visit(*value),
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => {
                    left.all_difference_entries(&WBTreeMap::new(), |key, (), _| visit(key))
                }
                Storage::Singleton(excluded) => left
                    .all_difference_entries(&WBTreeMap::new(), |key, (), _| {
                        key == *excluded || visit(key)
                    }),
                Storage::Tree(right) => left
                    .all_difference_entries(right, |key, (), value| value.is_some() || visit(key)),
            },
        }
    }

    pub fn difference_iter<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = u32> + 'a {
        match &self.storage {
            Storage::Empty => DifferenceIter::Inline(None),
            Storage::Singleton(value) => {
                DifferenceIter::Inline((!other.contains(value)).then_some(*value))
            }
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => DifferenceIter::Exclude {
                    iter: left.iter(),
                    excluded: None,
                },
                Storage::Singleton(value) => DifferenceIter::Exclude {
                    iter: left.iter(),
                    excluded: Some(*value),
                },
                Storage::Tree(right) => DifferenceIter::Shared(left.difference_entries(right)),
            },
        }
    }
}

impl fmt::Debug for WBTreeSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

pub struct WBTreeSetIter<'a> {
    storage: IterStorage<'a>,
}
enum IterStorage<'a> {
    Inline(Option<u32>),
    Tree(Iter<'a, ()>),
}

impl Iterator for WBTreeSetIter<'_> {
    type Item = u32;
    #[inline]
    fn next(&mut self) -> Option<u32> {
        match &mut self.storage {
            IterStorage::Inline(value) => value.take(),
            IterStorage::Tree(iter) => iter.next().map(|(key, ())| key),
        }
    }
}

enum DifferenceIter<'a> {
    Inline(Option<u32>),
    Exclude {
        iter: Iter<'a, ()>,
        excluded: Option<u32>,
    },
    Shared(Difference<'a, ()>),
}

impl Iterator for DifferenceIter<'_> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        match self {
            Self::Inline(value) => value.take(),
            Self::Exclude { iter, excluded } => {
                iter.find_map(|(key, ())| (Some(key) != *excluded).then_some(key))
            }
            Self::Shared(iter) => iter.find_map(|(key, (), right)| right.is_none().then_some(key)),
        }
    }
}
