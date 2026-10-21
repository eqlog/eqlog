use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::versions::SnapshotSet;
use crate::wbtree::mapping::MonotoneMap;
use crate::wbtree::{map, map::WBTreeMap, set::WBTreeSet};

// type definitions
#[derive(Clone, Debug)]
pub struct PrefixTree0(pub Option<()>);

#[derive(Clone, Debug)]
pub struct PrefixTree1 {
    pub set: WBTreeSet,
}

#[derive(Clone, Debug)]
pub struct PrefixTree2 {
    pub map: WBTreeMap<PrefixTree1>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree3 {
    pub map: WBTreeMap<PrefixTree2>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree4 {
    pub map: WBTreeMap<PrefixTree3>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree5 {
    pub map: WBTreeMap<PrefixTree4>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree6 {
    pub map: WBTreeMap<PrefixTree5>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree7 {
    pub map: WBTreeMap<PrefixTree6>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree8 {
    pub map: WBTreeMap<PrefixTree7>,
}

#[derive(Clone, Debug)]
pub struct PrefixTree9 {
    pub map: WBTreeMap<PrefixTree8>,
}

#[derive(Default)]
struct KeyReplacementCache {
    tree1: BTreeMap<usize, (PrefixTree1, Option<PrefixTree1>)>,
    tree2: BTreeMap<usize, (PrefixTree2, Option<PrefixTree2>)>,
    tree3: BTreeMap<usize, (PrefixTree3, Option<PrefixTree3>)>,
    tree4: BTreeMap<usize, (PrefixTree4, Option<PrefixTree4>)>,
    tree5: BTreeMap<usize, (PrefixTree5, Option<PrefixTree5>)>,
    tree6: BTreeMap<usize, (PrefixTree6, Option<PrefixTree6>)>,
    tree7: BTreeMap<usize, (PrefixTree7, Option<PrefixTree7>)>,
    tree8: BTreeMap<usize, (PrefixTree8, Option<PrefixTree8>)>,
    tree9: BTreeMap<usize, (PrefixTree9, Option<PrefixTree9>)>,
}

impl PrefixTree0 {
    pub fn replace_keys(&self, _replacements: [&BTreeMap<u32, u32>; 0]) -> Option<Self> {
        None
    }

    fn replace_keys_cached(
        &self,
        _replacements: [&BTreeMap<u32, u32>; 0],
        _cache: &mut KeyReplacementCache,
    ) -> Option<Self> {
        None
    }
}

macro_rules! replace_keys {
    (@overwrite $tree:ident, set, $key:expr, $subtree:expr) => {
        $tree.insert_restriction($key, $subtree)
    };
    (@overwrite $tree:ident, map, $key:expr, $subtree:expr) => {
        $tree.map.insert($key, $subtree)
    };
    ($tree:ident, $arity:literal, $storage:ident, $cache_field:ident) => {
        impl $tree {
            /// Returns `None` when no key changes, so callers can retain the original tree.
            pub fn replace_keys(
                &self,
                replacements: [&BTreeMap<u32, u32>; $arity],
            ) -> Option<Self> {
                if replacements.iter().all(|mapping| mapping.is_empty()) {
                    return None;
                }
                self.replace_keys_cached(replacements, &mut KeyReplacementCache::default())
            }

            fn replace_keys_cached(
                &self,
                replacements: [&BTreeMap<u32, u32>; $arity],
                cache: &mut KeyReplacementCache,
            ) -> Option<Self> {
                let identity = self.$storage.root_identity();
                if let Some((_, result)) = cache.$cache_field.get(&identity) {
                    return result.clone();
                }
                let result = self.replace_keys_uncached(replacements, cache);
                // Pin each input snapshot so its identity cannot be reused while
                // this call traverses shared suffixes. Cache absent changes too.
                cache
                    .$cache_field
                    .insert(identity, (self.clone(), result.clone()));
                result
            }

            fn replace_keys_uncached(
                &self,
                replacements: [&BTreeMap<u32, u32>; $arity],
                cache: &mut KeyReplacementCache,
            ) -> Option<Self> {
                let remaining = replacements[1..].try_into().unwrap();
                let mut changes = Vec::new();
                let suffix_changes = replacements[1..].iter().any(|mapping| !mapping.is_empty());
                if !suffix_changes && replacements[0].len() <= self.$storage.len_upper_bound() {
                    for (&old, &new) in replacements[0] {
                        if old == new {
                            continue;
                        }
                        if let Some(subtree) = self.get(old) {
                            changes.push((old, new, subtree.clone()));
                        }
                    }
                } else {
                    for (old, subtree) in self.iter_restrictions() {
                        let new = replacements[0].get(&old).copied().unwrap_or(old);
                        let replaced = if suffix_changes {
                            subtree.replace_keys_cached(remaining, cache)
                        } else {
                            None
                        };
                        if old != new || replaced.is_some() {
                            let result = replaced.unwrap_or_else(|| subtree.clone());
                            changes.push((old, new, result));
                        }
                    }
                }
                if changes.is_empty() {
                    return None;
                }
                let mut result = self.clone();
                // Set stationary values before merging incoming keys, and remove
                // moved keys before inserting replacements that may collide.
                for (old, new, subtree) in &changes {
                    if old == new {
                        replace_keys!(@overwrite result, $storage, *old, subtree.clone());
                    } else {
                        result.$storage.remove(old);
                    }
                }
                for (old, new, subtree) in changes {
                    if old != new {
                        result.insert_restriction(new, subtree);
                    }
                }
                Some(result)
            }
        }
    };
}

replace_keys!(PrefixTree1, 1, set, tree1);
replace_keys!(PrefixTree2, 2, map, tree2);
replace_keys!(PrefixTree3, 3, map, tree3);
replace_keys!(PrefixTree4, 4, map, tree4);
replace_keys!(PrefixTree5, 5, map, tree5);
replace_keys!(PrefixTree6, 6, map, tree6);
replace_keys!(PrefixTree7, 7, map, tree7);
replace_keys!(PrefixTree8, 8, map, tree8);
replace_keys!(PrefixTree9, 9, map, tree9);

macro_rules! replace_keys_in_prefixes {
    ($tree:ident, $suffix_arity:literal) => {
        impl $tree {
            pub fn replace_keys_in_prefixes(
                &self,
                prefixes: &[&BTreeSet<u32>],
                replacements: [&BTreeMap<u32, u32>; $suffix_arity],
            ) -> Option<Self> {
                if replacements.iter().all(|mapping| mapping.is_empty()) {
                    return None;
                }
                let mut cache = KeyReplacementCache::default();
                let mut result: Option<Self> = None;
                for &prefix in prefixes.iter().flat_map(|prefixes| prefixes.iter()) {
                    if let Some(subtree) = self.get(prefix) {
                        if let Some(replaced) =
                            subtree.replace_keys_cached(replacements, &mut cache)
                        {
                            result
                                .get_or_insert_with(|| self.clone())
                                .map
                                .insert(prefix, replaced);
                        }
                    }
                }
                result
            }
        }
    };
}

replace_keys_in_prefixes!(PrefixTree2, 1);
replace_keys_in_prefixes!(PrefixTree3, 2);
replace_keys_in_prefixes!(PrefixTree4, 3);
replace_keys_in_prefixes!(PrefixTree5, 4);
replace_keys_in_prefixes!(PrefixTree6, 5);
replace_keys_in_prefixes!(PrefixTree7, 6);
replace_keys_in_prefixes!(PrefixTree8, 7);
replace_keys_in_prefixes!(PrefixTree9, 8);

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
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree1::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree3 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree2) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree2::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree4 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree3) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree3::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree5 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree4) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree4::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree6 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree5) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree5::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree7 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree6) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree6::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree8 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree7) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree7::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
    }
}
impl PrefixTree9 {
    pub fn insert_restriction(&mut self, el0: u32, restriction: PrefixTree8) {
        if restriction.is_empty() {
            return;
        }

        self.map.update_entry(el0, PrefixTree8::new, |suffix| {
            suffix.union_assign_owned(restriction);
        });
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
            .update_entry(el0, PrefixTree1::new, |suffix| suffix.insert([el1]))
    }
}

impl PrefixTree3 {
    pub fn insert(&mut self, [el0, el1, el2]: [u32; 3]) -> bool {
        self.map
            .update_entry(el0, PrefixTree2::new, |suffix| suffix.insert([el1, el2]))
    }
}

impl PrefixTree4 {
    pub fn insert(&mut self, [el0, el1, el2, el3]: [u32; 4]) -> bool {
        self.map.update_entry(el0, PrefixTree3::new, |suffix| {
            suffix.insert([el1, el2, el3])
        })
    }
}

impl PrefixTree5 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4]: [u32; 5]) -> bool {
        self.map.update_entry(el0, PrefixTree4::new, |suffix| {
            suffix.insert([el1, el2, el3, el4])
        })
    }
}

impl PrefixTree6 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5]: [u32; 6]) -> bool {
        self.map.update_entry(el0, PrefixTree5::new, |suffix| {
            suffix.insert([el1, el2, el3, el4, el5])
        })
    }
}

impl PrefixTree7 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6]: [u32; 7]) -> bool {
        self.map.update_entry(el0, PrefixTree6::new, |suffix| {
            suffix.insert([el1, el2, el3, el4, el5, el6])
        })
    }
}

impl PrefixTree8 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7]: [u32; 8]) -> bool {
        self.map.update_entry(el0, PrefixTree7::new, |suffix| {
            suffix.insert([el1, el2, el3, el4, el5, el6, el7])
        })
    }
}

impl PrefixTree9 {
    pub fn insert(&mut self, [el0, el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 9]) -> bool {
        self.map.update_entry(el0, PrefixTree8::new, |suffix| {
            suffix.insert([el1, el2, el3, el4, el5, el6, el7, el8])
        })
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
    #[inline]
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
    #[inline]
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, PrefixTree0)> + '_ {
        self.set.iter().map(|x| (x, PrefixTree0(Some(()))))
    }
}
impl PrefixTree2 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree1)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree3 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree2)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree4 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree3)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree5 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree4)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree6 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree5)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree7 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree6)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree8 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree7)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

impl PrefixTree9 {
    pub fn iter_restrictions(&self) -> impl Iterator<Item = (u32, &PrefixTree8)> + '_ {
        self.map.iter().map(|(k, v)| (k, v))
    }
}

// iter_restrictions_mut methods
impl PrefixTree2 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree1)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree3 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree2)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree4 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree3)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree5 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree4)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree6 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree5)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree7 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree6)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree8 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree7)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
    }
}

impl PrefixTree9 {
    pub fn iter_restrictions_mut(&mut self) -> impl Iterator<Item = (u32, &mut PrefixTree8)> + '_ {
        self.map.iter_mut().map(|(k, v)| (k, v))
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
        self.set.iter().map(|x| [x])
    }
}

impl PrefixTree2 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 2]> + '_ {
        self.map
            .iter()
            .flat_map(|(k, v)| v.iter().map(move |[x]| [k, x]))
    }
}

impl PrefixTree3 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 3]> + '_ {
        self.map
            .iter()
            .flat_map(|(k, v)| v.iter().map(move |[x, y]| [k, x, y]))
    }
}

impl PrefixTree4 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 4]> + '_ {
        self.map
            .iter()
            .flat_map(|(k, v)| v.iter().map(move |[x, y, z]| [k, x, y, z]))
    }
}

impl PrefixTree5 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 5]> + '_ {
        self.map
            .iter()
            .flat_map(|(k, v)| v.iter().map(move |[x, y, z, a]| [k, x, y, z, a]))
    }
}

impl PrefixTree6 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 6]> + '_ {
        self.map
            .iter()
            .flat_map(|(k, v)| v.iter().map(move |[x, y, z, a, b]| [k, x, y, z, a, b]))
    }
}

impl PrefixTree7 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 7]> + '_ {
        self.map.iter().flat_map(|(k, v)| {
            v.iter()
                .map(move |[x, y, z, a, b, c]| [k, x, y, z, a, b, c])
        })
    }
}

impl PrefixTree8 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 8]> + '_ {
        self.map.iter().flat_map(|(k, v)| {
            v.iter()
                .map(move |[x, y, z, a, b, c, d]| [k, x, y, z, a, b, c, d])
        })
    }
}

impl PrefixTree9 {
    pub fn iter(&self) -> impl Iterator<Item = [u32; 9]> + '_ {
        self.map.iter().flat_map(|(k, v)| {
            v.iter()
                .map(move |[x, y, z, a, b, c, d, e]| [k, x, y, z, a, b, c, d, e])
        })
    }
}

// get methods
impl PrefixTree1 {
    #[inline]
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
    fn union_assign(&mut self, other: &Self) {
        self.set.union_assign(&other.set);
    }

    fn union_assign_owned(&mut self, other: Self) {
        self.set.union_assign(&other.set);
    }

    pub fn union(&self, other: &Self) -> Self {
        Self {
            set: self.set.union(&other.set),
        }
    }
}

macro_rules! union_assign_owned {
    ($tree:ident, $child:ident) => {
        impl $tree {
            fn union_assign_owned(&mut self, other: Self) {
                if self.map.shares_root(&other.map) || other.map.len_upper_bound() == 0 {
                    return;
                }
                if self.map.len_upper_bound() == 0 {
                    *self = other;
                    return;
                }
                if other.map.len_upper_bound() == 1 {
                    if let Some((key, value)) = other.map.into_single_entry() {
                        self.map.update_entry(key, $child::new, |suffix| {
                            suffix.union_assign_owned(value);
                        });
                    }
                    return;
                }
                self.map
                    .union_assign_owned_shared(other.map, |_key, mut left, right| {
                        left.union_assign_owned(right);
                        left
                    });
            }
        }
    };
}

union_assign_owned!(PrefixTree2, PrefixTree1);
union_assign_owned!(PrefixTree3, PrefixTree2);
union_assign_owned!(PrefixTree4, PrefixTree3);
union_assign_owned!(PrefixTree5, PrefixTree4);
union_assign_owned!(PrefixTree6, PrefixTree5);
union_assign_owned!(PrefixTree7, PrefixTree6);
union_assign_owned!(PrefixTree8, PrefixTree7);

macro_rules! union_assign {
    ($tree:ident, $child:ident) => {
        impl $tree {
            fn union_assign(&mut self, other: &Self) {
                if self.map.shares_root(&other.map) || other.map.len_upper_bound() == 0 {
                    return;
                }
                if self.map.len_upper_bound() == 0 {
                    *self = other.clone();
                    return;
                }
                // A singleton suffix can reuse the existing path through every remaining column.
                if other.map.len_upper_bound() == 1 {
                    if let Some((key, value)) = other.map.iter().next() {
                        self.map.update_entry(key, $child::new, |suffix| {
                            suffix.union_assign(value);
                        });
                    }
                    return;
                }
                self.map
                    .union_assign_shared(&other.map, |_key, mut left, right| {
                        left.union_assign(&right);
                        left
                    });
            }
        }
    };
}

union_assign!(PrefixTree2, PrefixTree1);
union_assign!(PrefixTree3, PrefixTree2);
union_assign!(PrefixTree4, PrefixTree3);
union_assign!(PrefixTree5, PrefixTree4);
union_assign!(PrefixTree6, PrefixTree5);
union_assign!(PrefixTree7, PrefixTree6);
union_assign!(PrefixTree8, PrefixTree7);
union_assign!(PrefixTree9, PrefixTree8);

impl PrefixTree2 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree3 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree4 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree5 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree6 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree7 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree8 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree9 {
    pub fn union(&self, other: &Self) -> Self {
        let map = self
            .map
            .union_shared(&other.map, |_key, val1, val2| val1.union(&val2));
        Self { map }
    }
}

impl PrefixTree0 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.0.is_none() || other.0.is_some()
    }
}

impl PrefixTree1 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.set.all_difference(&other.set, |_| false)
    }
}

impl PrefixTree2 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree3 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree4 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree5 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree6 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree7 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree8 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

impl PrefixTree9 {
    pub fn is_subset(&self, other: &Self) -> bool {
        self.map
            .all_difference_entries(&other.map, |_, left, right| match right {
                Some(right) => left.is_subset(right),
                None => left.is_empty(),
            })
    }
}

// A visitor avoids allocating intermediate tuple sets when callers only need edits.
impl PrefixTree0 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 0])) {
        if self.0.is_some() && other.0.is_none() {
            visit([]);
        }
    }
}

impl PrefixTree1 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 1])) {
        self.set.all_difference(&other.set, |key| {
            visit([key]);
            true
        });
    }
}

impl PrefixTree2 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 2])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1]: [u32; 1]| visit([key, el1]);
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree1::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree3 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 3])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1, el2]: [u32; 2]| visit([key, el1, el2]);
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree2::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree4 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 4])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1, el2, el3]: [u32; 3]| visit([key, el1, el2, el3]);
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree3::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree5 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 5])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1, el2, el3, el4]: [u32; 4]| visit([key, el1, el2, el3, el4]);
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree4::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree6 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 6])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix =
                    |[el1, el2, el3, el4, el5]: [u32; 5]| visit([key, el1, el2, el3, el4, el5]);
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree5::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree7 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 7])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1, el2, el3, el4, el5, el6]: [u32; 6]| {
                    visit([key, el1, el2, el3, el4, el5, el6])
                };
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree6::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree8 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 8])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1, el2, el3, el4, el5, el6, el7]: [u32; 7]| {
                    visit([key, el1, el2, el3, el4, el5, el6, el7])
                };
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree7::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree9 {
    pub fn visit_difference(&self, other: &Self, visit: &mut impl FnMut([u32; 9])) {
        self.map
            .all_difference_entries(&other.map, |key, left, right| {
                let mut suffix = |[el1, el2, el3, el4, el5, el6, el7, el8]: [u32; 8]| {
                    visit([key, el1, el2, el3, el4, el5, el6, el7, el8])
                };
                match right {
                    Some(right) => left.visit_difference(right, &mut suffix),
                    None => left.visit_difference(&PrefixTree8::new(), &mut suffix),
                }
                true
            });
    }
}

impl PrefixTree0 {
    pub fn intersection(&self, other: &Self) -> Self {
        Self(self.0.and(other.0))
    }
}

impl PrefixTree1 {
    pub fn intersection(&self, other: &Self) -> Self {
        Self {
            set: self.set.intersection(&other.set),
        }
    }
}

macro_rules! intersection {
    ($($tree:ident),*) => {$(
        impl $tree {
            pub fn intersection(&self, other: &Self) -> Self {
                let map = self.map.intersection_shared(&other.map, |_key, left, right| {
                    let result = left.intersection(right);
                    (!result.is_empty()).then_some(result)
                }, |left, right| left.shares_root(right));
                Self { map }
            }
        }
    )*};
}

intersection!(
    PrefixTree2,
    PrefixTree3,
    PrefixTree4,
    PrefixTree5,
    PrefixTree6,
    PrefixTree7,
    PrefixTree8,
    PrefixTree9
);

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
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree3 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree4 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree5 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree6 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree7 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree8 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
        Self { map }
    }
}

impl PrefixTree9 {
    pub fn difference(&self, other: &Self) -> Self {
        let map = self.map.difference_shared(
            &other.map,
            |_key, val1, val2| {
                let diff_result = val1.difference(&val2);
                if diff_result.is_empty() {
                    None
                } else {
                    Some(diff_result)
                }
            },
            SnapshotSet::shares_root,
        );
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
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
                if occupied_entry.get_mut().is_empty() {
                    occupied_entry.remove();
                }
            }
            map::Entry::Vacant(_) => {}
        }
    }
}

// Preparing maps once per column avoids rescanning their rows at every prefix.
struct ColumnMapping {
    relation: PrefixTree2,
    monotone: OnceCell<Option<MonotoneMap>>,
}

const EAGER_MAPPING_BUDGET: usize = 8;
const MAX_EAGER_MAPPING_BUDGET: usize = 4096;

impl ColumnMapping {
    fn new(relation: PrefixTree2) -> Self {
        Self {
            relation,
            monotone: OnceCell::new(),
        }
    }

    fn monotone_for(&self, source_len: usize) -> Option<&MonotoneMap> {
        // A small source delta is cheaper to map directly than to prepare a large image map.
        if self.monotone.get().is_none() && source_len < self.relation.map.len_upper_bound() {
            return None;
        }
        self.monotone
            .get_or_init(|| MonotoneMap::new(&self.relation))
            .as_ref()
    }
}

fn prepare_monotone_maps<const N: usize>(
    mappings: [Option<&ColumnMapping>; N],
    source_len: usize,
) -> Option<[Option<MonotoneMap>; N]> {
    let mut prepared: [Option<MonotoneMap>; N] = std::array::from_fn(|_| None);
    for (target, mapping) in prepared.iter_mut().zip(mappings) {
        if let Some(mapping) = mapping {
            *target = Some(mapping.monotone_for(source_len)?.clone());
        }
    }
    Some(prepared)
}

fn suffix_mapping_work<const N: usize>(maps: &[Option<MonotoneMap>; N]) -> u64 {
    // A first access can search for a surviving row at every suffix level.
    let lookups = maps.iter().flatten().fold(1u64, |work, map| {
        work.saturating_add(map.run_count() as u64)
            .saturating_add(1)
    });
    lookups.saturating_mul(2 * (N as u64 + 1))
}

impl PrefixTree0 {
    pub fn mapped(&self) -> Self {
        self.clone()
    }

    pub fn mapped_shared(&self, _maps: [Option<MonotoneMap>; 0]) -> Self {
        self.clone()
    }
}

impl PrefixTree1 {
    pub fn mapped_shared(&self, maps: [Option<MonotoneMap>; 1]) -> Self {
        self.mapped_monotone(maps)
    }

    pub fn mapped(&self, map0: Option<PrefixTree2>) -> Self {
        let map0 = map0.map(ColumnMapping::new);
        self.mapped_prepared(map0.as_ref())
    }

    fn mapped_prepared(&self, map0: Option<&ColumnMapping>) -> Self {
        let Some(mapping) = map0 else {
            return self.clone();
        };
        if let Some(monotone) = mapping.monotone_for(self.set.len_upper_bound()) {
            return Self {
                set: self.set.mapped(monotone.clone()),
            };
        }
        let mut result = Self::new();
        for key in self.set.iter() {
            if let Some(images) = mapping.relation.get(key) {
                if result.is_empty() {
                    result = images.clone();
                    continue;
                }
                for [image] in images.iter() {
                    result.set.insert(image);
                }
            }
        }
        result
    }

    fn extend_mapped_prepared(&mut self, source: &Self, mapping: Option<&ColumnMapping>) {
        let mapped = source.mapped_prepared(mapping);
        if !mapped.is_empty() {
            self.union_assign(&mapped);
        }
    }

    fn mapped_monotone(&self, [mapping]: [Option<MonotoneMap>; 1]) -> Self {
        match mapping {
            None => self.clone(),
            Some(mapping) => Self {
                set: self.set.mapped(mapping),
            },
        }
    }

    fn fits_materialized_budget(&self, budget: &mut usize) -> bool {
        self.set.fits_materialized_budget(budget)
    }
}

macro_rules! mapped_tree {
    ($tree:ident, $arity:literal, $($map:ident),+) => {
        impl $tree {
            /// Prepared maps can share sparse relations without materializing
            /// their small suffixes at every inherited owner.
            pub fn mapped_shared(&self, maps: [Option<MonotoneMap>; $arity]) -> Self {
                self.mapped_monotone_impl(maps, false)
            }

            pub fn mapped(&self, map0: Option<PrefixTree2>, $($map: Option<PrefixTree2>),+) -> Self {
                let map0 = map0.map(ColumnMapping::new);
                $(let $map = $map.map(ColumnMapping::new);)+
                self.mapped_prepared(map0.as_ref(), $($map.as_ref()),+)
            }

            fn mapped_prepared(&self, map0: Option<&ColumnMapping>, $($map: Option<&ColumnMapping>),+) -> Self {
                let mut result = Self::new();
                result.extend_mapped_prepared(self, map0, $($map),+);
                result
            }

            fn extend_mapped_prepared(&mut self, source: &Self, map0: Option<&ColumnMapping>, $($map: Option<&ColumnMapping>),+) {
                if source.map.len_upper_bound() == 0
                    || [map0, $($map),+].into_iter().flatten()
                        .any(|mapping| mapping.relation.map.len_upper_bound() == 0)
                {
                    return;
                }
                if let Some(maps) = prepare_monotone_maps([map0, $($map),+], source.map.len_upper_bound()) {
                    let mapped = source.mapped_monotone(maps);
                    if self.map.len_upper_bound() == 0 {
                        *self = mapped;
                    } else if !mapped.is_empty() {
                        self.union_assign(&mapped);
                    }
                    return;
                }
                self.extend_mapped_eager(source, map0, $($map),+);
            }

            fn extend_mapped_eager(&mut self, source: &Self, map0: Option<&ColumnMapping>, $($map: Option<&ColumnMapping>),+) {
                for (key, value) in source.map.iter() {
                    let image = match map0 {
                        None => key,
                        Some(mapping) => {
                            let Some(images) = mapping.relation.get(key) else {
                                continue;
                            };
                            let mut images = images.iter();
                            let Some([first]) = images.next() else {
                                continue;
                            };
                            if let Some([second]) = images.next() {
                                // Multiple images can share one transformed suffix.
                                let mapped = value.mapped_prepared($($map),+);
                                self.insert_restriction(first, mapped.clone());
                                self.insert_restriction(second, mapped.clone());
                                for [image] in images {
                                    self.insert_restriction(image, mapped.clone());
                                }
                                continue;
                            }
                            first
                        }
                    };
                    if let Some(existing) = self.map.get_mut(&image) {
                        // Colliding head images need no intermediate suffix tree.
                        existing.extend_mapped_prepared(value, $($map),+);
                    } else {
                        self.insert_restriction(image, value.mapped_prepared($($map),+));
                    }
                }
            }

            fn fits_materialized_budget(&self, budget: &mut usize) -> bool {
                self.map.fits_materialized_budget(budget, |value, budget| {
                    value.fits_materialized_budget(budget)
                })
            }

            fn mapped_monotone(&self, [map0, $($map),+]: [Option<MonotoneMap>; $arity]) -> Self {
                self.mapped_monotone_impl([map0, $($map),+], true)
            }

            fn mapped_monotone_impl(&self, [map0, $($map),+]: [Option<MonotoneMap>; $arity], allow_eager: bool) -> Self {
                let suffix = [$($map),+];
                if suffix.iter().flatten().any(|mapping| mapping.run_count() == 0) {
                    return Self::new();
                }
                let suffix_unchanged = suffix.iter().all(Option::is_none);
                if map0.is_none() && suffix_unchanged {
                    return self.clone();
                }
                // Only bounded materialized suffixes have cheap emptiness checks.
                // Preflight rejects existing lazy children without forcing them.
                let eager_limit = if suffix_unchanged {
                    EAGER_MAPPING_BUDGET
                } else {
                    MAX_EAGER_MAPPING_BUDGET
                };
                // Wide sparse prefixes avoid caches while dense suffixes retain sharing.
                let mut budget = eager_limit.min(
                    self.map.len_upper_bound().saturating_mul(EAGER_MAPPING_BUDGET)
                        .max(EAGER_MAPPING_BUDGET)
                );
                if allow_eager && (suffix_unchanged || self.fits_materialized_budget(&mut budget)) {
                    if let Some(map) = self.map.mapped_small_entries(map0.as_ref(), eager_limit, |value| {
                        let value = value.mapped_monotone(suffix.clone());
                        (suffix_unchanged || !value.is_empty()).then_some(value)
                    }) {
                        return Self { map };
                    }
                }
                if suffix_unchanged {
                    return match map0 {
                        None => self.clone(),
                        Some(mapping) => Self { map: self.map.mapped_keys(mapping) },
                    };
                }
                let work = suffix_mapping_work(&suffix);
                Self {
                    map: self.map.mapped_entries_with_work(map0, work, move |value| {
                        let value = if allow_eager {
                            value.mapped_monotone(suffix.clone())
                        } else {
                            value.mapped_shared(suffix.clone())
                        };
                        (!value.is_empty()).then_some(value)
                    }),
                }
            }
        }
    };
}

mapped_tree!(PrefixTree2, 2, map1);
mapped_tree!(PrefixTree3, 3, map1, map2);
mapped_tree!(PrefixTree4, 4, map1, map2, map3);
mapped_tree!(PrefixTree5, 5, map1, map2, map3, map4);
mapped_tree!(PrefixTree6, 6, map1, map2, map3, map4, map5);
mapped_tree!(PrefixTree7, 7, map1, map2, map3, map4, map5, map6);
mapped_tree!(PrefixTree8, 8, map1, map2, map3, map4, map5, map6, map7);
mapped_tree!(
    PrefixTree9,
    9,
    map1,
    map2,
    map3,
    map4,
    map5,
    map6,
    map7,
    map8
);
