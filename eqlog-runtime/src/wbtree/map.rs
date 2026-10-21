use std::cell::OnceCell;
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::num::NonZeroUsize;
use std::rc::Rc;

use super::mapping::MonotoneMap;
use crate::{Error, Fuel, PrefixTree2};

mod difference;
pub use difference::Difference;

#[derive(Clone)]
pub struct WBTreeMap<V: Clone> {
    root: Option<Rc<Node<V>>>,
    len: SizeBound,
}

#[derive(Clone, Copy)]
struct SizeBound(usize);

impl SizeBound {
    // Keeping the exactness flag in the count avoids enlarging every prefix-tree value.
    const INEXACT: usize = 1 << (usize::BITS - 1);

    const fn exact(count: usize) -> Self {
        assert!(
            count < Self::INEXACT,
            "tree size exceeds the supported bound"
        );
        Self(count)
    }

    fn upper_bound(self) -> usize {
        self.0 & !Self::INEXACT
    }

    fn is_exact(self) -> bool {
        self.0 & Self::INEXACT == 0
    }

    fn inexact(self) -> Self {
        Self(self.0 | Self::INEXACT)
    }

    fn combined(count: usize, left: Self, right: Self) -> Self {
        let count = Self::exact(count);
        Self(count.0 | ((left.0 | right.0) & Self::INEXACT))
    }

    fn inserted(&mut self, inserted: bool) {
        let count = self
            .upper_bound()
            .checked_add(usize::from(inserted))
            .expect("tree size overflow");
        *self = Self::combined(count, *self, *self);
    }

    fn removed(&mut self) {
        let count = self
            .upper_bound()
            .checked_sub(1)
            .expect("a removed key contributes to the size bound");
        *self = Self::combined(count, *self, *self);
    }
}

#[derive(Clone)]
struct DataNode<V: Clone> {
    key: u32,
    value: V,
    left: Option<Rc<Node<V>>>,
    right: Option<Rc<Node<V>>>,
    // Zero can distinguish mapped storage because a data node always contributes one entry.
    size: NonZeroUsize,
}

impl<V: Clone> DataNode<V> {
    fn update_size_internal(&mut self) {
        self.size = Node::joined_size(&self.left, &self.right);
    }
}

#[derive(Clone)]
struct MappingNode<V: Clone> {
    transform: Rc<MappingTransform<V>>,
    child: Option<Rc<Node<V>>>,
    exposed: OnceCell<Option<Rc<Node<V>>>>,
}

impl<V: Clone> Drop for MappingNode<V> {
    fn drop(&mut self) {
        let mut child = self.child.take();
        // Retain the child while releasing cached views and their source aliases.
        // Long morphism chains then need no recursive Rc destruction.
        drop(self.exposed.take());
        if let Some(transform) = Rc::get_mut(&mut self.transform) {
            drop(transform.keys.take());
            drop(transform.values.take());
        }
        while let Some(node) = child {
            match Rc::try_unwrap(node) {
                Ok(Node::Mapping(mut mapping)) => child = mapping.child.take(),
                Ok(Node::Data(_)) | Err(_) => return,
            }
        }
    }
}

struct MappingTransform<V: Clone> {
    keys: Option<MonotoneMap>,
    values: Option<ValueMapping<V>>,
}

struct ValueMapping<V: Clone> {
    apply: Box<dyn Fn(&V) -> Option<V>>,
    cache: ValueCache<V>,
    source: Rc<Node<V>>,
    source_offset: u32,
    lookup_work: OnceCell<u64>,
    work_factor: u64,
}

impl<V: Clone> ValueMapping<V> {
    fn source_for_cache(source: &Rc<Node<V>>) -> (Rc<Node<V>>, u32) {
        let mut current = source;
        let mut offset = 0u32;
        loop {
            match current.as_ref() {
                Node::Data(_) => return (current.clone(), offset),
                Node::Mapping(mapping) => {
                    let shift = match &mapping.transform.keys {
                        None => 0,
                        Some(keys) => {
                            let Some(shift) = keys.single_offset() else {
                                return (current.clone(), offset);
                            };
                            shift
                        }
                    };
                    let next_offset = offset.wrapping_add(shift);
                    let Some(child) = &mapping.child else {
                        return (current.clone(), offset);
                    };
                    match child.as_ref() {
                        Node::Data(_) => return (child.clone(), next_offset),
                        Node::Mapping(_) => {}
                    }
                    if let Some(values) = &mapping.transform.values {
                        // Cache coordinates do not depend on the intervening value
                        // transforms, so a new view can reuse their raw origin.
                        return (
                            values.source.clone(),
                            next_offset.wrapping_add(values.source_offset),
                        );
                    }
                    offset = next_offset;
                    current = child;
                }
            }
        }
    }

    fn map_value<'a>(&'a self, raw_key: u32, value: &'a V) -> Option<&'a V> {
        // The actual lookup has checked every mapped domain. Wrapping also
        // represents negative offsets without a branch in this cache lookup.
        let mut raw_key = raw_key.wrapping_sub(self.source_offset);
        let mut current = Some(self.source.as_ref());
        let mut cache = &self.cache;
        // A snapshot's raw topology gives cache entries stable addresses without
        // allocating slots for values that a lookup never visits.
        while let Some(node) = current {
            match node {
                Node::Data(data) => match raw_key.cmp(&data.key) {
                    Ordering::Less => {
                        current = data.left.as_deref();
                        cache = cache.left.get_or_init(|| Box::new(ValueCache::new()));
                    }
                    Ordering::Greater => {
                        current = data.right.as_deref();
                        cache = cache.right.get_or_init(|| Box::new(ValueCache::new()));
                    }
                    Ordering::Equal => {
                        return cache.value.get_or_init(|| (self.apply)(value)).as_ref()
                    }
                },
                Node::Mapping(mapping) => {
                    if let Some(keys) = &mapping.transform.keys {
                        raw_key = keys.preimage(raw_key)?;
                    }
                    current = mapping.child.as_deref();
                }
            }
        }
        unreachable!("a mapped value belongs to the source snapshot")
    }

    fn lookup_work(&self, fuel: &mut Fuel) -> Result<u64, Error> {
        if let Some(work) = self.lookup_work.get() {
            return Ok(*work);
        }
        let mut work = 0;
        let mut pending = vec![(&self.source, 0u64)];
        while let Some((node, depth)) = pending.pop() {
            fuel.consume(1)?;
            let depth = depth.saturating_add(1);
            work = work.max(depth);
            match node.as_ref() {
                Node::Data(data) => {
                    if let Some(left) = &data.left {
                        pending.push((left, depth));
                    }
                    if let Some(right) = &data.right {
                        pending.push((right, depth));
                    }
                }
                Node::Mapping(mapping) => {
                    if let Some(child) = &mapping.child {
                        let work = mapping
                            .transform
                            .keys
                            .as_ref()
                            .map_or(0, |keys| keys.run_count() as u64);
                        pending.push((child, depth.saturating_add(work)));
                    }
                }
            }
        }
        self.lookup_work
            .set(work)
            .expect("the cache is initialized once");
        Ok(work)
    }
}

struct ValueCache<V> {
    value: OnceCell<Option<V>>,
    left: OnceCell<Box<ValueCache<V>>>,
    right: OnceCell<Box<ValueCache<V>>>,
}

impl<V> ValueCache<V> {
    fn new() -> Self {
        Self {
            value: OnceCell::new(),
            left: OnceCell::new(),
            right: OnceCell::new(),
        }
    }
}

impl<V: Clone> MappingNode<V> {
    fn map_value<'a>(&'a self, raw_key: u32, value: &'a V) -> Option<&'a V> {
        match &self.transform.values {
            None => Some(value),
            Some(values) => values.map_value(raw_key, value),
        }
    }

    fn wrap(&self, child: Option<Rc<Node<V>>>) -> Option<Rc<Node<V>>> {
        child.map(|child| {
            Rc::new(Node::Mapping(Self {
                transform: self.transform.clone(),
                child: Some(child),
                exposed: OnceCell::new(),
            }))
        })
    }

    fn expose(&self) -> &Option<Rc<Node<V>>> {
        self.exposed.get_or_init(|| {
            let child = Node::expose(self.child.clone())?;
            let data = match child.as_ref() {
                Node::Data(data) => data,
                Node::Mapping(_) => unreachable!("exposure resolves the root"),
            };
            let left = self.wrap(data.left.clone());
            let right = self.wrap(data.right.clone());
            let key = match &self.transform.keys {
                Some(mapping) => mapping.apply(data.key),
                None => Some(data.key),
            };
            let value = key.and_then(|_| self.map_value(data.key, &data.value));
            match (key, value) {
                (Some(key), Some(value)) => {
                    Some(Node::new_data_node(key, value.clone(), left, right))
                }
                (None, None) | (Some(_), None) => Node::concat(left, right),
                (None, Some(_)) => unreachable!("filtered keys do not map their values"),
            }
        })
    }

    fn same_mapping(&self, other: &Self) -> bool {
        let keys = match (&self.transform.keys, &other.transform.keys) {
            (None, None) => true,
            (Some(left), Some(right)) => left.same_snapshot(right),
            (Some(_), None) | (None, Some(_)) => false,
        };
        let values = match (&self.transform.values, &other.transform.values) {
            (None, None) => true,
            (Some(left), Some(right)) => std::ptr::eq(left, right),
            (Some(_), None) | (None, Some(_)) => false,
        };
        keys && values
    }
}

#[derive(Clone)]
enum Node<V: Clone> {
    Data(DataNode<V>),
    Mapping(MappingNode<V>),
}

// Traversal accumulates outer mappings first, but keys start in the inner domain.
fn apply_mappings<V: Clone>(mappings: &[&MappingNode<V>], val: u32) -> Option<u32> {
    let mut result = val;
    for mapping in mappings.iter().rev() {
        if let Some(keys) = &mapping.transform.keys {
            result = keys.apply(result)?;
        }
    }
    Some(result)
}

fn apply_value_mappings<'a, V: Clone>(
    mappings: impl ExactSizeIterator<Item = &'a MappingNode<V>> + DoubleEndedIterator,
    mut raw_key: u32,
    mut value: &'a V,
) -> Option<&'a V> {
    for (index, mapping) in mappings.enumerate().rev() {
        value = mapping.map_value(raw_key, value)?;
        if index > 0 {
            if let Some(keys) = &mapping.transform.keys {
                raw_key = keys.apply(raw_key)?;
            }
        }
    }
    Some(value)
}

// Weight balance parameters
const DELTA: usize = 3;
const GAMMA: usize = 2;

fn too_heavy(weight: usize, other: usize) -> bool {
    weight > other.saturating_mul(DELTA)
}

fn needs_double_rotation(inner: usize, outer: usize) -> bool {
    inner / GAMMA >= outer
}

impl<V: Clone> Node<V> {
    fn all_data_values(node: &Option<Rc<Self>>, visit: &mut impl FnMut(&V) -> bool) -> bool {
        let Some(node) = node else {
            return true;
        };
        let data = match node.as_ref() {
            Self::Data(data) => data,
            Self::Mapping(_) => unreachable!("the caller requires materialized entries"),
        };
        visit(&data.value)
            && Self::all_data_values(&data.left, visit)
            && Self::all_data_values(&data.right, visit)
    }

    fn map_data_entries(
        node: &Option<Rc<Self>>,
        keys: Option<&MonotoneMap>,
        values: &impl Fn(&V) -> Option<V>,
    ) -> Option<Rc<Self>> {
        let node = node.as_ref()?;
        let data = match node.as_ref() {
            Self::Data(data) => data,
            Self::Mapping(_) => unreachable!("the caller requires materialized entries"),
        };
        let left = Self::map_data_entries(&data.left, keys, values);
        let right = Self::map_data_entries(&data.right, keys, values);
        let entry = keys
            .map_or(Some(data.key), |keys| keys.apply(data.key))
            .and_then(|key| values(&data.value).map(|value| (key, value)));
        match entry {
            Some((key, value)) => Self::join(left, key, value, right),
            None => Self::concat(left, right),
        }
    }

    fn from_sorted_iter(
        len: usize,
        entries: &mut impl Iterator<Item = (u32, V)>,
    ) -> Option<Rc<Self>> {
        if len == 0 {
            return None;
        }
        let left_len = len / 2;
        let left = Self::from_sorted_iter(left_len, entries);
        let (key, value) = entries.next().expect("sorted entry count is exact");
        let right = Self::from_sorted_iter(len - left_len - 1, entries);
        Some(Self::new_data_node(key, value, left, right))
    }

    fn new(key: u32, value: V) -> Self {
        Self::Data(DataNode {
            key,
            value,
            left: None,
            right: None,
            size: NonZeroUsize::MIN,
        })
    }

    fn expose_mapping_chain(mapping: &MappingNode<V>) -> &Option<Rc<Self>> {
        if let Some(exposed) = mapping.exposed.get() {
            return exposed;
        }
        let mut pending = Vec::new();
        let mut current = mapping.child.as_deref();
        while let Some(node) = current {
            match node {
                Self::Data(_) => break,
                Self::Mapping(inner) => {
                    if inner.exposed.get().is_some() {
                        break;
                    }
                    pending.push(inner);
                    current = inner.child.as_deref();
                }
            }
        }
        // Morphism chains may be much deeper than their balanced source trees.
        // Resolve their dependencies before exposing pivots on the call stack.
        for inner in pending.into_iter().rev() {
            inner.expose();
        }
        mapping.expose()
    }

    #[inline]
    fn expose(node: Option<Rc<Self>>) -> Option<Rc<Self>> {
        let node = node?;
        match node.as_ref() {
            Self::Data(_) => Some(node),
            Self::Mapping(_) => Self::expose_mapped(node),
        }
    }

    // Keep deferred resolution out of ordinary updates' inlining budget.
    #[inline(never)]
    fn expose_mapped(mut node: Rc<Self>) -> Option<Rc<Self>> {
        loop {
            let next = match node.as_ref() {
                Self::Data(_) => return Some(node),
                Self::Mapping(mapping) => Self::expose_mapping_chain(mapping).clone()?,
            };
            node = next;
        }
    }

    fn data(mut node: &Rc<Self>) -> Option<&DataNode<V>> {
        loop {
            match node.as_ref() {
                Self::Data(data) => return Some(data),
                Self::Mapping(mapping) => node = Self::expose_mapping_chain(mapping).as_ref()?,
            }
        }
    }

    fn data_mut(node: &mut Rc<Self>) -> &mut DataNode<V> {
        match Rc::make_mut(node) {
            Self::Data(data) => data,
            Self::Mapping(_) => unreachable!("expose the root before editing it"),
        }
    }

    fn unwrap_to_data(node: Rc<Self>) -> DataNode<V> {
        match Rc::unwrap_or_clone(node) {
            Self::Data(data) => data,
            Self::Mapping(_) => unreachable!("expose the root before editing it"),
        }
    }

    /// Create a new data node with the given fields
    fn new_data_node(
        key: u32,
        value: V,
        left: Option<Rc<Node<V>>>,
        right: Option<Rc<Node<V>>>,
    ) -> Rc<Node<V>> {
        let size = Self::joined_size(&left, &right);
        Rc::new(Node::Data(DataNode {
            key,
            value,
            left,
            right,
            size,
        }))
    }

    fn joined_size(left: &Option<Rc<Self>>, right: &Option<Rc<Self>>) -> NonZeroUsize {
        let size = Self::size(left)
            .checked_add(Self::size(right))
            .and_then(|size| size.checked_add(1))
            .expect("tree size overflow");
        NonZeroUsize::new(size).expect("a data node contributes to its subtree size")
    }

    fn size(node: &Option<Rc<Node<V>>>) -> usize {
        let mut current = node.as_deref();
        while let Some(node) = current {
            match node {
                Node::Data(data) => return data.size.get(),
                Node::Mapping(mapping) => current = mapping.child.as_deref(),
            }
        }
        0
    }

    fn rotate_left(mut node: Rc<Self>) -> Rc<Self> {
        let data = Self::data_mut(&mut node);
        let mut right = Self::expose(data.right.take()).expect("a rotation needs a nonempty child");
        let right_data = Self::data_mut(&mut right);
        data.right = right_data.left.take();
        data.update_size_internal();
        right_data.left = Some(node);
        right_data.update_size_internal();
        right
    }

    fn rotate_right(mut node: Rc<Self>) -> Rc<Self> {
        let data = Self::data_mut(&mut node);
        let mut left = Self::expose(data.left.take()).expect("a rotation needs a nonempty child");
        let left_data = Self::data_mut(&mut left);
        data.left = left_data.right.take();
        data.update_size_internal();
        left_data.right = Some(node);
        left_data.update_size_internal();
        left
    }

    fn balance(mut node: Rc<Self>) -> Rc<Self> {
        let (left_size, right_size) = match node.as_ref() {
            Self::Data(data) => (Self::size(&data.left), Self::size(&data.right)),
            Self::Mapping(_) => unreachable!("expose a pivot before balancing it"),
        };
        if left_size + right_size < 2 {
            return node;
        }
        let left_weight = left_size + 1;
        let right_weight = right_size + 1;
        if too_heavy(right_weight, left_weight) {
            let data = Self::data_mut(&mut node);
            data.right = Self::expose(data.right.take());
            data.update_size_internal();
            if Self::size(&data.right) != right_size {
                return Self::balance(node);
            }
            let right = Self::data_mut(data.right.as_mut().expect("the heavy child is nonempty"));
            if needs_double_rotation(Self::size(&right.left) + 1, Self::size(&right.right) + 1) {
                let inner_size = Self::size(&right.left);
                right.left = Self::expose(right.left.take());
                right.update_size_internal();
                let shrank = Self::size(&right.left) != inner_size;
                data.update_size_internal();
                if shrank {
                    return Self::balance(node);
                }
                data.right = data.right.take().map(Self::rotate_right);
            }
            Self::rotate_left(node)
        } else if too_heavy(left_weight, right_weight) {
            let data = Self::data_mut(&mut node);
            data.left = Self::expose(data.left.take());
            data.update_size_internal();
            if Self::size(&data.left) != left_size {
                return Self::balance(node);
            }
            let left = Self::data_mut(data.left.as_mut().expect("the heavy child is nonempty"));
            if needs_double_rotation(Self::size(&left.right) + 1, Self::size(&left.left) + 1) {
                let inner_size = Self::size(&left.right);
                left.right = Self::expose(left.right.take());
                left.update_size_internal();
                let shrank = Self::size(&left.right) != inner_size;
                data.update_size_internal();
                if shrank {
                    return Self::balance(node);
                }
                data.left = data.left.take().map(Self::rotate_left);
            }
            Self::rotate_right(node)
        } else {
            node
        }
    }

    /// Insert a key-value pair into the tree.
    fn insert_simple(
        node: Option<Rc<Node<V>>>,
        key: u32,
        value: V,
    ) -> (Option<Rc<Node<V>>>, Option<V>) {
        let mut node = match Self::expose(node) {
            Some(n) => n,
            None => {
                return (Some(Rc::new(Node::new(key, value))), None);
            }
        };

        let node_mut: &mut Node<V> = Rc::make_mut(&mut node);
        let data_node: &mut DataNode<V> = match node_mut {
            Node::Data(data_node) => data_node,
            Node::Mapping(_) => unreachable!("expose the root before editing it"),
        };

        let old_value: Option<V> = match key.cmp(&data_node.key) {
            Ordering::Equal => {
                let old = mem::replace(&mut data_node.value, value);
                Some(old)
            }
            Ordering::Less => {
                let old_left = data_node.left.take();
                let (new_left, old_value) = Self::insert_simple(old_left, key, value);
                data_node.left = new_left;
                data_node.update_size_internal();
                old_value
            }
            Ordering::Greater => {
                let old_right = data_node.right.take();
                let (new_right, old_value) = Self::insert_simple(old_right, key, value);
                data_node.right = new_right;
                data_node.update_size_internal();
                old_value
            }
        };

        let balanced_node = if old_value.is_none() {
            // Only balance if we actually inserted a new node
            Self::balance(node)
        } else {
            node
        };

        (Some(balanced_node), old_value)
    }

    fn update_entry<F, G, R>(
        node: Option<Rc<Self>>,
        key: u32,
        default: F,
        update: G,
    ) -> (Rc<Self>, bool, R)
    where
        F: FnOnce() -> V,
        G: FnOnce(&mut V) -> R,
    {
        let mut node = match Self::expose(node) {
            Some(node) => node,
            None => {
                let mut value = default();
                let result = update(&mut value);
                return (Rc::new(Self::new(key, value)), true, result);
            }
        };
        let data = match Rc::make_mut(&mut node) {
            Node::Data(data) => data,
            Node::Mapping(_) => unreachable!("expose the root before editing it"),
        };
        let (inserted, result) = match key.cmp(&data.key) {
            Ordering::Equal => (false, update(&mut data.value)),
            Ordering::Less => {
                let (child, inserted, result) =
                    Self::update_entry(data.left.take(), key, default, update);
                data.left = Some(child);
                (inserted, result)
            }
            Ordering::Greater => {
                let (child, inserted, result) =
                    Self::update_entry(data.right.take(), key, default, update);
                data.right = Some(child);
                (inserted, result)
            }
        };
        if inserted {
            data.update_size_internal();
            node = Self::balance(node);
        }
        (node, inserted, result)
    }

    fn remove_min(node: Rc<Self>) -> Option<(u32, V, Option<Rc<Self>>)> {
        let mut node = Self::expose(Some(node))?;
        let data = Self::data_mut(&mut node);
        let removed = data.left.take().and_then(Self::remove_min);
        match removed {
            None => {
                let data = Self::unwrap_to_data(node);
                Some((data.key, data.value, data.right))
            }
            Some((key, value, left)) => {
                data.left = left;
                data.update_size_internal();
                Some((key, value, Some(Self::balance(node))))
            }
        }
    }

    fn concat(left: Option<Rc<Self>>, right: Option<Rc<Self>>) -> Option<Rc<Self>> {
        match (left, right) {
            (None, tree) | (tree, None) => tree,
            (Some(left), Some(right)) => match Self::remove_min(right) {
                Some((key, value, right)) => Self::join(Some(left), key, value, right),
                None => Some(left),
            },
        }
    }

    fn remove_existing_node(node: Rc<Self>, key: &u32) -> (Option<Rc<Self>>, V) {
        let mut node = Self::expose(Some(node)).expect("the key is present");
        let data = Self::data_mut(&mut node);
        let value = match key.cmp(&data.key) {
            Ordering::Equal => {
                let data = Self::unwrap_to_data(node);
                return (Self::concat(data.left, data.right), data.value);
            }
            Ordering::Less => {
                let (left, value) =
                    Self::remove_existing_node(data.left.take().expect("the key is present"), key);
                data.left = left;
                value
            }
            Ordering::Greater => {
                let (right, value) =
                    Self::remove_existing_node(data.right.take().expect("the key is present"), key);
                data.right = right;
                value
            }
        };
        data.update_size_internal();
        (Some(Self::balance(node)), value)
    }

    fn split(
        node: Option<Rc<Node<V>>>,
        key: &u32,
    ) -> (Option<Rc<Node<V>>>, Option<V>, Option<Rc<Node<V>>>) {
        match Self::expose(node) {
            None => (None, None, None),
            Some(n) => {
                let DataNode {
                    key: node_key,
                    value: node_value,
                    left,
                    right,
                    size: _,
                } = Self::unwrap_to_data(n);
                match key.cmp(&node_key) {
                    Ordering::Equal => (left, Some(node_value), right),
                    Ordering::Less => {
                        let (new_left, found_value, new_right) = Self::split(left, key);
                        let joined_right = Self::join(new_right, node_key, node_value, right);
                        (new_left, found_value, joined_right)
                    }
                    Ordering::Greater => {
                        let (new_left, found_value, new_right) = Self::split(right, key);
                        let joined_left = Self::join(left, node_key, node_value, new_left);
                        (joined_left, found_value, new_right)
                    }
                }
            }
        }
    }

    fn join(
        left: Option<Rc<Node<V>>>,
        key: u32,
        value: V,
        right: Option<Rc<Node<V>>>,
    ) -> Option<Rc<Node<V>>> {
        let left_size = Self::size(&left);
        let right_size = Self::size(&right);

        if too_heavy(right_size, left_size) {
            match Self::expose(right) {
                None => Self::join(left, key, value, None),
                Some(r) => {
                    let DataNode {
                        key: r_key,
                        value: r_value,
                        left: r_left,
                        right: r_right,
                        size: _,
                    } = Self::unwrap_to_data(r);
                    let new_left = Self::join(left, key, value, r_left);
                    let new_node = Self::new_data_node(r_key, r_value, new_left, r_right);
                    Some(Node::balance(new_node))
                }
            }
        } else if too_heavy(left_size, right_size) {
            match Self::expose(left) {
                None => Self::join(None, key, value, right),
                Some(l) => {
                    let DataNode {
                        key: l_key,
                        value: l_value,
                        left: l_left,
                        right: l_right,
                        size: _,
                    } = Self::unwrap_to_data(l);
                    let new_right = Self::join(l_right, key, value, right);
                    let new_node = Self::new_data_node(l_key, l_value, l_left, new_right);
                    Some(Node::balance(new_node))
                }
            }
        } else {
            let new_node = Self::new_data_node(key, value, left, right);
            Some(Node::balance(new_node))
        }
    }

    fn union<F>(
        left: Option<Rc<Node<V>>>,
        right: Option<Rc<Node<V>>>,
        merge: &mut F,
        reuse_shared: bool,
    ) -> Option<Rc<Node<V>>>
    where
        F: FnMut(&u32, V, V) -> V,
    {
        match (left, right) {
            (None, None) => None,
            (Some(t), None) | (None, Some(t)) => Some(t),
            (Some(l), Some(r)) => {
                if reuse_shared && Rc::ptr_eq(&l, &r) {
                    return Some(l);
                }
                let Some(l) = Self::expose(Some(l)) else {
                    return Some(r);
                };
                let Some(r) = Self::expose(Some(r)) else {
                    return Some(l);
                };
                let l_size = Self::size(&Some(l.clone()));
                let r_size = Self::size(&Some(r.clone()));
                if l_size >= r_size {
                    // Use left tree as base, split right tree on left root's key
                    let DataNode {
                        key: l_key,
                        value: l_value,
                        left: l_left,
                        right: l_right,
                        size: _,
                    } = Self::unwrap_to_data(l);
                    let (r_left, r_value_opt, r_right) = Self::split(Some(r), &l_key);

                    let new_value = match r_value_opt {
                        Some(r_value) => merge(&l_key, l_value, r_value),
                        None => l_value,
                    };

                    let new_left = Self::union(l_left, r_left, merge, reuse_shared);
                    let new_right = Self::union(l_right, r_right, merge, reuse_shared);
                    Self::join(new_left, l_key, new_value, new_right)
                } else {
                    // Use right tree as base, split left tree on right root's key
                    let DataNode {
                        key: r_key,
                        value: r_value,
                        left: r_left,
                        right: r_right,
                        size: _,
                    } = Self::unwrap_to_data(r);
                    let (l_left, l_value_opt, l_right) = Self::split(Some(l), &r_key);

                    let new_value = match l_value_opt {
                        Some(l_value) => merge(&r_key, l_value, r_value),
                        None => r_value,
                    };

                    let new_left = Self::union(l_left, r_left, merge, reuse_shared);
                    let new_right = Self::union(l_right, r_right, merge, reuse_shared);
                    Self::join(new_left, r_key, new_value, new_right)
                }
            }
        }
    }

    fn join_without_key(left: Rc<Node<V>>, right: Rc<Node<V>>) -> Option<Rc<Node<V>>> {
        Self::concat(Some(left), Some(right))
    }

    // Borrow bounded portions of the right tree instead of allocating split
    // trees, which also keeps shared roots available for cancellation.
    fn difference<F, E>(
        left: Option<Rc<Node<V>>>,
        mut right: Option<&Rc<Node<V>>>,
        lower: Option<u32>,
        upper: Option<u32>,
        diff: &mut F,
        cancel_shared: bool,
        same_value: &E,
    ) -> Option<Rc<Node<V>>>
    where
        F: FnMut(&u32, V, V) -> Option<V>,
        E: Fn(&V, &V) -> bool,
    {
        let left = left?;
        while let Some(node) = right {
            let Some(data) = Self::data(node) else {
                right = None;
                break;
            };
            if lower.is_some_and(|lower| data.key <= lower) {
                right = data.right.as_ref();
            } else if upper.is_some_and(|upper| data.key >= upper) {
                right = data.left.as_ref();
            } else {
                break;
            }
        }
        let Some(right) = right else {
            return Some(left);
        };
        if cancel_shared && Rc::ptr_eq(&left, right) {
            return None;
        }
        let data = Self::data(&left)?;
        let mut candidate = Some(right);
        let mut value = None;
        while let Some(node) = candidate {
            let Some(other) = Self::data(node) else {
                break;
            };
            match data.key.cmp(&other.key) {
                Ordering::Less => candidate = other.left.as_ref(),
                Ordering::Greater => candidate = other.right.as_ref(),
                Ordering::Equal => {
                    value = Some(&other.value);
                    break;
                }
            }
        }
        let new_left = Self::difference(
            data.left.clone(),
            Some(right),
            lower,
            Some(data.key),
            diff,
            cancel_shared,
            same_value,
        );
        let new_right = Self::difference(
            data.right.clone(),
            Some(right),
            Some(data.key),
            upper,
            diff,
            cancel_shared,
            same_value,
        );
        let matched = value.is_some();
        let value = match value {
            Some(value) => diff(&data.key, data.value.clone(), value.clone()),
            None => Some(data.value.clone()),
        };
        match value {
            Some(value) => {
                let same_left = match (&new_left, &data.left) {
                    (Some(new), Some(old)) => Rc::ptr_eq(new, old),
                    (None, None) => true,
                    (Some(_), None) | (None, Some(_)) => false,
                };
                let same_right = match (&new_right, &data.right) {
                    (Some(new), Some(old)) => Rc::ptr_eq(new, old),
                    (None, None) => true,
                    (Some(_), None) | (None, Some(_)) => false,
                };
                if same_left && same_right && (!matched || same_value(&data.value, &value)) {
                    Some(left)
                } else {
                    Self::join(new_left, data.key, value, new_right)
                }
            }
            None => match (new_left, new_right) {
                (None, tree) | (tree, None) => tree,
                (Some(left), Some(right)) => Self::join_without_key(left, right),
            },
        }
    }

    fn intersection<F, E>(
        left: Option<&Rc<Node<V>>>,
        mut right: Option<&Rc<Node<V>>>,
        lower: Option<u32>,
        upper: Option<u32>,
        intersect: &mut F,
        same_value: &E,
    ) -> Option<Rc<Node<V>>>
    where
        F: FnMut(&u32, &V, &V) -> Option<V>,
        E: Fn(&V, &V) -> bool,
    {
        let left = left?;
        while let Some(node) = right {
            let Some(data) = Self::data(node) else {
                right = None;
                break;
            };
            if lower.is_some_and(|lower| data.key <= lower) {
                right = data.right.as_ref();
            } else if upper.is_some_and(|upper| data.key >= upper) {
                right = data.left.as_ref();
            } else {
                break;
            }
        }
        let right = right?;
        if Rc::ptr_eq(left, right) {
            return Some(left.clone());
        }
        let data = Self::data(left)?;
        let mut candidate = Some(right);
        let mut value = None;
        while let Some(node) = candidate {
            let Some(other) = Self::data(node) else {
                break;
            };
            match data.key.cmp(&other.key) {
                Ordering::Less => candidate = other.left.as_ref(),
                Ordering::Greater => candidate = other.right.as_ref(),
                Ordering::Equal => {
                    value = intersect(&data.key, &data.value, &other.value);
                    break;
                }
            }
        }
        let new_left = Self::intersection(
            data.left.as_ref(),
            Some(right),
            lower,
            Some(data.key),
            intersect,
            same_value,
        );
        let new_right = Self::intersection(
            data.right.as_ref(),
            Some(right),
            Some(data.key),
            upper,
            intersect,
            same_value,
        );
        match value {
            Some(value) => {
                let same_left = match (&new_left, &data.left) {
                    (Some(new), Some(old)) => Rc::ptr_eq(new, old),
                    (None, None) => true,
                    (Some(_), None) | (None, Some(_)) => false,
                };
                let same_right = match (&new_right, &data.right) {
                    (Some(new), Some(old)) => Rc::ptr_eq(new, old),
                    (None, None) => true,
                    (Some(_), None) | (None, Some(_)) => false,
                };
                if same_left && same_right && same_value(&data.value, &value) {
                    Some(left.clone())
                } else {
                    Self::join(new_left, data.key, value, new_right)
                }
            }
            None => match (new_left, new_right) {
                (None, tree) | (tree, None) => tree,
                (Some(left), Some(right)) => Self::join_without_key(left, right),
            },
        }
    }
}

impl<V: Clone> WBTreeMap<V> {
    pub(crate) fn fits_materialized_budget(
        &self,
        budget: &mut usize,
        mut values: impl FnMut(&V, &mut usize) -> bool,
    ) -> bool {
        if self.has_mapping() {
            return false;
        }
        let Some(remaining) = budget.checked_sub(self.len.upper_bound()) else {
            return false;
        };
        *budget = remaining;
        Node::all_data_values(&self.root, &mut |value| values(value, budget))
    }

    pub(crate) fn mapped_small_entries(
        &self,
        keys: Option<&MonotoneMap>,
        limit: usize,
        values: impl Fn(&V) -> Option<V>,
    ) -> Option<Self> {
        if self.has_mapping() || self.len.upper_bound() > limit {
            return None;
        }
        let root = Node::map_data_entries(&self.root, keys, &values);
        let len = SizeBound::exact(Node::size(&root));
        Some(Self { root, len })
    }

    pub(crate) fn from_sorted_entries(entries: Vec<(u32, V)>) -> Self {
        debug_assert!(entries.windows(2).all(|pair| pair[0].0 < pair[1].0));
        let len = entries.len();
        let root = Node::from_sorted_iter(len, &mut entries.into_iter());
        Self {
            root,
            len: SizeBound::exact(len),
        }
    }

    /// Visits unequal structure without constructing split or result trees.
    /// Equal keys are paired so callers can compare nested values themselves.
    pub fn difference_entries<'a>(&'a self, other: &'a Self) -> Difference<'a, V> {
        Difference::new(self, other)
    }

    /// Shared subtrees need no comparison; stops at the first false callback.
    pub fn all_difference_entries<'a>(
        &'a self,
        other: &'a Self,
        mut visit: impl FnMut(u32, &'a V, Option<&'a V>) -> bool,
    ) -> bool {
        if self.has_mapping() || other.has_mapping() {
            if self.shares_root(other) {
                return true;
            }
            // Sparse transports should search for their few keys instead of
            // advancing a mapped cursor through an unrelated dense prefix.
            if self.len_upper_bound() <= other.len_upper_bound() / 8 {
                return self
                    .iter()
                    .all(|(key, left)| visit(key, left, other.get(&key)));
            }
            return self
                .difference_entries(other)
                .all(|(key, left, right)| visit(key, left, right));
        }
        difference::all(
            self.root.as_ref(),
            other.root.as_ref(),
            None,
            None,
            &mut visit,
        )
    }

    pub(crate) fn shares_root(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(left), Some(right)) => Rc::ptr_eq(left, right),
            (None, Some(_)) | (Some(_), None) => false,
        }
    }

    /// The identity remains valid while a snapshot of this root is alive.
    pub(crate) fn root_identity(&self) -> usize {
        self.root
            .as_ref()
            .map_or(0, |root| Rc::as_ptr(root) as usize)
    }

    pub const fn new() -> Self {
        WBTreeMap {
            root: None,
            len: SizeBound::exact(0),
        }
    }

    fn has_mapping(&self) -> bool {
        !self.len.is_exact()
    }

    fn materialize(&mut self) {
        if !self.has_mapping() {
            return;
        }
        // Mutable iteration exposes every value, so keeping lazy nodes would not
        // save work and would complicate the iterator's unique-reference guarantee.
        // The visible keys are already sorted, so rebuilding needs no searches.
        let entries = self
            .iter()
            .map(|(key, value)| (key, value.clone()))
            .collect();
        *self = Self::from_sorted_entries(entries);
    }

    pub fn insert(&mut self, key: u32, value: V) -> Option<V> {
        let (new_root, old_value) = Node::insert_simple(self.root.take(), key, value);
        self.root = new_root;
        self.len.inserted(old_value.is_none());
        old_value
    }

    pub(crate) fn update_entry<F, G, R>(&mut self, key: u32, default: F, update: G) -> R
    where
        F: FnOnce() -> V,
        G: FnOnce(&mut V) -> R,
    {
        let (root, inserted, result) = Node::update_entry(self.root.take(), key, default, update);
        self.root = Some(root);
        self.len.inserted(inserted);
        result
    }

    pub fn get(&self, key: &u32) -> Option<&V> {
        let mut key = *key;
        let mut current = self.root.as_deref();
        let mut first_value: Option<(&ValueMapping<V>, u32)> = None;
        let mut inner_values: Vec<(&ValueMapping<V>, u32)> = Vec::new();
        while let Some(node) = current {
            match node {
                Node::Data(data) => match key.cmp(&data.key) {
                    Ordering::Less => current = data.left.as_deref(),
                    Ordering::Greater => current = data.right.as_deref(),
                    Ordering::Equal => {
                        let Some((outer, source_key)) = first_value else {
                            return Some(&data.value);
                        };
                        let mut value = &data.value;
                        for (mapping, key) in inner_values.into_iter().rev() {
                            value = mapping.map_value(key, value)?;
                        }
                        return outer.map_value(source_key, value);
                    }
                },
                Node::Mapping(mapping) => {
                    if let Some(keys) = &mapping.transform.keys {
                        key = keys.preimage(key)?;
                    }
                    if let Some(values) = &mapping.transform.values {
                        // The query already identifies this transform's source key.
                        // A single value transform needs no allocated stack.
                        if first_value.is_none() {
                            first_value = Some((values, key));
                        } else {
                            inner_values.push((values, key));
                        }
                    }
                    current = mapping.child.as_deref();
                }
            }
        }
        None
    }

    pub(crate) fn floor_entry(&self, key: u32) -> Option<(u32, &V)> {
        let mut current = self.root.as_deref();
        let mut result = None;
        while let Some(node) = current {
            match node {
                Node::Data(data) => match key.cmp(&data.key) {
                    Ordering::Less => current = data.left.as_deref(),
                    Ordering::Equal => return Some((data.key, &data.value)),
                    Ordering::Greater => {
                        result = Some((data.key, &data.value));
                        current = data.right.as_deref();
                    }
                },
                Node::Mapping(_) => return self.iter().take_while(|(next, _)| *next <= key).last(),
            }
        }
        result
    }

    pub(crate) fn ceiling_entry(&self, key: u32) -> Option<(u32, &V)> {
        let mut current = self.root.as_deref();
        let mut result = None;
        while let Some(node) = current {
            match node {
                Node::Data(data) => match key.cmp(&data.key) {
                    Ordering::Less => {
                        result = Some((data.key, &data.value));
                        current = data.left.as_deref();
                    }
                    Ordering::Equal => return Some((data.key, &data.value)),
                    Ordering::Greater => current = data.right.as_deref(),
                },
                Node::Mapping(_) => return self.iter().find(|(next, _)| *next >= key),
            }
        }
        result
    }

    pub fn get_mut(&mut self, key: &u32) -> Option<&mut V> {
        let mut current = &mut self.root;
        loop {
            *current = Node::expose(current.take());
            let Some(node) = current else {
                return None;
            };
            match Rc::make_mut(node) {
                Node::Data(data_node) => match key.cmp(&data_node.key) {
                    Ordering::Less => current = &mut data_node.left,
                    Ordering::Greater => current = &mut data_node.right,
                    Ordering::Equal => return Some(&mut data_node.value),
                },
                Node::Mapping(_) => {
                    unreachable!("expose the root before editing it")
                }
            }
        }
    }

    pub fn contains_key(&self, key: &u32) -> bool {
        self.get(key).is_some()
    }

    pub fn is_empty(&self) -> bool {
        if self.has_mapping() {
            match self.root.as_deref() {
                None => true,
                // A materialized pivot survives regardless of its mapped children.
                Some(Node::Data(_)) => false,
                Some(Node::Mapping(_)) => self.iter().next().is_none(),
            }
        } else {
            self.len.upper_bound() == 0
        }
    }

    pub fn len(&self) -> usize {
        if self.has_mapping() {
            self.iter().count()
        } else {
            self.len.upper_bound()
        }
    }

    pub(crate) fn len_up_to(&self, limit: usize) -> usize {
        if self.has_mapping() {
            self.iter().take(limit).count()
        } else {
            self.len().min(limit)
        }
    }

    #[doc(hidden)]
    pub fn len_upper_bound(&self) -> usize {
        self.len.upper_bound()
    }

    pub fn clear(&mut self) {
        self.root = None;
        self.len = SizeBound::exact(0);
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, V> {
        Iter {
            stack: Vec::new(),
            current: Some(&self.root),
            current_mappings: self.has_mapping().then(Vec::new),
        }
    }

    pub(crate) fn iteration_work(
        &self,
        fuel: &mut Fuel,
        value_work: fn(&V, &mut Fuel) -> Result<u64, Error>,
    ) -> Result<u64, Error> {
        let mut work = 1u64;
        let mut pending = vec![(&self.root, 0u64, 0u64, 1u64, 0u64)];
        while let Some((node, mapping_work, cache_work, value_factor, depth)) = pending.pop() {
            fuel.consume(1)?;
            if let Some(node) = node {
                match node.as_ref() {
                    Node::Data(data) => {
                        work = work.saturating_add(
                            (1u64
                                .saturating_add(mapping_work)
                                .saturating_add(if value_factor > 1 { depth } else { 0 })
                                .saturating_add(value_work(&data.value, fuel)?))
                            .saturating_mul(value_factor.saturating_mul(value_factor))
                            .saturating_add(cache_work),
                        );
                        pending.push((
                            &data.left,
                            mapping_work,
                            cache_work,
                            value_factor,
                            depth + 1,
                        ));
                        pending.push((
                            &data.right,
                            mapping_work,
                            cache_work,
                            value_factor,
                            depth + 1,
                        ));
                    }
                    Node::Mapping(mapping) => {
                        let lookup_work = mapping
                            .transform
                            .keys
                            .as_ref()
                            .map_or(0, |keys| keys.run_count() as u64);
                        let value_lookup_work = match &mapping.transform.values {
                            Some(values) => values.lookup_work(fuel)?,
                            None => 0,
                        };
                        let mapping_work =
                            mapping_work.saturating_add(lookup_work).saturating_add(1);
                        // Cache searches follow raw keys without forcing suffix
                        // transforms, so their bound is independent of suffix work.
                        let cache_work = cache_work.saturating_add(value_lookup_work);
                        // Prepay against the raw source; forcing a value here could
                        // scan a filtered suffix before its work has been charged.
                        // Successive transforms revisit inner wrappers; a squared
                        // additive bound avoids exponential charges for short chains.
                        let value_factor = value_factor.saturating_add(
                            mapping
                                .transform
                                .values
                                .as_ref()
                                .map_or(0, |values| values.work_factor),
                        );
                        work = work.saturating_add(1);
                        pending.push((
                            &mapping.child,
                            mapping_work,
                            cache_work,
                            value_factor,
                            depth,
                        ));
                    }
                }
            }
        }
        Ok(work)
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, V> {
        self.materialize();
        let current = &mut self.root as *mut Option<Rc<Node<V>>>;
        IterMut {
            stack: Vec::new(),
            current: Some(current),
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn entry<'a>(&'a mut self, key: u32) -> Entry<'a, V> {
        if self.contains_key(&key) {
            Entry::Occupied(OccupiedEntry { key, map: self })
        } else {
            Entry::Vacant(VacantEntry { key, map: self })
        }
    }

    pub fn remove(&mut self, key: &u32) -> Option<V> {
        if !self.contains_key(key) {
            return None;
        }

        let root = self.root.take().expect("Root must exist if key is present");
        let (new_root, value) = Node::remove_existing_node(root, key);
        self.root = new_root;
        self.len.removed();
        Some(value)
    }

    pub fn union<F>(&self, other: &Self, merge: F) -> Self
    where
        F: FnMut(&u32, V, V) -> V,
    {
        self.union_impl(other, merge, false)
    }

    // Set union is idempotent; arbitrary map callbacks may change shared values.
    pub(crate) fn union_shared<F>(&self, other: &Self, merge: F) -> Self
    where
        F: FnMut(&u32, V, V) -> V,
    {
        self.union_impl(other, merge, true)
    }

    // Shared roots bypass merge, so it must be idempotent. Owning the
    // destination lets recursive merges reuse its otherwise unshared children.
    pub(crate) fn union_assign_shared<F>(&mut self, other: &Self, mut merge: F)
    where
        F: FnMut(&u32, V, V) -> V,
    {
        if other.root.is_none() || self.shares_root(other) {
            return;
        }
        if self.root.is_none() {
            *self = other.clone();
            return;
        }
        let root = Node::union(self.root.take(), other.root.clone(), &mut merge, true);
        self.len = SizeBound::combined(Node::size(&root), self.len, other.len);
        self.root = root;
    }

    fn union_impl<F>(&self, other: &Self, mut merge: F, reuse_shared: bool) -> Self
    where
        F: FnMut(&u32, V, V) -> V,
    {
        if other.root.is_none() || (reuse_shared && self.shares_root(other)) {
            return self.clone();
        }
        if self.root.is_none() {
            return other.clone();
        }
        let left = self.clone();
        let right = other.clone();
        let new_root = Node::union(left.root, right.root, &mut merge, reuse_shared);
        let new_len = SizeBound::combined(Node::size(&new_root), self.len, other.len);
        WBTreeMap {
            root: new_root,
            len: new_len,
        }
    }

    // Shared roots bypass intersect, so it must be idempotent. same_value must
    // imply equality; retaining unchanged roots preserves version checkpoints.
    pub(crate) fn intersection_shared<F, E>(
        &self,
        other: &Self,
        mut intersect: F,
        same_value: E,
    ) -> Self
    where
        F: FnMut(&u32, &V, &V) -> Option<V>,
        E: Fn(&V, &V) -> bool,
    {
        if self.shares_root(other) {
            return self.clone();
        }
        if self.root.is_none() || other.root.is_none() {
            return Self::new();
        }
        let left = self.clone();
        let right = other.clone();
        let root = Node::intersection(
            left.root.as_ref(),
            right.root.as_ref(),
            None,
            None,
            &mut intersect,
            &same_value,
        );
        let len = SizeBound::combined(Node::size(&root), self.len, other.len);
        Self { root, len }
    }

    pub fn difference<F>(&self, other: &Self, diff: F) -> Self
    where
        F: FnMut(&u32, V, V) -> Option<V>,
    {
        self.difference_impl(other, diff, false, |_, _| false)
    }

    // Shared roots bypass diff, so equal values must cancel without effects.
    // same_value must imply equality; retaining unchanged roots preserves sharing.
    pub(crate) fn difference_shared<F, E>(&self, other: &Self, diff: F, same_value: E) -> Self
    where
        F: FnMut(&u32, V, V) -> Option<V>,
        E: Fn(&V, &V) -> bool,
    {
        self.difference_impl(other, diff, true, same_value)
    }

    fn difference_impl<F, E>(
        &self,
        other: &Self,
        mut diff: F,
        cancel_shared: bool,
        same_value: E,
    ) -> Self
    where
        F: FnMut(&u32, V, V) -> Option<V>,
        E: Fn(&V, &V) -> bool,
    {
        if self.root.is_none() {
            return Self::new();
        }
        if other.root.is_none() {
            return self.clone();
        }
        if cancel_shared && self.shares_root(other) {
            return Self::new();
        }
        let left = self.clone();
        let right = other.clone();
        let new_root = Node::difference(
            left.root,
            right.root.as_ref(),
            None,
            None,
            &mut diff,
            cancel_shared,
            &same_value,
        );
        let new_len = SizeBound::combined(Node::size(&new_root), self.len, other.len);
        WBTreeMap {
            root: new_root,
            len: new_len,
        }
    }

    /// Keys outside the domain are filtered out. Non-increasing maps are rejected.
    /// Preparing the offset runs takes time linear in the mapping's row count.
    pub fn mapped(&self, mapping: PrefixTree2) -> Self {
        let mapping = MonotoneMap::new(&mapping).expect("mapping must be strictly increasing");
        self.mapped_keys(mapping)
    }

    /// Wraps the shared root in O(1). Edits expose only the affected paths.
    pub fn mapped_keys(&self, mapping: MonotoneMap) -> Self {
        if mapping.run_count() == 0 {
            return Self::new();
        }
        let new_root = self.root.clone().map(|root| {
            Rc::new(Node::Mapping(MappingNode {
                transform: Rc::new(MappingTransform {
                    keys: Some(mapping),
                    values: None,
                }),
                child: Some(root),
                exposed: OnceCell::new(),
            }))
        });
        // Note: len might be different if mapping filters some keys out,
        // but we can't know without iterating. We keep the original len
        // as an upper bound.
        WBTreeMap {
            root: new_root,
            len: self.len.inexact(),
        }
    }

    /// Values are cached on demand; returning `None` removes the key.
    /// The transform must be deterministic and take constant work. Its result
    /// must not cost more to iterate than its input, so finite-fuel traversal
    /// can be prepaid without forcing the transform.
    pub fn mapped_entries(
        &self,
        mapping: Option<MonotoneMap>,
        values: impl Fn(&V) -> Option<V> + 'static,
    ) -> Self {
        self.mapped_entries_with_work(mapping, 1, values)
    }

    pub(crate) fn mapped_entries_with_work(
        &self,
        mapping: Option<MonotoneMap>,
        work_factor: u64,
        values: impl Fn(&V) -> Option<V> + 'static,
    ) -> Self {
        if mapping
            .as_ref()
            .is_some_and(|mapping| mapping.run_count() == 0)
        {
            return Self::new();
        }
        let root = self.root.clone().map(|child| {
            let (source, source_offset) = ValueMapping::source_for_cache(&child);
            Rc::new(Node::Mapping(MappingNode {
                transform: Rc::new(MappingTransform {
                    keys: mapping,
                    values: Some(ValueMapping {
                        apply: Box::new(values),
                        cache: ValueCache::new(),
                        source,
                        source_offset,
                        lookup_work: OnceCell::new(),
                        work_factor,
                    }),
                }),
                child: Some(child),
                exposed: OnceCell::new(),
            }))
        });
        Self {
            root,
            len: self.len.inexact(),
        }
    }
}

#[derive(Clone, Copy)]
struct KeyBounds {
    first: u32,
    last: u32,
}

impl KeyBounds {
    const ALL: Self = Self {
        first: 0,
        last: u32::MAX,
    };
    const EMPTY: Self = Self { first: 1, last: 0 };

    fn endpoints(self) -> Option<(u32, u32)> {
        (self.first <= self.last).then_some((self.first, self.last))
    }

    fn from_endpoints(endpoints: Option<(u32, u32)>) -> Self {
        endpoints.map_or(Self::EMPTY, |(first, last)| Self { first, last })
    }
}

struct MappingFrame<'a, V: Clone> {
    mapping: &'a MappingNode<V>,
    // Each bound belongs to this mapping's immediate input coordinates.
    bounds: KeyBounds,
}

pub struct Iter<'a, V: Clone> {
    stack: Vec<(&'a DataNode<V>, usize)>,
    current: Option<&'a Option<Rc<Node<V>>>>,
    // Exact trees need no mapping state or bounds checks.
    current_mappings: Option<Vec<MappingFrame<'a, V>>>,
}

impl<'a, V: Clone> Iter<'a, V> {
    fn next_plain(&mut self) -> Option<(u32, &'a V)> {
        while let Some(opt_node) = self.current {
            match opt_node {
                None => self.current = None,
                Some(node) => match node.as_ref() {
                    Node::Data(data) => {
                        if data.left.is_none() {
                            self.current = Some(&data.right);
                            return Some((data.key, &data.value));
                        }
                        self.stack.push((data, 0));
                        self.current = Some(&data.left);
                    }
                    Node::Mapping(_) => unreachable!("exact sizes have no mapped descendants"),
                },
            }
        }
        let (data, _) = self.stack.pop()?;
        self.current = Some(&data.right);
        Some((data.key, &data.value))
    }

    fn mappings(&self) -> &[MappingFrame<'a, V>] {
        self.current_mappings.as_deref().unwrap()
    }

    fn mappings_mut(&mut self) -> &mut Vec<MappingFrame<'a, V>> {
        self.current_mappings.as_mut().unwrap()
    }

    fn bounds(&self) -> Option<(u32, u32)> {
        self.mappings()
            .last()
            .map_or(KeyBounds::ALL, |frame| frame.bounds)
            .endpoints()
    }

    // Dense scans only need bounds after a mapping or a domain hole. A scan
    // can enter seeking once; seeking never calls back into the scan path.
    fn next_node<const SEEK: bool>(&mut self) -> Option<&'a DataNode<V>> {
        loop {
            while let Some(opt_node) = self.current {
                let bounds = if SEEK {
                    self.bounds()
                } else {
                    Some((0, u32::MAX))
                };
                let Some((first, last)) = bounds else {
                    self.current = None;
                    break;
                };
                match opt_node {
                    None => self.current = None,
                    Some(node) => match node.as_ref() {
                        Node::Data(data) => {
                            if SEEK && data.key < first {
                                self.current = Some(&data.right);
                            } else if SEEK && data.key > last {
                                self.current = Some(&data.left);
                            } else if data.left.is_none() {
                                self.current = Some(&data.right);
                                return Some(data);
                            } else {
                                self.stack.push((data, self.mappings().len()));
                                self.current = Some(&data.left);
                            }
                        }
                        Node::Mapping(mapping) => {
                            let Some((first, last)) = self.bounds() else {
                                self.current = None;
                                continue;
                            };
                            let bounds = match &mapping.transform.keys {
                                None => Some((first, last)),
                                Some(keys) => keys.preimage_bounds(first, last),
                            };
                            self.mappings_mut().push(MappingFrame {
                                mapping,
                                bounds: KeyBounds::from_endpoints(bounds),
                            });
                            self.current = Some(&mapping.child);
                            if !SEEK && mapping.transform.keys.is_some() {
                                return self.next_node::<true>();
                            }
                        }
                    },
                }
            }
            let (data, mapping_depth) = self.stack.pop()?;
            let same_scope = self.mappings().len() == mapping_depth;
            self.mappings_mut().truncate(mapping_depth);
            self.current = Some(&data.right);
            if !SEEK && same_scope {
                return Some(data);
            }
            if let Some((first, last)) = self.bounds() {
                if data.key <= last {
                    if data.key >= first {
                        return Some(data);
                    }
                    if !SEEK {
                        return self.next_node::<true>();
                    }
                    continue;
                }
            }
            self.current = None;
            if !SEEK {
                return self.next_node::<true>();
            }
        }
    }

    fn mapped_key(&mut self, mut key: u32) -> Option<u32> {
        for index in (0..self.mappings().len()).rev() {
            let Some(keys) = &self.mappings()[index].mapping.transform.keys else {
                continue;
            };
            if let Some(mapped) = keys.apply(key) {
                key = mapped;
                continue;
            }
            // The next domain key is expressed in this layer's input coordinates.
            // Pull it through the inner maps before seeking in the source tree.
            let mut next = keys.source_at_or_after(key);
            for inner in &self.mappings()[index + 1..] {
                if let Some(keys) = &inner.mapping.transform.keys {
                    next = next.and_then(|key| keys.preimage_at_or_after(key));
                }
            }
            let frame = self.mappings_mut().last_mut().unwrap();
            frame.bounds = KeyBounds::from_endpoints(frame.bounds.endpoints().zip(next).and_then(
                |((first, last), next)| (next <= last).then_some((first.max(next), last)),
            ));
            return None;
        }
        Some(key)
    }

    // Keep domain seeking out of the ordinary iterator's inlining budget.
    #[inline(never)]
    fn next_mapped(&mut self) -> Option<(u32, &'a V)> {
        let mut seek = false;
        loop {
            let data = if seek {
                self.next_node::<true>()?
            } else {
                self.next_node::<false>()?
            };
            seek = false;
            if self.mappings().is_empty() {
                return Some((data.key, &data.value));
            }
            if let Some(key) = self.mapped_key(data.key) {
                if let Some(value) = apply_value_mappings(
                    self.mappings().iter().map(|frame| frame.mapping),
                    data.key,
                    &data.value,
                ) {
                    return Some((key, value));
                }
            } else {
                seek = true;
            }
        }
    }
}

impl<'a, V: Clone> Iterator for Iter<'a, V> {
    type Item = (u32, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.current_mappings.is_none() {
            self.next_plain()
        } else {
            self.next_mapped()
        }
    }
}

// Mutable access resolves mappings before exposing references to stored values.
pub struct IterMut<'a, V: Clone> {
    stack: Vec<*mut DataNode<V>>,
    current: Option<*mut Option<Rc<Node<V>>>>,
    _phantom: std::marker::PhantomData<&'a mut WBTreeMap<V>>,
}

impl<'a, V: Clone> IterMut<'a, V> {
    fn descend_left(&mut self) {
        while let Some(current_ptr) = self.current {
            unsafe {
                let opt_node = &mut *current_ptr;
                match opt_node {
                    None => {
                        self.current = None;
                        return;
                    }
                    Some(node) => match Rc::make_mut(node) {
                        Node::Data(data) => {
                            self.stack.push(data as *mut DataNode<V>);
                            self.current = Some(&mut data.left as *mut _);
                        }
                        Node::Mapping(_) => unreachable!("mutable iteration materializes mappings"),
                    },
                }
            }
        }
    }
}

impl<'a, V: Clone> Iterator for IterMut<'a, V> {
    type Item = (u32, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.descend_left();
        let data = self.stack.pop()?;
        unsafe {
            let data = &mut *data;
            self.current = Some(&mut data.right as *mut _);
            Some((data.key, &mut data.value))
        }
    }
}

// Entry API
pub enum Entry<'a, V: Clone> {
    Occupied(OccupiedEntry<'a, V>),
    Vacant(VacantEntry<'a, V>),
}

pub struct OccupiedEntry<'a, V: Clone> {
    key: u32,
    map: &'a mut WBTreeMap<V>,
}

pub struct VacantEntry<'a, V: Clone> {
    key: u32,
    map: &'a mut WBTreeMap<V>,
}

impl<'a, V: Clone> Entry<'a, V> {
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }
}

impl<'a, V: Clone> OccupiedEntry<'a, V> {
    pub fn into_mut(self) -> &'a mut V {
        self.map.get_mut(&self.key).unwrap()
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.map.get_mut(&self.key).unwrap()
    }

    pub fn remove(self) -> V {
        self.map.remove(&self.key).unwrap()
    }
}

impl<'a, V: Clone> VacantEntry<'a, V> {
    pub fn insert(self, value: V) -> &'a mut V {
        self.map.insert(self.key.clone(), value);
        self.map.get_mut(&self.key).unwrap()
    }
}

impl<V: fmt::Debug + Clone> fmt::Debug for Node<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Data(data_node) => f
                .debug_struct("DataNode")
                .field("key", &data_node.key)
                .field("value", &data_node.value)
                .field("left", &data_node.left)
                .field("right", &data_node.right)
                .field("size", &data_node.size)
                .finish(),
            Node::Mapping(mapping_node) => f
                .debug_struct("MappingNode")
                .field("mapping", &mapping_node.transform.keys)
                .field("child", &mapping_node.child)
                .finish(),
        }
    }
}

impl<V: fmt::Debug + Clone> fmt::Debug for WBTreeMap<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::collections::BTreeMap;

    use rand::rngs::StdRng;
    use rand::{RngExt, SeedableRng};

    #[test]
    fn boundary_entries_preserve_mapped_coordinates_and_filters() {
        let mut plain = WBTreeMap::new();
        let mut relation = PrefixTree2::new();
        let mut expected = BTreeMap::new();
        for key in 0..64 {
            plain.insert(key, key);
            relation.insert([key, 10 + key * 2]);
            if key % 3 != 0 {
                expected.insert(10 + key * 2, key + 1);
            }
        }
        for key in 0..70 {
            assert_eq!(
                plain.floor_entry(key),
                plain.iter().take_while(|(next, _)| *next <= key).last()
            );
            assert_eq!(
                plain.ceiling_entry(key),
                plain.iter().find(|(next, _)| *next >= key)
            );
        }
        let mut mapped = plain
            .mapped_entries(Some(MonotoneMap::new(&relation).unwrap()), |value| {
                (value % 3 != 0).then_some(value + 1)
            });
        for key in 0..150 {
            assert_eq!(
                mapped.floor_entry(key),
                expected
                    .range(..=key)
                    .next_back()
                    .map(|(&key, value)| (key, value))
            );
            assert_eq!(
                mapped.ceiling_entry(key),
                expected
                    .range(key..)
                    .next()
                    .map(|(&key, value)| (key, value))
            );
        }
        mapped.insert(57, 999);
        expected.insert(57, 999);
        for key in (0..150).chain([u32::MAX]) {
            assert_eq!(
                mapped.floor_entry(key),
                expected
                    .range(..=key)
                    .next_back()
                    .map(|(&key, value)| (key, value))
            );
            assert_eq!(
                mapped.ceiling_entry(key),
                expected
                    .range(key..)
                    .next()
                    .map(|(&key, value)| (key, value))
            );
        }
    }

    #[test]
    fn cold_cache_origin_preprocessing_does_not_force_values() {
        let mut source = WBTreeMap::new();
        source.insert(10, 10);
        source.insert(11, 11);
        let mut relation = PrefixTree2::new();
        relation.insert([10, 100]);
        relation.insert([11, 101]);
        let calls = Rc::new(Cell::new(0));
        let first = calls.clone();
        let second = calls.clone();
        let mut mapped = source
            .mapped_entries(MonotoneMap::new(&relation), move |value| {
                first.set(first.get() + 1);
                Some(value + 1)
            })
            .mapped_entries(None, move |value| {
                second.set(second.get() + 1);
                Some(value * 2)
            });
        let snapshot = mapped.clone();
        assert_eq!(mapped.remove(&100), Some(22));
        calls.set(0);
        let third = calls.clone();
        let mapped = mapped.mapped_entries(None, move |value| {
            third.set(third.get() + 1);
            Some(value + 3)
        });
        assert_eq!(
            mapped.iteration_work(&mut Fuel::Finite(1), |_, _| Ok(0)),
            Err(Error::FuelExhausted)
        );
        assert_eq!(calls.get(), 0);
        let mut fuel = Fuel::Finite(1_000);
        let work = mapped.iteration_work(&mut fuel, |_, _| Ok(0)).unwrap();
        fuel.consume(work).unwrap();
        assert_eq!(calls.get(), 0);
        assert_eq!(
            mapped
                .iter()
                .map(|(key, &value)| (key, value))
                .collect::<Vec<_>>(),
            [(101, 27)]
        );
        assert_eq!(calls.get(), 3);
        assert_eq!(snapshot.get(&100), Some(&22));
    }

    #[test]
    fn balance_ratios_do_not_overflow_large_size_bounds() {
        let bounds = [
            0,
            1,
            2,
            usize::MAX / 3,
            usize::MAX / 2,
            usize::MAX - 1,
            usize::MAX,
        ];
        for left in bounds {
            for right in bounds {
                assert_eq!(
                    too_heavy(left, right),
                    left as u128 > DELTA as u128 * right as u128
                );
                assert_eq!(
                    needs_double_rotation(left, right),
                    left as u128 >= GAMMA as u128 * right as u128
                );
            }
        }
    }

    #[test]
    fn bounded_cardinality_does_not_force_unneeded_values() {
        let mut source = WBTreeMap::new();
        for key in 0..128 {
            source.insert(key, key);
        }
        let applied = Rc::new(Cell::new(0));
        let counter = applied.clone();
        let mapped = source.mapped_entries(None, move |value| {
            counter.set(counter.get() + 1);
            (value % 5 != 0).then_some(*value)
        });
        assert_eq!(mapped.len_up_to(0), 0);
        assert_eq!(applied.get(), 0);
        assert_eq!(mapped.len_up_to(2), 2);
        assert_eq!(applied.get(), 3);
        assert_eq!(mapped.len_up_to(1), 1);
        assert_eq!(applied.get(), 3);
        assert_eq!(mapped.len_up_to(usize::MAX), 102);
    }

    /// Print the tree structure in ASCII art format for debugging
    pub fn print_tree_debug<V>(node: &Option<Rc<Node<V>>>)
    where
        V: std::fmt::Debug + Clone,
    {
        print_tree_debug_helper(node, "", true, true);
    }

    fn print_tree_debug_helper<V>(
        node: &Option<Rc<Node<V>>>,
        prefix: &str,
        is_last: bool,
        is_root: bool,
    ) where
        V: std::fmt::Debug + Clone,
    {
        match node {
            None => {
                if !is_root {
                    println!("{}{}∅", prefix, if is_last { "└── " } else { "├── " });
                }
            }
            Some(n) => match n.as_ref() {
                Node::Data(data_node) => {
                    let node_symbol = if is_root {
                        ""
                    } else if is_last {
                        "└── "
                    } else {
                        "├── "
                    };
                    println!(
                        "{}{}({:?}: {:?}) [size: {}]",
                        prefix, node_symbol, data_node.key, data_node.value, data_node.size
                    );

                    let new_prefix = format!(
                        "{}{}",
                        prefix,
                        if is_root {
                            ""
                        } else if is_last {
                            "    "
                        } else {
                            "│   "
                        }
                    );

                    // Print children - left first, then right
                    let has_left = data_node.left.is_some();
                    let has_right = data_node.right.is_some();

                    if has_left || has_right {
                        if has_left {
                            print_tree_debug_helper(
                                &data_node.left,
                                &new_prefix,
                                !has_right,
                                false,
                            );
                        }
                        if has_right {
                            print_tree_debug_helper(&data_node.right, &new_prefix, true, false);
                        }
                    }
                }
                Node::Mapping(mapping_node) => {
                    let node_symbol = if is_root {
                        ""
                    } else if is_last {
                        "└── "
                    } else {
                        "├── "
                    };
                    println!("{}{}[MAPPING]", prefix, node_symbol);
                    let new_prefix = format!(
                        "{}{}",
                        prefix,
                        if is_root {
                            ""
                        } else if is_last {
                            "    "
                        } else {
                            "│   "
                        }
                    );
                    print_tree_debug_helper(&mapping_node.child, &new_prefix, true, false);
                }
            },
        }
    }

    /// Print a compact tree structure showing just keys and structure
    pub fn print_tree_compact<V>(node: &Option<Rc<Node<V>>>)
    where
        V: Clone,
    {
        print_tree_compact_helper(node, "", true, true);
    }

    fn print_tree_compact_helper<V>(
        node: &Option<Rc<Node<V>>>,
        prefix: &str,
        is_last: bool,
        is_root: bool,
    ) where
        V: Clone,
    {
        match node {
            None => {
                if !is_root {
                    println!("{}{}∅", prefix, if is_last { "└── " } else { "├── " });
                }
            }
            Some(n) => match n.as_ref() {
                Node::Data(data_node) => {
                    let node_symbol = if is_root {
                        ""
                    } else if is_last {
                        "└── "
                    } else {
                        "├── "
                    };
                    println!("{}{}{:?}", prefix, node_symbol, data_node.key);

                    let new_prefix = format!(
                        "{}{}",
                        prefix,
                        if is_root {
                            ""
                        } else if is_last {
                            "    "
                        } else {
                            "│   "
                        }
                    );

                    let has_left = data_node.left.is_some();
                    let has_right = data_node.right.is_some();

                    if has_left || has_right {
                        if has_left {
                            print_tree_compact_helper(
                                &data_node.left,
                                &new_prefix,
                                !has_right,
                                false,
                            );
                        }
                        if has_right {
                            print_tree_compact_helper(&data_node.right, &new_prefix, true, false);
                        }
                    }
                }
                Node::Mapping(mapping_node) => {
                    let node_symbol = if is_root {
                        ""
                    } else if is_last {
                        "└── "
                    } else {
                        "├── "
                    };
                    println!("{}{}[MAPPING]", prefix, node_symbol);
                    let new_prefix = format!(
                        "{}{}",
                        prefix,
                        if is_root {
                            ""
                        } else if is_last {
                            "    "
                        } else {
                            "│   "
                        }
                    );
                    print_tree_compact_helper(&mapping_node.child, &new_prefix, true, false);
                }
            },
        }
    }

    /// Example test demonstrating the debug printing functionality
    #[test]
    fn test_debug_tree_visualization() {
        let mut tree = WBTreeMap::new();

        // Insert some values to create a non-trivial tree structure
        let values = vec![5, 3, 7, 1, 4, 6, 8, 2];
        for val in values {
            tree.insert(val, format!("value_{}", val));
        }

        println!("\n=== Full Debug Tree Structure ===");
        print_tree_debug(&tree.root);

        println!("\n=== Compact Tree Structure (Keys Only) ===");
        print_tree_compact(&tree.root);

        // Verify the tree is still weight-balanced
        assert!(is_weight_balanced(&tree.root));
    }

    /// Test the debug printing with an empty tree
    #[test]
    fn test_debug_empty_tree() {
        let tree: WBTreeMap<String> = WBTreeMap::new();

        println!("\n=== Empty Tree Debug ===");
        print_tree_debug(&tree.root);

        println!("\n=== Empty Tree Compact ===");
        print_tree_compact(&tree.root);
    }

    /// Test the debug printing with a single node
    #[test]
    fn test_debug_single_node() {
        let mut tree = WBTreeMap::new();
        tree.insert(42, "answer");

        println!("\n=== Single Node Tree Debug ===");
        print_tree_debug(&tree.root);

        println!("\n=== Single Node Tree Compact ===");
        print_tree_compact(&tree.root);
    }

    /// Test the debug printing with a linear tree (worst case)
    #[test]
    fn test_debug_sequential_tree() {
        let mut tree = WBTreeMap::new();

        // Insert sequential values (this will trigger rebalancing)
        for i in 1..=7 {
            tree.insert(i, format!("val_{}", i));
        }

        println!("\n=== Sequential Insertion Tree (Rebalanced) ===");
        print_tree_debug(&tree.root);

        assert!(is_weight_balanced(&tree.root));
    }

    fn tree_height<V>(node: &Option<Rc<Node<V>>>) -> usize
    where
        V: Clone,
    {
        match node {
            None => 0,
            Some(n) => match n.as_ref() {
                Node::Data(data_node) => {
                    1 + tree_height(&data_node.left).max(tree_height(&data_node.right))
                }
                Node::Mapping(mapping_node) => tree_height(&mapping_node.child),
            },
        }
    }

    fn is_weight_balanced<V>(node: &Option<Rc<Node<V>>>) -> bool
    where
        V: Clone,
    {
        match node {
            None => true,
            Some(n) => match n.as_ref() {
                Node::Data(data_node) => {
                    let left_size = Node::size(&data_node.left);
                    let right_size = Node::size(&data_node.right);

                    // Check weight balance condition using original WBT algorithm
                    if left_size + right_size >= 2 {
                        // Original WBT: use weights (size + 1) instead of just sizes
                        let left_weight = left_size + 1;
                        let right_weight = right_size + 1;

                        // Balance condition: delta * left_weight >= right_weight AND delta * right_weight >= left_weight
                        if too_heavy(right_weight, left_weight)
                            || too_heavy(left_weight, right_weight)
                        {
                            return false;
                        }
                    }

                    // Check size is correct
                    if data_node.size.get() != 1 + left_size + right_size {
                        return false;
                    }

                    // Recursively check subtrees
                    is_weight_balanced(&data_node.left) && is_weight_balanced(&data_node.right)
                }
                Node::Mapping(mapping_node) => is_weight_balanced(&mapping_node.child),
            },
        }
    }

    #[test]
    fn test_basic_operations() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Test insert
        assert_eq!(wb_map.insert(5, "five"), bt_map.insert(5, "five"));
        assert_eq!(wb_map.insert(3, "three"), bt_map.insert(3, "three"));
        assert_eq!(wb_map.insert(7, "seven"), bt_map.insert(7, "seven"));
        assert_eq!(wb_map.insert(1, "one"), bt_map.insert(1, "one"));
        assert_eq!(wb_map.insert(9, "nine"), bt_map.insert(9, "nine"));

        // Test len and is_empty
        assert_eq!(wb_map.len(), bt_map.len());
        assert_eq!(wb_map.is_empty(), bt_map.is_empty());

        // Test get
        assert_eq!(wb_map.get(&5), bt_map.get(&5));
        assert_eq!(wb_map.get(&3), bt_map.get(&3));
        assert_eq!(wb_map.get(&10), bt_map.get(&10));

        // Test contains_key
        assert_eq!(wb_map.contains_key(&5), bt_map.contains_key(&5));
        assert_eq!(wb_map.contains_key(&10), bt_map.contains_key(&10));

        // Test update
        assert_eq!(wb_map.insert(5, "FIVE"), bt_map.insert(5, "FIVE"));
        assert_eq!(wb_map.get(&5), bt_map.get(&5));
    }

    #[test]
    fn test_iter() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        let data = vec![
            (5, "five"),
            (3, "three"),
            (7, "seven"),
            (1, "one"),
            (9, "nine"),
        ];

        for (k, v) in &data {
            wb_map.insert(*k, *v);
            bt_map.insert(*k, *v);
        }

        let wb_items: Vec<_> = wb_map.iter().collect();
        let bt_items: Vec<_> = bt_map.iter().collect();

        assert_eq!(wb_items.len(), bt_items.len());

        // Both should iterate in sorted order
        for (wb_item, bt_item) in wb_items.iter().zip(bt_items.iter()) {
            assert_eq!(wb_item.0, *bt_item.0);
            assert_eq!(wb_item.1, bt_item.1);
        }
    }

    #[test]
    fn test_clear() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        for i in 0..10 {
            wb_map.insert(i, i * 2);
            bt_map.insert(i, i * 2);
        }

        wb_map.clear();
        bt_map.clear();

        assert_eq!(wb_map.len(), bt_map.len());
        assert_eq!(wb_map.is_empty(), bt_map.is_empty());
    }

    #[test]
    fn test_entry_api() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Test or_insert
        *wb_map.entry(5).or_insert(10) += 5;
        *bt_map.entry(5).or_insert(10) += 5;
        assert_eq!(wb_map.get(&5), bt_map.get(&5));

        // Test or_insert_with
        *wb_map.entry(7).or_insert_with(|| 20) += 3;
        *bt_map.entry(7).or_insert_with(|| 20) += 3;
        assert_eq!(wb_map.get(&7), bt_map.get(&7));

        // Test modifying existing entry
        *wb_map.entry(5).or_insert(0) *= 2;
        *bt_map.entry(5).or_insert(0) *= 2;
        assert_eq!(wb_map.get(&5), bt_map.get(&5));
    }

    #[test]
    fn test_sequential_insert_ascending() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Insert in ascending order - worst case for unbalanced trees
        for i in 0..1000 {
            assert_eq!(wb_map.insert(i, i * 2), bt_map.insert(i, i * 2));
        }

        assert_eq!(wb_map.len(), bt_map.len());

        // Verify all values match
        for i in 0..1000 {
            assert_eq!(wb_map.get(&i), bt_map.get(&i));
        }

        // Check tree is balanced
        assert!(is_weight_balanced(&wb_map.root));
        let height = tree_height(&wb_map.root);
        let expected_max_height = (1000f64.log2() * 2.0) as usize; // Rough upper bound
                                                                   //
        assert!(
            height < expected_max_height,
            "Tree height {} exceeds expected max {}",
            height,
            expected_max_height
        );
    }

    #[test]
    fn test_sequential_insert_descending() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Insert in descending order
        for i in (0..1000).rev() {
            assert_eq!(wb_map.insert(i, i * 3), bt_map.insert(i, i * 3));
        }

        assert_eq!(wb_map.len(), bt_map.len());

        // Verify iteration order matches
        let wb_items: Vec<_> = wb_map.iter().map(|(k, v)| (k, *v)).collect();
        let bt_items: Vec<_> = bt_map.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(wb_items, bt_items);

        assert!(is_weight_balanced(&wb_map.root));
    }

    #[test]
    fn test_random_operations() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Random insertions
        for _ in 0..1000 {
            let key = rng.random_range(0..500);
            let value = rng.random_range(0..10000);
            assert_eq!(wb_map.insert(key, value), bt_map.insert(key, value));
        }

        // Random lookups
        for _ in 0..500 {
            let key = rng.random_range(0..600);
            assert_eq!(wb_map.get(&key), bt_map.get(&key));
            assert_eq!(wb_map.contains_key(&key), bt_map.contains_key(&key));
        }

        // Verify all entries match
        let wb_items: Vec<_> = wb_map.iter().map(|(k, v)| (k, *v)).collect();
        let bt_items: Vec<_> = bt_map.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(wb_items, bt_items);

        assert!(is_weight_balanced(&wb_map.root));
    }

    #[test]
    fn test_alternating_pattern() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Insert alternating small and large values
        for i in 0..500 {
            let key = if i % 2 == 0 { i } else { 1000 - i };
            assert_eq!(wb_map.insert(key, key * 2), bt_map.insert(key, key * 2));
        }

        assert_eq!(wb_map.len(), bt_map.len());
        assert!(is_weight_balanced(&wb_map.root));

        // Verify iteration order
        let wb_keys: Vec<_> = wb_map.iter().map(|(k, _)| k).collect();
        let bt_keys: Vec<_> = bt_map.keys().copied().collect();
        assert_eq!(wb_keys, bt_keys);
    }

    #[test]
    fn test_get_mut() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        for i in 0..20 {
            wb_map.insert(i, i * 10);
            bt_map.insert(i, i * 10);
        }

        // Modify values
        for i in (0..20).step_by(2) {
            if let Some(wb_val) = wb_map.get_mut(&i) {
                *wb_val += 100;
            }
            if let Some(bt_val) = bt_map.get_mut(&i) {
                *bt_val += 100;
            }
        }

        // Verify all values match
        for i in 0..20 {
            assert_eq!(wb_map.get(&i), bt_map.get(&i));
        }
    }

    #[test]
    fn test_clone() {
        let mut original = WBTreeMap::new();
        for i in 0..50 {
            original.insert(i, format!("value_{}", i));
        }

        let cloned = original.clone();

        assert_eq!(original.len(), cloned.len());
        for (k, v) in original.iter() {
            assert_eq!(cloned.get(&k), Some(v));
        }

        // Verify clone is independent
        original.insert(100, "new_value".to_string());
        assert!(!cloned.contains_key(&100));
    }

    #[test]
    fn test_empty_operations() {
        let mut wb_map: WBTreeMap<i32> = WBTreeMap::new();
        let bt_map: BTreeMap<u32, i32> = BTreeMap::new();

        assert_eq!(wb_map.is_empty(), bt_map.is_empty());
        assert_eq!(wb_map.len(), bt_map.len());
        assert_eq!(wb_map.get(&42), bt_map.get(&42));
        assert_eq!(wb_map.contains_key(&42), bt_map.contains_key(&42));

        let items: Vec<_> = wb_map.iter().collect();
        assert!(items.is_empty());

        wb_map.clear();
        assert!(wb_map.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        wb_map.insert(42, "answer");
        bt_map.insert(42, "answer");

        assert_eq!(wb_map.len(), bt_map.len());
        assert_eq!(wb_map.get(&42), bt_map.get(&42));

        let wb_items: Vec<_> = wb_map.iter().collect();
        let bt_items: Vec<_> = bt_map.iter().collect();
        assert_eq!(wb_items.len(), bt_items.len());
        assert_eq!(wb_items[0].0, *bt_items[0].0);
        assert_eq!(wb_items[0].1, bt_items[0].1);
    }

    #[test]
    fn test_duplicate_inserts() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // First insert
        assert_eq!(wb_map.insert(5, "first"), bt_map.insert(5, "first"));

        // Replace value
        assert_eq!(wb_map.insert(5, "second"), bt_map.insert(5, "second"));
        assert_eq!(wb_map.get(&5), bt_map.get(&5));

        // Replace again
        assert_eq!(wb_map.insert(5, "third"), bt_map.insert(5, "third"));
        assert_eq!(wb_map.get(&5), bt_map.get(&5));

        assert_eq!(wb_map.len(), bt_map.len());
    }

    #[test]
    fn test_zigzag_pattern() {
        let mut wb_map = WBTreeMap::new();

        // Create a zigzag pattern: insert middle, then alternating left/right
        let values = vec![
            500, 250, 750, 125, 375, 625, 875, 62, 187, 312, 437, 562, 687, 812, 937,
        ];
        for val in values {
            wb_map.insert(val, val);
        }

        assert!(is_weight_balanced(&wb_map.root));

        // Verify in-order traversal gives sorted sequence
        let keys: Vec<_> = wb_map.iter().map(|(k, _)| k).collect();
        let mut sorted = keys.clone();
        sorted.sort();
        assert_eq!(keys, sorted);
    }

    #[test]
    fn test_balance_verification() {
        // Test various insertion patterns
        let patterns = vec![
            // Sequential
            (0..100).collect::<Vec<_>>(),
            // Reverse sequential
            (0..100).rev().collect::<Vec<_>>(),
            // Random with seed
            {
                let mut rng = StdRng::seed_from_u64(12345);
                let mut v: Vec<u32> = (0..100).collect();
                use rand::seq::SliceRandom;
                v.shuffle(&mut rng);
                v
            },
        ];

        for (pattern_idx, pattern) in patterns.iter().enumerate() {
            println!("\n=== Testing Pattern {} ===", pattern_idx);
            let mut wb_map = WBTreeMap::new();
            for (i, val) in pattern.iter().copied().enumerate() {
                println!("\n--- Before inserting {}th value {} ---", i, val);
                print_tree_compact(&wb_map.root);

                wb_map.insert(val, val);

                println!("\n--- After inserting {}th value {} ---", i, val);
                print_tree_compact(&wb_map.root);

                // Check balance after each insertion
                let is_balanced = is_weight_balanced(&wb_map.root);
                if !is_balanced {
                    println!("\n!!! TREE BECAME UNBALANCED !!!");
                    println!("Full tree structure:");
                    print_tree_debug(&wb_map.root);

                    // Print detailed balance information
                    if let Some(ref root) = wb_map.root {
                        if let Node::Data(data_node) = root.as_ref() {
                            let left_size = Node::size(&data_node.left);
                            let right_size = Node::size(&data_node.right);
                            println!("Root node: {:?}", data_node.key);
                            println!("Left subtree size: {}", left_size);
                            println!("Right subtree size: {}", right_size);
                            println!("DELTA * left_size: {}", DELTA * left_size);
                            println!("DELTA * right_size: {}", DELTA * right_size);
                            println!(
                                "Is right_size > DELTA * left_size? {} > {} = {}",
                                right_size,
                                DELTA * left_size,
                                right_size > DELTA * left_size
                            );
                            println!(
                                "Is left_size > DELTA * right_size? {} > {} = {}",
                                left_size,
                                DELTA * right_size,
                                left_size > DELTA * right_size
                            );
                        }
                    }
                }

                assert!(
                    is_balanced,
                    "Tree became unbalanced after inserting the {i}th value {val}.\nIn pattern: {pattern:?}"
                );

                // Only print first few insertions to avoid too much output
                if i >= 10 {
                    break;
                }
            }
        }
    }

    #[test]
    fn test_entry_api_advanced() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Test entry on empty map
        wb_map.entry(5).or_insert(10);
        bt_map.entry(5).or_insert(10);
        assert_eq!(wb_map.get(&5), bt_map.get(&5));

        // Test entry on existing key
        *wb_map.entry(5).or_insert(20) += 5;
        *bt_map.entry(5).or_insert(20) += 5;
        assert_eq!(wb_map.get(&5), bt_map.get(&5));

        // Test or_insert_with with closure
        let mut counter = 0;
        wb_map.entry(10).or_insert_with(|| {
            counter += 1;
            counter * 100
        });
        assert_eq!(wb_map.get(&10), Some(&100));

        // Closure shouldn't be called for existing key
        wb_map.entry(10).or_insert_with(|| {
            counter += 1;
            counter * 100
        });
        assert_eq!(counter, 1); // Should still be 1
    }

    #[test]
    fn test_debug_output_matches_stdlib() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Empty maps should have same debug output
        assert_eq!(format!("{:?}", wb_map), format!("{:?}", bt_map));

        // Single element
        wb_map.insert(1, "one");
        bt_map.insert(1, "one");
        assert_eq!(format!("{:?}", wb_map), format!("{:?}", bt_map));

        // Multiple elements
        wb_map.insert(2, "two");
        wb_map.insert(0, "zero");
        bt_map.insert(2, "two");
        bt_map.insert(0, "zero");
        assert_eq!(format!("{:?}", wb_map), format!("{:?}", bt_map));

        // Test with different value types
        let mut wb_int_map: WBTreeMap<i32> = WBTreeMap::new();
        let mut bt_int_map: BTreeMap<u32, i32> = BTreeMap::new();

        for i in 0u32..5 {
            wb_int_map.insert(i, (i * 10) as i32);
            bt_int_map.insert(i, (i * 10) as i32);
        }
        assert_eq!(format!("{:?}", wb_int_map), format!("{:?}", bt_int_map));
    }

    #[test]
    fn test_debug_output_format() {
        let mut wb_map = WBTreeMap::new();
        wb_map.insert(1, "one");
        wb_map.insert(2, "two");

        let debug_str = format!("{:?}", wb_map);

        // Debug output should be a map format like {1: "one", 2: "two"}
        assert!(debug_str.starts_with('{'));
        assert!(debug_str.ends_with('}'));
        assert!(debug_str.contains("1: \"one\""));
        assert!(debug_str.contains("2: \"two\""));

        // Should be sorted by key (like stdlib BTreeMap)
        let key_1_pos = debug_str.find("1: \"one\"");
        let key_2_pos = debug_str.find("2: \"two\"");
        assert!(
            key_1_pos < key_2_pos,
            "Keys should be sorted in debug output"
        );
    }

    #[test]
    fn test_debug_with_complex_values() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        wb_map.insert(1, vec![1, 2, 3]);
        wb_map.insert(2, vec![4, 5, 6]);
        bt_map.insert(1, vec![1, 2, 3]);
        bt_map.insert(2, vec![4, 5, 6]);

        assert_eq!(format!("{:?}", wb_map), format!("{:?}", bt_map));
    }

    /// Debug test to reproduce the exact failing sequence
    #[test]
    fn test_debug_failing_sequence() {
        let mut wb_map = WBTreeMap::new();

        // Reproduce the exact sequence that fails: [49, 26, 67, 48, 24, 41]
        let sequence = vec![49, 26, 67, 48, 24, 41];

        for (i, val) in sequence.iter().enumerate() {
            println!("\n=== Step {}: Inserting {} ===", i + 1, val);
            println!("Before insertion:");
            print_tree_debug(&wb_map.root);

            wb_map.insert(*val, *val);

            println!("After insertion:");
            print_tree_debug(&wb_map.root);

            let is_balanced = is_weight_balanced(&wb_map.root);
            println!("Is balanced: {}", is_balanced);

            if !is_balanced {
                println!("!!! BALANCE VIOLATION DETECTED !!!");
                break;
            }
        }
    }

    #[test]
    fn test_removal_optimization() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Insert test data
        for i in 0..20 {
            wb_map.insert(i, i * 10);
            bt_map.insert(i, i * 10);
        }

        // Test removing existing keys
        for i in (0..20).step_by(3) {
            let wb_removed = wb_map.remove(&i);
            let bt_removed = bt_map.remove(&i);
            assert_eq!(wb_removed, bt_removed);
        }

        // Test removing non-existent keys
        for i in 100..105 {
            let wb_removed = wb_map.remove(&i);
            let bt_removed = bt_map.remove(&i);
            assert_eq!(wb_removed, bt_removed);
            assert_eq!(wb_removed, None);
        }

        // Verify final state matches
        assert_eq!(wb_map.len(), bt_map.len());
        for (k, v) in wb_map.iter() {
            assert_eq!(bt_map.get(&k), Some(v));
        }

        // Verify tree remains balanced after removals
        assert!(is_weight_balanced(&wb_map.root));
    }

    #[test]
    fn test_union_empty_maps() {
        let map1: WBTreeMap<String> = WBTreeMap::new();
        let map2: WBTreeMap<String> = WBTreeMap::new();

        let result = map1.union(&map2, |_, v1, _| v1);
        assert!(result.is_empty());
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_union_one_empty() {
        let mut map1 = WBTreeMap::new();
        let map2: WBTreeMap<String> = WBTreeMap::new();

        map1.insert(1, "one".to_string());
        map1.insert(2, "two".to_string());

        // Union with empty map
        let result = map1.union(&map2, |_, v1, _| v1);
        assert_eq!(result.len(), 2);
        assert_eq!(result.get(&1), Some(&"one".to_string()));
        assert_eq!(result.get(&2), Some(&"two".to_string()));

        // Empty map union with non-empty
        let result2 = map2.union(&map1, |_, v1, _| v1);
        assert_eq!(result2.len(), 2);
        assert_eq!(result2.get(&1), Some(&"one".to_string()));
        assert_eq!(result2.get(&2), Some(&"two".to_string()));
    }

    #[test]
    fn test_union_disjoint_sets() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Map 1: 1, 3, 5
        map1.insert(1, "one".to_string());
        map1.insert(3, "three".to_string());
        map1.insert(5, "five".to_string());

        // Map 2: 2, 4, 6
        map2.insert(2, "two".to_string());
        map2.insert(4, "four".to_string());
        map2.insert(6, "six".to_string());

        let result = map1.union(&map2, |_, v1, _| v1);
        assert_eq!(result.len(), 6);

        // Check all values are present
        assert_eq!(result.get(&1), Some(&"one".to_string()));
        assert_eq!(result.get(&2), Some(&"two".to_string()));
        assert_eq!(result.get(&3), Some(&"three".to_string()));
        assert_eq!(result.get(&4), Some(&"four".to_string()));
        assert_eq!(result.get(&5), Some(&"five".to_string()));
        assert_eq!(result.get(&6), Some(&"six".to_string()));

        // Verify tree is balanced
        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_union_overlapping_sets() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Map 1
        map1.insert(1, 10);
        map1.insert(2, 20);
        map1.insert(3, 30);
        map1.insert(4, 40);

        // Map 2 with some overlapping keys
        map2.insert(2, 200);
        map2.insert(3, 300);
        map2.insert(5, 500);
        map2.insert(6, 600);

        // Test with merge function that takes first value
        let result1 = map1.union(&map2, |_, v1, _| v1);
        assert_eq!(result1.len(), 6);
        assert_eq!(result1.get(&1), Some(&10));
        assert_eq!(result1.get(&2), Some(&20)); // From map1
        assert_eq!(result1.get(&3), Some(&30)); // From map1
        assert_eq!(result1.get(&4), Some(&40));
        assert_eq!(result1.get(&5), Some(&500));
        assert_eq!(result1.get(&6), Some(&600));

        // Test with merge function that takes second value
        let result2 = map1.union(&map2, |_, _, v2| v2);
        assert_eq!(result2.len(), 6);
        assert_eq!(result2.get(&1), Some(&10));
        assert_eq!(result2.get(&2), Some(&200)); // From map2
        assert_eq!(result2.get(&3), Some(&300)); // From map2
        assert_eq!(result2.get(&4), Some(&40));
        assert_eq!(result2.get(&5), Some(&500));
        assert_eq!(result2.get(&6), Some(&600));

        // Test with merge function that sums values
        let result3 = map1.union(&map2, |_, v1, v2| v1 + v2);
        assert_eq!(result3.len(), 6);
        assert_eq!(result3.get(&1), Some(&10));
        assert_eq!(result3.get(&2), Some(&220)); // 20 + 200
        assert_eq!(result3.get(&3), Some(&330)); // 30 + 300
        assert_eq!(result3.get(&4), Some(&40));
        assert_eq!(result3.get(&5), Some(&500));
        assert_eq!(result3.get(&6), Some(&600));

        // Verify all results are balanced
        assert!(is_weight_balanced(&result1.root));
        assert!(is_weight_balanced(&result2.root));
        assert!(is_weight_balanced(&result3.root));
    }

    #[test]
    fn test_union_large_maps() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();
        // Create two large maps with some overlap
        for i in 0..1000 {
            map1.insert(i * 2, format!("map1_{}", i));
        }

        for i in 0..1000 {
            map2.insert(i * 3, format!("map2_{}", i));
        }

        let result = map1.union(&map2, |_key, v1, v2| format!("merged_{}_{}", v1, v2));

        // Check size - should have all unique keys from both maps
        let mut expected_keys = std::collections::HashSet::new();
        for i in 0..1000 {
            expected_keys.insert(i * 2);
            expected_keys.insert(i * 3);
        }
        assert_eq!(result.len(), expected_keys.len());

        // Verify some specific values
        assert_eq!(result.get(&0), Some(&"merged_map1_0_map2_0".to_string()));
        assert_eq!(result.get(&2), Some(&"map1_1".to_string()));
        assert_eq!(result.get(&3), Some(&"map2_1".to_string()));
        assert_eq!(result.get(&6), Some(&"merged_map1_3_map2_2".to_string()));

        // Verify tree is balanced
        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_union_with_complex_merge() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Using vectors as values
        map1.insert(1, vec![1, 2, 3]);
        map1.insert(2, vec![4, 5]);
        map1.insert(3, vec![6]);

        map2.insert(2, vec![7, 8]);
        map2.insert(3, vec![9, 10, 11]);
        map2.insert(4, vec![12]);

        // Merge by concatenating vectors
        let result = map1.union(&map2, |_, mut v1, mut v2| {
            v1.append(&mut v2);
            v1
        });

        assert_eq!(result.len(), 4);
        assert_eq!(result.get(&1), Some(&vec![1, 2, 3]));
        assert_eq!(result.get(&2), Some(&vec![4, 5, 7, 8]));
        assert_eq!(result.get(&3), Some(&vec![6, 9, 10, 11]));
        assert_eq!(result.get(&4), Some(&vec![12]));

        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_union_identical_maps() {
        let mut map1 = WBTreeMap::new();

        for i in 0..50 {
            map1.insert(i, i * 100);
        }

        // Clone map1 to create identical map
        let map2 = map1.clone();

        // Union with max merge
        let result = map1.union(&map2, |_, v1, v2| v1.max(v2));

        assert_eq!(result.len(), 50);
        for i in 0..50 {
            assert_eq!(result.get(&i), Some(&(i * 100)));
        }

        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_difference_empty_maps() {
        let map1: WBTreeMap<String> = WBTreeMap::new();
        let map2: WBTreeMap<String> = WBTreeMap::new();

        let result = map1.difference(&map2, |_k, _v1, _v2| None);
        assert!(result.is_empty());
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_difference_one_empty() {
        let mut map1 = WBTreeMap::new();
        let map2: WBTreeMap<String> = WBTreeMap::new();

        map1.insert(1, "one".to_string());
        map1.insert(2, "two".to_string());

        // Non-empty - empty = original map
        let result = map1.difference(&map2, |_k, _v1, _v2| None);
        assert_eq!(result.len(), 2);
        assert_eq!(result.get(&1), Some(&"one".to_string()));
        assert_eq!(result.get(&2), Some(&"two".to_string()));

        // Empty - non-empty = empty
        let result2 = map2.difference(&map1, |_k, _v1, _v2| None);
        assert!(result2.is_empty());
        assert_eq!(result2.len(), 0);
    }

    #[test]
    fn test_difference_disjoint_sets() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Map 1: 1, 3, 5
        map1.insert(1, "one".to_string());
        map1.insert(3, "three".to_string());
        map1.insert(5, "five".to_string());

        // Map 2: 2, 4, 6
        map2.insert(2, "two".to_string());
        map2.insert(4, "four".to_string());
        map2.insert(6, "six".to_string());

        let result = map1.difference(&map2, |_k, _v1, _v2| None);
        assert_eq!(result.len(), 3);

        // All values from map1 should be present since they don't overlap
        assert_eq!(result.get(&1), Some(&"one".to_string()));
        assert_eq!(result.get(&3), Some(&"three".to_string()));
        assert_eq!(result.get(&5), Some(&"five".to_string()));

        // Values from map2 should not be present
        assert_eq!(result.get(&2), None);
        assert_eq!(result.get(&4), None);
        assert_eq!(result.get(&6), None);

        // Verify tree is balanced
        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_difference_overlapping_sets() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Map 1
        map1.insert(1, 10);
        map1.insert(2, 20);
        map1.insert(3, 30);
        map1.insert(4, 40);

        // Map 2 with some overlapping keys
        map2.insert(2, 200);
        map2.insert(3, 300);
        map2.insert(5, 500);
        map2.insert(6, 600);

        let result = map1.difference(&map2, |_k, _v1, _v2| None);
        assert_eq!(result.len(), 2);

        // Only non-overlapping keys from map1 should remain
        assert_eq!(result.get(&1), Some(&10));
        assert_eq!(result.get(&4), Some(&40));

        // Overlapping keys should be removed
        assert_eq!(result.get(&2), None);
        assert_eq!(result.get(&3), None);

        // Keys only in map2 should not be in result
        assert_eq!(result.get(&5), None);
        assert_eq!(result.get(&6), None);

        // Verify tree is balanced
        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_difference_identical_maps() {
        let mut map1 = WBTreeMap::new();

        for i in 0..50 {
            map1.insert(i, i * 100);
        }

        // Clone map1 to create identical map
        let map2 = map1.clone();

        // Difference of identical maps should be empty
        let result = map1.difference(&map2, |_k, _v1, _v2| None);
        assert!(result.is_empty());
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_difference_subset() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Map 1: 1, 2, 3, 4, 5
        for i in 1..=5 {
            map1.insert(i, i * 10);
        }

        // Map 2 is subset: 2, 4
        map2.insert(2, 200);
        map2.insert(4, 400);

        let result = map1.difference(&map2, |_k, _v1, _v2| None);
        assert_eq!(result.len(), 3);

        // Only non-subset elements should remain
        assert_eq!(result.get(&1), Some(&10));
        assert_eq!(result.get(&3), Some(&30));
        assert_eq!(result.get(&5), Some(&50));

        // Subset elements should be removed
        assert_eq!(result.get(&2), None);
        assert_eq!(result.get(&4), None);

        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_difference_large_maps() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Create two large maps with some overlap
        for i in 0..1000 {
            map1.insert(i * 2, format!("map1_{}", i));
        }

        for i in 0..500 {
            map2.insert(i * 4, format!("map2_{}", i));
        }

        let result = map1.difference(&map2, |_k, _v1, _v2| None);

        // Check that overlapping keys are removed
        for i in 0..500 {
            assert_eq!(result.get(&(i * 4)), None);
        }

        // Check that some non-overlapping keys remain
        assert!(result.get(&2).is_some());
        assert!(result.get(&6).is_some());
        assert!(result.get(&10).is_some());

        // Verify tree is balanced
        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_difference_with_complex_types() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        // Using vectors as values
        map1.insert(1, vec![1, 2, 3]);
        map1.insert(2, vec![4, 5]);
        map1.insert(3, vec![6]);
        map1.insert(4, vec![7, 8, 9]);

        map2.insert(2, vec![10, 11]);
        map2.insert(3, vec![12]);

        let result = map1.difference(&map2, |_k, _v1, _v2| None);

        assert_eq!(result.len(), 2);
        assert_eq!(result.get(&1), Some(&vec![1, 2, 3]));
        assert_eq!(result.get(&4), Some(&vec![7, 8, 9]));
        assert_eq!(result.get(&2), None);
        assert_eq!(result.get(&3), None);

        assert!(is_weight_balanced(&result.root));
    }

    #[test]
    fn test_difference_single_elements() {
        let mut map1 = WBTreeMap::new();
        let mut map2 = WBTreeMap::new();

        map1.insert(42, "answer");
        map2.insert(24, "not_answer");

        // No overlap
        let result1 = map1.difference(&map2, |_k, _v1, _v2| None);
        assert_eq!(result1.len(), 1);
        assert_eq!(result1.get(&42), Some(&"answer"));

        // Total overlap
        map2.clear();
        map2.insert(42, "different_answer");
        let result2 = map1.difference(&map2, |_k, _v1, _v2| None);
        assert!(result2.is_empty());
    }

    #[test]
    fn test_iter_mut() {
        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        // Insert initial data
        for i in 0..20 {
            wb_map.insert(i, i * 10);
            bt_map.insert(i, i * 10);
        }

        // Modify all values using iter_mut
        for (_key, value) in wb_map.iter_mut() {
            *value += 100;
        }

        // Modify BTreeMap for comparison
        for value in bt_map.values_mut() {
            *value += 100;
        }

        // Verify all values match
        for i in 0..20 {
            assert_eq!(wb_map.get(&i), bt_map.get(&i));
        }
    }

    #[test]
    fn test_iter_mut_empty() {
        let mut wb_map: WBTreeMap<i32> = WBTreeMap::new();

        // Should handle empty map gracefully
        let count = wb_map.iter_mut().count();
        assert_eq!(count, 0);
    }

    #[test]
    fn test_iter_mut_single_element() {
        let mut wb_map = WBTreeMap::new();
        wb_map.insert(42, "answer");

        // Modify the single element
        for (_key, value) in wb_map.iter_mut() {
            *value = "modified";
        }

        assert_eq!(wb_map.get(&42), Some(&"modified"));
    }

    #[test]
    fn test_iter_mut_copy_on_write() {
        let mut wb_map1 = WBTreeMap::new();

        // Insert some data
        for i in 0..10 {
            wb_map1.insert(i, i * 10);
        }

        // Clone the map - this will share the underlying nodes
        let wb_map2 = wb_map1.clone();

        // Modify map1 using iter_mut - should trigger copy-on-write
        for (_key, value) in wb_map1.iter_mut() {
            *value += 1000;
        }

        // Verify map1 was modified
        for i in 0..10 {
            assert_eq!(wb_map1.get(&i), Some(&(i * 10 + 1000)));
        }

        // Verify map2 was NOT modified (copy-on-write worked)
        for i in 0..10 {
            assert_eq!(wb_map2.get(&i), Some(&(i * 10)));
        }
    }

    #[test]
    fn test_iter_mut_order() {
        let mut wb_map = WBTreeMap::new();

        // Insert in random order
        let values = vec![5, 2, 8, 1, 3, 7, 9, 4, 6];
        for val in values {
            wb_map.insert(val, val * 100);
        }

        // Collect keys from iter_mut - should be in sorted order
        let mut keys = Vec::new();
        for (key, _value) in wb_map.iter_mut() {
            keys.push(key);
        }

        assert_eq!(keys, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_iter_mut_selective_modification() {
        let mut wb_map = WBTreeMap::new();

        // Insert data
        for i in 0..20 {
            wb_map.insert(i, i);
        }

        // Only modify even keys
        for (key, value) in wb_map.iter_mut() {
            if key % 2 == 0 {
                *value = *value * 1000;
            }
        }

        // Verify selective modification
        for i in 0..20 {
            if i % 2 == 0 {
                assert_eq!(wb_map.get(&i), Some(&(i * 1000)));
            } else {
                assert_eq!(wb_map.get(&i), Some(&i));
            }
        }
    }

    #[test]
    fn test_mapped_basic() {
        use crate::{PrefixTree1, PrefixTree2};

        // Create a simple map {0: "zero", 1: "one", 2: "two"}
        let mut base_map: WBTreeMap<&str> = WBTreeMap::new();
        base_map.insert(0, "zero");
        base_map.insert(1, "one");
        base_map.insert(2, "two");

        // Create a mapping: 0 -> 10, 1 -> 20, 2 -> 30
        let mut mapping = PrefixTree2::new();
        let mut set_10 = PrefixTree1::new();
        set_10.set.insert(10);
        let mut set_20 = PrefixTree1::new();
        set_20.set.insert(20);
        let mut set_30 = PrefixTree1::new();
        set_30.set.insert(30);
        mapping.insert_restriction(0, set_10);
        mapping.insert_restriction(1, set_20);
        mapping.insert_restriction(2, set_30);

        // Apply the mapping
        let mapped_tree = base_map.mapped(mapping);

        // Test get with mapped keys
        assert_eq!(mapped_tree.get(&10), Some(&"zero"));
        assert_eq!(mapped_tree.get(&20), Some(&"one"));
        assert_eq!(mapped_tree.get(&30), Some(&"two"));

        // Test that original keys don't work
        assert_eq!(mapped_tree.get(&0), None);
        assert_eq!(mapped_tree.get(&1), None);
        assert_eq!(mapped_tree.get(&2), None);

        // Test iteration yields mapped keys
        let items: Vec<_> = mapped_tree.iter().collect();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], (10, &"zero"));
        assert_eq!(items[1], (20, &"one"));
        assert_eq!(items[2], (30, &"two"));
    }

    #[test]
    fn test_mapped_partial_domain() {
        use crate::{PrefixTree1, PrefixTree2};

        // Create a map {0: "zero", 1: "one", 2: "two", 3: "three"}
        let mut base_map: WBTreeMap<&str> = WBTreeMap::new();
        base_map.insert(0, "zero");
        base_map.insert(1, "one");
        base_map.insert(2, "two");
        base_map.insert(3, "three");

        // Create a mapping that only covers 0 and 2: 0 -> 10, 2 -> 30
        let mut mapping = PrefixTree2::new();
        let mut set_10 = PrefixTree1::new();
        set_10.set.insert(10);
        let mut set_30 = PrefixTree1::new();
        set_30.set.insert(30);
        mapping.insert_restriction(0, set_10);
        mapping.insert_restriction(2, set_30);

        // Apply the mapping
        let mapped_tree = base_map.mapped(mapping);

        assert_eq!(mapped_tree.get(&10), Some(&"zero"));
        assert_eq!(mapped_tree.get(&30), Some(&"two"));
        assert_eq!(mapped_tree.len(), 2);

        // Iteration yields only keys in the mapping domain
        let items: Vec<_> = mapped_tree.iter().collect();
        assert_eq!(items.len(), 2);
        assert_eq!(items[0], (10, &"zero"));
        assert_eq!(items[1], (30, &"two"));
    }

    #[test]
    fn test_mapped_nested() {
        use crate::{PrefixTree1, PrefixTree2};

        // Create base map {0: "a", 1: "b"}
        let mut base_map: WBTreeMap<&str> = WBTreeMap::new();
        base_map.insert(0, "a");
        base_map.insert(1, "b");

        // First mapping: 0 -> 10, 1 -> 20
        let mut mapping1 = PrefixTree2::new();
        let mut set_10 = PrefixTree1::new();
        set_10.set.insert(10);
        let mut set_20 = PrefixTree1::new();
        set_20.set.insert(20);
        mapping1.insert_restriction(0, set_10);
        mapping1.insert_restriction(1, set_20);

        // Second mapping: 10 -> 100, 20 -> 200
        let mut mapping2 = PrefixTree2::new();
        let mut set_100 = PrefixTree1::new();
        set_100.set.insert(100);
        let mut set_200 = PrefixTree1::new();
        set_200.set.insert(200);
        mapping2.insert_restriction(10, set_100);
        mapping2.insert_restriction(20, set_200);

        // Apply mappings in sequence
        let mapped_once = base_map.mapped(mapping1);
        let mapped_twice = mapped_once.mapped(mapping2);

        // After two mappings: 0 -> 10 -> 100, 1 -> 20 -> 200
        assert_eq!(mapped_twice.get(&100), Some(&"a"));
        assert_eq!(mapped_twice.get(&200), Some(&"b"));

        // Intermediate keys shouldn't work
        assert_eq!(mapped_twice.get(&10), None);
        assert_eq!(mapped_twice.get(&20), None);
        assert_eq!(mapped_twice.get(&0), None);
        assert_eq!(mapped_twice.get(&1), None);

        // Iteration
        let items: Vec<_> = mapped_twice.iter().collect();
        assert_eq!(items.len(), 2);
        assert_eq!(items[0], (100, &"a"));
        assert_eq!(items[1], (200, &"b"));
    }
}
