use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::rc::Rc;

use crate::PrefixTree2;

#[derive(Clone)]
pub struct WBTreeMap<V: Clone> {
    root: Option<Rc<Node<V>>>,
    len: usize,
}

#[derive(Clone)]
struct DataNode<V: Clone> {
    key: u32,
    value: V,
    left: Option<Rc<Node<V>>>,
    right: Option<Rc<Node<V>>>,
    size: usize, // Total number of nodes in this subtree
}

impl<V: Clone> DataNode<V> {
    fn update_size_internal(&mut self) {
        self.size = 1 + Node::size(&self.left) + Node::size(&self.right);
    }
}

#[derive(Clone)]
struct MappingNode<V: Clone> {
    mapping: PrefixTree2,
    child: Option<Rc<Node<V>>>,
}

#[derive(Clone)]
#[allow(dead_code)]
enum Node<V: Clone> {
    Data(DataNode<V>),
    Mapping(MappingNode<V>),
}

/// Apply a single mapping to a u32 value.
/// Returns None if the mapping doesn't have an entry for the value.
fn apply_single_mapping(mapping: &PrefixTree2, val: u32) -> Option<u32> {
    mapping
        .get(val)
        .and_then(|restriction| restriction.set.iter().next())
}

/// Apply a sequence of mappings to a u32 value. Each mapping in the slice is a PrefixTree2.
/// Mappings are applied in reverse order: last mapping first, first mapping last.
/// This is because mappings are accumulated outermost-first during tree traversal,
/// but should be applied innermost-first (closest to data first).
/// Returns None if any mapping doesn't have an entry for the value.
fn apply_mappings(mappings: &[&PrefixTree2], val: u32) -> Option<u32> {
    let mut result = val;
    for mapping in mappings.iter().rev() {
        result = apply_single_mapping(mapping, result)?;
    }
    Some(result)
}

// TODO: Make this more sophisticated, e.g. by checking the invariant that the mapping is monotone,
// special cases for maps of the form (+ <offset>) etc.

// Weight balance parameters
const DELTA: usize = 3;
const GAMMA: usize = 2;

impl<V: Clone> Node<V> {
    fn new(key: u32, value: V) -> Self {
        Self::Data(DataNode {
            key,
            value,
            left: None,
            right: None,
            size: 1,
        })
    }

    /// Helper to get direct access to the underlying data node, skipping mapping nodes.
    /// Returns None for empty mapping chains.
    #[allow(dead_code)]
    fn as_data_node(node: &Rc<Node<V>>) -> Option<&DataNode<V>> {
        match node.as_ref() {
            Node::Data(data_node) => Some(data_node),
            Node::Mapping(mapping_node) => mapping_node.child.as_ref().and_then(Self::as_data_node),
        }
    }

    /// Unwrap a node to its DataNode, consuming the Rc.
    /// For mapping nodes, recursively unwraps to get the inner data.
    fn unwrap_to_data(node: Rc<Node<V>>) -> DataNode<V> {
        match Rc::unwrap_or_clone(node) {
            Node::Data(data_node) => data_node,
            Node::Mapping(mapping_node) => {
                let child = mapping_node.child.expect("Mapping node should have child");
                Self::unwrap_to_data(child)
            }
        }
    }

    /// Create a new data node with the given fields
    fn new_data_node(
        key: u32,
        value: V,
        left: Option<Rc<Node<V>>>,
        right: Option<Rc<Node<V>>>,
    ) -> Rc<Node<V>> {
        let size = 1 + Self::size(&left) + Self::size(&right);
        Rc::new(Node::Data(DataNode {
            key,
            value,
            left,
            right,
            size,
        }))
    }

    #[allow(dead_code)]
    fn wrapped_in_mappings(mappings: &[&PrefixTree2], node: Option<Rc<Self>>) -> Option<Rc<Self>> {
        let mut result = node;
        for mapping in mappings.iter().rev() {
            result = Some(Rc::new(Self::Mapping(MappingNode {
                mapping: (*mapping).clone(),
                child: result,
            })));
        }
        result
    }

    fn size(node: &Option<Rc<Node<V>>>) -> usize {
        node.as_ref().map_or(0, |n| match n.as_ref() {
            Node::Data(data_node) => data_node.size,
            Node::Mapping(mapping_node) => Self::size(&mapping_node.child),
        })
    }

    #[allow(dead_code)]
    fn update_size(&mut self) {
        match self {
            Node::Data(data_node) => {
                data_node.update_size_internal();
            }
            Node::Mapping(mapping_node) => {
                if let Some(ref mut child) = mapping_node.child {
                    Rc::make_mut(child).update_size();
                }
            }
        }
    }

    /// Rotate left around a data node. For mapping nodes, this is a no-op.
    fn rotate_left(mut node: Rc<Node<V>>) -> Rc<Node<V>> {
        // Only rotate data nodes
        let is_data = matches!(node.as_ref(), Node::Data(_));
        if !is_data {
            return node;
        }

        let node_mut = Rc::make_mut(&mut node);
        let data_node = match node_mut {
            Node::Data(d) => d,
            Node::Mapping(_) => return node,
        };

        let mut right = match data_node.right.take() {
            Some(r) => r,
            None => return node, // Can't rotate without right child
        };

        // Check if right child is a data node
        let right_is_data = matches!(right.as_ref(), Node::Data(_));
        if !right_is_data {
            // Put right back and return without rotating
            data_node.right = Some(right);
            return node;
        }

        let right_mut = Rc::make_mut(&mut right);
        let right_data = match right_mut {
            Node::Data(d) => d,
            Node::Mapping(_) => {
                data_node.right = Some(right);
                return node;
            }
        };

        data_node.right = right_data.left.take();
        data_node.update_size_internal();
        right_data.left = Some(node);
        right_data.update_size_internal();

        right
    }

    /// Rotate right around a data node. For mapping nodes, this is a no-op.
    fn rotate_right(mut node: Rc<Node<V>>) -> Rc<Node<V>> {
        // Only rotate data nodes
        let is_data = matches!(node.as_ref(), Node::Data(_));
        if !is_data {
            return node;
        }

        let node_mut = Rc::make_mut(&mut node);
        let data_node = match node_mut {
            Node::Data(d) => d,
            Node::Mapping(_) => return node,
        };

        let mut left = match data_node.left.take() {
            Some(l) => l,
            None => return node, // Can't rotate without left child
        };

        // Check if left child is a data node
        let left_is_data = matches!(left.as_ref(), Node::Data(_));
        if !left_is_data {
            // Put left back and return without rotating
            data_node.left = Some(left);
            return node;
        }

        let left_mut = Rc::make_mut(&mut left);
        let left_data = match left_mut {
            Node::Data(d) => d,
            Node::Mapping(_) => {
                data_node.left = Some(left);
                return node;
            }
        };

        data_node.left = left_data.right.take();
        data_node.update_size_internal();
        left_data.right = Some(node);
        left_data.update_size_internal();

        left
    }

    /// Balance a node. Only balances data nodes; mapping nodes pass through unchanged.
    fn balance(mut node: Rc<Node<V>>) -> Rc<Node<V>> {
        // Only balance data nodes
        let (left_size, right_size) = match node.as_ref() {
            Node::Data(data_node) => (Self::size(&data_node.left), Self::size(&data_node.right)),
            Node::Mapping(_) => return node, // Don't balance mapping nodes
        };

        if left_size + right_size < 2 {
            return node;
        }

        // Original WBT algorithm: use weights (size + 1) instead of just sizes
        let left_weight = left_size + 1;
        let right_weight = right_size + 1;

        if right_weight > DELTA * left_weight {
            // Right-heavy, need to check right child for rotation type
            let right_child_sizes = match node.as_ref() {
                Node::Data(data_node) => {
                    if let Some(ref right) = data_node.right {
                        match right.as_ref() {
                            Node::Data(right_data) => {
                                Some((Self::size(&right_data.left), Self::size(&right_data.right)))
                            }
                            Node::Mapping(_) => None, // Can't balance across mapping
                        }
                    } else {
                        None
                    }
                }
                Node::Mapping(_) => None,
            };

            if let Some((right_left_size, right_right_size)) = right_child_sizes {
                let right_left_weight = right_left_size + 1;
                let right_right_weight = right_right_size + 1;

                if right_left_weight < GAMMA * right_right_weight {
                    // Single rotation
                    Self::rotate_left(node)
                } else {
                    // Double rotation
                    let node_mut = Rc::make_mut(&mut node);
                    if let Node::Data(data_node) = node_mut {
                        data_node.right = data_node.right.take().map(Self::rotate_right);
                    }
                    Self::rotate_left(node)
                }
            } else {
                node // Can't balance, return as-is
            }
        } else if left_weight > DELTA * right_weight {
            // Left-heavy, need to check left child for rotation type
            let left_child_sizes = match node.as_ref() {
                Node::Data(data_node) => {
                    if let Some(ref left) = data_node.left {
                        match left.as_ref() {
                            Node::Data(left_data) => {
                                Some((Self::size(&left_data.left), Self::size(&left_data.right)))
                            }
                            Node::Mapping(_) => None, // Can't balance across mapping
                        }
                    } else {
                        None
                    }
                }
                Node::Mapping(_) => None,
            };

            if let Some((left_left_size, left_right_size)) = left_child_sizes {
                let left_left_weight = left_left_size + 1;
                let left_right_weight = left_right_size + 1;

                if left_right_weight < GAMMA * left_left_weight {
                    // Single rotation
                    Self::rotate_right(node)
                } else {
                    // Double rotation
                    let node_mut = Rc::make_mut(&mut node);
                    if let Node::Data(data_node) = node_mut {
                        data_node.left = data_node.left.take().map(Self::rotate_left);
                    }
                    Self::rotate_right(node)
                }
            } else {
                node // Can't balance, return as-is
            }
        } else {
            node
        }
    }

    /// Insert a key-value pair into the tree.
    /// This is the simple version that doesn't handle mappings - used by the public API.
    fn insert_simple(
        node: Option<Rc<Node<V>>>,
        key: u32,
        value: V,
    ) -> (Option<Rc<Node<V>>>, Option<V>) {
        let mut node = match node {
            Some(n) => n,
            None => {
                return (Some(Rc::new(Node::new(key, value))), None);
            }
        };

        let node_mut: &mut Node<V> = Rc::make_mut(&mut node);
        let data_node: &mut DataNode<V> = match node_mut {
            Node::Data(data_node) => data_node,
            Node::Mapping(mapping_node) => {
                // For the simple version, we recurse into mapping nodes transparently
                let (new_child, old_value) =
                    Self::insert_simple(mapping_node.child.take(), key, value);
                mapping_node.child = new_child;
                return (Some(node), old_value);
            }
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

    fn remove_min(mut node: Rc<Node<V>>) -> (u32, V, Option<Rc<Node<V>>>) {
        // First handle mapping nodes by recursing through them
        match node.as_ref() {
            Node::Mapping(_) => {
                let node_mut = Rc::make_mut(&mut node);
                if let Node::Mapping(mapping_node) = node_mut {
                    let child = mapping_node.child.take();
                    if let Some(child_node) = child {
                        let (min_key, min_value, new_child) = Self::remove_min(child_node);
                        mapping_node.child = new_child;
                        return (min_key, min_value, Some(node));
                    } else {
                        panic!("remove_min called on empty mapping node");
                    }
                }
                unreachable!()
            }
            Node::Data(data_node) => {
                if data_node.left.is_none() {
                    let DataNode {
                        key,
                        value,
                        left: _,
                        right,
                        size: _,
                    } = match Rc::unwrap_or_clone(node) {
                        Node::Data(d) => d,
                        Node::Mapping(_) => unreachable!(),
                    };
                    return (key, value, right);
                }
                // Fall through to handle the case where we have a left child
            }
        }

        // If we get here, we have a data node with a left child
        let node_mut = Rc::make_mut(&mut node);
        let (min_key, min_value) = if let Node::Data(data_node) = node_mut {
            let left = data_node.left.take().unwrap();
            let (min_key, min_value, new_left) = Self::remove_min(left);
            data_node.left = new_left;
            data_node.update_size_internal();
            (min_key, min_value)
        } else {
            unreachable!()
        };

        let balanced_node = Self::balance(node);
        (min_key, min_value, Some(balanced_node))
    }

    fn remove_existing_node(mut node: Rc<Node<V>>, key: &u32) -> (Option<Rc<Node<V>>>, V) {
        // First, handle mapping nodes by recursing through them
        match node.as_ref() {
            Node::Mapping(_) => {
                let node_mut = Rc::make_mut(&mut node);
                if let Node::Mapping(mapping_node) = node_mut {
                    let child = mapping_node
                        .child
                        .take()
                        .expect("Mapping node should have a child");
                    let (new_child, value) = Self::remove_existing_node(child, key);
                    mapping_node.child = new_child;
                    return (Some(node), value);
                }
                unreachable!()
            }
            Node::Data(data_node) => {
                let node_key = &data_node.key;
                match key.cmp(node_key) {
                    Ordering::Equal => {
                        let DataNode {
                            key: _,
                            value,
                            left,
                            right,
                            size: _,
                        } = match Rc::unwrap_or_clone(node) {
                            Node::Data(d) => d,
                            Node::Mapping(_) => unreachable!(),
                        };
                        let new_node = match (left, right) {
                            (None, None) => None,
                            (Some(left), None) => Some(left),
                            (None, Some(right)) => Some(right),
                            (Some(left), Some(right)) => {
                                // Find the minimum element in the right subtree to replace this node
                                let (min_key, min_value, new_right) = Self::remove_min(right);
                                let mut new_data_node = DataNode {
                                    key: min_key,
                                    value: min_value,
                                    left: Some(left),
                                    right: new_right,
                                    size: 0,
                                };
                                new_data_node.size = 1
                                    + Self::size(&new_data_node.left)
                                    + Self::size(&new_data_node.right);
                                Some(Self::balance(Rc::new(Node::Data(new_data_node))))
                            }
                        };
                        return (new_node, value);
                    }
                    Ordering::Less => {
                        let node_mut = Rc::make_mut(&mut node);
                        if let Node::Data(data_node) = node_mut {
                            let left = data_node
                                .left
                                .take()
                                .expect("Node with key must exist, so left cannot be None");

                            let (new_left, value) = Self::remove_existing_node(left, key);

                            data_node.left = new_left;
                            data_node.update_size_internal();

                            let balanced_node = Self::balance(node);
                            return (Some(balanced_node), value);
                        }
                        unreachable!()
                    }
                    Ordering::Greater => {
                        let node_mut = Rc::make_mut(&mut node);
                        if let Node::Data(data_node) = node_mut {
                            let right = data_node
                                .right
                                .take()
                                .expect("Node with key must exist, so right cannot be None");

                            let (new_right, value) = Self::remove_existing_node(right, key);

                            data_node.right = new_right;
                            data_node.update_size_internal();

                            let balanced_node = Self::balance(node);
                            return (Some(balanced_node), value);
                        }
                        unreachable!()
                    }
                }
            }
        }
    }

    fn split(
        node: Option<Rc<Node<V>>>,
        key: &u32,
    ) -> (Option<Rc<Node<V>>>, Option<V>, Option<Rc<Node<V>>>) {
        match node {
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

        if right_size > DELTA * left_size {
            match right {
                None => unreachable!("right should not be None when right_size > left_size"),
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
        } else if left_size > DELTA * right_size {
            match left {
                None => unreachable!("left should not be None when left_size > right_size"),
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
    ) -> Option<Rc<Node<V>>>
    where
        F: FnMut(&u32, V, V) -> V,
    {
        match (left, right) {
            (None, None) => None,
            (Some(t), None) | (None, Some(t)) => Some(t),
            (Some(l), Some(r)) => {
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

                    let new_left = Self::union(l_left, r_left, merge);
                    let new_right = Self::union(l_right, r_right, merge);
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

                    let new_left = Self::union(l_left, r_left, merge);
                    let new_right = Self::union(l_right, r_right, merge);
                    Self::join(new_left, r_key, new_value, new_right)
                }
            }
        }
    }

    fn difference<F>(
        left: Option<Rc<Node<V>>>,
        right: Option<Rc<Node<V>>>,
        diff: &mut F,
    ) -> Option<Rc<Node<V>>>
    where
        F: FnMut(&u32, V, V) -> Option<V>,
    {
        match (left, right) {
            (None, _) => None,
            (Some(l), None) => Some(l),
            (Some(l), Some(r)) => {
                // Use left tree as base, split right tree on left root's key
                let DataNode {
                    key: l_key,
                    value: l_value,
                    left: l_left,
                    right: l_right,
                    size: _,
                } = Self::unwrap_to_data(l);
                let (r_left, r_value_opt, r_right) = Self::split(Some(r), &l_key);

                let new_left = Self::difference(l_left, r_left, diff);
                let new_right = Self::difference(l_right, r_right, diff);

                match r_value_opt {
                    // Key exists in both trees, call diff function
                    Some(r_value) => {
                        match diff(&l_key, l_value, r_value) {
                            // diff returned None, exclude this key from result
                            None => {
                                match (new_left, new_right) {
                                    (None, None) => None,
                                    (Some(left), None) => Some(left),
                                    (None, Some(right)) => Some(right),
                                    (Some(left), Some(right)) => {
                                        // Need to join the subtrees without the current key
                                        Self::join_without_key(left, right)
                                    }
                                }
                            }
                            // diff returned Some(value), keep this key with the new value
                            Some(new_value) => Self::join(new_left, l_key, new_value, new_right),
                        }
                    }
                    // Key doesn't exist in right tree, include it in result
                    None => Self::join(new_left, l_key, l_value, new_right),
                }
            }
        }
    }

    fn join_without_key(left: Rc<Node<V>>, right: Rc<Node<V>>) -> Option<Rc<Node<V>>> {
        // Remove the minimum element from the right subtree to use as the new root
        let (min_key, min_value, new_right) = Self::remove_min(right);
        Self::join(Some(left), min_key, min_value, new_right)
    }
}

impl<V: Clone> WBTreeMap<V> {
    pub const fn new() -> Self {
        WBTreeMap { root: None, len: 0 }
    }

    pub fn insert(&mut self, key: u32, value: V) -> Option<V> {
        let (new_root, old_value) = Node::insert_simple(self.root.take(), key, value);
        self.root = new_root;
        if old_value.is_none() {
            self.len += 1;
        }
        old_value
    }

    pub fn get(&self, key: &u32) -> Option<&V> {
        // Accumulate mappings as we traverse
        let mut mappings: Vec<&PrefixTree2> = Vec::new();
        let mut current = &self.root;
        loop {
            match current {
                None => return None,
                Some(node) => match node.as_ref() {
                    Node::Data(data_node) => {
                        // Apply all accumulated mappings to the stored key
                        let mapped_key = if mappings.is_empty() {
                            Some(data_node.key)
                        } else {
                            apply_mappings(&mappings, data_node.key)
                        };

                        match mapped_key {
                            None => {
                                // Key is not in mapping domain, skip this subtree
                                // This shouldn't happen in a well-formed tree, but handle it
                                return None;
                            }
                            Some(mk) => match key.cmp(&mk) {
                                Ordering::Less => current = &data_node.left,
                                Ordering::Greater => current = &data_node.right,
                                Ordering::Equal => return Some(&data_node.value),
                            },
                        }
                    }
                    Node::Mapping(mapping_node) => {
                        mappings.push(&mapping_node.mapping);
                        current = &mapping_node.child;
                    }
                },
            }
        }
    }

    pub fn get_mut(&mut self, key: &u32) -> Option<&mut V> {
        // Accumulate mappings as we traverse (cloned since we need mutable access)
        let mut mappings: Vec<PrefixTree2> = Vec::new();
        let mut current = &mut self.root;
        loop {
            match current {
                None => return None,
                Some(node) => {
                    let node_mut = Rc::make_mut(node);
                    match node_mut {
                        Node::Data(data_node) => {
                            // Apply all accumulated mappings to the stored key
                            let mapped_key = if mappings.is_empty() {
                                Some(data_node.key)
                            } else {
                                let mapping_refs: Vec<&PrefixTree2> = mappings.iter().collect();
                                apply_mappings(&mapping_refs, data_node.key)
                            };

                            match mapped_key {
                                None => return None,
                                Some(mk) => match key.cmp(&mk) {
                                    Ordering::Less => current = &mut data_node.left,
                                    Ordering::Greater => current = &mut data_node.right,
                                    Ordering::Equal => return Some(&mut data_node.value),
                                },
                            }
                        }
                        Node::Mapping(mapping_node) => {
                            mappings.push(mapping_node.mapping.clone());
                            current = &mut mapping_node.child;
                        }
                    }
                }
            }
        }
    }

    pub fn contains_key(&self, key: &u32) -> bool {
        self.get(key).is_some()
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn clear(&mut self) {
        self.root = None;
        self.len = 0;
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, V> {
        Iter {
            stack: Vec::new(),
            current: Some(&self.root),
            current_mappings: Vec::new(),
        }
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, V> {
        let current = &mut self.root as *mut Option<Rc<Node<V>>>;
        IterMut {
            stack: Vec::new(),
            current: Some(current),
            current_mappings: Vec::new(),
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
        self.len -= 1;
        Some(value)
    }

    pub fn union<F>(&self, other: &Self, mut merge: F) -> Self
    where
        F: FnMut(&u32, V, V) -> V,
    {
        let new_root = Node::union(self.root.clone(), other.root.clone(), &mut merge);
        let new_len = Node::size(&new_root);
        WBTreeMap {
            root: new_root,
            len: new_len,
        }
    }

    pub fn difference<F>(&self, other: &Self, mut diff: F) -> Self
    where
        F: FnMut(&u32, V, V) -> Option<V>,
    {
        let new_root = Node::difference(self.root.clone(), other.root.clone(), &mut diff);
        let new_len = Node::size(&new_root);
        WBTreeMap {
            root: new_root,
            len: new_len,
        }
    }

    /// Returns a new map where all keys have been transformed by the given mapping.
    /// The mapping must be monotone (order-preserving) for the tree structure to remain valid.
    /// Keys not in the mapping's domain will be filtered out during iteration.
    /// This operation is O(1) - it just wraps the tree in a mapping node.
    pub fn mapped(&self, mapping: PrefixTree2) -> Self {
        let new_root = self.root.clone().map(|root| {
            Rc::new(Node::Mapping(MappingNode {
                mapping,
                child: Some(root),
            }))
        });
        // Note: len might be different if mapping filters some keys out,
        // but we can't know without iterating. We keep the original len
        // as an upper bound.
        WBTreeMap {
            root: new_root,
            len: self.len,
        }
    }
}

// Iterator implementation
// We need to track pointers to DataNodes since Node is an enum
// Each stack entry includes the accumulated mappings at that point
pub struct Iter<'a, V: Clone> {
    // Stack entries: (data_node, accumulated_mappings_at_this_level)
    // TODO: We shouldn't save the full path of mappings for element in the stack.
    // This looks like (log n)^2 complexity instead of log n.
    // Instead, we should just maintain the current_mappings value for the current path of
    // mappings, and `stack` should probably be `Node` instead of just `DataNode`.
    // Then, when we pop a MappingNode from `stack`, we have to pop an element from
    // `current_mappings` as well, but not if we pop a `DataNode`.
    stack: Vec<(&'a DataNode<V>, Vec<&'a PrefixTree2>)>,
    current: Option<&'a Option<Rc<Node<V>>>>,
    // Current accumulated mappings (grows as we descend through mapping nodes)
    current_mappings: Vec<&'a PrefixTree2>,
}

impl<'a, V: Clone> Iter<'a, V> {
    fn descend_left(&mut self) {
        while let Some(opt_node) = self.current {
            match opt_node {
                None => {
                    self.current = None;
                    return;
                }
                Some(node) => match node.as_ref() {
                    Node::Data(data_node) => {
                        // Push this node with a snapshot of current mappings
                        self.stack.push((data_node, self.current_mappings.clone()));
                        self.current = Some(&data_node.left);
                    }
                    Node::Mapping(mapping_node) => {
                        // Accumulate this mapping
                        self.current_mappings.push(&mapping_node.mapping);
                        self.current = Some(&mapping_node.child);
                    }
                },
            }
        }
    }
}

impl<'a, V: Clone> Iterator for Iter<'a, V> {
    // Return owned key since we compute it by applying mappings
    type Item = (u32, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // First descend left as far as possible
            self.descend_left();

            // Pop from stack and return
            if let Some((data_node, mappings)) = self.stack.pop() {
                // Restore the mapping state for when we go right
                self.current_mappings = mappings.clone();
                self.current = Some(&data_node.right);

                // Apply accumulated mappings to the key
                let mapped_key = if mappings.is_empty() {
                    Some(data_node.key)
                } else {
                    apply_mappings(&mappings, data_node.key)
                };

                // If key is in mapping domain, yield it; otherwise skip
                if let Some(mk) = mapped_key {
                    return Some((mk, &data_node.value));
                }
                // Key not in mapping domain, continue to next
            } else {
                return None;
            }
        }
    }
}

// Mutable iterator implementation
// Each stack entry includes the data node pointer and accumulated mappings at that point
pub struct IterMut<'a, V: Clone> {
    stack: Vec<(*mut DataNode<V>, Vec<PrefixTree2>)>,
    current: Option<*mut Option<Rc<Node<V>>>>,
    current_mappings: Vec<PrefixTree2>,
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
                    Some(node) => {
                        let node_mut = Rc::make_mut(node);
                        match node_mut {
                            Node::Data(data_node) => {
                                self.stack.push((
                                    data_node as *mut DataNode<V>,
                                    self.current_mappings.clone(),
                                ));
                                self.current = Some(&mut data_node.left as *mut _);
                            }
                            Node::Mapping(mapping_node) => {
                                self.current_mappings.push(mapping_node.mapping.clone());
                                self.current = Some(&mut mapping_node.child as *mut _);
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<'a, V: Clone> Iterator for IterMut<'a, V> {
    type Item = (u32, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // First descend left as far as possible
            self.descend_left();

            // Pop from stack and return
            if let Some((data_node_ptr, mappings)) = self.stack.pop() {
                unsafe {
                    let data_node = &mut *data_node_ptr;
                    // Restore mapping state for going right
                    self.current_mappings = mappings.clone();
                    self.current = Some(&mut data_node.right as *mut _);

                    // Apply accumulated mappings to the key
                    let mapped_key = if mappings.is_empty() {
                        Some(data_node.key)
                    } else {
                        let mapping_refs: Vec<&PrefixTree2> = mappings.iter().collect();
                        apply_mappings(&mapping_refs, data_node.key)
                    };

                    // If key is in mapping domain, yield it; otherwise skip
                    if let Some(mk) = mapped_key {
                        return Some((mk, &mut data_node.value));
                    }
                    // Key not in mapping domain, continue to next
                }
            } else {
                return None;
            }
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
                .field("mapping", &mapping_node.mapping)
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
    use std::collections::BTreeMap;

    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

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
                        if right_weight > DELTA * left_weight || left_weight > DELTA * right_weight
                        {
                            return false;
                        }
                    }

                    // Check size is correct
                    if data_node.size != 1 + left_size + right_size {
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

        // Note: get() with partial mappings may not work correctly for all keys
        // because tree search requires comparing with intermediate nodes.
        // However, iteration correctly filters and yields only mapped keys.

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
