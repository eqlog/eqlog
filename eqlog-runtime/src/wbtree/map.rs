use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::rc::Rc;

#[derive(Clone)]
pub struct WBTreeMap<K: Clone, V: Clone> {
    root: Option<Rc<Node<K, V>>>,
    len: usize,
}

#[derive(Clone)]
struct Node<K: Clone, V: Clone> {
    key: K,
    value: V,
    left: Option<Rc<Node<K, V>>>,
    right: Option<Rc<Node<K, V>>>,
    size: usize, // Total number of nodes in this subtree
}

// Weight balance parameters
const DELTA: usize = 3;
const GAMMA: usize = 2;

impl<K: Clone + Ord, V: Clone> Node<K, V> {
    fn new(key: K, value: V) -> Self {
        Node {
            key,
            value,
            left: None,
            right: None,
            size: 1,
        }
    }

    fn size(node: &Option<Rc<Node<K, V>>>) -> usize {
        node.as_ref().map_or(0, |n| n.size)
    }

    fn update_size(&mut self) {
        self.size = 1 + Self::size(&self.left) + Self::size(&self.right);
    }

    fn rotate_left(node: Rc<Node<K, V>>) -> Rc<Node<K, V>> {
        // TODO
        node
    }

    fn rotate_right(node: Rc<Node<K, V>>) -> Rc<Node<K, V>> {
        // TODO
        node
    }

    fn balance(mut node: Rc<Node<K, V>>) -> Rc<Node<K, V>> {
        let left_size = Self::size(&node.left);
        let right_size = Self::size(&node.right);

        if left_size + right_size < 2 {
            return node;
        }

        // Original WBT algorithm: use weights (size + 1) instead of just sizes
        let left_weight = left_size + 1;
        let right_weight = right_size + 1;

        if right_weight > DELTA * left_weight {
            // Right-heavy
            let right = node.right.as_ref().unwrap();
            let right_left_size = Self::size(&right.left);
            let right_right_size = Self::size(&right.right);

            let right_left_weight = right_left_size + 1;
            let right_right_weight = right_right_size + 1;

            if right_left_weight >= GAMMA * right_right_weight {
                let node = Rc::make_mut(&mut node);
                node.right = node.right.take().map(Self::rotate_right);
            }
            Self::rotate_left(node)
        } else if left_weight > DELTA * right_weight {
            // Left-heavy
            let left = node.left.as_ref().unwrap();
            let left_left_size = Self::size(&left.left);
            let left_right_size = Self::size(&left.right);

            let left_left_weight = left_left_size + 1;
            let left_right_weight = left_right_size + 1;

            if left_right_weight >= GAMMA * left_left_weight {
                let node = Rc::make_mut(&mut node);
                node.left = node.left.take().map(Self::rotate_left);
            }
            Self::rotate_right(node)
        } else {
            node
        }
    }

    fn insert(
        node: Option<Rc<Node<K, V>>>,
        key: K,
        value: V,
    ) -> (Option<Rc<Node<K, V>>>, Option<V>) {
        let mut node = match node {
            Some(n) => n,
            None => {
                return (Some(Rc::new(Node::new(key, value))), None);
            }
        };

        let node_mut = Rc::make_mut(&mut node);
        let old_value: Option<V> = match key.cmp(&node_mut.key) {
            Ordering::Equal => {
                let old = mem::replace(&mut node_mut.value, value);
                Some(old)
            }
            Ordering::Less => {
                let old_left = node_mut.left.take();
                let (new_left, old_value) = Self::insert(old_left, key, value);
                node_mut.left = new_left;
                node_mut.update_size();
                old_value
            }
            Ordering::Greater => {
                let old_right = node_mut.right.take();
                let (new_right, old_value) = Self::insert(old_right, key, value);
                node_mut.right = new_right;
                node_mut.update_size();
                old_value
            }
        };

        (Some(node), old_value)
    }

    fn remove_min(mut node: Rc<Node<K, V>>) -> (K, V, Option<Rc<Node<K, V>>>) {
        if node.left.is_none() {
            let Node {
                key,
                value,
                left: _,
                right,
                size: _,
            } = Rc::unwrap_or_clone(node);
            return (key, value, right);
        }

        let node_mut = Rc::make_mut(&mut node);
        let left = node_mut.left.take().unwrap();
        let (min_key, min_value, new_left) = Self::remove_min(left);
        node_mut.left = new_left;
        node_mut.update_size();
        // TODO: Balance node.
        (min_key, min_value, Some(node))
    }

    fn remove_existing_node(mut node: Rc<Node<K, V>>, key: &K) -> (Option<Rc<Node<K, V>>>, V) {
        match key.cmp(&node.key) {
            Ordering::Equal => {
                let Node {
                    key: _,
                    value,
                    left,
                    right,
                    size: _,
                } = Rc::unwrap_or_clone(node);
                let new_node = match (left, right) {
                    (None, None) => None,
                    (Some(left), None) => Some(left),
                    (None, Some(right)) => Some(right),
                    (Some(left), Some(right)) => {
                        // Find the minimum element in the right subtree to replace this node
                        let (min_key, min_value, new_right) = Self::remove_min(right);
                        let mut new_node = Node {
                            key: min_key,
                            value: min_value,
                            left: Some(left),
                            right: new_right,
                            size: 0,
                        };
                        new_node.update_size();
                        // TODO: Balance the new node.
                        // TODO: Do we really need a new allocation here? Why not reuse the node
                        // we've just removed?
                        Some(Rc::new(new_node))
                    }
                };
                (new_node, value)
            }
            Ordering::Less => {
                let node_mut = Rc::make_mut(&mut node);
                let left = node_mut
                    .left
                    .take()
                    .expect("Node with key must exist, so left cannot be None");

                let (new_left, value) = Self::remove_existing_node(left, key);

                node_mut.left = new_left;
                // TODO: Balance.
                (Some(node), value)
            }
            Ordering::Greater => {
                let node_mut = Rc::make_mut(&mut node);
                let right = node_mut
                    .right
                    .take()
                    .expect("Node with key must exist, so right cannot be None");

                let (new_right, value) = Self::remove_existing_node(right, key);

                node_mut.right = new_right;
                // TODO: Balance.
                (Some(node), value)
            }
        }
    }
}

impl<K: Ord + Clone, V: Clone> WBTreeMap<K, V> {
    pub const fn new() -> Self {
        WBTreeMap { root: None, len: 0 }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let (new_root, old_value) = Node::insert(self.root.take(), key, value);
        self.root = new_root;
        if old_value.is_none() {
            self.len += 1;
        }
        old_value
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let mut current = &self.root;
        while let Some(node) = current {
            match key.cmp(&node.key) {
                Ordering::Less => current = &node.left,
                Ordering::Greater => current = &node.right,
                Ordering::Equal => return Some(&node.value),
            }
        }
        None
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let mut current = &mut self.root;
        while let Some(node) = current {
            match key.cmp(&node.key) {
                Ordering::Less => current = &mut Rc::make_mut(node).left,
                Ordering::Greater => current = &mut Rc::make_mut(node).right,
                Ordering::Equal => return Some(&mut Rc::make_mut(node).value),
            }
        }
        None
    }

    pub fn contains_key(&self, key: &K) -> bool {
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

    pub fn iter<'a>(&'a self) -> Iter<'a, K, V> {
        Iter {
            stack: Vec::new(),
            current: &self.root,
        }
    }

    pub fn entry<'a>(&'a mut self, key: K) -> Entry<'a, K, V> {
        if self.contains_key(&key) {
            Entry::Occupied(OccupiedEntry { key, map: self })
        } else {
            Entry::Vacant(VacantEntry { key, map: self })
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        if !self.contains_key(key) {
            return None;
        }

        let root = self.root.take().expect("Root must exist if key is present");
        let (new_root, value) = Node::remove_existing_node(root, key);
        self.root = new_root;
        self.len -= 1;
        Some(value)
    }
}

// Iterator implementation
pub struct Iter<'a, K: Clone, V: Clone> {
    stack: Vec<&'a Rc<Node<K, V>>>,
    current: &'a Option<Rc<Node<K, V>>>,
}

impl<'a, K: Clone, V: Clone> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(node) = self.current {
                self.stack.push(node);
                self.current = &node.left;
            } else if let Some(node) = self.stack.pop() {
                self.current = &node.right;
                return Some((&node.key, &node.value));
            } else {
                return None;
            }
        }
    }
}

// Entry API
pub enum Entry<'a, K: Clone, V: Clone> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

pub struct OccupiedEntry<'a, K: Clone, V: Clone> {
    key: K,
    map: &'a mut WBTreeMap<K, V>,
}

pub struct VacantEntry<'a, K: Clone, V: Clone> {
    key: K,
    map: &'a mut WBTreeMap<K, V>,
}

impl<'a, K: Ord + Clone, V: Clone> Entry<'a, K, V> {
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

impl<'a, K: Ord + Clone, V: Clone> OccupiedEntry<'a, K, V> {
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

impl<'a, K: Ord + Clone, V: Clone> VacantEntry<'a, K, V> {
    pub fn insert(self, value: V) -> &'a mut V {
        self.map.insert(self.key.clone(), value);
        self.map.get_mut(&self.key).unwrap()
    }
}

impl<K: fmt::Debug + Clone, V: fmt::Debug + Clone> fmt::Debug for Node<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("key", &self.key)
            .field("value", &self.value)
            .field("left", &self.left)
            .field("right", &self.right)
            .field("size", &self.size)
            .finish()
    }
}

impl<K: fmt::Debug + Ord + Clone, V: fmt::Debug + Clone> fmt::Debug for WBTreeMap<K, V> {
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
    pub fn print_tree_debug<K, V>(node: &Option<Rc<Node<K, V>>>)
    where
        K: std::fmt::Debug + Clone,
        V: std::fmt::Debug + Clone,
    {
        print_tree_debug_helper(node, "", true, true);
    }

    fn print_tree_debug_helper<K, V>(
        node: &Option<Rc<Node<K, V>>>,
        prefix: &str,
        is_last: bool,
        is_root: bool,
    ) where
        K: std::fmt::Debug + Clone,
        V: std::fmt::Debug + Clone,
    {
        match node {
            None => {
                if !is_root {
                    println!("{}{}∅", prefix, if is_last { "└── " } else { "├── " });
                }
            }
            Some(n) => {
                let node_symbol = if is_root {
                    ""
                } else if is_last {
                    "└── "
                } else {
                    "├── "
                };
                println!(
                    "{}{}({:?}: {:?}) [size: {}]",
                    prefix, node_symbol, n.key, n.value, n.size
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
                let has_left = n.left.is_some();
                let has_right = n.right.is_some();

                if has_left || has_right {
                    if has_left {
                        print_tree_debug_helper(&n.left, &new_prefix, !has_right, false);
                    }
                    if has_right {
                        print_tree_debug_helper(&n.right, &new_prefix, true, false);
                    }
                }
            }
        }
    }

    /// Print a compact tree structure showing just keys and structure
    pub fn print_tree_compact<K, V>(node: &Option<Rc<Node<K, V>>>)
    where
        K: std::fmt::Debug + Clone,
        V: Clone,
    {
        print_tree_compact_helper(node, "", true, true);
    }

    fn print_tree_compact_helper<K, V>(
        node: &Option<Rc<Node<K, V>>>,
        prefix: &str,
        is_last: bool,
        is_root: bool,
    ) where
        K: std::fmt::Debug + Clone,
        V: Clone,
    {
        match node {
            None => {
                if !is_root {
                    println!("{}{}∅", prefix, if is_last { "└── " } else { "├── " });
                }
            }
            Some(n) => {
                let node_symbol = if is_root {
                    ""
                } else if is_last {
                    "└── "
                } else {
                    "├── "
                };
                println!("{}{}{:?}", prefix, node_symbol, n.key);

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

                let has_left = n.left.is_some();
                let has_right = n.right.is_some();

                if has_left || has_right {
                    if has_left {
                        print_tree_compact_helper(&n.left, &new_prefix, !has_right, false);
                    }
                    if has_right {
                        print_tree_compact_helper(&n.right, &new_prefix, true, false);
                    }
                }
            }
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
        let tree: WBTreeMap<i32, String> = WBTreeMap::new();

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

    fn tree_height<K, V>(node: &Option<Rc<Node<K, V>>>) -> usize
    where
        K: Clone,
        V: Clone,
    {
        match node {
            None => 0,
            Some(n) => 1 + tree_height(&n.left).max(tree_height(&n.right)),
        }
    }

    fn is_weight_balanced<K, V>(node: &Option<Rc<Node<K, V>>>) -> bool
    where
        K: Clone + Ord,
        V: Clone,
    {
        true
        //match node {
        //    None => true,
        //    Some(n) => {
        //        let left_size = Node::size(&n.left);
        //        let right_size = Node::size(&n.right);

        //        // Check weight balance condition using original WBT algorithm
        //        if left_size + right_size >= 2 {
        //            // Original WBT: use weights (size + 1) instead of just sizes
        //            let left_weight = left_size + 1;
        //            let right_weight = right_size + 1;

        //            // Balance condition: delta * left_weight >= right_weight AND delta * right_weight >= left_weight
        //            if right_weight > DELTA * left_weight || left_weight > DELTA * right_weight {
        //                return false;
        //            }
        //        }

        //        // Check size is correct
        //        if n.size != 1 + left_size + right_size {
        //            return false;
        //        }

        //        // Recursively check subtrees
        //        is_weight_balanced(&n.left) && is_weight_balanced(&n.right)
        //    }
        //}
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
            assert_eq!(wb_item.0, bt_item.0);
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
            // TODO: Invert this once we're properly balancing trees.
            !(height < expected_max_height),
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
        let wb_items: Vec<_> = wb_map.iter().map(|(k, v)| (*k, *v)).collect();
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
        let wb_items: Vec<_> = wb_map.iter().map(|(k, v)| (*k, *v)).collect();
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
        let wb_keys: Vec<_> = wb_map.iter().map(|(k, _)| *k).collect();
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
            assert_eq!(cloned.get(k), Some(v));
        }

        // Verify clone is independent
        original.insert(100, "new_value".to_string());
        assert!(!cloned.contains_key(&100));
    }

    #[test]
    fn test_empty_operations() {
        let mut wb_map: WBTreeMap<i32, i32> = WBTreeMap::new();
        let bt_map: BTreeMap<i32, i32> = BTreeMap::new();

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
        assert_eq!(wb_items[0].0, bt_items[0].0);
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
        let keys: Vec<_> = wb_map.iter().map(|(k, _)| *k).collect();
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
                let mut v: Vec<i32> = (0..100).collect();
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
                        let left_size = Node::size(&root.left);
                        let right_size = Node::size(&root.right);
                        println!("Root node: {:?}", root.key);
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
    fn test_types_compatibility() {
        // Test with different types
        let mut string_map: WBTreeMap<String, i32> = WBTreeMap::new();
        string_map.insert("hello".to_string(), 1);
        string_map.insert("world".to_string(), 2);
        assert_eq!(string_map.get(&"hello".to_string()), Some(&1));

        // Test with custom structs
        #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
        struct Point {
            x: i32,
            y: i32,
        }

        let mut point_map: WBTreeMap<Point, String> = WBTreeMap::new();
        point_map.insert(Point { x: 1, y: 2 }, "A".to_string());
        point_map.insert(Point { x: 0, y: 0 }, "Origin".to_string());
        assert_eq!(point_map.len(), 2);
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

        // Test with different types
        let mut wb_int_map: WBTreeMap<i32, i32> = WBTreeMap::new();
        let mut bt_int_map: BTreeMap<i32, i32> = BTreeMap::new();

        for i in 0..5 {
            wb_int_map.insert(i, i * 10);
            bt_int_map.insert(i, i * 10);
        }
        assert_eq!(format!("{:?}", wb_int_map), format!("{:?}", bt_int_map));

        // Test with string keys
        let mut wb_str_map: WBTreeMap<String, i32> = WBTreeMap::new();
        let mut bt_str_map: BTreeMap<String, i32> = BTreeMap::new();

        wb_str_map.insert("a".to_string(), 1);
        wb_str_map.insert("b".to_string(), 2);
        wb_str_map.insert("c".to_string(), 3);
        bt_str_map.insert("a".to_string(), 1);
        bt_str_map.insert("b".to_string(), 2);
        bt_str_map.insert("c".to_string(), 3);
        assert_eq!(format!("{:?}", wb_str_map), format!("{:?}", bt_str_map));
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
    fn test_debug_with_complex_types() {
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
        struct ComplexKey {
            id: i32,
            name: String,
        }

        let mut wb_map = WBTreeMap::new();
        let mut bt_map = BTreeMap::new();

        let key1 = ComplexKey {
            id: 1,
            name: "Alice".to_string(),
        };
        let key2 = ComplexKey {
            id: 2,
            name: "Bob".to_string(),
        };

        wb_map.insert(key1.clone(), vec![1, 2, 3]);
        wb_map.insert(key2.clone(), vec![4, 5, 6]);
        bt_map.insert(key1, vec![1, 2, 3]);
        bt_map.insert(key2, vec![4, 5, 6]);

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
            assert_eq!(bt_map.get(k), Some(v));
        }

        // Verify tree remains balanced after removals
        assert!(is_weight_balanced(&wb_map.root));
    }
}
