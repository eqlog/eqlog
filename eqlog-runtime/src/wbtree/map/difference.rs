use std::cmp::Ordering;
use std::rc::Rc;

use super::{apply_mappings, Node, WBTreeMap};
use crate::PrefixTree2;

// Bounds avoid allocating split trees while preserving the left traversal order.
pub(super) fn all<'a, V: Clone>(
    left: Option<&'a Rc<Node<V>>>,
    mut right: Option<&'a Rc<Node<V>>>,
    lower: Option<u32>,
    upper: Option<u32>,
    visit: &mut impl FnMut(u32, &'a V, Option<&'a V>) -> bool,
) -> bool {
    let Some(left) = left else {
        return true;
    };
    while let Some(node) = right {
        let data = match node.as_ref() {
            Node::Data(data) => data,
            Node::Mapping(_) => unreachable!("mapped roots use the difference cursor"),
        };
        if lower.is_some_and(|lower| data.key <= lower) {
            right = data.right.as_ref();
        } else if upper.is_some_and(|upper| data.key >= upper) {
            right = data.left.as_ref();
        } else {
            break;
        }
    }
    let data = match left.as_ref() {
        Node::Data(data) => data,
        Node::Mapping(_) => unreachable!("mapped roots use the difference cursor"),
    };
    let mut candidate = right;
    let mut value = None;
    while let Some(node) = candidate {
        // Rotations can move a shared subtree below the bounded right root.
        if Rc::ptr_eq(left, node) {
            return true;
        }
        let other = match node.as_ref() {
            Node::Data(other) => other,
            Node::Mapping(_) => unreachable!("mapped roots use the difference cursor"),
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
    all(data.left.as_ref(), right, lower, Some(data.key), visit)
        && visit(data.key, &data.value, value)
        && all(data.right.as_ref(), right, Some(data.key), upper, visit)
}

type Mappings<'a> = Option<Rc<Vec<&'a PrefixTree2>>>;

enum Pending<'a, V: Clone> {
    Tree(&'a Rc<Node<V>>, Mappings<'a>),
    Entry(u32, &'a V),
}

struct Cursor<'a, V: Clone> {
    pending: Vec<Pending<'a, V>>,
    // Singleton suffixes need no allocated pending stack.
    current: Option<Pending<'a, V>>,
    #[cfg(test)]
    opened: usize,
}

impl<'a, V: Clone> Cursor<'a, V> {
    fn new(root: Option<&'a Rc<Node<V>>>) -> Self {
        Self {
            pending: Vec::new(),
            current: root.map(|root| Pending::Tree(root, None)),
            #[cfg(test)]
            opened: 0,
        }
    }

    fn peek(&self) -> Option<&Pending<'a, V>> {
        self.current.as_ref()
    }

    fn pop(&mut self) -> Option<Pending<'a, V>> {
        std::mem::replace(&mut self.current, self.pending.pop())
    }

    fn push(&mut self, pending: Pending<'a, V>) {
        if let Some(previous) = self.current.replace(pending) {
            self.pending.push(previous);
        }
    }

    fn normalize(&mut self) {
        loop {
            let mapped = match self.peek() {
                Some(Pending::Tree(node, _)) => match node.as_ref() {
                    Node::Mapping(_) => true,
                    Node::Data(_) => false,
                },
                Some(Pending::Entry(_, _)) | None => false,
            };
            if !mapped {
                return;
            }
            match self.current.take().unwrap() {
                Pending::Tree(node, mut mappings) => match node.as_ref() {
                    Node::Mapping(mapping) => {
                        if let Some(child) = &mapping.child {
                            Rc::make_mut(mappings.get_or_insert_with(|| Rc::new(Vec::new())))
                                .push(&mapping.mapping);
                            self.push(Pending::Tree(child, mappings));
                        }
                    }
                    Node::Data(_) => unreachable!("only mapping roots are normalized"),
                },
                Pending::Entry(_, _) => unreachable!("only trees carry mappings"),
            }
            if self.current.is_none() {
                self.current = self.pending.pop();
            }
        }
    }

    fn expand(&mut self) {
        match self.current.take().expect("a tree must be pending") {
            Pending::Tree(node, mappings) => match node.as_ref() {
                Node::Data(data) => {
                    #[cfg(test)]
                    {
                        self.opened += 1;
                    }
                    if let Some(right) = &data.right {
                        self.push(Pending::Tree(right, mappings.clone()));
                    }
                    let mappings_slice = mappings.as_deref().map_or(&[][..], Vec::as_slice);
                    if let Some(key) = apply_mappings(mappings_slice, data.key) {
                        self.push(Pending::Entry(key, &data.value));
                    }
                    if let Some(left) = &data.left {
                        self.push(Pending::Tree(left, mappings));
                    }
                }
                Node::Mapping(_) => unreachable!("normalize before expanding"),
            },
            Pending::Entry(_, _) => unreachable!("only trees can be expanded"),
        }
        if self.current.is_none() {
            self.current = self.pending.pop();
        }
    }
}

fn same_mappings(left: &Mappings<'_>, right: &Mappings<'_>) -> bool {
    let left = left.as_deref().map_or(&[][..], Vec::as_slice);
    let right = right.as_deref().map_or(&[][..], Vec::as_slice);
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.map.shares_root(&right.map))
}

fn size<V: Clone>(node: &Node<V>) -> usize {
    match node {
        Node::Data(data) => data.size,
        Node::Mapping(_) => unreachable!("normalize before comparing sizes"),
    }
}

/// Keys unique to the left, or matching keys whose values still need comparison.
/// Pointer-identical subtrees are skipped only under identical mappings.
pub struct Difference<'a, V: Clone> {
    left: Cursor<'a, V>,
    right: Cursor<'a, V>,
}

impl<'a, V: Clone> Difference<'a, V> {
    pub(super) fn new(left: &'a WBTreeMap<V>, right: &'a WBTreeMap<V>) -> Self {
        if left.root.is_none() || left.shares_root(right) {
            return Self {
                left: Cursor::new(None),
                right: Cursor::new(None),
            };
        }
        Self {
            left: Cursor::new(left.root.as_ref()),
            right: Cursor::new(right.root.as_ref()),
        }
    }
}

impl<'a, V: Clone> Iterator for Difference<'a, V> {
    type Item = (u32, &'a V, Option<&'a V>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            self.left.normalize();
            self.right.normalize();
            let left = self.left.peek()?;
            match (left, self.right.peek()) {
                (Pending::Tree(left, lm), Some(Pending::Tree(right, rm))) => {
                    if Rc::ptr_eq(left, right) && same_mappings(lm, rm) {
                        self.left.pop();
                        self.right.pop();
                    } else if size(left) >= size(right) {
                        // Keeping the smaller frontier intact exposes shared subtrees
                        // even when rotations changed their depth in the other tree.
                        self.left.expand();
                    } else {
                        self.right.expand();
                    }
                }
                (Pending::Tree(_, _), Some(Pending::Entry(_, _)) | None) => {
                    self.left.expand();
                }
                (Pending::Entry(_, _), Some(Pending::Tree(_, _))) => {
                    self.right.expand();
                }
                (Pending::Entry(key, value), None) => {
                    let result = (*key, *value, None);
                    self.left.pop();
                    return Some(result);
                }
                (Pending::Entry(lk, lv), Some(Pending::Entry(rk, rv))) => match lk.cmp(rk) {
                    Ordering::Less => {
                        let result = (*lk, *lv, None);
                        self.left.pop();
                        return Some(result);
                    }
                    Ordering::Equal => {
                        let result = (*lk, *lv, Some(*rv));
                        self.left.pop();
                        self.right.pop();
                        return Some(result);
                    }
                    Ordering::Greater => {
                        self.right.pop();
                    }
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use super::Difference;
    use crate::wbtree::map::WBTreeMap;
    use crate::PrefixTree2;

    #[test]
    fn sparse_edits_skip_shared_subtrees_despite_rotations() {
        let mut original = WBTreeMap::new();
        for key in 0..65536 {
            original.insert(key, ());
        }
        for key in [0, 17, 32768, 65535, 65536] {
            let mut edited = original.clone();
            edited.remove(&key);
            edited.insert(65537, ());
            for (left, right) in [(&original, &edited), (&edited, &original)] {
                let mut diff = Difference::new(left, right);
                let actual: Vec<_> = diff
                    .by_ref()
                    .filter_map(|(k, _, r)| r.is_none().then_some(k))
                    .collect();
                let expected: Vec<_> = left
                    .iter()
                    .filter_map(|(k, _)| right.get(&k).is_none().then_some(k))
                    .collect();
                assert_eq!(actual, expected);
                assert!(
                    diff.left.opened + diff.right.opened < 200,
                    "a sparse edit scanned the tree"
                );
            }
        }
        let mut diff = Difference::new(&original, &original);
        assert_eq!(diff.next(), None);
        assert_eq!(diff.left.opened + diff.right.opened, 0);
    }

    struct CountClones(Rc<Cell<usize>>);

    impl Clone for CountClones {
        fn clone(&self) -> Self {
            self.0.set(self.0.get() + 1);
            Self(self.0.clone())
        }
    }

    #[test]
    fn mapped_comparisons_neither_materialize_nor_cancel_different_mappings() {
        let clones = Rc::new(Cell::new(0));
        let mut base = WBTreeMap::new();
        let mut first_map = PrefixTree2::new();
        let mut second_map = PrefixTree2::new();
        let mut outer_map = PrefixTree2::new();
        for i in 0..100 {
            base.insert(i, CountClones(clones.clone()));
            if i % 3 != 0 {
                first_map.insert([i, i * 2]);
            }
            second_map.insert([i, i * 3]);
            outer_map.insert([i * 2, i * 4]);
        }
        let first = base.mapped(first_map.clone());
        let same = base.mapped(first_map);
        let second = base.mapped(second_map);
        let nested = first.mapped(outer_map);
        clones.set(0);
        for (left, right) in [
            (&first, &same),
            (&first, &second),
            (&second, &first),
            (&nested, &second),
            (&base, &nested),
        ] {
            let actual: Vec<_> = left
                .difference_entries(right)
                .filter_map(|(k, _, r)| r.is_none().then_some(k))
                .collect();
            let expected: Vec<_> = left
                .iter()
                .filter_map(|(k, _)| right.get(&k).is_none().then_some(k))
                .collect();
            assert_eq!(actual, expected);
        }
        assert_eq!(clones.get(), 0);
        let mut diff = Difference::new(&first, &same);
        assert!(diff.next().is_none());
        assert_eq!(diff.left.opened + diff.right.opened, 0);
    }
}
