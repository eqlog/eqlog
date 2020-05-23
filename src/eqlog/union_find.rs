use super::element::Element;

use std::vec::Vec;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UnionFind(Vec<Element>);

impl UnionFind {
    pub fn new() -> UnionFind {
        UnionFind(Vec::new())
    }
    pub fn len(&self) -> usize {
        let UnionFind(vec) = self;
        vec.len()
    }

    fn get_parent(&self, el: Element) -> Element {
        let Element(el_) = el;
        let UnionFind(vec) = self;
        vec[el_ as usize]
    }
    fn set_parent(&mut self, el: Element, new_parent: Element) {
        let Element(el_) = el;
        let UnionFind(vec) = self;
        vec[el_ as usize] = new_parent;
    }

    pub fn find(&mut self, a: Element) -> Element {
        let Element(a_) = a;
        assert!((a_ as usize) < self.len());

        let mut el: Element = a;
        let mut parent = self.get_parent(el);
        let mut grandparent = self.get_parent(parent);

        while el != parent {
            self.set_parent(el, grandparent);
            el = parent;
            parent = grandparent;
            grandparent = self.get_parent(parent);
        }

        el
    }

    pub fn find_const(&self, a: Element) -> Element {
        let UnionFind(vec) = self;
        let Element(a_) = a;
        assert!((a_ as usize) < vec.len());

        let mut el = a;
        let mut parent = self.get_parent(el);

        while el != parent {
            el = parent;
            parent = self.get_parent(parent);
        }

        el
    }

    pub fn merge_into(&mut self, a: Element, b: Element) -> Element {
        let a_repr = self.find(a); 
        let b_repr = self.find(b);

        self.set_parent(a_repr, b_repr);
        b_repr
    }

    pub fn new_element(&mut self) -> Element {
        let UnionFind(vec) = self;
        let new_id = vec.len();
        assert!(new_id < (u32::max_value as usize));

        let new_el = Element(new_id as u32);
        vec.push(new_el);
        new_el
    }
}

#[test]
fn test_no_merges() {
    let mut uf = UnionFind::new();
    for i in 0 .. 5 {
        let Element(el) = uf.new_element();
        assert_eq!(el, i);
        assert_eq!(Element(el), uf.find(Element(el)));
    }
    for i in 0 .. 5 {
        assert_eq!(Element(i), uf.find(Element(i)));
    }
}

#[test]
fn test_merge_chain() {
    let mut uf = UnionFind::new();
    for _ in 0 .. 5 {
        uf.new_element();
    }
    uf.merge_into(Element(3), Element(2));
    uf.merge_into(Element(2), Element(1));
    assert_eq!(uf.find(Element(3)), Element(1));
    assert_eq!(uf.find(Element(2)), Element(1));
    assert_eq!(uf.find(Element(1)), Element(1));
    assert_eq!(uf.find(Element(0)), Element(0));
}

#[test]
fn test_merge_chain_find_const() {
    let mut uf = UnionFind::new();
    for _ in 0 .. 5 {
        uf.new_element();
    }
    uf.merge_into(Element(3), Element(2));
    uf.merge_into(Element(2), Element(1));
    assert_eq!(uf.find_const(Element(3)), Element(1));
    assert_eq!(uf.find_const(Element(2)), Element(1));
    assert_eq!(uf.find_const(Element(1)), Element(1));
    assert_eq!(uf.find_const(Element(0)), Element(0));
}

#[test]
fn test_merge_branching() {
    let mut uf = UnionFind::new();
    for _ in 0 .. 5 {
        uf.new_element();
    }
    uf.merge_into(Element(3), Element(2));
    uf.merge_into(Element(1), Element(0));
    uf.merge_into(Element(3), Element(1));
    assert_eq!(uf.find(Element(3)), Element(0));
    assert_eq!(uf.find(Element(2)), Element(0));
    assert_eq!(uf.find(Element(1)), Element(0));
    assert_eq!(uf.find(Element(0)), Element(0));
}

#[test]
fn test_merge_branching_find_const() {
    let mut uf = UnionFind::new();
    for _ in 0 .. 5 {
        uf.new_element();
    }
    uf.merge_into(Element(3), Element(2));
    uf.merge_into(Element(1), Element(0));
    uf.merge_into(Element(3), Element(1));
    assert_eq!(uf.find_const(Element(3)), Element(0));
    assert_eq!(uf.find_const(Element(2)), Element(0));
    assert_eq!(uf.find_const(Element(1)), Element(0));
    assert_eq!(uf.find_const(Element(0)), Element(0));
}
