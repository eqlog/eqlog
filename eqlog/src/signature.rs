use std::vec::Vec;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct SortId(pub usize);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct RelationId(pub usize);

// Some default values, fixed but chosen randomly
impl Default for SortId {
    fn default() -> Self {
        SortId(2201843232216218232)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Signature {
    sort_number: usize,
    relation_arities: Vec<Vec<SortId>>,
    // relations are identified by their index in `relation_arities`
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            sort_number: 0,
            relation_arities: vec![],
        }
    }
    pub fn from_sorts_arities(sort_number: usize, arities: Vec<Vec<SortId>>) -> Signature {
        let mut sig = Signature::new();
        for _ in 0 .. sort_number {
            sig.add_sort();
        }
        for arity in arities.into_iter() {
            sig.add_relation(arity);
        }
        sig
    }
    pub fn add_sort(&mut self) -> SortId {
        let s = SortId(self.sort_number);
        self.sort_number += 1;
        s
    }
    pub fn has_sort(&self, s: SortId) -> bool {
        let SortId(s0) = s;
        s0 < self.sort_number
    }
    pub fn sort_number(&self) -> usize {
        self.sort_number
    }
    pub fn add_relation(&mut self, arity: Vec<SortId>) -> RelationId {
        assert!(arity.iter().all(|s| self.has_sort(*s)));
        let r = RelationId(self.relation_arities.len());
        self.relation_arities.push(arity);
        r
    }
    pub fn iter_arities<'a>(&'a self) -> impl Iterator<Item = &'a [SortId]> {
        self.relation_arities.iter().map(|arity| arity.as_slice())
    }
    pub fn get_arity<'a>(&'a self, r: RelationId) -> Option<&'a [SortId]> {
        let RelationId(r0) = r;
        self.relation_arities.get(r0).map(|arity| arity.as_slice())
    }
    pub fn relation_number(&self) -> usize {
        self.relation_arities.len()
    }
}
