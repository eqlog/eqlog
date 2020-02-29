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

pub struct Signature {
    pub sort_number: usize,
    pub relation_arities: Vec<Vec<SortId>>,
    // relations are identified by their index in `relation_arities`
}

