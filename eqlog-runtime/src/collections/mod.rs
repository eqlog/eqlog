//! Collection types.

// Note: This module is also included in the alloctests crate using #[path] to
// run the tests. See the comment there for an explanation why this is the case.

mod btree;

pub mod btree_map {
    //! An ordered map based on a B-Tree.
    pub use super::btree::map::*;
}

pub mod btree_set {
    //! An ordered set based on a B-Tree.
    #[cfg(not(test))]
    pub use super::btree::set::*;
}

#[doc(no_inline)]
#[cfg(not(test))]
pub use btree_map::BTreeMap;
#[doc(no_inline)]
#[cfg(not(test))]
pub use btree_set::BTreeSet;
