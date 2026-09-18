//! Runtime signatures, structures, and conversions to generated models.
//!
//! Create a [`DynamicModel`] from a [`Signature`], or use [`CompiledModel`] to
//! exchange data with generated Rust models. Dynamic structures do not run rules.
//!
//! ```
//! use std::sync::Arc;
//! use eqlog_runtime::dynamic::{
//!     DynamicModel, Relation, RelationId, RelationKind, Signature, Sort, SortId,
//!     SortKind,
//! };
//!
//! let el = SortId(0);
//! let edge = RelationId(0);
//! let signature = Signature::new(
//!     vec![Sort { name: "El".into(), kind: SortKind::Plain, parents: vec![] }],
//!     vec![Relation {
//!         name: "edge".into(), kind: RelationKind::Predicate,
//!         arity: vec![el, el], parents: vec![],
//!     }],
//! )?;
//! let mut model = DynamicModel::new(Arc::new(signature));
//! let x = model.new_element(el, &[])?;
//! let y = model.new_element(el, &[])?;
//! model.insert(edge, &[x, y])?;
//! model.equate(x, y)?;
//! assert!(model.contains(edge, &[x, x])?);
//! assert_eq!(model.elements(el)?.count(), 1);
//! assert_eq!(model.handles(el)?.count(), 2);
//! # Ok::<(), eqlog_runtime::dynamic::Error>(())
//! ```

mod model;
mod signature;
mod table;

pub use model::DynamicModel;
pub use signature::{
    FunctionKind, Relation, RelationId, RelationKind, Signature, Sort, SortId, SortKind,
};

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

/// An element handle, local to one structure and its signature.
///
/// Equal numeric IDs in different structures have no implied correspondence.
/// Use [`ElementMap`] when transferring handles through a conversion.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Element {
    pub sort: SortId,
    pub index: u32,
}

/// Maps source handles to target handles, including noncanonical aliases.
///
/// Compiled handles use the sort ID in the generated dynamic signature and the
/// integer wrapped by their generated Rust type. Target handles may be shared
/// when source elements are equal. Numeric IDs need not survive conversion.
pub type ElementMap = BTreeMap<Element, Element>;

/// Implemented by generated models to transfer data without running rules.
pub trait CompiledModel: Sized {
    /// Returns the shared signature, independent of evaluation mode.
    ///
    /// Symbol names include enclosing models, for example `World::Inner::Item`.
    /// Rules are not part of the signature.
    fn dynamic_signature() -> Arc<Signature>;

    /// Exports the current facts and a map from compiled to dynamic handles.
    ///
    /// Equal elements share a target handle, including aliases retained by the
    /// caller. Inherited facts are included as currently represented; pending
    /// morphism propagation and functionality are not evaluated. The source is
    /// unchanged. See [`ElementMap`] for encoding compiled handles.
    fn to_dynamic(&self) -> (DynamicModel, ElementMap);

    /// Imports data and returns a map from dynamic to compiled handles.
    ///
    /// Equal elements share a target handle. All imported facts become explicit,
    /// and evaluation progress is reset for subsequent evaluation. Import does not
    /// establish theory axioms or guarantee that closure repairs unsatisfied
    /// constraints. An enum element without a constructor still has no case.
    ///
    /// Returns [`Error::SignatureMismatch`] if sort or relation descriptors differ
    /// from [`Self::dynamic_signature`], including their order and names.
    fn from_dynamic(model: &DynamicModel) -> Result<(Self, ElementMap), Error>;
}

/// Invalid descriptors, handles, or mutations. An error leaves model data unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// Descriptors violate the structural requirements of [`Signature::new`].
    InvalidSignature(String),
    /// The sort ID is outside this signature.
    UnknownSort(SortId),
    /// The relation ID is outside this signature.
    UnknownRelation(RelationId),
    /// The sort exists, but the element index has not been allocated.
    UnknownElement(Element),
    /// An argument has the wrong carrier sort.
    SortMismatch { expected: SortId, actual: SortId },
    /// A tuple or parent chain has the wrong length.
    ArityMismatch { expected: usize, actual: usize },
    /// An element would acquire a different parent chain, modulo equality.
    ParentMismatch,
    /// Import requires the same ordered signature as the generated model.
    SignatureMismatch,
    /// Allocation would exceed the union-find's supported element count.
    ElementLimit,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSignature(message) => write!(f, "invalid signature: {message}"),
            Self::UnknownSort(sort) => write!(f, "unknown sort {sort:?}"),
            Self::UnknownRelation(relation) => write!(f, "unknown relation {relation:?}"),
            Self::UnknownElement(element) => write!(f, "unknown element {element:?}"),
            Self::SortMismatch { expected, actual } => {
                write!(f, "expected sort {expected:?}, got {actual:?}")
            }
            Self::ArityMismatch { expected, actual } => {
                write!(f, "expected {expected} arguments, got {actual}")
            }
            Self::ParentMismatch => write!(f, "element has a different parent chain"),
            Self::SignatureMismatch => write!(f, "dynamic and compiled signatures differ"),
            Self::ElementLimit => write!(f, "element ID space exhausted"),
        }
    }
}

impl std::error::Error for Error {}
