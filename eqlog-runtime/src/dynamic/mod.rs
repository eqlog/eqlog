//! Data shared by compiled models and future interpreted evaluators.
//!
//! A dynamic model is a structure over a signature, not necessarily a model of
//! any theory's rules. In particular, function graphs may have multiple results.
//! Mutations enforce carrier sorts and unique parent chains, but do not perform
//! inference, check dependent relation arguments, or propagate morphisms.

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

/// Conversion preserves represented facts, not evaluation progress or provenance.
///
/// Neither direction runs rules. Export includes currently represented inherited
/// facts, but does not recompute inheritance or repair pending functionality.
/// Import makes all facts explicit and leaves the compiled structure ready for
/// a subsequent `close()`. It accepts only the generated signature, including
/// its sort and relation ordering; rules are not part of signature compatibility.
pub trait CompiledModel: Sized {
    fn dynamic_signature() -> Arc<Signature>;
    fn to_dynamic(&self) -> (DynamicModel, ElementMap);
    fn from_dynamic(model: &DynamicModel) -> Result<(Self, ElementMap), Error>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidSignature(String),
    UnknownSort(SortId),
    UnknownRelation(RelationId),
    UnknownElement(Element),
    SortMismatch { expected: SortId, actual: SortId },
    ArityMismatch { expected: usize, actual: usize },
    ParentMismatch,
    SignatureMismatch,
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
