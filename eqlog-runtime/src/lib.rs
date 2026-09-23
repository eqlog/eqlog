//! Runtime signatures, structures, and conversions to generated models.
//!
//! Create a [`Model`] from a [`Signature`], or use [`CompiledModel`] to
//! exchange data with generated Rust models. Dynamic structures do not run rules.
//!
//! ```
//! use std::sync::Arc;
//! use eqlog_runtime::{
//!     Model, Relation, RelationId, RelationKind, Signature, Type, TypeId,
//!     TypeKind,
//! };
//!
//! let el = TypeId(0);
//! let edge = RelationId(0);
//! let signature = Signature::new(
//!     vec![Type { name: "El".into(), kind: TypeKind::Plain, parents: vec![] }],
//!     vec![Relation {
//!         name: "edge".into(), kind: RelationKind::Predicate,
//!         arity: vec![el, el], parents: vec![],
//!     }],
//! )?;
//! let mut model = Model::new(Arc::new(signature));
//! let x = model.new_element(el, &[])?;
//! let y = model.new_element(el, &[])?;
//! model.insert(edge, &[x, y])?;
//! model.equate(&[], x, y)?;
//! assert_eq!(model.tuples(edge)?.collect::<Vec<_>>(), vec![vec![x, y]]);
//! assert_eq!(model.root(y)?, x);
//! assert_eq!(model.elements(el)?.count(), 1);
//! # Ok::<(), eqlog_runtime::Error>(())
//! ```

// This is here to support our cursed way of finding the eqlog runtime rlib file in the cargo
// target directory. Cargo does not let build scripts know where it put rlib files of dependencies.
// The build script in a crate that compiles eqlog modules must know where the rlib is though (at
// least for component builds) so that it can pass the eqlog runtime rlib path as --extern
// parameter to rustc when compiling eqlog modules.
//
// As a workaround, the build script scans the target directory for files that look like they might
// be the eqlog runtime rlib file. I haven't found a way to narrow this down to a single file
// though; there are several libeqlog_runtime-<hash>.rlib files. I think they might be there for
// macros and for the build script of the runtime crate. We're only interested in the actual
// runtime crate from this crate though. To find this file, the build script scans the .rlib file
// for the value of the TAG variable below.
//
// We also can't use a fixed tag value here because I think eqlog-runtime is built twice depending
// on whether it's a dependency for the build script or the crate itself. To single it down, we use
// the OUT_DIR variable as part of the tag. The OUT_DIR variable is also available in the buidl
// script of eqlog-runtime, which emits its value as link metadata value, see the cargo "link"
// feature. This metadata value is then available in the build scripts of crates that dependend on
// eqlog-runtime. The eqlog compiler crate can thus read it and scan potential eqlog-runtime rlib
// for whether they contain this tag.
#[used]
static TAG: &'static str = concat!("EQLOG_RUNTIME_TAG_", env!("OUT_DIR"));

mod data;
mod model;
mod signature;
mod table;

#[doc(hidden)]
pub mod __private;

pub use model::Model;
pub use signature::{
    FunctionKind, Relation, RelationId, RelationKind, Signature, Type, TypeId, TypeKind,
};

use std::fmt;
use std::sync::Arc;

/// An element handle within one structure.
///
/// The same ID can refer to different elements in different structures.
/// Conversions preserve the type ID and numeric index, including aliases.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Element {
    pub type_: TypeId,
    pub index: u32,
}

/// Implemented by generated models to transfer data without running rules.
pub trait CompiledModel: Sized {
    /// Returns the shared signature, independent of evaluation mode.
    ///
    /// Symbol names include enclosing models, for example `World::Inner::Item`.
    /// Rules are not part of the signature.
    fn dynamic_signature() -> Arc<Signature>;

    /// Copies stored data, preserving IDs, equality representatives, and raw rows.
    ///
    /// Includes inherited facts already present in the model. Export does not
    /// propagate morphisms or resolve function conflicts. The source is unchanged.
    /// Relation trees share their nodes with the source. Export validates stored
    /// handles and deeply copies union-find and weight vectors. For a compiled
    /// handle, use its wrapped integer and the type ID from [`Self::dynamic_signature`].
    fn to_dynamic(&self) -> Model;

    /// Imports data without changing IDs, equality representatives, or raw rows.
    ///
    /// All imported facts become explicit and are treated as new by evaluation.
    /// Compatible indices share tree nodes. Other indices are rebuilt as needed.
    /// Import does not check theory axioms. Calling `close` afterward may still
    /// leave some axioms unsatisfied. For example, an enum element created without
    /// a constructor may still have no case.
    ///
    /// Returns [`Error::SignatureMismatch`] if type or relation descriptors differ
    /// from [`Self::dynamic_signature`], including their order and names.
    fn from_dynamic(model: &Model) -> Result<Self, Error>;
}

/// Invalid descriptors, handles, or mutations. An error leaves model data unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// Descriptors violate the structural requirements of [`Signature::new`].
    InvalidSignature(String),
    /// Stored indices or vector dimensions are inconsistent.
    InvalidModel(String),
    /// The type ID is outside this signature.
    UnknownType(TypeId),
    /// The relation ID is outside this signature.
    UnknownRelation(RelationId),
    /// The type exists, but the element index has not been allocated.
    UnknownElement(Element),
    /// An argument has the wrong type.
    TypeMismatch { expected: TypeId, actual: TypeId },
    /// A tuple or parent chain has the wrong length.
    ArityMismatch { expected: usize, actual: usize },
    /// A member does not belong to the supplied enclosing models.
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
            Self::InvalidModel(message) => write!(f, "invalid model: {message}"),
            Self::UnknownType(type_) => write!(f, "unknown type {type_:?}"),
            Self::UnknownRelation(relation) => write!(f, "unknown relation {relation:?}"),
            Self::UnknownElement(element) => write!(f, "unknown element {element:?}"),
            Self::TypeMismatch { expected, actual } => {
                write!(f, "expected type {expected:?}, got {actual:?}")
            }
            Self::ArityMismatch { expected, actual } => {
                write!(f, "expected {expected} arguments, got {actual}")
            }
            Self::ParentMismatch => write!(f, "member does not belong to the supplied models"),
            Self::SignatureMismatch => write!(f, "dynamic and compiled signatures differ"),
            Self::ElementLimit => write!(f, "element ID space exhausted"),
        }
    }
}

impl std::error::Error for Error {}

mod prefix_tree;
mod toposort;
mod unification;
#[doc(hidden)]
pub mod wbtree;

#[doc(hidden)]
pub use crate::prefix_tree::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};
#[doc(hidden)]
pub use crate::unification::Unification;

#[doc(hidden)]
pub use crate::toposort::{morphism_toposort, MorphismWithSignature, ToposortError};

/// Declare an eqlog module.
///
/// # Examples
///
/// ```ignore
/// use eqlog_runtime::eqlog_mod;
/// eqlog_mod!(foo);
/// ```
///
/// Eqlog modules can be annotated with a visibility, or with attributes:
/// ```ignore
/// eqlog_mod!(#[cfg(test)] pub foo);
/// ```
#[macro_export]
macro_rules! eqlog_mod {
    ($(#[$attr:meta])* $vis:vis $modname:ident) => {
        $(#[$attr])* $vis mod $modname {
            include!(concat!(
                env!("EQLOG_OUT_DIR"),
                "/",
                file!(),
                "/",
                "..",
                "/",
                stringify!($modname),
                ".eql.rs"
            ));
        }
    };
}
