//! Compile checks that run after [`crate::scopes::resolve_scopes`] and need
//! ordered scopes but not type inference. Each submodule owns one
//! self-contained analysis:
//!
//! * [`bindings`] — position-local checks on `then`-atom terms, defined-var
//!   slots, and match-pattern arguments.
//! * [`occurrences`] — per-rule singleton detection for resolved variable
//!   bindings.
//!
//! The entry points return errors as a `Vec` or `Option`; [`crate::build`]
//! merges them through `CompileError`'s `Ord` so that the global
//! kind-precedence ordering applies.

pub mod bindings;
pub mod occurrences;

pub use bindings::check_bindings;
pub use occurrences::check_occurrences;
