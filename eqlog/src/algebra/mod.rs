//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! This module currently exposes only [`signature`], which extracts a
//! [`signature::Signature`] from the AST. Future passes (per-statement
//! morphism construction, structure population, ...) will live alongside it.

pub mod signature;
