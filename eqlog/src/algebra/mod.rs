//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! [`signature`] builds the dependent signature (types, preds, funcs) from
//! the AST. [`structure`] holds the per-rule and per-statement structure
//! data; [`algebraize`] populates it by walking the AST rule bodies. Future
//! passes (morphism construction, unification) will live alongside them.

pub mod algebraize;
pub mod signature;
pub mod structure;
