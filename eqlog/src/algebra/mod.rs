//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! [`signature`] builds the dependent signature (types, preds, funcs) from
//! the AST. [`structure`] holds the per-rule and per-statement structure
//! data, including the close pass that saturates it under functionality and
//! signature-imposed typing. [`algebraize`] populates the initial structure
//! by walking the AST rule bodies. Future passes (morphism construction)
//! will live alongside them.

pub mod algebraize;
pub mod signature;
pub mod structure;
