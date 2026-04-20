//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! [`signature`] builds the dependent signature (types, preds, funcs) from
//! the AST. [`structure`] holds the per-rule and per-statement structure
//! data; [`algebraize`] populates it by walking the AST rule bodies.
//! [`close`] saturates a structure under functionality and signature-imposed
//! typing. Future passes (morphism construction) will live alongside them.

pub mod algebraize;
pub mod close;
pub mod signature;
pub mod structure;
