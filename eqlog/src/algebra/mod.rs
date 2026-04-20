//! Rust-side construction of the algebraic objects (signatures, structures,
//! morphisms, ...) that the compiler reasons about.
//!
//! [`signature`] builds the dependent signature (types, preds, funcs) from
//! the AST. [`structure`] builds the before- and after-structures of every
//! statement in every rule. Future passes (morphism construction,
//! unification) will live alongside them.

pub mod signature;
pub mod structure;
