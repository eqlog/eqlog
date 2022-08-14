# Semilattice

This directory contains a minimal rust/cargo project that depends eqlog.
The project consists of the following additions to a minimal cargo binary project:
* In `Cargo.toml`, a build dependency on `eqlog` and a normal dependency on `eqlog-runtime`.
* The `build.rs` file.
* An example eqlog module `src/semilattice.eqlog` of meet-semilattices.
* A declaration and import of `src/semilattice.eqlog` in `main.rs` (this would be `lib.rs` for library projects) using 
  ```rust
  use eqlog_runtime::eqlog_mod;
  eqlog_mod!(semilattice);
  use crate::semilattice::*;
  ```
* An example `fn main` that computes whether or not meets in semilattices are associative.
  Execute it with `cargo run`.
