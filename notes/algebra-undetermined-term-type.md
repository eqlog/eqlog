# Algebra Undetermined-Term-Type Plan

## Goal

Replace `iter_undetermined_type_errors` in `eqlog/src/semantics/mod.rs` with a
Rust-side pass over `RuleStructures`.

## Current Gap

With `check_eqlog` disabled, `undetermined-variable-type` reaches flattening and
panics instead of reporting `CompileError::UndeterminedTermType`. The
`surjectivity-violation-mor-app` case also currently relies on the Eqlog-side
undetermined-type diagnostic.

## Implementation Steps

1. Add a post-close diagnostic pass in `eqlog/src/algebra/mod.rs` that runs
   after type conflicts and argument-number errors have been collected.
2. For every structure in a rule, inspect `rule.semantic_els[sid]`. For each
   term's element root, check whether `Structure::els[root]` has a
   `ConcreteType`.
3. Emit `CompileError::UndeterminedTermType { location: ast.loc(term) }` for
   surface terms whose element has no type.
4. Avoid duplicate diagnostics for the same AST term across structures. A
   `BTreeSet<TermId>` or `BTreeSet<Location>` is enough.
5. Do not report ambient model elements, generated result elements, or other
   internal elements without a surface `TermId`.
6. Consider diagnostic priority: this pass should run after symbol lookup and
   type conflicts are collected, then rely on `CompileError::Ord` when merging.
7. Temporarily remove only `iter_undetermined_type_errors` from `check_eqlog`
   and run the full compile-error suite.

## Files To Touch

- `eqlog/src/algebra/mod.rs`
- possibly `eqlog/src/algebra/structure.rs` for a small typedness helper
- `eqlog/src/semantics/mod.rs` when disabling/removing the Eqlog-side iterator

## Verification

- `cargo test -p eqlog-test-compile --test errors undetermined_variable_type -- --exact`
- `cargo test -p eqlog-test-compile --test errors surjectivity_violation_mor_app -- --exact`
- `cargo test -p eqlog-test-compile --test errors`
- `cargo fmt --check`

## Parallelization Notes

This is a narrow pass and can be implemented in parallel with symbol lookup or
enum-constructor checks. Coordinate edits to `algebra/mod.rs` if another worker
is also adding post-close diagnostics.
