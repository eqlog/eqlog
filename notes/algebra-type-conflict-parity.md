# Algebra Type-Conflict Parity Plan

## Goal

Make Rust-side algebra type conflicts match the user-facing behavior currently
provided by `iter_conflicting_type_errors` in `eqlog/src/semantics/mod.rs`, then
remove that Eqlog-side diagnostic from the merged error set.

## Known Gaps

With `check_eqlog` disabled, these cases show gaps:

- `bad-dep-func-arg-type` compiles when it should report a conflict between
  `s_0.El` and `s_1.El`.
- `bad-dep-func-result-type` compiles when it should report a conflict between
  `s_0.El` and `s_1.El`.
- `conflicting-term-type-equality` reports the later annotation and reversed
  type order compared to the Eqlog-side diagnostic.

The first two indicate that parent-dependent member type conflicts can be hidden
when information is propagated through member function applications and
morphisms. The last issue is diagnostic attribution, not detection.

## Implementation Steps

1. Add focused regression tests, or run the existing compile-error cases with
   only `iter_conflicting_type_errors` disabled, to pin the desired behavior.
2. Inspect `Structure::impose_concrete_type`, `resolve_parent_checks`, and
   `StructureCat::pull_morphism_types` for parent-list conflict paths that are
   recorded but later dropped.
3. Make parent disagreements durable across close cycles when they are not
   rescued by later equalities. A likely fix is to preserve enough source
   element information to report conflicts after `StructureCat::close`
   canonicalizes structures.
4. Review member-function application typing in `populate.rs`. For member
   functions, the parent chain emitted with `FuncApp` must force each argument
   and result to use the member receiver's model element, even after morphism
   push-forward and backward type reflection.
5. Improve `conflict_to_error` attribution. Prefer the earliest surface term in
   source order that participates in the conflicting equivalence class, matching
   Eqlog's current selection where possible.
6. Stabilize diagnostic type ordering. Preserve "existing type, newly imposed
   type" order for annotation conflicts, but use source-order or insertion-order
   behavior for equality conflicts so expected error text does not churn.
7. Temporarily remove only `iter_conflicting_type_errors` from `check_eqlog`,
   run the full compile-error suite, and keep the removal only if all existing
   conflicting-type cases match.

## Files To Touch

- `eqlog/src/algebra/structure.rs`
- `eqlog/src/algebra/mod.rs`
- `eqlog/src/algebra/populate.rs`
- `eqlog-test-compile/error-test-source/*` only if new edge cases are added

## Verification

- `cargo test -p eqlog-test-compile --test errors conflicting_term_type_equality -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_dep_func_arg_type -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_dep_func_result_type -- --exact`
- `cargo test -p eqlog-test-compile --test errors`
- `cargo fmt --check`

## Parallelization Notes

This workstream can run in parallel with symbol lookup, enum-constructor, and
morphism diagnostics. It should finish before the final `check_eqlog` removal
because other workstreams may still rely on algebra's type information.
