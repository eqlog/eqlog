# Algebra Morphism-Application Diagnostics Plan

## Goal

Replace these Eqlog-side diagnostics from `eqlog/src/semantics/mod.rs`:

- `iter_non_morphism_applied_as_morphism_errors`
- `iter_morphism_applied_to_non_member_errors`

## Rules To Preserve

For `f@(x)`:

- `f` must have type `Mor(M)` for some model `M`.
- `x` must be a member element of that same model `M`.

If `f` is not a morphism, report
`CompileError::NonMorphismAppliedAsMorphism` at the morphism term. If `x` is not
a member of the morphism's model, report
`CompileError::MorphismAppliedToNonMember` at the argument term.

## Implementation Steps

1. During or after `walk_term`, record every `Term::MorApp` site with:
   - the mor term `TermId`
   - the arg term `TermId`
   - the structure where the application was evaluated
2. After the close fixed point, inspect the concrete types of the mor and arg
   elements in that structure.
3. If the mor term has a known non-`Mor` type, emit
   `NonMorphismAppliedAsMorphism` at `ast.loc(mor_term)`.
4. If the mor term has a known `Mor(M)` type and the arg term is not a member
   element of model `M`, emit `MorphismAppliedToNonMember` at `ast.loc(arg)`.
5. Treat "arg is a member element of a different model" as
   `MorphismAppliedToNonMember`, matching the current
   `mor-applied-to-false-member` test.
6. If either term is still untyped, do not emit a morphism diagnostic from this
   pass. The undetermined-type pass should handle that.
7. Ensure `resolve_mor_app` does not create a function app for an invalid
   morphism application once the diagnostic is known. This avoids later
   surjectivity noise.
8. Temporarily remove the two Eqlog-side iterators from `check_eqlog` and run
   the targeted tests.

## Files To Touch

- `eqlog/src/algebra/populate.rs`
- `eqlog/src/algebra/mod.rs`
- possibly `eqlog/src/algebra/structure.rs` for type-inspection helpers
- `eqlog/src/semantics/mod.rs` when disabling/removing the Eqlog-side iterators

## Verification

- `cargo test -p eqlog-test-compile --test errors non_mor_applied_as_mor -- --exact`
- `cargo test -p eqlog-test-compile --test errors mor_applied_to_non_member -- --exact`
- `cargo test -p eqlog-test-compile --test errors mor_applied_to_false_member -- --exact`
- `cargo test -p eqlog-test-compile --test errors surjectivity_violation_mor_app -- --exact`
- `cargo test -p eqlog-test-compile --test errors`
- `cargo fmt --check`

## Parallelization Notes

This overlaps with undetermined-type work because invalid morphism applications
can leave result terms untyped. Agree on diagnostic priority before both changes
land.
