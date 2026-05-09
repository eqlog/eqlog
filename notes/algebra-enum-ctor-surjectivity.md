# Algebra Enum-Constructor Surjectivity Plan

## Goal

Replace `iter_enum_ctors_not_surjective_errors` in
`eqlog/src/semantics/mod.rs`.

## Rule To Preserve

For a `then t!` defined atom, if `t` has an enum type, `t` must be introduced
directly by one of that enum's constructors. A non-constructor function returning
the enum should produce `CompileError::EnumCtorsNotSurjective`.

This is distinct from rule morphism surjectivity, which is already implemented
in `algebra/mod.rs`.

## Implementation Steps

1. Add a pass over each rule body after structures have closed and no higher
   priority structure errors were emitted.
2. Find every `ThenAtom::Defined` term.
3. Resolve the term's algebra `ConcreteType` from the target statement
   structure. If the type is not an enum, skip it.
4. Determine whether the term is syntactically an ambient constructor
   application for that enum:
   - `Term::App`
   - `FuncExpr::Ambient`
   - lookup resolves to `Symbol::Ctor`
   - `signature.func_for_ctor_decl(ctor).codomain` is the same enum type
5. If not, emit `CompileError::EnumCtorsNotSurjective` with:
   - `term_location: ast.loc(term)`
   - `enum_location: ast.loc(enum_decl)`
   - `enum_name` from the AST
6. Avoid running this pass when the term type is conflicting or undetermined.
   In those cases, the type diagnostic should win.
7. Temporarily remove only `iter_enum_ctors_not_surjective_errors` from
   `check_eqlog` and run the error suite.

## Files To Touch

- `eqlog/src/algebra/mod.rs`
- possibly `eqlog/src/algebra/signature.rs` if an enum-name helper is useful
- `eqlog/src/semantics/mod.rs` when disabling/removing the Eqlog-side iterator

## Verification

- `cargo test -p eqlog-test-compile --test errors enum_ctors_not_surjective -- --exact`
- Add a positive test if one does not already cover `then Ctor(...)!` for an
  enum constructor.
- `cargo test -p eqlog-test-compile --test errors`
- `cargo fmt --check`

## Parallelization Notes

This can be implemented in parallel with undetermined-type detection, but both
will probably edit `algebra/mod.rs`. Keep helpers small and local to reduce
merge conflicts.
