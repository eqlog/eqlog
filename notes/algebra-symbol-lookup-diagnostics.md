# Algebra Symbol-Lookup Diagnostics Plan

## Goal

Replace `iter_symbol_lookup_errors` in `eqlog/src/semantics/mod.rs` with
Rust-side checks based on the AST and `Scopes`.

## Scope

This detector should cover rule-body lookup sites, not just declaration
signatures:

- ambient type expressions in `if x: Type`
- member type expressions in `if x: model.Type`
- ambient predicate expressions
- member predicate expressions
- ambient function expressions, accepting functions and constructors where the
  grammar allows both
- member function expressions
- match-case pattern constructors, where the pattern function must be a
  constructor

Declaration-signature type lookup is already handled by `build_signature`.

## Implementation Steps

1. Create a small lookup-diagnostics module, probably
   `eqlog/src/algebra/symbols.rs` or a new `scope_checks` submodule, with an
   entry point returning `Vec<CompileError>`.
2. Walk modules, nested models, and all rule bodies in source order.
3. For ambient lookups, use `scopes.entry(node)` and `scopes.lookup` directly.
   Emit `UndeclaredSymbol` or `BadSymbolKind` with the same primary expected
   kind as Eqlog:
   - type positions: expected `TypeSymbol`, but accept type, enum, or model
   - predicate positions: expected `PredSymbol`
   - function positions: expected `FuncSymbol`, but ambient app terms accept
     functions or constructors
   - morphism type positions: expected `ModelSymbol`
   - match patterns: expected `CtorSymbol`
4. For member lookups, delay the diagnostic until the receiver term has a known
   model type. Reuse algebra's term type information from `RuleStructures`, or
   add a small post-structure pass that maps each member expression to the
   receiver's resolved model body scope.
5. When a receiver is not known to be a model, do not emit a symbol lookup
   diagnostic from this pass. That should remain a type diagnostic.
6. Preserve Eqlog behavior for variables and args in symbol positions:
   `iter_symbol_lookup_errors` cannot report a variable kind, so these cases
   should be `UndeclaredSymbol`, not `BadSymbolKind`.
7. Merge these errors in `build.rs` before `eqlog_err`, then temporarily remove
   `iter_symbol_lookup_errors` from `check_eqlog` and run the error suite.

## Files To Touch

- new module under `eqlog/src/algebra/` or `eqlog/src/scope_checks/`
- `eqlog/src/build.rs`
- possibly `eqlog/src/algebra/mod.rs` if the pass needs `RuleStructures`
- `eqlog/src/semantics/mod.rs` when disabling/removing the Eqlog-side iterator

## Verification

- `cargo test -p eqlog-test-compile --test errors undeclared_function -- --exact`
- `cargo test -p eqlog-test-compile --test errors undeclared_predicate -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_member_type_missing -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_member_type_not_a_type -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_symbol_kind_function_rule -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_symbol_kind_predicate_function -- --exact`
- `cargo test -p eqlog-test-compile --test errors bad_symbol_kind_type_predicate -- --exact`
- `cargo test -p eqlog-test-compile --test errors`
- `cargo fmt --check`

## Parallelization Notes

This can run mostly independently. The only likely conflict is if another
workstream changes `build.rs` error merging or exports new data from
`RuleStructures`.
