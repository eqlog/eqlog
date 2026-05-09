# Algebra Semantic Diagnostics Parallelization

The remaining migration from `eqlog-eqlog` diagnostics to Rust-side `algebra`
checks can be parallelized, but not all workstreams are independent.

## Current State

`eqlog/src/build.rs` already computes Rust-side diagnostics before calling
`check_eqlog`. The Rust-side pieces cover signature type lookup, argument
counts, many type conflicts, rule surjectivity, and match exhaustiveness.
`eqlog/src/semantics/mod.rs` still contributes rule-body symbol lookup,
undetermined term type, enum-constructor surjectivity, morphism-application
misuse, and some type-conflict cases.

A temporary probe with `check_eqlog` disabled left 31 of 48 compile-error tests
passing. The failures are the migration backlog.

## Workstreams

- `algebra-type-conflict-parity.md`: fix known type-conflict gaps and diagnostic
  attribution. This is the main dependency for safely removing
  `iter_conflicting_type_errors`.
- `algebra-symbol-lookup-diagnostics.md`: replace rule-body
  `iter_symbol_lookup_errors`.
- `algebra-undetermined-term-type.md`: replace `iter_undetermined_type_errors`.
- `algebra-enum-ctor-surjectivity.md`: replace
  `iter_enum_ctors_not_surjective_errors`.
- `algebra-morphism-application-diagnostics.md`: replace
  `iter_non_morphism_applied_as_morphism_errors` and
  `iter_morphism_applied_to_non_member_errors`.
- `algebra-check-eqlog-removal.md`: final switch-over plan once the above are
  implemented.

## Parallelization

The symbol lookup, enum constructor, undetermined type, and morphism-application
plans can be implemented in parallel as independently reviewable diagnostic
features. Type-conflict parity should be treated as a prerequisite for deleting
the Eqlog-side conflicting-type pass, but it does not block implementing the
other detectors.

Recommended feature split:

- Type-conflict parity: parent-dependent function/member type conflicts and
  diagnostic attribution for term equality conflicts.
- Rule-body symbol lookup: undeclared symbols, wrong symbol kind, and missing or
  invalid member type references.
- Undetermined term type: variables or terms whose type remains open after the
  rule-body constraints close.
- Enum-constructor surjectivity: enum values used in `then` terms that are not
  introduced by a constructor.
- Morphism-application diagnostics: non-morphism `@` applications and morphism
  applications to terms outside the morphism's model.
- Final `check_eqlog` diagnostic removal: integration-only cleanup after the
  feature migrations have landed.

File ownership is a coordination detail within each feature, not the review
unit. If two features need the same helper, land the helper with the first
feature that needs it and keep the second feature's patch focused on its own
diagnostic behavior.

Avoid having multiple workers edit the same test expectations at once. Each
workstream should add or adjust tests only for its own diagnostic cases, then the
final integration workstream should run the full error suite after disabling the
specific Eqlog-side iterator it is replacing.

## Common Verification

Every workstream should run at least:

- `cargo test -p eqlog-test-compile --test errors`
- The focused test case being migrated with `-- --exact` when applicable.
- `cargo fmt --check`

Before a final removal commit, regenerate prebuilt Eqlog output only if
`eqlog-eqlog/src/eqlog.eql` changed:

```sh
eqlog eqlog-eqlog/src eqlog-eqlog/prebuilt/
```

Use the installed `eqlog` binary from the environment, not one built from this
checkout.
