# Algebra `check_eqlog` Removal Plan

## Goal

Remove dependency on Eqlog-side semantic error detection once Rust-side algebra
passes provide equivalent diagnostics.

## Preconditions

Do not start this work until these workstreams have landed:

- type-conflict parity
- rule-body symbol lookup diagnostics
- undetermined term type
- enum-constructor surjectivity
- morphism-application diagnostics

Each workstream should already have proven parity by temporarily disabling its
corresponding iterator in `check_eqlog`.

## Implementation Steps

1. Disable all diagnostic iterators in `eqlog/src/semantics/mod.rs` locally and
   run `cargo test -p eqlog-test-compile --test errors`.
2. If the full suite passes, remove the now-unused diagnostic functions from
   `semantics/mod.rs`.
3. Decide whether `semantics/mod.rs` should disappear entirely. If no other
   code imports it, remove the module declaration from `eqlog/src/lib.rs`.
4. Keep `populate_eqlog` and `eqlog.close()` in `build.rs` if flattening and code
   generation still depend on generated Eqlog facts. This plan removes semantic
   error detection, not generated Eqlog lowering.
5. If `eqlog-eqlog/src/eqlog.eql` no longer needs the diagnostic-only
   predicates, remove them in a separate, easy-to-review patch.
6. Regenerate prebuilt Eqlog Rust if `eqlog-eqlog/src/eqlog.eql` changed:

```sh
eqlog eqlog-eqlog/src eqlog-eqlog/prebuilt/
```

Use the installed `eqlog` binary from the environment.

## Verification

- `cargo test`
- `cargo fmt --check`
- If Eqlog source changed, verify `git diff -- eqlog-eqlog/prebuilt/eqlog.rs`
  and commit the regenerated file.
- Review the final removal as one feature-level diff, then use per-file diffs
  only as a consistency check for generated output, leftover helpers, and stale
  comments.

## Parallelization Notes

This is an integration task and should not run in parallel with the individual
diagnostic migrations. It is the final cleanup once the parallel workstreams
have converged.
