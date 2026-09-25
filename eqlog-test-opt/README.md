Run all four combinations of naive/semi-naive evaluation and native/desugared
morphisms:

```sh
cargo test -p eqlog-test-opt
```

`src/authored.rs` uses the checked-in theories in `corpus/` and generated Rust
setters. It tests merged witnesses with a late gate, a morphism diamond with
model and morphism equalities, and nested images with late facts and members.
Each case makes explicit assertions and compares closures up to isomorphism,
fixing all supplied elements, including later allocations.

The randomized morphism test creates 3-6 model instances joined by a chain,
random forward arrows, and a parallel arrow. It varies carrier sizes, arrow
insertion order, and partial image maps, including non-injective maps.
Codomains, facts, members, and equalities arrive between closures. Arrows stay
acyclic to bound image creation and satisfy the native evaluator.

`theories.rs` generates 1-3 sorts, unary partial functions, 3-6 predicates of
arity 0-3, and 4-9 rules with typed joins and predicate/equality conclusions.
Equality conclusions include both repeated and distinct variables.
Each seed produces a flat theory and a version inside a model with image
creation rules. Ordinary rules create no elements. The grammar excludes enums
and nested models; the latter are covered by a handwritten case.

`src/trace.rs` generates allocations, fact insertions, function definitions,
equalities, and closures for those theories. Compiled models persist between
operations. Runtime dispatch calls their setters; reimporting a dynamic model
would mark all facts as new and could hide incremental evaluation bugs.

Defaults are two theory seeds, four traces per generated theory, five rounds
per trace, and sixteen seeds for the randomized morphism test. To vary them:

```sh
EQLOG_OPT_THEORY_SEED=42 EQLOG_OPT_THEORIES=4 cargo test -p eqlog-test-opt
EQLOG_OPT_INPUT_SEED=100 EQLOG_OPT_TRACES=100 EQLOG_OPT_ROUNDS=8 cargo test -p eqlog-test-opt
```

Input seeds and trace counts also control the randomized morphism test.
For an OS-selected theory seed:

```sh
seed=$(od -An -N8 -tu8 /dev/urandom | tr -d ' ')
echo "Theory seed: $seed"
EQLOG_OPT_THEORY_SEED="$seed" cargo test -p eqlog-test-opt
```

Evaluation or comparison failures save the generated theory and operation
trace under `target/eqlog-opt-failures/` and print a replay command:

```sh
EQLOG_OPT_CASE=/absolute/path/case.eql EQLOG_OPT_TRACE=/absolute/path/trace.json \
    cargo test -p eqlog-test-opt optimization_equivalence
```

The randomized morphism test prints its seed; replay it with
`EQLOG_OPT_INPUT_SEED=<seed> EQLOG_OPT_TRACES=1`.

Closure fails after 512 iterations. Isomorphism search fails on fuel exhaustion
(50 million by default; override with `EQLOG_OPT_FUEL`). There is no shrinking
or timeout for an individual rule evaluation.
