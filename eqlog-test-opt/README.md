This crate compares naive/semi-naive evaluation and native/desugared model
morphisms, using all four compiler configurations.

```sh
cargo test -p eqlog-test-opt
```

The authored cases are ordinary Rust tests in `src/authored.rs`, paired with
Eqlog theories in `corpus/`. They call generated setters and make explicit
assertions about results. Each test body runs against all four compilations;
closures are also compared up to isomorphism under the supplied inputs,
including morphisms and members allocated in later rounds.
The compiled models stay alive across every round.

The cases cover:

- A late gate enabling a join through previously merged function results.
- A diamond of morphisms whose target images and function results merge,
  followed by equalities between intermediate models and parallel morphisms.
- Nested model and member images, with new facts and members arriving after
  both the inner and outer morphisms have already been evaluated.
- Random graphs on three to six models, including chains, diamonds, and
  parallel arrows. Morphisms start with only a domain; codomains and partial,
  possibly non-injective image maps arrive after closure. Later rounds add
  members, facts, and equalities. Assertions check membership, predicate
  preservation, and preservation of functions.

The morphism graph test uses sixteen input seeds by default. Its random
choices are in the Rust test itself. Increasing model indices orient the
arrows acyclically, which keeps image creation finite and respects the native
morphism evaluator's requirement. The graph shape, edge insertion order,
carrier sizes, and image assignments vary by seed.

There is also a separate theory generator in `theories.rs`. It samples one to
three sorts, three to six predicates of arity zero to three, and four to nine
rules with typed joins, function lookups, and predicate/equality conclusions.
Each seed produces a flat theory and a version inside a model with image
creation rules. Ordinary rules create no elements. This generator still has
a restricted grammar; enums and arbitrary nested theories are outside it.

These generated theories receive random edit sequences from `src/trace.rs`.
The comparison preserves every supplied symbolic input, including handles
returned by function definitions. Runtime-typed edits call generated setters
in place, retaining old/new facts and auxiliary indices. The default is two
theory seeds, four input seeds, and five rounds per generated theory.

To explore more inputs or new theories:

```sh
EQLOG_OPT_INPUT_SEED=100 EQLOG_OPT_TRACES=100 cargo test -p eqlog-test-opt
EQLOG_OPT_THEORY_SEED=42 EQLOG_OPT_THEORIES=4 cargo test -p eqlog-test-opt
```

The input seed and trace count also control the randomized morphism graph
test. `EQLOG_OPT_ROUNDS` controls the generated edit sequences. Defaults are
reproducible. For a fresh theory seed from the OS:

```sh
seed=$(od -An -N8 -tu8 /dev/urandom | tr -d ' ')
echo "Theory seed: $seed"
EQLOG_OPT_THEORY_SEED="$seed" cargo test -p eqlog-test-opt
```

Failing generated edit sequences save their exact theory and a machine-readable
trace under `target/eqlog-opt-failures/`, with a replay command:

```sh
EQLOG_OPT_CASE=/absolute/path/case.eql EQLOG_OPT_TRACE=/absolute/path/trace.json \
    cargo test -p eqlog-test-opt optimization_equivalence
```

JSON is only a failure/replay format for generated edit sequences. Authored
cases use Rust tests. Random morphism graph failures print their input seed;
rerun that test with `EQLOG_OPT_INPUT_SEED` set to it and `EQLOG_OPT_TRACES=1`.

Closure has a 512-iteration budget and isomorphism search has 50 million units
of fuel (`EQLOG_OPT_FUEL` overrides it). Exhaustion fails explicitly. The
iteration budget cannot interrupt a single rule evaluation. Automated
shrinking and hard per-case process limits are not implemented.
