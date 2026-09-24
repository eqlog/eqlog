This crate compares the closures produced by all four combinations of naive or
semi-naive evaluation and native or desugared model morphisms. Run it with:

```sh
cargo test -p eqlog-test-opt
```

The default suite compiles four random theories (two seeds, each with a flat and
an indexed version) and the `.eql` files in `corpus/`. Each theory gets four
random operation sequences, each with five rounds of edits and closure. The
same trace runs independently against each compilation. The test compares
after every closure, including an initial empty closure and repeated closures.
Paired corpus `.json` traces also run, ensuring their intended interactions
remain covered regardless of random inputs.

The comparison uses `find_isomorphism_under` with the model of supplied inputs
as its common base. An arbitrary isomorphism would be too weak: it could swap
two distinct inputs to disguise a wrong answer. Allocation and function
definition operations produce symbolic handles, resolved separately in each
execution. Thus later edits can use old aliases or function results even when
compilations allocate different IDs or identify different elements. Each
compiled model stays alive across the whole trace, retaining its old/new
partitions and auxiliary indices. Runtime-typed edits dispatch to its generated
setters after validation on a snapshot; importing that snapshot would instead
mark every fact new and mask incremental evaluation bugs. The next round never
restarts from the inputs or copies the reference closure.

"Random" here means seeded pseudorandom sampling from an explicit, restricted
distribution, not uniform sampling over all Eqlog programs. `theories.rs`
samples one to three sorts, three to six predicates of arity zero to three,
and four to nine rules. Rules sample typed variables, one to three predicate
premises, optional function lookups, and predicate or equality conclusions.
Repeated variables, disconnected joins, and recursive predicate dependencies
are possible. Each sort also has a unary partial function. The indexed version
puts the declarations and rules inside a model and adds image-creation rules.
Rules never create ordinary function results, so these theories have finite
closure over finite inputs and acyclic morphisms.

`src/trace.rs` samples well-typed allocations, relation and function-graph
insertions, definitions, equalities, duplicate insertions, and explicit
canonicalization. Every declared input relation is scheduled for insertion in
a randomly chosen round. Each round adds eight to sixteen random edits, with insertion
weighted twice as heavily as each other available action. Indexed traces have
three model instances and up to three morphisms with strictly increasing
endpoints; image operations include both definitions and supplied images.
Only members of the same parent context are equated. This prevents cycles and
keeps operations valid under the homomorphisms into every evaluated model.
Enums, nested models, model equalities, and arbitrary dependent signatures are
outside this first generator's scope. Unsupported shapes fail explicitly.

Theory generation happens during the Cargo build because Eqlog emits Rust.
Input generation happens during the test, so exploring more inputs is cheap:

```sh
EQLOG_OPT_INPUT_SEED=100 EQLOG_OPT_TRACES=100 cargo test -p eqlog-test-opt
EQLOG_OPT_THEORY_SEED=42 EQLOG_OPT_THEORIES=4 cargo test -p eqlog-test-opt
```

`EQLOG_OPT_ROUNDS` changes the number of rounds per trace. Seeds and counts are
decimal unsigned integers. Defaults are deterministic for routine CI. For fresh
campaigns, draw a seed from the OS, retain it in the job log, and rebuild:

```sh
seed=$(od -An -N8 -tu8 /dev/urandom | tr -d ' ')
echo "Theory and input seed: $seed"
EQLOG_OPT_THEORY_SEED="$seed" EQLOG_OPT_INPUT_SEED="$seed" cargo test -p eqlog-test-opt
```

The generator uses the pinned `rand` version in Cargo.lock. Exact sources and
traces are the durable reproduction format across generator changes. On an
evaluation or comparison failure, the test writes `case.eql` and `trace.json`
under `target/eqlog-opt-failures/` and prints a replay command:

```sh
EQLOG_OPT_CASE=/absolute/path/case.eql EQLOG_OPT_TRACE=/absolute/path/trace.json \
    cargo test -p eqlog-test-opt optimization_equivalence
```

The JSON array is also editable for manual reduction. New/Define operations
append a handle; other operations reference zero-based handle slots. Replay
requires a final Close operation. Compiler failures report the generated
source path under Cargo's build output. Closure has a 512-iteration budget and
comparison has 50 million units of search fuel (`EQLOG_OPT_FUEL` overrides it).
Exhaustion fails the test with a separate
diagnostic; it is never accepted as equivalence. The iteration limit cannot
interrupt an individual rule evaluation; use a process timeout for campaigns
with untrusted or much larger corpus entries. Automated shrinking and hard
per-case process limits are future work.

The LLM contribution lives in a reviewed, checked-in corpus, not an API call
during tests. `corpus/README.md` records the scenarios and a recipe for adding
diverse cases. Random input traces already vary each corpus theory. The two
sources complement each other: a model can propose purposeful feature
interactions, while classical generation explores syntax and data without
depending on a model's tendency to repeat familiar examples. Neither source
is an independent semantics oracle; agreement between implementations can
still miss a shared compiler bug.
