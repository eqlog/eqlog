# ETT evaluator investigation

Measured at `8991f586ba5e9288e663f2d9fba6ea144716e031`, after merging
`host/master` at `895e9a7`. This is an investigation and implementation plan;
the production evaluator and proof checker are unchanged.

The main finding is that model isolation is currently semantic, but not an
effective scheduling boundary for this kernel. All 17 generated strata are
global. Most closure time goes to repeatedly transporting existing facts and
preparing indices, rather than matching the proof rules themselves.

## Measurements

The diagnostic builds an independent executable from the release evaluator's
generated Rust and its existing rule libraries. Nested timers separate rule
calls, primary transport, native secondary-index preparation, graph
construction, canonicalization, and allocation rounds. Only exclusive times
can be added. Counters record visits and candidate output batches, not unique
new facts. Relation cardinalities and graph statistics are collected outside
`close()`.

Hardware: x86_64 AMD EPYC 9645; Rust 1.95.0. Runs are sequential. The evaluator
uses one CPU. Compilation is excluded. Hardware sampling was unavailable in
the container, so these are instrumented wall-clock measurements, not sampled
CPU profiles. They are individual diagnostic runs, not statistical benchmarks.

The small fixture is `nat.ett` through `add_assoc`, before `congr_succ`. Nat
uses the complete `nat.ett`; the full development concatenates Nat and Vec and
uses the same single `close()` as the integration test.

| Workload | Declarations | Contexts | Final canonical terms | Final morphisms | `close()` | Peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Addition prefix | 8 | 48 | 252 | 491 | 2.067 s | 18.5 MiB |
| Nat | 31 | 207 | 1,638 | 3,882 | 83.295 s | 120.6 MiB |
| Nat + Vec | 52 | 430 | 4,905 | 11,240 | 841.025 s | 618.7 MiB |

These are different developments, not a controlled estimate of a scaling
exponent. The uninstrumented addition executable took 2.230 s end to end;
the instrumented executable took 2.089 s. That difference illustrates timing
noise rather than a negative instrumentation overhead. Elaboration took
0.007 s, 0.115 s, and 0.523 s respectively.

| Exclusive closure cost | Addition | Nat | Nat + Vec | Full share |
| --- | ---: | ---: | ---: | ---: |
| Primary relation transport | 0.884 s | 37.612 s | 417.312 s | 49.6% |
| Alternate native indices, excluding graph construction | 0.476 s | 24.921 s | 273.647 s | 32.5% |
| Morphism graph construction | 0.100 s | 4.974 s | 35.914 s | 4.3% |
| All rule groups, including category/functionality rules | 0.304 s | 7.415 s | 54.490 s | 6.5% |
| Direct canonicalization | 0.026 s | 0.711 s | 4.569 s | 0.5% |
| Applying allocation requests | 0.003 s | 0.041 s | 0.188 s | <0.1% |
| Other input views, output insertion, and scheduling | 0.275 s | 7.622 s | 54.906 s | 6.5% |

Thus 86.4% of the full closure is transport/index/graph preparation. Its main
stratum runs 915 times; the five main alternate indices rebuild 874 times
each. The graph is reconstructed 5,405 times. Primary transport makes
8,015,082 edge visits, and all transport paths produce 374,970,808 candidate
subtree batches. These batches can contain shared suffixes and duplicates;
they are not counts of new facts. The final graph has 397 SCCs and a largest
component of three contexts. The largest individual rule cost is identity
proof uniqueness at 8.032 s, less than 1% of closure time.

The earlier 689 s and 951 s figures measured the whole 11-test integration
suite. These profiles measure the combined positive development alone and
are instrumented. They diagnose the current evaluator, but do not attribute
the earlier regression to a particular upstream change. That would require
matched profiles of both revisions.

Machine-readable measurements are in [ett-profile.csv](results/ett-profile.csv)
and [ett-costs.csv](results/ett-costs.csv). `profile` denotes the initial timing
runs; `timing` denotes the follow-up build with update probes, equality reset
counters, and table hashes. `primary` is the optional alternate-index
experiment; `alloc` enables the counting allocator. Empty cells mean a metric
was not collected. All nanosecond columns are measured values, not predictions.

### Sparse changes after closure

The update probes use the raw Kernel API. After checking the development, they
create a disconnected `Context` containing `universe()`. They then add two
untyped terms in that context, close that setup, and measure merging just
those terms. There are no morphisms connecting this context to the old graph.
This deliberately removes the legitimate cost of copying a source context or
checking a new declaration.

| Existing development | Update | Closure time | Primary edge visits | Graph builds |
| --- | --- | ---: | ---: | ---: |
| Addition | Unchanged | <1 us | 0 | 0 |
| Addition | Disconnected context | 39.627 ms | 2,455 | 15 |
| Addition | One isolated equality | 17.083 ms | 1,485 | 3 |
| Nat | Unchanged | <1 us | 0 | 0 |
| Nat | Disconnected context | 773.446 ms | 19,410 | 15 |
| Nat | One isolated equality | 313.104 ms | 11,676 | 3 |

The isolated equality causes exactly one inherited-data reset. The new
context causes no equality merges, yet still scans the pre-existing graph.
Thus broad replay occurs both with and without equality invalidation. The
unchanged-model fast path works; it does not provide locality for sparse
updates.

### Alternate-index experiment

In a separate generated copy, replace the seven native alternate-index
rebuilds with `IndexSeed` projections from the already transported primary
`_all` relations. Leave rule code, primary transport, scheduling, and the
theory unchanged.

| Workload | Normal closure | Primary-reuse closure | Time reduction | Graph builds |
| --- | ---: | ---: | ---: | --- |
| Addition | 2.024 s | 1.408 s | 30.5% | 999 -> 188 |
| Nat | 90.251 s | 55.479 s | 38.5% | 2,471 -> 441 |

The normal column is the follow-up timing build, not the earlier 83.295 s
Nat run. That variation is another reason to avoid treating these single-run
ratios as precise speedup estimates. The work counters agree across the two
normal Nat runs. In the paired experiment, alternate-index time drops from
27.008 s to 1.823 s. Primary transport still costs 37.233 s, so this does not
solve the whole problem.

All declarations in both fixtures pass. Every recorded primary relation/type
table has the same cardinality and hash before and after this change; the
CSV `state_hash` aggregates those per-table records. This is useful evidence
for the shortcut, not a general correctness proof or validation for nested
models. The full Vec development was not rerun with the experimental change.
Four temporary negative checks also reject a false equality, a constructor
from the wrong type, equality leaking between contexts, and a reduction beyond
the beta budget. These are development checks, not new permanent unit tests.

A separate counting-allocator run of the normal addition workload records
29,003,399 allocation requests totalling 2,298,980,328 bytes during closure,
against about 18.4 MiB peak RSS. This is cumulative requested traffic,
including reallocation sizes, not live memory. It supports investigating
temporary tree construction and repeated index rebuilding; changing the
allocator itself is not the first priority.

## Why the context graph does not isolate the work

1. `flat_eqlog/scope.rs::infer_scope` makes equality-producing rules global.
   It also requires model-owned premises and conclusions to agree on an owner.
   Ambient dependent signatures alone do not make ambient rules owner-local.
2. `flat_eqlog/schedule.rs::schedule_scope` falls back to global scheduling
   when model rules participate in a dependency cycle through ambient rules.
   ETT deliberately has such cycles: typing enables checked substitutions;
   substitutions transport typing; proofs reflect equalities; equalities
   enable more typing and substitution instances.
3. The resulting evaluator has no `__run_stratum_*_at` methods. Of its 128
   compiled rule groups, 109 are in stratum 5. Functionality and category
   rules are included in those counts. Stratification is enabled, but the
   important stratum is a global fixed point.
4. `rust_gen/stratified.rs::methods` prepares native transport before its
   global stratum's dirty-input check. It can therefore scan the graph even
   when rule inputs will turn out to be unchanged.
5. `rust_gen/mod.rs::display_propagate_model_morphisms_fn` traverses all
   relevant morphisms, scanning source facts and looking up their images.
   Existing destination tuples avoid repeated insertion, but not the work
   needed to rediscover that they are already there.
6. `rust_gen/native_indices.rs::methods` separately starts each alternate
   index from owned facts and transports it through the graph. The main
   stratum does this for five alternate indices: one for `has_type`, two for
   `cons_args`, and two for `identity`. Primary transport already prepared
   the corresponding inherited relations.
7. `rust_gen/mod.rs::display_canonicalize_fn` resets every inherited relation
   to its owned rows whenever any type has uprooted elements. An equality
   local to one context can thus discard transport caches elsewhere. The
   direct time inside canonicalization understates this indirect cost.

The bound of three expansions controls allocation diagrams. It does not bound
fixed-point iterations, transport passes, or the number of call occurrences.
Nat takes 21 allocation rounds and 419 visits to its main stratum. Its final
morphism graph has 3,882 edges, but primary transport visits edges 1,251,352
times. Alternate-index transport is additional work. Its largest strongly
connected component contains two contexts: large graph cycles do not explain
this result.

There is also real input growth. Frontend weakening copies the finite local
material into fresh contexts, and elaboration allocates placeholders that
equality later identifies. Nat starts with 14,283 type members and 8,671 term
members, ending with 831 and 1,638 canonical members. The full input starts
with 47,657 type members and 26,889 term members across 430 contexts. Finite
and isolated does not mean constant work per source declaration. Nevertheless,
the profile points first to repeated engine work on that material.

## Implementation order

### 1. Reuse prepared relations and graph topology

For global strata that already have complete primary transport, construct
alternate indices incrementally from the primary `_all` relation using
`IndexSeed`. Do not independently reconstruct inherited closure for each
permutation. The compiler should express this preparation precondition
explicitly. Model-local traversal can have only a slice prepared; it needs a
separate decision rather than the same unconditional shortcut.

Cache the morphism SCC order by the actual object/domain/codomain snapshots,
including the enclosing owner for nested models. Reuse it across strata and
alternate indices until those inputs change. Do not use cardinalities as
versions. Graph construction is measurable but smaller than tuple transport.

These are bounded changes in `ram/prepare.rs`, `rust_gen/native_indices.rs`,
`rust_gen/stratified.rs`, and the graph preparation runtime. They can help even
while all ETT strata remain global. Compare closures against the existing
evaluator before extending the shortcut to stable inputs or nested models.
Also check destination membership before constructing temporary mapped-prefix
trees where possible. The current transport builds wrappers before discovering
that a tuple is already present. Preserve the owned-support bookkeeping when
moving that check earlier.

### 2. Make primary transport incremental

Maintain consumption checkpoints per relation, owner, and morphism. Transport
new source tuples and changes in the member maps instead of rescanning every
edge on every stratum visit. A work queue should wake only affected transport
jobs; initially it can retain the existing global rule schedule.

There are several independent triggers: source tuple changes, newly defined
member images, graph edges, canonical representative replacement, and changes
propagated into a destination that is itself a source. A late image must join
against old source tuples. Skipping work solely because source facts are
unchanged is incorrect. Partial maps must remain partial; this optimization
must never create missing images of hidden terms.

Start with whole-source-subtree checkpoints for an edge as a conservative
fast path. Then add delta joins for changed facts and image entries. Retain
full recomputation for invalidated regions until the finer dependency scheme
is validated.

### 3. Preserve unaffected inherited data through equality

Use the existing element-occurrence information, extended where necessary for
inherited data, to identify affected relation/owner slices. Canonicalize or
rebuild those slices and propagate their changes downstream. Avoid the global
`_all = _own` reset for a merge in an unrelated context.

This must be designed together with transport checkpoints. Equality can
replace rows and enable joins, so consumers must still see the newly enabled
matches. Owned support must survive cycles and transient conflicting function
results. Ambient relations can contain foreign model members; the affected
owners must follow column ownership, not merely the member's type name.

The simple safe first milestone is retaining unrelated slices while using
the current reset/rebuild behavior inside affected components. Member merges,
model-owner merges, and morphism merges need distinct invalidation paths.

### 4. Schedule ambient feedback by actual owners and morphisms

Once transport is incremental, improve `RuleScope` and scheduling so equality
and ambient dependencies do not force an entire model type into a global
loop. Use owner-keyed tasks for local rules and morphism-keyed tasks for rules
connecting contexts. Global declarations can supply shared inputs without
making every consumer globally active.

This needs runtime dependencies for the actual owner values. A context-local
equality may wake ambient rows referring to its members, then particular
target contexts; it must not be silently treated as having no external
effects. Merely removing the existing global fallback is unsound. Cyclic
dependencies still need a local fixed point, and dynamically introduced
edges must update the work queue.

This is the larger change that should deliver the intended property: adding
one context costs its new material and the consequences reachable from it,
rather than a pass over every old context. Keep the one-call `close()` API.

### 5. Re-profile before changing matching or allocation policy

Rule joins, candidate deduplication, and non-surjective allocation barriers
may matter after transport costs fall. Count matches and newly inserted facts
before optimizing a particular rule. Moving allocations into local work queues
could reduce global waves, but eager allocation can also create more temporary
witnesses before equality collapses them. Treat that as a separate experiment.

Frontend placeholder reuse may reduce input size, but should not be the main
fix. Do not trade away fresh contexts, equality reflection, partial images,
or the bounded computation policy to obtain a faster benchmark.

## Validation and benchmarks

Add small scaled workloads to the existing scheduling benchmark harness, with
executing integration coverage. They should combine model-local equality,
ambient dependent rules, and partial morphisms; the existing model-chain
fixtures do not reproduce this combination.

Measure initial closure, unchanged closure, one new disconnected context, one
new weakening edge, one late member image, and one equality in a disconnected
context. Scale the pre-existing graph while keeping each update fixed. Record
edge visits, tuples or batches transported, graph reconstructions, allocation
traffic, and canonical relation sizes as well as wall time.

Correctness cases include equality enabling a previously impossible join,
late partial images, independent contexts, cycles with owned support, nested
models, foreign members of ambient relations, model-owner merges, conflicting
function results, and interrupted `close_until`. Compare optimized and
reference closures. Keep the existing ETT positive and negative integration
checks. Run full Nat+Vec manually for performance validation rather than
adding another redundant long-running unit test.

The success criterion is proportional work on sparse updates, not a promised
millisecond target. The initial target is eliminating repeated secondary
transport and reducing unaffected edge visits toward zero. The full workload
then checks whether those improvements survive the combined theory.

## Reproduction

`profile-ett.py` is a diagnostic for this generated kernel shape, not a stable
profiling API. It fails if the expected shape changes. After a normal Cargo
build, it instruments only copies in the chosen output directory. Production
source and generated evaluator files are not patched. It requires Python 3
and the existing Rust toolchain.

```sh
python3 eqlog-bench/profile-ett.py /tmp/ett-timing
/tmp/ett-timing/profile eqlog-ett/nat.ett > /tmp/nat-profile.csv
/tmp/ett-timing/profile eqlog-ett/nat.ett eqlog-ett/vec.ett > /tmp/full-profile.csv
ETT_PROFILE_UPDATES=1 /tmp/ett-timing/profile eqlog-ett/nat.ett > /tmp/updates-profile.csv
python3 eqlog-bench/profile-ett.py /tmp/ett-primary --reuse-primary
/tmp/ett-primary/profile eqlog-ett/nat.ett > /tmp/primary-profile.csv
python3 eqlog-bench/profile-ett.py /tmp/ett-alloc --allocations
```

To reproduce the small fixture, take `nat.ett` up to, but not including, the
line beginning `theorem congr_succ`. Run the allocation executable on that
file; `ETT_PROFILE_UPDATES=1` also measures allocations in the update phases.

The raw output uses tagged CSV rows: `metric,name,calls,inclusive_ns,
exclusive_ns,counter`, `rows,before_or_after,table,count,hash`, and graph or
phase records. Hashes cover the recorded primary trees, including owned and
inherited variants and canonical type-element sets; they do not serialize the
entire union-find representation. The output directory also records the code
revision, compiler version, generated-source SHA-256, and diagnostic options.

The optional `--reuse-primary` build is a diagnostic ablation, not a proposed
production implementation. The optional `--allocations` build counts requested
allocation bytes during `close()`; use separate runs because the allocator
instrumentation changes timings. Neither allocation traffic nor propagated
batch counts represents live memory or distinct facts.
