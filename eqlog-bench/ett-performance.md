# ETT evaluator investigation

The historical tables preserve the baseline investigation at
`8991f586ba5e9288e663f2d9fba6ea144716e031`, after merging `host/master` at
`895e9a7`. They are historical measurements, not timings of the optimized
implementation described later in this report.

The baseline spent most closure time transporting existing facts and preparing
indices. Model isolation was semantic, but its 17 global strata did not make
small changes cheap. The first optimization round cached prepared data and propagated
changes within that global schedule. A functionality normalization barrier
splits the main component into separate consumers; that version of the ETT evaluator
had 18 global strata. The subsequent scheduling work is described below.

The Nat and Vec source modules, fresh contexts, equality reflection, partial
morphisms, three-expansion budget, and single `close()` call are unchanged.
All closure timings exclude Rust compilation.

## Commit milestones

These are end-to-end runs of the unchanged 52-declaration Nat+Vec
development, excluding Rust compilation and instrumentation. They are
historical observations on this machine; host variation prevents treating
small differences as precise speedups.

| Implementation commit | Recorded time | Milestone |
| --- | --- | --- |
| `b23fca3` | 50.180-56.077 s | First below one minute; results recorded in `8dfa987`. |
| `676d1e6` | 21.980 s | Recursive normalization and local transport scheduling. |
| `22a2b1d` | 20.466 s | Constrained joins and ordinary iteration. |
| `a7cf045` | 17.283 s | Inline singleton suffixes and shared intersections. |
| `2c019b4` | 16.804 s | Unary index operations exposed across component crates. |
| `8da252e` | 14.846 s | Shared historical inputs and selective join probes. |
| `bd48d1c` | 13.598-15.431 s | Borrowed difference traversal and publication caching. |
| `f3a494a` | Final combined timing pending | Validated residual joins and direct transport borrowing. |

Optimization is paused at `f3a494a`; the five-second target is unmet.
That checkpoint passed 283 evaluator library tests, nine four-mode
optimization oracles, 12 focused four-mode checks, and 49 combined native
checks. Independent reviews approved correctness and general applicability.
Separate candidate runs reached approximately 12 seconds, but they do not
establish a final combined performance milestone. Unpromoted experiments
remain outside the branch.

## Owner-scoped scheduling checkpoint

The following schedule refinement saturates each self-recursive global group
and runs the shared functionality normalizer between its passes. Plain
per-group commits regressed Nat to 26.459 s and 508.2 MiB peak RSS; normalizing
between recursive passes reduced Nat to 4.604 s and the full development to
22.947 s end to end. The diagnostic full run used 374 model traversals instead
of 762, with 24.040 s total elapsed time including instrumentation.

Eligible leaf models now interleave local rules and outgoing transport rather
than preparing their full primary closure before traversing owners. Initial
frontier work and immutable entry snapshots cover changes before and during
the traversal. Staged frontiers commit only after visiting every component;
later changes to an earlier owner remain pending for the next pass. This
measured 4.319 s for Nat and 22.377 s for Nat+Vec without instrumentation.
Sharing identical join prefixes and grouping functionality lookups by domain
gave a subsequent full result of 21.980 s. All 41 focused generated-evaluator
checks passed again. Independent reviews approved the scheduling, traversal,
functionality indexing, prefix sharing, and inline difference cursor changes.
These results remain above the five-second target; broad final validation is
still pending.

Prioritizing bound join keys after cheap function lookups, together with an
identity fast path for unmapped tree iterators, measured 3.858 s for Nat and
20.466 s for Nat+Vec. Both changes passed independent static review. All nine
optimization-oracle tests pass across naive/semi-naive and native/desugared
evaluation, including late equalities, partial images, and circular graphs.

Inline singleton suffix sets reduced the full run to 18.451 s and peak RSS
to 245.3 MiB. Direct structural intersection of persistent snapshots then
measured 17.283 s with the same peak memory. Both preserve shared subtrees;
intersection avoids constructing removed rows merely to subtract them again.
Independent reviews approved both runtime changes. The 13 prefix-tree and
nine relation-version checks passed, alongside temporary randomized set and
version-consumer comparisons. All 52 source declarations remain unchanged.

Four inline annotations expose unary suffix iteration and membership to
generated component crates. A same-core comparison measured 16.804 s for
this variant, with baseline results of 19.991 s and 18.743 s. Earlier
unpinned runs of the same variant varied from 15.877 s to 18.642 s, so small
differences between individual experimental runs are inconclusive. Broader
inlining and adaptive joins at every eligible loop remain unpromoted.

Historical rule inputs now retain their shared snapshots. Iterators reject
noncanonical keys before binding them, including at every suffix of an ALL
scan and before selecting a functionality representative. NEW inputs still
contain equality-enabled tuples; old aliases are never remapped into them.
Private existential witnesses need no canonical binding. This removes the
materialized intersection needed for most OLD inputs.

The compiler can also reverse a join when an already available membership
guard supplies fewer candidate keys. It compares constant-time upper bounds,
retains the original guards, and preserves both input-age multiplicities.
Complete function-result lookups and the initial delta seed keep their original
traversal. A diagnostic category join avoided over nine million key visits;
most function-result sites never benefited from the broader experimental pass.
The narrowed candidate measured 17.176 s against 18.734 s for the preceding
production version in a sequential same-core pair.

Ordinary tree lookup now avoids mapping state until it encounters a mapping.
Tuple insertion updates suffixes during one tree descent, avoiding repeated
searches through the entry API. Together with canonical filtering and narrowed
adaptive joins, the full development measured 14.846 s end to end with all 52
declarations checked. The compiler changes passed nine four-mode optimization
oracles, 281 evaluator library tests, and 17 focused integrations. The runtime
changes passed existing runtime and prefix-tree checks plus temporary mapped
and snapshot differential checks. Independent reviews found no correctness or
ETT-specific assumptions in these mechanisms. Final combined validation and
further work toward the five-second target remain.

Allocation sampling on the preceding version found approximately 28.5 million
allocation requests. Difference cursors were a substantial source, but adding
inline cursor storage made the tested traversals slower despite reducing
allocations; that experiment is not included.

A borrowed difference visitor now walks ordinary trees without a temporary
cursor stack, preserves early termination and shared-subtree cancellation,
and retains the existing cursor for mapped roots. Materialized differences
retain unchanged roots, including when tuple prefixes overlap but suffixes
are disjoint. Repeated publication of an equal rebuilt tree remembers that
source root instead of comparing it again. Necessary root-emptiness guards
also move ahead of restricted joins.

Sequential same-core runs checked all 52 declarations in 13.598 s and
15.431 s with these changes. The preceding version took 16.852 s in this
comparison; the new guards and cache without the visitor took 14.656 s.
Host variation remains visible, so these measurements do not establish a
precise speedup. The combined runtime passed 55 tests, 14 prefix-tree checks,
and nine version checks. The compiler guards passed the nine optimization
oracles and three focused cases in each of four evaluator modes. Independent
review found no correctness blocker or application-specific assumption.

The next engine changes retain owner-scoped rules inside ambient cycles,
including ordinary member equalities. Global saturation still revisits the
owner traversal when cross-owner facts change. Alternate indices reuse the
prepared primary slices, and an immutable traversal-entry snapshot suppresses
unchanged edge transport. These retain the existing evaluation semantics.

An instrumented full run with input, output, and transport detail measured
28.965 s in closure and 30.255 s end to end, with 328.2 MiB peak RSS. All 52
declarations passed; the graph still has 397 SCCs and closure uses 41 allocation
rounds. This improves the earlier 50-56 s result but does not meet the current
five-second target. These are diagnostic timings, not an uninstrumented result.

The changes also narrow inherited equality rewrites, reuse SCC partitions
under conservative topology checks, preserve shared input subtrees, and batch
duplicate outputs. Imported models use full equality rewriting because their
dependent ownership facts can be incomplete. Independent review exposed the
conflicting-endpoint and import cases; all 41 focused evaluator checks pass,
including the resulting regressions. Broader final validation remains pending.

## Optimized results

Measured production source: `b23fca3`. Both uninstrumented runs checked all 52
Nat+Vec declarations in one `close()` call: **56.077 s and 50.180 s end to end**.
These times include parsing, elaboration, checking, and CLI output, and exclude
Rust compilation. They meet the one-minute target on this machine; individual
runs still vary appreciably.

The separately instrumented profiles give the following closure times and
whole-process peak memory:

| Workload | Baseline `close()` | Optimized `close()` | Baseline peak RSS | Optimized peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Nat | 83.295 s | 6.424 s | 120.6 MiB | 94.5 MiB |
| Nat + Vec | 841.025 s | 50.401 s | 618.7 MiB | 306.2 MiB |

The full profile attributes 5.563 s to primary transport, down from 417.312 s,
and 1.868 s to alternate indices, down from 273.647 s. Remaining costs include
17.595 s in rule matching, 12.629 s in canonicalization, 4.247 s in graph
preparation, and 8.385 s in other evaluation work. Direct canonicalization is
more expensive than in the baseline, but it preserves inherited data instead
of forcing the much larger transport replay. Candidate transport batches fell
from 374,970,808 to 6,744,029.

After Nat is closed, an unchanged close takes 221 ns, a disconnected-context
update takes 2.559 ms, and an isolated equality takes 2.252 ms. Both nontrivial
updates perform zero primary edge visits; their baseline times were 773.446 ms
and 313.104 ms. These remain globally scheduled updates, with some graph and
canonicalization work, rather than constant-time operations.

The final canonical context, morphism, type, and term counts match the baseline
for both developments. The full graph still has 397 SCCs and the same 41
allocation rounds. Representative IDs may differ, so raw tuple hashes are not
used as cross-revision correctness checks.

The [optimized profile summary](results/ett-optimized-profile.csv),
[exclusive costs](results/ett-optimized-costs.csv), and
[build and measurement metadata](results/ett-optimized-metadata.json) record
these results. Profile times and the two CLI process times are separate rows.
The profiler was built on base revision `cf3e93d` before the measured production
changes were committed as `b23fca3`; metadata records both identities and the
generated-source and runtime hashes.

## Historical baseline measurements

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
are instrumented. They diagnose the baseline evaluator, but do not attribute
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

## Why the baseline did not isolate the work

The following describes the baseline code paths and counts. Several of these
paths have since been replaced, as detailed below.

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

## Implemented mechanisms

### Prepared primary relations and graph caches

The compiler records when a global stratum has completed primary transport.
Eligible alternate native indices are then maintained by `IndexSeed`
projections from that primary relation, rather than by transporting the same
facts again for each column order. Model-local preparation retains its previous
path because a prepared slice is not a complete relation. Copy-only transport
also retains its sharing-preserving path: permuting every row would discard
shared suffixes without avoiding member-map joins. Support indices used only
by replaced transport paths are removed from the preparation plan.

`MorphismGraphCache` caches SCC order by persistent object, domain, and codomain
snapshots, separately for each enclosing owner tuple. It never uses row counts
as versions. Cached graphs also share their sorted edge signatures, including
whether an edge is internal to an SCC. Equal signatures can survive a snapshot
change with the same shared identity, keeping per-relation comparisons cheap.
Nested graph preparation includes visible endpoints without asserting new
model membership.

### Incremental primary transport

A `TransportCheckpoint` records the source subtree and partial member maps for
a relation, enclosing owners, morphism, domain, and codomain. New source facts
join the current maps. Newly available images join old source facts, so a late
image can enable transport even when the source relation is unchanged. Map
changes are partitioned by their first changed column to avoid repeating the
same combination. No path allocates a missing image of a hidden term.

Relation-specific `TransportFrontier` records identify changed source owners,
changed maps, and newly added edge signatures. A source or map partition needs
work only when it contains tuples absent from its previous snapshot; removing
equality aliases alone cannot enable a join. Only active relation/edge
combinations perform transport; an insertion activates the destination for
downstream work. The graph remains traversed in SCC order, with a fixed point inside
cycles and owned support retained where cyclic inheritance requires it. After
that pass saturates, the frontier records the resulting relation, avoiding a
second pass over its own output on the next preparation call.

The fast frontier applies to leaf model graphs with supported owner-prefix
indices. Nested model traversal and unsupported primary orders keep the
conservative traversal. The initial graph and changes to owned-support retention
force a full pass. Other graph changes activate newly present signatures,
including edges whose classification as internal to an SCC changed. Per-edge
checkpoints replay the source when that edge's retention mode changes. Removed
edge aliases need no replay: source, map, graph, and target facts must grow or
undergo the same equality quotient. These caches do not support arbitrary
destructive edits. Checkpoints whose owner or morphism keys cease to be canonical
are pruned.

### Equality preserves inherited snapshots

Canonicalization rewrites existing inherited tuples to current representatives
instead of resetting every inherited relation to its owned rows. Transported
facts remain valid under the equality quotient. Rewriting every relevant column
also handles ambient relations containing foreign model members; it does not
assume that only the first owner column can change. Owned-support bookkeeping
continues to protect cycles.

`PrefixTree::replace_keys` uses sparse replacement maps. Unchanged subtrees
retain their roots, and a per-call cache rewrites a shared subtree only once.
The cache keeps source snapshots alive so pointer identities cannot be reused
during the call. Moved keys are removed and stationary subtrees overwritten
before incoming replacements are merged. At the last affected column, traversal
chooses between replacement keys and subtree keys using a constant-time size upper
bound; querying the exact length of a lazy mapped tree could itself scan it.
Changed indices are invalidated, and the normal consumer snapshots expose newly
canonical tuples to rule evaluation.

### Normalize functionality before larger joins

A structural matcher recognizes the two-application rule expressing function
uniqueness. Its second result loop chooses one representative while the first
loop still visits every new result. The representative is chosen from old
results before new ones: choosing a new result itself could fail to connect it
to an existing value. This gives a linear equality star for each domain without
relying on rule or function names.

In a mixed recursive global component, functionality groups saturate before
other rule groups run. The original outer fixed point and model-child traversal
remain, so equalities enabling other rules still feed back into functionality.
The two groups have independent consumer checkpoints, and stable inputs are
classified using the original SCC before partitioning. Allocation requests
remain behind the existing allocation barrier; `close_until` can still stop
and resume between completed steps. Model-local scheduling is unchanged.

Empty-conclusion flat rules are discarded before semi-naive expansion, and
reflexive equality outputs are omitted. The RAM scheduler reconsiders ready
statements after each selection so newly enabled guards can run before another
loop expands the branch. These changes preserve the original data dependencies.

### Avoid iterator and build-cache overhead

Immutable weight-balanced-tree iteration stores mapping depths rather than
cloning a mapping vector at every node. Nodes without a left child yield
directly, avoiding an ancestor-stack allocation for singleton suffixes. Mapping
prefixes remain valid until the corresponding ancestor is popped, including
for filtered and nested lazy mappings.

Component-build cache keys now include runtime library contents, compiler
identity, optimization level, and debug mode. Reusing an rlib path after its
contents changed must not leave rule components linked against stale runtime
code. This is necessary for correct builds and performance comparisons; it
is separate from evaluator closure time.

## Validation and benchmarks

Correctness is checked by executing generated evaluators. Coverage includes
late partial images, disconnected contexts, graph growth and cycles, nested
models, foreign members, owner and member equality, shared inherited suffixes,
conflicting function results, and interrupted `close_until` followed by resume.
The functionality barrier is exercised with equalities cascading through
function domains and a deferred allocation. Existing ETT positive and negative
checks retain the unchanged Nat and Vec developments.

Final validation at the measured source passed:

```sh
cargo test --release -p eqlog-runtime -p eqlog-test-compile -p eqlog-test-eval -p eqlog
cargo test -p eqlog-test-opt
cargo test -p eqlog-test-eval --features naive,desugared \
  --test functionality_star --test functionality_barrier \
  --test prepared_mapped --test prepared_native
```

The release run passed 483 tests, with two existing documentation examples
ignored. This includes all 11 ETT tests; that test executable finished in
59.51 s. The optimization suite passed nine tests comparing all four
naive/semi-naive and native/desugared combinations. The final command passed
six focused cases; native-only cases are disabled in desugared mode.

Temporary differential checks compare tree rewrites, partial-map delta joins,
and lazy iteration against ordinary set/map or direct traversal semantics.
These development probes are not additional permanent unit-test suites.
Independent reviewers examine the generality and correctness of the transport,
scheduling, and runtime mechanisms separately from benchmark results.

Two reviewers started without the parent conversation context. Their final
reviews found no blocking correctness issue or ETT-specific compiler/runtime
heuristic. Temporary differential checks included 64,000 transport updates,
with partial endpoints, typed quotients, cycles, and reconstruction from owned
support, plus 10,000 ordinary and lazy tree rewrites. These checks supplement
the generated-evaluator integration tests; they are not a formal proof.

Performance runs should be sequential and repeated. Measure initial closure,
unchanged closure, a disconnected context, late images, graph changes, and an
isolated equality. Compare wall time alongside transported batches, active
edge visits, allocation traffic, and final canonical cardinalities. A sparse
update should avoid replaying unrelated relation/edge combinations; global
rule scheduling and conservative nested fallbacks can still do wider work.

Current `graph_preparation` metrics include cache lookups and occasional graph
reconstruction. Their call count is not a graph-build count and must not be
compared directly with the historical `Graph builds` columns. Current primary
edge counters exclude wrapper calls; older instrumentation included them, so
edge-count comparisons must account for that correction. Candidate outputs and
transport batches remain counts of attempted work, not unique new facts.

The functionality schedule can change which element represents an equality
class. Raw tuple hashes therefore need not match the baseline even when the
models agree. Compare canonical cardinalities and observable proof-checking
results, and use correspondence-aware comparisons where identities matter.
Equal cardinalities alone are not a correctness proof. Optimized measurement
artifacts above record the exact build metadata separately from test validation.

## Reproduction

`profile-ett.py` is a diagnostic for this generated kernel shape, not a stable
profiling API. It discovers the current global strata and instrumentation
methods, and fails if required generated structures are missing. It first
builds the release evaluator, then instruments only copies in the chosen output
directory. Production source and generated evaluator files are not patched.
It requires Python 3 and the existing Rust toolchain.

```sh
python3 eqlog-bench/profile-ett.py /tmp/ett-timing
/tmp/ett-timing/profile eqlog-ett/nat.ett > /tmp/nat-profile.csv
/tmp/ett-timing/profile eqlog-ett/nat.ett eqlog-ett/vec.ett > /tmp/full-profile.csv
ETT_PROFILE_UPDATES=1 /tmp/ett-timing/profile eqlog-ett/nat.ett > /tmp/updates-profile.csv
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

The optional `--reuse-primary` flag reproduces the historical ablation on the
baseline revision. It rejects current generated code because eligible primary
reuse is already compiled in. The optional `--allocations` build counts requested
allocation bytes during `close()`; use separate runs because the allocator
instrumentation changes timings. Neither allocation traffic nor propagated
batch counts represents live memory or distinct facts.
