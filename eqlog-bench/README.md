# Member propagation benchmarks

This suite compares generated native Eqlog evaluators with explicit Rust
copy-on-write propagation. Every graph is acyclic. All morphisms, local elements,
input rows and root marks are inserted before the timed operation: one populated
`close()` for Eqlog, or one topological sweep for COW. Every model snapshot is
retained.

The Eqlog programs live in [theories/](theories/). Cargo generates their evaluators
using the compiler and runtime in this checkout, in native semi-naive mode.
The native fixtures enable compact member storage and total member inheritance.
No generated evaluator, input dataset or historical binary is needed to run them.

## Cases

| Case | Workload |
| --- | --- |
| `chain-plain` | Eight root seeds and one owned output per model. A randomly chosen inherited marked input causes the local output to be marked. |
| `chain-equation` | The same jobs also identify two distinct inherited equivalence classes. |
| `dag-forward` | Each model chooses up to `parents` earlier models; rules may require inputs from two parents. |
| `dag-layered` | Random parents from the preceding layer, with `width` models per layer. |
| `dag-wide` | A root branches into siblings, all of which feed a final sink. |
| `dag-comb` | A chain with an additional edge from the root to every later model. |
| `dag-chain` | A chain control using the DAG program and shuffled output keys. |
| `join-fanout` | Many children inherit complete grouped products from independent parents with distinct groups. |
| `join-overlap` | Parents share two groups, requiring new cross-parent products. |
| `join-split` | Parents share one group but supply alternating left-only and right-only inputs. |
| `join-diamonds` | Repeated branching and merging, with fresh left/right inputs on branches. |
| `join-layered` | Random parents from the preceding layer; new inputs reuse groups. |
| `join-comb` | Root products propagate down a chain with redundant root edges. |
| `join-chain` | Root products propagate down a single chain. |

The chain and DAG programs use `item(Key)` to name corresponding members across
paths. Functionality identifies coincident images at merges. The grouped-join
program derives `pair(g, x, y)` from `left(g, x)` and `right(g, y)`, so it separates
already completed inherited matches from genuinely new cross-parent matches.
Every grouped-join model also owns a spare named element.

The source modules contain the input generator, native adapter, COW reference,
and independent oracle for each group:

- [chain/](src/chain/): plain and equation chains; COW uses a persistent partition.
- [dag/](src/dag/): DAG propagation; COW checks functionality collisions by probing
  the smaller input map.
- [join/](src/join/): grouped joins; COW shares Cartesian-product suffixes and
  derives only products absent from the completed inputs.

## Running

Run all cases, or select a case and size:

```sh
cargo bench -p eqlog-bench --bench member_mapping
cargo bench -p eqlog-bench --bench member_mapping -- --case chain-equation --vertices 1024 --samples 5
cargo bench -p eqlog-bench --bench member_mapping -- --case dag-forward --vertices 512 --parents 4 --seed 91
cargo bench -p eqlog-bench --bench member_mapping -- --case join-fanout --vertices 128 --parents 32 --members 64
```

Use `--help` for all options. `--case` accepts a comma-separated list.
`--engine native` or `--engine cow` selects just one engine. By default, both
engines receive the same immutable input, and their execution order alternates
between samples. There are no discarded warmups. Each sample constructs a fresh
engine and closes it once.

`vertices` counts all models, including roots. `parents` is the requested fan-in,
limited by available predecessors; it does not change fixed graph shapes.
`members` controls the grouped-join root seeds. `seed-mask` is a decimal mask for
the eight initial marked seeds in the chain and DAG cases; `255` marks them all,
`0` marks none, and `85` is a partial-propagation control. It has no effect on
grouped joins.

Standard output is CSV with one row per engine and sample. It records all input
parameters, graph size, locally introduced elements, `local_size`, closure time
in nanoseconds, and a semantic checksum. `local_size` counts owned elements and
member function/predicate rows first introduced at each model, before quotienting.
It excludes inherited copies, automatic membership rows, morphism-image rows,
and global control predicates. It is a logical contribution count, not bytes of
retained memory.

Input generation, construction, full output verification and destruction are
outside the timer. Verification checks actual elements, equality classes,
relations and morphism images against an independent oracle; agreement of the
printed checksum alone is insufficient. The oracle enumerates logical inherited
contents, so large runs can spend much longer verifying than closing. Total wall
time and process RSS are not measurements of closure time or retained storage.

Allocation traffic can be measured in a separate run:

```sh
cargo bench -p eqlog-bench --bench member_mapping --features allocations -- --case chain-plain --vertices 1024
```

This replaces the timing column with allocation calls and allocated bytes during
closure. It does not measure retained or peak memory, and allocator instrumentation
is disabled in ordinary timing runs. Pin the process to an otherwise idle CPU
when collecting comparable timings; the runner does not control machine load.

## Correctness and provenance

```sh
cargo test -p eqlog-test-eval --test member_benchmarks
```

The integration tests execute both engines, check every family against its oracle,
exercise short graphs, partial/inactive marks and larger fan-in, and verify closure
idempotence. The native benchmarks always use native semi-naive compilation,
independently of features selected for the surrounding test crate.

These sources replace the older synthetic scheduling benchmark. They were promoted
from the temporary one-close chain/DAG and grouped-join experiments. The seeded
Rust generators preserve the workload definitions, but do not reproduce the old
Python generators' exact random samples. Record the source revision and CSV
parameters when comparing results; historical timings need fresh baselines for
these inputs.

Existing files in [results/](results/) and [ett-performance.md](ett-performance.md)
are historical measurements with their own provenance. They are not outputs of
this runner or measurements of the current checkout. [profile-ett.py](profile-ett.py)
remains a separate diagnostic for the ETT evaluator.
