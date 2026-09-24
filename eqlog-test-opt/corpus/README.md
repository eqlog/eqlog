These initial cases were authored by Codex for this suite. Cargo automatically
includes every `.eql` file in this directory in all four configurations.
Each paired `.json` trace forces the scenario described below before the
random traces run. `witness_join.json` merges generated witnesses before
inserting the gate; `transport.json` adds a morphism after facts have aged,
then supplies new facts and merges target images across later closures.

| Case | Features to combine | Why it is finite |
| --- | --- | --- |
| witness_join | Function-created witnesses, equality joins, delayed nullary gates, recursive reachability | Only Key -> Value creates elements; no rule creates Keys |
| transport | Member joins, diagonals, partial functions, ambient arguments, transported facts, observed target models | No ordinary witness creation; image creation follows the trace's acyclic morphisms |

For an LLM generation batch, give the model the Eqlog syntax, this table, the
trace generator's supported signature fragment, and an explicit novelty brief.
Draw that brief independently from a feature matrix: joins (chain, diamond,
disconnected, diagonal), equality (premise, conclusion, function collision),
scope (flat, member, ambient argument), creation (none, acyclic function
dependencies, morphism image), and scheduling (facts before morphisms,
morphisms before facts, late equality, repeated close). Choose combinations
missing from the existing corpus. Randomize names and declaration order only
after choosing a structurally new case; renaming alone is not diversity.

Suggested prompt:

```text
Produce one small valid Eqlog theory for differential optimization testing.
Target this feature combination: <independently sampled combination>.
Here are the existing cases and their features: <table and source examples>.
Explain a structural difference from every existing case. Explain why closure
terminates on finite inputs with acyclic model morphisms. Use only plain types,
top-level models, their plain members, predicates, and ordinary functions;
member relations may also mention top-level plain types. Do not create or
equate models or morphisms in rules. Prefer a small interaction that becomes
observable when facts or equalities arrive after an earlier close(). Supply
an example operation sequence that reaches that interaction. Do not use an
existing case with only different names.
```

Review validity, the termination argument, and the suggested triggering trace
before retaining a case. Run many random inputs and preserve any useful
explicit trace as a reproduction. Keep a short feature/termination entry in
the table. Reject exact duplicates and inspect structural duplicates manually;
the current suite does not claim automatic novelty scoring or coverage-guided
corpus selection. A larger campaign should track exercised rule/operation
features and retain cases that add coverage, not simply more generated text.
