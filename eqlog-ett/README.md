# Extensional type theory with partial substitutions

Run the proof checker from the repository root:

```sh
cargo run --release -p eqlog-ett -- eqlog-ett/nat.ett eqlog-ett/vec.ett
```

Use a release build. The kernel is compiled as a desugared Eqlog model, which
stores the facts transported along substitutions explicitly. Closing uses up
to eight threads; set `EQLOG_THREADS=1` to check sequentially.

Run the checker integration suite with:

```sh
cargo test --release -p eqlog-test-eval --test ett
```

`nat.ett` defines addition, predecessor, and multiplication. It proves the
zero and successor laws, successor injectivity, commutativity, associativity,
both distributive laws, and rearrangement lemmas. The statements follow Lean's
[Init.Data.Nat.Basic](https://github.com/leanprover/lean4/blob/master/src/Init/Data/Nat/Basic.lean).
The checker has no built-in natural numbers or arithmetic equations.
`vec.ett` declares `Vec A n`, defines replication, append, successor mapping,
and sum, and proves laws relating these operations. Append associativity uses
an explicit length equality to reindex its result. Both files are elaborated
together and checked by one `close()` call.

The input language has `inductive`, `def`, `theorem`, explicitly typed
parameters, equality types, `rfl`, and typed `let` statements. `by rfl` and
`by exact term` are also accepted. Inductive declarations have explicit uniform
parameters, index telescopes, and dependent constructor fields. Recursion must
be directly through the declared family with unchanged parameters; nested and
mutual inductives are not supported. There are no Pi types, implicit arguments,
tactics, or general recursive definitions.

```text
inductive Nat where
| zero
| succ (pred : Nat)

def add (m n : Nat) : Nat :=
  rec n motive (k : Nat) => Nat with
  | zero => m
  | succ k ih => Nat.succ ih
  end
```

`rec` has an explicit motive, with one branch per constructor. Each branch
binds the constructor's fields in order, with an induction hypothesis
immediately after each recursive field. The hypothesis uses the motive at
that field's own indices.

```text
inductive Vec (A : Type) : (n : Nat) -> Type where
| nil : Vec A Nat.zero
| cons (k : Nat) (x : A) (xs : Vec A k) : Vec A (Nat.succ k)

def sum (n : Nat) (xs : Vec Nat n) : Nat :=
  rec n, xs motive (k : Nat) (zs : Vec Nat k) => Nat with
  | nil => Nat.zero
  | cons k x tail ih => add ih x
  end
```

An indexed recursor supplies its indices before its scrutinee. The motive
binds these indices and then an element of that fiber. Beta requires the
constructor's parameters and return indices to match: equality of two family
fibers does not imply equality of their indices.

`Type` marks a fresh type parameter: `(A : Type)` extends the context by an
abstract type, and `(x : A)` then extends it by a term of that type. Passing
`Nat` for `A` substitutes a type directly. There are no universes, type codes,
or decoding operations. `Type` is not itself a type or a term; definitions
cannot return it, and types cannot occur as endpoints of a term equality.
Only uniform parameters and definition/theorem parameters may bind fresh
types. Inductive indices and constructor fields must have ordinary types.

`let` statements can begin declaration and branch bodies. Each records a
typing obligation before making its annotated value available to subsequent
expressions. Numeric literals and infix arithmetic are not implemented;
constructors use qualified names.

## Contexts and checking

Each scope is an instance of the `Context` Eqlog model in `src/kernel.eql`.
Types, terms and equalities belong to that model. A context extension remains
fresh even when its parent and binder type agree with another extension.
Weakening maps material into later scopes; equality cannot flow back into
the earlier scope.

The frontend constructs contexts, types and substitutions without waiting for
positive well-formedness judgments. Obligations are facts in the Eqlog model:
`types_should_be_equal` records required type equalities, and
`terms_should_be_equal` records required term equalities. The frontend records
type obligations for arguments, bodies, equality endpoints, and index binders.
Eqlog derives term equality obligations from `reflexivity_goal` facts during
closure. These predicates do not assert the equalities they require.

The frontend continues under the declared typing assumptions and calls
`close()` once. Rust then queries the obligation relations, checks their
equalities, and checks that each reflexivity goal has an equality type.
Rust retains only source positions and messages for these obligations. It
reports the first failure in source order, including deferred failures before
later elaboration errors. Obligation relations live outside `Context` so
substitution does not transport them into scopes with additional assumptions.

Inferred types are recorded separately from assumed typings. The kernel's
`has_type` relation is not functional: adding an expected typing cannot
identify two types and thereby satisfy the obligation that compares them.

An inhabitant of an equality type identifies its endpoints in its context;
equality proofs are proof irrelevant. An assumption that can introduce such
equalities belongs to a fresh continuation context after its obligation.
Abstract types are treated conservatively because a type parameter might
later be instantiated with an equality type. Calls also isolate proof
assumptions made inside their defining bodies. Ordinary data-typed
applications can share a context.

Consequently, a later `let` assumption cannot rescue an ill-typed application
in an earlier declaration header. Put a required equality proof before the
application it justifies. Recursor branches use a motive template without
an assumed result; the result is introduced separately so it cannot validate
its own branch obligations.

Morphisms have the direction of substitution: a variable extension has a
weakening `Gamma -> Gamma.x:A`. `pair` and `pair_type` instantiate the last
term or type variable after the relevant obligations have been recorded.
`advance` adds a scope without a variable, and `context_parent` records
ancestry. `closed_context` and `variable_context` describe that ancestry,
rather than certifying well-formedness; a context without local variables has
a unique substitution to a fixed target. Identities and composition use
Eqlog's native `id` and `>>`. `restrict_to_parents` requests restriction of
selected substitutions through their finite source ancestry. Branch-body
composites are requested only after the branch substitution has endpoints.

The frontend is part of the trusted checker. It resolves lexical names,
constructs motives and branch obligations, records inferred types, and places
assumptions after the obligations on which they depend.

## Open definitions and finite computation

Definitions are open. Instantiating a signature explicitly creates its types
and terms in the destination context. Substitution on the defining body stays
partial: requesting an image of `foo`, where `foo = bar + baz`, does not
allocate images of `bar` or `baz`. Existing destination expressions can supply
missing images through surjective rules. Weakening creates images on demand
for referenced values and their written syntax dependencies, including their
types. It also preserves the syntax of in-scope equality assumptions, whose
consequences can matter even when their proof variables are unused. It does
not copy all the material from the parent scope.

Constructor computation is a separate, bounded allocation mechanism. Each
elaborated call occurrence, including occurrences in instantiated signatures,
gets a finite chain of three expansion steps. A step opens one constructor case
and may request the recursive call and the branch result. It does not copy
hidden branch subterms. Recursive calls and calls at the head of a branch
consume the remaining chain. Immutable call descriptors keep a branch that
returns its recursive result from restarting its fuel after equality merging.
Merely weakening a term does not reset its budget. Equality saturation on the
resulting material has no step limit.

The bound counts the terminal constructor case too: reducing `add m (succ
(succ zero))` to `succ (succ m)` needs three steps. Additional written
intermediate expressions can supply more computation. Distinct literal roots
may become equal and share results, so this is a bound on allocated expansion
diagrams, not a global normalization-depth bound. A failed obligation means
the finite diagram did not establish the type, not that the statement is false.

An eliminator captures the shortest existing context prefix containing its
free variables. This avoids capturing an unused scrutinee parameter, so a
recursive call in `add m (succ n)` agrees with the written term `add m n`.
The scope instances themselves remain fresh.

Integration coverage lives in `eqlog-test-eval/tests/ett.rs`. The design follows
the partial-model approach discussed in
[The type-theoretic case for Datalog](https://www.mbid.me/posts/datalog-for-type-theorists/)
and the former `exp-epa` experiment, with model-local equality and a single
closure replacing its evaluate/define loop.
