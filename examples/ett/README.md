# Extensional type theory with partial substitutions

Run the example from the repository root:

```sh
cargo run --release -p eqlog-ett -- examples/ett/nat.ett examples/ett/vec.ett
```

Use a release build: the full development currently takes minutes to saturate.

Pass `--features stratified` to use dependency-stratified scheduling. The same
feature selects it for the checker in the evaluator integration suite:

```sh
cargo test --release -p eqlog-test-eval --test ett --features stratified
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
parameters, identity types, `rfl`, and typed `let` statements. `by rfl` and
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

`Type` is a universe of codes for small types. A parameter `A : Type` can be
used as a type by decoding its code. The universe itself is formed but is not
small, so `Type : Type` and small constructors with fields of type `Type`
are rejected. Uniform parameters such as Vec's `A` are external to its fields.

`let` statements can begin declaration and branch bodies; their annotations
are checked before their values become available. Numeric literals and
infix arithmetic are not implemented; constructors use qualified names.

## Contexts and checking

Each scope is a fresh instance of the `Context` Eqlog model in `src/kernel.eql`.
Types, terms, typing judgments and equalities belong to that model. Extending
a context never identifies it with another context having the same telescope.
Declarations, branches and let statements also create fresh scopes. Weakening
maps existing material forward into the new scope; equality cannot flow back
to the earlier scope.

Morphisms have the direction of substitution: the projection for a variable
extension is `Gamma -> Gamma.x:A`. Pairing substitutes an argument for the
last variable after its type has been established. A definition with parameters
is a term in an extended context. Applying it requests its image along a
sequence of such pairings, without constructing a function type.

An inhabitant of an identity type identifies its endpoints in its context.
Consequently, induction hypotheses are used by equality reflection, and many
branches are simply `rfl`. Identity proofs are proof irrelevant.

The frontend elaborates the entire module into one Eqlog model. It allocates
syntax and substitution requests, but does not evaluate terms or assert that
unchecked annotations hold. It calls `close()` exactly once and then checks
the declaration, constructor-field, index-binder, and definition obligations.
A declaration's exported term is identified with its body only after the body
has the declared type. The frontend is part of
the trusted checker: in particular, it constructs the motives and branch
obligations and resolves names hygienically.

## Open definitions and finite computation

Definitions are open. Instantiating a signature explicitly creates its types
and terms in the destination context. Substitution on the defining body stays
partial: requesting an image of `foo`, where `foo = bar + baz`, does not
allocate images of `bar` or `baz`. Existing destination expressions can supply
missing images through surjective rules. Weakening copies the finite material
already present in the previous statement context.

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
