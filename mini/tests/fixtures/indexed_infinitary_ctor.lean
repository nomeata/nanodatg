/-
# An indexed family branching over a closed fibre — and the decline that is
# reached first

This fixture was exported to be the **consumer** `mini/src/ctor_ix.rs`'s
`ctor_abbrevs` has never had: an inductive that is indexed (`ni ≥ 1`), has a
parameter (`np ≥ 1`), and carries a **function-typed** recursive argument, which
is the combination under which that function's abstraction over the fields alone
is distinguishable from an abstraction over `p⃗ ++ f⃗`. At `np = 0` the parameter
prefix is empty and the two spellings are the same term.

**It does not reach `ctor_abbrevs`, and that is the measurement.**

```text
$ mini --verbose --acceptance-only indexed_infinitary_ctor.ndjson
… accept  8 declarations  untranslated: 1 declaration  uncertified: 4 const typings, 3 type typings
ledger    pairs=4 typesOk=1 valuesOk=0/4
          ind-spec(IxT: indexed function-typed recursive argument)=7
evidence  pairs=4 typeEv=1 constEv=0
          waiting:ind-spec(IxT: indexed function-typed recursive argument)=4
untranslated declarations=1
          notrans:ind-spec(IxT: indexed function-typed recursive argument)=1
```

The refusal is `mini/src/zoneb.rs`'s `ctor_spec`, in the `fun_rec` arm:

```rust
if ni != 0 {
    return Err(Gap::IndSpec(ind_name.clone(), "indexed function-typed recursive argument"))
}
```

— one site in the repository, and the reason string is for once exactly the
cause. It fires during the **constructor telescope walk**, which runs before the
carrier is built and therefore before `ctor_ix::ctor_abbrevs` is called at all.
The whole declaration is `notrans`, not merely the constructor: `⟦IxT⟧` itself
never lands, which is why `typeEv = 1` (the three closed helper types) rather
than `2`.

So the abstraction gap in `ctor_abbrevs` sits **behind** a decline one
construction earlier, and it stays unreachable — and untestable end to end —
until `ctor_spec` admits this shape. The reason `ctor_spec` gives for refusing
is not the abstraction: it is that a function-typed recursive argument's index
expressions may mention the bound `z⃗`, which `index_syms` abstracts over the
parameters and the plain fields alone. That is a *third* abstraction list, and a
separate question from `ctor_abbrevs`'.

The shape is nonetheless legal Lean and Lean exports it as
`numParams=1, numIndices=1, isReflexive=true`, so nothing here is hypothetical.

# Why these three constructors

`leaf` has no recursive argument, `node` branches over a two-element fibre and
`wide` over a three-element one. The fibre summand row is read off
`Inductive::fibre_summands_at` by constructor index, and a clamp `i ↦ min(i,1)`
is the identity on `{0,1}` — with only `leaf` and `node` the third row could not
say it was picked correctly. The two branching constructors are identical in
every other respect, including their result index, so what distinguishes them is
the fibre and nothing else.

# Why the fibres and the index type are hand-declared

`Bool` and `Nat` come from `Init.Prelude`, which `prelude` does not import, and
`Nat` additionally is literal-carrying, so it would drag `Expr::NatLit` handling
into a file that is about branching. The recursive arguments' domains are
**closed** (`B2`, `T3`) on purpose: a domain mentioning a parameter is a
different open question and would confound this one.
-/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

--#export N B2 T3 IxT ixTTy ixTLeaf ixTNode ixTWide

/-- The index type. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- A two-element closed fibre. -/
inductive B2 : Type where
  | ff : B2
  | tt : B2

/-- A three-element closed fibre. -/
inductive T3 : Type where
  | a : T3
  | b : T3
  | c : T3

/-- Indexed — `N.z` and `N.s n` are not one fixed variable, so
    `fixedIndicesToParams` cannot promote the index to a parameter — with
    `np = 1` and two constructors taking a **function-typed** recursive argument
    over a **closed** domain. -/
inductive IxT (α : Type) : N → Type where
  | leaf : α → IxT α N.z
  | node : {n : N} → (B2 → IxT α n) → IxT α (N.s n)
  | wide : {n : N} → (T3 → IxT α n) → IxT α (N.s n)

def ixTTy (α : Type) (n : N) : Type := IxT α n
def ixTLeaf (α : Type) (a : α) : IxT α N.z := IxT.leaf a
def ixTNode (α : Type) (n : N) (f : B2 → IxT α n) : IxT α (N.s n) := IxT.node f
def ixTWide (α : Type) (n : N) (f : T3 → IxT α n) : IxT α (N.s n) := IxT.wide f
