/-
# An indexed family branching over a closed fibre — and the layer it stops at

This fixture was exported to be the **consumer** `mini/src/ctor_ix.rs`'s
`ctor_abbrevs` had never had: an inductive that is indexed (`ni ≥ 1`), has a
parameter (`np ≥ 1`), and carries a **function-typed** recursive argument, which
is the combination under which that function's abstraction over the fields alone
is distinguishable from an abstraction over `p⃗ ++ f⃗`. At `np = 0` the parameter
prefix is empty and the two spellings are the same term.

**Three layers have lifted on it and it certifies in part.** That is the record
this header keeps, because each lift revealed the next and none of them was the
one predicted underneath it.

| round | the stop | what it was |
|---|---|---|
| exported | `ind-spec(IxT: indexed function-typed recursive argument)` | a blanket `ni != 0` refusal in `zoneb::ctor_spec`'s `fun_rec` arm |
| lift 1 | `ind-spec(IxT: naming a constructor's term)` | `ctor_ix::ctor_abbrevs` abstracting over the fields alone |
| lift 2 | `ind-spec(IxT: indexed carrier)` | `derived/`'s good-set matrix, at a fibre with more than one point |
| lift 3 | `ctor(IxT.node: a recursive argument's indices)` | **`mini/`**, and where it stands today |

```text
$ mini --verbose --acceptance-only indexed_infinitary_ctor.ndjson
… accept  8 declarations  untranslated: 2 constructors, 1 eliminator
                          uncertified: 2 const typings
ledger    pairs=4 typesOk=4 valuesOk=2/4
          ctor(IxT.node: a recursive argument's indices)=1
          ctor(IxT.wide: a recursive argument's indices)=1
evidence  pairs=4 typeEv=4 constEv=2
untranslated declarations=0 constructors=2 eliminators=1
```

`constEv` is **2** and the target is 4: `ixTTy` and `ixTLeaf` certify, and the
two branching constructors' use sites do not.

# Lift 1 — the index expressions, and the frame nobody had shifted

`ctor_spec` refused `ni != 0` outright, on the stated ground that a
function-typed recursive argument's index expressions may mention the bound `z⃗`
while `index_syms` abstracts over the parameters and the plain fields alone.

That ground is real but it is **not this declaration**: `IxT.node`'s recursive
occurrence is indexed by the *plain field* `n`, which `index_syms` can abstract
over. What actually had to change is a **frame**, not an abstraction list.
`rec_field` peels `∀z⃗` to find the spine, so it hands back index expressions
stated at binder depth `d + |γ⃗|` while the checker has `np + d` open — read at
the shallower depth, `n` resolves to the parameter `α`, which is *also* in the
abstraction list, so `define_abbrev` would have succeeded and minted the wrong
symbol in silence. The arm opens the `γ⃗` binders for that one call.

A genuinely `z`-dependent index stays declined, and it is unrepresentable rather
than unbuilt: `IndexedDeclSpec` fixes `d⃗ᵢⱼ`'s arity at
`np + plains_before(i,j)`, because the tag telescope holds the plain fields and
nothing else. `derived`'s spec header calls that the thesis's own restriction.
`zoneb::tests::a_function_typed_recursive_arguments_indices_are_read_inside_its_own_binders`
is the three-cell walk.

# Lift 2 — `p⃗ ++ f⃗`, exactly as the header predicted

`ctor_abbrevs`' header said "the day there is a witness, this takes `p⃗`". This
is the witness and it did, and nothing else about the mint changed. Its three
consumers moved with it — `ctor_ix::build`, `iota_ix_dep` and `minor_ix` — and
that they had to be found is the measurement: the non-indexed twin caught the
same omission as a 15-of-91 arity blow-up, and here it surfaced as ten failing
tests including the corpus, not as a wrong term.

# Lift 3 — the good-set matrix learns a fibre with more than one point

`gval.rs::matrix_atoms` gave each recursive slot the atom
`tup(d⃗ᵢⱼ) ∈ app(r, Inj_j(•))`, a membership at a **single point**, which is the
`finord(mᵢ)` fibre spelling. Under `RecArg::general` the summand is `Σ(z::γⱼ)`
and the slot holds a whole family, so the atom is now
`∀z. (z ∈ Aⱼ → tup(d⃗ᵢⱼ) ∈ app(r, Inj_j(z)))` — one atom still, so no
`conj_proj` position moves.

What blocked it was not that atom but the equation the two carrier rules rewrite
its slot with: `GoodIota::ih_eqs` was `⊢ app(cmp, Inj_j(•)) = app(goodrec, rⱼ)`,
**unconditional**, and there is no such equation at a general constructor —
computing `app(f(g⃗), Inj_j z)` needs the branches to be functions. It is
`IhRow::Fibre` now, `z`-indexed and stated under the constructor's own argument
typings, which is an ambient `Good` always had. Five sites moved together;
`derived/tests/family_infinitary.rs` is the witness, with a `node` firing over a
genuinely two-element fibre and the carrier still provably empty at a height no
constructor produces.

# Where it stops now, censused rather than named

`ctor_ix::ctor_bottom`, at `ind_spine` on the recursive field's own binder type
— twice, once per branching constructor, and at no other site. That type is
`∀z::γ. IxT α n`, and `ind_spine` wants the family's spine, so a function-typed
field's `d⃗ᵢⱼ` cannot be read at all yet. Behind it sit the two halves
`zoneb::ctor_bottom` already has for the non-indexed twin: peel the `γ⃗` binders
*and shift the frame* — lift 1's hazard, one construction over — and carry the
field's typing `dprod(b,⟦γ⟧) → fs(⟦γ⟧,⟦T p⃗ d⃗⟧) → fs(β₀(p⃗), ind(p⃗,d⃗ᵢⱼ))` and
then through `sigma::reindex_in_funspace`.

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
