/-
# An indexed family branching over a closed fibre — and the layer it stops at

This fixture was exported to be the **consumer** `mini/src/ctor_ix.rs`'s
`ctor_abbrevs` had never had: an inductive that is indexed (`ni ≥ 1`), has a
parameter (`np ≥ 1`), and carries a **function-typed** recursive argument, which
is the combination under which that function's abstraction over the fields alone
is distinguishable from an abstraction over `p⃗ ++ f⃗`. At `np = 0` the parameter
prefix is empty and the two spellings are the same term.

**Two layers have lifted on it and it has not certified yet.** That is the
record this header keeps, because each lift revealed the next and none of them
was the one predicted underneath it.

| round | the stop | what it was |
|---|---|---|
| exported | `ind-spec(IxT: indexed function-typed recursive argument)` | a blanket `ni != 0` refusal in `zoneb::ctor_spec`'s `fun_rec` arm |
| lift 1 | `ind-spec(IxT: naming a constructor's term)` | `ctor_ix::ctor_abbrevs` abstracting over the fields alone |
| lift 2 | `ind-spec(IxT: indexed carrier)` | **`derived/`**, and where it stands today |

```text
$ mini --verbose --acceptance-only indexed_infinitary_ctor.ndjson
… accept  8 declarations  untranslated: 1 declaration  uncertified: 4 const typings, 3 type typings
ledger    pairs=4 typesOk=1 valuesOk=0/4
          ind-spec(IxT: indexed carrier)=7
evidence  pairs=4 typeEv=1 constEv=0
          waiting:ind-spec(IxT: indexed carrier)=4
untranslated declarations=1
```

`constEv` is **0** and the target is 4. The whole declaration is `notrans`, not
merely the constructor: `⟦IxT⟧` itself never lands, which is why `typeEv = 1`
(the three closed helper types) rather than `2`.

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

# Where it stops now, located rather than named

`derived/src/inductive/family/good.rs:247` — the ι rebuild inside
`Good::build`, comparing `rec(ctorᵢ(…))` against `GoodValues::of(i, …)`. A
`?`-census over `IndexedInductive::build` and the five constructions under it
puts it there and at `family.rs:187` one frame up, and **nowhere else**.

The shape is in `gval.rs::matrix_atoms`, which builds the good-set matrix `ψᵢ`:

```rust
for j in 0..ctor.recs {
    let child = IndexedDeclSpec::tup(s, &spec.rec_index_vec(i, j, ps, &comps)?);
    let slot = ap.apply(r.clone(), mach.syms.inj(j, s.point())?);
    atoms.push(Formula::mem(child, slot));
}
```

`slot` is `r(Inj_j(•))` — the `j`-th recursive child at a **single point**,
which is the `finord(mᵢ)` fibre spelling. Under `RecArg::general` the summand is
`Σ(z::γⱼ)` and the slot holds a whole family, so the atom has to become
`∀z ∈ γⱼ. tup(d⃗ᵢⱼ) ∈ r(Inj_j(⟨z,•⟩))` — a quantified obligation rather than a
membership. That changes `matrix_atoms`, the inversion rule in
`family/carrier.rs` that projects out of exactly that list, and `good.rs`'s ι
rebuild that compares against it. It is a construction, not a wiring gap, and it
is `derived/`'s.

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
