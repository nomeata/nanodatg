/-
# A mutual block with parameters, and two of them

Every member of a `mutual … end` block must be declared with the **same
parameter telescope** — the kernel checks it, and mini's `defEqParams` is the
check. This file is the positive witness: three members, two parameters each,
and every constructor's result type applied to the parameters in the declared
order.

**Two parameters, not one.** With a single parameter, a builder that takes the
parameter prefix from the wrong member, or that reverses it, produces the same
telescope; with two of *different* types the reversal is a type error and the
wrong-member choice is not, so the two failure modes are separated. `α` and `β`
are distinct type variables and each is used by a different member — `PA.leaf`
holds an `α`, `PB.wrap` holds a `β`, `PC` holds neither — so a parameter list
built by scanning one member's constructors rather than the block's declaration
would be short.

# Why there is an `Eq` in a file about parameters

`mutual_aux` states a recursor rule as a theorem only when the environment has
an equality to state it with, and it does not fabricate one. Without `Eq` here,
the only file whose rules are ever stated is `mutual_iota_reduction` — which has
**no parameters**, so the shift that carries a constructor field's type past the
motives and the minors is the identity there and is never exercised. A mutation
that deleted that shift outright passed the whole suite.

So this file carries an `Eq`, and its five rule theorems are the ones that
travel under a two-parameter telescope. `paLeafRefl` is there to pull `Eq` into
the export; nothing else uses it.

# What the recursive occurrences pin

The block is a cycle again: `PA → PB → PC → PA`. In a parameterised block every
recursive occurrence must be at the block's *own* parameters — `PB α β`, never
`PB β α` — and the recursor's minors state their induction hypotheses at motives
that are themselves under the same parameter prefix. So the parameter prefix is
shared three ways: by the type formers, by the motives, and by the recursive
occurrences inside the minors.
-/
prelude

--#export PA PB PC
--#export paTy pbTy pcTy paLeaf paNode pbWrap pcBack paLeafRefl

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. It is here so that the
    encoder has an equality to state its recursor rules with — and therefore so
    that those rules are stated over a block that has **parameters**. See the
    section below. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

mutual

/-- Uses `α`. -/
inductive PA (α : Type) (β : Type) : Type where
  | leaf : α → PA α β
  | node : PB α β → PA α β

/-- Uses `β`. -/
inductive PB (α : Type) (β : Type) : Type where
  | wrap : β → PC α β → PB α β

/-- Uses neither, and closes the cycle. -/
inductive PC (α : Type) (β : Type) : Type where
  | done : PC α β
  | back : PA α β → PC α β

end

def paTy (α β : Type) : Type := PA α β
def pbTy (α β : Type) : Type := PB α β
def pcTy (α β : Type) : Type := PC α β
def paLeaf (α β : Type) (a : α) : PA α β := PA.leaf a
def paNode (α β : Type) (b : PB α β) : PA α β := PA.node b
def pbWrap (α β : Type) (b : β) (c : PC α β) : PB α β := PB.wrap b c
def pcBack (α β : Type) (a : PA α β) : PC α β := PC.back a
theorem paLeafRefl (α β : Type) (a : α) : Eq (PA.leaf (β := β) a) (PA.leaf a) := Eq.refl _
