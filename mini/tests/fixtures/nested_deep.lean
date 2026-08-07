/-
# **Two packed positions in one constructor**, which is where the fold is paid for

`nested_iota.lean` carries every nesting shape that matters for `Lean.Syntax`
except one, and `nested_shapes.lean` carries that one but declares no `Eq`, so
`mini::nested_ev` declines it before reaching the interesting part. This file is
the missing witness at the smallest size that has it.

`DTree.node : List (List DTree) → DTree` specialises to two mimics of the **same**
container at two depths,

```text
M₀ ≅ List (List DTree)      M₀.cons : M₁ → M₀ → M₀
M₁ ≅ List DTree             M₁.cons : D  → M₁ → M₁
```

and `M₀.cons` is the point: **both** of its fields sit at a mimic, so the round
trip moves two arguments of one constructor application at once. Every other
nested constructor in the fixture directory moves at most one — `List.cons`'s
head is at the root, `Box.mk` has a single field — so without this file
`nested_ev`'s congruence fold runs its loop at most once wherever it is tested,
and a fold that handled one position and dropped the rest would pass everything.

That is the same reason `mini/tests/nested.rs` needs three elements to pin an
order: two positions is the first arity that can distinguish a fold from a single
transport.

`Eq` is declared here for the reason `nested_shapes.lean` does not have it: the
round trips are equations, and `nested_ev` refuses to fabricate an `Eq` the
export never wrote. That refusal is what `nested_shapes` measures; this file
measures what happens past it.

`Nat` is avoided for the reason `infinitary_branching.lean` gives.
-/
prelude

--#export Eq N List DTree dtreeOfN

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload, so a use site can exist without `Nat`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The container, used at two depths. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- `numNested = 2`, **one** container twice. The inner copy's `cons` is the
    constructor with two packed positions. -/
inductive DTree : Type where
  | leaf : N → DTree
  | node : List (List DTree) → DTree

/-- A closed inhabitant, so the file carries a pair and is not measuring an
    empty ledger. -/
def dtreeOfN : DTree := DTree.node (List.cons (List.cons (DTree.leaf N.z) List.nil) List.nil)
