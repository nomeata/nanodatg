/-
# The one number in the encoding that is not syntax

`mutual_aux` encodes a block by packing its `n` motives into one, by recursion
on the tag:

```text
Mot := fun p⃗ m⃗ => Tag.rec (fun t => ∀ix, Aux p⃗ t ix → Sort v) m⃗
```

and `Tag.rec` has to be instantiated at **exactly** the sort that motive body
lives at, which is

```text
max(s₁, …, s_k, u, v+1)      sⱼ = the sort of the j-th index *type*
```

Every other number in the encoding is read off the declaration. This one is
not: an index of type `N` is at `Sort 1` only because `N`'s declaration says so,
so the encoder asks the checker (`kernel::sort_under`, whose entire output is a
`Level`). This file is the fixture that makes the question have a different
answer from the cheap guess.

# Why the cheap guess is usually right, and here is not

On almost every block the index sorts are **below** `max(u, v+1)` and could be
dropped from the `max` without anyone noticing:

* If a constructor binds index `j` as a field, `checkCtorParam`'s
  `assertLevelLe sⱼ u` forces `sⱼ ≤ u` — so for a `Type`-valued family the
  index sorts are already inside the `max`. Every index in
  `mutual_indices.lean` is of this kind.
* A `Prop`-valued family skips that check (`indLevel` is `Zero`, and mini-lean
  skips `assertLevelLe` there), but its motive level `v` is `0` and the indices
  in `mutual_prop_even_odd.lean` are `N`, at `Sort 1` — which is exactly
  `max(0, 0+1)`. Equal again.

So a builder that wrote `max(u, v+1)` and ignored the index sorts entirely
passes both of those files. The escape is a **`Prop`-valued family indexed by a
large type**: no universe constraint on the fields, `v = 0`, and an index at
`Type 1`, whose sort is `Sort 3`. Then the answer is `3` and the guess is `1`.

`SA`/`SB`/`SC` are that. `γ : Type 1` is a genuine index and not a promoted
parameter because `SA.base` and `SC.base` give it the *closed* value `Type`
while `step` gives it a variable — `fixedIndicesToParams` promotes only an index
that is the same variable everywhere.

# The other three axes, held apart from each other

An indexed block has more ways to be degenerate than a plain one, and the two
mutations that survived the last round were both "the only fixture exercising
this had a degenerate shape". So this file is deliberately non-degenerate on
every axis at once:

| axis | elsewhere | here |
| --- | --- | --- |
| index arity | 1 (`mutual_indices`, `mutual_prop_even_odd`) | **2** |
| index sorts | all equal | **`Sort 3` and `Sort 1`, in that order** |
| parameters *and* indices | never together | **2 parameters, 2 indices** |
| an index *type* that mentions a parameter | never | **`VA`/`VB`, indexed by `Pair α`** |
| rule theorems over an indexed block | never | **`Eq` is here, so they are stated** |
| members | 3 | 3, in a cycle `SA → SC → SB → SA` |

# The third block, and the four shifts it is the only witness for

An index *type* that mentions a parameter is the shape that makes the encoding's
de Bruijn arithmetic observable. The index telescope is moved under extra
binders in four places — past `Aux`'s tag, past the motives that precede each
motive, past the motives and the tag inside the packed motive, and past the
motives and the minors inside a rule — and **every one of those shifts is the
identity when no index type mentions a parameter**. `SA`/`SB`/`SC`'s indices are
`Type 1` and `N`, both closed; so are every index in every other fixture. A
mutation that deleted the first of those shifts outright passed the whole suite.

`VA`/`VB` are indexed by `Pair α`, which mentions the block's parameter, and
`VA.base`'s index is the *computed* `Pair.mk x x` so `fixedIndicesToParams` does
not promote it away. Two members rather than three: this block's claim is about
the shifts, and member order is pinned three ways elsewhere.

Two indices of *different* sorts in a fixed order is what catches a builder that
computes the `max` correctly but binds the index telescope in the wrong order,
or that shifts an index type past the wrong number of binders — with two indices
at the same sort, a swap is invisible.

`Eq` is here so that the recursor rules are stated as theorems at all: the
encoder does not fabricate an equality, so a block in a file without one gets
its encoding and no rules. `saBaseRefl` exists only to pull `Eq` into the
export.

# The second block is the scope line

`HA : N → Type` has one index, `HB : Type` has none. `Aux` has **one** index
telescope, so the members of a block must share theirs — a rule of this
encoding and not of the kernel, which is happy with the block. So this block
declines, by name, with
`ind-spec(HA: mutual with unequal index telescopes)`, and having it in the same
file as a block that *does* encode is what makes the line visible.

When the line is lifted this block becomes the fixture for the **arity**
axis — one index against none, at two members — and it becomes it without
being regenerated. The lift is a generalisation of the encoding rather than a
second path: the indices move into the tag, `Tag.i : ∀p⃗ ix⃗ᵢ, Tag p⃗` carries
each member's own telescope, and `Aux (p⃗) : Tag p⃗ → Sort u` has none. It has
been checked in Lean by hand, for this block and five others, with every
recursor rule still `rfl`. Two axes this file would then *not* cover and that
the lift needs their own fixtures for: three members with two sharing a
telescope and one differing, and two members at equal arity whose index
**types** differ. (The header above's `Sort 3`/`Sort 1` claim survives the
lift and changes address: the index sorts stop being part of the level
`Tag.rec` runs at and become `Tag`'s own universe, which is the same
`kernel::sort_under` question and the same escape shape.)

`PUnit` and `PProd` are the `prelude` tax for a `Prop`-valued mutual block:
Lean's own `below`/`brecOn` generation needs them. Neither is exported.
-/
prelude

--#export SA SB SC HA HB VA VB Pair
--#export saTy sbTy scTy saBase saStep sbStep saBaseRefl
--#export haTy hbTy haMk vaTy vbTy vaBase vaStep

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

structure PProd (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β

/-- The second index's type, at `Sort 1`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The third block's index type. It mentions the block's parameter, which is
    what makes the index telescope's shifts observable. -/
inductive Pair (α : Type) : Type where
  | mk : α → α → Pair α

mutual

/-- Two parameters, two indices at two different sorts, and a base case that
    gives the first index a **closed** value so it is not promoted. -/
inductive SA (α : Type) (β : Type) : Type 1 → N → Prop where
  | base : α → SA α β Type N.z
  | step : (γ : Type 1) → (n : N) → SC α β γ n → SA α β γ (N.s n)

/-- No base case; recurses into `SA`. -/
inductive SB (α : Type) (β : Type) : Type 1 → N → Prop where
  | step : (γ : Type 1) → (n : N) → SA α β γ n → SB α β γ (N.s n)

/-- Closes the cycle at `SB`, so the recursion runs against declaration
    order. -/
inductive SC (α : Type) (β : Type) : Type 1 → N → Prop where
  | base : β → SC α β Type N.z
  | step : (γ : Type 1) → (n : N) → SB α β γ n → SC α β γ (N.s n)

end

mutual

/-- One index. -/
inductive HA : N → Type where
  | mk : HB → HA N.z

/-- None — so the block's members do not share an index telescope, and the
    encoding declines. -/
inductive HB : Type where
  | mk : HB

end

def saTy (α β : Type) (γ : Type 1) (n : N) : Prop := SA α β γ n
def sbTy (α β : Type) (γ : Type 1) (n : N) : Prop := SB α β γ n
def scTy (α β : Type) (γ : Type 1) (n : N) : Prop := SC α β γ n
def saBase (α β : Type) (a : α) : SA α β Type N.z := SA.base a
def saStep (α β : Type) (γ : Type 1) (n : N) (x : SC α β γ n) : SA α β γ (N.s n) := SA.step γ n x
def sbStep (α β : Type) (γ : Type 1) (n : N) (x : SA α β γ n) : SB α β γ (N.s n) := SB.step γ n x

/-- Only here to pull `Eq` into the export, so that the rule theorems are
    stated over an indexed, parameterised block. -/
theorem saBaseRefl (α β : Type) (a : α) : Eq (SA.base (β := β) a) (SA.base a) := Eq.refl _

mutual

/-- Indexed by `Pair α` — an index type that mentions the parameter. `base`'s
    index is computed, so it stays an index. -/
inductive VA (α : Type) : Pair α → Prop where
  | base : (x : α) → VA α (Pair.mk x x)
  | step : (p : Pair α) → VB α p → VA α p

/-- The other member. -/
inductive VB (α : Type) : Pair α → Prop where
  | step : (p : Pair α) → VA α p → VB α p

end

def vaTy (α : Type) (p : Pair α) : Prop := VA α p
def vbTy (α : Type) (p : Pair α) : Prop := VB α p
def vaBase (α : Type) (x : α) : VA α (Pair.mk x x) := VA.base x
def vaStep (α : Type) (p : Pair α) (h : VB α p) : VA α p := VA.step p h

def haTy (n : N) : Type := HA n
def hbTy : Type := HB
def haMk (b : HB) : HA N.z := HA.mk b
