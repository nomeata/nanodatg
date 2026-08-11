/-
# An indexed family with **two** parameters — the cell `index_congr` is never reached at

`mini::ctor_ix::index_congr` builds `⊢ ind(p⃗, sym⃗) = ind(p⃗, ⟦x⃗⟧)` and checks
each *index* against the term inference produced:

```rust
if at.concl().as_eq()?.1 != *t { return None }
```

The **parameters enter at `Thm::eq_refl`** (`ctor_ix.rs:913`) and are compared
against nothing, so the guard cannot see a wrong parameter: both sides of the
congruence carry the same wrong `p⃗` and the equation is well formed.

## Why the corpus cannot answer whether that matters

Measured, and it is not the measurement the arm census gives. `scripts/arm-coverage.py`
reports 35 indexed declarations and none at `np = 0`, which suggests parameters
are well covered. At the **guard** the picture is different: instrumenting
`index_congr` over all 91 exports, it is reached by **exactly one**,
`077_RBTree.id_spec`, and only ever at `np = 1` (69 calls: 3 at `nx = 0`, 3 at
`nx = 1`, 63 at `nx = 2`). The thirty `np = 2` indexed declarations in the
corpus are all `Eq`, and `Eq` never reaches this route.

So a **swap** mutation — the natural probe for a parameter frame — is a no-op
on the entire corpus, because there are never two parameters to swap where the
guard runs. A first draft of this investigation ran exactly that mutation,
watched it survive on six exports, and would have reported a hole; the survival
was vacuous. This fixture is the cell that makes the probe mean something.

## What it declares

`Ix α β` has **two parameters of the same sort**, so exchanging them is
well-formed rather than ill-typed — the wrong-but-well-formed shape the whole
confluence question is about. The index varies between the constructors
(`N.z` against `N.s n`), which is what stops Lean's `fixedIndicesToParams` from
promoting it and leaving a fixture that measures nothing.

| declaration | why |
| --- | --- |
| `Ix` | `np = 2`, `ni = 1` — the unreached cell |
| `Ix.mk` | fields at **both** parameters, in order, so a swap changes what the constructor's fields must be |
| `Ix.step` | a recursive occurrence at a *different* index, which is what takes the constructor down `ctor_ix`'s indexed route at all |
| `ixMk`, `ixStep` | use sites, because the ledger opens a pair for a `def` and not for an `inductive` |

`α` and `β` are distinct binders of the same sort on purpose: at one parameter
a swap does not exist, and at two parameters of *different* sorts it would be
caught by typing rather than by the guard under test. Two same-sorted
parameters is the only cell where the question is live.
-/
prelude

--#export Eq N Ix ixMk ixStep

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

/-- Two parameters of the **same** sort, and an index that genuinely varies. -/
inductive Ix (α : Type) (β : Type) : N → Type where
  | mk : α → β → Ix α β N.z
  | step : (n : N) → Ix α β n → Ix α β (N.s n)

def ixMk (α : Type) (β : Type) (a : α) (b : β) : Ix α β N.z := Ix.mk a b

def ixStep (α : Type) (β : Type) (n : N) (t : Ix α β n) : Ix α β (N.s n) := Ix.step n t
