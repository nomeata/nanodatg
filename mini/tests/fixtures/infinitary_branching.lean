/-
# Infinitary branching — a W-type the `ω`-tower cannot hold

**This fixture exists to fail.** `NTree.node : (N → NTree) → NTree` is ordinary
Lean, and `derived/src/cumul/bounded.rs` cannot place its carrier: the tower
`T = ⋃ₙ Vₙ` is closed under `sup` only for fibres satisfying

```text
bnd(k) := ∀g. ((∀b. b ∈ k → g(b) ∈ T) → ∃p ∈ ω. ∀b. b ∈ k → g(b) ∈ Vₚ)
```

and at `k = ⟦N⟧` that formula is **refutable**, not merely underived: send `n`
to an element first appearing at stage `n` and the ranks are cofinal in `ω`, so
no single `Vₚ` covers the image. The thesis's answer is §6.2.1 — a tower at a
regular `κ` with `cf(κ) > sup_{a∈A}|B(a)|` — and nothing weaker.

# Three fibres, because two cannot distinguish

The declaration under test is one of three with the *same* shape and different
recursive-argument domains, so the row that fails names the property that
fails rather than the position in a list:

| declaration | `γ` | `γ`'s constructors | today |
|---|---|---|---|
| `FinTree.node : (B2 → FinTree) → FinTree`  | `B2` | two, nullary | **certifies** |
| `FieldTree.node : (P1 → FieldTree) → FieldTree` | `P1` | one, with a field | declines |
| `NTree.node : (N → NTree) → NTree` | `N` | two, one *recursive* | declines |

`FinTree` is `RTree` from `115_rTreeRec`, restated here so the discrimination
lives in one file. `FieldTree` and `NTree` both decline today and they decline
for **different** reasons: `bnd_nullary_tags` refuses a constructor with a
field, and `bnd_carrier` refuses a constructor with a recursive argument. Only
the third is the `ω`-tower — `P1`'s carrier is a one-point set and its `bnd` is
true, so `FieldTree` is a missing lemma. Fixing the tower closes `NTree` and
leaves `FieldTree` exactly where it is; fixing `bnd_nullary_tags` does the
converse. A single declining row could not have said that.

# Why `N` and not `Nat`

`Nat` is a *literal-carrying* inductive in Lean and the export gives it
`Expr::NatLit` support that has nothing to do with branching. `N` is the same
inductive without that machinery, so the only thing this file measures is the
fibre.
-/
prelude

universe u

unsafe axiom lcErased : Type u
unsafe axiom lcAny : Type u
unsafe axiom lcVoid : Type u

--#export finTreeTy finTreeNode fieldTreeTy fieldTreeNode ntreeTy ntreeNode

/-- Two nullary constructors: a fibre whose `bnd` the library proves today. -/
inductive B2 : Type where
  | ff : B2
  | tt : B2

/-- One constructor, one field: a *finite* fibre whose `bnd` is true and
    unbuilt. -/
inductive P1 : Type where
  | mk : B2 → P1

/-- Two constructors, one recursive: an *infinite* fibre whose `bnd` is
    false. -/
inductive N : Type where
  | zero : N
  | succ : N → N

/-- The control. -/
inductive FinTree : Type where
  | leaf : FinTree
  | node : (B2 → FinTree) → FinTree

/-- The discriminator: finite fibre, missing lemma. -/
inductive FieldTree : Type where
  | leaf : FieldTree
  | node : (P1 → FieldTree) → FieldTree

/-- The witness: infinite fibre, refutable `bnd`. -/
inductive NTree : Type where
  | leaf : NTree
  | node : (N → NTree) → NTree

def finTreeTy : Type := FinTree
def finTreeNode (f : B2 → FinTree) : FinTree := FinTree.node f
def fieldTreeTy : Type := FieldTree
def fieldTreeNode (f : P1 → FieldTree) : FieldTree := FieldTree.node f
def ntreeTy : Type := NTree
def ntreeNode (f : N → NTree) : NTree := NTree.node f
