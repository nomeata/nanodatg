/-
# Infinitary branching — a W-type the `ω`-tower could not hold

**This fixture existed to fail, and as of 2026-08-05 it does not.**
`NTree.node : (N → NTree) → NTree` is ordinary Lean, and its carrier is now
placed. What it could not be placed *by* is the tower: `derived/src/cumul/bounded.rs`
closes `T = ⋃ₙ Vₙ` under `sup` only for fibres satisfying

```text
bnd(k) := ∀g. ((∀b. b ∈ k → g(b) ∈ T) → ∃p ∈ ω. ∀b. b ∈ k → g(b) ∈ Vₚ)
```

and at `k = ⟦N⟧` that formula is **refutable**, not merely underived: send `n`
to an element first appearing at stage `n` and the ranks are cofinal in `ω`, so
no single `Vₚ` covers the image. The thesis's answer is §6.2.1 — a tower at a
regular `κ` with `cf(κ) > sup_{a∈A}|B(a)|` — and **that is not the route taken**.
`derived/src/wpath/` bounds `W` by its set of labelled finite *paths* instead: a
path is built one fibre element at a time, so the ambient set need only be
closed under binary pairing, and `bnd` is never stated. The tower survives as
the set the paths live in (`derived::cumul::tower_amb`), where its height was
never in question. See SCOPING.md §14.

What was *never* the missing piece is a Grothendieck universe: a universe is
already this W-type's **bound** and is already sup-closed at an infinite fibre,
with no fibre condition at all (`derived::bound::least_universe_closed`). `bnd`
bought a sup-closed **member** of `U₁`, which no universe can be — §14 "Route C".

# Three fibres, because two cannot distinguish

The declaration under test is one of three with the *same* shape and different
recursive-argument domains, so the row that fails names the property that
fails rather than the position in a list:

| declaration | `γ` | `γ`'s constructors | before | after |
|---|---|---|---|---|
| `FinTree.node : (B2 → FinTree) → FinTree`  | `B2` | two, nullary | certifies | certifies |
| `FieldTree.node : (P1 → FieldTree) → FieldTree` | `P1` | one, with a field | declined | **certifies** |
| `NTree.node : (N → NTree) → NTree` | `N` | two, one *recursive* | declined | **certifies** |

`FinTree` is `RTree` from `115_rTreeRec`, restated here so the discrimination
lives in one file. `FieldTree` and `NTree` used to decline for **different**
reasons: `bnd_nullary_tags` refused a constructor with a field, and
`bnd_carrier` a constructor with a recursive argument. Only the third was the
`ω`-tower — `P1`'s carrier is a one-point set and its `bnd` is *true*, so
`FieldTree` was a missing lemma while `NTree` was a missing construction. A
taller tower would have closed `NTree` and left `FieldTree`; a lemma for
`bnd_nullary_tags` the converse.

**They closed together, and that is what says which route this was.** The path
construction deletes the obligation rather than discharging it, so the
true-but-unbuilt `bnd` and the false one went the same way. A single declining
row could not have said that, and neither could a landing that reached
`constEv = 4`.

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

/-- The discriminator: finite fibre, `bnd` true and never built. -/
inductive FieldTree : Type where
  | leaf : FieldTree
  | node : (P1 → FieldTree) → FieldTree

/-- The witness: infinite fibre, refutable `bnd` — and it certifies anyway. -/
inductive NTree : Type where
  | leaf : NTree
  | node : (N → NTree) → NTree

def finTreeTy : Type := FinTree
def finTreeNode (f : B2 → FinTree) : FinTree := FinTree.node f
def fieldTreeTy : Type := FieldTree
def fieldTreeNode (f : P1 → FieldTree) : FieldTree := FieldTree.node f
def ntreeTy : Type := NTree
def ntreeNode (f : N → NTree) : NTree := NTree.node f
