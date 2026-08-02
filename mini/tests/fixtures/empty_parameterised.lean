/-
# A declaration with no constructors **and parameters**

**What breaks if `voidRec` or `void3Rec` stops deriving.** `recursor::empty_bottom`
holds `t ∈ ⟦T p⃗⟧` — the applied spine — while `EmptyDecl` speaks of `ind(p⃗)`,
and `Interp::beta_spine` is the equation between them. That bridge is
*reflexivity at `np = 0` and a real derivation above it*, and

    Empty has np = 0.

`059_emptyRec` is the only witness in the corpus and it is the degenerate one,
so the `np > 0` branch — the `beta_spine` derivation, the `ps` threading through
`inst_all(any, p⃗ ++ [t])`, and `EmptyDecl::over_declaration` at a parameterised
carrier — was written on faith. This file is the shape that exercises it.

| declaration | np | resultant sort | why it is here |
| --- | ---: | --- | --- |
| `Void0` | 0 | `Type` | the control: `Empty` again, in this file, so a failure below is about parameters and not about `EmptyDecl` |
| `Void` | 1 | `Type` | **the target** — the first `np > 0` witness anywhere |
| `Void3` | 3 | `Type` | the parameters in a dependency chain, so their order is forced |
| `VoidU` | 1 | `Type u` | a universe parameter in the declaration's **own** resultant sort |
| `VoidProp` | 1 | `Prop` | zero constructors on the other side of the trichotomy |

# Why three parameters and not two

`empty_bottom` finishes with `inst_all(any, p⃗ ++ [t])` and then `Thm::mp`
against the major premise, whose statement names `ind(p⃗)` with the parameters
in order. `mp` matches its antecedent exactly, so a *permutation* of `p⃗` is
already caught at `np = 2`. What two parameters cannot catch is a rule that
threads *some* prefix — dropping the outermost, or keeping only the innermost —
and `Void3`'s chain `α`, `β : α → Type`, `γ : (a : α) → β a → Type` makes each
of the three a different type mentioning a different set of earlier ones, so no
wrong subset is well-formed.

# `VoidProp` is a contrast row, not a second target

Zero constructors makes a declaration large-eliminating by Carneiro §2.6.2's
reason 2 whatever its sort, but `provably_nonzero(Sort 0)` is false, so
`VoidProp` is routed to **class (S)** and never reaches `EmptyDecl` at all. It
is here so that "zero constructors" and "class (T), `n = 0`" are visibly
different questions — `EmptyDecl`'s row in `recursor.rs`'s table is the second,
not the first — and so that whatever class (S) does with an empty disjunction is
measured rather than assumed.

# The use sites

`059_emptyRec` is `def emptyRec.{u} : ∀ (motive : Empty → Sort u) (t : Empty),
motive t := Empty.rec.{u}` — an alias for the eliminator, and the whole reason
that file reaches `empty_rec` at all. These mirror it, with the parameters
applied explicitly so that nothing depends on how Lean elaborates an implicit
argument. Each declaration also gets a `…Ty` def, so that a failure in the
carrier is distinguishable from a failure in the eliminator.

`numParams` is asserted out of the **export** in `designed.rs`, not read off the
source: Lean rewrites inductive telescopes (`fixedIndicesToParams` is one way,
and a constructor-less declaration gives it nothing to inspect, which is a
reason to check rather than a reason not to).
-/
prelude
universe u

--#export Void0 Void0.rec Void Void.rec Void3 Void3.rec VoidU VoidU.rec VoidProp VoidProp.rec
--#export void0Ty void0Rec voidTy voidRec void3Ty void3Rec voidUTy voidURec
--#export voidPropTy voidPropRec

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- The control: `Empty` under another name, `np = 0`. -/
inductive Void0 : Type

/-- **The target.** One parameter, no constructors. -/
inductive Void (α : Type) : Type

/-- Three parameters in a dependency chain, so no wrong subset of them is
    even well-formed. -/
inductive Void3 (α : Type) (β : α → Type) (γ : (a : α) → β a → Type) : Type

/-- A universe parameter in the declaration's own resultant sort. -/
inductive VoidU (α : Type u) : Type u

/-- Zero constructors at `Prop`: large-eliminating by reason 2, but not
    provably nonzero, so class (S) rather than `EmptyDecl`. -/
inductive VoidProp (α : Type) : Prop

noncomputable def void0Ty : Type := Void0
noncomputable def void0Rec (motive : Void0 → Sort u) (t : Void0) : motive t :=
  @Void0.rec motive t

noncomputable def voidTy (α : Type) : Type := Void α
noncomputable def voidRec (α : Type) (motive : Void α → Sort u) (t : Void α) : motive t :=
  @Void.rec α motive t

noncomputable def void3Ty (α : Type) (β : α → Type) (γ : (a : α) → β a → Type) : Type :=
  Void3 α β γ
noncomputable def void3Rec (α : Type) (β : α → Type) (γ : (a : α) → β a → Type)
    (motive : Void3 α β γ → Sort u) (t : Void3 α β γ) : motive t :=
  @Void3.rec α β γ motive t

noncomputable def voidUTy (α : Type u) : Type u := VoidU α
noncomputable def voidURec (α : Type u) (motive : VoidU α → Sort u) (t : VoidU α) : motive t :=
  @VoidU.rec α motive t

noncomputable def voidPropTy (α : Type) : Prop := VoidProp α
noncomputable def voidPropRec (α : Type) (motive : VoidProp α → Sort u) (t : VoidProp α) : motive t :=
  @VoidProp.rec α motive t
