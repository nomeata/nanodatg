/-
# A projection whose subject **reduces and stays stuck**

`proj_reduced_subject.lean` is the sibling case: the subject reduces *to a
constructor application*, the ι step fires, and `proj_data::iota` composes the
subject's reduction certificate in front of its computation rule. That is the
path where the reduction ends somewhere.

This file is the path where it does **not**. `mini::kernel`'s `whnf` has three
exits in its `Expr::Proj` arm for a subject that reduced and did not reach a
constructor — the reduct's head is not a constant, the projected type is not an
inductive, the head is not the declaration's single constructor — and all three
`done!` the *changed* expression `proj[T,j] s₂` while `acc.ev` is still the
certificate for the **unreduced** `proj[T,j] s`. `whnf_conv`'s contract is that
`acc.ev`'s right endpoint is `⟦acc.to⟧`; at those three exits it was the left
one, silently.

Nothing rejects on that, because the theorem returned is *true* — it is stated
about the wrong terms, not falsely. What it costs is every consumer that checks
its endpoints. `proj_data::proj_congr` is the one that does: handed two
projections whose Lean subjects are the same reduct but whose interpretations
were carried from two different unreduced spellings, it derives
`⊢ πⱼ(⟦s₂⟧) = πⱼ(⟦s₂⟧)` correctly, finds it is not the pair of endpoints the
caller holds, and throws it away.

**This is not about which structure.** The three exits do not look at the
declaration; they are reached by any projection whose subject bottoms out at a
variable, which is what Lean's structural-recursion output does everywhere
(`Nat.brecOn` is `(Nat.brecOn.go …).1`). The fixture declares its own
three-field structure and its own two-element enumeration, and the export
contains neither `Nat` nor `PProd` — asserted in `mini/tests/designed.rs`
rather than claimed here.

## The cells

| theorem | left subject | what it exercises |
| --- | --- | --- |
| `ctorTwo` | `Tri.mk x y z`, already a constructor | **control** — no reduction, no leg owed |
| `stuckOne`, `stuckTwo`, `stuckThd` | `selAlias …` against `sel …` | the defect, at all three indices |
| `flipOne`, `flipTwo`, `flipThd` | `flip …`, one ι **onto** a stuck projection | the leg is owed after the loop re-enters the arm |

## Why three fields, and why `flip` permutes them

Two fields cannot tell a projection index that is threaded from one that is
dropped: at `k = 2` every wrong index is the other field and the equation still
has two visibly different sides, so an off-by-one lands somewhere plausible.
At three, index 1 has a distinct answer on both sides.

`flip` is the part that makes that bite. It repacks `sel`'s three fields in
reverse, so `flipOne` states `(flip …).one = (sel …).thd` — the two indices
across the equation **differ**, and they differ by a different amount in each
of the three cells (`+2`, `0`, `−2`). A congruence built at a fixed wrong index,
or at the subject's index rather than the projection's, is a true equation
about the wrong field and fails the endpoint check; a congruence that happened
to be right for `flipTwo` alone is caught by its two neighbours.

The three parameters are three *distinct* types, so `flip`'s result type
`Tri γ β α` is not its argument's and a chain that walked into the wrong
component is a type error rather than a coincidence.

`Two` is not `Bool` and `Tri` is not `PProd`, for the reason
`proj_reduced_subject.lean` gives: the finding is that none of this is about
the declarations `Nat` happens to use.
-/
prelude

--#export Eq Two Tri sel selAlias flip
--#export ctorTwo stuckOne stuckTwo stuckThd flipOne flipTwo flipThd

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive Two : Type where
  | a : Two
  | b : Two

structure Tri (α : Type) (β : Type) (γ : Type) : Type where
  one : α
  two : β
  thd : γ

/-- A subject that δ-unfolds and then **gets stuck**: the recursor's major is a
variable, so no constructor ever reaches head position. -/
noncomputable def sel (α β γ : Type) (p q : Tri α β γ) (t : Two) : Tri α β γ :=
  Two.rec (motive := fun _ => Tri α β γ) p q t

/-- The same stuck subject, one δ further out — so the two sides of the
`stuck*` equations reach the identical reduct from different spellings. -/
noncomputable def selAlias (α β γ : Type) (p q : Tri α β γ) (t : Two) : Tri α β γ :=
  sel α β γ p q t

/-- A constructor application whose three fields are stuck projections, in
reverse order. -/
noncomputable def flip (α β γ : Type) (p q : Tri α β γ) (t : Two) : Tri γ β α :=
  Tri.mk (sel α β γ p q t).thd (sel α β γ p q t).two (sel α β γ p q t).one

-- ── the control: the subject is already a constructor application ───────────

theorem ctorTwo (α β γ : Type) (x : α) (y : β) (z : γ) :
    Eq (Tri.mk x y z : Tri α β γ).two y := Eq.refl _

-- ── the subject reduces and stays stuck, at all three indices ───────────────

theorem stuckOne (α β γ : Type) (p q : Tri α β γ) (t : Two) :
    Eq (selAlias α β γ p q t).one (sel α β γ p q t).one := Eq.refl _

theorem stuckTwo (α β γ : Type) (p q : Tri α β γ) (t : Two) :
    Eq (selAlias α β γ p q t).two (sel α β γ p q t).two := Eq.refl _

theorem stuckThd (α β γ : Type) (p q : Tri α β γ) (t : Two) :
    Eq (selAlias α β γ p q t).thd (sel α β γ p q t).thd := Eq.refl _

-- ── one ι onto a stuck projection, at three *different* index shifts ────────

theorem flipOne (α β γ : Type) (p q : Tri α β γ) (t : Two) :
    Eq (flip α β γ p q t).one (sel α β γ p q t).thd := Eq.refl _

theorem flipTwo (α β γ : Type) (p q : Tri α β γ) (t : Two) :
    Eq (flip α β γ p q t).two (sel α β γ p q t).two := Eq.refl _

theorem flipThd (α β γ : Type) (p q : Tri α β γ) (t : Two) :
    Eq (flip α β γ p q t).thd (sel α β γ p q t).one := Eq.refl _
