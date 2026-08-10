/-
CoreFacts.lean — core-library facts the basis document cites, pinned at
leanprover/lean4:v4.29.1. Each is a one-line typecheck; a toolchain where
any of these change breaks this file.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean CoreFacts.lean
Expected: 0 errors.
-/
universe u v w

-- And is LARGE-eliminating (subsingleton: both constructor args are Props).
example : ∀ {a b : Prop} {motive : a ∧ b → Sort w},
    ((ha : a) → (hb : b) → motive ⟨ha, hb⟩) → ∀ t, motive t := @And.rec
-- Exists is SMALL-eliminating only (the witness argument is not a Prop and
-- not an index).
example : ∀ {α : Sort u} {p : α → Prop} {motive : Exists p → Prop},
    (∀ a (h : p a), motive ⟨a, h⟩) → ∀ t, motive t := @Exists.rec
-- Subtype sits at Sort (max 1 u) — the PSigma level with a Prop second
-- component; Subtype IS the PSigma shape.
example : Sort (max 1 u) := Subtype (fun _ : PUnit.{u} => True)
example (α : Sort u) (β : α → Sort v) : Sort (max 1 u v) := PSigma β
example (α : Sort u) (β : Sort v) : Sort (max 1 u v) := PSum α β
-- PUnit and PEmpty are core's two bare-variable-sort inductives, declared
-- behind `bootstrap.inductiveCheckResultingUniverse false`; both
-- large-eliminating.
example : Sort u := PUnit.{u}
example : Sort u := PEmpty.{u}
noncomputable example : ∀ {motive : PEmpty.{u} → Sort w} (t : PEmpty),
    motive t := @PEmpty.rec
noncomputable example : ∀ {motive : PUnit.{u} → Sort w},
    motive .unit → ∀ t, motive t := @PUnit.rec
-- ULift is Type-to-Type and max-shaped; PLift lifts a Sort into Type u.
-- Neither reaches a bare-variable target sort.
example (α : Type v) : Type (max v u) := ULift α
example (α : Sort u) : Type u := PLift α
-- Quot preserves its carrier's level exactly (no max 1) — but cannot
-- create inhabitants or emptiness, so it does not affect the bare-sort
-- reachability argument.
example (α : Sort u) (r : α → α → Prop) : Sort u := Quot r
