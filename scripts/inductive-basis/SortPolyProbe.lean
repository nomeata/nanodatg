/-
SortPolyProbe.lean — what Lean's KERNEL admits at a maybe-zero resultant sort.

Establishes, at leanprover/lean4:v4.29.1, the exact boundary of universe-
polymorphic inductive declarations whose resultant sort is a level expression
that is zero at some instantiations and nonzero at others (`Sort u`,
`Sort (max u v)`, ...), and the eliminating universe each admitted shape gets.

Two rules are in play and they differ:
  * the ELABORATOR refuses every maybe-zero resultant sort
    ("Invalid universe polymorphic resulting type"), an over-approximation
    that core itself bypasses for PUnit and PEmpty with
    `set_option bootstrap.inductiveCheckResultingUniverse false`
    (Init/Prelude.lean:123,211 at v4.29.1);
  * the KERNEL (src/kernel/inductive.cpp) checks only, per constructor
    argument, `is_geq(result_level, arg_level) || is_zero(result_level)`,
    and computes the eliminating universe by `elim_only_at_universe_zero`:
    large elimination iff the resultant level `is_not_zero`, OR the block is
    a single inductive with zero constructors, OR a single constructor whose
    arguments each are Props or appear in the result indices (subsingleton).

This file is a `prelude` file so that the front end's auxiliary constructions
(sizeOf, ctorIdx, noConfusion, below/brecOn — all gated on Nat/Unit/Prod/Eq
existing, and some of them impossible for small-eliminating shapes) stay out
of the way; every inductive below goes through the kernel as declared.

Findings pinned below:
  F1. The kernel admits zero-constructor and subsingleton-shaped declarations
      at any maybe-zero sort, with LARGE elimination (E0, U0, L0, Q0, M0).
  F2. The kernel also admits arbitrary-constructor declarations at maybe-zero
      sorts (I0, T3, F0, the mutual MA/MB) — but with SMALL elimination.
  F3. A recursive argument at a maybe-zero sort KILLS the subsingleton grant:
      its type is at the maybe-zero level, hence not syntactically a Prop, so
      R0.rec is small — unlike Acc at literal Prop, where the recursive
      argument's type is a Prop and SS survives.
  F4. Level arithmetic: imax u u = u; imax 0 u = u; max 1 absorbs into
      never-zero levels; imax with never-zero right side becomes max; but a
      max does NOT absorb an imax it dominates semantically (L5) — Lean's
      level defeq is normal-form equality, not semantic equality.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean SortPolyProbe.lean

Expected: 0 errors. (Negative probes live in SortPolyNeg.lean,
  which needs #guard_msgs and hence Init.)
-/
prelude
universe u v w

set_option bootstrap.inductiveCheckResultingUniverse false

-- Minimal own environment (this is a prelude file: no False, Bool, Eq yet).
inductive PFalse : Prop
inductive B2 : Type
  | tt
  | ff

-- ── Positive probes: the kernel admits all of these at maybe-zero sorts ─────

-- P1: zero constructors (PEmpty's shape) — large-eliminating.
inductive E0 : Sort u

-- P2: one constructor, no arguments (PUnit's shape) — large-eliminating (SS).
inductive U0 : Sort u
  | unit

-- P3: one constructor, one Prop argument — the "lift a Prop to Sort u"
--     former. Large-eliminating (SS: the argument is a proposition).
--     This is the shape this document's basis takes as its fifth member.
inductive L0 (p : Prop) : Sort u
  | up : p → L0 p

-- P4: one constructor, argument at the type's own maybe-zero sort.
--     Admitted (arg level u, is_geq(u,u)), but NOT subsingleton-shaped:
--     the argument is neither a Prop nor an index — small-eliminating.
inductive I0 (α : Sort u) : Sort u
  | mk : α → I0 α

-- P5: indexed, Eq's shape at a variable resultant sort — large (SS).
inductive Q0 (α : Sort u) (a : α) : α → Sort v
  | refl : Q0 α a a

-- P6: recursive argument at a maybe-zero sort — admitted, and SMALL:
--     the argument's type (E0 → R0) sits at level imax u u = u, which is
--     not syntactically a Prop, so the subsingleton test fails (F3).
inductive R0 : Sort u
  | mk : (E0.{u} → R0) → R0

-- P7: TWO constructors at a maybe-zero sort. Admitted — and forced small:
--     at u := 0 both constructors are proofs of one Prop, so a
--     large-eliminating recursor would prove False by discrimination.
inductive T3 : Sort u
  | a
  | b

-- P8: maybe-zero `max u v`, zero constructors — large.
inductive M0 : Sort (max u v)

-- P9: two nullary constructors separated by an index — the fibered form of
--     a mutual pair of PUnits. Admitted, small-eliminating (2 constructors).
inductive F0 : B2 → Sort u
  | a : F0 .tt
  | b : F0 .ff

-- P11: the PSigma SHAPE at `Sort (max u v)` — the `max 1` question. The
--     ELABORATOR refuses this (SortPolyNeg N2's rule); the KERNEL admits it,
--     with small elimination (one constructor, arguments neither Props nor
--     indices). Core's `PSigma : Sort (max 1 u v)` is therefore the price of
--     large elimination (never-zero resultant), not a kernel admission
--     boundary.
inductive S0 (α : Sort u) (β : α → Sort v) : Sort (max u v)
  | mk : (a : α) → β a → S0 α β

-- P10: a mutual pair at Sort u — admitted, small (block size > 1).
mutual
  inductive MA : Sort u
    | mk : MB → MA
  inductive MB : Sort u
    | mk : MA → MB
end

-- ── The eliminating universes, pinned ──────────────────────────────────────
-- Large where claimed large:
noncomputable example : ∀ {motive : E0.{u} → Sort w} (t : E0), motive t := @E0.rec
noncomputable example : ∀ {motive : U0.{u} → Sort w}, motive .unit → ∀ t, motive t := @U0.rec
noncomputable example : ∀ {p : Prop} {motive : L0.{u} p → Sort w},
    (∀ h, motive (.up h)) → ∀ t, motive t := @L0.rec
noncomputable example : ∀ {motive : M0.{u,v} → Sort w} (t : M0), motive t := @M0.rec
noncomputable example : ∀ {α : Sort u} {a : α} {motive : (b : α) → Q0.{u,v} α a b → Sort w},
    motive a .refl → ∀ {b} (t : Q0 α a b), motive b t := @Q0.rec
-- Small where claimed small (the motive's codomain is Prop, not Sort _):
example : ∀ {α : Sort u} {motive : I0 α → Prop},
    (∀ a, motive (.mk a)) → ∀ t, motive t := @I0.rec
example : ∀ {motive : R0.{u} → Prop},
    (∀ f, (∀ e, motive (f e)) → motive (.mk f)) → ∀ t, motive t := @R0.rec
example : ∀ {motive : T3.{u} → Prop},
    motive .a → motive .b → ∀ t, motive t := @T3.rec
example : ∀ {motive : ∀ b, F0.{u} b → Prop},
    motive .tt .a → motive .ff .b → ∀ b (t : F0 b), motive b t := @F0.rec
example : ∀ {motive_1 : MA.{u} → Prop} {motive_2 : MB.{u} → Prop},
    (∀ b, motive_2 b → motive_1 (.mk b)) → (∀ a, motive_1 a → motive_2 (.mk a)) →
    ∀ t, motive_1 t := @MA.rec
example : ∀ {α : Sort u} {β : α → Sort v} {motive : S0 α β → Prop},
    (∀ a b, motive (.mk a b)) → ∀ t, motive t := @S0.rec

-- ── Level-arithmetic facts the constructions lean on ───────────────────────

-- L1: imax u u = u (a Π from a bare-u type to a bare-u type stays at bare u).
example : Sort u := E0.{u} → E0.{u}
-- L2: the False-Π collapse, imax 0 u = u.
noncomputable example : Sort u := (h : PFalse) → PFalse.rec (motive := fun _ => Sort u) h
-- L3: max 1 absorbs into a never-zero level.
example : Type u := U0.{max 1 (u+1)}
example : Sort (max 1 u) := U0.{max 1 (max 1 u)}
-- L4: imax with a never-zero right side collapses to max.
example : Sort (max u 1 v) := U0.{imax u (max 1 v)}
