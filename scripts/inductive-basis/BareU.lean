/-
BareU.lean — every kernel-admissible declaration at a maybe-zero sort is
constructible over {Π, PULiftP, Eq, Nat}, where PULiftP is the Prop-lift
`(p : Prop) → Sort u` taken as the basis primitive.

SortPolyProbe.lean establishes the kernel's admission boundary at maybe-zero
resultant sorts: zero-constructor and subsingleton shapes get large
elimination (E0, U0, Q0, and PULiftP itself as L0); everything else that
passes the per-argument level rule gets small elimination (I0, T3, R1-like
recursive shapes, indexed F0). This file compiles a model for one occupant
of every one of those classes, from the single primitive

  inductive PULiftP (p : Prop) : Sort u | up : p → PULiftP p

plus Π, Eq and Nat (Nat and Eq only for the empty type's large eliminator).
Each model provides carrier, constructors, recursor at the kernel's own
eliminating universe for the shape, and ι as a theorem (`rfl` where noted).
No other inductive is consumed: no False, no PSigma, no Acc, no Quot, and
in particular no funext.

What this establishes for INDUCTIVE-BASIS.md:
  * the Prop-lift closes the owner's `PEmpty` gap — an EMPTY carrier at a
    bare variable sort is `PULiftP CFalse`, and its large eliminator is
    derivable because a Church-False yields 0 = 1 and Nat.rec builds a
    Sort-w family to transport along;
  * proof irrelevance makes `PULiftP p` propositionally rigid (eta), which
    is what turns subsingleton shapes' large recursors and the collapsed
    small-elimination shapes' recursors into transports;
  * the R1 model is the Church-with-strong-induction derivation
    (fold at the Church-pair of "element" and "proof") that also serves
    the recursive small-eliminating Prop class at u := 0.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean BareU.lean
Expected: 0 errors.
-/
universe u v w

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PULiftP (p : Prop) : Sort u
  | up : p → PULiftP p

namespace PULiftP
variable {p : Prop}

noncomputable def down (t : PULiftP.{u} p) : p :=
  PULiftP.rec (motive := fun _ => p) (fun h => h) t

/-- Propositional eta: every element is an `up`. The minor premise closes by
    proof irrelevance (`down (up h)` and `h` are proofs of `p`). -/
theorem eta (t : PULiftP.{u} p) : t = .up (down t) :=
  PULiftP.rec (motive := fun t => t = .up (down t)) (fun _ => rfl) t

end PULiftP

/-- Church False and Church True: the two Props the constructions seed with. -/
def CFalse : Prop := ∀ p : Prop, p
def CTrue : Prop := ∀ p : Prop, p → p

def CTrue.triv : CTrue := fun _ h => h

-- ─────────────────────────────────────────────────────────────────────────────
-- 1. The empty type at a bare sort (E0's class: zero constructors, LARGE).
-- ─────────────────────────────────────────────────────────────────────────────

noncomputable def PE : Sort u := PULiftP.{u} CFalse

/-- A unit at any sort, needed as the inhabited transport source. -/
noncomputable def PUu : Sort w := PULiftP.{w} CTrue

/-- Large elimination for the empty carrier: Church-False gives `0 = 1`, and
    `Nat.rec` builds the `Sort w`-valued family `{0 ↦ PUu, n+1 ↦ motive t}`
    to transport along. This is where Nat and Eq enter. -/
noncomputable def PE.elim {motive : PE.{u} → Sort w} (t : PE) : motive t :=
  @Eq.rec Nat 0
    (fun n _ => Nat.rec (motive := fun _ => Sort w) PUu (fun _ _ => motive t) n)
    (.up CTrue.triv)
    1
    (PULiftP.down t (0 = 1))

-- the model recursor has E0.rec's exact shape (zero minor premises):
noncomputable example : ∀ {motive : PE.{u} → Sort w} (t : PE), motive t := @PE.elim

-- ─────────────────────────────────────────────────────────────────────────────
-- 2. The unit at a bare sort (U0's class: one nullary constructor, LARGE).
-- ─────────────────────────────────────────────────────────────────────────────

noncomputable def PU : Sort u := PULiftP.{u} CTrue
noncomputable def PU.unit : PU.{u} := .up CTrue.triv

/-- The recursor: every element equals `unit` — `eta` gives `t = up (down t)`
    and proof irrelevance makes `up (down t)` and `unit` definitionally
    equal — then transport. -/
noncomputable def PU.elim {motive : PU.{u} → Sort w} (m : motive .unit)
    (t : PU) : motive t :=
  @Eq.rec PU PU.unit (fun x _ => motive x) m t (PULiftP.eta t : PU.unit = t)

noncomputable example : ∀ {motive : PU.{u} → Sort w},
    motive .unit → ∀ t, motive t := @PU.elim

/-- ι holds definitionally: on `unit` the transport is along a proof of
    `unit = unit`, which the kernel's K-like reduction for `Eq.rec` erases. -/
theorem PU.iota {motive : PU.{u} → Sort w} (m : motive .unit) :
    PU.elim m .unit = m := rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- 3. Eq at a variable sort (Q0's class: SS with index-appearing data, LARGE).
-- ─────────────────────────────────────────────────────────────────────────────

noncomputable def EqS {α : Sort u} (a : α) : α → Sort v :=
  fun b => PULiftP.{v} (a = b)

noncomputable def EqS.refl {α : Sort u} (a : α) : EqS.{u,v} a a := .up rfl

/-- The large dependent eliminator, from `Eq.rec` (index transport) plus the
    lift's eta (proof transport, closed by proof irrelevance). -/
noncomputable def EqS.elim {α : Sort u} {a : α}
    {motive : (b : α) → EqS.{u,v} a b → Sort w}
    (m : motive a (.refl a)) {b : α} (t : EqS.{u,v} a b) : motive b t :=
  @Eq.rec (EqS.{u,v} a b) (.up (PULiftP.down t))
    (fun x _ => motive b x)
    (@Eq.rec α a (fun c h => motive c (.up h)) m b (PULiftP.down t))
    t
    (PULiftP.eta t).symm

noncomputable example : ∀ {α : Sort u} {a : α}
    {motive : (b : α) → EqS.{u,v} a b → Sort w},
    motive a (.refl a) → ∀ {b} (t : EqS.{u,v} a b), motive b t := @EqS.elim

/-- ι, again definitional via K-like reduction (both transports are along
    self-equalities on the constructor). -/
theorem EqS.iota {α : Sort u} {a : α}
    {motive : (b : α) → EqS.{u,v} a b → Sort w} (m : motive a (.refl a)) :
    EqS.elim m (.refl a) = m := rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- 4. The identity shape (I0's class: one constructor, payload at the type's
--    own maybe-zero sort — SMALL elimination). The carrier is the payload.
-- ─────────────────────────────────────────────────────────────────────────────

def I0' (α : Sort u) : Sort u := α
def I0'.mk {α : Sort u} (a : α) : I0' α := a

def I0'.elim {α : Sort u} {motive : I0' α → Prop}
    (m : ∀ a, motive (.mk a)) (t : I0' α) : motive t := m t

theorem I0'.iota {α : Sort u} {motive : I0' α → Prop}
    (m : ∀ a, motive (.mk a)) (a : α) : I0'.elim m (.mk a) = m a := rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- 5. Two constructors at a bare sort (T3's class — SMALL elimination).
--    Small elimination cannot discriminate, so the carrier collapses to the
--    unit; the two ι theorems close by proof irrelevance of the Prop-valued
--    motive.
-- ─────────────────────────────────────────────────────────────────────────────

noncomputable def T3' : Sort u := PU.{u}
noncomputable def T3'.a : T3'.{u} := PU.unit
noncomputable def T3'.b : T3'.{u} := PU.unit

noncomputable def T3'.elim {motive : T3'.{u} → Prop}
    (ha : motive .a) (_hb : motive .b) (t : T3') : motive t :=
  @Eq.rec T3' T3'.a (fun x _ => motive x) ha t (PULiftP.eta t : T3'.a = t)

theorem T3'.iota_a {motive : T3'.{u} → Prop} (ha : motive .a) (hb : motive .b) :
    T3'.elim ha hb .a = ha := rfl
/-- The b-rule: the motive is a Prop, so the two sides are equal proofs. -/
theorem T3'.iota_b {motive : T3'.{u} → Prop} (ha : motive .a) (hb : motive .b) :
    T3'.elim ha hb .b = hb := rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- 6. A recursive shape at a bare sort (R1: one constructor with a recursive
--    argument under a binder — SMALL elimination, per SortPolyProbe F3).
--    Model: lift of the impredicative Church encoding; the recursor is the
--    fold at the Church-pair of "element" and "proof" (strong induction).
-- ─────────────────────────────────────────────────────────────────────────────

-- The target shape, pinned by declaring it. The KERNEL accepts the
-- declaration (the `example` against @R1.rec below typechecks); what fails
-- is the front end's auxiliary `SizeOf`/`below`/`brecOn` generation, which
-- assumes large elimination. Those front-end failures are pinned here:
/--
error: failed to generate `SizeOf` instance for `R1`:
  incorrect number of universe levels R1._sizeOf_1
---
error: (kernel) application type mismatch
  @R1.rec fun t => Sort (max u u)
argument has type
  R1 → Type (max u u)
but function has type
  {motive : R1 → Prop} →
    (∀ (a : @PULiftP CTrue → R1), (∀ (a_1 : @PULiftP CTrue), motive (a a_1)) → motive (@R1.mk a)) → ∀ (t : R1), motive t
---
error: (kernel) application type mismatch
  @R1.rec fun t => motive t ×' @R1.below motive t
argument has type
  R1 → Sort (max 1 u)
but function has type
  {motive : R1 → Prop} →
    (∀ (a : @PULiftP CTrue → R1), (∀ (a_1 : @PULiftP CTrue), motive (a a_1)) → motive (@R1.mk a)) → ∀ (t : R1), motive t
---
error: (kernel) invalid reference to undefined universe level parameter 'u'
-/
#guard_msgs (error) in
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive R1 : Sort u
  | mk : (PULiftP.{u} CTrue → R1) → R1

example : ∀ {motive : R1.{u} → Prop},
    (∀ f, (∀ x, motive (f x)) → motive (.mk f)) → ∀ t, motive t := @R1.rec

-- the model:
def R1P : Prop := ∀ C : Prop, ((PU.{u} → C) → C) → C

noncomputable def R1' : Sort u := PULiftP.{u} R1P.{u}

noncomputable def R1'.mk (f : PU.{u} → R1'.{u}) : R1'.{u} :=
  .up (fun C step => step (fun x => PULiftP.down (f x) C step))

/-- The small dependent recursor. Fold at the Church-conjunction
    `C := ∀ D : Prop, (R1P → (∀ h, motive (up h)) → D) → D`; the step
    rebuilds the element alongside the proof, and every appeal to "which
    proof of `R1P`" closes by proof irrelevance. -/
noncomputable def R1'.elim {motive : R1'.{u} → Prop}
    (m : ∀ f : PU.{u} → R1'.{u}, (∀ x, motive (f x)) → motive (.mk f))
    (t : R1') : motive t :=
  let C : Prop := ∀ D : Prop, (R1P.{u} → (∀ h : R1P.{u}, motive (.up h)) → D) → D
  let fold : C :=
    PULiftP.down t C (fun (g : PU.{u} → C) _D k =>
      -- rebuild the element:
      let hcomb : R1P.{u} := fun Cc stepc =>
        stepc (fun x => g x R1P.{u} (fun he _ => he) Cc stepc)
      -- rebuild the proof, as `motive (mk f)` for the rebuilt subtrees f:
      let f : PU.{u} → R1'.{u} := fun x => .up (g x R1P.{u} (fun he _ => he))
      let ih : ∀ x, motive (f x) := fun x =>
        g x (∀ h : R1P.{u}, motive (.up h)) (fun _ hp => hp)
          (g x R1P.{u} (fun he _ => he))
      k hcomb (fun _ => m f ih))
  fold (motive t) (fun _ hp =>
    @Eq.rec R1' (.up (PULiftP.down t)) (fun x _ => motive x)
      (hp (PULiftP.down t)) t (PULiftP.eta t).symm)

theorem R1'.iota {motive : R1'.{u} → Prop}
    (m : ∀ f : PU.{u} → R1'.{u}, (∀ x, motive (f x)) → motive (.mk f))
    (f : PU.{u} → R1'.{u}) :
    R1'.elim m (.mk f) = m f (fun x => R1'.elim m (f x)) := rfl

-- ── Axiom audit: the constructions are axiom-free ──────────────────────────
/-- info: 'PE.elim' does not depend on any axioms -/
#guard_msgs in #print axioms PE.elim
/-- info: 'PU.elim' does not depend on any axioms -/
#guard_msgs in #print axioms PU.elim
/-- info: 'EqS.elim' does not depend on any axioms -/
#guard_msgs in #print axioms EqS.elim
/-- info: 'R1'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms R1'.elim
