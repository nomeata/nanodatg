/-
AccArmShapes.lean — the `AccFromChoice` recipe is UNIFORM in the constructor's
field shape: three more subsingleton-recursive shapes, each carried through the
same nine steps, each pinned against the kernel's own recursor type.

`AccFromChoice.lean` derives `Acc.rec`'s exact type over no inductive primitive
(Church carrier + `Classical.choice`, recursion defined by its GRAPH), and
repeats the derivation once (§6, `CD`/`DD`) for a shape with one extra PROOF
field. Two shapes are not enough to conclude that a `modelgen` arm can emit
this for an ARBITRARY recursive subsingleton — an inductive `Prop` with one
constructor each of whose fields is a proposition or a variable that is
literally one of the conclusion's indices. This file settles the open
dimensions by compiling the recipe on three shapes `AccFromChoice` misses.

VERDICT: uniform. All three go through, verbatim in structure; only two lines
of the recipe are shape-sensitive, and both are mechanical:

  * `Graph.unique`'s congruence must be an n-ARY congruence in the recursive
    fields (`congrArg` composed with `Eq.trans`, one factor per field), and
  * the `funext` chain inside it is per BINDER of a recursive field, so a
    recursive field with no binders contributes none.

SHAPES.

  S1  inductive I1 : Prop | mk : I1 → I1
      No parameters, no indices, one recursive field with NO binders. The
      degenerate case: the recursive "argument function" is not a function.

  S2  inductive I2 (r s : Nat → Nat → Prop) : Nat → Prop
        | mk : (x : Nat) → ((y : Nat) → r y x → I2 r s y) →
               ((y : Nat) → s y x → I2 r s y) → I2 r s x
      TWO recursive fields — the shape on which `AccFromChoice`'s single
      `congrArg (step x h)` is insufficient. Their domains differ (`r` vs `s`)
      on purpose, so that swapping them is a type error: the shape can catch a
      field-ORDER bug, which two identical fields could not.

  S3  inductive I3 (q : Prop) (p : Nat → Prop) (r : Nat → Nat → Prop) : Nat → Prop
        | mk : (x : Nat) → q → ((y : Nat) → r y x → I3 q p r y) → p x → I3 q p r x
      A non-recursive proof field on BOTH sides of the recursive one, three
      fields total. `q`, the recursive field and `p x` are pairwise
      distinguishable types, so any permutation is a type error; with fields
      only before (or only after) the recursion an ordering bug is invisible.

AXIOM TABLE (measured, pinned with `#guard_msgs` below).

    shape   rec'                  iota
    ------  --------------------  --------------------------------
    S1      [Classical.choice]    [Classical.choice]
    S2      [Classical.choice]    [Classical.choice, Quot.sound]
    S3      [Classical.choice]    [Classical.choice, Quot.sound]
    CAcc    [Classical.choice]    [Classical.choice, Quot.sound]   (AccFromChoice §3)
    CD      [Classical.choice]    [Classical.choice, Quot.sound]   (AccFromChoice §6)

S1's ι costs NO `Quot.sound`. That is a real result, and it says the axiom cost
is PER SHAPE, not per arm: `funext` (which is what `Quot.sound` is standing in
for — core proves `funext` via `Quot`) enters `Graph.unique` only to equate two
recursive-argument FUNCTIONS pointwise, and S1's recursive argument is a bare
value, so the induction hypothesis already delivers `f1 = f2` and plain
`congrArg` closes the proof. `funext` is charged per binder of a recursive
field, not per use of the recipe. Totality never needs it in any shape, so
`rec'` is `[Classical.choice]` everywhere; only ι pays. S1 is nevertheless
still NOT definitional — pinned as a `#guard_msgs (error)` below — because the
value is a `Classical.choice` application whichever shape it comes from.

MEASURED UNIFORM IN:
  * the NUMBER of recursive fields (S1/S3/CAcc: one; S2: two);
  * recursive fields WITH binders (CAcc, S2, S3) and WITHOUT (S1);
  * non-recursive PROOF fields before the recursive one (CD), after it, and on
    both sides at once (S3);
  * the presence of a DATA field that is literally the conclusion's index
    (CAcc, S2, S3: the field `x`) and its absence (S1);
  * parameters that are relations (S2's `r`, `s`), predicates (S3's `p`) or
    bare propositions (S3's `q`), and their total absence (S1);
  * indices present (S2, S3, CAcc) and absent (S1).

STILL NOT UNIFORM IN — unchanged from `AccFromChoice` §6: constructor arguments
that are DATA occurring inside the conclusion's INDEX EXPRESSION where the
index does not determine them. Every data field here is a variable that IS an
index (Lean's subsingleton rule permits nothing else), so inversion recovers it
definitionally; where an index expression is not a variable, inversion needs
the index's injectivity, and in the limiting case (`Eq`) the Church encoding is
Leibniz equality and this route does not reach J. That case is outside this
class anyway — it is non-recursive, and `BareU.lean` models it from `PULiftP`.

THE SHAPES DISCRIMINATE, and that is measured rather than asserted — a pin
that cannot fail is worth nothing, and S2 and S3 exist precisely to catch a
field-order bug in the arm that will emit this:

  * S2's two recursive fields swapped in `C2.iota`'s right-hand side —
    **red**: `hy : r y x` is not `s y x`. Two *identical* recursive fields
    would have been green, which is why the domains differ.
  * S3's `hq : q` and `hp : p x` swapped in `C3.iota`'s right-hand side —
    **red**: `p x` is not `q`. A shape whose non-recursive fields had the same
    type, or sat on only one side of the recursion, would have been green.

TACTICS: none, anywhere. Every proof is a raw term (`fun`, `Eq.trans`,
`Eq.symm`, `congrArg`, `funext`, `rfl`), so a generator can emit all of it as
`Expr`s.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean AccArmShapes.lean
Expected: 0 errors.
-/
universe v
set_option linter.unusedVariables false

/-- Church conjunction, so the folds below need no `And`. Same definition as
    `AccFromChoice.lean` §0; this file has no imports either. -/
def AndC (A B : Prop) : Prop := ∀ D : Prop, (A → B → D) → D

-- ═════════════════════════════════════════════════════════════════════════
-- §1. S1 — `I1 : Prop | mk : I1 → I1`. No parameters, no indices, one
--     recursive field with NO binders. The degenerate shape.
-- ═════════════════════════════════════════════════════════════════════════

/-- The yardstick declaration. Lean grants it large elimination by the
    subsingleton rule: one constructor, and its single field is a `Prop`. -/
inductive I1 : Prop
  | mk : I1 → I1

/-- The impredicative Church carrier. (`I1` and `C1` are both empty — there is
    no base case — which is irrelevant to the recursor's derivation and is
    exactly why an ι rule must still be produced.) -/
def C1 : Prop := ∀ P : Prop, (P → P) → P

theorem C1.mk (a : C1) : C1 := fun P s => s (a P s)

/-- The free Prop-motive recursor: fold at the Church conjunction of "is a
    `C1`" and "the motive holds at every proof". -/
theorem C1.ind {motive : C1 → Prop}
    (step : (a : C1) → motive a → motive (C1.mk a))
    (t : C1) : motive t :=
  t (AndC C1 (∀ s : C1, motive s))
    (fun g =>
      let h : C1 := g C1 (fun c _ => c)
      let ih : motive h := g (motive h) (fun _ m => m h)
      fun D k => k (C1.mk h) (fun _s => step h ih))
    (motive t) (fun _ m => m t)

section Rec1
variable {motive : C1 → Sort v}
  (step : (a : C1) → motive a → motive (C1.mk a))

/-- "`val` is what the recursion produces at `t`", impredicatively. -/
def G1 (t : C1) (val : motive t) : Prop :=
  ∀ Q : (s : C1) → motive s → Prop,
    ((a : C1) → (f : motive a) → Q a f → Q (C1.mk a) (step a f)) →
    Q t val

theorem G1.mk (a : C1) (f : motive a) (hf : G1 step a f) :
    G1 step (C1.mk a) (step a f) :=
  fun Q q => q a f (hf Q q)

/-- Inversion. The recursive field `a` is itself a proof, so it is universally
    quantified and recovered by proof irrelevance — the same clause as
    `AccFromChoice`'s `GraphInv`, with the binder list of the recursive field
    (there empty here) contributing nothing. -/
def G1Inv (t : C1) (val : motive t) : Prop :=
  ∀ (a : C1) (D : Prop),
    ((f : motive a) → G1 step a f → val = step a f → D) → D

theorem G1.inv {t : C1} {val : motive t} (g : G1 step t val) :
    G1Inv step t val :=
  g (fun s w => AndC (G1 step s w) (G1Inv step s w))
    (fun a f ih =>
      let hg : G1 step a f := ih (G1 step a f) (fun b _ => b)
      fun D k => k (G1.mk step a f hg) (fun _a' _D' k' => k' f hg rfl))
    (G1Inv step t val) (fun _g i => i)

/-- Single-valuedness. THE POINT OF S1: no `funext`. The recursive argument is
    a value, not a function, so the induction hypothesis hands over `f1 = f2`
    directly and one `congrArg` closes it. This is why S1's ι does not pay
    `Quot.sound`. -/
theorem G1.unique (t : C1) (v w : motive t)
    (gv : G1 step t v) (gw : G1 step t w) : v = w :=
  C1.ind
    (motive := fun t => ∀ v w : motive t,
      G1 step t v → G1 step t w → v = w)
    (fun a ih v w gv gw =>
      G1.inv step gv a (v = w) (fun f1 hf1 e1 =>
        G1.inv step gw a (v = w) (fun f2 hf2 e2 =>
          e1.trans (Eq.trans
            (congrArg (step a) (ih f1 f2 hf1 hf2))
            e2.symm))))
    t v w gv gw

theorem G1.exists (t : C1) :
    Nonempty (PSigma fun val : motive t => G1 step t val) :=
  C1.ind
    (motive := fun t => Nonempty (PSigma fun val : motive t => G1 step t val))
    (fun a ih =>
      Nonempty.intro
        ⟨step a (Classical.choice ih).fst,
         G1.mk step a (Classical.choice ih).fst (Classical.choice ih).snd⟩)
    t

noncomputable def C1.rec' (t : C1) : motive t :=
  (Classical.choice (G1.exists step t)).fst

theorem C1.rec'_graph (t : C1) : G1 step t (C1.rec' step t) :=
  (Classical.choice (G1.exists step t)).snd

theorem C1.iota (a : C1) :
    C1.rec' step (C1.mk a) = step a (C1.rec' step a) :=
  G1.unique step (C1.mk a) _ _
    (C1.rec'_graph step (C1.mk a))
    (G1.mk step a (C1.rec' step a) (C1.rec'_graph step a))

-- Cheaper in axioms, but still not definitional: the value is a
-- `Classical.choice` application, which reduces to nothing.
/--
error: Type mismatch
  Eq.refl (C1.rec' step (C1.mk a))
has type
  C1.rec' step ⋯ = C1.rec' step ⋯
but is expected to have type
  C1.rec' step ⋯ = step a (C1.rec' step a)
-/
#guard_msgs (error) in
example (a : C1) :
    C1.rec' step (C1.mk a) = step a (C1.rec' step a) :=
  Eq.refl (C1.rec' step (C1.mk a))

end Rec1

/-- The kernel's own grant, transcribed from `#check @I1.rec` with `I1 := C1`. -/
noncomputable example : ∀ {motive : C1 → Sort v},
    ((a : C1) → motive a → motive (C1.mk a)) → (t : C1) → motive t := @C1.rec'

/-- ... and the very same transcription against the real inductive, so the
    transcription is checked against Lean rather than trusted. -/
noncomputable example : ∀ {motive : I1 → Sort v},
    ((a : I1) → motive a → motive (I1.mk a)) → (t : I1) → motive t := @I1.rec

/-- info: 'C1.rec'' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms C1.rec'
/-- info: 'C1.iota' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms C1.iota
/-- info: 'C1.ind' does not depend on any axioms -/
#guard_msgs in #print axioms C1.ind

-- ═════════════════════════════════════════════════════════════════════════
-- §2. S2 — TWO recursive fields, with different domains. The shape that
--     breaks a one-argument `congrArg` in `Graph.unique`.
-- ═════════════════════════════════════════════════════════════════════════

inductive I2 (r s : Nat → Nat → Prop) : Nat → Prop
  | mk : (x : Nat) → ((y : Nat) → r y x → I2 r s y) →
         ((y : Nat) → s y x → I2 r s y) → I2 r s x

def C2 (r s : Nat → Nat → Prop) (x : Nat) : Prop :=
  ∀ P : Nat → Prop,
    ((y : Nat) → ((z : Nat) → r z y → P z) → ((z : Nat) → s z y → P z) → P y) →
    P x

theorem C2.mk {r s : Nat → Nat → Prop} (x : Nat)
    (h1 : (y : Nat) → r y x → C2 r s y)
    (h2 : (y : Nat) → s y x → C2 r s y) : C2 r s x :=
  fun P k => k x (fun z hz => h1 z hz P k) (fun z hz => h2 z hz P k)

theorem C2.ind {r s : Nat → Nat → Prop}
    {motive : (x : Nat) → C2 r s x → Prop}
    (step : (x : Nat) → (h1 : (y : Nat) → r y x → C2 r s y) →
      (h2 : (y : Nat) → s y x → C2 r s y) →
      ((y : Nat) → (hy : r y x) → motive y (h1 y hy)) →
      ((y : Nat) → (hy : s y x) → motive y (h2 y hy)) →
      motive x (C2.mk x h1 h2))
    {x : Nat} (t : C2 r s x) : motive x t :=
  t (fun y => AndC (C2 r s y) (∀ w : C2 r s y, motive y w))
    (fun y g1 g2 =>
      let h1 : (z : Nat) → r z y → C2 r s z :=
        fun z hz => g1 z hz (C2 r s z) (fun c _ => c)
      let h2 : (z : Nat) → s z y → C2 r s z :=
        fun z hz => g2 z hz (C2 r s z) (fun c _ => c)
      let ih1 : (z : Nat) → (hz : r z y) → motive z (h1 z hz) :=
        fun z hz => g1 z hz (motive z (h1 z hz)) (fun _ m => m (h1 z hz))
      let ih2 : (z : Nat) → (hz : s z y) → motive z (h2 z hz) :=
        fun z hz => g2 z hz (motive z (h2 z hz)) (fun _ m => m (h2 z hz))
      fun D k => k (C2.mk y h1 h2) (fun _w => step y h1 h2 ih1 ih2))
    (motive x t) (fun _ m => m t)

section Rec2
variable {r s : Nat → Nat → Prop} {motive : (x : Nat) → C2 r s x → Sort v}
  (step : (x : Nat) → (h1 : (y : Nat) → r y x → C2 r s y) →
    (h2 : (y : Nat) → s y x → C2 r s y) →
    ((y : Nat) → (hy : r y x) → motive y (h1 y hy)) →
    ((y : Nat) → (hy : s y x) → motive y (h2 y hy)) →
    motive x (C2.mk x h1 h2))

def G2 (x : Nat) (t : C2 r s x) (val : motive x t) : Prop :=
  ∀ Q : (y : Nat) → (w : C2 r s y) → motive y w → Prop,
    ((y : Nat) → (h1 : (z : Nat) → r z y → C2 r s z) →
      (h2 : (z : Nat) → s z y → C2 r s z) →
      (f1 : (z : Nat) → (hz : r z y) → motive z (h1 z hz)) →
      (f2 : (z : Nat) → (hz : s z y) → motive z (h2 z hz)) →
      ((z : Nat) → (hz : r z y) → Q z (h1 z hz) (f1 z hz)) →
      ((z : Nat) → (hz : s z y) → Q z (h2 z hz) (f2 z hz)) →
      Q y (C2.mk y h1 h2) (step y h1 h2 f1 f2)) →
    Q x t val

theorem G2.mk (x : Nat) (h1 : (y : Nat) → r y x → C2 r s y)
    (h2 : (y : Nat) → s y x → C2 r s y)
    (f1 : (y : Nat) → (hy : r y x) → motive y (h1 y hy))
    (f2 : (y : Nat) → (hy : s y x) → motive y (h2 y hy))
    (hf1 : (y : Nat) → (hy : r y x) → G2 step y (h1 y hy) (f1 y hy))
    (hf2 : (y : Nat) → (hy : s y x) → G2 step y (h2 y hy) (f2 y hy)) :
    G2 step x (C2.mk x h1 h2) (step x h1 h2 f1 f2) :=
  fun Q q => q x h1 h2 f1 f2 (fun z hz => hf1 z hz Q q) (fun z hz => hf2 z hz Q q)

def G2Inv (x : Nat) (t : C2 r s x) (val : motive x t) : Prop :=
  ∀ (h1 : (y : Nat) → r y x → C2 r s y) (h2 : (y : Nat) → s y x → C2 r s y)
    (D : Prop),
    ((f1 : (y : Nat) → (hy : r y x) → motive y (h1 y hy)) →
      (f2 : (y : Nat) → (hy : s y x) → motive y (h2 y hy)) →
      ((y : Nat) → (hy : r y x) → G2 step y (h1 y hy) (f1 y hy)) →
      ((y : Nat) → (hy : s y x) → G2 step y (h2 y hy) (f2 y hy)) →
      val = step x h1 h2 f1 f2 → D) → D

theorem G2.inv {x : Nat} {t : C2 r s x} {val : motive x t}
    (g : G2 step x t val) : G2Inv step x t val :=
  g (fun z w u => AndC (G2 step z w u) (G2Inv step z w u))
    (fun y h1 h2 f1 f2 ih1 ih2 =>
      let hg1 : (z : Nat) → (hz : r z y) → G2 step z (h1 z hz) (f1 z hz) :=
        fun z hz => ih1 z hz (G2 step z (h1 z hz) (f1 z hz)) (fun b _ => b)
      let hg2 : (z : Nat) → (hz : s z y) → G2 step z (h2 z hz) (f2 z hz) :=
        fun z hz => ih2 z hz (G2 step z (h2 z hz) (f2 z hz)) (fun b _ => b)
      fun D k => k (G2.mk step y h1 h2 f1 f2 hg1 hg2)
        (fun _h1' _h2' _D' k' => k' f1 f2 hg1 hg2 rfl))
    (G2Inv step x t val) (fun _g i => i)

/-- Single-valuedness. THE POINT OF S2: `congrArg (step x h1 h2)` alone is not
    enough — the step function takes TWO recursive-argument functions, so the
    congruence is binary, built as a composite of two `congrArg`s through the
    intermediate term `step x h1 h2 fb1 fa2`. Generalising, an n-ary shape
    needs an (n+1)-term `Eq.trans` chain, one factor per recursive field. -/
theorem G2.unique {x : Nat} (t : C2 r s x) (v w : motive x t)
    (gv : G2 step x t v) (gw : G2 step x t w) : v = w :=
  C2.ind
    (motive := fun x t => ∀ v w : motive x t,
      G2 step x t v → G2 step x t w → v = w)
    (fun x h1 h2 ih1 ih2 v w gv gw =>
      G2.inv step gv h1 h2 (v = w) (fun fa1 fa2 hfa1 hfa2 ea =>
        G2.inv step gw h1 h2 (v = w) (fun fb1 fb2 hfb1 hfb2 eb =>
          ea.trans (Eq.trans
            (Eq.trans
              (congrArg (fun a => step x h1 h2 a fa2)
                (funext fun y => funext fun hy =>
                  ih1 y hy (fa1 y hy) (fb1 y hy) (hfa1 y hy) (hfb1 y hy)))
              (congrArg (step x h1 h2 fb1)
                (funext fun y => funext fun hy =>
                  ih2 y hy (fa2 y hy) (fb2 y hy) (hfa2 y hy) (hfb2 y hy))))
            eb.symm))))
    t v w gv gw

theorem G2.exists {x : Nat} (t : C2 r s x) :
    Nonempty (PSigma fun val : motive x t => G2 step x t val) :=
  C2.ind
    (motive := fun x t =>
      Nonempty (PSigma fun val : motive x t => G2 step x t val))
    (fun x h1 h2 ih1 ih2 =>
      Nonempty.intro
        ⟨step x h1 h2 (fun y hy => (Classical.choice (ih1 y hy)).fst)
           (fun y hy => (Classical.choice (ih2 y hy)).fst),
         G2.mk step x h1 h2 (fun y hy => (Classical.choice (ih1 y hy)).fst)
           (fun y hy => (Classical.choice (ih2 y hy)).fst)
           (fun y hy => (Classical.choice (ih1 y hy)).snd)
           (fun y hy => (Classical.choice (ih2 y hy)).snd)⟩)
    t

noncomputable def C2.rec' {x : Nat} (t : C2 r s x) : motive x t :=
  (Classical.choice (G2.exists step t)).fst

theorem C2.rec'_graph {x : Nat} (t : C2 r s x) :
    G2 step x t (C2.rec' step t) :=
  (Classical.choice (G2.exists step t)).snd

theorem C2.iota (x : Nat) (h1 : (y : Nat) → r y x → C2 r s y)
    (h2 : (y : Nat) → s y x → C2 r s y) :
    C2.rec' step (C2.mk x h1 h2)
      = step x h1 h2 (fun y hy => C2.rec' step (h1 y hy))
          (fun y hy => C2.rec' step (h2 y hy)) :=
  G2.unique step (C2.mk x h1 h2) _ _
    (C2.rec'_graph step (C2.mk x h1 h2))
    (G2.mk step x h1 h2 (fun y hy => C2.rec' step (h1 y hy))
      (fun y hy => C2.rec' step (h2 y hy))
      (fun y hy => C2.rec'_graph step (h1 y hy))
      (fun y hy => C2.rec'_graph step (h2 y hy)))

end Rec2

/-- `#check @I2.rec`, transcribed with `I2 := C2`. -/
noncomputable example : ∀ {r s : Nat → Nat → Prop}
    {motive : (a : Nat) → C2 r s a → Sort v},
    ((x : Nat) → (h1 : ∀ (y : Nat), r y x → C2 r s y) →
      (h2 : ∀ (y : Nat), s y x → C2 r s y) →
      ((y : Nat) → (hy : r y x) → motive y (h1 y hy)) →
      ((y : Nat) → (hy : s y x) → motive y (h2 y hy)) →
      motive x (C2.mk x h1 h2)) →
    {a : Nat} → (t : C2 r s a) → motive a t := @C2.rec'

/-- The same transcription, against Lean's own recursor. -/
noncomputable example : ∀ {r s : Nat → Nat → Prop}
    {motive : (a : Nat) → I2 r s a → Sort v},
    ((x : Nat) → (h1 : ∀ (y : Nat), r y x → I2 r s y) →
      (h2 : ∀ (y : Nat), s y x → I2 r s y) →
      ((y : Nat) → (hy : r y x) → motive y (h1 y hy)) →
      ((y : Nat) → (hy : s y x) → motive y (h2 y hy)) →
      motive x (I2.mk x h1 h2)) →
    {a : Nat} → (t : I2 r s a) → motive a t := @I2.rec

/-- info: 'C2.rec'' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms C2.rec'
/-- info: 'C2.iota' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms C2.iota
/-- info: 'C2.ind' does not depend on any axioms -/
#guard_msgs in #print axioms C2.ind

-- ═════════════════════════════════════════════════════════════════════════
-- §3. S3 — a non-recursive proof field on BOTH sides of the recursive one.
--     Three fields, pairwise distinguishable: any permutation is a type error.
-- ═════════════════════════════════════════════════════════════════════════

inductive I3 (q : Prop) (p : Nat → Prop) (r : Nat → Nat → Prop) : Nat → Prop
  | mk : (x : Nat) → q → ((y : Nat) → r y x → I3 q p r y) → p x → I3 q p r x

def C3 (q : Prop) (p : Nat → Prop) (r : Nat → Nat → Prop) (x : Nat) : Prop :=
  ∀ P : Nat → Prop,
    ((y : Nat) → q → ((z : Nat) → r z y → P z) → p y → P y) → P x

theorem C3.mk {q : Prop} {p : Nat → Prop} {r : Nat → Nat → Prop} (x : Nat)
    (hq : q) (h : (y : Nat) → r y x → C3 q p r y) (hp : p x) : C3 q p r x :=
  fun P k => k x hq (fun z hz => h z hz P k) hp

theorem C3.ind {q : Prop} {p : Nat → Prop} {r : Nat → Nat → Prop}
    {motive : (x : Nat) → C3 q p r x → Prop}
    (step : (x : Nat) → (hq : q) → (h : (y : Nat) → r y x → C3 q p r y) →
      (hp : p x) → ((y : Nat) → (hy : r y x) → motive y (h y hy)) →
      motive x (C3.mk x hq h hp))
    {x : Nat} (t : C3 q p r x) : motive x t :=
  t (fun y => AndC (C3 q p r y) (∀ w : C3 q p r y, motive y w))
    (fun y hq g hp =>
      let h : (z : Nat) → r z y → C3 q p r z :=
        fun z hz => g z hz (C3 q p r z) (fun c _ => c)
      let ih : (z : Nat) → (hz : r z y) → motive z (h z hz) :=
        fun z hz => g z hz (motive z (h z hz)) (fun _ m => m (h z hz))
      fun D k => k (C3.mk y hq h hp) (fun _w => step y hq h hp ih))
    (motive x t) (fun _ m => m t)

section Rec3
variable {q : Prop} {p : Nat → Prop} {r : Nat → Nat → Prop}
  {motive : (x : Nat) → C3 q p r x → Sort v}
  (step : (x : Nat) → (hq : q) → (h : (y : Nat) → r y x → C3 q p r y) →
    (hp : p x) → ((y : Nat) → (hy : r y x) → motive y (h y hy)) →
    motive x (C3.mk x hq h hp))

def G3 (x : Nat) (t : C3 q p r x) (val : motive x t) : Prop :=
  ∀ Q : (y : Nat) → (w : C3 q p r y) → motive y w → Prop,
    ((y : Nat) → (hq : q) → (h : (z : Nat) → r z y → C3 q p r z) → (hp : p y) →
      (f : (z : Nat) → (hz : r z y) → motive z (h z hz)) →
      ((z : Nat) → (hz : r z y) → Q z (h z hz) (f z hz)) →
      Q y (C3.mk y hq h hp) (step y hq h hp f)) →
    Q x t val

theorem G3.mk (x : Nat) (hq : q) (h : (y : Nat) → r y x → C3 q p r y)
    (hp : p x) (f : (y : Nat) → (hy : r y x) → motive y (h y hy))
    (hf : (y : Nat) → (hy : r y x) → G3 step y (h y hy) (f y hy)) :
    G3 step x (C3.mk x hq h hp) (step x hq h hp f) :=
  fun Q k => k x hq h hp f (fun z hz => hf z hz Q k)

/-- All three fields other than the index are proofs, and all three are
    universally quantified: proof irrelevance recovers each, regardless of
    which side of the recursive field it sits on. -/
def G3Inv (x : Nat) (t : C3 q p r x) (val : motive x t) : Prop :=
  ∀ (hq : q) (h : (y : Nat) → r y x → C3 q p r y) (hp : p x) (D : Prop),
    ((f : (y : Nat) → (hy : r y x) → motive y (h y hy)) →
      ((y : Nat) → (hy : r y x) → G3 step y (h y hy) (f y hy)) →
      val = step x hq h hp f → D) → D

theorem G3.inv {x : Nat} {t : C3 q p r x} {val : motive x t}
    (g : G3 step x t val) : G3Inv step x t val :=
  g (fun z w u => AndC (G3 step z w u) (G3Inv step z w u))
    (fun y hq h hp f ih =>
      let hg : (z : Nat) → (hz : r z y) → G3 step z (h z hz) (f z hz) :=
        fun z hz => ih z hz (G3 step z (h z hz) (f z hz)) (fun b _ => b)
      fun D k => k (G3.mk step y hq h hp f hg)
        (fun _hq' _h' _hp' _D' k' => k' f hg rfl))
    (G3Inv step x t val) (fun _g i => i)

theorem G3.unique {x : Nat} (t : C3 q p r x) (v w : motive x t)
    (gv : G3 step x t v) (gw : G3 step x t w) : v = w :=
  C3.ind
    (motive := fun x t => ∀ v w : motive x t,
      G3 step x t v → G3 step x t w → v = w)
    (fun x hq h hp ih v w gv gw =>
      G3.inv step gv hq h hp (v = w) (fun f1 hf1 e1 =>
        G3.inv step gw hq h hp (v = w) (fun f2 hf2 e2 =>
          e1.trans (Eq.trans
            (congrArg (step x hq h hp)
              (funext fun y => funext fun hy =>
                ih y hy (f1 y hy) (f2 y hy) (hf1 y hy) (hf2 y hy)))
            e2.symm))))
    t v w gv gw

theorem G3.exists {x : Nat} (t : C3 q p r x) :
    Nonempty (PSigma fun val : motive x t => G3 step x t val) :=
  C3.ind
    (motive := fun x t =>
      Nonempty (PSigma fun val : motive x t => G3 step x t val))
    (fun x hq h hp ih =>
      Nonempty.intro
        ⟨step x hq h hp (fun y hy => (Classical.choice (ih y hy)).fst),
         G3.mk step x hq h hp (fun y hy => (Classical.choice (ih y hy)).fst)
           (fun y hy => (Classical.choice (ih y hy)).snd)⟩)
    t

noncomputable def C3.rec' {x : Nat} (t : C3 q p r x) : motive x t :=
  (Classical.choice (G3.exists step t)).fst

theorem C3.rec'_graph {x : Nat} (t : C3 q p r x) :
    G3 step x t (C3.rec' step t) :=
  (Classical.choice (G3.exists step t)).snd

theorem C3.iota (x : Nat) (hq : q) (h : (y : Nat) → r y x → C3 q p r y)
    (hp : p x) :
    C3.rec' step (C3.mk x hq h hp)
      = step x hq h hp (fun y hy => C3.rec' step (h y hy)) :=
  G3.unique step (C3.mk x hq h hp) _ _
    (C3.rec'_graph step (C3.mk x hq h hp))
    (G3.mk step x hq h hp (fun y hy => C3.rec' step (h y hy))
      (fun y hy => C3.rec'_graph step (h y hy)))

end Rec3

/-- `#check @I3.rec`, transcribed with `I3 := C3`. Note the argument order:
    the kernel puts ALL constructor fields first (`x`, `q`, the recursive one,
    `p x`) and the induction hypothesis last, so the transcription pins the
    recipe's handling of a field that follows the recursion. -/
noncomputable example : ∀ {q : Prop} {p : Nat → Prop} {r : Nat → Nat → Prop}
    {motive : (a : Nat) → C3 q p r a → Sort v},
    ((x : Nat) → (hq : q) → (h : ∀ (y : Nat), r y x → C3 q p r y) →
      (hp : p x) → ((y : Nat) → (hy : r y x) → motive y (h y hy)) →
      motive x (C3.mk x hq h hp)) →
    {a : Nat} → (t : C3 q p r a) → motive a t := @C3.rec'

/-- The same transcription, against Lean's own recursor. -/
noncomputable example : ∀ {q : Prop} {p : Nat → Prop} {r : Nat → Nat → Prop}
    {motive : (a : Nat) → I3 q p r a → Sort v},
    ((x : Nat) → (hq : q) → (h : ∀ (y : Nat), r y x → I3 q p r y) →
      (hp : p x) → ((y : Nat) → (hy : r y x) → motive y (h y hy)) →
      motive x (I3.mk x hq h hp)) →
    {a : Nat} → (t : I3 q p r a) → motive a t := @I3.rec

/-- info: 'C3.rec'' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms C3.rec'
/-- info: 'C3.iota' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms C3.iota
/-- info: 'C3.ind' does not depend on any axioms -/
#guard_msgs in #print axioms C3.ind
