/-
AccFromChoice.lean — `Acc` LEAVES the primitive basis: the subsingleton-
recursive large eliminator is derivable, over no inductive primitive at all
plus `Classical.choice` and `funext`.

`modelgen`'s basis holds `Acc` for exactly one reason: it is the only
subsingleton-recursive LARGE eliminator, and the kernel grants

  Acc.rec : {α : Sort u} → {r : α → α → Prop} →
    {motive : (a : α) → Acc r a → Sort v} →
    ((x : α) → (h : ∀ y, r y x → Acc r y) →
      ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (Acc.intro x h)) →
    {a : α} → (t : Acc r a) → motive a t

by the subsingleton rule — a grant to the DECLARATION that an emitted `def`
does not inherit. This file derives that exact type, for the carrier

  CAcc r x := ∀ P : α → Prop, (∀ y, (∀ z, r z y → P z) → P y) → P x

(the impredicative Church encoding: carrier, `intro` and the Prop-motive
recursor cost no primitive whatsoever, §0).

VERDICT: yes. `CAcc.rec'` (§2) has `Acc.rec`'s exact type (pinned §3), and ι
is a THEOREM (`CAcc.iota`) — propositional, not `rfl`, because the value is
extracted with `Classical.choice`.

  #print axioms CAcc.rec'  →  [Classical.choice]
  #print axioms CAcc.iota  →  [Classical.choice, Quot.sound]   (Quot.sound = funext)

`propext` is not needed, and note the split: TOTALITY costs only
`Classical.choice`, UNIQUENESS is what brings in `funext`, so only ι pays for
it. Beyond Π and Prop-impredicativity the construction consumes `Eq`,
`PSigma`, `Nonempty` — the last only as `Classical.choice`'s own domain; it is
Church-encodable in Prop and `NonemptyC.toNonempty` crosses the boundary — and
`Quot`, which is a kernel primitive rather than an inductive and enters only
inside core's proof of `funext`. No `Acc`, no `Nat`, no `PULiftP`; `Acc`
appears in this file only in the adequacy yardsticks (§1).

METHOD — define the function by its GRAPH, never by choosing a value:

  1. `Graph step x t val` (§2) is the impredicative least relation closed
     under "if the value at every r-predecessor y is `f y`, then the value at
     x is `step x h f`". It is a Prop: `∀ Q : (y : α) → (s : CAcc r y) →
     motive y s → Prop, closed Q → Q x t val`. The `CAcc`-proof argument `t`
     is a non-issue exactly as sketched — `CAcc r x` is a Prop, so `motive x t`
     and `motive x t'` are DEFINITIONALLY equal and every `t`/`h`/`s` in sight
     is interchangeable by proof irrelevance. That is what lets `GraphInv`
     universally quantify its `h` and close its `rfl`.
  2. Totality (`Graph.exists`) and single-valuedness (`Graph.unique`) are
     proved by the free Prop-motive recursor `CAcc.ind`. Totality picks the
     predecessors' values with `Classical.choice` inside the induction — safe,
     because uniqueness makes it irrelevant WHICH witness was picked.
  3. `CAcc.rec' step t := (Classical.choice (Graph.exists step t)).fst` — the
     `Nonempty (Σ' val, Graph step x t val)` packaging, which is what keeps
     the extracted value tied to the graph.
  4. ι is then a theorem: both sides satisfy `Graph step x (intro x h) ·`
     (LHS by `choice_spec`, RHS by the graph's own closure rule) and `Graph`
     is single-valued.

§4 REFUTES the naive route by compiling it: `Classical.choice` on
`Nonempty (motive x t)` produces a value that is provably INDEPENDENT of the
step function (`naive_value_indep`, by `rfl`, since the two `Nonempty` proofs
are defeq), so its ι rule is not merely unproved but inconsistent
(`naive_iota_false`). §5 shows the graph recursor is not degenerate in the
same spot: two different steps give two different, step-determined values.

§6 GENERALITY. The construction is uniform in `α`'s universe `u` (including
`u = 0`, i.e. `α : Prop`), in the motive's universe `v` (including `v = 0`,
i.e. a Prop motive), and in `r` — all three pinned as `example`s in §3, by
universe instantiation of the single polymorphic `CAcc.rec'`. §6 repeats the
whole derivation for the indexed shape with an extra Prop argument

  inductive DD (A : ι → Prop) (R : (x : ι) → A x → ι → Prop) : ι → Prop
    | mk : (x : ι) → (a : A x) → ((y : ι) → R x a y → DD A R y) → DD A R x

(the AccPhi/`accφ` shape, whose kernel-granted large recursor is pinned
against `@DD.rec`), showing the recipe is uniform in the constructor's PROOF
arguments too. What it is NOT uniform in: constructor arguments that are DATA
occurring inside the conclusion's index expression. Inversion recovers proof
arguments for free (proof irrelevance) and index arguments only when the index
determines them; where it does not, inversion needs the index's injectivity,
and in the limiting case (`Eq`, whose entire content is such an argument) the
Church encoding is Leibniz equality and this route does not reach J. That case
is not in this class anyway — it is non-recursive, and BareU.lean models it
from `PULiftP`.

TACTICS: none, anywhere in the file — not in the constructions, not in the
probes, not in the refutation. Every proof is a raw term (`fun`, `Eq.trans`,
`Eq.symm`, `congrArg`, `funext`, `rfl`), so the generator can emit all of it.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean AccFromChoice.lean
Expected: 0 errors.
-/
universe u v
set_option linter.unusedVariables false

-- ═════════════════════════════════════════════════════════════════════════
-- §0. The carrier: the impredicative Church encoding. No primitive at all.
-- ═════════════════════════════════════════════════════════════════════════

/-- Church conjunction, so the folds below need no `And`. -/
def AndC (A B : Prop) : Prop := ∀ D : Prop, (A → B → D) → D

/-- `Nonempty` is not an extra basis commitment either: the Church version is
    a Prop and crosses to the axiom's own inductive in one step. Below, core
    `Nonempty` is used directly, since it is `Classical.choice`'s own domain. -/
def NonemptyC (α : Sort u) : Prop := ∀ C : Prop, (α → C) → C

theorem NonemptyC.toNonempty {α : Sort u} (k : NonemptyC α) : Nonempty α :=
  k (Nonempty α) Nonempty.intro

def CAcc {α : Sort u} (r : α → α → Prop) (x : α) : Prop :=
  ∀ P : α → Prop, (∀ y, (∀ z, r z y → P z) → P y) → P x

theorem CAcc.intro {α : Sort u} {r : α → α → Prop} (x : α)
    (h : ∀ y, r y x → CAcc r y) : CAcc r x :=
  fun P s => s x (fun z hz => h z hz P s)

/-- The dependent Prop-motive recursor, free: fold at the Church conjunction
    of "is accessible" and "the motive holds at every proof". The second
    component is stated `∀ s, motive y s` because the fold has no proof to
    hand; supplying `CAcc.intro y h` for it is free by proof irrelevance. -/
theorem CAcc.ind {α : Sort u} {r : α → α → Prop}
    {motive : (a : α) → CAcc r a → Prop}
    (step : (x : α) → (h : ∀ y, r y x → CAcc r y) →
      ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (CAcc.intro x h))
    {a : α} (t : CAcc r a) : motive a t :=
  t (fun y => AndC (CAcc r y) (∀ s : CAcc r y, motive y s))
    (fun y g =>
      let h : ∀ z, r z y → CAcc r z :=
        fun z hz => g z hz (CAcc r z) (fun c _ => c)
      let ih : ∀ z (hz : r z y), motive z (h z hz) :=
        fun z hz => g z hz (motive z (h z hz)) (fun _ m => m (h z hz))
      fun D k => k (CAcc.intro y h) (fun _s => step y h ih))
    (motive a t) (fun _ m => m t)

-- ═════════════════════════════════════════════════════════════════════════
-- §1. Adequacy: the model is core's `Acc`, both ways.
--     (Yardstick only — `Acc` is used nowhere else in this file.)
-- ═════════════════════════════════════════════════════════════════════════

theorem CAcc.toAcc {α : Sort u} {r : α → α → Prop} {x : α}
    (t : CAcc r x) : Acc r x :=
  t (Acc r) (fun y ih => Acc.intro y ih)

theorem CAcc.ofAcc {α : Sort u} {r : α → α → Prop} {x : α}
    (t : Acc r x) : CAcc r x :=
  Acc.rec (motive := fun a _ => CAcc r a) (fun y _h ih => CAcc.intro y ih) t

-- ═════════════════════════════════════════════════════════════════════════
-- §2. The large recursor, by the graph of the recursion.
-- ═════════════════════════════════════════════════════════════════════════

section Rec
variable {α : Sort u} {r : α → α → Prop} {motive : (a : α) → CAcc r a → Sort v}
  (step : (x : α) → (h : ∀ y, r y x → CAcc r y) →
    ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (CAcc.intro x h))

/-- "`val` is what the recursion produces at `x`": the least relation closed
    under the step rule, encoded impredicatively. `Q` ranges over a
    `Sort (max u v 1)`; the body lands in `Prop`, so `Graph` is a Prop. -/
def Graph (x : α) (t : CAcc r x) (val : motive x t) : Prop :=
  ∀ Q : (y : α) → (s : CAcc r y) → motive y s → Prop,
    ((y : α) → (h : ∀ z, r z y → CAcc r z) →
      (f : (z : α) → (hz : r z y) → motive z (h z hz)) →
      ((z : α) → (hz : r z y) → Q z (h z hz) (f z hz)) →
      Q y (CAcc.intro y h) (step y h f)) →
    Q x t val

/-- The graph is itself closed under the step rule (it is a fixed point, not
    merely a pre-fixed point). This is the direction that makes ι's RHS a
    graph point. -/
theorem Graph.mk (x : α) (h : ∀ y, r y x → CAcc r y)
    (f : (y : α) → (hy : r y x) → motive y (h y hy))
    (hf : (y : α) → (hy : r y x) → Graph step y (h y hy) (f y hy)) :
    Graph step x (CAcc.intro x h) (step x h f) :=
  fun Q q => q x h f (fun z hz => hf z hz Q q)

/-- Inversion, Church-encoded. `h` is universally quantified rather than
    existentially: any two inhabitants of `∀ y, r y x → CAcc r y` are
    definitionally equal (it is a Prop), so proving it for the one the
    constructor used gives it for the caller's. -/
def GraphInv (x : α) (t : CAcc r x) (val : motive x t) : Prop :=
  ∀ (h : ∀ y, r y x → CAcc r y) (D : Prop),
    ((f : (y : α) → (hy : r y x) → motive y (h y hy)) →
      ((y : α) → (hy : r y x) → Graph step y (h y hy) (f y hy)) →
      val = step x h f → D) → D

/-- Inversion holds, by folding the graph at `Graph ∧ GraphInv` (the graph
    alone is not closed enough to rebuild the sub-values' graph facts). The
    final `rfl` is where proof irrelevance does the work: `step x h f` and
    `step x h' f` are the same term. -/
theorem Graph.inv {x : α} {t : CAcc r x} {val : motive x t}
    (g : Graph step x t val) : GraphInv step x t val :=
  g (fun z s w => AndC (Graph step z s w) (GraphInv step z s w))
    (fun y h f ih =>
      let hg : (z : α) → (hz : r z y) → Graph step z (h z hz) (f z hz) :=
        fun z hz => ih z hz (Graph step z (h z hz) (f z hz)) (fun a _ => a)
      fun D k => k (Graph.mk step y h f hg)
        (fun _h' _D' k' => k' f hg rfl))
    (GraphInv step x t val) (fun _g i => i)

/-- Single-valuedness, by induction at a Prop motive. `funext` enters here
    (and only here): the two inverted argument-functions agree pointwise. -/
theorem Graph.unique {x : α} (t : CAcc r x) (v w : motive x t)
    (gv : Graph step x t v) (gw : Graph step x t w) : v = w :=
  CAcc.ind
    (motive := fun x t => ∀ v w : motive x t,
      Graph step x t v → Graph step x t w → v = w)
    (fun x h ih v w gv gw =>
      Graph.inv step gv h (v = w) (fun f1 hf1 e1 =>
        Graph.inv step gw h (v = w) (fun f2 hf2 e2 =>
          e1.trans (Eq.trans
            (congrArg (step x h)
              (funext fun y => funext fun hy =>
                ih y hy (f1 y hy) (f2 y hy) (hf1 y hy) (hf2 y hy)))
            e2.symm))))
    t v w gv gw

/-- Totality, again by induction at a Prop motive. `Classical.choice` picks
    the predecessors' values here; uniqueness above is what makes the choice
    harmless. -/
theorem Graph.exists {x : α} (t : CAcc r x) :
    Nonempty (PSigma fun val : motive x t => Graph step x t val) :=
  CAcc.ind
    (motive := fun x t =>
      Nonempty (PSigma fun val : motive x t => Graph step x t val))
    (fun x h ih =>
      Nonempty.intro
        ⟨step x h (fun y hy => (Classical.choice (ih y hy)).fst),
         Graph.mk step x h (fun y hy => (Classical.choice (ih y hy)).fst)
           (fun y hy => (Classical.choice (ih y hy)).snd)⟩)
    t

/-- THE LARGE RECURSOR. The value is extracted from a `Nonempty` of the
    SIGMA of value-and-graph-proof, never from `Nonempty (motive x t)`; that
    is the whole difference from the failed route in §4. -/
noncomputable def CAcc.rec' {a : α} (t : CAcc r a) : motive a t :=
  (Classical.choice (Graph.exists step t)).fst

theorem CAcc.rec'_graph {a : α} (t : CAcc r a) :
    Graph step a t (CAcc.rec' step t) :=
  (Classical.choice (Graph.exists step t)).snd

/-- THE ι RULE, as a theorem. It is propositional, not `rfl`: the left side
    is a `Classical.choice` application, which reduces to nothing. Both sides
    are graph points at `CAcc.intro x h`, and the graph is single-valued. -/
theorem CAcc.iota (x : α) (h : ∀ y, r y x → CAcc r y) :
    CAcc.rec' step (CAcc.intro x h)
      = step x h (fun y hy => CAcc.rec' step (h y hy)) :=
  Graph.unique step (CAcc.intro x h) _ _
    (CAcc.rec'_graph step (CAcc.intro x h))
    (Graph.mk step x h (fun y hy => CAcc.rec' step (h y hy))
      (fun y hy => CAcc.rec'_graph step (h y hy)))

-- ... and it is NOT definitional. Pinned: the same statement by `Eq.refl`
-- is a type mismatch. Every consumer of an emitted `Acc` must therefore
-- rewrite with `CAcc.iota` where the kernel would have reduced.
/--
error: Type mismatch
  Eq.refl (CAcc.rec' step (CAcc.intro x h))
has type
  CAcc.rec' step ⋯ = CAcc.rec' step ⋯
but is expected to have type
  CAcc.rec' step ⋯ = step x h fun y hy => CAcc.rec' step ⋯
-/
#guard_msgs (error) in
example (x : α) (h : ∀ y, r y x → CAcc r y) :
    CAcc.rec' step (CAcc.intro x h)
      = step x h (fun y hy => CAcc.rec' step (h y hy)) :=
  Eq.refl (CAcc.rec' step (CAcc.intro x h))

end Rec

-- ═════════════════════════════════════════════════════════════════════════
-- §3. The shape, pinned against `Acc.rec`; and the axiom audit.
-- ═════════════════════════════════════════════════════════════════════════

/-- `Acc.rec`'s type, transcribed from `#check @Acc.rec` with `Acc := CAcc`. -/
noncomputable example : ∀ {α : Sort u} {r : α → α → Prop}
    {motive : (a : α) → CAcc r a → Sort v},
    ((x : α) → (h : ∀ (y : α), r y x → CAcc r y) →
      ((y : α) → (a : r y x) → motive y (h y a)) → motive x (CAcc.intro x h)) →
    {a : α} → (t : CAcc r a) → motive a t := @CAcc.rec'

/-- `v := 0`: nothing breaks when the motive lands in `Prop` — the graph is
    then redundant (`CAcc.ind` already gives that recursor, axiom-free), but
    the polymorphic construction still instantiates, and `Graph.unique` is
    discharged by proof irrelevance. `CAcc.rec'` needs no `v ≥ 1` side
    condition, so `modelgen` may emit one universe-polymorphic definition. -/
noncomputable example : ∀ {α : Sort u} {r : α → α → Prop}
    {motive : (a : α) → CAcc r a → Prop},
    ((x : α) → (h : ∀ (y : α), r y x → CAcc r y) →
      ((y : α) → (a : r y x) → motive y (h y a)) → motive x (CAcc.intro x h)) →
    {a : α} → (t : CAcc r a) → motive a t := @CAcc.rec'.{u, 0}

/-- `u := 0`: nothing breaks when `α : Prop` either. -/
noncomputable example : ∀ {α : Prop} {r : α → α → Prop}
    {motive : (a : α) → CAcc r a → Sort v},
    ((x : α) → (h : ∀ (y : α), r y x → CAcc r y) →
      ((y : α) → (a : r y x) → motive y (h y a)) → motive x (CAcc.intro x h)) →
    {a : α} → (t : CAcc r a) → motive a t := @CAcc.rec'.{0, v}

/-- both at once. -/
noncomputable example : ∀ {α : Prop} {r : α → α → Prop}
    {motive : (a : α) → CAcc r a → Prop},
    ((x : α) → (h : ∀ (y : α), r y x → CAcc r y) →
      ((y : α) → (a : r y x) → motive y (h y a)) → motive x (CAcc.intro x h)) →
    {a : α} → (t : CAcc r a) → motive a t := @CAcc.rec'.{0, 0}

/-- info: 'CAcc.rec'' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms CAcc.rec'
/-- info: 'CAcc.iota' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CAcc.iota
/-- info: 'CAcc.ind' does not depend on any axioms -/
#guard_msgs in #print axioms CAcc.ind
/-- info: 'CAcc.toAcc' does not depend on any axioms -/
#guard_msgs in #print axioms CAcc.toAcc
/-- info: 'CAcc.ofAcc' does not depend on any axioms -/
#guard_msgs in #print axioms CAcc.ofAcc

-- ═════════════════════════════════════════════════════════════════════════
-- §4. Refutation of the naive route: `Classical.choice (Nonempty (motive x))`
--     yields a recursor whose ι rule is INCONSISTENT, not merely unprovable.
-- ═════════════════════════════════════════════════════════════════════════

/-- The naive recursor. It typechecks; it is even total and universe-correct.
    But the `Nonempty (motive a t)` it eliminates is a PROOF, so by proof
    irrelevance the `Classical.choice` application cannot see `step`. -/
noncomputable def naiveRec {α : Sort u} {r : α → α → Prop}
    {motive : (a : α) → CAcc r a → Sort v}
    (step : (x : α) → (h : ∀ y, r y x → CAcc r y) →
      ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (CAcc.intro x h))
    {a : α} (t : CAcc r a) : motive a t :=
  Classical.choice
    (CAcc.ind (motive := fun a t => Nonempty (motive a t))
      (fun x h ih =>
        Nonempty.intro (step x h (fun y hy => Classical.choice (ih y hy)))) t)

section NaiveFails

/-- The empty relation on `Nat`; every point is accessible, vacuously. -/
def noR : Nat → Nat → Prop := fun _ _ => False
def noR.acc (x : Nat) : ∀ y, noR y x → CAcc noR y := fun y hy => False.elim hy

/-- The naive recursor's value does not depend on the step function AT ALL —
    the two proofs of `Nonempty Bool` are definitionally equal, so this is
    `rfl`. Any ι rule for it therefore equates `true` with `false`. -/
theorem naive_value_indep (x : Nat) (t : CAcc noR x) :
    naiveRec (motive := fun _ _ => Bool) (fun _ _ _ => true) t
      = naiveRec (motive := fun _ _ => Bool) (fun _ _ _ => false) t := rfl

/-- So the naive route's ι rule proves `False`. (Stated monomorphically at
    `Nat`/`Bool`, which only strengthens the refutation.) -/
theorem naive_iota_false
    (iota : (st : (x : Nat) → (h : ∀ y, noR y x → CAcc noR y) →
              ((y : Nat) → noR y x → Bool) → Bool) →
            (x : Nat) → (h : ∀ y, noR y x → CAcc noR y) →
            naiveRec (motive := fun _ _ => Bool) st (CAcc.intro x h)
              = st x h (fun y hy =>
                  naiveRec (motive := fun _ _ => Bool) st (h y hy))) : False :=
  Bool.noConfusion
    (((iota (fun _ _ _ => true) 0 (noR.acc 0)).symm.trans
        (naive_value_indep 0 (CAcc.intro 0 (noR.acc 0)))).trans
      (iota (fun _ _ _ => false) 0 (noR.acc 0)))

end NaiveFails

-- ═════════════════════════════════════════════════════════════════════════
-- §5. ... and the graph recursor is not degenerate in that same spot.
-- ═════════════════════════════════════════════════════════════════════════

/-- Two different steps, two different step-determined values, on the very
    instance where the naive recursor was provably step-blind. Each is ι
    applied once; proof irrelevance transports it from `CAcc.intro x h` to an
    arbitrary `t`. -/
theorem probe_true (x : Nat) (t : CAcc noR x) :
    CAcc.rec' (motive := fun _ _ => Bool) (fun _ _ _ => true) t = true :=
  CAcc.iota (motive := fun _ _ => Bool) (fun _ _ _ => true) x (noR.acc x)

theorem probe_false (x : Nat) (t : CAcc noR x) :
    CAcc.rec' (motive := fun _ _ => Bool) (fun _ _ _ => false) t = false :=
  CAcc.iota (motive := fun _ _ => Bool) (fun _ _ _ => false) x (noR.acc x)

/-- A `Type`-valued motive whose value is the index: the recursor really
    returns `step`'s answer. -/
theorem probe_index (x : Nat) (t : CAcc noR x) :
    CAcc.rec' (motive := fun _ _ => Nat) (fun z _ _ => z) t = x :=
  CAcc.iota (motive := fun _ _ => Nat) (fun z _ _ => z) x (noR.acc x)

-- ═════════════════════════════════════════════════════════════════════════
-- §6. Generality: the same recipe for the indexed shape with an extra PROOF
--     argument (the `accφ`/AccPhi shape). Uniform in the proof arguments.
-- ═════════════════════════════════════════════════════════════════════════

/-- The generic subsingleton-recursive declaration: one constructor, whose
    arguments are the index `x`, a proof `a : A x`, and a recursive argument
    under a binder. The kernel grants it large elimination — pinned below. -/
inductive DD {ι : Sort u} (A : ι → Prop) (R : (x : ι) → A x → ι → Prop) :
    ι → Prop
  | mk : (x : ι) → (a : A x) → ((y : ι) → R x a y → DD A R y) → DD A R x

def CD {ι : Sort u} (A : ι → Prop) (R : (x : ι) → A x → ι → Prop) (x : ι) :
    Prop :=
  ∀ P : ι → Prop, ((y : ι) → (a : A y) → ((z : ι) → R y a z → P z) → P y) → P x

theorem CD.mk {ι : Sort u} {A : ι → Prop} {R : (x : ι) → A x → ι → Prop}
    (x : ι) (a : A x) (h : (y : ι) → R x a y → CD A R y) : CD A R x :=
  fun P s => s x a (fun z hz => h z hz P s)

theorem CD.ind {ι : Sort u} {A : ι → Prop} {R : (x : ι) → A x → ι → Prop}
    {motive : (x : ι) → CD A R x → Prop}
    (step : (x : ι) → (a : A x) → (h : (y : ι) → R x a y → CD A R y) →
      ((y : ι) → (hy : R x a y) → motive y (h y hy)) → motive x (CD.mk x a h))
    {x : ι} (t : CD A R x) : motive x t :=
  t (fun y => AndC (CD A R y) (∀ s : CD A R y, motive y s))
    (fun y a g =>
      let h : (z : ι) → R y a z → CD A R z :=
        fun z hz => g z hz (CD A R z) (fun c _ => c)
      let ih : (z : ι) → (hz : R y a z) → motive z (h z hz) :=
        fun z hz => g z hz (motive z (h z hz)) (fun _ m => m (h z hz))
      fun D k => k (CD.mk y a h) (fun _s => step y a h ih))
    (motive x t) (fun _ m => m t)

section GenericRec
variable {ι : Sort u} {A : ι → Prop} {R : (x : ι) → A x → ι → Prop}
  {motive : (x : ι) → CD A R x → Sort v}
  (step : (x : ι) → (a : A x) → (h : (y : ι) → R x a y → CD A R y) →
    ((y : ι) → (hy : R x a y) → motive y (h y hy)) → motive x (CD.mk x a h))

def DGraph (x : ι) (t : CD A R x) (val : motive x t) : Prop :=
  ∀ Q : (y : ι) → (s : CD A R y) → motive y s → Prop,
    ((y : ι) → (a : A y) → (h : (z : ι) → R y a z → CD A R z) →
      (f : (z : ι) → (hz : R y a z) → motive z (h z hz)) →
      ((z : ι) → (hz : R y a z) → Q z (h z hz) (f z hz)) →
      Q y (CD.mk y a h) (step y a h f)) →
    Q x t val

theorem DGraph.mk (x : ι) (a : A x) (h : (y : ι) → R x a y → CD A R y)
    (f : (y : ι) → (hy : R x a y) → motive y (h y hy))
    (hf : (y : ι) → (hy : R x a y) → DGraph step y (h y hy) (f y hy)) :
    DGraph step x (CD.mk x a h) (step x a h f) :=
  fun Q q => q x a h f (fun z hz => hf z hz Q q)

/-- Both `a` and `h` are universally quantified: both are proofs, so both are
    recovered by proof irrelevance. This is the clause that generalises. -/
def DGraphInv (x : ι) (t : CD A R x) (val : motive x t) : Prop :=
  ∀ (a : A x) (h : (y : ι) → R x a y → CD A R y) (D : Prop),
    ((f : (y : ι) → (hy : R x a y) → motive y (h y hy)) →
      ((y : ι) → (hy : R x a y) → DGraph step y (h y hy) (f y hy)) →
      val = step x a h f → D) → D

theorem DGraph.inv {x : ι} {t : CD A R x} {val : motive x t}
    (g : DGraph step x t val) : DGraphInv step x t val :=
  g (fun z s w => AndC (DGraph step z s w) (DGraphInv step z s w))
    (fun y a h f ih =>
      let hg : (z : ι) → (hz : R y a z) → DGraph step z (h z hz) (f z hz) :=
        fun z hz => ih z hz (DGraph step z (h z hz) (f z hz)) (fun b _ => b)
      fun D k => k (DGraph.mk step y a h f hg)
        (fun _a' _h' _D' k' => k' f hg rfl))
    (DGraphInv step x t val) (fun _g i => i)

theorem DGraph.unique {x : ι} (t : CD A R x) (v w : motive x t)
    (gv : DGraph step x t v) (gw : DGraph step x t w) : v = w :=
  CD.ind
    (motive := fun x t => ∀ v w : motive x t,
      DGraph step x t v → DGraph step x t w → v = w)
    (fun x a h ih v w gv gw =>
      DGraph.inv step gv a h (v = w) (fun f1 hf1 e1 =>
        DGraph.inv step gw a h (v = w) (fun f2 hf2 e2 =>
          e1.trans (Eq.trans
            (congrArg (step x a h)
              (funext fun y => funext fun hy =>
                ih y hy (f1 y hy) (f2 y hy) (hf1 y hy) (hf2 y hy)))
            e2.symm))))
    t v w gv gw

theorem DGraph.exists {x : ι} (t : CD A R x) :
    Nonempty (PSigma fun val : motive x t => DGraph step x t val) :=
  CD.ind
    (motive := fun x t =>
      Nonempty (PSigma fun val : motive x t => DGraph step x t val))
    (fun x a h ih =>
      Nonempty.intro
        ⟨step x a h (fun y hy => (Classical.choice (ih y hy)).fst),
         DGraph.mk step x a h (fun y hy => (Classical.choice (ih y hy)).fst)
           (fun y hy => (Classical.choice (ih y hy)).snd)⟩)
    t

noncomputable def CD.rec' {x : ι} (t : CD A R x) : motive x t :=
  (Classical.choice (DGraph.exists step t)).fst

theorem CD.rec'_graph {x : ι} (t : CD A R x) :
    DGraph step x t (CD.rec' step t) :=
  (Classical.choice (DGraph.exists step t)).snd

theorem CD.iota (x : ι) (a : A x) (h : (y : ι) → R x a y → CD A R y) :
    CD.rec' step (CD.mk x a h)
      = step x a h (fun y hy => CD.rec' step (h y hy)) :=
  DGraph.unique step (CD.mk x a h) _ _
    (CD.rec'_graph step (CD.mk x a h))
    (DGraph.mk step x a h (fun y hy => CD.rec' step (h y hy))
      (fun y hy => CD.rec'_graph step (h y hy)))

end GenericRec

/-- The kernel's own grant for the generic shape, transcribed with
    `DD := CD`; `@DD.rec` below witnesses that the grant is a LARGE one. -/
noncomputable example : ∀ {ι : Sort u} {A : ι → Prop}
    {R : (x : ι) → A x → ι → Prop} {motive : (x : ι) → CD A R x → Sort v},
    ((x : ι) → (a : A x) → (h : (y : ι) → R x a y → CD A R y) →
      ((y : ι) → (hy : R x a y) → motive y (h y hy)) → motive x (CD.mk x a h)) →
    {x : ι} → (t : CD A R x) → motive x t := @CD.rec'

noncomputable example : ∀ {ι : Sort u} {A : ι → Prop}
    {R : (x : ι) → A x → ι → Prop}
    {motive : (x : ι) → DD A R x → Sort v},
    ((x : ι) → (a : A x) → (h : (y : ι) → R x a y → DD A R y) →
      ((y : ι) → (hy : R x a y) → motive y (h y hy)) → motive x (DD.mk x a h)) →
    {x : ι} → (t : DD A R x) → motive x t := @DD.rec

/-- info: 'CD.rec'' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms CD.rec'
/-- info: 'CD.iota' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CD.iota
