import Lean

/-
WFromPaths.lean -- a generic W-type model over ordinary Lean types, and three branching
declarations derived from it.  Feasibility prototype for a code generator.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean WFromPaths.lean
Expected: 0 errors, 0 warnings, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
VERDICT
════════════════════════════════════════════════════════════════════════════
Feasible, and the generic part is genuinely generic.  ONE construction
(`WCon`, ~130 lines) is parameterised by `A : Type u` and `B : A → Type u`;
each target declaration is then ~15 lines of glue that (i) picks `A` and `B`
and (ii) curries the W constructor/recursor into the declaration's own arity.
The glue is the only per-declaration work, it is small, and it is schematic
over the constructor telescope -- see MECHANISATION below for the one place
where it is NOT.

════════════════════════════════════════════════════════════════════════════
WHAT COMPILED
════════════════════════════════════════════════════════════════════════════
Generic:  `WCon.W A B`, `WCon.sup`, `WCon.Wind` (small motive),
          `WCon.Sub` + `WCon.sub_wf`, `WCon.Wrec` (motive into `Sort v`),
          `WCon.Wrec_iota`.
Target 1  `BT` (finite branching, two recursive fields, two constructors):
          `CBT`, `CBT.leaf`, `CBT.node`, `CBT.rec'`, `CBT.iota_leaf`,
          `CBT.iota_node`.
Target 2  `IT` (infinite branching, recursive field under a binder):
          `CIT`, `CIT.sup`, `CIT.rec'`, `CIT.iota`.
Target 3  `DT | mk : (n : Nat) → (Fin n → DT) → DT`  (extra, unrequested):
          a non-recursive field that the recursive field's binder type
          DEPENDS on.  `CDT.rec' = Wrec` and `CDT.iota = Wrec_iota`, verbatim.
Pins:     for each target, the derived recursor AND Lean's own recursor are
          both checked against one transcription (6 `example`s).
Non-degeneracy: `CBT.leaf_ne_node` is proved from `CBT.rec'` + its two iotas
          alone, so the recursor is not blind to its step function; plus one
          worked evaluation exercising both iotas.

Iota is propositional (a theorem), not `rfl`, as expected -- `Wrec` goes
through `WellFounded.fix`, whose reduction is blocked on an `Acc` proof.

════════════════════════════════════════════════════════════════════════════
AXIOM TABLE  (pinned below with `#guard_msgs`)
════════════════════════════════════════════════════════════════════════════
  CBT.rec'       propext, Classical.choice, Quot.sound
  CBT.iota_leaf  propext, Classical.choice, Quot.sound
  CBT.iota_node  propext, Classical.choice, Quot.sound
  CIT.rec'       propext, Classical.choice, Quot.sound
  CIT.iota       propext, Classical.choice, Quot.sound
  CDT.rec'       propext, Classical.choice, Quot.sound
  CDT.iota       propext, Classical.choice, Quot.sound

Where each comes from:
  Classical.choice / propext -- `WCon.mk` must decide `x.1 = a` (does this
      path step leave by the node's own label?) for an ARBITRARY `A`.  That
      is `Classical.propDecidable`, hence choice, hence (via `Classical.em`)
      propext.  Nothing else in the construction is classical.
  Quot.sound -- `funext`, used to compare raw trees.
Not removable in general: deciding `x.1 = a` for arbitrary `A` is exactly
excluded middle.  It IS removable when `B` factors through a decidable tag
(see MECHANISATION #5).

════════════════════════════════════════════════════════════════════════════
REACHABLE INDUCTIVES  (closure over types AND values; computed below)
════════════════════════════════════════════════════════════════════════════
All 7 roots (22):
  Acc, And, Bool, Decidable, Empty, Eq, Exists, False, Fin, HEq, Iff, List,
  Nat, Nonempty, Option, Or, PProd, PUnit, Sigma, Subtype, True, WellFounded
Generic core only (`W`, `sup`, `Wrec`, `Wrec_iota`) (20): the same list minus
  `Empty` and `Fin`, which enter only through the `BT` and `DT` glue.
`BT`, `IT`, `DT` themselves are NOT reachable (asserted, not just reported):
the yardsticks are used only in the pins.

For the generator's dependency order, the core is:
  load-bearing carriers   Eq, List, Option, Sigma, Subtype, Nat, Bool
  well-foundedness        Acc, WellFounded
  proof plumbing          And, Or, Iff, Exists, True, False, HEq, PProd, PUnit
  classical dispatch      Decidable, Nonempty
`Acc`/`WellFounded` are the interesting entries: the W model needs a PRIOR
model of accessibility.  `Decidable`+`Nonempty` are there only because of the
label-equality test.

════════════════════════════════════════════════════════════════════════════
DEVIATIONS FROM THE BRIEF
════════════════════════════════════════════════════════════════════════════
1. `Good`'s one-step operator carries a THIRD clause beyond the obvious two:
      ∀ x, x.1 ≠ a → subt t x = nowhere
   (subtrees hanging off a label other than the node's own are empty).
   Without it a good tree is NOT determined by its root and its children:
   `canon : w = sup (root w) (kids w)` fails, `sup` is not surjective onto the
   carrier, and the recursor cannot be built at all.  This is the single
   non-obvious ingredient in the whole model.
2. `WellFounded.fix` / `WellFounded.fix_eq` rather than raw `Acc.rec` +
   `Acc.fix_eq`.  Costs one extra name (`WellFounded`) in the dependency list;
   using `Acc.rec` directly would remove it at the price of re-proving the
   fixpoint equation by hand.
3. Transports are written as `cast (congrArg C h)`, not `h ▸ _`.  `▸`
   elaborates to a motive that does not reduce at `rfl`, which breaks the iota
   proofs; `cast (congrArg C rfl) x` is definitionally `x`, which is what makes
   `Wrec_iota` fall out of `Wrec_key` at `h := rfl`.
4. Target 3 (`DT`) is extra, added because it is the case I expected to resist
   mechanisation.

════════════════════════════════════════════════════════════════════════════
MECHANISATION -- what schematises and what does not
════════════════════════════════════════════════════════════════════════════
Reduces to filling in `A` and `B`, mechanically, from the declaration:
  * arbitrary number of constructors -- `A := Σ (tag) (that tag's
    non-recursive telescope)`, `B` by case on the tag.  Here two constructors
    made `A := Bool`; k constructors make `A := Σ' t : Fin k, Args t`.
  * arbitrary non-recursive fields, INCLUDING dependent ones, and including
    ones the recursive field's binder type depends on -- target 3 shows this
    is free: it is exactly what the `B : A → Type` dependency is for.
  * recursive fields with and without binders -- a field `(x : σ) → T` and a
    field `T` are both just summands of `B`; the second contributes `PUnit`.
  * parameters -- section variables in front of everything; no new content.

Resists being written as a schema:
  A. THE CURRYING GLUE, and it is the real cost.  W gives
     `(f : B a → W) → ...`; Lean's recursor wants the fields UNCURRIED
     (`motive a → motive b → motive (node a b)`).  Converting needs, per
     constructor, (i) a chosen iso `B a ≅ Fin (arity)` and (ii) an ETA lemma
     `f = fun i => <case-split> i` proved by case analysis on that index type
     -- see the `Bool.rec ... rfl rfl` inside `CBT.rec'`.  This is generatable
     (the index type is a generated finite enumeration, so the eta lemma is a
     generated `rfl`-per-constructor), but it is real code per constructor,
     not a uniform term, and it is where a generator will first break.
  B. INDICES.  Nothing here handles them.  `W A B` models a single
     non-indexed type; an indexed family needs `A`, `B` and the whole
     `Good`/`canon` development re-run index-aware (roughly: trees labelled by
     index, `Good` carrying the index constraint), or an encoding of the
     family as one type plus an index projection with an equality constraint
     in each constructor.  I did not attempt it and I would not assume the
     above generalises without doing it.
  C. MUTUAL AND NESTED declarations: not addressed; both need a prior
     reduction (mutual → indexed, nested → mutual) which lands you in B.
  D. UNIVERSES.  `A B : Type u` with `W A B : Type u` is fine, but a
     declaration in `Prop`, or one whose recursor is only small-eliminating,
     is a different construction; and `Sort`-polymorphic targets would need
     `A B : Sort u`, which `List`-of-`Sigma` paths do not directly support.
  E. The classical dispatch (axiom table above) is unavoidable for arbitrary
     `A`, but a generator CAN avoid it whenever `B` factors through the
     constructor tag: then the label test is `Fin k` equality, decidable
     without choice, and the model becomes axiom-lighter.  Worth a special
     case, since it covers every declaration whose recursive-field binder
     types do not mention its non-recursive fields -- i.e. almost all of them.
-/

universe u v

namespace WCon

variable {A : Type u} {B : A → Type u}

/-- One step of a path: which constructor-label, and which of its branches. -/
abbrev Edge (A : Type u) (B : A → Type u) : Type u := Σ a : A, B a

/-- A raw tree: a partial labelling of paths. -/
abbrev PTree (A : Type u) (B : A → Type u) : Type u := List (Edge A B) → Option A

def subt (t : PTree A B) (x : Edge A B) : PTree A B := fun p => t (x :: p)

def nowhere : PTree A B := fun _ => none

/-- One-step unfolding whose least fixpoint is "is a well-founded tree". -/
def Step (S : PTree A B → Prop) (t : PTree A B) : Prop :=
  ∃ a : A, t [] = some a ∧ (∀ b : B a, S (subt t ⟨a, b⟩)) ∧
    ∀ x : Edge A B, x.1 ≠ a → subt t x = nowhere

theorem Step.mono {S S' : PTree A B → Prop} (hss : ∀ u, S u → S' u) {t : PTree A B}
    (h : Step S t) : Step S' t := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, fun b => hss _ (h2 b), h3⟩

/-- Knaster-Tarski least fixpoint, impredicatively. -/
def Good (t : PTree A B) : Prop := ∀ S : PTree A B → Prop, (∀ u, Step S u → S u) → S t

theorem Good.pre {t : PTree A B} (h : Step Good t) : Good t :=
  fun S hS => hS t (Step.mono (fun _u hu => hu S hS) h)

theorem Good.post {t : PTree A B} (h : Good t) : Step Good t :=
  h (Step Good) (fun _u hu => Step.mono (fun _v hv => Good.pre hv) hu)

/-- The carrier. -/
def W (A : Type u) (B : A → Type u) : Type u := {t : PTree A B // Good t}

open Classical in
/-- The raw tree of a node labelled `a` with children `f`. -/
noncomputable def mk (a : A) (f : B a → PTree A B) : PTree A B
  | [] => some a
  | x :: p => if h : x.1 = a then f (h ▸ x.2) p else none

theorem mk_nil (a : A) (f : B a → PTree A B) : mk a f [] = some a := rfl

theorem mk_sub (a : A) (f : B a → PTree A B) (b : B a) : subt (mk a f) ⟨a, b⟩ = f b := by
  funext p; simp [subt, mk]

theorem mk_ne (a : A) (f : B a → PTree A B) (x : Edge A B) (h : x.1 ≠ a) :
    subt (mk a f) x = nowhere := by
  funext p; simp [subt, mk, nowhere, h]

noncomputable def sup (a : A) (f : B a → W A B) : W A B :=
  ⟨mk a (fun b => (f b).1),
   Good.pre ⟨a, rfl, fun b => by rw [mk_sub]; exact (f b).2, fun x hx => mk_ne _ _ x hx⟩⟩

theorem isSome_root (w : W A B) : (w.1 []).isSome := by
  obtain ⟨a, ha, _, _⟩ := w.2.post
  rw [ha]; rfl

noncomputable def root (w : W A B) : A := (w.1 []).get (isSome_root w)

theorem root_spec (w : W A B) : w.1 [] = some (root w) := (Option.some_get _).symm

theorem root_eq {w : W A B} {a : A} (h : w.1 [] = some a) : root w = a := by
  rw [root_spec] at h; exact Option.some.inj h

theorem good_sub (w : W A B) (b : B (root w)) : Good (subt w.1 ⟨root w, b⟩) := by
  obtain ⟨a, ha, hk, _⟩ := w.2.post
  have hra : root w = a := root_eq ha
  subst hra; exact hk b

noncomputable def kids (w : W A B) (b : B (root w)) : W A B :=
  ⟨subt w.1 ⟨root w, b⟩, good_sub w b⟩

theorem canon (w : W A B) : w = sup (root w) (kids w) := by
  apply Subtype.ext
  obtain ⟨a, ha, _, hm⟩ := w.2.post
  have hra : root w = a := root_eq ha
  subst hra
  funext p
  match p with
  | [] => exact ha
  | ⟨x1, x2⟩ :: p =>
    by_cases h : x1 = root w
    · subst h
      show w.1 (⟨root w, x2⟩ :: p)
          = subt (mk (root w) (fun b => (kids w b).1)) ⟨root w, x2⟩ p
      rw [mk_sub]
      rfl
    · have := congrFun (hm ⟨x1, x2⟩ h) p
      show w.1 (⟨x1, x2⟩ :: p) = mk (root w) (fun b => (kids w b).1) (⟨x1, x2⟩ :: p)
      rw [show w.1 (⟨x1, x2⟩ :: p) = subt w.1 ⟨x1, x2⟩ p from rfl, this]
      simp [mk, nowhere, h]

theorem root_sup (a : A) (f : B a → W A B) : root (sup a f) = a := root_eq rfl

theorem kids_eq' (w : W A B) (f : B (root w) → W A B) (hw : w = sup (root w) f)
    (b : B (root w)) : kids w b = f b := by
  apply Subtype.ext
  have h1 : w.val = (sup (root w) f).val := congrArg Subtype.val hw
  show subt w.1 ⟨root w, b⟩ = (f b).1
  rw [h1]
  exact mk_sub (root w) (fun b => (f b).val) b

theorem kids_cast (w : W A B) (a : A) (f : B a → W A B) (hw : w = sup a f)
    (hra : root w = a) (b : B (root w)) : kids w b = f (cast (congrArg B hra) b) := by
  subst hra
  exact kids_eq' w f hw b

theorem kids_sup (a : A) (f : B a → W A B) (b : B (root (sup a f))) :
    kids (sup a f) b = f (cast (congrArg B (root_sup a f)) b) :=
  kids_cast (sup a f) a f rfl (root_sup a f) b

/-- Induction (small motive) is immediate from the fixpoint. -/
theorem Wind {P : W A B → Prop}
    (h : ∀ (a : A) (f : B a → W A B), (∀ b, P (f b)) → P (sup a f)) : ∀ w, P w := by
  have key : ∀ t : PTree A B, Good t → ∀ ht : Good t, P ⟨t, ht⟩ := by
    intro t hg
    refine hg (fun t => ∀ ht : Good t, P ⟨t, ht⟩) ?_
    intro u hu ht
    obtain ⟨a, ha, hk, _hm⟩ := hu
    have hra : root (⟨u, ht⟩ : W A B) = a := root_eq ha
    have hP : ∀ b : B (root (⟨u, ht⟩ : W A B)), P (kids ⟨u, ht⟩ b) := by
      intro b
      have : kids (⟨u, ht⟩ : W A B) b = ⟨subt u ⟨root ⟨u, ht⟩, b⟩, good_sub _ b⟩ := rfl
      rw [this]
      subst hra
      exact hk b _
    exact (canon (⟨u, ht⟩ : W A B)).symm ▸ h _ _ hP
  intro w
  exact key w.1 w.2 w.2

/-- The immediate-subtree relation. -/
def Sub (w' w : W A B) : Prop := ∃ b : B (root w), w' = kids w b

theorem sub_wf : ∀ w : W A B, Acc Sub w := by
  refine Wind ?_
  intro a f ih
  refine Acc.intro _ ?_
  rintro w' ⟨b, rfl⟩
  rw [kids_sup]
  exact ih _

theorem cast_symm_cancel {α β : Sort v} (h1 : β = α) (h2 : α = β) (x : β) :
    cast h2 (cast h1 x) = x := by
  cases h2; rfl

section Rec
variable {C : W A B → Sort v}
  (F : (a : A) → (f : B a → W A B) → ((b : B a) → C (f b)) → C (sup a f))

/-- The large recursor, by well-founded recursion on `Sub`. -/
noncomputable def Wrec : (w : W A B) → C w :=
  WellFounded.fix ⟨sub_wf⟩ fun w ih =>
    cast (congrArg C (canon w).symm) (F (root w) (kids w) fun b => ih (kids w b) ⟨b, rfl⟩)

theorem Wrec_unfold (w : W A B) :
    Wrec F w = cast (congrArg C (canon w).symm)
      (F (root w) (kids w) fun b => Wrec F (kids w b)) :=
  WellFounded.fix_eq _ _ _

theorem Wrec_key (w : W A B) (a : A) (f : B a → W A B) (h : w = sup a f) :
    cast (congrArg C h) (Wrec F w) = F a f (fun b => Wrec F (f b)) := by
  have hra : root w = a := by rw [h]; exact root_sup a f
  subst hra
  have hf : kids w = f := by
    funext b; exact kids_eq' w f h b
  subst hf
  rw [Wrec_unfold]
  exact cast_symm_cancel _ _ _

theorem Wrec_iota (a : A) (f : B a → W A B) :
    Wrec F (sup a f) = F a f (fun b => Wrec F (f b)) :=
  Wrec_key F (sup a f) a f rfl

end Rec

end WCon

open WCon

/-! ## Target 1: `BT` -- finite branching, two recursive fields. -/

/-- The yardstick. Used ONLY in the pins. -/
inductive BT : Type where
  | leaf : BT
  | node : BT → BT → BT

def ABT : Type := Bool
def BBT : ABT → Type := fun a => cond a Bool Empty

abbrev CBT : Type := W ABT BBT

noncomputable def CBT.leaf : CBT := sup false (fun e => Empty.elim e)
noncomputable def CBT.node (x y : CBT) : CBT := sup true (fun i => cond i x y)

noncomputable def CBT.rec' {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) : (t : CBT) → C t :=
  Wrec (C := C) (fun a =>
    Bool.rec (motive := fun a : ABT => (f : BBT a → CBT) → ((b : BBT a) → C (f b)) → C (sup a f))
      (fun f _ih =>
        cast (congrArg C (congrArg (sup false)
          (funext (fun e : BBT false => Empty.elim (C := (fun e' => Empty.elim e') e = f e) e))))
          hl)
      (fun f ih =>
        cast (congrArg C (congrArg (sup true)
          (funext (fun i : BBT true =>
            Bool.rec (motive := fun i : Bool => cond i (f true) (f false) = f i) rfl rfl i))))
          (hn (f true) (f false) (ih true) (ih false)))
      a)

theorem CBT.iota_leaf {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) :
    CBT.rec' hl hn CBT.leaf = hl :=
  Wrec_iota _ _ _

theorem CBT.iota_node {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) (x y : CBT) :
    CBT.rec' hl hn (CBT.node x y)
      = hn x y (CBT.rec' hl hn x) (CBT.rec' hl hn y) :=
  Wrec_iota _ _ _

/-! ## Target 2: `IT` -- infinite branching, recursive field under a binder. -/

inductive IT : Type where
  | sup : (Nat → IT) → IT

def AIT : Type := Unit
def BIT : AIT → Type := fun _ => Nat

abbrev CIT : Type := W AIT BIT

noncomputable def CIT.sup (g : Nat → CIT) : CIT := WCon.sup () g

noncomputable def CIT.rec' {C : CIT → Sort v}
    (h : (g : Nat → CIT) → ((n : Nat) → C (g n)) → C (CIT.sup g)) : (t : CIT) → C t :=
  Wrec (C := C) (fun _a f ih => h f ih)

theorem CIT.iota {C : CIT → Sort v}
    (h : (g : Nat → CIT) → ((n : Nat) → C (g n)) → C (CIT.sup g)) (g : Nat → CIT) :
    CIT.rec' h (CIT.sup g) = h g (fun n => CIT.rec' h (g n)) :=
  Wrec_iota _ _ _

/-! ## The four transcription pins. -/

noncomputable example : ∀ {motive : CBT → Sort v},
    motive CBT.leaf → ((a b : CBT) → motive a → motive b → motive (CBT.node a b)) →
    (t : CBT) → motive t := @CBT.rec'

noncomputable example : ∀ {motive : BT → Sort v},
    motive BT.leaf → ((a b : BT) → motive a → motive b → motive (BT.node a b)) →
    (t : BT) → motive t := @BT.rec

noncomputable example : ∀ {motive : CIT → Sort v},
    ((a : Nat → CIT) → ((n : Nat) → motive (a n)) → motive (CIT.sup a)) →
    (t : CIT) → motive t := @CIT.rec'

noncomputable example : ∀ {motive : IT → Sort v},
    ((a : Nat → IT) → ((n : Nat) → motive (a n)) → motive (IT.sup a)) →
    (t : IT) → motive t := @IT.rec

/-! ## Target 3 (extra): `DT` -- a non-recursive field the branch type DEPENDS on.

This was not asked for; it is here because it is the case I expected to resist
mechanisation and it turns out not to.  `A` is the whole non-recursive telescope,
`B` the branch type over it, and `W A B` is already the answer with no glue at all:
`rec'` is literally `Wrec` and `iota` is literally `Wrec_iota`. -/

inductive DT : Type where
  | mk : (n : Nat) → (Fin n → DT) → DT

abbrev CDT : Type := W Nat Fin

noncomputable def CDT.mk (n : Nat) (f : Fin n → CDT) : CDT := sup n f

noncomputable def CDT.rec' {C : CDT → Sort v}
    (h : (n : Nat) → (f : Fin n → CDT) → ((i : Fin n) → C (f i)) → C (CDT.mk n f)) :
    (t : CDT) → C t :=
  Wrec (C := C) h

theorem CDT.iota {C : CDT → Sort v}
    (h : (n : Nat) → (f : Fin n → CDT) → ((i : Fin n) → C (f i)) → C (CDT.mk n f))
    (n : Nat) (f : Fin n → CDT) :
    CDT.rec' h (CDT.mk n f) = h n f (fun i => CDT.rec' h (f i)) :=
  Wrec_iota _ _ _

noncomputable example : ∀ {motive : CDT → Sort v},
    ((n : Nat) → (f : Fin n → CDT) → ((i : Fin n) → motive (f i)) → motive (CDT.mk n f)) →
    (t : CDT) → motive t := @CDT.rec'

noncomputable example : ∀ {motive : DT → Sort v},
    ((n : Nat) → (f : Fin n → DT) → ((i : Fin n) → motive (f i)) → motive (DT.mk n f)) →
    (t : DT) → motive t := @DT.rec

/-! ## Non-degeneracy: the recursor is not blind to its step function. -/

/-- `leaf ≠ node` is derivable from the derived recursor + its two iota rules alone,
    so the model is not the degenerate "choose an element of `motive t`" recursor. -/
theorem CBT.leaf_ne_node (x y : CBT) : CBT.leaf ≠ CBT.node x y := by
  intro h
  have h1 := CBT.iota_leaf (C := fun _ => Prop) True (fun _ _ _ _ => False)
  have h2 := CBT.iota_node (C := fun _ => Prop) True (fun _ _ _ _ => False) x y
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

/-- Both iota rules, exercised together. -/
example : CBT.rec' (C := fun _ => Nat) 0 (fun _ _ m n => m + n + 1)
    (CBT.node CBT.leaf CBT.leaf) = 1 := by
  rw [CBT.iota_node, CBT.iota_leaf]

/-! ## Axiom bill, pinned. -/

/-- info: 'CBT.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CBT.rec'
/-- info: 'CBT.iota_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CBT.iota_leaf
/-- info: 'CBT.iota_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CBT.iota_node
/-- info: 'CIT.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CIT.rec'
/-- info: 'CIT.iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CIT.iota

/-! ## Dependency closure: which real inductives must exist before the W model. -/

open Lean in
/-- Closure of a constant set over BOTH types and values; collects every `inductInfo`. -/
partial def closureInds (env : Environment) :
    List Name → NameSet → NameSet → NameSet
  | [], _, inds => inds
  | n :: rest, seen, inds =>
    if seen.contains n then closureInds env rest seen inds
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closureInds env rest seen inds
      | some ci =>
        let inds := if ci matches .inductInfo _ then inds.insert n else inds
        let more := ci.type.getUsedConstants.toList ++
          (match ci.value? with | some v => v.getUsedConstants.toList | none => [])
        closureInds env (more ++ rest) seen inds

open Lean in
/--
info: 22 reachable inductives: Acc, And, Bool, Decidable, Empty, Eq, Exists, False, Fin, HEq, Iff, List, Nat, Nonempty, Option, Or, PProd, PUnit, Sigma, Subtype, True, WellFounded
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let roots := [`CBT.rec', `CBT.iota_leaf, `CBT.iota_node, `CIT.rec', `CIT.iota,
    `CDT.rec', `CDT.iota]
  let inds := closureInds env roots {} {}
  if inds.contains `BT || inds.contains `IT || inds.contains `DT then
    throwError "the yardstick leaked into the construction"
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"{names.size} reachable inductives: {String.intercalate ", " names.toList}"

open Lean in
/--
info: generic W core needs: Acc, And, Bool, Decidable, Eq, Exists, False, HEq, Iff, List, Nat, Nonempty, Option, Or, PProd, PUnit, Sigma, Subtype, True, WellFounded
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let inds := closureInds env [`WCon.W, `WCon.sup, `WCon.Wrec, `WCon.Wrec_iota] {} {}
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"generic W core needs: {String.intercalate ", " names.toList}"

/-- info: 'CDT.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CDT.rec'
/-- info: 'CDT.iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CDT.iota
