import Lean

/-
WIndexedCarve.lean -- the INDEXED carve ("skeleton plus `good`", thesis §5.2) built once
over the generic W-type of `WFromPaths.lean`, four indexed branching families
derived from it, and the non-indexed case recovered as its degenerate instance.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean WIndexedCarve.lean
Expected: 0 errors, 0 warnings, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
VERDICT
════════════════════════════════════════════════════════════════════════════
YES.  Build the indexed carve and the non-indexed case falls out as the
degenerate instance, with the SAME per-constructor glue -- not similar glue,
the same characters.  Build one arm, not two.

Three things make that answer strong rather than nominal:

  1. The degenerate instance reproduces the non-indexed INTERFACE exactly.
     `Deg.dsup`, `Deg.drec`, `Deg.drec_iota` are `ICon.isup`, `ICon.Irec`,
     `ICon.Irec_iota` at `ι := Unit`, and they are pinned by `example`s to have
     literally the types of `WCon.sup`, `WCon.Wrec`, `WCon.Wrec_iota`.

  2. `WFromPaths.lean`'s `BT`/`IT`/`DT` glue is reused verbatim.  The 67 lines
     from `def ABT` to `CDT.iota` in this file were produced from
     `WFromPaths.lean` by the substitution
         W A B -> Deg.dW A B,  sup -> Deg.dsup,
         Wrec -> Deg.drec,     Wrec_iota -> Deg.drec_iota
     and nothing else.  `check-glue.py` in this directory regenerates them and
     diffs; it exits 0.  No index argument, no index-equality hypothesis, no
     transport, no extra proof obligation appears in the non-indexed glue.

  3. The indexed glue does not pay for indices either.  The per-constructor
     work for `Tri`, `Two`, `Bal`, `ITree` is the same three items as for `BT`
     (chosen children function, eta lemma, one `cast` in the step), with two
     token-level differences and no new proof obligations.  See GLUE below.

The carve does NOT need genuinely indexed W-types.  A plain `W A B` over
ordinary Lean types, carved by a `Prop`-valued predicate, is enough.  That is
the fork the brief asks about, and we are on the plain-W side.  Three features
of Lean make it work, and they should be stated because a system missing any
one of them would land on the other side:
  * definitional proof irrelevance -- the `good` component of a carved element
    never obstructs an equality, so `Subtype.ext` is the whole story and
    `isup a (fun b => ⟨f b, _⟩)` is DEFINITIONALLY `⟨sup a f, _⟩`;
  * large elimination of `Eq` plus K-like reduction -- the index transport
    `cast (rebase_ty ... (e : idx a = x) ...)` disappears definitionally as
    soon as the two indices are the same term, which is why every `iota`
    theorem below is `ICon.Irec_iota _ _ _ _ _` and nothing more;
  * impredicative `Prop` -- the Knaster-Tarski `Good` of the underlying W, and
    `good` itself, are `Prop`-valued fixpoints.

════════════════════════════════════════════════════════════════════════════
WHAT COMPILED
════════════════════════════════════════════════════════════════════════════
Generic W (`WCon`, lines copied verbatim from `WFromPaths.lean`, unchanged).

Generic carve (`ICon`, 66 lines, the only new construction):
    parameters  `idx : A → ι`   -- the index a constructor produces
                `chi : (a : A) → B a → ι`  -- the index each child must carry
    `good : W A B → ι → Prop`  (by `Wrec` into `ι → Prop`), `good_unfold`,
    `good_iff`, `good_mk`, `P x := {s : W A B // good s x}`, `isup`,
    `rebase_ty`, `Irec`, `Irec_iota`.

Degenerate instance (`Deg`, 40 lines): `didx`, `dchi`, `dW`, `good_triv`
    (the carve is VACUOUS when `ι` is a subsingleton -- every skeleton is
    good), `toW`/`ofW` with both round trips `rfl`, `dsup`, `drec`,
    `drec_iota`.

Indexed targets, each with carrier, constructors, large recursor at Lean's
exact recursor type, and iota as a theorem:
  `Tri   : Nat → Type`        indexed, finite branching, two constructors
  `ITree : Nat → Type`        indexed, infinite branching under a binder
  `Two   : Nat → Type`        TWO CONSTRUCTORS AT THE SAME INDEX -- `Tri`'s
                              constructors are separated by their index (0 vs
                              m+n+1) so a broken model could pass its pins;
                              `Two.l n` and `Two.r n _ _` both live at `n`, and
                              `CTwo.l_ne_r` derives their disjointness from the
                              recursor and its two iotas alone
  `Bal   : Nat → Nat → Type`  an index TELESCOPE of length two

Non-indexed targets, re-derived THROUGH the carve at `ι := Unit`:
  `BT`, `IT`, `DT` -- glue byte-identical to `WFromPaths.lean` (item 2 above).

Pins: 7 pairs.  For each target the derived recursor AND Lean's own recursor
are checked against ONE transcription, so the transcription is measured against
Lean rather than trusted.  Plus 6 `example`s pinning the recovered non-indexed
interface against `WCon.sup` / `WCon.Wrec` / `WCon.Wrec_iota`.

Non-degeneracy: `CTwo.l_ne_r`, `CBT.leaf_ne_node`, three worked evaluations,
and two `example`s showing `good` is genuinely index-sensitive (the leaf
skeleton is good at 0 and not good at 1) -- i.e. the carve carves.

Closure: `Tri`, `ITree`, `Two`, `Bal`, `BT`, `IT`, `DT` are asserted (not just
reported) unreachable from the construction.  The yardsticks appear only in
the pins.

════════════════════════════════════════════════════════════════════════════
AXIOM BILL  (pinned below with `#guard_msgs`; 24 `#print axioms`)
════════════════════════════════════════════════════════════════════════════
Every one of `ICon.good`, `ICon.Irec`, `ICon.Irec_iota`, `Deg.good_triv`,
`Deg.drec`, `Deg.drec_iota`, and all 18 target `rec'`/`iota` constants:

    propext, Classical.choice, Quot.sound

Identical to `WFromPaths.lean`'s bill.  Indexing adds NO axiom: the carve is
`Prop`-valued and its transports are `Eq`, both free.  All three still come
from the underlying W (deciding `x.1 = a` for an arbitrary label type, and
`funext`), exactly as before.

Reachable inductives are also unchanged: the carve core
(`ICon.P/isup/Irec/Irec_iota`) reaches the SAME 20 inductives as the plain W
core (`WCon.W/sup/Wrec/Wrec_iota`).  It adds none.  Both lists are pinned.

════════════════════════════════════════════════════════════════════════════
THE PER-CONSTRUCTOR GLUE, side by side
════════════════════════════════════════════════════════════════════════════
NON-INDEXED (`CBT.node`, from `WFromPaths.lean`), three items:
  (a) chosen children function      `fun i => cond i x y`
  (b) eta lemma                     `Bool.rec (motive := fun i => cond i (f true) (f false) = f i)
                                       rfl rfl i`, under `funext`
  (c) one `cast` in the step arm    `cast (congrArg C (congrArg (dsup true) <eta>)) (hn ...)`

INDEXED (`CTri.node`), the same three items:
  (a) `CTri.nodeKids`  `fun b => Bool.rec (motive := fun b => CTri (chi a b)) y x b`
  (b) `CTri.nodeKids_eq`  `Bool.rec (motive := fun b => nodeKids m n (g true) (g false) b = g b)
                              rfl rfl b`, under `funext`
  (c) `cast (congrArg (C (idxTri (some p))) (congrArg (isup .. (some p)) <eta>)) (hn ...)`

The two differences, in full:
  * (a) `cond b x y` becomes `Bool.rec (motive := ...) y x b`.  Needed only
    when one constructor's recursive fields sit at DIFFERENT indices, because
    then the children function is dependently typed.  Same generator -- a
    k-way split over the branch enumeration -- one extra `motive :=`
    annotation.  `CTwo` and `CITree`, whose children share an index, keep
    `cond` and `fun` respectively.
  * (c) `congrArg C` becomes `congrArg (C (idx a))`, i.e. the motive is applied
    to the index first.  One extra argument, generated from `idx`.

What the indexed case does NOT need, and this is the finding:
  * NO per-constructor `good` proof.  `ICon.isup` discharges it generically:
    its premise `∀ b, good (g b) (chi a b)` is `fun b => (g b).2`.
  * NO per-constructor index-equality hypothesis and NO per-constructor
    transport.  Extracting `idx a = x` from the `good` proof and casting along
    it happens once, inside `ICon.Irec` (`rebase_ty`), and never surfaces.
  * NO change to the iota proofs.  All 11 are `ICon.Irec_iota _ _ _ _ _` (or
    `Deg.drec_iota _ _ _`) and nothing else, exactly as `WFromPaths.lean`'s
    were `Wrec_iota _ _ _`.

Cost of unification, stated honestly: the non-indexed carrier acquires a
`Subtype` wrapper, `dW A B = {s : W A B // good s ()}`, whose predicate is
provably always true (`Deg.good_triv`) with `toW`/`ofW` inverse by `rfl`.  That
is one indirection in the carrier and zero lines of per-declaration work.

════════════════════════════════════════════════════════════════════════════
NET
════════════════════════════════════════════════════════════════════════════
Cheaper to build the carve once.  Measured: `ICon` is 66 lines and `Deg` is 40,
against which a second non-indexed arm would be `WCon`'s `sup`/`Wrec`/
`Wrec_iota` re-exposed plus, more importantly, a second body of glue to
maintain.  The carve subsumes the non-indexed arm and, via the standard
reductions (mutual -> indexed, nested -> mutual), also puts mutual and nested
declarations inside reach of the same code, which the non-indexed arm never
was.

════════════════════════════════════════════════════════════════════════════
WHAT STILL BLOCKS MECHANISATION FOR AN ARBITRARY INDEXED BRANCHING DECLARATION
════════════════════════════════════════════════════════════════════════════
1. `idx` and `chi` must REDUCE.  The generated `rec'` only has Lean's exact
   recursor type if `idx (tag, args)` is definitionally the constructor's index
   expression, and likewise `chi`.  In this file that is four `rfl` `example`s
   per target and it holds because `idx`/`chi` are compiled matches on the tag.
   A generator must emit them so they reduce -- e.g. never behind an opaque
   `def` of the tag type.  This bit me once already: `AIT2` had to become an
   `abbrev` before `n + 1` would even elaborate.
   This is not a semantic restriction: a Lean constructor's index expressions
   can only mention its non-recursive fields (there is no way to compute an
   index out of a recursive field before the type exists), which is exactly
   what `idx : A → ι` and `chi : (a : A) → B a → ι` capture.
2. INDEX TELESCOPES need a wrapper.  `ι` is one type, so a length-k telescope
   becomes a nested product/Sigma and the motive is wrapped
   `fun x t => C x.1 x.2 t`, which typechecks only by structure eta.  Done and
   pinned for k = 2 (`Bal`).  A telescope whose later index TYPES depend on
   earlier indices needs `Sigma` rather than `Prod` there; the eta is the same
   and I expect no new content, but it is NOT tested here.
3. `Prop`-valued targets, and targets that only small-eliminate, are a
   different construction.  Unchanged from `WFromPaths.lean`.
4. Universe polymorphism: `A B : Type u`, `ι : Type w`, carrier in `Type u`.  A
   `Sort`-polymorphic target still does not fit the `List`-of-`Sigma` paths.
5. Iota is still propositional, not `rfl` -- `Wrec` goes through
   `WellFounded.fix`.  The carve does not make this worse; the index transport
   itself IS definitional.
6. The classical dispatch is unchanged and still removable in the common case
   where `B` factors through the constructor tag.
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

universe w

open WCon

/-! ############################################################
    ## The carve: an indexed family as a subtype of a plain W
    ############################################################ -/

namespace ICon

variable {ι : Type w} {A : Type u} {B : A → Type u}

section Carve
variable (idx : A → ι) (chi : (a : A) → B a → ι)

/-- `good s x` : the skeleton `s` is a well-indexed tree at index `x`. -/
noncomputable def good : W A B → ι → Prop :=
  Wrec (C := fun _ => ι → Prop) (fun a _f ih x => idx a = x ∧ ∀ b, ih b (chi a b))

theorem good_unfold (a : A) (f : B a → W A B) :
    good idx chi (sup a f) = fun x => idx a = x ∧ ∀ b, good idx chi (f b) (chi a b) :=
  Wrec_iota _ _ _

theorem good_iff (a : A) (f : B a → W A B) (x : ι) :
    good idx chi (sup a f) x ↔ (idx a = x ∧ ∀ b, good idx chi (f b) (chi a b)) := by
  rw [good_unfold]

theorem good_mk (a : A) (f : B a → W A B) (hb : ∀ b, good idx chi (f b) (chi a b)) :
    good idx chi (sup a f) (idx a) :=
  (good_iff idx chi a f (idx a)).2 ⟨rfl, hb⟩

/-- The carrier of the modelled indexed family. -/
def P (x : ι) : Type u := {s : W A B // good idx chi s x}

/-- The generic constructor. -/
noncomputable def isup (a : A) (g : (b : B a) → P idx chi (chi a b)) : P idx chi (idx a) :=
  ⟨sup a (fun b => (g b).1), good_mk idx chi a _ (fun b => (g b).2)⟩

theorem rebase_ty (C : (x : ι) → P idx chi x → Sort v) {x y : ι} (e : x = y) (s : W A B)
    (hx : good idx chi s x) (hy : good idx chi s y) :
    C x ⟨s, hx⟩ = C y ⟨s, hy⟩ := by
  subst e; rfl

section Rec
variable {C : (x : ι) → P idx chi x → Sort v}
  (F : (a : A) → (g : (b : B a) → P idx chi (chi a b)) →
        ((b : B a) → C (chi a b) (g b)) → C (idx a) (isup idx chi a g))

/-- The large recursor of the carved family, with the shape of Lean's own. -/
noncomputable def Irec : (x : ι) → (p : P idx chi x) → C x p := fun x p =>
  Wrec (C := fun s => (y : ι) → (hy : good idx chi s y) → C y ⟨s, hy⟩)
    (fun a f ih y hy =>
      cast (rebase_ty idx chi C ((good_iff idx chi a f y).1 hy).1 (sup a f)
              (good_mk idx chi a f ((good_iff idx chi a f y).1 hy).2) hy)
        (F a (fun b => ⟨f b, ((good_iff idx chi a f y).1 hy).2 b⟩)
             (fun b => ih b (chi a b) (((good_iff idx chi a f y).1 hy).2 b))))
    p.1 x p.2

theorem Irec_iota (a : A) (g : (b : B a) → P idx chi (chi a b)) :
    Irec idx chi F (idx a) (isup idx chi a g)
      = F a g (fun b => Irec idx chi F (chi a b) (g b)) := by
  have h := Wrec_iota (A := A) (B := B)
    (C := fun s => (y : ι) → (hy : good idx chi s y) → C y ⟨s, hy⟩)
    (fun a f ih y hy =>
      cast (rebase_ty idx chi C ((good_iff idx chi a f y).1 hy).1 (sup a f)
              (good_mk idx chi a f ((good_iff idx chi a f y).1 hy).2) hy)
        (F a (fun b => ⟨f b, ((good_iff idx chi a f y).1 hy).2 b⟩)
             (fun b => ih b (chi a b) (((good_iff idx chi a f y).1 hy).2 b))))
    a (fun b => (g b).1)
  exact congrFun (congrFun h (idx a)) (isup idx chi a g).2

end Rec
end Carve
end ICon

/-! ############################################################
    ## Indexed target 1: `Tri` -- indexed AND branching
    ############################################################ -/

/-- The yardstick.  Used ONLY in the pins. -/
inductive Tri : Nat → Type where
  | leaf : Tri 0
  | node : (m n : Nat) → Tri m → Tri n → Tri (m + n + 1)

/-- Constructor tag plus its non-recursive telescope. -/
def ATri : Type := Option (Nat × Nat)
/-- Branch type per tag. -/
def BTri : ATri → Type
  | none => Empty
  | some _ => Bool
/-- The index this constructor produces. -/
def idxTri : ATri → Nat
  | none => 0
  | some p => p.1 + p.2 + 1
/-- The index each child must carry. -/
def chiTri : (a : ATri) → BTri a → Nat
  | none => fun e => Empty.elim e
  | some p => fun b => cond b p.1 p.2

abbrev CTri : Nat → Type := ICon.P idxTri chiTri

-- the three reductions the glue relies on
example : idxTri none = 0 := rfl
example (m n : Nat) : idxTri (some (m, n)) = m + n + 1 := rfl
example (m n : Nat) : chiTri (some (m, n)) true = m := rfl
example (m n : Nat) : chiTri (some (m, n)) false = n := rfl

/-- GLUE (leaf): the chosen children function `BTri none ≅ Fin 0`. -/
noncomputable def CTri.leafKids : (b : BTri none) → CTri (chiTri none b) := fun e => Empty.elim e
/-- GLUE (leaf): the eta lemma. -/
theorem CTri.leafKids_eq (g : (b : BTri none) → CTri (chiTri none b)) : CTri.leafKids = g :=
  funext (fun e => Empty.elim (C := CTri.leafKids e = g e) e)

/-- GLUE (node): the chosen children function `BTri (some p) ≅ Fin 2`. -/
noncomputable def CTri.nodeKids (m n : Nat) (x : CTri m) (y : CTri n) :
    (b : BTri (some (m, n))) → CTri (chiTri (some (m, n)) b) :=
  fun b => Bool.rec (motive := fun b : Bool => CTri (chiTri (some (m, n)) b)) y x b
/-- GLUE (node): the eta lemma. -/
theorem CTri.nodeKids_eq (m n : Nat) (g : (b : BTri (some (m, n))) → CTri (chiTri (some (m, n)) b)) :
    CTri.nodeKids m n (g true) (g false) = g :=
  funext (fun b => Bool.rec
    (motive := fun b : Bool => CTri.nodeKids m n (g true) (g false) b = g b) rfl rfl b)

noncomputable def CTri.leaf : CTri 0 := ICon.isup idxTri chiTri none CTri.leafKids

noncomputable def CTri.node (m n : Nat) (x : CTri m) (y : CTri n) : CTri (m + n + 1) :=
  ICon.isup idxTri chiTri (some (m, n)) (CTri.nodeKids m n x y)

noncomputable def CTri.rec' {C : (a : Nat) → CTri a → Sort v}
    (hl : C 0 CTri.leaf)
    (hn : (m n : Nat) → (x : CTri m) → (y : CTri n) → C m x → C n y →
            C (m + n + 1) (CTri.node m n x y)) :
    {a : Nat} → (t : CTri a) → C a t :=
  fun {a} t =>
    ICon.Irec (C := C) idxTri chiTri
      (fun a =>
        Option.rec
          (motive := fun a : ATri =>
            (g : (b : BTri a) → CTri (chiTri a b)) →
            ((b : BTri a) → C (chiTri a b) (g b)) →
            C (idxTri a) (ICon.isup idxTri chiTri a g))
          (fun g _ih =>
            cast (congrArg (C 0)
                   (congrArg (ICon.isup idxTri chiTri none) (CTri.leafKids_eq g))) hl)
          (fun p g ih =>
            cast (congrArg (C (idxTri (some p)))
                   (congrArg (ICon.isup idxTri chiTri (some p)) (CTri.nodeKids_eq p.1 p.2 g)))
              (hn p.1 p.2 (g true) (g false) (ih true) (ih false)))
          a)
      a t

theorem CTri.iota_leaf {C : (a : Nat) → CTri a → Sort v}
    (hl : C 0 CTri.leaf)
    (hn : (m n : Nat) → (x : CTri m) → (y : CTri n) → C m x → C n y →
            C (m + n + 1) (CTri.node m n x y)) :
    CTri.rec' hl hn CTri.leaf = hl :=
  ICon.Irec_iota _ _ _ _ _

theorem CTri.iota_node {C : (a : Nat) → CTri a → Sort v}
    (hl : C 0 CTri.leaf)
    (hn : (m n : Nat) → (x : CTri m) → (y : CTri n) → C m x → C n y →
            C (m + n + 1) (CTri.node m n x y)) (m n : Nat) (x : CTri m) (y : CTri n) :
    CTri.rec' hl hn (CTri.node m n x y)
      = hn m n x y (CTri.rec' hl hn x) (CTri.rec' hl hn y) :=
  ICon.Irec_iota _ _ _ _ _

/-! ### Pin 1: the derived recursor and Lean's own, against ONE transcription. -/

noncomputable example : ∀ {motive : (a : Nat) → CTri a → Sort v},
    motive 0 CTri.leaf →
    ((m n : Nat) → (x : CTri m) → (y : CTri n) → motive m x → motive n y →
      motive (m + n + 1) (CTri.node m n x y)) →
    {a : Nat} → (t : CTri a) → motive a t := @CTri.rec'

noncomputable example : ∀ {motive : (a : Nat) → Tri a → Sort v},
    motive 0 Tri.leaf →
    ((m n : Nat) → (x : Tri m) → (y : Tri n) → motive m x → motive n y →
      motive (m + n + 1) (Tri.node m n x y)) →
    {a : Nat} → (t : Tri a) → motive a t := @Tri.rec

/-- Both iotas exercised together; the recursor is not blind to its step functions. -/
example : CTri.rec' (C := fun _ _ => Nat) 0 (fun _ _ _ _ p q => p + q + 1)
    (CTri.node 0 0 CTri.leaf CTri.leaf) = 1 := by
  rw [CTri.iota_node, CTri.iota_leaf]

/-! ############################################################
    ## Indexed target 2: `ITree` -- indexed, infinite branching
    ############################################################ -/

inductive ITree : Nat → Type where
  | mk : (n : Nat) → (Nat → ITree n) → ITree (n + 1)

abbrev AIT2 : Type := Nat
def BIT2 : AIT2 → Type := fun _ => Nat
def idxIT2 : AIT2 → Nat := fun n => n + 1
def chiIT2 : (a : AIT2) → BIT2 a → Nat := fun n _ => n

abbrev CITree : Nat → Type := ICon.P idxIT2 chiIT2

/-- NO glue: the constructor telescope is already in W's shape. -/
noncomputable def CITree.mk (n : Nat) (f : Nat → CITree n) : CITree (n + 1) :=
  ICon.isup idxIT2 chiIT2 n f

noncomputable def CITree.rec' {C : (a : Nat) → CITree a → Sort v}
    (h : (n : Nat) → (f : Nat → CITree n) → ((k : Nat) → C n (f k)) →
          C (n + 1) (CITree.mk n f)) :
    {a : Nat} → (t : CITree a) → C a t :=
  fun {a} t => ICon.Irec (C := C) idxIT2 chiIT2 h a t

theorem CITree.iota {C : (a : Nat) → CITree a → Sort v}
    (h : (n : Nat) → (f : Nat → CITree n) → ((k : Nat) → C n (f k)) →
          C (n + 1) (CITree.mk n f)) (n : Nat) (f : Nat → CITree n) :
    CITree.rec' h (CITree.mk n f) = h n f (fun k => CITree.rec' h (f k)) :=
  ICon.Irec_iota _ _ _ _ _

/-! ### Pin 2. -/

noncomputable example : ∀ {motive : (a : Nat) → CITree a → Sort v},
    ((n : Nat) → (f : Nat → CITree n) → ((k : Nat) → motive n (f k)) →
      motive (n + 1) (CITree.mk n f)) →
    {a : Nat} → (t : CITree a) → motive a t := @CITree.rec'

noncomputable example : ∀ {motive : (a : Nat) → ITree a → Sort v},
    ((n : Nat) → (f : Nat → ITree n) → ((k : Nat) → motive n (f k)) →
      motive (n + 1) (ITree.mk n f)) →
    {a : Nat} → (t : ITree a) → motive a t := @ITree.rec

/-! ############################################################
    ## The degenerate instance: `ι := Unit`
    ##
    ## Instantiating the carve at a one-point index type gives back, verbatim,
    ## the non-indexed W interface `dsup / drec / drec_iota` -- the same three
    ## names with the same three types as `WCon.sup / Wrec / Wrec_iota`.
    ############################################################ -/

namespace Deg

def didx (A : Type u) : A → Unit := fun _ => ()
def dchi (A : Type u) (B : A → Type u) : (a : A) → B a → Unit := fun _ _ => ()

/-- The degenerate carrier: a plain W carved by a predicate that is always true. -/
abbrev dW (A : Type u) (B : A → Type u) : Type u := ICon.P (didx A) (dchi A B) ()

variable {A : Type u} {B : A → Type u}

/-- The carve is VACUOUS at a subsingleton index type: every skeleton is good. -/
theorem good_triv : ∀ s : W A B, ICon.good (didx A) (dchi A B) s () := by
  refine Wind ?_
  intro a f ih
  exact ICon.good_mk (didx A) (dchi A B) a f ih

/-- ... so `dW A B` is `W A B` up to a retraction pair. -/
noncomputable def toW (p : dW A B) : W A B := p.1
noncomputable def ofW (s : W A B) : dW A B := ⟨s, good_triv s⟩
theorem to_of (s : W A B) : toW (ofW s) = s := rfl
theorem of_to (p : dW A B) : ofW (toW p) = p := rfl

/-- `WCon.sup`, recovered. -/
noncomputable def dsup (a : A) (f : B a → dW A B) : dW A B :=
  ICon.isup (didx A) (dchi A B) a f

/-- `WCon.Wrec`, recovered, with exactly its type. -/
noncomputable def drec {C : dW A B → Sort v}
    (F : (a : A) → (f : B a → dW A B) → ((b : B a) → C (f b)) → C (dsup a f)) :
    (w : dW A B) → C w :=
  fun w => ICon.Irec (C := fun (_ : Unit) (p : dW A B) => C p) (didx A) (dchi A B) F () w

/-- `WCon.Wrec_iota`, recovered. -/
theorem drec_iota {C : dW A B → Sort v}
    (F : (a : A) → (f : B a → dW A B) → ((b : B a) → C (f b)) → C (dsup a f))
    (a : A) (f : B a → dW A B) :
    drec F (dsup a f) = F a f (fun b => drec F (f b)) :=
  ICon.Irec_iota _ _ _ _ _

end Deg

/-! ### The recovered interface, pinned against `WCon`'s own. -/

noncomputable example : ∀ {A : Type u} {B : A → Type u} (a : A),
    (B a → WCon.W A B) → WCon.W A B := @WCon.sup
noncomputable example : ∀ {A : Type u} {B : A → Type u} (a : A),
    (B a → Deg.dW A B) → Deg.dW A B := @Deg.dsup

noncomputable example : ∀ {A : Type u} {B : A → Type u} {C : WCon.W A B → Sort v},
    ((a : A) → (f : B a → WCon.W A B) → ((b : B a) → C (f b)) → C (WCon.sup a f)) →
    (w : WCon.W A B) → C w := @WCon.Wrec

noncomputable example : ∀ {A : Type u} {B : A → Type u} {C : Deg.dW A B → Sort v},
    ((a : A) → (f : B a → Deg.dW A B) → ((b : B a) → C (f b)) → C (Deg.dsup a f)) →
    (w : Deg.dW A B) → C w := @Deg.drec

/-! ############################################################
    ## `BT`, `IT`, `DT` re-derived through the carve
    ##
    ## Everything from here to the pins is `WFromPaths.lean`'s glue with the
    ## three names renamed:  `sup -> Deg.dsup`, `Wrec -> Deg.drec`,
    ## `Wrec_iota -> Deg.drec_iota`, `W A B -> Deg.dW A B`.  Nothing else
    ## changed -- no index argument, no transport, no extra proof obligation.
    ## (`scripts/check-glue.py` in this directory regenerates it from
    ##  `WFromPaths.lean` by exactly that substitution.)
    ############################################################ -/

/-- Yardstick.  Used ONLY in the pins. -/
inductive BT : Type where
  | leaf : BT
  | node : BT → BT → BT

/-- Yardstick.  Used ONLY in the pins. -/
inductive IT : Type where
  | sup : (Nat → IT) → IT

def ABT : Type := Bool
def BBT : ABT → Type := fun a => cond a Bool Empty

abbrev CBT : Type := Deg.dW ABT BBT

noncomputable def CBT.leaf : CBT := Deg.dsup false (fun e => Empty.elim e)
noncomputable def CBT.node (x y : CBT) : CBT := Deg.dsup true (fun i => cond i x y)

noncomputable def CBT.rec' {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) : (t : CBT) → C t :=
  Deg.drec (C := C) (fun a =>
    Bool.rec (motive := fun a : ABT => (f : BBT a → CBT) → ((b : BBT a) → C (f b)) → C (Deg.dsup a f))
      (fun f _ih =>
        cast (congrArg C (congrArg (Deg.dsup false)
          (funext (fun e : BBT false => Empty.elim (C := (fun e' => Empty.elim e') e = f e) e))))
          hl)
      (fun f ih =>
        cast (congrArg C (congrArg (Deg.dsup true)
          (funext (fun i : BBT true =>
            Bool.rec (motive := fun i : Bool => cond i (f true) (f false) = f i) rfl rfl i))))
          (hn (f true) (f false) (ih true) (ih false)))
      a)

theorem CBT.iota_leaf {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) :
    CBT.rec' hl hn CBT.leaf = hl :=
  Deg.drec_iota _ _ _

theorem CBT.iota_node {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) (x y : CBT) :
    CBT.rec' hl hn (CBT.node x y)
      = hn x y (CBT.rec' hl hn x) (CBT.rec' hl hn y) :=
  Deg.drec_iota _ _ _

def AIT : Type := Unit
def BIT : AIT → Type := fun _ => Nat

abbrev CIT : Type := Deg.dW AIT BIT

noncomputable def CIT.sup (g : Nat → CIT) : CIT := Deg.dsup () g

noncomputable def CIT.rec' {C : CIT → Sort v}
    (h : (g : Nat → CIT) → ((n : Nat) → C (g n)) → C (CIT.sup g)) : (t : CIT) → C t :=
  Deg.drec (C := C) (fun _a f ih => h f ih)

theorem CIT.iota {C : CIT → Sort v}
    (h : (g : Nat → CIT) → ((n : Nat) → C (g n)) → C (CIT.sup g)) (g : Nat → CIT) :
    CIT.rec' h (CIT.sup g) = h g (fun n => CIT.rec' h (g n)) :=
  Deg.drec_iota _ _ _

inductive DT : Type where
  | mk : (n : Nat) → (Fin n → DT) → DT

abbrev CDT : Type := Deg.dW Nat Fin

noncomputable def CDT.mk (n : Nat) (f : Fin n → CDT) : CDT := Deg.dsup n f

noncomputable def CDT.rec' {C : CDT → Sort v}
    (h : (n : Nat) → (f : Fin n → CDT) → ((i : Fin n) → C (f i)) → C (CDT.mk n f)) :
    (t : CDT) → C t :=
  Deg.drec (C := C) h

theorem CDT.iota {C : CDT → Sort v}
    (h : (n : Nat) → (f : Fin n → CDT) → ((i : Fin n) → C (f i)) → C (CDT.mk n f))
    (n : Nat) (f : Fin n → CDT) :
    CDT.rec' h (CDT.mk n f) = h n f (fun i => CDT.rec' h (f i)) :=
  Deg.drec_iota _ _ _

/-! ### Pins 3-5: each derived recursor and Lean's own, against ONE transcription. -/

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

noncomputable example : ∀ {motive : CDT → Sort v},
    ((n : Nat) → (f : Fin n → CDT) → ((i : Fin n) → motive (f i)) → motive (CDT.mk n f)) →
    (t : CDT) → motive t := @CDT.rec'

noncomputable example : ∀ {motive : DT → Sort v},
    ((n : Nat) → (f : Fin n → DT) → ((i : Fin n) → motive (f i)) → motive (DT.mk n f)) →
    (t : DT) → motive t := @DT.rec

/-- Non-degeneracy, unchanged from `WFromPaths.lean`. -/
theorem CBT.leaf_ne_node (x y : CBT) : CBT.leaf ≠ CBT.node x y := by
  intro h
  have h1 := CBT.iota_leaf (C := fun _ => Prop) True (fun _ _ _ _ => False)
  have h2 := CBT.iota_node (C := fun _ => Prop) True (fun _ _ _ _ => False) x y
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

example : CBT.rec' (C := fun _ => Nat) 0 (fun _ _ m n => m + n + 1)
    (CBT.node CBT.leaf CBT.leaf) = 1 := by
  rw [CBT.iota_node, CBT.iota_leaf]

/-! ############################################################
    ## Indexed target 3: `Two` -- two constructors at the SAME index
    ##
    ## `Tri`'s two constructors are separated by their index (0 vs m+n+1), so
    ## a broken model could still pass its pins.  Here every index is inhabited
    ## by both constructors, so the recursor has to tell them apart on its own.
    ############################################################ -/

inductive Two : Nat → Type where
  | l : (n : Nat) → Two n
  | r : (n : Nat) → Two (n + 1) → Two (n + 1) → Two n

/-- `A := Σ tag, (that tag's non-recursive telescope)`, here `Bool × Nat`. -/
def ATwo : Type := Bool × Nat
def BTwo : ATwo → Type := fun a => cond a.1 Bool Empty
def idxTwo : ATwo → Nat := fun a => a.2
def chiTwo : (a : ATwo) → BTwo a → Nat := fun a _ => a.2 + 1

abbrev CTwo : Nat → Type := ICon.P idxTwo chiTwo

/-- GLUE (l): chosen children function + eta lemma. -/
noncomputable def CTwo.lKids (n : Nat) : (b : BTwo (false, n)) → CTwo (chiTwo (false, n) b) :=
  fun e => Empty.elim e
theorem CTwo.lKids_eq (n : Nat) (g : (b : BTwo (false, n)) → CTwo (chiTwo (false, n) b)) :
    CTwo.lKids n = g :=
  funext (fun e => Empty.elim (C := CTwo.lKids n e = g e) e)

/-- GLUE (r): chosen children function + eta lemma. -/
noncomputable def CTwo.rKids (n : Nat) (x y : CTwo (n + 1)) :
    (b : BTwo (true, n)) → CTwo (chiTwo (true, n) b) :=
  fun b => cond b x y
theorem CTwo.rKids_eq (n : Nat) (g : (b : BTwo (true, n)) → CTwo (chiTwo (true, n) b)) :
    CTwo.rKids n (g true) (g false) = g :=
  funext (fun b => Bool.rec
    (motive := fun b : Bool => CTwo.rKids n (g true) (g false) b = g b) rfl rfl b)

noncomputable def CTwo.l (n : Nat) : CTwo n := ICon.isup idxTwo chiTwo (false, n) (CTwo.lKids n)
noncomputable def CTwo.r (n : Nat) (x y : CTwo (n + 1)) : CTwo n :=
  ICon.isup idxTwo chiTwo (true, n) (CTwo.rKids n x y)

noncomputable def CTwo.rec' {C : (a : Nat) → CTwo a → Sort v}
    (hl : (n : Nat) → C n (CTwo.l n))
    (hr : (n : Nat) → (x y : CTwo (n + 1)) → C (n + 1) x → C (n + 1) y → C n (CTwo.r n x y)) :
    {a : Nat} → (t : CTwo a) → C a t :=
  fun {a} t =>
    ICon.Irec (C := C) idxTwo chiTwo
      (fun a =>
        Bool.rec
          (motive := fun t : Bool =>
            (g : (b : BTwo (t, a.2)) → CTwo (chiTwo (t, a.2) b)) →
            ((b : BTwo (t, a.2)) → C (chiTwo (t, a.2) b) (g b)) →
            C (idxTwo (t, a.2)) (ICon.isup idxTwo chiTwo (t, a.2) g))
          (fun g _ih =>
            cast (congrArg (C a.2)
                   (congrArg (ICon.isup idxTwo chiTwo (false, a.2)) (CTwo.lKids_eq a.2 g)))
              (hl a.2))
          (fun g ih =>
            cast (congrArg (C a.2)
                   (congrArg (ICon.isup idxTwo chiTwo (true, a.2)) (CTwo.rKids_eq a.2 g)))
              (hr a.2 (g true) (g false) (ih true) (ih false)))
          a.1)
      a t

theorem CTwo.iota_l {C : (a : Nat) → CTwo a → Sort v}
    (hl : (n : Nat) → C n (CTwo.l n))
    (hr : (n : Nat) → (x y : CTwo (n + 1)) → C (n + 1) x → C (n + 1) y → C n (CTwo.r n x y))
    (n : Nat) :
    CTwo.rec' hl hr (CTwo.l n) = hl n :=
  ICon.Irec_iota _ _ _ _ _

theorem CTwo.iota_r {C : (a : Nat) → CTwo a → Sort v}
    (hl : (n : Nat) → C n (CTwo.l n))
    (hr : (n : Nat) → (x y : CTwo (n + 1)) → C (n + 1) x → C (n + 1) y → C n (CTwo.r n x y))
    (n : Nat) (x y : CTwo (n + 1)) :
    CTwo.rec' hl hr (CTwo.r n x y)
      = hr n x y (CTwo.rec' hl hr x) (CTwo.rec' hl hr y) :=
  ICon.Irec_iota _ _ _ _ _

/-! ### Pin 6. -/

noncomputable example : ∀ {motive : (a : Nat) → CTwo a → Sort v},
    ((n : Nat) → motive n (CTwo.l n)) →
    ((n : Nat) → (x y : CTwo (n + 1)) → motive (n + 1) x → motive (n + 1) y →
      motive n (CTwo.r n x y)) →
    {a : Nat} → (t : CTwo a) → motive a t := @CTwo.rec'

noncomputable example : ∀ {motive : (a : Nat) → Two a → Sort v},
    ((n : Nat) → motive n (Two.l n)) →
    ((n : Nat) → (x y : Two (n + 1)) → motive (n + 1) x → motive (n + 1) y →
      motive n (Two.r n x y)) →
    {a : Nat} → (t : Two a) → motive a t := @Two.rec

/-- Two constructors at the SAME index stay apart, from the recursor + iotas alone. -/
theorem CTwo.l_ne_r (n : Nat) (x y : CTwo (n + 1)) : CTwo.l n ≠ CTwo.r n x y := by
  intro h
  have h1 := CTwo.iota_l (C := fun _ _ => Prop) (fun _ => True) (fun _ _ _ _ _ => False) n
  have h2 := CTwo.iota_r (C := fun _ _ => Prop) (fun _ => True) (fun _ _ _ _ _ => False) n x y
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

/-! ### The carve actually carves: `good` is index-sensitive.

At a non-trivial index type the predicate is not vacuous -- the leaf skeleton is
good at 0 and not good at 1.  (Contrast `Deg.good_triv`, which shows it IS
vacuous when `ι` is a subsingleton: that is exactly why the degenerate instance
costs nothing.) -/

example : ICon.good idxTri chiTri (CTri.leaf.1) 0 := CTri.leaf.2

example : ¬ ICon.good idxTri chiTri (CTri.leaf.1) 1 := by
  intro h
  have h0 := ((ICon.good_iff idxTri chiTri none (fun b => (CTri.leafKids b).1) 1).1 h).1
  exact absurd h0 (by decide)

/-! ############################################################
    ## Indexed target 4: `Bal` -- an index TELESCOPE of length 2
    ##
    ## `ι` is a single type, so a k-ary index telescope becomes `ι := Nat × Nat`
    ## (in general a nested Sigma over the telescope).  The only cost is a motive
    ## wrapper `fun x t => C x.1 x.2 t`, which typechecks by structure eta.
    ## No new machinery below the wrapper.
    ############################################################ -/

inductive Bal : Nat → Nat → Type where
  | tip : Bal 0 0
  | bin : (a b c d : Nat) → Bal a b → Bal c d → Bal (a + c + 1) (b + d)

def ABal : Type := Option (Nat × Nat × Nat × Nat)
def BBal : ABal → Type
  | none => Empty
  | some _ => Bool
def idxBal : ABal → Nat × Nat
  | none => (0, 0)
  | some q => (q.1 + q.2.2.1 + 1, q.2.1 + q.2.2.2)
def chiBal : (a : ABal) → BBal a → Nat × Nat
  | none => fun e => Empty.elim e
  | some q => fun t => cond t (q.1, q.2.1) (q.2.2.1, q.2.2.2)

abbrev CBal (a b : Nat) : Type := ICon.P idxBal chiBal (a, b)

example : idxBal none = (0, 0) := rfl
example (a b c d : Nat) : idxBal (some (a, b, c, d)) = (a + c + 1, b + d) := rfl
example (a b c d : Nat) : chiBal (some (a, b, c, d)) true = (a, b) := rfl
example (a b c d : Nat) : chiBal (some (a, b, c, d)) false = (c, d) := rfl

/-- GLUE (tip). -/
noncomputable def CBal.tipKids :
    (t : BBal none) → ICon.P idxBal chiBal (chiBal none t) := fun e => Empty.elim e
theorem CBal.tipKids_eq (g : (t : BBal none) → ICon.P idxBal chiBal (chiBal none t)) :
    CBal.tipKids = g :=
  funext (fun e => Empty.elim (C := CBal.tipKids e = g e) e)

/-- GLUE (bin). -/
noncomputable def CBal.binKids (a b c d : Nat) (x : CBal a b) (y : CBal c d) :
    (t : BBal (some (a, b, c, d))) → ICon.P idxBal chiBal (chiBal (some (a, b, c, d)) t) :=
  fun t => Bool.rec
    (motive := fun t : Bool => ICon.P idxBal chiBal (chiBal (some (a, b, c, d)) t)) y x t
theorem CBal.binKids_eq (a b c d : Nat)
    (g : (t : BBal (some (a, b, c, d))) → ICon.P idxBal chiBal (chiBal (some (a, b, c, d)) t)) :
    CBal.binKids a b c d (g true) (g false) = g :=
  funext (fun t => Bool.rec
    (motive := fun t : Bool => CBal.binKids a b c d (g true) (g false) t = g t) rfl rfl t)

noncomputable def CBal.tip : CBal 0 0 := ICon.isup idxBal chiBal none CBal.tipKids
noncomputable def CBal.bin (a b c d : Nat) (x : CBal a b) (y : CBal c d) :
    CBal (a + c + 1) (b + d) :=
  ICon.isup idxBal chiBal (some (a, b, c, d)) (CBal.binKids a b c d x y)

noncomputable def CBal.rec' {C : (a b : Nat) → CBal a b → Sort v}
    (ht : C 0 0 CBal.tip)
    (hb : (a b c d : Nat) → (x : CBal a b) → (y : CBal c d) → C a b x → C c d y →
            C (a + c + 1) (b + d) (CBal.bin a b c d x y)) :
    {a b : Nat} → (t : CBal a b) → C a b t :=
  fun {a b} t =>
    ICon.Irec (C := fun (x : Nat × Nat) (p : ICon.P idxBal chiBal x) => C x.1 x.2 p)
      idxBal chiBal
      (fun a =>
        Option.rec
          (motive := fun a : ABal =>
            (g : (t : BBal a) → ICon.P idxBal chiBal (chiBal a t)) →
            ((t : BBal a) → C (chiBal a t).1 (chiBal a t).2 (g t)) →
            C (idxBal a).1 (idxBal a).2 (ICon.isup idxBal chiBal a g))
          (fun g _ih =>
            cast (congrArg (C 0 0)
                   (congrArg (ICon.isup idxBal chiBal none) (CBal.tipKids_eq g))) ht)
          (fun q g ih =>
            cast (congrArg (C (idxBal (some q)).1 (idxBal (some q)).2)
                   (congrArg (ICon.isup idxBal chiBal (some q))
                     (CBal.binKids_eq q.1 q.2.1 q.2.2.1 q.2.2.2 g)))
              (hb q.1 q.2.1 q.2.2.1 q.2.2.2 (g true) (g false) (ih true) (ih false)))
          a)
      (a, b) t

theorem CBal.iota_tip {C : (a b : Nat) → CBal a b → Sort v}
    (ht : C 0 0 CBal.tip)
    (hb : (a b c d : Nat) → (x : CBal a b) → (y : CBal c d) → C a b x → C c d y →
            C (a + c + 1) (b + d) (CBal.bin a b c d x y)) :
    CBal.rec' ht hb CBal.tip = ht :=
  ICon.Irec_iota _ _ _ _ _

theorem CBal.iota_bin {C : (a b : Nat) → CBal a b → Sort v}
    (ht : C 0 0 CBal.tip)
    (hb : (a b c d : Nat) → (x : CBal a b) → (y : CBal c d) → C a b x → C c d y →
            C (a + c + 1) (b + d) (CBal.bin a b c d x y))
    (a b c d : Nat) (x : CBal a b) (y : CBal c d) :
    CBal.rec' ht hb (CBal.bin a b c d x y)
      = hb a b c d x y (CBal.rec' ht hb x) (CBal.rec' ht hb y) :=
  ICon.Irec_iota _ _ _ _ _

/-! ### Pin 7. -/

noncomputable example : ∀ {motive : (a b : Nat) → CBal a b → Sort v},
    motive 0 0 CBal.tip →
    ((a b c d : Nat) → (x : CBal a b) → (y : CBal c d) → motive a b x → motive c d y →
      motive (a + c + 1) (b + d) (CBal.bin a b c d x y)) →
    {a b : Nat} → (t : CBal a b) → motive a b t := @CBal.rec'

noncomputable example : ∀ {motive : (a b : Nat) → Bal a b → Sort v},
    motive 0 0 Bal.tip →
    ((a b c d : Nat) → (x : Bal a b) → (y : Bal c d) → motive a b x → motive c d y →
      motive (a + c + 1) (b + d) (Bal.bin a b c d x y)) →
    {a b : Nat} → (t : Bal a b) → motive a b t := @Bal.rec

example : CBal.rec' (C := fun _ _ _ => Nat) 0 (fun _ _ _ _ _ _ p q => p + q + 1)
    (CBal.bin 0 0 0 0 CBal.tip CBal.tip) = 1 := by
  rw [CBal.iota_bin, CBal.iota_tip]

/-! ### One more pin on the recovered interface: the iota rule. -/

example : ∀ {A : Type u} {B : A → Type u} {C : WCon.W A B → Sort v}
    (F : (a : A) → (f : B a → WCon.W A B) → ((b : B a) → C (f b)) → C (WCon.sup a f))
    (a : A) (f : B a → WCon.W A B),
    WCon.Wrec F (WCon.sup a f) = F a f (fun b => WCon.Wrec F (f b)) := @WCon.Wrec_iota

example : ∀ {A : Type u} {B : A → Type u} {C : Deg.dW A B → Sort v}
    (F : (a : A) → (f : B a → Deg.dW A B) → ((b : B a) → C (f b)) → C (Deg.dsup a f))
    (a : A) (f : B a → Deg.dW A B),
    Deg.drec F (Deg.dsup a f) = F a f (fun b => Deg.drec F (f b)) := @Deg.drec_iota

/-! ############################################################
    ## Axiom bill, pinned.  Identical to the non-indexed model's:
    ## indexing costs nothing here.
    ############################################################ -/

/-- info: 'ICon.good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ICon.good
/-- info: 'ICon.Irec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ICon.Irec
/-- info: 'ICon.Irec_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ICon.Irec_iota
/-- info: 'CTri.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CTri.rec'
/-- info: 'CTri.iota_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CTri.iota_leaf
/-- info: 'CTri.iota_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CTri.iota_node
/-- info: 'CITree.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CITree.rec'
/-- info: 'CITree.iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CITree.iota
/-- info: 'CTwo.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CTwo.rec'
/-- info: 'CTwo.iota_l' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CTwo.iota_l
/-- info: 'CTwo.iota_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CTwo.iota_r
/-- info: 'CBal.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CBal.rec'
/-- info: 'CBal.iota_tip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CBal.iota_tip
/-- info: 'CBal.iota_bin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CBal.iota_bin
/-- info: 'Deg.good_triv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deg.good_triv
/-- info: 'Deg.drec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deg.drec
/-- info: 'Deg.drec_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Deg.drec_iota
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
/-- info: 'CDT.rec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CDT.rec'
/-- info: 'CDT.iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CDT.iota

/-! ############################################################
    ## Dependency closure, and the assertion that no yardstick leaked.
    ############################################################ -/

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
info: 26 reachable inductives: Acc, Add, And, Bool, Decidable, Empty, Eq, Exists, False, Fin, HAdd, HEq, Iff, List, Nat, Nonempty, OfNat, Option, Or, PProd, PUnit, Prod, Sigma, Subtype, True, WellFounded
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let roots := [`CTri.rec', `CTri.iota_leaf, `CTri.iota_node, `CITree.rec', `CITree.iota,
    `CTwo.rec', `CTwo.iota_l, `CTwo.iota_r, `CBal.rec', `CBal.iota_tip, `CBal.iota_bin,
    `CBT.rec', `CBT.iota_leaf, `CBT.iota_node, `CIT.rec', `CIT.iota, `CDT.rec', `CDT.iota]
  let inds := closureInds env roots {} {}
  for bad in [`Tri, `ITree, `Two, `Bal, `BT, `IT, `DT] do
    if inds.contains bad then throwError "the yardstick {bad} leaked into the construction"
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"{names.size} reachable inductives: {String.intercalate ", " names.toList}"

open Lean in
/--
info: indexed carve core needs: Acc, And, Bool, Decidable, Eq, Exists, False, HEq, Iff, List, Nat, Nonempty, Option, Or, PProd, PUnit, Sigma, Subtype, True, WellFounded
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let inds := closureInds env [`ICon.P, `ICon.isup, `ICon.Irec, `ICon.Irec_iota] {} {}
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"indexed carve core needs: {String.intercalate ", " names.toList}"

open Lean in
/--
info: plain W core needs: Acc, And, Bool, Decidable, Eq, Exists, False, HEq, Iff, List, Nat, Nonempty, Option, Or, PProd, PUnit, Sigma, Subtype, True, WellFounded
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let inds := closureInds env [`WCon.W, `WCon.sup, `WCon.Wrec, `WCon.Wrec_iota] {} {}
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"plain W core needs: {String.intercalate ", " names.toList}"
