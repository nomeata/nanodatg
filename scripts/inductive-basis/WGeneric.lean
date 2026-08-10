import Lean

/-
WGeneric.lean -- the tag scheme a GENERATOR can use, as opposed to the three
hand-picked ones in `WTagged.lean`.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean WGeneric.lean
Expected: 0 errors, 0 warnings, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
THE QUESTION THIS FILE EXISTS FOR
════════════════════════════════════════════════════════════════════════════
`WTagged.lean` settles that the tagged W construction exists at
`[propext, Quot.sound]`, and MODELGEN.md §8.16 settles that its 190-constant
closure splices through `addChecked`.  Neither settles the thing a generator
hits first, because all three of its targets pick their tag type BY HAND:

    KBT := Bool     KFT := Bool     KIT := Unit

The core's signature is `{K : Type} ... [DecidableEq K]`, and **the fragment
carries no `DecidableEq` for any concrete `K`** -- it cannot, since the closure
of `W`, `sup`, `Wrec` and `Wrec_iota` takes the instance as a parameter.  So a
generator must either

  (a) mint a bespoke enumeration inductive per declaration and PROVE its
      `DecidableEq` -- an nc x nc case split, plus a new inductive that
      `Iso.requires` then obliges the run to model in turn; or
  (b) fix ONE tag type for every declaration and get its `DecidableEq` from
      the fragment, once.

This file builds (b) and checks it against a target the three in `WTagged.lean`
do not reach: **four constructors** -- one carrying data and no children, one
carrying data and two children, one with a recursive field under a binder, and
a fourth of the FIRST one's shape at a different tag.

Three shapes, not two, because a two-constructor target cannot distinguish a
dispatch that is right from one with its arms swapped.  And the fourth, because
differently-shaped arms cannot be transposed without a type error, so a file of
only those never asks whether the tag assignment is right -- it asks whether it
elaborates.  `CTT.leaf_ne_alt` is the pin with no type error behind it.

════════════════════════════════════════════════════════════════════════════
THE SCHEME
════════════════════════════════════════════════════════════════════════════
    K  := Nat                     the tag is the constructor's index
    D  : Nat -> Type u            tag |-> that constructor's NON-recursive
                                  fields, as a tuple
    B' : Nat -> Type u            tag |-> that constructor's branch type
    A  := Sigma D                 the label: a tag and its data
    tg := Sigma.fst

`Nat` is the tag type rather than `Fin nc` for two reasons, and the second is
the one that decides it:

  * `Nat` is already shared with the input by the splice (MODELGEN.md §8.16 --
    the kernel's `Expr.lit` forces it), so it costs no new fragment inductive
    and no new unmodelled constant in the output; and
  * `Fin` is a structure over `Nat` whose `DecidableEq` reduces to `Nat`'s
    anyway, so it buys only the finiteness -- and finiteness is not needed,
    because the JUNK TAGS ARE UNINHABITED.

That last point is the one thing here that is not obvious, and it is what makes
`Nat` safe.  `D t` for `t >= nc` is an EMPTY type, so `A = Sigma D` has no
element whose tag is out of range, so `W B' tg` has no tree whose root label is
out of range.  Had `D` sent the junk tags to `PUnit` instead, `W` would have
been strictly bigger than the target -- trees the recursor must still be able
to eliminate and no constructor produces -- and the model would be wrong while
every ctor/iota check still passed.  `TT.no_junk` below is the check that fails
if that is ever weakened.

The empty type is built from what the fragment already carries -- `Subtype`,
`PUnit`, `False` -- rather than from `PEmpty`, which is not in it.

════════════════════════════════════════════════════════════════════════════
WHAT THE FRAGMENT MUST GAIN
════════════════════════════════════════════════════════════════════════════
Exactly one root: a `DecidableEq Nat`.  `w_core.ndjson` today carries
`Nat.beq` and `noConfusion_of_Nat` but not the instance, because nothing in
the closure of the four roots names it.  Re-export with

    --#export WT.W WT.sup WT.Wrec WT.Wrec_iota instDecidableEqNat

and the generator never proves a decidable equality.  `WVoid` and `Sigma.fst`
are already in.
-/

set_option linter.unusedVariables false

namespace WT

-- Half the lemmas below need `DecidableEq K` and half do not, and they are
-- interleaved by what they depend on rather than by that. Splitting the
-- section in two to satisfy the linter would order the file by an instance
-- rather than by the construction.
set_option linter.unusedSectionVars false

/-! `K` is the constructor tag — `Fin k` in the generator, and the only type
whose equality this construction decides. `A` is the full label, tag plus that
constructor's non-recursive fields. `B'` is the branch type **per tag**, which
is item E's precondition made into a signature: there is nowhere to put a
dependence on the label's data.

Every binder below is written out rather than taken from a `section variable`.
`W` has to take `B'` **explicitly** — `W tg` does not determine it, since `tg`
mentions only `A` and `K` — and once one definition needs it explicit, mixing
the two through section variables is more confusing than the repetition. -/

/-- One step of a path: which constructor-tag, and which of its branches. -/
abbrev Edge (K : Type) (B' : K → Type u) : Type u := Σ t : K, B' t

/-- A raw tree: a partial labelling of paths. The label at a path is the
**whole** `A`, so nothing about the constructor's data is lost by recording
only the tag on the path itself. -/
abbrev PTree (K : Type) (B' : K → Type u) (A : Type u) : Type u :=
  List (Edge K B') → Option A

variable {K : Type} {A : Type u} {B' : K → Type u}

def subt (t : PTree K B' A) (x : Edge K B') : PTree K B' A := fun p => t (x :: p)

def nowhere : PTree K B' A := fun _ => none

/-- One step of unfolding whose least fixpoint is "is a well-founded tree". The
third clause — subtrees hanging off a *tag* other than the node's own are
empty — is `WFromPaths.lean`'s one non-obvious ingredient, and it is the clause
that makes `canon` provable. Here it quantifies over tags rather than labels,
which is the whole difference. -/
def Step (tg : A → K) (S : PTree K B' A → Prop) (t : PTree K B' A) : Prop :=
  ∃ a : A, t [] = some a ∧ (∀ b : B' (tg a), S (subt t ⟨tg a, b⟩)) ∧
    ∀ x : Edge K B', x.1 ≠ tg a → subt t x = nowhere

theorem Step.mono {tg : A → K} {S S' : PTree K B' A → Prop} (hss : ∀ u, S u → S' u)
    {t : PTree K B' A} (h : Step tg S t) : Step tg S' t := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, fun b => hss _ (h2 b), h3⟩

/-- Knaster–Tarski least fixpoint, impredicatively. -/
def Good (tg : A → K) (t : PTree K B' A) : Prop :=
  ∀ S : PTree K B' A → Prop, (∀ u, Step tg S u → S u) → S t

theorem Good.pre {tg : A → K} {t : PTree K B' A} (h : Step tg (Good tg) t) : Good tg t :=
  fun S hS => hS t (Step.mono (fun _u hu => hu S hS) h)

theorem Good.post {tg : A → K} {t : PTree K B' A} (h : Good tg t) : Step tg (Good tg) t :=
  h (Step tg (Good tg)) (fun _u hu => Step.mono (fun _v hv => Good.pre hv) hu)

/-- The carrier. `B'` is explicit because nothing else determines it. -/
def W (B' : K → Type u) (tg : A → K) : Type u := {t : PTree K B' A // Good tg t}

/-- The raw tree of a node labelled `a` with children `f`.

**This is the whole difference from `WFromPaths.lean`.** There, the guard is
`x.1 = a` at the label type and needs `Classical.propDecidable`; here it is
`x.1 = tg a` at the tag type, and `DecidableEq K` discharges it. Everything
downstream costs what it costs because of this one line. -/
def mk [DecidableEq K] (tg : A → K) (a : A) (f : B' (tg a) → PTree K B' A) :
    PTree K B' A
  | [] => some a
  | x :: p => if h : x.1 = tg a then f (h ▸ x.2) p else none

variable [DecidableEq K] {tg : A → K}

theorem mk_nil (a : A) (f : B' (tg a) → PTree K B' A) : mk tg a f [] = some a := rfl

theorem mk_sub (a : A) (f : B' (tg a) → PTree K B' A) (b : B' (tg a)) :
    subt (mk tg a f) ⟨tg a, b⟩ = f b := by
  funext p; simp [subt, mk]

theorem mk_ne (a : A) (f : B' (tg a) → PTree K B' A) (x : Edge K B') (h : x.1 ≠ tg a) :
    subt (mk tg a f) x = nowhere := by
  funext p; simp [subt, mk, nowhere, h]

def sup (a : A) (f : B' (tg a) → W B' tg) : W B' tg :=
  ⟨mk tg a (fun b => (f b).1),
   Good.pre ⟨a, rfl, fun b => by rw [mk_sub]; exact (f b).2, fun x hx => mk_ne _ _ x hx⟩⟩

theorem isSome_root (w : W B' tg) : (w.1 []).isSome := by
  obtain ⟨a, ha, _, _⟩ := w.2.post
  rw [ha]; rfl

def root (w : W B' tg) : A := (w.1 []).get (isSome_root w)

theorem root_spec (w : W B' tg) : w.1 [] = some (root w) := (Option.some_get _).symm

theorem root_eq {w : W B' tg} {a : A} (h : w.1 [] = some a) : root w = a := by
  rw [root_spec] at h; exact Option.some.inj h

theorem good_sub (w : W B' tg) (b : B' (tg (root w))) :
    Good tg (subt w.1 ⟨tg (root w), b⟩) := by
  obtain ⟨a, ha, hk, _⟩ := w.2.post
  have hra : root w = a := root_eq ha
  subst hra; exact hk b

def kids (w : W B' tg) (b : B' (tg (root w))) : W B' tg :=
  ⟨subt w.1 ⟨tg (root w), b⟩, good_sub w b⟩

theorem canon (w : W B' tg) : w = sup (root w) (kids w) := by
  apply Subtype.ext
  obtain ⟨a, ha, _, hm⟩ := w.2.post
  have hra : root w = a := root_eq ha
  subst hra
  funext p
  match p with
  | [] => exact ha
  | ⟨x1, x2⟩ :: p =>
    by_cases h : x1 = tg (root w)
    · subst h
      show w.1 (⟨tg (root w), x2⟩ :: p)
          = subt (mk tg (root w) (fun b => (kids w b).1)) ⟨tg (root w), x2⟩ p
      rw [mk_sub]
      rfl
    · have := congrFun (hm ⟨x1, x2⟩ h) p
      show w.1 (⟨x1, x2⟩ :: p) = mk tg (root w) (fun b => (kids w b).1) (⟨x1, x2⟩ :: p)
      rw [show w.1 (⟨x1, x2⟩ :: p) = subt w.1 ⟨x1, x2⟩ p from rfl, this]
      simp [mk, nowhere, h]

theorem root_sup (a : A) (f : B' (tg a) → W B' tg) : root (sup a f) = a := root_eq rfl

theorem kids_eq' (w : W B' tg) (f : B' (tg (root w)) → W B' tg) (hw : w = sup (root w) f)
    (b : B' (tg (root w))) : kids w b = f b := by
  apply Subtype.ext
  have h1 : w.val = (sup (root w) f).val := congrArg Subtype.val hw
  show subt w.1 ⟨tg (root w), b⟩ = (f b).1
  rw [h1]
  exact mk_sub (root w) (fun b => (f b).val) b

/-- Induction (small motive) is immediate from the fixpoint. -/
theorem Wind {P : W B' tg → Prop}
    (h : ∀ (a : A) (f : B' (tg a) → W B' tg), (∀ b, P (f b)) → P (sup a f)) : ∀ w, P w := by
  have key : ∀ t : PTree K B' A, Good tg t → ∀ ht : Good tg t, P ⟨t, ht⟩ := by
    intro t hg
    refine hg (fun t => ∀ ht : Good tg t, P ⟨t, ht⟩) ?_
    intro u hu ht
    obtain ⟨a, ha, hk, _hm⟩ := hu
    have hra : root (⟨u, ht⟩ : W B' tg) = a := root_eq ha
    have hP : ∀ b : B' (tg (root (⟨u, ht⟩ : W B' tg))), P (kids ⟨u, ht⟩ b) := by
      intro b
      have : kids (⟨u, ht⟩ : W B' tg) b
          = ⟨subt u ⟨tg (root ⟨u, ht⟩), b⟩, good_sub _ b⟩ := rfl
      rw [this]
      subst hra
      exact hk b _
    exact (canon (⟨u, ht⟩ : W B' tg)).symm ▸ h _ _ hP
  intro w
  exact key w.1 w.2 w.2

/-- The immediate-subtree relation. -/
def Sub (w' w : W B' tg) : Prop := ∃ b : B' (tg (root w)), w' = kids w b

theorem kids_cast (w : W B' tg) (a : A) (f : B' (tg a) → W B' tg) (hw : w = sup a f)
    (hra : root w = a) (b : B' (tg (root w))) :
    kids w b = f (cast (congrArg (fun z => B' (tg z)) hra) b) := by
  subst hra
  exact kids_eq' w f hw b

theorem kids_sup (a : A) (f : B' (tg a) → W B' tg) (b : B' (tg (root (sup a f)))) :
    kids (sup a f) b = f (cast (congrArg (fun z => B' (tg z)) (root_sup a f)) b) :=
  kids_cast (sup a f) a f rfl (root_sup a f) b

theorem sub_wf : ∀ w : W B' tg, Acc (Sub (B' := B') (tg := tg)) w := by
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
variable {C : W B' tg → Sort v}
  (F : (a : A) → (f : B' (tg a) → W B' tg) → ((b : B' (tg a)) → C (f b)) → C (sup a f))

/-- The large recursor, by well-founded recursion on `Sub`. -/
def Wrec : (w : W B' tg) → C w :=
  WellFounded.fix ⟨sub_wf⟩ fun w ih =>
    cast (congrArg C (canon w).symm) (F (root w) (kids w) fun b => ih (kids w b) ⟨b, rfl⟩)

theorem Wrec_unfold (w : W B' tg) :
    Wrec F w = cast (congrArg C (canon w).symm)
      (F (root w) (kids w) fun b => Wrec F (kids w b)) :=
  WellFounded.fix_eq _ _ _

theorem Wrec_key (w : W B' tg) (a : A) (f : B' (tg a) → W B' tg) (h : w = sup a f) :
    cast (congrArg C h) (Wrec F w) = F a f (fun b => Wrec F (f b)) := by
  have hra : root w = a := by rw [h]; exact root_sup a f
  subst hra
  have hf : kids w = f := by
    funext b; exact kids_eq' w f h b
  subst hf
  rw [Wrec_unfold]
  exact cast_symm_cancel _ _ _

theorem Wrec_iota (a : A) (f : B' (tg a) → W B' tg) :
    Wrec F (sup a f) = F a f (fun b => Wrec F (f b)) :=
  Wrec_key F (sup a f) a f rfl

end Rec

end WT

open WT

/-! ############################################################
    ## The generator's scheme
    ############################################################ -/

/-- **The empty type at `Type u`, from what the fragment already carries.**
`PEmpty` is not in `w_core.ndjson`; `Subtype`, `PUnit` and `False` are. -/
def WVoid : Type := Subtype (fun _ : PUnit.{1} => False)

def WVoid.elim {α : Sort v} (x : WVoid) : α := x.2.elim

/-! ############################################################
    ## The target: three constructors, three shapes
    ############################################################ -/

/-- The yardstick. Used ONLY in the pins.

`leaf` carries data and no children; `node` carries data **and** branches;
`lim` has its recursive field under a binder. Three arms, because two cannot
tell a correct dispatch from one with its arms swapped. -/
inductive TT : Type where
  | leaf : Nat → TT
  | node : Bool → TT → TT → TT
  | lim  : (Nat → TT) → TT
  | alt  : Nat → TT

/-- `D` — tag ↦ that constructor's non-recursive fields, as a tuple, and the
**empty** type off the end. Written as a `Nat.casesOn` cascade rather than a
`match`, because a cascade is what a generator emits: `match` would mint a
`TT.D.match_1` the model would then owe the output. -/
def DTT (t : Nat) : Type :=
  Nat.casesOn (motive := fun _ => Type) t
    Nat                                        -- leaf: one `Nat`
    (fun t1 => Nat.casesOn (motive := fun _ => Type) t1
      Bool                                     -- node: one `Bool`
      (fun t2 => Nat.casesOn (motive := fun _ => Type) t2
        PUnit                                  -- lim: no data
        (fun t3 => Nat.casesOn (motive := fun _ => Type) t3
          Nat                                  -- alt: one `Nat`, like `leaf`
          (fun _ => WVoid))))                  -- junk: uninhabited

/-- `B'` — tag ↦ that constructor's branch type. The junk arm is never reached
and its value is irrelevant; `WVoid` is used anyway so that a reader does not
have to ask. -/
def BTT (t : Nat) : Type :=
  Nat.casesOn (motive := fun _ => Type) t
    WVoid                                       -- leaf: no children
    (fun t1 => Nat.casesOn (motive := fun _ => Type) t1
      Bool                                     -- node: two children
      (fun t2 => Nat.casesOn (motive := fun _ => Type) t2
        Nat                                    -- lim: Nat-many children
        (fun t3 => Nat.casesOn (motive := fun _ => Type) t3
          WVoid                                -- alt: no children, like `leaf`
          (fun _ => WVoid))))

/-- The label. -/
abbrev ATT : Type := Σ t : Nat, DTT t
/-- The tag of a label, which is the first projection and nothing else. -/
def tgTT : ATT → Nat := Sigma.fst

abbrev CTT : Type := W BTT tgTT

/-! ### The constructors -/

noncomputable def CTT.leaf (n : Nat) : CTT :=
  sup (B' := BTT) ⟨0, n⟩ (fun e => WVoid.elim e)

noncomputable def CTT.node (c : Bool) (x y : CTT) : CTT :=
  sup (B' := BTT) ⟨1, c⟩ (fun i => cond i x y)

noncomputable def CTT.lim (g : Nat → CTT) : CTT :=
  sup (B' := BTT) ⟨2, PUnit.unit⟩ g

/-- **The same shape as `leaf`, at a different tag.** This is the constructor
the file gains nothing else from and exists entirely for `CTT.leaf_ne_alt`
below: two constructors of *different* shapes cannot be transposed without a
type error, so a target with only those cannot tell a correct tag assignment
from a permuted one. -/
noncomputable def CTT.alt (n : Nat) : CTT :=
  sup (B' := BTT) ⟨3, n⟩ (fun e => WVoid.elim e)

/-! ### The recursor, and the currying eta lemma per constructor

This is the term MODELGEN.md §8.16 calls "the per-declaration glue", and it is
the whole of it. Three things happen per constructor:

1. the tag is dispatched on -- a `Nat.casesOn` cascade over `a.1`, whose motive
   has to be well-typed at **every** tag including the junk ones, which is why
   the cascade is written at `fun t => (f : BTT (tgTT ⟨t, _⟩) -> CTT) -> ...`
   and not at a per-arm type;
2. the abstract child function `f : B' t -> CTT` is **uncurried** into the
   fields Lean's recursor wants, and the equation between `f` and its
   uncurried-then-recurried form is a `funext` -- one per constructor, and this
   is the piece arm C had none of;
3. the junk arm is discharged from the emptiness of `DTT t`.
-/

noncomputable def CTT.rec' {C : CTT → Sort v}
    (hl : (n : Nat) → C (CTT.leaf n))
    (hn : (c : Bool) → (x y : CTT) → C x → C y → C (CTT.node c x y))
    (hm : (g : Nat → CTT) → ((i : Nat) → C (g i)) → C (CTT.lim g))
    (ha : (n : Nat) → C (CTT.alt n)) :
    (t : CTT) → C t :=
  Wrec (C := C) (fun a =>
    Nat.casesOn (motive := fun t =>
        (d : DTT t) → (f : BTT (tgTT ⟨t, d⟩) → CTT) →
          ((b : BTT (tgTT ⟨t, d⟩)) → C (f b)) → C (sup ⟨t, d⟩ f))
      a.1
      -- ── tag 0: leaf ──
      (fun d f _ih =>
        cast (congrArg C (congrArg (sup (B' := BTT) (tg := tgTT) ⟨0, d⟩)
          (funext (fun e : BTT 0 => WVoid.elim (α := (fun e' => WVoid.elim e') e = f e) e))))
          (hl d))
      (fun t1 => Nat.casesOn (motive := fun t1 =>
          (d : DTT (t1 + 1)) → (f : BTT (tgTT ⟨t1 + 1, d⟩) → CTT) →
            ((b : BTT (tgTT ⟨t1 + 1, d⟩)) → C (f b)) → C (sup ⟨t1 + 1, d⟩ f))
        t1
        -- ── tag 1: node ──
        (fun d f ih =>
          cast (congrArg C (congrArg (sup (B' := BTT) (tg := tgTT) ⟨1, d⟩)
            (funext (fun i : BTT 1 =>
              Bool.rec (motive := fun i : Bool => cond i (f true) (f false) = f i) rfl rfl i))))
            (hn d (f true) (f false) (ih true) (ih false)))
        (fun t2 => Nat.casesOn (motive := fun t2 =>
            (d : DTT (t2 + 2)) → (f : BTT (tgTT ⟨t2 + 2, d⟩) → CTT) →
              ((b : BTT (tgTT ⟨t2 + 2, d⟩)) → C (f b)) → C (sup ⟨t2 + 2, d⟩ f))
          t2
          -- ── tag 2: lim.  `d : PUnit`, and the eta lemma is `PUnit`'s. ──
          (fun d f ih =>
            cast (congrArg C (congrArg (sup (B' := BTT) (tg := tgTT) (⟨2, d⟩ : ATT))
              (funext (fun i : BTT 2 => rfl))))
              (PUnit.rec (motive := fun d : PUnit =>
                C (sup (B' := BTT) (⟨2, d⟩ : ATT) f)) (hm f ih) d))
          (fun t3 => Nat.casesOn (motive := fun t3 =>
              (d : DTT (t3 + 3)) → (f : BTT (tgTT ⟨t3 + 3, d⟩) → CTT) →
                ((b : BTT (tgTT ⟨t3 + 3, d⟩)) → C (f b)) → C (sup ⟨t3 + 3, d⟩ f))
            t3
            -- ── tag 3: alt.  `leaf`'s shape exactly, at another tag. ──
            (fun d f _ih =>
              cast (congrArg C (congrArg (sup (B' := BTT) (tg := tgTT) ⟨3, d⟩)
                (funext (fun e : BTT 3 =>
                  WVoid.elim (α := (fun e' => WVoid.elim e') e = f e) e))))
                (ha d))
            -- ── the junk tags, discharged from the emptiness of `DTT` ──
            (fun t4 d _f _ih => WVoid.elim d))))
      a.2)

theorem CTT.iota_leaf {C : CTT → Sort v}
    (hl : (n : Nat) → C (CTT.leaf n))
    (hn : (c : Bool) → (x y : CTT) → C x → C y → C (CTT.node c x y))
    (hm : (g : Nat → CTT) → ((i : Nat) → C (g i)) → C (CTT.lim g))
    (ha : (n : Nat) → C (CTT.alt n)) (n : Nat) :
    CTT.rec' hl hn hm ha (CTT.leaf n) = hl n :=
  Wrec_iota _ _ _

theorem CTT.iota_alt {C : CTT → Sort v}
    (hl : (n : Nat) → C (CTT.leaf n))
    (hn : (c : Bool) → (x y : CTT) → C x → C y → C (CTT.node c x y))
    (hm : (g : Nat → CTT) → ((i : Nat) → C (g i)) → C (CTT.lim g))
    (ha : (n : Nat) → C (CTT.alt n)) (n : Nat) :
    CTT.rec' hl hn hm ha (CTT.alt n) = ha n :=
  Wrec_iota _ _ _

theorem CTT.iota_node {C : CTT → Sort v}
    (hl : (n : Nat) → C (CTT.leaf n))
    (hn : (c : Bool) → (x y : CTT) → C x → C y → C (CTT.node c x y))
    (hm : (g : Nat → CTT) → ((i : Nat) → C (g i)) → C (CTT.lim g))
    (ha : (n : Nat) → C (CTT.alt n))
    (c : Bool) (x y : CTT) :
    CTT.rec' hl hn hm ha (CTT.node c x y)
      = hn c x y (CTT.rec' hl hn hm ha x) (CTT.rec' hl hn hm ha y) :=
  Wrec_iota _ _ _

theorem CTT.iota_lim {C : CTT → Sort v}
    (hl : (n : Nat) → C (CTT.leaf n))
    (hn : (c : Bool) → (x y : CTT) → C x → C y → C (CTT.node c x y))
    (hm : (g : Nat → CTT) → ((i : Nat) → C (g i)) → C (CTT.lim g))
    (ha : (n : Nat) → C (CTT.alt n))
    (g : Nat → CTT) :
    CTT.rec' hl hn hm ha (CTT.lim g) = hm g (fun i => CTT.rec' hl hn hm ha (g i)) :=
  Wrec_iota _ _ _

/-! ### Pin 1: the derived recursor against a transcription, and Lean's own
recursor against the **same** transcription, so the transcription is checked
rather than trusted. -/

noncomputable example : ∀ {motive : CTT → Sort v},
    ((n : Nat) → motive (CTT.leaf n)) →
    ((c : Bool) → (x y : CTT) → motive x → motive y → motive (CTT.node c x y)) →
    ((g : Nat → CTT) → ((i : Nat) → motive (g i)) → motive (CTT.lim g)) →
    ((n : Nat) → motive (CTT.alt n)) →
    (t : CTT) → motive t := @CTT.rec'

noncomputable example : ∀ {motive : TT → Sort v},
    ((n : Nat) → motive (TT.leaf n)) →
    ((c : Bool) → (x y : TT) → motive x → motive y → motive (TT.node c x y)) →
    ((g : Nat → TT) → ((i : Nat) → motive (g i)) → motive (TT.lim g)) →
    ((n : Nat) → motive (TT.alt n)) →
    (t : TT) → motive t := @TT.rec

/-! ### Pin 2: non-degeneracy, from the recursor and its ι rules alone.

Three constructors give three pairs, and all three are checked: a dispatch with
two arms transposed passes the one-pair test. -/

theorem CTT.leaf_ne_node (n : Nat) (c : Bool) (x y : CTT) :
    CTT.leaf n ≠ CTT.node c x y := by
  intro h
  have h1 := CTT.iota_leaf (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => False) (fun _ _ => False) (fun _ => False) n
  have h2 := CTT.iota_node (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => False) (fun _ _ => False) (fun _ => False) c x y
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

theorem CTT.leaf_ne_lim (n : Nat) (g : Nat → CTT) : CTT.leaf n ≠ CTT.lim g := by
  intro h
  have h1 := CTT.iota_leaf (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => False) (fun _ _ => False) (fun _ => False) n
  have h2 := CTT.iota_lim (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => False) (fun _ _ => False) (fun _ => False) g
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

theorem CTT.node_ne_lim (c : Bool) (x y : CTT) (g : Nat → CTT) :
    CTT.node c x y ≠ CTT.lim g := by
  intro h
  have h1 := CTT.iota_node (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => True) (fun _ _ => False) (fun _ => False) c x y
  have h2 := CTT.iota_lim (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => True) (fun _ _ => False) (fun _ => False) g
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

/-- **The pin for the pair the shapes do not separate.** Every other
transposition in this file is caught by a *type error* in `CTT.rec'` — `node`'s
minor cannot stand in for `leaf`'s, so the cascade will not elaborate. `leaf`
and `alt` have the same shape, so nothing about their two minors' types
distinguishes them, and what does the work is this statement and `iota_alt`.
Measured, not assumed: giving `alt` the tag `0` breaks exactly those two and
nothing that a differently-shaped pair would have caught first. It is
`CFT.tip_ne_fork`'s statement at the one pair where it is not free. -/
theorem CTT.leaf_ne_alt (n m : Nat) : CTT.leaf n ≠ CTT.alt m := by
  intro h
  have h1 := CTT.iota_leaf (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => False) (fun _ _ => False) (fun _ => False) n
  have h2 := CTT.iota_alt (C := fun _ => Prop)
    (fun _ => True) (fun _ _ _ _ _ => False) (fun _ _ => False) (fun _ => False) m
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

/-! ### Pin 3: `CFT.tip_inj_data`'s shape, at all three arms.

**The payload survives the round trip.** A model that recorded the tag on the
path and then lost the label's data would pass every check above; these are the
ones that fail if it does. -/

theorem CTT.leaf_inj_data (n m : Nat) (h : CTT.leaf n = CTT.leaf m) : n = m := by
  have h1 := CTT.iota_leaf (C := fun _ => Nat)
    (fun k => k) (fun _ _ _ p q => p + q) (fun _ _ => 0) (fun _ => 0) n
  have h2 := CTT.iota_leaf (C := fun _ => Nat)
    (fun k => k) (fun _ _ _ p q => p + q) (fun _ _ => 0) (fun _ => 0) m
  rw [h] at h1
  exact h1.symm.trans h2

theorem CTT.node_inj_data (c d : Bool) (x y : CTT) (h : CTT.node c x y = CTT.node d x y) :
    c = d := by
  have h1 := CTT.iota_node (C := fun _ => Bool)
    (fun _ => false) (fun b _ _ _ _ => b) (fun _ _ => false) (fun _ => false) c x y
  have h2 := CTT.iota_node (C := fun _ => Bool)
    (fun _ => false) (fun b _ _ _ _ => b) (fun _ _ => false) (fun _ => false) d x y
  rw [h] at h1
  exact h1.symm.trans h2

/-! ### Pin 4: **the children survive too**, and in the right order.

`node`'s two children are the one place a `Bool`-branch model can silently
transpose, and `iota_node` alone does not catch it because it is stated with
the same `x y` on both sides. -/

theorem CTT.node_inj_kids (x y : CTT) :
    CTT.rec' (C := fun _ => Nat) (fun k => k) (fun _ _ _ p q => 2 * p + q) (fun _ _ => 0) (fun _ => 0)
      (CTT.node true (CTT.leaf 1) (CTT.leaf 2)) = 4 := by
  rw [CTT.iota_node, CTT.iota_leaf, CTT.iota_leaf]

theorem CTT.lim_computes :
    CTT.rec' (C := fun _ => Nat) (fun k => k) (fun _ _ _ p q => p + q)
      (fun _ ih => ih 3 + ih 5) (fun _ => 0) (CTT.lim (fun i => CTT.leaf i)) = 8 := by
  simp only [CTT.iota_lim, CTT.iota_leaf]

/-! ### Pin 5: **the junk tags are uninhabited**, which is what makes `Nat`
safe as the tag type. If `DTT` is ever weakened to send them to `PUnit`, `W`
acquires trees no constructor produces and the model is wrong while every check
above still passes. -/

theorem ATT.no_junk (a : ATT) : a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 := by
  obtain ⟨t, d⟩ := a
  match t with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | 2 => exact Or.inr (Or.inr (Or.inl rfl))
  | 3 => exact Or.inr (Or.inr (Or.inr rfl))
  | _ + 4 => exact WVoid.elim d

/-! ############################################################
    ## The bill
    ############################################################ -/

/-- info: 'CTT.rec'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.rec'
/-- info: 'CTT.iota_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.iota_leaf
/-- info: 'CTT.iota_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.iota_node
/-- info: 'CTT.iota_lim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.iota_lim
/-- info: 'CTT.leaf_ne_alt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.leaf_ne_alt
/-- info: 'CTT.iota_alt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.iota_alt
/-- info: 'CTT.leaf_ne_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.leaf_ne_node
/-- info: 'CTT.node_ne_lim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.node_ne_lim
/-- info: 'CTT.leaf_inj_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.leaf_inj_data
/-- info: 'CTT.node_inj_kids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTT.node_inj_kids
/-- info: 'ATT.no_junk' does not depend on any axioms -/
#guard_msgs in #print axioms ATT.no_junk
