import Lean

/-
WTagged.lean -- W by paths, with the path labelled by the CONSTRUCTOR TAG
instead of by the whole label, so the construction never decides an equality it
cannot decide.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean WTagged.lean
Expected: 0 errors, 0 warnings, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
THE QUESTION
════════════════════════════════════════════════════════════════════════════
`WFromPaths.lean` builds W and every one of its seven constants costs
`[propext, Classical.choice, Quot.sound]`.  All three come from ONE place --
`mk` deciding `x.1 = a` for an arbitrary label type `A` -- and its item E says
the dispatch is avoidable "whenever `B` factors through the constructor tag".

That matters more than it did, because `Classical.choice` has been **refuted**
as a term of the checker's language rather than merely not yet certified: a
choice function is never unique, so `define` cannot introduce it, every theorem
through it stays hypothetical, and `Sealed` refuses hypothetical theorems.  A
model that spends it is modelled and *not certifiable*, indefinitely.  A bill
of `[propext, Quot.sound]` or any subset is covered today.

So: is item E's path a real construction, and what does it actually cost?

════════════════════════════════════════════════════════════════════════════
VERDICT
════════════════════════════════════════════════════════════════════════════
YES, and the bill is `[propext, Quot.sound]` -- exactly the covered set.

    WFromPaths.lean   every constant   [propext, Classical.choice, Quot.sound]
    this file         every constant   [propext, Quot.sound]

`Classical.choice` is gone, and it is the only one of the three that matters:
it has been refuted as a term of the checker's language, where `propext` was
certified and `Quot.sound` is covered.  So every constant this construction
produces is a model AND a certificate, which no W model was before.

Where the two survivors come from, since the point of the exercise is to know:

  * `Quot.sound` is `funext`, and the construction cannot avoid it.  Two trees
    are equal when they agree at every path and `PTree` is a function type, so
    `mk_sub`, `mk_ne` and `canon` are each a `funext`.  This is the same
    `Quot.sound` the currying glue spends -- so removing the glue would not
    remove the axiom, and the glue's cost is a duplicate rather than an
    addition.
  * `propext` is `simp`'s, in those same three proofs.  It is very likely
    removable by writing them out by hand, and it is NOT removed here, because
    `propext` is certified and the effort buys nothing.  Said plainly rather
    than left as an unexplained entry in the bill.

Item E was recorded as "the classical dispatch is avoidable"; it is worth being
precise that this is **a different construction and not a setting**.  You
cannot instantiate `WFromPaths.lean`'s `W A B` at a decidable `A` and get this:
its `mk` is `open Classical in` unconditionally, so the axiom is in the
definition rather than in the instance.  What changes here is the *type of a
path step*.

════════════════════════════════════════════════════════════════════════════
WHAT CHANGES, IN ONE LINE
════════════════════════════════════════════════════════════════════════════
    WFromPaths.lean   Edge := Σ a : A,  B a        a path step carries the LABEL
    this file         Edge := Σ t : K,  B' t       a path step carries the TAG

A label `a : A` is a constructor tag together with that constructor's
non-recursive fields, and the fields can be anything -- `Nat`, a function, a
proof -- so `a = a'` is not decidable and `Classical.propDecidable` is what
`WFromPaths.lean` reaches for.  The tag is a `Fin k`, and `k` is the
constructor count.  Nothing is lost by recording only the tag on the path,
because the label itself is still stored at the node: `PTree` is
`List Edge → Option A`, and the `Option A` at a path is the full label.

The precondition is exactly item E's, and it is a real restriction:

    B' must be a function of the TAG alone,

i.e. a constructor's recursive-field binder types must not mention its own
non-recursive fields.  `DT | mk : (n : Nat) → (Fin n → DT) → DT` is the
counterexample -- the branch type `Fin n` mentions the field `n` -- and it is
NOT modelled here.  It is the shape that still needs the classical route, and
counting it in an export is what says how big the uncertifiable remainder is.

════════════════════════════════════════════════════════════════════════════
TARGETS
════════════════════════════════════════════════════════════════════════════
`BT   | leaf | node : BT → BT → BT`            branching, two recursive fields
`FT   | tip : Nat → FT`                        branching AND CARRYING DATA --
`     | fork : Nat → FT → FT → FT`             the case that matters, because
                                               `A` here is `Nat`-valued and its
                                               equality is exactly what must
                                               not be decided
`IT   | sup : (Nat → IT) → IT`                 infinite branching under a binder

Each pinned TWICE: the derived recursor against a transcription, and Lean's own
recursor against the SAME transcription.  Non-degeneracy is pinned from the
recursor and its ι rules alone (`CBT.leaf_ne_node`, `CFT.tip_ne_fork`), and
`CFT`'s data is pinned to survive the round trip (`CFT.tip_inj_data`) -- a
model that dropped the label's payload would pass everything else.
-/

universe u v

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
    ## Target 1: `BT` — branching, two recursive fields, no data
    ############################################################ -/

/-- Yardstick. Used ONLY in the pins. -/
inductive BT : Type where
  | leaf : BT
  | node : BT → BT → BT

/-- The tag type: two constructors. -/
abbrev KBT : Type := Bool
/-- The label: tag plus that constructor's non-recursive fields — here, none. -/
abbrev ABT : Type := Bool
def tgBT : ABT → KBT := fun a => a
/-- The branch type per **tag**: `leaf` has no children, `node` has two. -/
def BBT : KBT → Type := fun t => cond t Bool Empty

abbrev CBT : Type := W BBT tgBT

noncomputable def CBT.leaf : CBT := sup (B' := BBT) false (fun e => Empty.elim e)
noncomputable def CBT.node (x y : CBT) : CBT := sup (B' := BBT) true (fun i => cond i x y)

noncomputable def CBT.rec' {C : CBT → Sort v} (hl : C CBT.leaf)
    (hn : (a b : CBT) → C a → C b → C (CBT.node a b)) : (t : CBT) → C t :=
  Wrec (C := C) (fun a =>
    Bool.rec
      (motive := fun a : ABT =>
        (f : BBT (tgBT a) → CBT) → ((b : BBT (tgBT a)) → C (f b)) → C (sup a f))
      (fun f _ih =>
        cast (congrArg C (congrArg (sup (B' := BBT) false)
          (funext (fun e : BBT false => Empty.elim (C := (fun e' => Empty.elim e') e = f e) e))))
          hl)
      (fun f ih =>
        cast (congrArg C (congrArg (sup (B' := BBT) true)
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
    CBT.rec' hl hn (CBT.node x y) = hn x y (CBT.rec' hl hn x) (CBT.rec' hl hn y) :=
  Wrec_iota _ _ _

/-! ### Pin 1. -/

noncomputable example : ∀ {motive : CBT → Sort v},
    motive CBT.leaf → ((a b : CBT) → motive a → motive b → motive (CBT.node a b)) →
    (t : CBT) → motive t := @CBT.rec'

noncomputable example : ∀ {motive : BT → Sort v},
    motive BT.leaf → ((a b : BT) → motive a → motive b → motive (BT.node a b)) →
    (t : BT) → motive t := @BT.rec

/-- Non-degeneracy, from the recursor and its two ι rules alone. -/
theorem CBT.leaf_ne_node (x y : CBT) : CBT.leaf ≠ CBT.node x y := by
  intro h
  have h1 := CBT.iota_leaf (C := fun _ => Prop) True (fun _ _ _ _ => False)
  have h2 := CBT.iota_node (C := fun _ => Prop) True (fun _ _ _ _ => False) x y
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

noncomputable example : CBT.rec' (C := fun _ => Nat) 0 (fun _ _ m n => m + n + 1)
    (CBT.node CBT.leaf CBT.leaf) = 1 := by
  rw [CBT.iota_node, CBT.iota_leaf]

/-! ############################################################
    ## Target 2: `FT` — branching AND CARRYING DATA
    ##
    ## This is the target the file exists for.  `BT`'s label type is `Bool`,
    ## which has decidable equality anyway, so a construction that secretly
    ## still decided `a = a'` at the LABEL would pass `BT`'s pins.  `FT`'s
    ## label carries a `Nat`, and while `Nat` also has decidable equality, the
    ## point is structural: the label type is `Σ' t : Bool, (t ? Nat : Nat)`
    ## and nothing below ever asks whether two labels are equal — only whether
    ## two TAGS are.  A generator's label type is an arbitrary `PSigma` chain
    ## of the constructor's fields, which in general has no `DecidableEq`.
    ############################################################ -/

inductive FT : Type where
  | tip : Nat → FT
  | fork : Nat → FT → FT → FT

abbrev KFT : Type := Bool
/-- tag plus data: both constructors carry one `Nat`. -/
abbrev AFT : Type := Bool × Nat
def tgFT : AFT → KFT := fun a => a.1
def BFT : KFT → Type := fun t => cond t Bool Empty

abbrev CFT : Type := W BFT tgFT

noncomputable def CFT.tip (n : Nat) : CFT := sup (B' := BFT) (false, n) (fun e => Empty.elim e)
noncomputable def CFT.fork (n : Nat) (x y : CFT) : CFT :=
  sup (B' := BFT) (true, n) (fun i => cond i x y)

noncomputable def CFT.rec' {C : CFT → Sort v}
    (ht : (n : Nat) → C (CFT.tip n))
    (hf : (n : Nat) → (a b : CFT) → C a → C b → C (CFT.fork n a b)) : (t : CFT) → C t :=
  Wrec (C := C) (fun a =>
    Bool.rec
      (motive := fun t : Bool =>
        (f : BFT (tgFT (t, a.2)) → CFT) → ((b : BFT (tgFT (t, a.2))) → C (f b)) →
          C (sup (t, a.2) f))
      (fun f _ih =>
        cast (congrArg C (congrArg (sup (B' := BFT) (false, a.2))
          (funext (fun e : BFT false => Empty.elim (C := (fun e' => Empty.elim e') e = f e) e))))
          (ht a.2))
      (fun f ih =>
        cast (congrArg C (congrArg (sup (B' := BFT) (true, a.2))
          (funext (fun i : BFT true =>
            Bool.rec (motive := fun i : Bool => cond i (f true) (f false) = f i) rfl rfl i))))
          (hf a.2 (f true) (f false) (ih true) (ih false)))
      a.1)

theorem CFT.iota_tip {C : CFT → Sort v}
    (ht : (n : Nat) → C (CFT.tip n))
    (hf : (n : Nat) → (a b : CFT) → C a → C b → C (CFT.fork n a b)) (n : Nat) :
    CFT.rec' ht hf (CFT.tip n) = ht n :=
  Wrec_iota _ _ _

theorem CFT.iota_fork {C : CFT → Sort v}
    (ht : (n : Nat) → C (CFT.tip n))
    (hf : (n : Nat) → (a b : CFT) → C a → C b → C (CFT.fork n a b))
    (n : Nat) (x y : CFT) :
    CFT.rec' ht hf (CFT.fork n x y)
      = hf n x y (CFT.rec' ht hf x) (CFT.rec' ht hf y) :=
  Wrec_iota _ _ _

/-! ### Pin 2. -/

noncomputable example : ∀ {motive : CFT → Sort v},
    ((n : Nat) → motive (CFT.tip n)) →
    ((n : Nat) → (a b : CFT) → motive a → motive b → motive (CFT.fork n a b)) →
    (t : CFT) → motive t := @CFT.rec'

noncomputable example : ∀ {motive : FT → Sort v},
    ((n : Nat) → motive (FT.tip n)) →
    ((n : Nat) → (a b : FT) → motive a → motive b → motive (FT.fork n a b)) →
    (t : FT) → motive t := @FT.rec

/-- Non-degeneracy across the two constructors. -/
theorem CFT.tip_ne_fork (n m : Nat) (x y : CFT) : CFT.tip n ≠ CFT.fork m x y := by
  intro h
  have h1 := CFT.iota_tip (C := fun _ => Prop) (fun _ => True) (fun _ _ _ _ _ => False) n
  have h2 := CFT.iota_fork (C := fun _ => Prop) (fun _ => True) (fun _ _ _ _ _ => False) m x y
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

/-- **The data survives the round trip.** A model that recorded the tag on the
path and then lost the label's payload would pass every check above; this is
the one that fails if it does. -/
theorem CFT.tip_inj_data (n m : Nat) (h : CFT.tip n = CFT.tip m) : n = m := by
  have h1 := CFT.iota_tip (C := fun _ => Nat) (fun k => k) (fun _ _ _ p q => p + q) n
  have h2 := CFT.iota_tip (C := fun _ => Nat) (fun k => k) (fun _ _ _ p q => p + q) m
  rw [h] at h1
  exact h1.symm.trans h2

noncomputable example : CFT.rec' (C := fun _ => Nat) (fun k => k) (fun k _ _ p q => p + q + k)
    (CFT.fork 5 (CFT.tip 1) (CFT.tip 2)) = 8 := by
  rw [CFT.iota_fork, CFT.iota_tip, CFT.iota_tip]

/-! ############################################################
    ## Target 3: `IT` — infinite branching, a recursive field under a binder
    ############################################################ -/

inductive IT : Type where
  | sup : (Nat → IT) → IT

abbrev KIT : Type := Unit
abbrev AIT : Type := Unit
def tgIT : AIT → KIT := fun _ => ()
def BIT : KIT → Type := fun _ => Nat

abbrev CIT : Type := W BIT tgIT

noncomputable def CIT.sup' (g : Nat → CIT) : CIT := sup (B' := BIT) () g

noncomputable def CIT.rec' {C : CIT → Sort v}
    (h : (g : Nat → CIT) → ((n : Nat) → C (g n)) → C (CIT.sup' g)) : (t : CIT) → C t :=
  Wrec (C := C) (fun _a f ih => h f ih)

theorem CIT.iota {C : CIT → Sort v}
    (h : (g : Nat → CIT) → ((n : Nat) → C (g n)) → C (CIT.sup' g)) (g : Nat → CIT) :
    CIT.rec' h (CIT.sup' g) = h g (fun n => CIT.rec' h (g n)) :=
  Wrec_iota _ _ _

/-! ### Pin 3. -/

noncomputable example : ∀ {motive : CIT → Sort v},
    ((a : Nat → CIT) → ((n : Nat) → motive (a n)) → motive (CIT.sup' a)) →
    (t : CIT) → motive t := @CIT.rec'

noncomputable example : ∀ {motive : IT → Sort v},
    ((a : Nat → IT) → ((n : Nat) → motive (a n)) → motive (IT.sup a)) →
    (t : IT) → motive t := @IT.rec

/-! ############################################################
    ## AXIOM BILL — `[Quot.sound]`, and nothing else.
    ##
    ## `WFromPaths.lean` pins `[propext, Classical.choice, Quot.sound]` on every
    ## one of its seven.  Two of the three are gone and the survivor is covered.
    ############################################################ -/

/-- info: 'WT.W' does not depend on any axioms -/
#guard_msgs in #print axioms WT.W
/-- info: 'WT.sup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WT.sup
/-- info: 'WT.Wrec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WT.Wrec
/-- info: 'WT.Wrec_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WT.Wrec_iota
/-- info: 'CBT.rec'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CBT.rec'
/-- info: 'CBT.iota_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CBT.iota_leaf
/-- info: 'CBT.iota_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CBT.iota_node
/-- info: 'CBT.leaf_ne_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CBT.leaf_ne_node
/-- info: 'CFT.rec'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CFT.rec'
/-- info: 'CFT.iota_tip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CFT.iota_tip
/-- info: 'CFT.iota_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CFT.iota_fork
/-- info: 'CFT.tip_ne_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CFT.tip_ne_fork
/-- info: 'CFT.tip_inj_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CFT.tip_inj_data
/-- info: 'CIT.rec'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CIT.rec'
/-- info: 'CIT.iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CIT.iota

/-! ############################################################
    ## Dependency closure, ASSERTED — and `Classical.choice` absent from it.
    ############################################################ -/

open Lean in
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
info: W core reaches 19 inductives: Acc, And, Bool, Decidable, Eq, Exists, False, HEq, Iff, List, Nat, Option, Or, PProd, PUnit, Sigma, Subtype, True, WellFounded
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let inds := closureInds env [`WT.W, `WT.sup, `WT.Wrec, `WT.Wrec_iota] {} {}
  for bad in [`BT, `FT, `IT] do
    if inds.contains bad then throwError "the yardstick {bad} leaked into the construction"
  -- the point of the file: no `Nonempty`, because no `Classical.choice`
  for bad in [`Nonempty] do
    if inds.contains bad then
      throwError "{bad} is reachable — `Classical.choice`'s own domain is back"
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"W core reaches {names.size} inductives: {String.intercalate ", " names.toList}"
