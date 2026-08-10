/-
CarveOverSkeleton.lean -- the indexed carve ("skeleton plus `good`", thesis §5.2)
built over a **spliced index-erased inductive** rather than over a W-type, in
the four primitives the `--prim-models` basis actually has.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean CarveOverSkeleton.lean
Expected: 0 errors, 0 warnings, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
WHAT THIS ASKS, AND WHY IT IS A DIFFERENT QUESTION FROM `WIndexedCarve.lean`
════════════════════════════════════════════════════════════════════════════
`WIndexedCarve.lean` carves an indexed family out of `WCon.W A B`, and answers
"does the carve subsume the non-indexed case" with yes.  It leaves the carve
*standing on W*, and therefore inherits everything W costs: 22 modelled
inductives in front of it, three axioms, a propositional ι, and -- the piece
its own verdict names as the place a generator breaks first -- a per-
constructor **currying glue**, because `W` hands you `(f : B a → W) → …` where
Lean's recursor wants the constructor's fields uncurried.

`MODELGEN.md` §8.10 says to model in dependency order and then use the **real**
type, with its definitional ι, rather than routing a later construction through
a derived interface.  Applied here that says something the W framing hides:

  the thing the carve needs underneath it is a **non-indexed inductive with the
  same constructor telescopes**, and that is a declaration we can SPLICE.

`modelgen` can already splice an inductive and then model it -- that is
`MODELGEN.md` §8.13's splice-and-model, landed for exactly this shape of need.
So the skeleton need not be built out of W at all.  It is emitted as an
ordinary `inductive`, Lean's kernel mints its recursor, and the carve is
written against that.

════════════════════════════════════════════════════════════════════════════
VERDICT
════════════════════════════════════════════════════════════════════════════
It works, and it is strictly cheaper than the carve over W on four axes that
are each independently checked below.

  1. NO CURRYING GLUE, AT ALL.  A spliced skeleton keeps the constructor's
     field telescope, so the minor premise `STri.rec` wants and the minor
     premise `Tri.rec` wants are the same telescope.  There is no `B a ≅ Fin k`
     iso, no eta lemma, no `funext`, and nothing emitted per constructor beyond
     the constructor itself.  This retires the one item `WFromPaths.lean` and
     `WIndexedCarve.lean` both name as the place a generator first breaks.

  2. ι IS `rfl`.  Pinned below with `Eq.refl` as the literal proof for all
     six ι rules across three targets.  The carve over W cannot do this --
     `Wrec` goes through `WellFounded.fix`, so its ι is propositional and
     `modelgen/README.md`'s "an ι theorem does not promise `Eq.refl`" carve-out
     would have had to widen from the graph arm to the whole indexed cluster.
     Three Lean features carry it: definitional proof irrelevance (the `good`
     component never obstructs an equality, so `⟨s, h⟩ ≡ ⟨s, h'⟩`), ι for the
     skeleton's own recursor (which a *real* inductive has and a model does
     not), and structure eta for `PSigma` (so `⟨t.1, t.2⟩ ≡ t`).

  3. NO AXIOMS.  `#print axioms` is empty for all 22 derived constants.  The
     carve over W costs `[propext, Classical.choice, Quot.sound]` on every one
     of its 24, from `sup` deciding `x.1 = a`; there is no such decision here.

  4. THE BASIS IS UNCHANGED.  Everything below is `Eq`, `PSigma` and the
     spliced skeleton.  No `List`, no `Option`, no `Sigma`, no `Subtype`, no
     `Acc`, no `WellFounded`, no `Decidable`, no `Nonempty` -- i.e. none of
     `WFromPaths.lean` §8.11's 22-inductive dependency list.  Conjunction is
     Church (`AndC` below), which is what `Modelgen.andCOf` already emits.
     Asserted, not just reported, by the closure walk at the end.

════════════════════════════════════════════════════════════════════════════
WHAT IT COSTS INSTEAD, STATED HONESTLY
════════════════════════════════════════════════════════════════════════════
One spliced inductive per modelled indexed family, which splice-and-model must
then model.  So the arm's reach is
    { indexed families whose index erasure the existing routes model }
and an indexed family whose erasure is *branching* still waits for W -- the
erasure of `Lean.Expr`'s aux is still `Lean.Expr`-shaped.  This does not make
the arm smaller than the carve-over-W arm; it makes the dependency explicit and
separable.  Under the W framing the same declarations were blocked too, just
invisibly, because W was underneath everything.

And the contract obligation is real: a spliced-but-unmodelled skeleton would
put a fifth inductive in front of a consumer.  The rule that keeps
`modelgen/README.md` honest is therefore **decline the family when its skeleton
does not model** -- an emission is not allowed to leave an unmodelled inductive
behind.  That is a decline, never an emission, in §8.10's sense.

════════════════════════════════════════════════════════════════════════════
THE THREE TARGETS, AND WHY EACH IS HERE
════════════════════════════════════════════════════════════════════════════
`Tri   : Nat → Type`       indexed, branching, two constructors, and a
                           constructor whose two recursive fields sit at
                           DIFFERENT indices.
`Two   : Nat → Type`       TWO CONSTRUCTORS AT THE SAME INDEX.  `Tri`'s are
                           separated by their index (0 vs m+n+1), so a broken
                           model could pass `Tri`'s pins; `Two.l n` and
                           `Two.r n _ _` both live at `n`, and `CTwo.l_ne_r`
                           derives their disjointness from the recursor and its
                           two ι rules ALONE.  (`WIndexedCarve.lean` added this
                           target for the same reason and it is kept.)
`Bal   : Nat → Nat → Type` an index TELESCOPE of length two, packed into one
                           `PSigma`, which is what `Modelgen.packTyOf` already
                           builds for arm F.

Each target is pinned TWICE: the derived recursor against a transcription, and
Lean's own recursor against the SAME transcription, so the transcription is
measured against Lean rather than trusted.
-/

import Lean

universe u v w

/-! ############################################################
    ## The basis: `Eq`, `PSigma`, and Church conjunction
    ##
    ## `Nat` and `PULiftP` are the other two basis primitives and are not
    ## needed by the carve itself; `Nat` appears below only because the
    ## targets' indices happen to be naturals.
    ############################################################ -/

/-- Church conjunction, which is what `Modelgen.andCOf` emits: impredicative,
`Prop`-valued, and its two projections are instantiations rather than
eliminations, so nothing here consumes a large eliminator. -/
def AndC (A B : Prop) : Prop := ∀ D : Prop, (A → B → D) → D

def AndC.mk {A B : Prop} (a : A) (b : B) : AndC A B := fun _ k => k a b
def AndC.left {A B : Prop} (p : AndC A B) : A := p A (fun a _ => a)
def AndC.right {A B : Prop} (p : AndC A B) : B := p B (fun _ b => b)

/-- Both projections reduce on a literal pair -- by β alone, no ι, no
irrelevance.  This is what makes the ι rules below `rfl`. -/
example {A B : Prop} (a : A) (b : B) : AndC.left (AndC.mk a b) = a := rfl
example {A B : Prop} (a : A) (b : B) : AndC.right (AndC.mk a b) = b := rfl

/-! ############################################################
    ## Target 1: `Tri` -- indexed, branching, children at different indices
    ############################################################ -/

/-- The yardstick.  Used ONLY in the pins. -/
inductive Tri : Nat → Type where
  | leaf : Tri 0
  | node : (m n : Nat) → Tri m → Tri n → Tri (m + n + 1)

/-- **The spliced skeleton**: `Tri` with its indices erased.  Each constructor
keeps its field telescope exactly; only the recursive fields' `Tri e` become
`STri`, and the result type `Tri e` becomes `STri`.  This is the declaration
`modelgen` would splice, and the kernel mints `STri.rec` for it. -/
inductive STri : Type where
  | sleaf : STri
  | snode : (m n : Nat) → STri → STri → STri

/-- `good s x` : the skeleton `s` is a well-indexed tree at index `x`.  One
`STri.rec` into `Nat → Prop`; the conjunction is Church and the index
equations are `Eq`. -/
def goodTri : STri → Nat → Prop :=
  STri.rec (motive := fun _ => Nat → Prop)
    (fun x => 0 = x)
    (fun m n _a _b iha ihb x => AndC (m + n + 1 = x) (AndC (iha m) (ihb n)))

/-- The skeleton's own ι is definitional, so `good`'s unfolding is `rfl` --
this is the step the carve over W has to buy with `WellFounded.fix_eq`. -/
example : goodTri .sleaf = fun x => 0 = x := rfl
example (m n : Nat) (a b : STri) :
    goodTri (.snode m n a b) = fun x => AndC (m + n + 1 = x) (AndC (goodTri a m) (goodTri b n)) :=
  rfl

/-- The carrier: a `PSigma` over the skeleton, carved by `good`.  `PSigma` and
not `Subtype` because `PSigma` is the basis's Σ and reaches `Sort`. -/
def CTri (x : Nat) : Type := PSigma (fun s : STri => goodTri s x)

def CTri.leaf : CTri 0 := ⟨.sleaf, rfl⟩

def CTri.node (m n : Nat) (a : CTri m) (b : CTri n) : CTri (m + n + 1) :=
  ⟨.snode m n a.1 b.1, AndC.mk rfl (AndC.mk a.2 b.2)⟩

/-- The recursor.  **No glue**: `STri.rec`'s minor for `snode` already binds
`(m n : Nat) (a b : STri)` uncurried, which is the telescope `Tri.rec`'s minor
binds.  The whole of the per-constructor work is packaging each recursive field
back into a `PSigma` and transporting the conclusion along the index equation
the `good` proof carries. -/
noncomputable def CTri.rec' {C : (x : Nat) → CTri x → Sort v}
    (hl : C 0 CTri.leaf)
    (hn : (m n : Nat) → (a : CTri m) → (b : CTri n) → C m a → C n b →
            C (m + n + 1) (CTri.node m n a b)) :
    {x : Nat} → (t : CTri x) → C x t :=
  fun {x} t =>
    STri.rec (motive := fun s => (y : Nat) → (h : goodTri s y) → C y ⟨s, h⟩)
      (fun y h => h ▸ hl)
      (fun m n a b iha ihb y h =>
        (AndC.left h) ▸
          hn m n ⟨a, AndC.left (AndC.right h)⟩ ⟨b, AndC.right (AndC.right h)⟩
            (iha m (AndC.left (AndC.right h))) (ihb n (AndC.right (AndC.right h))))
      t.1 x t.2

/-! ### ι, and it is `Eq.refl` -- the proof term, not merely a provable one. -/

theorem CTri.iota_leaf {C : (x : Nat) → CTri x → Sort v}
    (hl : C 0 CTri.leaf)
    (hn : (m n : Nat) → (a : CTri m) → (b : CTri n) → C m a → C n b →
            C (m + n + 1) (CTri.node m n a b)) :
    CTri.rec' hl hn CTri.leaf = hl :=
  Eq.refl _

theorem CTri.iota_node {C : (x : Nat) → CTri x → Sort v}
    (hl : C 0 CTri.leaf)
    (hn : (m n : Nat) → (a : CTri m) → (b : CTri n) → C m a → C n b →
            C (m + n + 1) (CTri.node m n a b))
    (m n : Nat) (a : CTri m) (b : CTri n) :
    CTri.rec' hl hn (CTri.node m n a b)
      = hn m n a b (CTri.rec' hl hn a) (CTri.rec' hl hn b) :=
  Eq.refl _

/-! ### Pin 1: the derived recursor and Lean's own, against ONE transcription. -/

noncomputable example : ∀ {motive : (x : Nat) → CTri x → Sort v},
    motive 0 CTri.leaf →
    ((m n : Nat) → (a : CTri m) → (b : CTri n) → motive m a → motive n b →
      motive (m + n + 1) (CTri.node m n a b)) →
    {x : Nat} → (t : CTri x) → motive x t := @CTri.rec'

noncomputable example : ∀ {motive : (x : Nat) → Tri x → Sort v},
    motive 0 Tri.leaf →
    ((m n : Nat) → (a : Tri m) → (b : Tri n) → motive m a → motive n b →
      motive (m + n + 1) (Tri.node m n a b)) →
    {x : Nat} → (t : Tri x) → motive x t := @Tri.rec

/-- Both ι rules exercised together: the recursor is not blind to its step
functions.  Evaluated by `decide`-free reduction, so this is `rfl` too. -/
noncomputable example : CTri.rec' (C := fun _ _ => Nat) 0 (fun _ _ _ _ p q => p + q + 1)
    (CTri.node 0 0 CTri.leaf CTri.leaf) = 1 := rfl

/-! ############################################################
    ## Target 2: `Two` -- two constructors at the SAME index
    ############################################################ -/

inductive Two : Nat → Type where
  | l : (n : Nat) → Two n
  | r : (n : Nat) → Two (n + 1) → Two (n + 1) → Two n

inductive STwo : Type where
  | sl : (n : Nat) → STwo
  | sr : (n : Nat) → STwo → STwo → STwo

def goodTwo : STwo → Nat → Prop :=
  STwo.rec (motive := fun _ => Nat → Prop)
    (fun n x => n = x)
    (fun n _a _b iha ihb x => AndC (n = x) (AndC (iha (n + 1)) (ihb (n + 1))))

def CTwo (x : Nat) : Type := PSigma (fun s : STwo => goodTwo s x)

def CTwo.l (n : Nat) : CTwo n := ⟨.sl n, rfl⟩

def CTwo.r (n : Nat) (a b : CTwo (n + 1)) : CTwo n :=
  ⟨.sr n a.1 b.1, AndC.mk rfl (AndC.mk a.2 b.2)⟩

noncomputable def CTwo.rec' {C : (x : Nat) → CTwo x → Sort v}
    (hl : (n : Nat) → C n (CTwo.l n))
    (hr : (n : Nat) → (a b : CTwo (n + 1)) → C (n + 1) a → C (n + 1) b → C n (CTwo.r n a b)) :
    {x : Nat} → (t : CTwo x) → C x t :=
  fun {x} t =>
    STwo.rec (motive := fun s => (y : Nat) → (h : goodTwo s y) → C y ⟨s, h⟩)
      (fun n y h => h ▸ hl n)
      (fun n a b iha ihb y h =>
        (AndC.left h) ▸
          hr n ⟨a, AndC.left (AndC.right h)⟩ ⟨b, AndC.right (AndC.right h)⟩
            (iha (n + 1) (AndC.left (AndC.right h))) (ihb (n + 1) (AndC.right (AndC.right h))))
      t.1 x t.2

theorem CTwo.iota_l {C : (x : Nat) → CTwo x → Sort v}
    (hl : (n : Nat) → C n (CTwo.l n))
    (hr : (n : Nat) → (a b : CTwo (n + 1)) → C (n + 1) a → C (n + 1) b → C n (CTwo.r n a b))
    (n : Nat) :
    CTwo.rec' hl hr (CTwo.l n) = hl n :=
  Eq.refl _

theorem CTwo.iota_r {C : (x : Nat) → CTwo x → Sort v}
    (hl : (n : Nat) → C n (CTwo.l n))
    (hr : (n : Nat) → (a b : CTwo (n + 1)) → C (n + 1) a → C (n + 1) b → C n (CTwo.r n a b))
    (n : Nat) (a b : CTwo (n + 1)) :
    CTwo.rec' hl hr (CTwo.r n a b) = hr n a b (CTwo.rec' hl hr a) (CTwo.rec' hl hr b) :=
  Eq.refl _

/-! ### Pin 2. -/

noncomputable example : ∀ {motive : (x : Nat) → CTwo x → Sort v},
    ((n : Nat) → motive n (CTwo.l n)) →
    ((n : Nat) → (a b : CTwo (n + 1)) → motive (n + 1) a → motive (n + 1) b →
      motive n (CTwo.r n a b)) →
    {x : Nat} → (t : CTwo x) → motive x t := @CTwo.rec'

noncomputable example : ∀ {motive : (x : Nat) → Two x → Sort v},
    ((n : Nat) → motive n (Two.l n)) →
    ((n : Nat) → (a b : Two (n + 1)) → motive (n + 1) a → motive (n + 1) b →
      motive n (Two.r n a b)) →
    {x : Nat} → (t : Two x) → motive x t := @Two.rec

/-- Two constructors at the SAME index stay apart, from the recursor and its
two ι rules alone.  An earlier arm's refutation is why this check exists. -/
theorem CTwo.l_ne_r (n : Nat) (a b : CTwo (n + 1)) : CTwo.l n ≠ CTwo.r n a b := by
  intro h
  have h1 := CTwo.iota_l (C := fun _ _ => Prop) (fun _ => True) (fun _ _ _ _ _ => False) n
  have h2 := CTwo.iota_r (C := fun _ _ => Prop) (fun _ => True) (fun _ _ _ _ _ => False) n a b
  rw [h] at h1
  exact Eq.mpr (h2.symm.trans h1) trivial

/-- The carve genuinely carves: `good` is index-sensitive, so the `PSigma` is
not a wrapper around a subsingleton predicate.  (Contrast the degenerate
`ι := Unit` instance in `WIndexedCarve.lean`, where it *is* vacuous.) -/
example : goodTwo (.sl 0) 0 := rfl
example : ¬ goodTwo (.sl 0) 1 := fun h => Nat.noConfusion h

/-! ############################################################
    ## Target 3: `Bal` -- an index TELESCOPE of length two
    ##
    ## `good`'s second argument is one type, so a length-k telescope is packed
    ## into a right-nested `PSigma` -- which is exactly `Modelgen.packTyOf`,
    ## already built and already used by arm F.  Structure eta is what makes
    ## `pack (unpack y) ≡ y`, so the motive wrapper `fun y t => C y.1 y.2 t`
    ## typechecks with nothing to prove.
    ############################################################ -/

/-- The packed index telescope.  `PSigma` and not `Prod` so that a later
index's *type* may depend on an earlier index; nothing below changes if it
does. -/
abbrev Pk : Type := PSigma (fun _ : Nat => Nat)

inductive Bal : Nat → Nat → Type where
  | tip : Bal 0 0
  | bin : (a b c d : Nat) → Bal a b → Bal c d → Bal (a + c + 1) (b + d)

inductive SBal : Type where
  | stip : SBal
  | sbin : (a b c d : Nat) → SBal → SBal → SBal

def goodBal : SBal → Pk → Prop :=
  SBal.rec (motive := fun _ => Pk → Prop)
    (fun y => (⟨0, 0⟩ : Pk) = y)
    (fun a b c d _x _z ihx ihz y =>
      AndC ((⟨a + c + 1, b + d⟩ : Pk) = y) (AndC (ihx ⟨a, b⟩) (ihz ⟨c, d⟩)))

def CBal (a b : Nat) : Type := PSigma (fun s : SBal => goodBal s ⟨a, b⟩)

def CBal.tip : CBal 0 0 := ⟨.stip, rfl⟩

def CBal.bin (a b c d : Nat) (x : CBal a b) (z : CBal c d) : CBal (a + c + 1) (b + d) :=
  ⟨.sbin a b c d x.1 z.1, AndC.mk rfl (AndC.mk x.2 z.2)⟩

noncomputable def CBal.rec' {C : (a b : Nat) → CBal a b → Sort v}
    (ht : C 0 0 CBal.tip)
    (hb : (a b c d : Nat) → (x : CBal a b) → (z : CBal c d) → C a b x → C c d z →
            C (a + c + 1) (b + d) (CBal.bin a b c d x z)) :
    {a b : Nat} → (t : CBal a b) → C a b t :=
  fun {a b} t =>
    SBal.rec (motive := fun s => (y : Pk) → (h : goodBal s y) → C y.1 y.2 ⟨s, h⟩)
      (fun y h => h ▸ ht)
      (fun a b c d x z ihx ihz y h =>
        (AndC.left h) ▸
          hb a b c d ⟨x, AndC.left (AndC.right h)⟩ ⟨z, AndC.right (AndC.right h)⟩
            (ihx ⟨a, b⟩ (AndC.left (AndC.right h))) (ihz ⟨c, d⟩ (AndC.right (AndC.right h))))
      t.1 ⟨a, b⟩ t.2

theorem CBal.iota_tip {C : (a b : Nat) → CBal a b → Sort v}
    (ht : C 0 0 CBal.tip)
    (hb : (a b c d : Nat) → (x : CBal a b) → (z : CBal c d) → C a b x → C c d z →
            C (a + c + 1) (b + d) (CBal.bin a b c d x z)) :
    CBal.rec' ht hb CBal.tip = ht :=
  Eq.refl _

theorem CBal.iota_bin {C : (a b : Nat) → CBal a b → Sort v}
    (ht : C 0 0 CBal.tip)
    (hb : (a b c d : Nat) → (x : CBal a b) → (z : CBal c d) → C a b x → C c d z →
            C (a + c + 1) (b + d) (CBal.bin a b c d x z))
    (a b c d : Nat) (x : CBal a b) (z : CBal c d) :
    CBal.rec' ht hb (CBal.bin a b c d x z)
      = hb a b c d x z (CBal.rec' ht hb x) (CBal.rec' ht hb z) :=
  Eq.refl _

/-! ### Pin 3. -/

noncomputable example : ∀ {motive : (a b : Nat) → CBal a b → Sort v},
    motive 0 0 CBal.tip →
    ((a b c d : Nat) → (x : CBal a b) → (z : CBal c d) → motive a b x → motive c d z →
      motive (a + c + 1) (b + d) (CBal.bin a b c d x z)) →
    {a b : Nat} → (t : CBal a b) → motive a b t := @CBal.rec'

noncomputable example : ∀ {motive : (a b : Nat) → Bal a b → Sort v},
    motive 0 0 Bal.tip →
    ((a b c d : Nat) → (x : Bal a b) → (z : Bal c d) → motive a b x → motive c d z →
      motive (a + c + 1) (b + d) (Bal.bin a b c d x z)) →
    {a b : Nat} → (t : Bal a b) → motive a b t := @Bal.rec

noncomputable example : CBal.rec' (C := fun _ _ _ => Nat) 0 (fun _ _ _ _ _ _ p q => p + q + 1)
    (CBal.bin 0 0 0 0 CBal.tip CBal.tip) = 1 := rfl

/-! ############################################################
    ## Axiom bill: EMPTY, on all 21 derived constants.
    ##
    ## `WIndexedCarve.lean`'s bill is `[propext, Classical.choice, Quot.sound]`
    ## on every one of its 24, all three from the underlying W deciding
    ## `x.1 = a` for an arbitrary label type.  There is no such decision here.
    ############################################################ -/

/-- info: 'goodTri' does not depend on any axioms -/
#guard_msgs in #print axioms goodTri
/-- info: 'CTri' does not depend on any axioms -/
#guard_msgs in #print axioms CTri
/-- info: 'CTri.leaf' does not depend on any axioms -/
#guard_msgs in #print axioms CTri.leaf
/-- info: 'CTri.node' does not depend on any axioms -/
#guard_msgs in #print axioms CTri.node
/-- info: 'CTri.rec'' does not depend on any axioms -/
#guard_msgs in #print axioms CTri.rec'
/-- info: 'CTri.iota_leaf' does not depend on any axioms -/
#guard_msgs in #print axioms CTri.iota_leaf
/-- info: 'CTri.iota_node' does not depend on any axioms -/
#guard_msgs in #print axioms CTri.iota_node
/-- info: 'goodTwo' does not depend on any axioms -/
#guard_msgs in #print axioms goodTwo
/-- info: 'CTwo' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo
/-- info: 'CTwo.l' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo.l
/-- info: 'CTwo.r' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo.r
/-- info: 'CTwo.rec'' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo.rec'
/-- info: 'CTwo.iota_l' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo.iota_l
/-- info: 'CTwo.iota_r' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo.iota_r
/-- info: 'CTwo.l_ne_r' does not depend on any axioms -/
#guard_msgs in #print axioms CTwo.l_ne_r
/-- info: 'goodBal' does not depend on any axioms -/
#guard_msgs in #print axioms goodBal
/-- info: 'CBal' does not depend on any axioms -/
#guard_msgs in #print axioms CBal
/-- info: 'CBal.tip' does not depend on any axioms -/
#guard_msgs in #print axioms CBal.tip
/-- info: 'CBal.bin' does not depend on any axioms -/
#guard_msgs in #print axioms CBal.bin
/-- info: 'CBal.rec'' does not depend on any axioms -/
#guard_msgs in #print axioms CBal.rec'
/-- info: 'CBal.iota_tip' does not depend on any axioms -/
#guard_msgs in #print axioms CBal.iota_tip
/-- info: 'CBal.iota_bin' does not depend on any axioms -/
#guard_msgs in #print axioms CBal.iota_bin

/-! ############################################################
    ## Dependency closure, ASSERTED.
    ##
    ## Two things are checked rather than reported: that no yardstick leaked
    ## into the construction, and that none of W's distinctive dependencies is
    ## reachable.  The second is the claim that this arm does not stand on W.
    ##
    ## Eleven inductives are reachable and only six belong to the construction:
    ## `Eq` and `PSigma` (two of the four basis primitives), the three spliced
    ## skeletons, and `Nat`.  The other five -- `Add`, `HAdd`, `OfNat`,
    ## `PProd`, `PUnit` -- arrive through the TARGETS' OWN INDEX EXPRESSIONS
    ## (`m + n + 1`, the numeral `0`, and `Nat.rec`'s `below`/`brecOn`
    ## machinery).  A generator copies a constructor's index expressions
    ## verbatim out of the export, so whatever they mention is the modelled
    ## declaration's dependency and not the construction's; had the yardsticks
    ## been indexed by a bare variable instead, the list would be six.
    ##
    ## For contrast, `WIndexedCarve.lean` pins TWENTY for its carve core
    ## alone, before any target: Acc, And, Bool, Decidable, Eq, Exists, False,
    ## HEq, Iff, List, Nat, Nonempty, Option, Or, PProd, PUnit, Sigma, Subtype,
    ## True, WellFounded.
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
info: 11 reachable inductives: Add, Eq, HAdd, Nat, OfNat, PProd, PSigma, PUnit, SBal, STri, STwo
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let roots := [`CTri, `CTri.leaf, `CTri.node, `CTri.rec', `CTri.iota_leaf, `CTri.iota_node,
    `CTwo, `CTwo.l, `CTwo.r, `CTwo.rec', `CTwo.iota_l, `CTwo.iota_r,
    `CBal, `CBal.tip, `CBal.bin, `CBal.rec', `CBal.iota_tip, `CBal.iota_bin]
  let inds := closureInds env roots {} {}
  -- no yardstick leaked
  for bad in [`Tri, `Two, `Bal] do
    if inds.contains bad then throwError "the yardstick {bad} leaked into the construction"
  -- and nothing from W's 22-inductive dependency list (§8.11) is underneath this
  for bad in [`List, `Option, `Sigma, `Subtype, `Acc, `WellFounded, `And, `Or, `Iff,
              `Exists, `HEq, `Decidable, `Nonempty, `Quot, `Bool, `True, `False] do
    if inds.contains bad then
      throwError "{bad} is reachable: this arm has acquired one of W's dependencies"
  let names := (inds.toList.map toString).toArray.qsort (fun a b => decide (a < b))
  logInfo m!"{names.size} reachable inductives: {String.intercalate ", " names.toList}"
