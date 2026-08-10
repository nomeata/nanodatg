import Lean

/-
WEmitted.lean -- the shape a GENERATOR emits, as opposed to the shape a human
picks when the target is in front of them.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean WEmitted.lean
Expected: 0 errors, 0 warnings, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
THE QUESTION THIS FILE EXISTS FOR
════════════════════════════════════════════════════════════════════════════
`WGeneric.lean` settles the **tag** scheme: `K := Nat`, `A := Sigma D`,
`tg := Sigma.fst`, junk tags uninhabited.  What it does not settle is the
**branch** scheme, because it picks `B'` by hand at every arm:

    BTT 0 := WVoid     BTT 1 := Bool     BTT 2 := Nat     BTT 3 := WVoid

`Bool` because `node` happens to have two children and `Nat` because `lim`
happens to be `Nat`-branching.  A generator has neither of those observations.
It has a constructor telescope, and it has to produce -- uniformly, for every
arity, for binders and no binders, and for the two mixed together -- a branch
type, a dispatch, and the **eta lemma** that says the dispatch rebuilt from an
abstract `f` is `f` again.  That lemma is the whole of the per-constructor
glue, and `WGeneric.lean`'s three instances of it (`WVoid.elim`, `Bool.rec rfl
rfl`, and a bare `rfl`) are three special cases with no general form between
them.

This file writes the general form and checks it against a target that has all
six shapes at once.

════════════════════════════════════════════════════════════════════════════
THE SCHEME
════════════════════════════════════════════════════════════════════════════
Write `nrᵗ` for constructor `t`'s non-recursive fields and `rᵗ` for its
recursive ones, each recursive field `j` carrying a binder telescope
`x⃗ⱼ : Xⱼ,₁ → … → Xⱼ,ₘ`.

    D  t   := Σ (a : nrᵗ₁), … Σ (a : nrᵗₖ), PUnit        -- WVoid off the end
    Tel t j := Σ (x : Xⱼ,₁), … Σ (x : Xⱼ,ₘ), PUnit        -- WVoid off the end
    B' t   := Σ j : Nat, Tel t j
    A      := Σ t : Nat, D t
    tg     := Sigma.fst

**Both towers end in `PUnit`, and neither is allowed to collapse.** A
one-field `D` could be written as that field's type directly -- `WGeneric.lean`
writes `DTT 0 := Nat` -- and a no-binder `Tel` could be written `PUnit` with no
`Sigma` around it. Uniformity is worth more than the saved constructor here,
but it is not only that: **the terminating `PUnit` is what makes the universes
come out**, and that is the one part of this scheme that is not obvious.

  The core fixes `A` and `B'` at the *same* `Type u`, since `PTree`'s
  `A : Type u` and `Edge`'s `B' : K → Type u`. For a target at `Type u` every
  field type sits at some `Type v` with `v ≤ u` -- Lean's own constraint on the
  declaration. A Sigma tower over those alone would land at `Type (max v⃗)`,
  which is **below** `u` in general and would need a `ULift` that
  `w_core.ndjson` does not carry. Ending the tower at `PUnit.{u+1} : Type u`
  makes the max exactly `u` for free, at every arity including zero.

**Finiteness is still not needed and the junk is still uninhabited**, in both
towers now: `D t` is `WVoid` for `t ≥ nc` and `Tel t j` is `WVoid` for
`j ≥ rᵗ`. `GA.no_junk_tag` and `GA.no_junk_branch` are the two pins, and the
second is new here -- `WGeneric.lean` has no branch tower to get wrong.

════════════════════════════════════════════════════════════════════════════
THE ETA LEMMA, WHICH IS THE POINT
════════════════════════════════════════════════════════════════════════════
At tag `t` the recursor's minor is handed an abstract `f : B' t → C` and must
call the user's minor, which wants the children **uncurried** -- one argument
per recursive field, each a function of its own binders. Those are read off `f`:

    childⱼ x⃗ := f ⟨j, ⟨x₁, …, xₘ, ⟨⟩⟩⟩

and the user's minor then returns a `C` at the constructor *rebuilt* from them,
which is `sup ⟨t, d⟩ (dispatch child⃗)` rather than `sup ⟨t, d⟩ f`. So the arm
owes

    dispatch (child⃗ f) = f

**Every arm of it is `rfl`,** and that is the finding this file exists to
record. Writing `b : B' t` as `⟨b.1, b.2⟩` is `Sigma`'s definitional eta, so it
is enough to prove `∀ j tel, dispatch j tel = f ⟨j, tel⟩` and instantiate at
`b.1, b.2` -- no `Sigma.casesOn` in the proof at all. At branch `j` the left
side reduces to `f ⟨j, ⟨tel.1, …, tel.ₘ, ⟨⟩⟩⟩` and the right is `f ⟨j, tel⟩`,
and the two are definitionally equal by `Sigma` eta once more and `PUnit` eta
at the tower's end. Off the end of the telescope `tel : WVoid` and the arm is
`WVoid.elim`.

So the general form is one `funext`, one `Nat.casesOn` cascade over the branch
index whose motive is `fun j => ∀ tel, ⟨the dispatch at j⟩ = f ⟨j, tel⟩`,
`rfl` at each real branch and `WVoid.elim` off the end. That is a shape a
generator can emit from the constructor telescope alone.

════════════════════════════════════════════════════════════════════════════
WHAT THE MUTATIONS SAY -- MEASURED, NOT ASSUMED
════════════════════════════════════════════════════════════════════════════
Seven mutations were run against the file below. All seven are caught, and
**where** they are caught is the more interesting half of the answer, because
it is not where a reader would guess.

| mutation                                       | errors | caught at |
|---|---|---|
| junk **tag** inhabited (`GD` junk to `PUnit`)  | 19 | `GA.no_junk_tag`, **and `GC.rec'`** |
| junk **branch** inhabited (`GTel` junk)        | 32 | `GA.no_junk_branch`, **and four constructors and `GC.rec'`** |
| `alt`'s constructor moved to `leaf`'s tag      | 18 | `GC.rec'` |
| `two`'s children transposed in its dispatch    | 18 | `GC.rec'` |
| `mix` drops its branch index                   | 18 | `GC.rec'` |
| `gap`'s data tower drops its leading `Nat`     |  6 | `GC.iota_gap` |
| `alt` **collapsed onto** `leaf`'s tag, tag 5 vacated |  3 | `GC.iota_alt` |

**The junk being uninhabited is load-bearing for elaboration, not only for
correctness.** This is the opposite of the failure mode `WGeneric.lean` warns
about, and it is worth stating plainly: the junk arms are discharged by
`WVoid.elim`, so a `D` or `Tel` that sends the junk to `PUnit` does not quietly
produce a `W` bigger than the target -- it fails to elaborate, at the
constructor and at the recursor, before any pin is consulted. `GA.no_junk_tag`
and `GA.no_junk_branch` still fail too, so they are not vacuous; what they
guard is a *differently discharged* junk arm, which a later generator could
introduce without noticing.

**The last row is the only mutation with no type error behind it,** and it is
the one `WGeneric.lean` singles out. Two constructors of the same shape sharing
a tag is not a type error, because their minors have the same type; `GC.leaf n`
and `GC.alt n` simply become the same term. It is caught at `GC.iota_alt`,
which cannot be `Wrec_iota` any more, and `GC.leaf_ne_alt` is *false* under it
rather than merely unproven -- it is not reported only because Lean propagates
the earlier error. So the load-bearing pin for a collapsed tag assignment is
the ι rule itself, and `GC.leaf_ne_alt` is the statement that says why.
-/

set_option linter.unusedVariables false

namespace WT

set_option linter.unusedSectionVars false

abbrev Edge (K : Type) (B' : K → Type u) : Type u := Σ t : K, B' t

abbrev PTree (K : Type) (B' : K → Type u) (A : Type u) : Type u :=
  List (Edge K B') → Option A

variable {K : Type} {A : Type u} {B' : K → Type u}

def subt (t : PTree K B' A) (x : Edge K B') : PTree K B' A := fun p => t (x :: p)

def nowhere : PTree K B' A := fun _ => none

def Step (tg : A → K) (S : PTree K B' A → Prop) (t : PTree K B' A) : Prop :=
  ∃ a : A, t [] = some a ∧ (∀ b : B' (tg a), S (subt t ⟨tg a, b⟩)) ∧
    ∀ x : Edge K B', x.1 ≠ tg a → subt t x = nowhere

theorem Step.mono {tg : A → K} {S S' : PTree K B' A → Prop} (hss : ∀ u, S u → S' u)
    {t : PTree K B' A} (h : Step tg S t) : Step tg S' t := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, fun b => hss _ (h2 b), h3⟩

def Good (tg : A → K) (t : PTree K B' A) : Prop :=
  ∀ S : PTree K B' A → Prop, (∀ u, Step tg S u → S u) → S t

theorem Good.pre {tg : A → K} {t : PTree K B' A} (h : Step tg (Good tg) t) : Good tg t :=
  fun S hS => hS t (Step.mono (fun _u hu => hu S hS) h)

theorem Good.post {tg : A → K} {t : PTree K B' A} (h : Good tg t) : Step tg (Good tg) t :=
  h (Step tg (Good tg)) (fun _u hu => Step.mono (fun _v hv => Good.pre hv) hu)

def W (B' : K → Type u) (tg : A → K) : Type u := {t : PTree K B' A // Good tg t}

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

/-- The empty type, from what the fragment already carries. `PEmpty` is not in
`w_core.ndjson`; `Subtype`, `PUnit` and `False` are. -/
def WVoid : Type := Subtype (fun _ : PUnit.{1} => False)

def WVoid.elim {α : Sort v} (x : WVoid) : α := x.2.elim

/-! ############################################################
    ## The target: six constructors, six shapes
    ############################################################ -/

/-- The yardstick. Used ONLY in the pins.

Six arms, and each is here for a shape the emitted scheme has to handle and the
one before it does not:

* `leaf` — data, **no** children. The branch tower is `WVoid` at every index.
* `one` — **no** data, one plain child. The data tower is bare `PUnit`.
* `two` — data **and two** plain children, which is where a branch index that
  is right differs from one with its arms swapped.
* `mix` — a plain child **and** an infinitary one **in the same constructor**.
  This is the arm with no counterpart in `WGeneric.lean`: `lim` is infinitary
  and `node` is plain, and neither asks whether the two towers stay in step
  when a single constructor has both.
* `gap` — **data on both sides of a child**, so the non-recursive tower and the
  branch tower index *different* subsequences of one telescope. A generator
  that built `D` from "the fields before the first recursive one" passes every
  other arm here.
* `alt` — `leaf`'s shape at another tag, so that a permuted tag assignment is
  caught by a statement rather than by a type error. -/
inductive GT : Type where
  | leaf : Nat → GT
  | one  : GT → GT
  | two  : Bool → GT → GT → GT
  | mix  : GT → (Nat → GT) → GT
  | gap  : Nat → GT → Bool → GT → GT
  | alt  : Nat → GT

/-! ### The two towers

Both are `Nat.casesOn` cascades rather than `match`es, because a cascade is
what a generator emits: a `match` would mint a `GD.match_1` that the model
would then owe the output. -/

/-- `D` — tag ↦ that constructor's non-recursive fields as a `Sigma` tower
ending in `PUnit`, and `WVoid` off the end. -/
def GD (t : Nat) : Type :=
  Nat.casesOn (motive := fun _ => Type) t
    (Σ _ : Nat, PUnit)                                  -- 0 leaf : Nat
    (fun t1 => Nat.casesOn (motive := fun _ => Type) t1
      PUnit                                             -- 1 one  : —
      (fun t2 => Nat.casesOn (motive := fun _ => Type) t2
        (Σ _ : Bool, PUnit)                             -- 2 two  : Bool
        (fun t3 => Nat.casesOn (motive := fun _ => Type) t3
          PUnit                                         -- 3 mix  : —
          (fun t4 => Nat.casesOn (motive := fun _ => Type) t4
            (Σ _ : Nat, Σ _ : Bool, PUnit)              -- 4 gap  : Nat, Bool
            (fun t5 => Nat.casesOn (motive := fun _ => Type) t5
              (Σ _ : Nat, PUnit)                        -- 5 alt  : Nat
              (fun _ => WVoid))))))                     -- junk: uninhabited

/-- `Tel` — tag ↦ branch index ↦ that recursive field's binder telescope, as a
`Sigma` tower ending in `PUnit`, and `WVoid` off the end of **either** index.

The junk is uninhabited in both directions, and the second direction is the one
`WGeneric.lean` has no analogue of: a branch index past the constructor's
recursive-field count must be as empty as a tag past the constructor count, or
`W` acquires children no constructor produces. -/
def GTel (t : Nat) (j : Nat) : Type :=
  Nat.casesOn (motive := fun _ => Type) t
    WVoid                                               -- 0 leaf: no children
    (fun t1 => Nat.casesOn (motive := fun _ => Type) t1
      -- 1 one: one plain child
      (Nat.casesOn (motive := fun _ => Type) j PUnit (fun _ => WVoid))
      (fun t2 => Nat.casesOn (motive := fun _ => Type) t2
        -- 2 two: two plain children
        (Nat.casesOn (motive := fun _ => Type) j PUnit
          (fun j1 => Nat.casesOn (motive := fun _ => Type) j1 PUnit (fun _ => WVoid)))
        (fun t3 => Nat.casesOn (motive := fun _ => Type) t3
          -- 3 mix: a plain child, then a `Nat`-branching one
          (Nat.casesOn (motive := fun _ => Type) j PUnit
            (fun j1 => Nat.casesOn (motive := fun _ => Type) j1
              (Σ _ : Nat, PUnit) (fun _ => WVoid)))
          (fun t4 => Nat.casesOn (motive := fun _ => Type) t4
            -- 4 gap: two plain children, with data between them
            (Nat.casesOn (motive := fun _ => Type) j PUnit
              (fun j1 => Nat.casesOn (motive := fun _ => Type) j1 PUnit (fun _ => WVoid)))
            (fun t5 => Nat.casesOn (motive := fun _ => Type) t5
              WVoid                                     -- 5 alt: no children
              (fun _ => WVoid))))))                     -- junk

/-- The label. -/
abbrev GA : Type := Σ t : Nat, GD t
/-- The branch type: an index and that branch's binders. -/
abbrev GB (t : Nat) : Type := Σ j : Nat, GTel t j
/-- The tag of a label — the first projection and nothing else. -/
def gtg : GA → Nat := Sigma.fst

abbrev GC : Type := W GB gtg

/-! ### The constructors

Each is `sup ⟨t, dataTower⟩ dispatch`, where `dispatch` is a `Nat.casesOn`
cascade over the branch index `b.1` applied to `b.2`. The motive is written at
`fun j => GTel t j → GC` — at *every* index including the junk ones, which is
why it is a cascade and not a per-branch type. -/

noncomputable def GC.leaf (n : Nat) : GC :=
  sup (B' := GB) ⟨0, ⟨n, PUnit.unit⟩⟩ (fun b => WVoid.elim b.2)

noncomputable def GC.one (x : GC) : GC :=
  sup (B' := GB) ⟨1, PUnit.unit⟩ (fun b =>
    Nat.casesOn (motive := fun j => GTel 1 j → GC) b.1
      (fun _ => x)
      (fun _ tel => WVoid.elim tel)
      b.2)

noncomputable def GC.two (c : Bool) (x y : GC) : GC :=
  sup (B' := GB) ⟨2, ⟨c, PUnit.unit⟩⟩ (fun b =>
    Nat.casesOn (motive := fun j => GTel 2 j → GC) b.1
      (fun _ => x)
      (fun j1 => Nat.casesOn (motive := fun j1 => GTel 2 (j1 + 1) → GC) j1
        (fun _ => y)
        (fun _ tel => WVoid.elim tel))
      b.2)

noncomputable def GC.mix (x : GC) (g : Nat → GC) : GC :=
  sup (B' := GB) ⟨3, PUnit.unit⟩ (fun b =>
    Nat.casesOn (motive := fun j => GTel 3 j → GC) b.1
      (fun _ => x)
      (fun j1 => Nat.casesOn (motive := fun j1 => GTel 3 (j1 + 1) → GC) j1
        (fun tel => g tel.1)
        (fun _ tel => WVoid.elim tel))
      b.2)

noncomputable def GC.gap (n : Nat) (x : GC) (c : Bool) (y : GC) : GC :=
  sup (B' := GB) ⟨4, ⟨n, ⟨c, PUnit.unit⟩⟩⟩ (fun b =>
    Nat.casesOn (motive := fun j => GTel 4 j → GC) b.1
      (fun _ => x)
      (fun j1 => Nat.casesOn (motive := fun j1 => GTel 4 (j1 + 1) → GC) j1
        (fun _ => y)
        (fun _ tel => WVoid.elim tel))
      b.2)

noncomputable def GC.alt (n : Nat) : GC :=
  sup (B' := GB) ⟨5, ⟨n, PUnit.unit⟩⟩ (fun b => WVoid.elim b.2)

/-! ### The recursor

Two cascades, nested. The outer is over the **tag** and is `WGeneric.lean`'s;
the inner, inside each arm, is the **eta lemma** over the branch index, and it
is the piece that file has no general form of.

The eta lemma at tag `t` is
```
funext (fun b : GB t => <cascade over b.1, applied to b.2>)
```
with motive `fun j => ∀ tel : GTel t j, ⟨dispatch at j⟩ tel = f ⟨j, tel⟩`.
No `Sigma.casesOn`: `f b` and `f ⟨b.1, b.2⟩` are definitionally equal, so
instantiating the cascade at `b.1` and `b.2` already has the right type. Every
real branch is `rfl` and every junk branch is `WVoid.elim`. -/

noncomputable def GC.rec' {C : GC → Sort v}
    (hl : (n : Nat) → C (GC.leaf n))
    (ho : (x : GC) → C x → C (GC.one x))
    (ht : (c : Bool) → (x y : GC) → C x → C y → C (GC.two c x y))
    (hm : (x : GC) → (g : Nat → GC) → C x → ((i : Nat) → C (g i)) → C (GC.mix x g))
    (hg : (n : Nat) → (x : GC) → (c : Bool) → (y : GC) → C x → C y → C (GC.gap n x c y))
    (ha : (n : Nat) → C (GC.alt n)) :
    (t : GC) → C t :=
  Wrec (C := C) (fun a =>
    Nat.casesOn (motive := fun t =>
        (d : GD t) → (f : GB (gtg ⟨t, d⟩) → GC) →
          ((b : GB (gtg ⟨t, d⟩)) → C (f b)) → C (sup ⟨t, d⟩ f))
      a.1
      -- ── tag 0: leaf.  No children, so the eta lemma is `WVoid.elim` at
      --    every branch and the data tower is one deep. ──
      (fun d f _ih =>
        cast (congrArg C (congrArg (sup (B' := GB) (tg := gtg) ⟨0, d⟩)
          (funext (fun b : GB 0 =>
            WVoid.elim (α := WVoid.elim b.2 = f b) b.2))))
          (hl d.1))
      (fun t1 => Nat.casesOn (motive := fun t1 =>
          (d : GD (t1 + 1)) → (f : GB (gtg ⟨t1 + 1, d⟩) → GC) →
            ((b : GB (gtg ⟨t1 + 1, d⟩)) → C (f b)) → C (sup ⟨t1 + 1, d⟩ f))
        t1
        -- ── tag 1: one.  Data tower is bare `PUnit`, so nothing is projected
        --    out of `d` and its eta is `PUnit`'s. ──
        (fun d f ih =>
          cast (congrArg C (congrArg (sup (B' := GB) (tg := gtg) ⟨1, d⟩)
            (funext (fun b : GB 1 =>
              Nat.casesOn (motive := fun j => ∀ tel : GTel 1 j,
                  Nat.casesOn (motive := fun j => GTel 1 j → GC) j
                    (fun _ => f ⟨0, PUnit.unit⟩) (fun _ t => WVoid.elim t) tel
                    = f ⟨j, tel⟩)
                b.1 (fun _ => rfl) (fun _ t => WVoid.elim t) b.2))))
            (ho (f ⟨0, PUnit.unit⟩) (ih ⟨0, PUnit.unit⟩)))
        (fun t2 => Nat.casesOn (motive := fun t2 =>
            (d : GD (t2 + 2)) → (f : GB (gtg ⟨t2 + 2, d⟩) → GC) →
              ((b : GB (gtg ⟨t2 + 2, d⟩)) → C (f b)) → C (sup ⟨t2 + 2, d⟩ f))
          t2
          -- ── tag 2: two.  Two plain children; the branch cascade is two deep
          --    and swapping its arms is caught by `GC.two_inj_kids`. ──
          (fun d f ih =>
            cast (congrArg C (congrArg (sup (B' := GB) (tg := gtg) ⟨2, d⟩)
              (funext (fun b : GB 2 =>
                Nat.casesOn (motive := fun j => ∀ tel : GTel 2 j,
                    Nat.casesOn (motive := fun j => GTel 2 j → GC) j
                      (fun _ => f ⟨0, PUnit.unit⟩)
                      (fun j1 => Nat.casesOn (motive := fun j1 => GTel 2 (j1 + 1) → GC) j1
                        (fun _ => f ⟨1, PUnit.unit⟩) (fun _ t => WVoid.elim t))
                      tel = f ⟨j, tel⟩)
                  b.1 (fun _ => rfl)
                  (fun j1 => Nat.casesOn (motive := fun j1 => ∀ tel : GTel 2 (j1 + 1),
                      Nat.casesOn (motive := fun j => GTel 2 j → GC) (j1 + 1)
                        (fun _ => f ⟨0, PUnit.unit⟩)
                        (fun j1 => Nat.casesOn (motive := fun j1 => GTel 2 (j1 + 1) → GC) j1
                          (fun _ => f ⟨1, PUnit.unit⟩) (fun _ t => WVoid.elim t))
                        tel = f ⟨j1 + 1, tel⟩)
                    j1 (fun _ => rfl) (fun _ t => WVoid.elim t))
                  b.2))))
              (ht d.1 (f ⟨0, PUnit.unit⟩) (f ⟨1, PUnit.unit⟩)
                (ih ⟨0, PUnit.unit⟩) (ih ⟨1, PUnit.unit⟩)))
          (fun t3 => Nat.casesOn (motive := fun t3 =>
              (d : GD (t3 + 3)) → (f : GB (gtg ⟨t3 + 3, d⟩) → GC) →
                ((b : GB (gtg ⟨t3 + 3, d⟩)) → C (f b)) → C (sup ⟨t3 + 3, d⟩ f))
            t3
            -- ── tag 3: mix.  A plain child and an infinitary one in the same
            --    constructor: branch 0's telescope is empty and branch 1's is
            --    one `Nat` deep, so the two towers are at different depths in
            --    one cascade. This is the arm with no counterpart above. ──
            (fun d f ih =>
              cast (congrArg C (congrArg (sup (B' := GB) (tg := gtg) ⟨3, d⟩)
                (funext (fun b : GB 3 =>
                  Nat.casesOn (motive := fun j => ∀ tel : GTel 3 j,
                      Nat.casesOn (motive := fun j => GTel 3 j → GC) j
                        (fun _ => f ⟨0, PUnit.unit⟩)
                        (fun j1 => Nat.casesOn (motive := fun j1 => GTel 3 (j1 + 1) → GC) j1
                          (fun tl => f ⟨1, ⟨tl.1, PUnit.unit⟩⟩) (fun _ t => WVoid.elim t))
                        tel = f ⟨j, tel⟩)
                    b.1 (fun _ => rfl)
                    (fun j1 => Nat.casesOn (motive := fun j1 => ∀ tel : GTel 3 (j1 + 1),
                        Nat.casesOn (motive := fun j => GTel 3 j → GC) (j1 + 1)
                          (fun _ => f ⟨0, PUnit.unit⟩)
                          (fun j1 => Nat.casesOn (motive := fun j1 => GTel 3 (j1 + 1) → GC) j1
                            (fun tl => f ⟨1, ⟨tl.1, PUnit.unit⟩⟩) (fun _ t => WVoid.elim t))
                          tel = f ⟨j1 + 1, tel⟩)
                      j1 (fun _ => rfl) (fun _ t => WVoid.elim t))
                    b.2))))
                (hm (f ⟨0, PUnit.unit⟩) (fun i => f ⟨1, ⟨i, PUnit.unit⟩⟩)
                  (ih ⟨0, PUnit.unit⟩) (fun i => ih ⟨1, ⟨i, PUnit.unit⟩⟩)))
            (fun t4 => Nat.casesOn (motive := fun t4 =>
                (d : GD (t4 + 4)) → (f : GB (gtg ⟨t4 + 4, d⟩) → GC) →
                  ((b : GB (gtg ⟨t4 + 4, d⟩)) → C (f b)) → C (sup ⟨t4 + 4, d⟩ f))
              t4
              -- ── tag 4: gap.  Data on both sides of a child. The data tower
              --    is `⟨n, ⟨c, ⟨⟩⟩⟩` — the two non-recursive fields in their
              --    own order, with the recursive ones simply not in it — and
              --    the branch tower is the recursive ones in theirs. ──
              (fun d f ih =>
                cast (congrArg C (congrArg (sup (B' := GB) (tg := gtg) ⟨4, d⟩)
                  (funext (fun b : GB 4 =>
                    Nat.casesOn (motive := fun j => ∀ tel : GTel 4 j,
                        Nat.casesOn (motive := fun j => GTel 4 j → GC) j
                          (fun _ => f ⟨0, PUnit.unit⟩)
                          (fun j1 => Nat.casesOn (motive := fun j1 => GTel 4 (j1 + 1) → GC) j1
                            (fun _ => f ⟨1, PUnit.unit⟩) (fun _ t => WVoid.elim t))
                          tel = f ⟨j, tel⟩)
                      b.1 (fun _ => rfl)
                      (fun j1 => Nat.casesOn (motive := fun j1 => ∀ tel : GTel 4 (j1 + 1),
                          Nat.casesOn (motive := fun j => GTel 4 j → GC) (j1 + 1)
                            (fun _ => f ⟨0, PUnit.unit⟩)
                            (fun j1 => Nat.casesOn (motive := fun j1 => GTel 4 (j1 + 1) → GC) j1
                              (fun _ => f ⟨1, PUnit.unit⟩) (fun _ t => WVoid.elim t))
                            tel = f ⟨j1 + 1, tel⟩)
                        j1 (fun _ => rfl) (fun _ t => WVoid.elim t))
                      b.2))))
                  (hg d.1 (f ⟨0, PUnit.unit⟩) d.2.1 (f ⟨1, PUnit.unit⟩)
                    (ih ⟨0, PUnit.unit⟩) (ih ⟨1, PUnit.unit⟩)))
              (fun t5 => Nat.casesOn (motive := fun t5 =>
                  (d : GD (t5 + 5)) → (f : GB (gtg ⟨t5 + 5, d⟩) → GC) →
                    ((b : GB (gtg ⟨t5 + 5, d⟩)) → C (f b)) → C (sup ⟨t5 + 5, d⟩ f))
                t5
                -- ── tag 5: alt.  `leaf`'s shape exactly, at another tag. ──
                (fun d f _ih =>
                  cast (congrArg C (congrArg (sup (B' := GB) (tg := gtg) ⟨5, d⟩)
                    (funext (fun b : GB 5 =>
                      WVoid.elim (α := WVoid.elim b.2 = f b) b.2))))
                    (ha d.1))
                -- ── the junk tags, discharged from the emptiness of `GD` ──
                (fun _t6 d _f _ih => WVoid.elim d))))))
      a.2)

/-! ### The ι rules — one per constructor, each `Wrec_iota` and nothing else -/

section Iota
variable {C : GC → Sort v}
  (hl : (n : Nat) → C (GC.leaf n))
  (ho : (x : GC) → C x → C (GC.one x))
  (ht : (c : Bool) → (x y : GC) → C x → C y → C (GC.two c x y))
  (hm : (x : GC) → (g : Nat → GC) → C x → ((i : Nat) → C (g i)) → C (GC.mix x g))
  (hg : (n : Nat) → (x : GC) → (c : Bool) → (y : GC) → C x → C y → C (GC.gap n x c y))
  (ha : (n : Nat) → C (GC.alt n))

theorem GC.iota_leaf (n : Nat) :
    GC.rec' hl ho ht hm hg ha (GC.leaf n) = hl n := Wrec_iota _ _ _

theorem GC.iota_one (x : GC) :
    GC.rec' hl ho ht hm hg ha (GC.one x)
      = ho x (GC.rec' hl ho ht hm hg ha x) := Wrec_iota _ _ _

theorem GC.iota_two (c : Bool) (x y : GC) :
    GC.rec' hl ho ht hm hg ha (GC.two c x y)
      = ht c x y (GC.rec' hl ho ht hm hg ha x) (GC.rec' hl ho ht hm hg ha y) :=
  Wrec_iota _ _ _

theorem GC.iota_mix (x : GC) (g : Nat → GC) :
    GC.rec' hl ho ht hm hg ha (GC.mix x g)
      = hm x g (GC.rec' hl ho ht hm hg ha x)
          (fun i => GC.rec' hl ho ht hm hg ha (g i)) := Wrec_iota _ _ _

theorem GC.iota_gap (n : Nat) (x : GC) (c : Bool) (y : GC) :
    GC.rec' hl ho ht hm hg ha (GC.gap n x c y)
      = hg n x c y (GC.rec' hl ho ht hm hg ha x) (GC.rec' hl ho ht hm hg ha y) :=
  Wrec_iota _ _ _

theorem GC.iota_alt (n : Nat) :
    GC.rec' hl ho ht hm hg ha (GC.alt n) = ha n := Wrec_iota _ _ _

end Iota

/-! ### Pin 1: the derived recursor against a transcription, and Lean's own
recursor against the **same** transcription, so the transcription is checked
rather than trusted. -/

noncomputable example : ∀ {motive : GC → Sort v},
    ((n : Nat) → motive (GC.leaf n)) →
    ((x : GC) → motive x → motive (GC.one x)) →
    ((c : Bool) → (x y : GC) → motive x → motive y → motive (GC.two c x y)) →
    ((x : GC) → (g : Nat → GC) → motive x → ((i : Nat) → motive (g i)) →
      motive (GC.mix x g)) →
    ((n : Nat) → (x : GC) → (c : Bool) → (y : GC) → motive x → motive y →
      motive (GC.gap n x c y)) →
    ((n : Nat) → motive (GC.alt n)) →
    (t : GC) → motive t := @GC.rec'

noncomputable example : ∀ {motive : GT → Sort v},
    ((n : Nat) → motive (GT.leaf n)) →
    ((x : GT) → motive x → motive (GT.one x)) →
    ((c : Bool) → (x y : GT) → motive x → motive y → motive (GT.two c x y)) →
    ((x : GT) → (g : Nat → GT) → motive x → ((i : Nat) → motive (g i)) →
      motive (GT.mix x g)) →
    ((n : Nat) → (x : GT) → (c : Bool) → (y : GT) → motive x → motive y →
      motive (GT.gap n x c y)) →
    ((n : Nat) → motive (GT.alt n)) →
    (t : GT) → motive t := @GT.rec

/-! ### Pin 2: non-degeneracy, from the recursor and its ι rules alone.

`tagIx` reads the **arm index** back out of a term through the derived
recursor. Six one-line lemmas then separate all fifteen pairs at once, which is
the only form that scales: `WGeneric.lean` writes its three pairs out by hand
and a sixth constructor would have taken that to fifteen theorems, at which
point the pair that actually needs one gets lost among the fourteen that are
already type errors. -/

private noncomputable abbrev tagIx : GC → Nat :=
  GC.rec' (C := fun _ => Nat)
    (fun _ => 0) (fun _ _ => 1) (fun _ _ _ _ _ => 2)
    (fun _ _ _ _ => 3) (fun _ _ _ _ _ _ => 4) (fun _ => 5)

theorem GC.tag_leaf (n : Nat) : tagIx (GC.leaf n) = 0 := GC.iota_leaf _ _ _ _ _ _ n
theorem GC.tag_one (x : GC) : tagIx (GC.one x) = 1 := GC.iota_one _ _ _ _ _ _ x
theorem GC.tag_two (c : Bool) (x y : GC) : tagIx (GC.two c x y) = 2 :=
  GC.iota_two _ _ _ _ _ _ c x y
theorem GC.tag_mix (x : GC) (g : Nat → GC) : tagIx (GC.mix x g) = 3 :=
  GC.iota_mix _ _ _ _ _ _ x g
theorem GC.tag_gap (n : Nat) (x : GC) (c : Bool) (y : GC) : tagIx (GC.gap n x c y) = 4 :=
  GC.iota_gap _ _ _ _ _ _ n x c y
theorem GC.tag_alt (n : Nat) : tagIx (GC.alt n) = 5 := GC.iota_alt _ _ _ _ _ _ n

/-- **The pin for the pair the shapes do not separate.** `leaf` and `alt` have
the same field telescope, so nothing about their minors' types distinguishes
them: two constructors of the same shape sharing a tag is not a type error,
and `GC.leaf n` and `GC.alt n` simply become the same term.

Measured: under that mutation this statement is **false**, and the run reports
it at `GC.iota_alt` — which can no longer be `Wrec_iota`, since the tag's arm
calls `hl` — rather than here, because Lean propagates the earlier error. The
ι rule is what does the catching; this is what says why it matters. -/
theorem GC.leaf_ne_alt (n m : Nat) : GC.leaf n ≠ GC.alt m := fun h =>
  absurd ((GC.tag_leaf n).symm.trans (h ▸ GC.tag_alt m : tagIx (GC.leaf n) = 5))
    (by decide)

/-- The same for `two` and `gap`. Their minors differ only by `gap`'s leading
`Nat`, so a generator that built the data tower from "the fields before the
first recursive one" — dropping `gap`'s `Bool`, which sits *after* a child —
would emit two arms of the same shape.

Measured: that mutation is caught six lines earlier, at `GC.iota_gap`, whose
statement stops being `Wrec_iota`'s. This pin is not what notices it; it is
what would notice a *tag* collapse between the two, which the shapes do not
rule out either. -/
theorem GC.two_ne_gap (c : Bool) (x y : GC) (n : Nat) (d : Bool) (u v : GC) :
    GC.two c x y ≠ GC.gap n u d v := fun h =>
  absurd ((GC.tag_two c x y).symm.trans (h ▸ GC.tag_gap n u d v : tagIx (GC.two c x y) = 4))
    (by decide)

/-! ### Pin 3: **the payload survives the round trip**, at every arm that has
one, and *each* field of a multi-field arm separately.

A model that recorded the tag and lost the data tower — or kept the tower and
projected the wrong component out of it — passes every check above. `gap` is
the arm that matters: its two fields sit at tower depths 1 and 2, and reading
`d.1` where `d.2.1` belongs is exactly the slip a generator makes. -/

private noncomputable abbrev natOf : GC → Nat :=
  GC.rec' (C := fun _ => Nat)
    (fun n => n) (fun _ _ => 0) (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ => 0) (fun n _ _ _ _ _ => n) (fun n => n)

private noncomputable abbrev boolOf : GC → Bool :=
  GC.rec' (C := fun _ => Bool)
    (fun _ => false) (fun _ _ => false) (fun c _ _ _ _ => c)
    (fun _ _ _ _ => false) (fun _ _ c _ _ _ => c) (fun _ => false)

theorem GC.leaf_data (n : Nat) : natOf (GC.leaf n) = n := GC.iota_leaf _ _ _ _ _ _ n
theorem GC.alt_data (n : Nat) : natOf (GC.alt n) = n := GC.iota_alt _ _ _ _ _ _ n
theorem GC.two_data (c : Bool) (x y : GC) : boolOf (GC.two c x y) = c :=
  GC.iota_two _ _ _ _ _ _ c x y

/-- **`gap`'s two fields, both of them, and they are at different tower
depths.** Reading `d.1` for the `Bool` — or `d.2.1` for the `Nat` — is a type
error and needs no pin. Reading the *right* component of the *wrong* tower is
not: had `GD 4` been built as `Σ _ : Bool, Σ _ : Nat, PUnit` with the
constructor storing `⟨c, ⟨n, ⟨⟩⟩⟩`, every other check in this file still passes
and these two fail. -/
theorem GC.gap_data (n : Nat) (x : GC) (c : Bool) (y : GC) :
    natOf (GC.gap n x c y) = n ∧ boolOf (GC.gap n x c y) = c :=
  ⟨GC.iota_gap _ _ _ _ _ _ n x c y, GC.iota_gap _ _ _ _ _ _ n x c y⟩

/-! ### Pin 4: **the children survive too, and in the right order.**

`two` and `gap` each have two plain children at branch indices 0 and 1, and
nothing above distinguishes a dispatch that swaps them: the ι rules are stated
with the same `x y` on both sides. The weight `2 * p + q` is not symmetric, so
it does. -/

private noncomputable abbrev weigh : GC → Nat :=
  GC.rec' (C := fun _ => Nat)
    (fun n => n) (fun _ p => p + 1) (fun _ _ _ p q => 2 * p + q)
    (fun _ _ p ih => 2 * p + ih 3 + ih 5) (fun _ _ _ _ p q => 2 * p + q) (fun _ => 0)

theorem GC.weigh_leaf (n : Nat) : weigh (GC.leaf n) = n := GC.iota_leaf _ _ _ _ _ _ n
theorem GC.weigh_two (c : Bool) (x y : GC) :
    weigh (GC.two c x y) = 2 * weigh x + weigh y := GC.iota_two _ _ _ _ _ _ c x y
theorem GC.weigh_gap (n : Nat) (x : GC) (c : Bool) (y : GC) :
    weigh (GC.gap n x c y) = 2 * weigh x + weigh y := GC.iota_gap _ _ _ _ _ _ n x c y
theorem GC.weigh_mix (x : GC) (g : Nat → GC) :
    weigh (GC.mix x g) = 2 * weigh x + weigh (g 3) + weigh (g 5) :=
  GC.iota_mix _ _ _ _ _ _ x g

theorem GC.two_inj_kids : weigh (GC.two true (GC.leaf 1) (GC.leaf 2)) = 4 := by
  rw [GC.weigh_two, GC.weigh_leaf, GC.weigh_leaf]

theorem GC.gap_inj_kids : weigh (GC.gap 9 (GC.leaf 1) false (GC.leaf 2)) = 4 := by
  rw [GC.weigh_gap, GC.weigh_leaf, GC.weigh_leaf]

/-- **The infinitary child is indexed, and by the right index.** `mix`'s branch
1 carries a `Nat` in its telescope, and a dispatch that dropped it — sending
every `i` to one child — satisfies `GC.iota_mix` and fails here. -/
theorem GC.mix_indexes : weigh (GC.mix (GC.leaf 1) (fun i => GC.leaf i)) = 10 := by
  rw [GC.weigh_mix, GC.weigh_leaf, GC.weigh_leaf, GC.weigh_leaf]

/-! ### Pin 5: **the junk is uninhabited in both directions.**

`GA.no_junk_tag` is `WGeneric.lean`'s `ATT.no_junk`. `GA.no_junk_branch` is the
one this scheme adds: a branch index past a constructor's recursive-field count
must be as empty as a tag past the constructor count, or `W` acquires children
that no constructor produces and the model is strictly bigger than the target.

**Both were measured, and both are stronger here than the statement suggests.**
Sending either junk to `PUnit` does not give a wrong model that passes every
check — it fails to elaborate, because the junk arms of the constructors and of
`GC.rec'` are discharged by `WVoid.elim` and there is no such term at `PUnit`.
These two still fail under the mutation, so they are not vacuous; what they
guard against is a junk arm discharged some *other* way, which a later
generator could introduce without a type error to stop it. -/

theorem GA.no_junk_tag (a : GA) :
    a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 ∨ a.1 = 4 ∨ a.1 = 5 := by
  obtain ⟨t, d⟩ := a
  match t with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | 2 => exact Or.inr (Or.inr (Or.inl rfl))
  | 3 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | 4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | 5 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | _ + 6 => exact WVoid.elim d

/-- Branch indices, per tag: `leaf` and `alt` admit none, `one` admits only 0,
and the other three only 0 and 1. Written out arm by arm rather than closed by
one tactic, because the whole content of the statement is that the six arms
have *different* answers. -/
theorem GA.no_junk_branch :
    (∀ b : GB 0, False) ∧ (∀ b : GB 1, b.1 = 0) ∧
    (∀ b : GB 2, b.1 = 0 ∨ b.1 = 1) ∧ (∀ b : GB 3, b.1 = 0 ∨ b.1 = 1) ∧
    (∀ b : GB 4, b.1 = 0 ∨ b.1 = 1) ∧ (∀ b : GB 5, False) := by
  refine ⟨fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_⟩
  · exact WVoid.elim b.2
  · obtain ⟨j, tel⟩ := b
    match j with
    | 0 => rfl
    | _ + 1 => exact WVoid.elim tel
  · obtain ⟨j, tel⟩ := b
    match j with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | _ + 2 => exact WVoid.elim tel
  · obtain ⟨j, tel⟩ := b
    match j with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | _ + 2 => exact WVoid.elim tel
  · obtain ⟨j, tel⟩ := b
    match j with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | _ + 2 => exact WVoid.elim tel
  · exact WVoid.elim b.2

/-! ############################################################
    ## The bill
    ############################################################ -/

/-- info: 'GC.rec'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.rec'
/-- info: 'GC.iota_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.iota_leaf
/-- info: 'GC.iota_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.iota_one
/-- info: 'GC.iota_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.iota_two
/-- info: 'GC.iota_mix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.iota_mix
/-- info: 'GC.iota_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.iota_gap
/-- info: 'GC.iota_alt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.iota_alt
/-- info: 'GC.tag_mix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.tag_mix
/-- info: 'GC.tag_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.tag_gap
/-- info: 'GC.weigh_mix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.weigh_mix
/-- info: 'GC.leaf_ne_alt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.leaf_ne_alt
/-- info: 'GC.two_ne_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.two_ne_gap
/-- info: 'GC.gap_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.gap_data
/-- info: 'GC.two_inj_kids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.two_inj_kids
/-- info: 'GC.gap_inj_kids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.gap_inj_kids
/-- info: 'GC.mix_indexes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GC.mix_indexes
/-- info: 'GA.no_junk_tag' does not depend on any axioms -/
#guard_msgs in #print axioms GA.no_junk_tag
/-- info: 'GA.no_junk_branch' does not depend on any axioms -/
#guard_msgs in #print axioms GA.no_junk_branch
