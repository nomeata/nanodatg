import Lean

/-
WUntagged.lean -- **the untagged W is the tagged W at `K := A` and `tg := id`.**

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean WUntagged.lean
Expected: 0 errors, every `#guard_msgs` satisfied.

════════════════════════════════════════════════════════════════════════════
THE QUESTION THIS FILE EXISTS FOR
════════════════════════════════════════════════════════════════════════════
`WTagged.lean` builds W with a path step carrying only the constructor **tag**,
so `mk`'s guard is `x.1 = tg a` at the tag type and `DecidableEq K` discharges
it at `K := Nat`.  Its precondition is that the branch type factor through the
tag: a recursive field's binder telescope may not mention the constructor's own
non-recursive fields.  `WType`, `PSet` and `FirstOrder.Language.Term` are
exactly the shapes that fail it -- `WType.mk`'s child is `β a → WType β`, whose
binder is the *first field*.

`WFromPaths.lean` builds a W that does reach them, with the path carrying the
whole label, and `MODELGEN.md` §8.16 has presented the two as **two
constructions** with different bills ever since.

**They are one construction.**  `WTagged.lean`'s core is already generic in
`K`, `B' : K → Type u` and `tg : A → K`; the untagged construction is that core
at `K := A` and `tg := id`, and `WFromPaths.lean` is its special case.  Two
things had to be checked and both hold:

  1. **`K` may live at `Type w`.**  It was written `K : Type` because `Nat` is,
     and the untagged instantiation needs `K := A : Type u`.  Generalising it
     costs **no proof change at all** -- the whole core below is `WTagged.lean`'s
     with three binders widened, and `Edge`/`PTree`/`W` land at
     `Type (max w u)`, which normalises to `Type u` at both `w := 0` (tagged)
     and `w := u` (untagged).
  2. **`DecidableEq A` is the entire price.**  `WT.decEqAll` below is
     `Classical.propDecidable` at an equality, and `#print axioms` puts the
     untagged ι rule at `[propext, Classical.choice, Quot.sound]` against the
     tagged one's `[propext, Quot.sound]`.  That is the trade §8.16 measured and
     declined when `Classical.choice` was uncovered; it is covered now, so the
     trade is available and this file is what it buys.

════════════════════════════════════════════════════════════════════════════
WHAT IS ACTUALLY NEW -- THE BRANCH SCHEME
════════════════════════════════════════════════════════════════════════════
The carrier is not the hard part; the **branch tower** is.  At the tag scheme

    D   t   := Σ' (a : nr^t_1), … , 1        -- ctor t's non-recursive fields
    Tel t j := Σ' (x : X_{j,1}), … , 1       -- ctor t's j-th child's binders
    B'  t   := Σ' j : Nat, Tel t j
    A       := Σ' t : Nat, D t
    tg      := PSigma.fst

`Tel` is a function of the **tag**, which is exactly why the binders may not
mention the fields.  Untagged, `B' : A → Type u`, so

    Tel a j := Nat.rec (motive := fun t => D t → Nat → Type u) … a.1 a.2

-- the cascade is still on the tag, but the **data is an argument of the
motive**, and each arm receives that constructor's own `D t` to project the
fields it needs out of.  That one change is the whole delta, and everything
downstream (the dispatch, the eta lemma, the ι rules) follows it.

`Tm` below carries every hazard at once: a child whose binder is field 0
(`FirstOrder.Language.Term`'s and `WType`'s shape), a constructor with **two**
children of which only the first has binders (so the branch-index cascade is
exercised and not just the tag cascade), a non-recursive field *between* the
one the binder mentions and the child (so the projection depth is not 1), and a
base constructor with no children at all.

════════════════════════════════════════════════════════════════════════════
WHAT THIS BUYS, AND WHAT IT DOES NOT
════════════════════════════════════════════════════════════════════════════
Three of `MODELGEN.md` §8.16.5's nine declines are `tagFactored`'s refusal and
this scheme is what closes them: `WType`, `PSet` and
`FirstOrder.Language.Term`, all three declining at `recSlotOf` with
`B factors through the tag: no` and `carrier is Type u: yes`.

**`PFunctor.Approx.CofixA` is not one of them**, and the census row that puts
it beside them is about *which job* would close it, not about which guard stops
it. It is an **indexed** family and declines at arm C's erasure guard, before
any of this is reached: `intro {n} : ∀ a, (F.B a → CofixA F n) → CofixA F (n+1)`
has a recursive occurrence under a binder, so `eraseCtorTy` and `spineSwap` —
which replace a recursive field's *whole domain* — have nothing to replace.
This scheme would model its skeleton (`Skel | intro : ∀ a, (F.B a → Skel) → Skel`
is `WType F`), so `Iso.requires` would be satisfied; what is missing is the
erasure, and that is an **infinitary arm C**: `eraseCtorTy` walking into a
field's own forall-telescope to replace only the final `T p⃗ e⃗`, and then
`good`, its minor and the carve proof carrying a slot whose clause is
`∀ b, good (f b) ι⃗` rather than `good f ι⃗`. Two jobs, not one. So the untagged
arm takes the census to **6**, not to 5.

════════════════════════════════════════════════════════════════════════════
THE MUTATIONS
════════════════════════════════════════════════════════════════════════════
Six, against the scheme below, and one of them is green.

  | mutation                                             | result |
  |------------------------------------------------------|--------|
  | `Tel` reads a constant bound instead of `d.1`         | red    |
  | `mix`'s second IH read from branch 0, not branch 1    | red    |
  | the eta transport dropped from `F`'s `app` arm        | red    |
  | `D`'s junk-**tag** arm inhabited                      | red    |
  | `Tel`'s junk-**branch-index** arm inhabited           | red    |
  | `Tel`'s junk-**tag** arm inhabited                    | GREEN  |

The last row is a fact about the scheme worth having rather than a hole in the
pin: a label at a junk tag is already impossible, because `A = Σ' t, D t` and
`D`'s own junk arm is empty — so `Tel` is never asked at a tag no constructor
has, and what it answers there cannot be observed. The **branch-index** junk
arm is a different matter and is load-bearing, because within a *real* tag the
index ranges over all of `Nat`. `WEmitted.lean`'s "junk uninhabited in both
directions" is therefore one requirement on `D` and one on `Tel`, and only the
second of `Tel`'s two is a requirement at all.

The first row is the one that says this file is not `WTagged.lean` again: the
whole difference is that `Tel` reads `d`, and a scheme that does not is red at
three separate sites.
-/

universe u v w

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
abbrev Edge (K : Type w) (B' : K → Type u) : Type (max w u) := Σ t : K, B' t

/-- A raw tree: a partial labelling of paths. The label at a path is the
**whole** `A`, so nothing about the constructor's data is lost by recording
only the tag on the path itself. -/
abbrev PTree (K : Type w) (B' : K → Type u) (A : Type u) : Type (max w u) :=
  List (Edge K B') → Option A

variable {K : Type w} {A : Type u} {B' : K → Type u}

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
def W (B' : K → Type u) (tg : A → K) : Type (max w u) := {t : PTree K B' A // Good tg t}

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

noncomputable def WT.decEqAll (α : Sort u) : DecidableEq α :=
  fun a b => Classical.propDecidable (a = b)


/-! ## The target, and every hazard in one declaration -/

/-- `var` has no children; `app`'s child's binder is **field 0**; `mix` has
**two** children of which only the first has binders, and the field its binder
mentions is **not** adjacent to it. -/
inductive Tm : Type where
  | var : Nat → Tm
  | app : (n : Nat) → (Fin n → Tm) → Tm
  | mix : (k : Nat) → Bool → (Fin k → Tm) → Tm → Tm

/-! ## The scheme, in the uniform form a generator emits

Both towers end at a unit at exactly the carrier's sort and the junk arms are
uninhabited in both directions — `WEmitted.lean`'s two rules, unchanged. At
`Type 0` the unit is `PUnit` and the empty is `PEmpty`. -/

namespace WU

abbrev One : Type := PUnit
abbrev Non : Type := PEmpty

/-- `D t` — constructor `t`'s non-recursive fields, right-nested. -/
def D : Nat → Type
  | 0 => PSigma fun _ : Nat => One                      -- var
  | 1 => PSigma fun _ : Nat => One                      -- app
  | 2 => PSigma fun _ : Nat => PSigma fun _ : Bool => One  -- mix
  | _ + 3 => Non

/-- The label: tag plus that constructor's data. -/
abbrev A : Type := PSigma D

/-- `Tel a j` — the `j`-th child's binder tower of the constructor `a` names,
**reading `a`'s own data**. The cascade is on the tag and the data is an
argument of the motive, which is the whole difference from the tag scheme. -/
def Tel : A → Nat → Type := fun a =>
  Nat.rec (motive := fun t => D t → Nat → Type)
    (fun _ _ => Non)                                     -- var: no children
    (fun t ih =>
      match t, ih with
      | 0, _ => fun d j =>                               -- app
        Nat.rec (motive := fun _ => Type)
          (PSigma fun _ : Fin d.1 => One)                -- child 0: binder `Fin n`
          (fun _ _ => Non) j
      | 1, _ => fun d j =>                               -- mix
        Nat.rec (motive := fun _ => Type)
          (PSigma fun _ : Fin d.1 => One)                -- child 0: binder `Fin k`
          (fun j' _ =>
            Nat.rec (motive := fun _ => Type) One (fun _ _ => Non) j') j
      | _ + 2, _ => fun _ _ => Non)                      -- junk tags
    a.1 a.2

abbrev B : A → Type := fun a => PSigma (Tel a)

noncomputable abbrev TmW : Type := WT.W (K := A) (A := A) B id

noncomputable instance decA : DecidableEq A := WT.decEqAll A

/-! ### The labels, and the dispatch

`⟨t, d⟩` with `t` a literal is the label; the dispatch is a `Nat.rec` on the
branch index whose motive is `fun j => Tel a j → TmW`, with the junk arm
discharged from `Non`. Both are the tag scheme's shapes with `a` in place of
`a.1`, which is the point. -/

abbrev lVar (m : Nat) : A := ⟨0, ⟨m, ⟨⟩⟩⟩
abbrev lApp (n : Nat) : A := ⟨1, ⟨n, ⟨⟩⟩⟩
abbrev lMix (k : Nat) (c : Bool) : A := ⟨2, ⟨k, ⟨c, ⟨⟩⟩⟩⟩

noncomputable def dVar (m : Nat) : B (lVar m) → TmW := fun b => PEmpty.elim b.2

noncomputable def dApp (n : Nat) (f : Fin n → TmW) : B (lApp n) → TmW := fun b =>
  Nat.rec (motive := fun j => Tel (lApp n) j → TmW)
    (fun tel => f tel.1)
    (fun _ _ tel => PEmpty.elim tel)
    b.1 b.2

noncomputable def dMix (k : Nat) (c : Bool) (f : Fin k → TmW) (g : TmW) :
    B (lMix k c) → TmW := fun b =>
  Nat.rec (motive := fun j => Tel (lMix k c) j → TmW)
    (fun tel => f tel.1)
    (fun j _ => Nat.rec (motive := fun j' => Tel (lMix k c) (j' + 1) → TmW)
      (fun _ => g)
      (fun _ _ tel => PEmpty.elim tel)
      j)
    b.1 b.2

/-! ### The constructors -/

noncomputable def cVar (m : Nat) : TmW := WT.sup (B' := B) (tg := id) (lVar m) (dVar m)
noncomputable def cApp (n : Nat) (f : Fin n → TmW) : TmW :=
  WT.sup (B' := B) (tg := id) (lApp n) (dApp n f)
noncomputable def cMix (k : Nat) (c : Bool) (f : Fin k → TmW) (g : TmW) : TmW :=
  WT.sup (B' := B) (tg := id) (lMix k c) (dMix k c f g)

/-! ### The eta lemmas — the dispatch rebuilt from an abstract `f` is `f`

One per constructor, and this is the whole of the per-constructor glue. Each is
`funext` then the branch-index cascade: the real arms are `rfl` by `PSigma` and
`PUnit` structure eta, and the junk arms are `PEmpty.elim`. -/

theorem etaVar (d : D 0) (f : B ⟨0, d⟩ → TmW) : dVar d.1 = f := by
  funext b; exact PEmpty.elim b.2

theorem etaApp (d : D 1) (f : B ⟨1, d⟩ → TmW) :
    dApp d.1 (fun i => f ⟨0, ⟨i, ⟨⟩⟩⟩) = f := by
  funext b
  obtain ⟨j, tel⟩ := b
  cases j with
  | zero => rfl
  | succ _ => exact PEmpty.elim tel

theorem etaMix (d : D 2) (f : B ⟨2, d⟩ → TmW) :
    dMix d.1 d.2.1 (fun i => f ⟨0, ⟨i, ⟨⟩⟩⟩) (f ⟨1, ⟨⟩⟩) = f := by
  funext b
  obtain ⟨j, tel⟩ := b
  cases j with
  | zero => rfl
  | succ j' =>
    cases j' with
    | zero => rfl
    | succ _ => exact PEmpty.elim tel

/-! ### `F` — the core's minor, as the generator hoists it

A `Nat.rec` cascade on the tag whose motive takes the **data** as an argument,
exactly as `Tel`'s does. Each real arm applies the target's own minor to the
projections of `d` and to the children read out of `f`, and then transports
along that constructor's eta lemma; the junk arm is discharged from `Non`.

The transport is a `cast` along `congrArg`, and it is what disappears at an ι
rule: there the equation is between a dispatch and *itself*, so the proof is
`rfl` by definitional proof irrelevance and the `cast` computes away. -/

section Rec
variable {C : TmW → Sort v}
  (mv : (m : Nat) → C (cVar m))
  (ma : (n : Nat) → (f : Fin n → TmW) → ((i : Fin n) → C (f i)) → C (cApp n f))
  (mm : (k : Nat) → (c : Bool) → (f : Fin k → TmW) → (g : TmW) →
        ((i : Fin k) → C (f i)) → C g → C (cMix k c f g))

noncomputable def F : (a : A) → (f : B a → TmW) →
    ((b : B a) → C (f b)) → C (WT.sup (B' := B) (tg := id) a f) := fun a =>
  Nat.rec
    (motive := fun t => (d : D t) → (f : B ⟨t, d⟩ → TmW) →
      ((b : B ⟨t, d⟩) → C (f b)) → C (WT.sup (B' := B) (tg := id) ⟨t, d⟩ f))
    (fun d f _ => cast (congrArg (fun z => C (WT.sup (B' := B) (tg := id) ⟨0, d⟩ z))
        (etaVar d f)) (mv d.1))
    (fun t ih =>
      match t, ih with
      | 0, _ => fun d f ihf =>
        cast (congrArg (fun z => C (WT.sup (B' := B) (tg := id) ⟨1, d⟩ z)) (etaApp d f))
          (ma d.1 (fun i => f ⟨0, ⟨i, ⟨⟩⟩⟩) (fun i => ihf ⟨0, ⟨i, ⟨⟩⟩⟩))
      | 1, _ => fun d f ihf =>
        cast (congrArg (fun z => C (WT.sup (B' := B) (tg := id) ⟨2, d⟩ z)) (etaMix d f))
          (mm d.1 d.2.1 (fun i => f ⟨0, ⟨i, ⟨⟩⟩⟩) (f ⟨1, ⟨⟩⟩)
            (fun i => ihf ⟨0, ⟨i, ⟨⟩⟩⟩) (ihf ⟨1, ⟨⟩⟩))
      | _ + 2, _ => fun d _ _ => PEmpty.elim d)
    a.1 a.2

/-- The recursor, at Lean's own `Tm.rec` signature. -/
noncomputable def rec' : (w : TmW) → C w :=
  WT.Wrec (B' := B) (tg := id) (C := C) (F mv ma mm)

/-! ### The three ι rules -/

theorem iotaVar (m : Nat) : rec' mv ma mm (cVar m) = mv m :=
  WT.Wrec_iota (B' := B) (tg := id) (C := C) (F mv ma mm) (lVar m) (dVar m)

theorem iotaApp (n : Nat) (f : Fin n → TmW) :
    rec' mv ma mm (cApp n f) = ma n f (fun i => rec' mv ma mm (f i)) :=
  WT.Wrec_iota (B' := B) (tg := id) (C := C) (F mv ma mm) (lApp n) (dApp n f)

theorem iotaMix (k : Nat) (c : Bool) (f : Fin k → TmW) (g : TmW) :
    rec' mv ma mm (cMix k c f g)
      = mm k c f g (fun i => rec' mv ma mm (f i)) (rec' mv ma mm g) :=
  WT.Wrec_iota (B' := B) (tg := id) (C := C) (F mv ma mm) (lMix k c) (dMix k c f g)

end Rec

end WU

/-! ## The pins

**Twice, as `MODELGEN.md` §4 requires**: the model's recursor against a
transcription of `Tm.rec`, and `Tm.rec`'s own type against that same
transcription — here in one step, by substituting the model's carrier and
constructors into the type Lean minted and asking `isDefEq`. -/

/-- info: rec' is Tm.rec at the model -/
#guard_msgs in
open Lean Meta in
run_meta do
  let some (.recInfo rv) := (← getEnv).find? ``Tm.rec | throwError "no Tm.rec"
  let subst : Expr → Expr := fun e => e.replace fun s => match s with
    | .const ``Tm _     => some (.const ``WU.TmW [])
    | .const ``Tm.var _ => some (.const ``WU.cVar [])
    | .const ``Tm.app _ => some (.const ``WU.cApp [])
    | .const ``Tm.mix _ => some (.const ``WU.cMix [])
    | _ => none
  let some ci := (← getEnv).find? ``WU.rec' | throwError "no WU.rec'"
  let got := ci.type.instantiateLevelParams ci.levelParams (rv.levelParams.map .param)
  unless ← isDefEq (subst rv.type) got do throwError "not Lean's rule"
  logInfo "rec' is Tm.rec at the model"

/-- info: 'WT.W' does not depend on any axioms -/
#guard_msgs in #print axioms WT.W
/-- info: 'WT.Wrec_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WT.Wrec_iota
/-- info: 'WT.decEqAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WT.decEqAll
/-- info: 'WU.iotaApp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WU.iotaApp
/-- info: 'WU.iotaMix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WU.iotaMix
