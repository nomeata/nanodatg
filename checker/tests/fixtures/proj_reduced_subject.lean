/-
# A projection whose **subject** has to reduce before the ι step fires

`mini::kernel`'s `whnf` reduces a projection by reducing its subject and then
reading the field off the constructor application. It reduced the subject with
the acceptance-only `self.whnf(s)`, which threads no certificate, so the arm
guarded on `s2 == s` — *the subject was already a constructor application* —
and minted `proj(PProd)` for everything else. `proj_data::iota`'s header called
that decline unreachable: "`093_projRed`'s subject satisfies it. No corpus
member exercises the decline."

Both halves of that sentence were true and the conclusion was not. **Every**
projection Lean's structural-recursion compiler emits takes the decline:
`Nat.brecOn` is literally `(Nat.brecOn.go motive t F).1`, so the subject is a
definition that has to δ-unfold and then ι-reduce before a constructor is
anywhere near head position. The corpus contained one hand-written projection
whose subject was already `Pair.mk …`, and it stood in for the whole clause.

This file is the decline, with no `Nat` and no `brecOn` in it.

## The cells

| theorem | subject | what it exercises |
| --- | --- | --- |
| `ctorFst`, `ctorSnd` | `Pair.mk x y`, already a constructor | **control** — the case the old guard admitted |
| `defFst`, `defSnd` | `mk2 α x y`, one δ | the decline, at its shallowest |
| `recFst` | `pick α x y Two.a`, δ then ι | the subject moves by *reduction*, not only unfolding |
| `nestedFst` | `(mk2 α (mk2 α x y).fst y).fst` | a projection **inside** the subject of a projection |

`nestedFst` is the depth axis and it is not decoration: the fix peels `⟦s⟧` off
the projection's own recorded interpretation rather than re-inferring it
(`proj_data::subject_of`), because `infer_type` of a projection infers its own
subject and the obvious route is exponential in exactly this nesting. A fixture
with no nesting is passed by the exponential version too.

`recFst` separates "the subject unfolds" from "the subject reduces": a fix that
only δ-unfolded the head would pass `defFst` and fail here.

Both fields are projected everywhere for the reason
`proj_reduced_carrier.lean` gives: at one field the prefix is empty and the
rung fold is the identity.

`Two` and its `pick` are not `Bool`, and `Pair` is not `PProd`, for the same
reason as in the sibling file — the finding is that none of this is about the
declarations `Nat` happens to use.
-/
prelude

--#export Eq Two Pair mk2 pick
--#export ctorFst ctorSnd defFst defSnd recFst nestedFst

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive Two : Type where
  | a : Two
  | b : Two

structure Pair (α : Type) (β : Type) : Type where
  fst : α
  snd : β

/-- A subject that is one δ away from a constructor application. -/
def mk2 (α : Type) (x : α) (y : α) : Pair α α := Pair.mk x y

/-- A subject that is δ **and then ι** away: which pair you get is computed. -/
noncomputable def pick (α : Type) (x : α) (y : α) (t : Two) : Pair α α :=
  Two.rec (motive := fun _ => Pair α α) (Pair.mk x y) (Pair.mk y x) t

-- ── the control: the subject is already a constructor application ───────────

theorem ctorFst (α : Type) (x : α) (y : α) : Eq (Pair.mk x y).fst x := Eq.refl _
theorem ctorSnd (α : Type) (x : α) (y : α) : Eq (Pair.mk x y).snd y := Eq.refl _

-- ── one δ ───────────────────────────────────────────────────────────────────

theorem defFst (α : Type) (x : α) (y : α) : Eq (mk2 α x y).fst x := Eq.refl _
theorem defSnd (α : Type) (x : α) (y : α) : Eq (mk2 α x y).snd y := Eq.refl _

-- ── δ then ι: the subject *reduces* rather than merely unfolding ────────────

theorem recFst (α : Type) (x : α) (y : α) : Eq (pick α x y Two.a).fst x := Eq.refl _

-- ── a projection inside a projection's subject ──────────────────────────────

theorem nestedFst (α : Type) (x : α) (y : α) :
    Eq (mk2 α (mk2 α x y).fst y).fst x := Eq.refl _
