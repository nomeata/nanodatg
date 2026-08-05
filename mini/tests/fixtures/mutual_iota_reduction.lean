/-
# The recursor rules, fired rather than inspected

Every other fixture in this group is checked by comparing the recursor mini
*generates* against the one Lean *exports*. That comparison is syntactic, and it
is the strongest oracle zone A has — but a rule can be right on paper and never
reach the reduction machinery, because whnf locates the major argument by
arithmetic (`num_params + num_motives + num_minors + num_indices`) and that
arithmetic used to have `num_motives` written as a literal `1`.

So this file states the rules as **theorems whose proof is reflexivity**. Each
one forces mini's whnf to fire a mutual ι rule and to agree with the right-hand
side the fixture wrote by hand.

| theorem | fires | the induction hypothesis it produces |
| --- | --- | --- |
| `aBase` | `A.rec` at `A.a0` | none — the base case, which needs no ι argument |
| `aStep` | `A.rec` at `A.aB` | `B.rec` at the same motives and minors |
| `bStep` | `B.rec` at `B.bC` | `C.rec` at the same motives and minors |
| `cStep` | `C.rec` at `C.cA` | `A.rec` at the same motives and minors |

Three step rules, at three members, each producing its induction hypothesis at a
*different* member — so a rule builder that took the recursor from the
constructor's owner rather than from the recursive field's own type is wrong at
all three, and one that clamped to the first member is wrong at two.

**`aSize`, `bSize` and `cSize` are three separate `def`s over the same motives
and the same six minors.** That is what makes the right-hand sides sayable at
all: the induction hypothesis a mutual ι rule produces is *literally*
`B.rec params motives minors …` with the caller's own motives and minors, so
`N.s (bSize b)` is only definitionally the reduct if the shared prefix really is
shared. Give `bSize` a different minor and `aStep` stops being `rfl`.

`Eq` is declared here because the file is `prelude`. It is Lean's own shape, and
mini interprets it by a named clause (`mini::direct`), so its presence adds no
new translation obligation — only a way to write an equation down.
-/
prelude

--#export A B C
--#export aSize bSize cSize aBase aStep bStep cStep

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The value the three sizes return. -/
inductive N : Type where
  | z : N
  | s : N → N

mutual

inductive A : Type where
  | a0 : A
  | aB : B → A

inductive B : Type where
  | b0 : B
  | bC : C → B

inductive C : Type where
  | c0 : C
  | cA : A → C

end

/-- Three motives and six minors, positional; the same list in all three. -/
noncomputable def aSize : A → N :=
  @A.rec (fun _ => N) (fun _ => N) (fun _ => N)
    N.z (fun _ ih => N.s ih) N.z (fun _ ih => N.s ih) N.z (fun _ ih => N.s ih)

noncomputable def bSize : B → N :=
  @B.rec (fun _ => N) (fun _ => N) (fun _ => N)
    N.z (fun _ ih => N.s ih) N.z (fun _ ih => N.s ih) N.z (fun _ ih => N.s ih)

noncomputable def cSize : C → N :=
  @C.rec (fun _ => N) (fun _ => N) (fun _ => N)
    N.z (fun _ ih => N.s ih) N.z (fun _ ih => N.s ih) N.z (fun _ ih => N.s ih)

theorem aBase : Eq (aSize A.a0) N.z := Eq.refl _
theorem aStep (b : B) : Eq (aSize (A.aB b)) (N.s (bSize b)) := Eq.refl _
theorem bStep (c : C) : Eq (bSize (B.bC c)) (N.s (cSize c)) := Eq.refl _
theorem cStep (a : A) : Eq (cSize (C.cA a)) (N.s (aSize a)) := Eq.refl _
