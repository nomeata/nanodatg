/-
# `Squash.{u}` at `u := 1` — a class-(P) declaration whose resultant sort is a
# nonzero numeral

**This fixture exists to open a branch that is closed for want of a test.**

`mini` decides the eliminator trichotomy on the declaration's **own** resultant
level expression, never on the σ-substituted numeral
(`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3): `Sort u` is not `provably_nonzero`, so
`Squash.{u}` is class (P) *at every `u`*, including `u := 1` where the
substituted sort is `Sort 1`. Reading the substituted type instead would hand a
possibly-`Prop` declaration a W-type, and that bug was real — it was caught by
`a_possibly_prop_declaration_never_acquires_a_w_type` when `eliminator_class`
was rewritten (`000f74b`).

Having got the class right, `zoneb::build_trunc` then **declines** when the
ground resultant level is not `0`, with `ind-spec(Squash: class (P) above Prop)`.
Tara established that this case is reachable, that deriving it would be sound,
and that the fix is one line — and then established that **no file in `good/`
can exercise it**, because every class-(P) declaration in the corpus has
resultant sort literally `Sort 0`. The only witnesses are in `bad/`, which is
rejected at acceptance before any clause runs. This is the `good/` witness.

# Why `Squash` and not `bad/large-elim-param.ndjson`'s `MyBool.{u}`

`MyBool` reaches class (P) by having two constructors, which fails §2.6.2's
reason 2 on the coarse clause — the count. `Squash` reaches it the subtle way:
**one** constructor, whose single field `a : α` infers as `Sort u`, fails
`is_zero`, and is *not* rescued by the result indices, because the result spine
`Squash α` carries the **parameter** `α` and not the field. That is the same
`y ∈ e` clause `elim_class_trichotomy.lean` approaches from the succeeding side
(`IdxHit`), here approached from the failing side, and it is the clause with
exactly one corpus witness.

**Lean adjudicates rather than we do.** The export carries `Squash.rec`, so the
test compares the computed class against the exported recursor exactly as the
corpus test does. If Lean puts `Squash` on the other side, our reading of
`large_elim_test_aux` is wrong and that is worth more than the fixture.

# Both instantiations, on purpose

`mini`'s σ schedule is the pre-pass's: an instantiation appears only if the file
demands it. `squashProp` demands `u := 0` and `squashType` demands `u := 1`, so
both are scheduled and the nonzero numeral is actually reached. Without
`squashType` the fixture would measure the `Sort 0` case twice and prove
nothing about the branch it exists for.

**The expectations pinned in `designed.rs` are the *current* behaviour, decline
and all.** When the one-line change lands, the `u := 1` row inverts from
`ind-spec(Squash: class (P) above Prop)` to a derived carrier, and this file is
what proves it.
-/
prelude
universe u

--#export P0 A Squash Squash.rec squashPropTy squashProp squashTypeTy squashType

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- An inhabited `Prop`, to instantiate `Squash` at `u := 0`. Inhabited on
    purpose: `‖∅‖ = ∅` makes a truncation clause pass vacuously, which is
    exactly how the `Quot` equivalence-class clause looked right. -/
inductive P0 : Prop where
  | triv : P0

/-- A `Type`, to instantiate `Squash` at `u := 1`. -/
inductive A : Type where
  | a0 : A

-- `bootstrap.inductiveCheckResultingUniverse` is how `Init.Prelude` declares
-- `PUnit.{u}` and `PProd.{u,v}`; it is off here for the same reason, so that
-- the resultant sort stays a bare universe parameter.
set_option bootstrap.inductiveCheckResultingUniverse false in
/-- One constructor, one field at `Sort u`, and the result spine carries the
    parameter rather than the field. -/
inductive Squash (α : Sort u) : Sort u where
  | mk : α → Squash α

/-- `u := 0`: `Squash P0 : Prop`, the case the corpus already covers. -/
def squashPropTy : Prop := Squash P0
def squashProp : Squash P0 := Squash.mk P0.triv

/-- `u := 1`: `Squash A : Type`, the case nothing in `good/` reaches. -/
def squashTypeTy : Type := Squash A
def squashType : Squash A := Squash.mk A.a0
