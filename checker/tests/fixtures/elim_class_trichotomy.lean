/-
# Carneiro §2.6.2, at the shapes the corpus does not contain

**What breaks if any row of the table in `designed.rs` moves.**
`zoneb::large_eliminating` computes the rule from the declaration:

1. the resultant sort is **provably nonzero**; or
2. there is **at most one** constructor, and each of its non-recursive
   arguments is either a proposition or **appears among the result indices**.

`tutorial_eliminator_class_matches_the_export_recursor` checks that computation
against the exported recursor over 29 corpus declarations with zero
disagreements. What it cannot check is the clauses the corpus does not witness,
and there are three:

* **`y ∈ e` has exactly one witness in the whole corpus — `Acc`.** One witness
  for a clause is the thinnest coverage there is, and it is the subtle half of
  the rule: a field that would otherwise sink large elimination is rescued by
  occurring among the result indices. `IdxHit` is that case; `IdxMiss` differs
  from it by **one extra field of the same type** that does not occur in an
  index, and must come out small. `IdxUnder`'s field occurs *inside* a result
  index rather than *being* one, which is where "appears among" has to mean
  occurrence and not equality.
* **The constructor-count boundary.** The rule says *at most* one. `Zero` has
  none, `OneNoField` one, `TwoAllProp` two — and `TwoAllProp` must be small
  **even though every one of its fields is a proposition**, because the count
  fails before the field test is reached.
* **A `Prop` field against a `Type` field, everything else equal.**
  `OnePropField` and `OneTypeField` differ in exactly one character of one field
  type and must land on opposite sides. That single difference is the whole
  discriminant, and it is what makes `PredWithTypeField` class (P).

Every declaration here is `Prop`-valued, so reason 1 never fires and reason 2 is
the *only* thing being measured. A file where some rows were `Type`-valued would
pass with reason 2 unimplemented. The reason-1 side, at a bare universe
parameter, is `squash_at_nonzero_sigma.lean`.

The computed class is compared against the **exported recursor** here exactly as
it is on the corpus, so a disagreement is a finding about the reading of
§2.6.2 or about Lean, not a test to relax.
-/
prelude

--#export A Wrap Zero OneNoField TwoAllProp OnePropField OneTypeField
--#export IdxHit IdxMiss IdxUnder
--#export Zero.rec OneNoField.rec TwoAllProp.rec OnePropField.rec OneTypeField.rec
--#export IdxHit.rec IdxMiss.rec IdxUnder.rec

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- A `Type`, to be a non-propositional field. -/
inductive A : Type where
  | a0 : A

/-- A carrier for a result index that *contains* a field without being one. -/
inductive Wrap (α : Type) : Type where
  | wrap : α → Wrap α

-- ── the constructor-count boundary ──────────────────────────────────────────

/-- **Zero** constructors: "at most one" holds vacuously. -/
inductive Zero : Prop where

/-- **One** constructor, no fields: the field test is vacuous. -/
inductive OneNoField : Prop where
  | mk : OneNoField

/-- **Two** constructors, and every field of both is a proposition. The count
    fails before the fields are looked at, so this must still be small. -/
inductive TwoAllProp : Prop where
  | l : OneNoField → TwoAllProp
  | r : OneNoField → TwoAllProp

-- ── a Prop field against a Type field, everything else equal ────────────────

/-- One constructor, one field, and the field **is** a proposition. -/
inductive OnePropField : Prop where
  | mk : OneNoField → OnePropField

/-- The same, with the field's type changed from `OneNoField` to `A` and
    nothing else. -/
inductive OneTypeField : Prop where
  | mk : A → OneTypeField

-- ── `y ∈ e`: the field is rescued by the result indices, or is not ──────────

-- **Index 0's result term is computed on purpose.** Lean's
-- `fixedIndicesToParams` promotes an index that is a fixed constructor field
-- into a *parameter*, invisibly in the source and visibly only as `numIndices`
-- in the export. The first draft of these two wrote
-- `IdxHit (α : Type) : α → Prop | mk : (a : α) → IdxHit α a` and Lean exported
-- `numParams=2, numIndices=0` — a declaration with no indices at all, in which
-- `IdxHit` is large because its constructor has no fields left and `IdxMiss` is
-- small because `b` is a plain non-propositional field. Both verdicts right,
-- the `y ∈ e` clause never reached. Computing index 0 blocks the promotion, and
-- because parameters are a prefix it keeps index 1 an index too, so the field
-- `a` really is a result index. Lean confirms: `numParams=1, numIndices=2`.

/-- The field `a : α` is not a proposition, and is **rescued** by being one of
    the result indices. This is `Acc`'s clause without `Acc`'s function-typed
    recursive argument in the way, and the second witness for it in the
    project. -/
inductive IdxHit (α : Type) : Wrap α → α → Prop where
  | mk : (a : α) → IdxHit α (Wrap.wrap a) a

/-- `IdxHit` plus **one** extra field of the same type that is not a result
    index. Nothing else differs. -/
inductive IdxMiss (α : Type) : Wrap α → α → Prop where
  | mk : (a : α) → (b : α) → IdxMiss α (Wrap.wrap a) a

/-- The field occurs *inside* the single result index rather than being it, so
    "appears among the result indices" has to mean occurrence. -/
inductive IdxUnder (α : Type) : Wrap α → Prop where
  | mk : (a : α) → IdxUnder α (Wrap.wrap a)
