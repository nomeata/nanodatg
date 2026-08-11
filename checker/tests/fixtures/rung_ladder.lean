/-
# Walking up the rungs deliberately

**What breaks if any of `R2 … R5` or `Mixed` stops deriving.** `ctor_spec` used
to raise every field type's typing **into `U₁`** and run the summand induction
there, which is a decline the moment a field itself lives at `Sort 2` or above,
because cumulativity cannot lower. `cumul::summand_obligations_at` / `summand_at`
/ `tags_at` now run the chain at the declaration's **own** resultant rung
(`5a89420`).

The corpus's witnesses for that fix are `Prod`, `TypeWithTypeField`,
`TypeWithTypeFieldPoly` and `RBTree.{1}` — every one found by accident, and every
one exactly **one** rung up. A fix that hardcoded the next rung rather than
generalising would pass all four. This file walks the ladder on purpose:

| declaration | field sorts | own resultant sort |
| --- | --- | --- |
| `R2` | `Sort 1` | `Sort 2` |
| `R3` | `Sort 2` | `Sort 3` |
| `R4` | `Sort 3` | `Sort 4` |
| `R5` | `Sort 4` | `Sort 5` |
| `Mixed` | `Sort 1`, `Sort 2`, `Sort 3` | `Sort 4` |

`R2` is the corpus's case and is here as the control: if it fails, the failure is
not about rungs. `R3` is the first rung the fix bought. `R4` and `R5` are the two
that say it is a generalisation and not an increment — `mini::interp::CUMUL_HEIGHT`
is 8, so `Sort 5` is comfortably inside the table and a failure there is about the
summand chain, not about the tower running out.

`Mixed` is the shape none of the four corpus witnesses has: **three fields at
three different rungs, none of them the declaration's own.** Running the chain
"at the declaration's own rung" means each field's typing is raised *up* to
`Sort 4` from a different starting point, and a chain that quietly assumed all
fields share a rung — or that the first field's rung is the chain's — is right on
every single-field declaration and wrong here. Three fields, not two: with two,
"take the max" and "take the last" agree whenever they are ordered, and the
declared order here is ascending precisely so that the *last* field is not the
answer either — `Mixed` sits at `Sort 4` while its last field is at `Sort 3`.

Every declaration is an `inductive` with one constructor rather than a
`structure`, so that no projection is generated: `Expr.proj` is an
un-interpreted clause in mini and a projection would block these pairs for a
reason that has nothing to do with rungs.

The `def`s are the pairs. Each names both the carrier and the constructor, so a
regression in either shows up as a named declaration and not as a count.
-/
prelude

--#export R2 R3 R4 R5 Mixed
--#export r2Ty r2Mk r3Ty r3Mk r4Ty r4Mk r5Ty r5Mk mixedTy mixedMk

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- The control: one field at `Sort 1`, the rung the corpus already covers. -/
inductive R2 : Type 1 where
  | mk : Type → R2

/-- The first rung the fix bought: a field at `Sort 2`, which no raise into
    `U₁` can reach. -/
inductive R3 : Type 2 where
  | mk : Type 1 → R3

/-- Two rungs past the corpus. -/
inductive R4 : Type 3 where
  | mk : Type 2 → R4

/-- Three rungs past the corpus, and still well inside `CUMUL_HEIGHT`. -/
inductive R5 : Type 4 where
  | mk : Type 3 → R5

/-- Three fields at three distinct rungs, the declaration's own rung above all
    of them, and the fields in ascending order so that neither "the first
    field's rung" nor "the last field's rung" is the right answer. -/
inductive Mixed : Type 3 where
  | mk : Type → Type 1 → Type 2 → Mixed

def r2Ty : Type 1 := R2
def r2Mk (a : Type) : R2 := R2.mk a
def r3Ty : Type 2 := R3
def r3Mk (a : Type 1) : R3 := R3.mk a
def r4Ty : Type 3 := R4
def r4Mk (a : Type 2) : R4 := R4.mk a
def r5Ty : Type 4 := R5
def r5Mk (a : Type 3) : R5 := R5.mk a
def mixedTy : Type 3 := Mixed
def mixedMk (a : Type) (b : Type 1) (c : Type 2) : Mixed := Mixed.mk a b c
