/-
# The shape mutual inductives actually get used for

Every other fixture in this group isolates one property. This one is the
**realistic** case: an expression/statement pair from a toy language, which is
the example every account of mutual inductives opens with and the reason the
feature exists.

It is a *three*-member block rather than the textbook two, and the third member
is what makes it honest. The textbook version writes

```text
inductive Stm | seq : List Stm → Stm
```

which is a **nested** inductive, not a mutual one — `List` is an inductive
applied to the type being defined, and Lean compiles it by generating an
auxiliary copy of `List`. Nesting is a separate feature with a separate
encoding, so this file spells the list out as `Stms`, a third mutual member.
That is exactly what Lean's own nested-inductive compiler produces internally,
so the three-member block here is the shape a nested declaration is *reduced
to*, not an avoidance of it.

# What the three members are not symmetric in

`Exp` has three constructors, `Stm` three, `Stms` two — eight minors in total,
in a block order no rotation preserves. The recursive occurrences cross in both
directions (`Exp.call` holds a `Stm`, `Stm.assign` holds an `Exp`), and
`Stms.cons` holds one of each of `Stm` and `Stms`, so a single minor carries two
induction hypotheses stated at two *different* motives. A recursor builder that
takes the induction hypothesis's motive from the constructor's owner rather than
from the field's own type is wrong at exactly that one minor and right at the
other seven.

No constructor has a function-typed recursive argument; the aux encoding for a
mutual family is indexed, and an indexed function-typed recursive argument is
refused by `zoneb.rs`'s indexed branch today.
-/
prelude

--#export Exp Stm Stms
--#export expTy stmTy stmsTy expAdd expCall stmAssign stmSeq stmsCons

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- Literals and variable names, without `Nat`'s literal machinery. -/
inductive N : Type where
  | z : N
  | s : N → N

mutual

/-- Three constructors, one of them crossing into `Stm`. -/
inductive Exp : Type where
  | lit : N → Exp
  | add : Exp → Exp → Exp
  | call : Stm → Exp → Exp

/-- Three constructors, crossing into `Exp` and into `Stms`. -/
inductive Stm : Type where
  | skip : Stm
  | assign : N → Exp → Stm
  | seq : Stms → Stm

/-- The spelled-out list: what a nested `List Stm` would be compiled to.
    `cons` is the one constructor carrying two induction hypotheses at two
    different motives. -/
inductive Stms : Type where
  | nil : Stms
  | cons : Stm → Stms → Stms

end

def expTy : Type := Exp
def stmTy : Type := Stm
def stmsTy : Type := Stms
def expAdd (a b : Exp) : Exp := Exp.add a b
def expCall (s : Stm) (e : Exp) : Exp := Exp.call s e
def stmAssign (n : N) (e : Exp) : Stm := Stm.assign n e
def stmSeq (l : Stms) : Stm := Stm.seq l
def stmsCons (h : Stm) (t : Stms) : Stms := Stms.cons h t
