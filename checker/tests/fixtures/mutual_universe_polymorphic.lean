/-
# A mutual block at two level parameters, and the recursor's third

A mutual block's members share their level parameters exactly as they share
their parameter telescope, and the recursor of each member carries **one extra**
level — the motive's — in front of them. This file has two declared levels, `u`
and `v`, so the recursor's level list is `w u v` and neither "the recursor's
levels are the type's levels" nor "there is exactly one extra level, prepended
to a singleton" can be confused with the truth.

`mini/src/convert.rs`'s `audit_recursor_shape` is the check this exercises: it
compares mini's generated recursor's level list against the export's, accepting
either the type's own list or that list with one level prepended. Two declared
levels means a builder that appended rather than prepended is caught (`u v w` ≠
`w u v`), and a builder that emitted `w u` is caught by length.

# The resultant sort is `max u v`, and it is not any member's field level

Each member's resultant sort is `Type (max u v)` while `UA.mk`'s first field is
at `u` and `UB.mk`'s at `v`. So the universe bound each constructor's fields are
checked against (`assertLevelLe u indLevel`) is a `max` neither of its own fields
sits at, and it is the *same* bound for all three members — a mutual block's
members must agree on their resultant universe. A builder that took the bound
from the member being checked rather than from the block would still be right
here; a builder that took it from the member's *first field* would not.

Three members, and the cycle runs `UA → UB → UC → UA`, so the level parameters
travel around the cycle with the recursive occurrences.
-/
prelude

--#export UA UB UC
--#export uaTy ubTy ucTy uaMk ubMk ucMore

universe u v

unsafe axiom lcErased : Type u
unsafe axiom lcAny : Type u
unsafe axiom lcVoid : Type u

mutual

/-- Holds an `α : Type u`. -/
inductive UA (α : Type u) (β : Type v) : Type (max u v) where
  | mk : α → UB α β → UA α β

/-- Holds a `β : Type v`. -/
inductive UB (α : Type u) (β : Type v) : Type (max u v) where
  | mk : β → UC α β → UB α β

/-- Holds neither, and closes the cycle. -/
inductive UC (α : Type u) (β : Type v) : Type (max u v) where
  | done : UC α β
  | more : UA α β → UC α β

end

def uaTy (α : Type u) (β : Type v) : Type (max u v) := UA α β
def ubTy (α : Type u) (β : Type v) : Type (max u v) := UB α β
def ucTy (α : Type u) (β : Type v) : Type (max u v) := UC α β
def uaMk (α : Type u) (β : Type v) (a : α) (b : UB α β) : UA α β := UA.mk a b
def ubMk (α : Type u) (β : Type v) (b : β) (c : UC α β) : UB α β := UB.mk b c
def ucMore (α : Type u) (β : Type v) (a : UA α β) : UC α β := UC.more a
