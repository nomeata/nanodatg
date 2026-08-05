/-
# A mutual block that is *also* indexed

The aux encoding for a mutual family is itself an indexed inductive — the tag
that says which member a value belongs to is an index. So a mutual family whose
members already carry indices of their own is the case where the encoding's
index and the family's indices have to coexist, and the recursor's index
telescope is per-member rather than shared.

**Per-member is the whole point of putting it in a separate file.** Parameters
are shared across a mutual block by kernel rule; indices are **not**. Each
`Tᵢ.rec` binds the indices of `Tᵢ` only, after the motives and minors that are
shared, and each motive `motive_j` binds the indices of `T_j`. Here all three
members happen to be indexed by one `N`, which is deliberate: with three
*differently* indexed members a wrong index count would be a type error caught
by arity alone, and this file is meant to catch the subtler failure where the
counts agree and the *binding site* does not.

# The indices are genuinely indices

`Lean.Elab.Command`'s `fixedIndicesToParams` promotes an index that is the same
variable in every constructor result and every recursive occurrence into a
parameter, invisibly. Here every constructor's result index is `N.s n` while the
recursive occurrence is at `n`, so the index varies and no promotion happens —
`numIndices = 1` for all three members. (`indexed_result_index_shape.lean` is
the fixture that pins the promotion rule itself.)

`T0` has a base case at the closed index `N.z`; `T1` and `T2` have none, so two
of the three members are **empty** at every index — which is fine and is not
what the file measures, but it does mean nothing here builds a closed inhabitant
of `T1` or `T2`, and the `def`s take one as an argument instead.

The cycle is `T0 → T2 → T1 → T0`, i.e. the recursion runs *against* declaration
order, so a builder that assumed a member only recurses into its predecessors is
wrong at two of the three.
-/
prelude

--#export T0 T1 T2
--#export t0Ty t1Ty t2Ty t0Base t0Step t1Step t2Step

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- The index type. -/
inductive N : Type where
  | z : N
  | s : N → N

mutual

/-- The only member with a base case. Recurses into `T2`. -/
inductive T0 : N → Type where
  | base : T0 N.z
  | step : (n : N) → T2 n → T0 (N.s n)

/-- Recurses into `T0`. -/
inductive T1 : N → Type where
  | step : (n : N) → T0 n → T1 (N.s n)

/-- Recurses into `T1`. -/
inductive T2 : N → Type where
  | step : (n : N) → T1 n → T2 (N.s n)

end

def t0Ty (n : N) : Type := T0 n
def t1Ty (n : N) : Type := T1 n
def t2Ty (n : N) : Type := T2 n
def t0Base : T0 N.z := T0.base
def t0Step (n : N) (x : T2 n) : T0 (N.s n) := T0.step n x
def t1Step (n : N) (x : T0 n) : T1 (N.s n) := T1.step n x
def t2Step (n : N) (x : T1 n) : T2 (N.s n) := T2.step n x
