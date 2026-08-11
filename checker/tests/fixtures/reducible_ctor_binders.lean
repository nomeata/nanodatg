/-
# A recursive field's type is Lean's *syntax*, and the eliminator's atom is not

A constructor's field types are written down by the `inductive` command exactly
as the user spelled them; what makes a field *recursive* is that it **reduces**
to the declaration's own spine. When the two differ, mini's interpretation of
them is two different terms, and the eliminator's minor premise binds the one
while `derived`'s atom is stated at the other.

`good/tutorial`'s `052_reduceCtorParam`, `113_reduceCtorParamRefl` and
`114_reduceCtorParamRefl2` are the corpus witnesses and they were the last
three untranslated rows on it. They are also *obfuscated*: each carries this
defect and a second one at the same constructor, so the row that failed never
said which. This fixture is the half that surface Lean can express, separated
and indexed.

| declaration | recursive slots | the bridge it needs |
|---|---|---|
| `Spelled` | one plain, spelled `Spelled α`                     | none — the control |
| `Cod`     | one plain, `constType (Cod α) (Cod α)`             | `at_atom`'s set, composed |
| `FunCod`  | **three** function-typed: spelled, then **two different** aliases | `push_into_pi`, at slots 1 and 2 of 3 |

`Spelled` is the control: it says that a recursive field is not on its own what
the walk could not do. Both witnesses are `np = 1`, because the bridge is built
per constructor at the caller's own `⟦p⃗⟧` and a parameterless declaration would
not say whether it arrived in the right frame.

# The other half of the corpus rows is not expressible here, and that is a
# measurement rather than an omission

`052`/`113`/`114` also have a constructor whose **parameter binder** is
`id (Type 1) Type` while the type former's and the recursor's are `Sort 1` —
definitionally equal, syntactically two terms, and `Interp::beta_spine`'s
per-level premise is at the λ's own domain. That shape cannot be exported from
surface syntax: writing `inductive T (α : id Type) : Type` puts the alias on
*all three* of the type former, the constructors and the recursor, which is a
uniform frame and exercises nothing — measured, and what it does produce is a
different and earlier row, `ind-spec(T: type former spine)`, because the type
former's own binder is then not a `Sort`. The corpus's three are hand-built
kernel tests, and `rec_dep`'s own
`a_function_typed_recursive_slot_stops_the_dependent_eliminator_at_both_sigma`
has a `Q.c` cell that builds that environment directly — with the alias as a
bare β-redex, so it depends on no other declaration. That is where the
parameter half is pinned.

# Why `FunCod` has three recursive slots, and why two of them are *different*
# aliases

`rec_dep::CtorBridge::rec_eq` is indexed by **recursive-slot order**, and the
walk reads it at the index its own `Slot::Rec` counter produced. Getting that
mask wrong is this project's recurring defect — `derived/` found eight index
maps that a whole suite could not see — and the shape of the cell is chosen
against the three ways it goes wrong rather than against one:

| index map | what happens here |
|---|---|
| shift, `j ↦ j+1` | slot 1 reads slot 2's equation, whose left endpoint is the *other* alias |
| clamp, `j ↦ min(j,1)` | slot 2 reads slot 1's equation, same |
| reversal, `j ↦ 2-j` | slot 2 reads slot 0's, which is `None`, and the walk declines |

The two aliases are `constType` and `constType2`, two *different* definitions
with the same reduct, so their interpretations are different terms and an
equation read at the wrong index fails its endpoint check instead of being
spent. **`min(j,1)` is why the aliased slots are 1 and 2 and not 1 alone**: a
clamp is the identity at `{0,1}`, so a single aliased slot in the middle is
exactly the cell it survives — measured, it did.

All three slots are function-typed, because a constructor mixing a plain
recursive slot with a function-typed one is a *mixed* constructor and
`rec_dep::general_slot_declines` refuses it one step earlier —
`parameter_domain_branching`'s `XTree` is the cell for that row and it is a
different obstacle.

# Why `B2` and not `Bool`, and why `constType` and not an identity

`Bool` is not available under `prelude`. `B2` is the smallest closed domain
whose `Σ(z::γ)` is not the one-point summand an empty `γ` gets, which is
`parameter_domain_branching`'s reason for it too.

`constType x y = x` is the corpus's own obfuscation and it is the right one:
its reduct **discards** an argument, so `⟦constType (T α) (T α)⟧` is an
application term mentioning `⟦T α⟧` twice while the spine mentions it once. A
one-argument alias would reduce to a term the walk could have found by peeling.
`constType2` is the same definition under a second name, which is the cheapest
way to get two aliased slots whose interpretations are different terms.
-/
prelude

universe u v

unsafe axiom lcErased : Type u
unsafe axiom lcAny : Type u
unsafe axiom lcVoid : Type u

--#export spelledTy spelledMk spelledRec codTy codMk codRec
--#export funcodTy funcodNode funcodRec

/-- A binary function whose reduct discards its second argument. -/
def constType (x _y : Type) : Type := x

/-- A second one, so that two aliased slots carry two *different* terms. -/
def constType2 (x _y : Type) : Type := x

/-- A closed two-point domain, for the function-typed slots. -/
inductive B2 : Type where
  | ff : B2
  | tt : B2

/-- The control: the recursive field is spelled as the spine. -/
inductive Spelled (α : Type) : Type where
  | nil : Spelled α
  | mk : Spelled α → Spelled α

/-- The plain recursive field's type only *reduces* to the spine. -/
inductive Cod (α : Type) : Type where
  | nil : Cod α
  | mk : constType (Cod α) (Cod α) → Cod α

/-- Three function-typed recursive slots: one spelled, then two codomains
    behind two *different* aliases. -/
inductive FunCod (α : Type) : Type where
  | leaf : FunCod α
  | node : (B2 → FunCod α) → (B2 → constType (FunCod α) (FunCod α)) →
      (B2 → constType2 (FunCod α) (FunCod α)) → FunCod α

def spelledTy : Type := Spelled B2
def spelledMk (t : Spelled B2) : Spelled B2 := Spelled.mk t
noncomputable def spelledRec (t : Spelled B2) : B2 := Spelled.rec B2.ff (fun _ ih => ih) t

def codTy : Type := Cod B2
def codMk (t : constType (Cod B2) (Cod B2)) : Cod B2 := Cod.mk t
noncomputable def codRec (t : Cod B2) : B2 := Cod.rec B2.ff (fun _ ih => ih) t

def funcodTy : Type := FunCod B2
def funcodNode (f : B2 → FunCod B2) (g : B2 → constType (FunCod B2) (FunCod B2))
    (h : B2 → constType2 (FunCod B2) (FunCod B2)) : FunCod B2 := FunCod.node f g h
noncomputable def funcodRec (t : FunCod B2) : B2 :=
  FunCod.rec B2.ff (fun _ _ _ _ _ ihh => ihh B2.ff) t
