/-
# `monomorph`'s output, end to end

**This fixture's `.ndjson` is not `lean4export`'s output.** It is that output
passed through `modelgen/.lake/build/bin/monomorph`, which is what the
`--#monomorph` line below asks `scripts/export-fixture.sh` for. It is the only
fixture here with a `_at.` name in it, and the only one whose declarations carry
no universe parameters at all.

# What it measures

`monomorph` erases universe polymorphism by emitting one copy of each
declaration per ground instantiation and prepending `_at.⟨|σ|⟩.⟨σ₀⟩…` at the
**root** of every name (`MONOMORPH.md` §1.1). The prefix is deliberately free of
any dependence on the shape of the name it is prepended to, so that it composes
with other naming schemes without either knowing about the other. Everything a
consumer must adapt is therefore on the consumer's side, and `MONOMORPH.md`
§4.3 measured two places where `mini` had not:

1. **A decision keyed on a bare name.** `mini::direct::clause_for` is a table on
   `Eq`, `Acc` and `Nat` — three declarations whose denotation is *named* rather
   than translated. `Eq` and `Nat` survived the pass only because they are
   carried built-ins (`MONOMORPH.md` §3); `Acc` became `_at.1.0.Acc`, the row
   did not fire, and the general walk reached `Acc.intro`'s depth-2 recursive
   telescope and declined it. `mini::mono_name::strip` is how the table now
   asks.

2. **A decision keyed on surface level syntax.** `mini::zoneb`'s trichotomy
   asked `provably_nonzero` on the declaration's own level *expression*, which
   monomorphization grounds: `PU.{u} : Sort u` is not provably nonzero and its
   copy `_at.1.1.PU : Sort 1` is, so the copy took the class-(T) W branch and
   lost the `LeProp::subsingleton` that `mini::unit_like` consumes. The
   trichotomy now asks `zoneb::subsingleton`, which is structural.

Between them those two cost four of the 91 `tutorial/` exports — `086`, `102`,
`117`, `118` — every one of them a declaration that was certified before the
pass and gapped after it.

# The declarations

| declaration | copy | what it pins |
| --- | --- | --- |
| `Acc` | `_at.1.0.Acc` | the named clause, through the prefix |
| `PU.{u}` at `1` | `_at.1.1.PU` | the trichotomy, through a grounded sort |

`Acc` is `Init.WF`'s, re-declared: two parameters, one index, one constructor,
which is the shape `direct::Clause::Acc`'s arity check demands. It is used at a
`Prop` carrier so the copy is `_at.1.0.Acc` and not some other σ.

`PU.{u}` is `Init.Prelude`'s `PUnit.{u}`, re-declared for
`field_in_u0_by_carrier.lean`'s reason — it must be **polymorphic in the
source**, because a ground `Type 0` unit is a different measurement and
`ground_unit_subsingleton.lean` is that one. Here the pass is what grounds it,
which is the point: the two fixtures are the same defect before and after
monomorphization, and neither subsumes the other.

`Eq` and `rfl` are declared here because every fixture is `prelude` and imports
nothing. They keep their names through the pass for the wrong reason — they are
*locally* declared, not carried built-ins — but the copy `_at.1.1.Eq` would
serve as well; `direct::clause_for` sees through the prefix either way.
-/
prelude
universe u

--#monomorph
--#export Eq Eq.refl rfl Acc Acc.intro Acc.rec PU PU.unit
--#export Lt accIntro accRec puEta

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- `Init.Prelude`'s `Eq`, re-declared: the fixture needs an equation to state
    η at. -/
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

/-- `Init.Prelude`'s `rfl`. -/
def rfl {α : Sort u} (a : α) : Eq a a := Eq.refl a

/-- `Init.WF`'s `Acc`, re-declared. Two parameters, one index, one constructor
    whose recursive field `h` is a depth-2 telescope — which is what the general
    class-(S) walk declines and why this declaration has a named clause. -/
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

-- `bootstrap.inductiveCheckResultingUniverse` is how `Init.Prelude` declares
-- `PUnit.{u}`; it is off here for the same reason, so that the resultant sort
-- stays a bare universe parameter and the *source* declaration is the
-- possibly-`Prop` one.
set_option bootstrap.inductiveCheckResultingUniverse false in
/-- `Init.Prelude`'s `PUnit.{u}`, re-declared. Level-polymorphic in the source;
    `monomorph` is what grounds it. -/
inductive PU : Sort u where
  | unit : PU

/-- A relation for `Acc` to be taken over. A `def` and not an `inductive`: an
    empty `Prop`-valued inductive is a subsingleton with no constructors, whose
    class-(S) eliminator is `recursor::CLASS_S_EMPTY` — a gap this fixture is
    not about, and one that would put it on exit 4 for an unrelated reason. -/
def Lt (x : PU.{1}) (y : PU.{1}) : Prop := Eq x y

-- The use sites. `mini::ledger::run` opens no pair for an `Inductive`, so
-- without these the file is accepted with an empty ledger and measures nothing.

noncomputable def accIntro (x : PU.{1}) (h : (y : PU.{1}) → Lt y x → Acc Lt y) :
    Acc Lt x :=
  Acc.intro x h
noncomputable def accRec := @Acc.rec

/-- η for a unit-like structure. After the pass this is `_at.1.1.PU`, whose
    resultant sort is the ground `Sort 1`. -/
def puEta (x : PU.{1}) (y : PU.{1}) : Eq x y := rfl x
