/-
# Lean's other two standard axioms, in a file whose types can interpret

`mini::ev::Gap::Axiom` is reached **only once the axiom's own type has
interpreted**, and `mini/tests/tutorial.rs` records that on the 91-file corpus
the variant is therefore unreachable: "no axiom's type interprets yet". That
sentence is the reason this file exists. `mini::axiom` has one clause,
`Quot.sound`, and the two axioms with no clause — `propext` and
`Classical.choice` — do not occur in `good/tutorial` at all and occur in
`good/init-prelude` (`Classical.choice`) only inside a file whose 63723 lines
bury the measurement.

So: the smallest export that declares both of them, at Lean's own types, over
locally declared `Eq`, `Iff` and `Nonempty`, with a use site each so the
declaration walk opens a pair.

**Both axioms are declared under Lean's own names**, which is the point:
`mini::convert::is_standard_axiom` accepts `propext` and `Classical.choice` and
declines anything else, so a fixture that renamed them would be declined at the
frontend and would measure the decline instead of the gap.

# The declarations

| declaration | why |
| --- | --- |
| `Eq` | `propext`'s codomain is an equation, at `Sort 1` — not at `Sort 0` |
| `Iff` | `propext`'s premise: two `Prop` fields, no index — class (S) |
| `Nonempty` | `Classical.choice`'s premise: one *data* field — class (P) |
| `propext` | `∀ {a b : Prop}, (a ↔ b) → a = b` |
| `Classical.choice` | `∀ {α : Sort u}, Nonempty α → α` — the codomain is **not** a `Prop` |

`propextUse` and `choiceUse` are the use sites; without them the axioms are
still scheduled (`ledger::run` opens a pair for every `Axiom`), but a use site
also puts the axiom's *interpretation* on some other declaration's path, which
is where a store entry that is not about what its typing says would show.

`Eq` is declared here because every fixture is `prelude` and imports nothing
(`scripts/export-fixture.sh`'s header says why).
-/
prelude
universe u

--#export Eq Eq.refl Iff Iff.intro Nonempty Nonempty.intro
--#export propext Classical.choice propextUse choiceUse trueIff

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- `Init.Prelude`'s `Eq`, re-declared. -/
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

/-- `Init.Core`'s `Iff`, re-declared: two `Prop`-valued fields, no index. -/
structure Iff (a b : Prop) : Prop where
  intro ::
  mp : a → b
  mpr : b → a

/-- `Init.Prelude`'s `Nonempty`, re-declared: one field, of the parameter's own
    (arbitrary) sort. -/
inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

/-- `Init.Core`'s `propext`, at its own type. -/
axiom propext {a b : Prop} : Iff a b → Eq a b

/-- `Init.Core`'s `Classical.choice`, at its own type. -/
axiom Classical.choice {α : Sort u} : Nonempty α → α

-- The use sites.

/-- A closed `Iff`, so `propextUse` has a premise that is not a binder. -/
def trueIff (a : Prop) : Iff a a := Iff.intro (fun h => h) (fun h => h)

def propextUse (a : Prop) : Eq a a := propext (trueIff a)

noncomputable def choiceUse (α : Sort u) (h : Nonempty α) : α := Classical.choice h
