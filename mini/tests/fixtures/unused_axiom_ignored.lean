/-
# A non-standard axiom **nothing in the file refers to** — ignored, and the file stays in scope

`mini::convert::is_standard_axiom` takes a file declaring a user axiom out of
scope, because that axiom's inhabitation is not derivable in principle and a run
that stops at the first missing derivation would stop there for ever. This file
is the shape that narrowing is about, and it is the whole reason `init-prelude`
was unreachable: that export declares `sorryAx`, **nothing in it uses `sorryAx`**,
and one line took 1 459 declarations and 3 078 scheduled pairs out of scope after
mini had already got all of them through `convert::load`.

The owner's decision, and the design principle at the site
(`mini/src/unused_axiom.rs`):

> We cannot generate evidence for it, and nothing depends on it, so there is
> nothing to be evidence *for*.

## What it declares

| declaration | why |
| --- | --- |
| `unusedProp` | a non-standard axiom at `Prop`, referred to by nothing |
| `unusedRel` | a **second** one, at an arrow type, so `ignored axioms:` is a list rather than a singleton and an implementation that reports only the first fails |
| `N`, `nZero`, `nSucc` | the content, so the file has pairs to certify — the ledger opens a pair for a `def` and for **no** `inductive` |

## The polarity, and its twin

This file must now be **accepted**, with both axioms named on the verdict line
and counted in the `ledger` row, and with no pair opened for either of them.
`used_axiom_declines.lean` is the other polarity: a non-standard axiom something
in the file genuinely refers to still declines, with its reason. Neither test
means anything without the other — the first is passed by a checker that ignores
every axiom, the second by one that ignores none.

## Why the skip has to be visible

`#64`: *a declined declaration with no scheduled pair is invisible*. An ignored
axiom has no pair **by construction**, so every counter in the ledger is indexed
by something it cannot appear in. `mini::ledger::Ledger::ignored_axioms` is the
list that stops it from being silent, and `ignoredAxioms=2` on the `ledger` row
plus `ignored axioms: unusedProp, unusedRel` on the verdict line is what a
reader sees.

It is deliberately **not** exit 4. `Uncertified` and `Untranslated` are lists of
obligations mini *owes*; nothing in this file rests on either axiom, so there is
no claim to be short of.
-/
prelude

--#export unusedProp unusedRel N nZero nSucc

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- A user-declared axiom. Nothing below mentions it. -/
axiom unusedProp : Prop

/-- A second one, at an arrow type rather than a sort. Also mentioned nowhere. -/
axiom unusedRel : Prop → Prop

inductive N : Type where
  | z : N
  | s : N → N

def nZero : N := N.z

def nSucc (n : N) : N := N.s n
