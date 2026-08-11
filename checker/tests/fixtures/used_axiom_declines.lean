/-
# A non-standard axiom something in the file **does** refer to — still declines

The other polarity of `unused_axiom_ignored.lean`, and the one that carries the
correctness content. Ignoring an *unused* non-standard axiom is a narrowing of
the rule `mini::convert::is_standard_axiom` draws; a **used** one must go on
taking the file out of scope, with the same reason string and the same exit 2,
because the file's theorems rest on an inhabitation that is not derivable in
principle. The must-kill mutation for the whole change is *treat a used axiom as
unused*, and this is where it dies.

## Three axioms, and the used one is declared last

Two atoms cannot distinguish the three readings this file has to separate, so
there are three, and the two unused ones come **first**:

| declaration | referred to from | what it rules out |
| --- | --- | --- |
| `spareAx` | nowhere | a checker that declines on the *first* non-standard axiom reports **this** name — that is the pre-narrowing behaviour, and it is wrong now |
| `alsoSpare` | nowhere | …and a checker that reports the first *or* the second, or any fixed position |
| `usedOnlyInAValue` | `viaValue`'s **value**, and nothing else | the must-kill: ignore it and the file is accepted. A reachability walk that reads declarations' *types* and not their *values* accepts this file |

So the decline's reason is `non-standard axiom: usedOnlyInAValue`. Three
distinct wrong implementations produce three distinct wrong outputs here:
`spareAx` (the old rule), an `accept` line (ignore everything, or skip def
values), and this file's `alsoSpare` never being reported at all.

**A real reference, not a name.** The use is an `Expr::Const` occurrence the
elaborator put there; nothing keys on a spelling. `mini/src/unused_axiom.rs`
says why that is the rule — this project has paid for name-keying at
`_auxCarrier` and at `proj(PProd)`.

## Where the other reference kinds are covered

The *value* kind is the one this fixture can pin end to end, because a declined
run prints no ledger and so reveals only the **first** used axiom. The rest of
the enumeration — an axiom's own statement, a `def`'s type, an inductive's type,
a constructor's type, a mutual member's, a projection's head — is pinned by
`mini::unused_axiom`'s `every_reference_kind_is_a_use`, which asserts the whole
unused set over one declaration per kind, so a walk that drops an arm fails by
name.

The corpus was measured rather than assumed, and it pins **one** arm
independently. `031_letTypeDep` declares two axioms: `aDepProp`, which occurs in
`mkADepProp`'s **axiom statement** and in `letTypeDep`'s **type** and in no
value, and `mkADepProp`, which occurs in `letTypeDep`'s **value**.
`032_letRed`'s `aProp` occurs only in `letRed`'s **value**. So both corpus
declines do use their axioms — and:

* drop `Declaration::Def`'s `value` from the walk and `032` **accepts**
  (`accept 2 declarations … ignored axioms: aProp`), so `decline 2` becomes
  `decline 1`. Measured.
* drop both *type* arms and `031` still declines, on `mkADepProp` instead of
  `aDepProp` — its two axioms are a redundant witness for each other, and what
  moves is the reason string, which `tutorial_good_all_accepted` compares
  exactly. Also measured; a first draft of this paragraph claimed the file
  accepted, and it does not.

Every other arm has exactly one witness anywhere, and it is the unit test.

## The `Prop` is inhabited nowhere

`viaValue` is a `def` whose value is the constant `usedOnlyInAValue`, which is
legal because `usedOnlyInAValue : Prop` is itself a term of type `Prop`; it is
not a proof of anything. The file is *accepted* by the kernel and declined by
the scope rule, and those are the two axes `mini/src/run.rs` keeps apart.
-/
prelude

--#export spareAx alsoSpare usedOnlyInAValue viaValue

-- `Init.Prelude`'s first three declarations; `unsafe`, so never exported.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- Declared first, referred to by nothing. Ignored, not declined. -/
axiom spareAx : Prop

/-- A second unused one, at an arrow type, so no fixed position is the answer. -/
axiom alsoSpare : Prop → Prop

/-- Referred to from a `def`'s **value**, and from nowhere else. -/
axiom usedOnlyInAValue : Prop

def viaValue : Prop := usedOnlyInAValue
