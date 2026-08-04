/-
# A declaration the cumulativity table cannot reach

**This fixture exists to be permanently uncertified.** It is the negative
witness for the certification axis: `mini` accepts it — it is well typed, and
`Main.lean` and nanoda accept it too — and cannot derive
`⊢ ⟦Type 30 → Type 30⟧ ∈ ⟦Sort 32⟧`, so the run reports
`uncertified: 1 type typing` and exits `4`.

# Why a universe and not a missing clause

Every other "mini cannot do this yet" fixture has a shelf life, and this project
has spent that lesson twice: `mini/src/ledger.rs`'s three tests used
`Expr::NatLit` as their uninterpretable stand-in until nat literals interpreted,
and `mini/tests/dump.rs`'s witness ran out twice in one round. A fixture chosen
for being unsupported stops testing what it is about the moment the support
lands, and it does so *silently* if the assertion is one-sided.

`mini::interp::CUMUL_HEIGHT` is different in kind. The cumulativity table is
built **eagerly**, is `O(h²)` theorems, and is finite by construction: a Lean
sort above it yields a gap rather than a wrong universe, and that is a design
decision rather than an unwritten clause. `Type 30` is `Sort 31`, so the arrow's
own sort is `Sort 32` against a table of height 8. Closing this row means
building 1 024 theorems at every `Interp::new`, which is not a thing that
happens by accident on the way to something else. (`Type 30` and not something
sillier: Lean's own `maxUniverseOffset` caps a universe literal at 32.)

If it ever *does* certify, the assertion in
`the_certification_axis_is_in_the_verdict_and_in_the_exit_code` fails loudly and
should be re-pointed at a higher sort — which is the behaviour the two
worn-out fixtures above did not have.

# Why `fine` is here

A fixture where *everything* is uncertified would pass a check that reported
every run as uncertified. `fine` is one pair that derives both of its
obligations, in the same file, so the count `1 type typing` is a discrimination
and not a constant.

# What this measures that a `constEv` gap would not

`constEv` is **2** here and `typeEv` is **1**: `⊢ ⟦beyondTheTower⟧ ∈ ⟦ty⟧`
derives while `⊢ ⟦ty⟧ ∈ ⟦Sort 32⟧` does not — the ledger's `typeEvOnlyGap`
row, at 1. So a definition of "uncertified" that watched only the constant
typings would read this run as **clean** while a real obligation is owed. That
is why `Uncertified::type_typings` is in the set, and this file is the witness
that it has to be.
-/
prelude

--#export fine beyondTheTower

/-- A pair whose every obligation derives, so the count below discriminates. -/
def fine : Type := Prop

/-- `Type 30 → Type 30` is `Sort 32`, far above `mini::interp::CUMUL_HEIGHT`. -/
def beyondTheTower : Type 30 → Type 30 := fun x => x
