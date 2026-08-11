/-
# A unit-like declaration at a **ground** nonzero sort

`MONOMORPH.md` §4.3's first cause, in the shape a plain export can carry.

`mini::zoneb::build`'s trichotomy used to ask `provably_nonzero` on the
declaration's own level expression *first*, and send everything it answered
`true` about to class (T). That is right for a declaration with distinguishable
elements and wrong for a subsingleton: the class-(S) carrier is a subset of
`{•}`, hence a member of every rung, so it denotes a `Type`-valued declaration
as faithfully as a `Prop`-valued one (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3).
Under the old order `U1 : Type` — one constructor, no fields — got a W-carrier
and with it no `LeProp`, so:

* `mini::unit_like` had nothing to build `⟦x⟧ = ⟦y⟧` out of and reported
  `waiting:unit-like(U1)`;
* `mini::proj_prop::field_in_u0`'s **second route**, which discharges
  `Pⱼ = ⟦βⱼ⟧ ⊆ 1` out of the field declaration's own `ClassS::in_u0`, had no
  `ClassS` to read and the projection came back a value instead of `•`.

`field_in_u0_by_carrier.lean` records that both of those were measured: its
witness had to be written `PU.{u}` and used at `u := 1`, because
`inductive PU : Type 0` "was written first and **failed**". This file is that
failing declaration, kept.

# Why it is the same defect as `monomorph`'s

`monomorph` emits `PUnit.{u}` at `[1]` as `_at.1.1.PUnit : Sort 1`, which is
`U1` with a longer name. The pass destroys nothing — a one-constructor
no-field inductive is one whatever its sort is — so the fix is a structural
test, and once the test is structural the ground declaration is served too.
That is why this fixture needs no monomorphized export to be the same
measurement; `mono_prefix.lean` is the end-to-end one.

# The declarations

| declaration | ctors | fields | class | why |
| --- | --- | --- | --- | --- |
| `U1 : Type` | 1 | none | **(S)** | the target: a subsingleton at a ground `Sort 1` |
| `Pair2 : Type` | 1 | two data | (T) | one constructor is not enough — its fields are distinguishable |
| `Three : Type` | 3 | none | (T) | no fields is not enough either |
| `EmptyG : Type` | 0 | — | (T) | **control for the narrowing** |
| `RecU : Type` | 1 | one recursive | (T) | **control for the narrowing** |

**Three constructors in `Three`, not two.** Two nullary constructors are
distinguishable, so two would already refute "no fields means subsingleton" —
but two also pass under an off-by-one in a constructor walk, and the tag sum
`Three` produces is the first that cannot be read as a boolean. `Pair2` is the
other half of the same pair of controls: `U1` differs from `Pair2` in its
fields and from `Three` in its constructor count, so neither alone identifies
what the class-(S) preference is keyed on.

`EmptyG` and `RecU` are the **narrowing**, and they are here because widening
the preference without them was measured to cost five `tutorial/` files
(`033_empty`, `059_emptyRec`, `052`, `113`, `114`). Both are subsingletons by
Carneiro §2.6.2 reason 2 — no constructors is large-eliminating, and a
recursive field passes the `LE ctor` walk unconditionally — and for neither
does `mini::class_s` produce the `LeProp` the preference exists to produce:
`EmptyG` would get `¬ψ` and no eliminator (`recursor::CLASS_S_EMPTY`) where its
W-carrier gives it a working `rec`, and `RecU`'s interpretation would have to be
the `acc` and not `A_φ`, which `class_s` declines by name. They must stay
class (T), and if the narrowing is ever dropped this file says so before the
corpus does.

`Eq` and `rfl` are declared here because every fixture is `prelude` and imports
nothing (`scripts/export-fixture.sh`'s header says why).
-/
prelude
universe u

--#export Eq Eq.refl rfl U1 U1.unit Pair2 Three EmptyG RecU
--#export WG WG.u wgMk wgUse groundEta pair2Mk threeMk emptyGRec recUMk

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

/-- **The target.** One constructor, no fields, at a **ground** `Sort 1`. This
    is `_at.1.1.PUnit` under a shorter name. -/
inductive U1 : Type where
  | unit : U1

/-- **Control.** No fields anywhere, three constructors. -/
inductive Three : Type where
  | a : Three
  | b : Three
  | c : Three

/-- **Control.** One constructor, two *data* fields — not a subsingleton, and
    it must keep its W-carrier. Two fields of two distinct types, so their
    order is observable. -/
inductive Pair2 : Type where
  | mk : U1 → Three → Pair2

/-- **Control for the narrowing.** No constructors: a subsingleton by reason 2,
    and class (S) would leave it without an eliminator. -/
inductive EmptyG : Type

/-- **Control for the narrowing.** One constructor with a recursive field: a
    subsingleton by reason 2, and class (S)'s carrier would have to be the
    `acc`. -/
inductive RecU : Type where
  | mk : RecU → RecU

/-- `field_in_u0_by_carrier.lean`'s `W`, over the **ground** unit. Its `u`
    projection is the second route's witness. -/
structure WG : Type where
  u : U1

-- The use sites. `mini::ledger::run` opens no pair for an `Inductive`, so
-- without these the file is accepted with an empty ledger and measures nothing.

def wgMk : WG := WG.mk U1.unit
def wgUse : U1 := wgMk.u

/-- η for a unit-like structure, at a ground `Sort 1`. Lean's `isDefEq` accepts
    `x ≡ y` here by unit-like η; `mini::unit_like` is what has to certify it,
    and it consumes `LeProp::subsingleton`. -/
def groundEta (x : U1) (y : U1) : Eq x y := rfl x

def pair2Mk : Pair2 := Pair2.mk U1.unit Three.a
def threeMk : Three := Three.c
noncomputable def emptyGRec := @EmptyG.rec
def recUMk (r : RecU) : RecU := RecU.mk r
