/-
# A data field that still denotes `•`, because its **carrier** is in `U₀`

`INTERP-AUDIT.md` L4. `mini::proj_prop::field_in_u0` discharges the rung
premise `Pⱼ = ⟦βⱼ⟧ ⊆ 1` by **two** routes, and they are not the same
condition:

1. the field's inferred sort is `⟦Prop⟧` — the Lean sort of `βⱼ` is `Prop`,
   which is `SCOPING.md` §6.2's own wording;
2. the field type's **own declaration's** carrier membership `⊢ ⟦βⱼ⟧ ∈ U₀`,
   moved back along `beta_spine` onto the interpretation the field binder was
   opened at.

Route 2 is strictly weaker, so there is a cell where the two disagree: a field
whose Lean sort is *not* `Prop` and whose carrier is in `U₀` all the same. L4
kept that route (option A) rather than gating it on `is_prop_ev`, because what
licenses the `•` is a theorem in hand while `is_prop_ev`'s bool is a syntactic
flag whose own `Ev` may be a `Gap`. **No corpus member is in that cell.** This
file is, twice.

# The declarations

| declaration | fields | what it is |
| --- | --- | --- |
| `W` | `u : PU.{1}` | `INTERP-AUDIT.md` L4's own witness, verbatim |
| `Mixed α` | `p : α`, `u : PU.{1}`, `a : Two` | the ladder — **the target** |

`W` is the audit's `structure W : Type where u : PUnit.{1}` with `PUnit`
re-declared (see below). It is the minimal witness and it reaches route 2 at
rung 0.

`Mixed` is the one that makes route 1 *load-bearing* rather than merely
present. A projection at index `j` is owed `P₀ ∧ … ∧ Pⱼ`, so `Mixed.u` at
index 1 needs **both** routes: `P₀` for the parameter `α` can only come from
route 1, and `P₁` for `PU.{1}` only from route 2. Breaking either one declines
it — checked, both ways. `Mixed.a` at index 2 adds the third cell: `⟦Two⟧ ∈ U₀`
says nothing about `⟦Two⟧ ⊆ 1`, no route applies, and the projection is a
**value**.

Three fields rather than two, for `class_s_dependent_fields.lean`'s reason: at
two fields the prefix *is* everything, and only a third separates a fold over
the whole prefix from one over a fixed prefix of it.

# Why the assertions read terms and not counts

Under L4's option B — gate the route on `is_prop_ev` — `W.u` and `Mixed.u`
would answer `πⱼ(z)` like `Mixed.a` instead of `•`, and every pair in this file
would still **derive**: `proj_data` supplies a well-typed term for the
projection of a class-(T) structure, so `constEv` is blind to the choice. The
assertions in `designed.rs` therefore read the dumped conclusions. The two
candidate terms are provably equal (`⟦PU.{1}⟧ ⊆ 1`), which is why choosing
wrongly costs drift and gaps rather than a false certificate — and is also why
nothing but the term distinguishes them.

`Mixed.p` is not an oracle for route 1 and the test does not use it as one: a
function into a `Prop` is itself a `Prop`, so `⟦Mixed.p⟧` is `•` by proof
irrelevance whatever the projection clause does. Route 1 is asserted where it
is load-bearing, at `Mixed.u` — whose rung 0 *is* `Mixed.p`'s field.

# The witness is level-polymorphic because the audit's is, not because it must be

`inductive PU : Type 0 | unit : PU` was written first and **failed**, and the
reason is worth keeping because it was a defect and has been fixed.
`zoneb::build`'s trichotomy used to ask `provably_nonzero` on the declaration's
own resultant level *expression* first (`LEVEL-POLYMORPHIC-INDUCTIVES.md`
§3.3), so `Sort u` was class (S) at every σ and lands in
`IndApparatus::props` with `ClassS::in_u0` beside it — which is exactly what
route 2 reads — while a ground `Type 0` unit was class (T), landed in
`IndApparatus::decls`, and its projection routed to `proj_data`.

The branch is `zoneb::subsingleton` now: one constructor and no fields, which
is true of `PU` in either spelling, so a monomorphic unit reaches route 2 too.
`ground_unit_subsingleton.lean` is that spelling and is a fixture in its own
right; the same defect cost four `tutorial/` exports under `monomorph`
(`MONOMORPH.md` §4.3), which grounds `PU.{u}` into exactly the declaration that
used to fail here.

This file keeps `PU.{u}` because the audit's witness is `PUnit.{1}` and this is
the audit's cell verbatim, not because the polymorphism is load-bearing.

`PUnit` itself is not available: every fixture here is `prelude` and imports
nothing (`scripts/export-fixture.sh`'s header says why), so `PU.{u}` is
`Init.Prelude`'s `PUnit.{u}` re-declared, `bootstrap` option and all.

# `PU` is the second occupant of a K-likeness exemption, and that is a finding

`mutual.rs::the_generated_recursors_are_the_ones_lean_exports` compares every
generated recursor against Lean's export, and records one **pre-existing**
divergence instead of failing on it: at a declaration whose resultant sort is a
bare level parameter, mini-lean's `Environment.add` asks `isNotZero` where
Lean's `init_k_target` asks `is_zero`, so mini calls the recursor K-like and
Lean does not. It is mini being a faithful port of mini-lean, it costs nothing
observable, and `PUnit.rec` was its only witness.

`PU.rec` is a second one, and it is the same shape under a different name — so
an exemption keyed on the *name* reports it as a new divergence. Keeping the
declaration called `PU` rather than `PUnit` is therefore deliberate: it is what
forces that exemption to be keyed on the cause. **Renaming this declaration to
make a name list match would delete the only thing that distinguishes the two
keyings.**
-/
prelude
universe u

--#export Tru Two PU W Mixed
--#export W.u Mixed.p Mixed.u Mixed.a
--#export wMk mixedMk wUse mixedUse

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- An inhabited closed `Prop`, to instantiate `Mixed`'s parameter. Inhabited on
    purpose: a provably empty `Prop` discharges an inhabitation clause
    vacuously. -/
inductive Tru : Prop where
  | triv : Tru

/-- A genuine data type, for `Mixed`'s neither-route rung. **Two**
    constructors, so that it is not unit-like and its carrier is not in `U₀` as
    a conditional singleton — one constructor would make it a second `PU`. -/
inductive Two : Type where
  | ff : Two
  | tt : Two

-- `bootstrap.inductiveCheckResultingUniverse` is how `Init.Prelude` declares
-- `PUnit.{u}`; it is off here for the same reason, so that the resultant sort
-- stays a bare universe parameter and `provably_nonzero` reads `Sort u`.
set_option bootstrap.inductiveCheckResultingUniverse false in
/-- `Init.Prelude`'s `PUnit.{u}`, re-declared because this file imports
    nothing. Level-polymorphic, which is the whole point: see the header. -/
inductive PU : Sort u where
  | unit : PU

/-- `INTERP-AUDIT.md` L4's witness verbatim: one field, whose Lean sort is
    `Type 0` and whose carrier is in `U₀`. -/
structure W : Type where
  u : PU.{1}

/-- **The target.** Rung 0 is route 1, rung 1 is route 2 *on top of* rung 0,
    and rung 2 is neither.

    The route-1 rung is a **parameter** and not the closed `Tru`, and that was
    measured rather than chosen: `whnf` of a closed `Prop` is a `Const`
    application, so route 2 answers it out of `Tru`'s own `ClassS::in_u0` and
    route 1 is never reached. A parameter has no declaration to consult, so
    route 1 is the only thing that can discharge it — and it is the corpus's own
    shape, since `And a b`'s two field types are its parameters. -/
structure Mixed (α : Prop) : Type where
  p : α
  u : PU.{1}
  a : Two

-- The use sites. `mini::ledger::run` opens no pair for an `Inductive`, so
-- without these the file is accepted with an empty ledger and measures nothing.
-- The generated projection functions `T.f` are `def`s in their own right and
-- carry the `Expr.proj` this fixture is about — they are named on the
-- `--#export` lines above and are what `designed.rs` reads. The `Mk`/`Use`
-- defs schedule the constructor and a projection at a *closed* subject beside
-- the projection at a binder.

def wMk : W := W.mk PU.unit
def mixedMk : Mixed Tru := Mixed.mk Tru.triv PU.unit Two.ff

def wUse : PU.{1} := wMk.u
def mixedUse : PU.{1} := mixedMk.u
