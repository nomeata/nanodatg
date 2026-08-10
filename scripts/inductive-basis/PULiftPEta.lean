/-
PULiftPEta.lean — exactly which definitional property of `PULiftP` the
`--prim-models` construction rests on, measured rather than asserted.

`modelgen`'s basis holds `PULiftP.{u} (p : Prop) : Sort u` because it is the
one former that reaches a bare variable sort and can be *empty*. Two claims
were made for it in `MODELGEN.md` §8.1 and in `Modelgen/Simple.lean`'s
docstrings, and they are **not the same claim**:

  (A) every element of `PULiftP p` is definitionally equal to a literal
      `PULiftP.up h` — eta-for-structures fires because one side is already a
      constructor application, and proof irrelevance then closes the payload;

  (B) `PULiftP ⊤` is a "definitional singleton", i.e. any two of its
      inhabitants are definitionally equal.

VERDICT: **(A) holds. (B) does not hold as a conversion, and the reason is
algorithmic incompleteness rather than a fact about the theory.** §2 pins
both, and pins the gap between them, which is the part worth understanding:

  * (B) fails even when the kernel is forced with `@Eq.refl _ x` instead of
    the elaborator's `rfl`, so it is **not** a unification-order artifact.
    Eta-for-structures fires only when one side is already a constructor
    application; two opaque variables expand neither side and the comparison
    falls through to two distinct free variables.
  * and yet `x = y` **is provable, with no axiom** (§2's last example), by
    routing through `up (down ·)` by hand: each round trip is a redex, so each
    is `rfl`, and proof irrelevance closes `down x = down y` in the middle.

Both together say the conversion is **not transitive here**: `x ≡ up (down x)`
and `up (down x) ≡ up (down y)` and `up (down y) ≡ y` each hold, and `x ≡ y`
does not. Nothing is wrong in the theory; the algorithm simply has no step
that eta-expands a variable on speculation. **What a generator may rely on is
what the kernel accepts**, so the distinction is the whole of the matter:
`modelgen` must arrange for a redex, and it does.

WHY THE CONSTRUCTION IS NEVERTHELESS SOUND. Every place the generator relies
on the lift is an eta *redex* — one side is a literal `up`:

  * the [`Modelgen.unitAt`] pad. Its canonical element `unitAtCanon` is
    `PULiftP.up ⊤ trueI`, a literal constructor application, so `canon ≡ scrut`
    for an opaque `scrut` is case (A) and not case (B). `Modelgen.padsAt`
    marks the pad `canonical := true` on the strength of exactly this.
  * the maybe-zero carrier. `Modelgen.puliftEta` is `Eq.refl` at the statement
    `up (down t) = t`, whose left side is a constructor application — again
    (A). `motive (up (down t))` and `motive t` are therefore convertible and
    the maybe-zero recursor is the `Prop` route's with `up`/`down` at the ends.

Nowhere are two *opaque* inhabitants compared, so nothing in the construction
depends on (B). The wording that said otherwise has been narrowed in place.

TWO MEASUREMENTS ON THE GENERATOR SIDE, recorded here because they are what
say the reliance is where this file claims it is (`prim_shapes.ndjson`, the
`--prim-models` run, the kernel's own answer through `addDeclCore`):

  * marking the `unitAt` pad `canonical := false`, which routes it through the
    propositional `unitAtUniq` transport instead of the conversion — **green**,
    every shape still models. So the transport branch in
    `Modelgen.chainDestruct` is a working alternative that nothing reaches:
    the conversion is what ships, and (A) is what makes it typecheck.
  * marking the *`dsingAt`* pad `canonical := false`, which would route it
    through the same `unitAt` transport — **red** at `Tri`, `Opt`, `Dec` and
    `Big`. The two pad families are not interchangeable, which is what says
    the flag is carrying real information and not decoration.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean PULiftPEta.lean
Expected: 0 errors (the two failures are pinned with `#guard_msgs`).
-/
universe u
set_option linter.unusedVariables false

-- ═════════════════════════════════════════════════════════════════════════
-- §1. The basis member, at the shape `modelgen` splices.
-- ═════════════════════════════════════════════════════════════════════════

-- The **`inductive`** form. Lean's elaborator refuses the general maybe-zero
-- resulting universe; `bootstrap.inductiveCheckResultingUniverse false` bypasses
-- that check, and core crosses the same line twice itself for `PUnit` and
-- `PEmpty` (`Init/Prelude.lean:123,211`).
--
-- The `structure` form is **not** interchangeable here: the `structure` command
-- has its own resulting-universe path that the bootstrap option does not reach,
-- and `structure PULiftP (p : Prop) : Sort u where get : p` is rejected even
-- with the option set. `modelgen` emits a `Declaration` and checks it with
-- `addDeclCore`, so no elaborator is in its loop; this matters only to someone
-- writing the basis member by hand.
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PULiftP (p : Prop) : Sort u where
  | up : p → PULiftP p

/-- Church `⊤` and its inhabitant — what the pad is the lift of. No primitive:
pure Π. -/
def TrueC : Prop := ∀ C : Prop, C → C
def trueI : TrueC := fun _ c => c

/-- `down`, through the kernel's subsingleton-rule large eliminator. -/
noncomputable def down {p : Prop} (x : PULiftP.{u} p) : p :=
  PULiftP.rec (motive := fun _ => p) (fun h => h) x

/-- The eliminator really is large — a `Type`-valued motive, no axioms. -/
noncomputable def big (p : Prop) (x : PULiftP.{u} p) : Nat :=
  PULiftP.rec (motive := fun _ => Nat) (fun _ => 0) x

/-- info: 'big' does not depend on any axioms -/
#guard_msgs in #print axioms big

/-- The pad, exactly as [`Modelgen.unitAt`] and [`Modelgen.unitAtCanon`] build
it. -/
abbrev unitAt : Sort u := PULiftP.{u} TrueC
abbrev unitAtCanon : unitAt.{u} := PULiftP.up trueI

-- ═════════════════════════════════════════════════════════════════════════
-- §2. (A) holds, (B) does not.
-- ═════════════════════════════════════════════════════════════════════════

/-- **(A), the eta redex.** One side is a literal `up`, so eta-for-structures
expands the other. This is [`Modelgen.puliftEta`]'s statement. -/
example (p : Prop) (x : PULiftP.{u} p) : PULiftP.up (down x) = x := rfl

/-- **(A) at the pad**, in the direction the generator uses it: the applied
minor has type `motive canon` and is handed to a context wanting `motive t`.
`unitAtCanon` is a constructor application and `t` is opaque. -/
example (t : unitAt.{u}) : unitAtCanon.{u} = t := @Eq.refl _ t

/-- **(A), the other direction.** Which side the redex is on does not matter;
what matters is that *some* side is one. -/
example (t : unitAt.{u}) : t = unitAtCanon.{u} := @Eq.refl _ t

/-- **(A) is what makes the conversion, not just the equation, go through**:
a motive applied at the canonical element and at an opaque one are the same
type. This is the step `Modelgen.chainDestruct` takes when `Pad.canonical`. -/
example (motive : unitAt.{u} → Sort u) (t : unitAt.{u})
    (m : motive unitAtCanon.{u}) : motive t := m

-- **(B) fails**, and first by the unifier: `rfl` elaborates at `?m = ?m`,
-- which will not unify with `x = y`.
/--
error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  x = y
-/
#guard_msgs (error) in
example (x y : unitAt.{u}) : x = y := rfl

-- **(B) fails with the kernel forced too**, which is the case that settles
-- it: `@Eq.refl _ x` fixes the left side, so there is no metavariable left and
-- the only question is whether `x ≡ y`. It is not. Two opaque variables trigger
-- no eta expansion on either side, and proof irrelevance never gets to see the
-- payloads because nothing exposes them.
--
-- **So a construction may not assume two arbitrary inhabitants of `PULiftP ⊤`
-- collapse.** `modelgen` does not; the header lists every place it relies on
-- the lift and both are redexes.
/--
error: Type mismatch
  Eq.refl x
has type
  x = x
but is expected to have type
  x = y
-/
#guard_msgs (error) in
example (x y : unitAt.{u}) : x = y := @Eq.refl _ x

/-- **And yet (B) is provable, with no axiom** — which is what makes the two
results above a statement about the *algorithm* and not about the theory.
Every step here is a redex the kernel does take: `up (down x) ≡ x` by eta,
`down x = down y` by proof irrelevance, and `congrArg` in between. So the
conversion is not transitive at this shape, and a generator that wants two
opaque inhabitants identified must emit this proof rather than rely on a
conversion. `modelgen` never needs to; its unreachable transport branch is
this proof's shape. -/
example (x y : unitAt.{u}) : x = y :=
  Eq.trans (Eq.symm (congrArg PULiftP.up (rfl : down x = down y))) rfl

/-- info: 'PULiftP.up' does not depend on any axioms -/
#guard_msgs in #print axioms PULiftP.up

-- ═════════════════════════════════════════════════════════════════════════
-- §3. Emptiness, the other property the basis member is in for.
-- ═════════════════════════════════════════════════════════════════════════

/-- Church `⊥`. -/
def FalseC : Prop := ∀ p : Prop, p

/-- `PULiftP ⊥` is **empty at every level** — this is what `PEmpty` models as,
and what no type the old five-primitive basis reached at a bare `Sort u`
could be. -/
example (x : PULiftP.{u} FalseC) : FalseC := down x
example (x : PULiftP.{u} FalseC) (C : Prop) : C := down x C
