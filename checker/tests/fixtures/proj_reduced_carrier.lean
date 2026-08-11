/-
# A projection whose **structure has to be computed** — the `brecOn` nest, without `Nat`

`NAT-BRIDGE-FEASIBILITY.md` §2.3 recorded `Nat.add`'s value as blocked on
`proj(PProd)`, and §6.1 recorded *why* as open with the obvious hypothesis
already refuted: a projection out of a `Nat.below`-typed subject certifies in
isolation, and `080_PProd.snd`/`081_PSigma.snd` certify, so the discriminator is
neither `PProd` nor `below`. This file is that question with **no `Nat` in it**,
and it says what the discriminator is.

## Why this file has to compile a structural recursion

The shape cannot be written in surface syntax. `p.fst` on a variable elaborates
to `Pair.fst α β p` — an *application* of the projection function, whose own
body projects a binder typed syntactically `Pair`. A raw `Expr.proj` at a
subject whose type merely *reduces* to a structure is emitted only by Lean's
**structural-recursion compiler**: `addN`'s step case becomes

```
fun k (f : N.below (motive := fun _ => N → N) (N.s k)) a => N.s (f.1 a)
```

and `N.below motive (N.s k)` is an `N.rec` application — it reduces to a
`PProd` and is not one. That is `Nat.add`'s shape exactly, with `Nat` replaced
by a two-constructor Peano type this file declares itself.

**A fixture that wrote the projection by hand would be green under the bug**,
which is what a first draft of this file measured: eight hand-written cells,
`constEv 12/12`, before and after.

## The two causes, both in `mini::proj_data::typing`

Each is sufficient on its own to decline the projection with the clause's own
label, and neither subsumes the other — measured across all four fix
combinations, `mini/tests/designed.rs`.

**(1) The parameter memberships were not converted.**
`Interp::beta_spine` compares each premise's set against the nest's own domain
*on the nose*, and this route built those premises straight out of
`infer_type`. `N.below motive (N.s k)` reduces to `PProd (motive k) (N.rec …
k)`, and the second parameter's inferred type is `(fun _ => Type) k` — a redex,
because a recursor's conclusion is `motive major` and mini substitutes rather
than reduces — where the declaration says `Sort 1`. The two are defeq and not
identical, so the comparison failed. The fix is `Checker::nest_arg_mems`, which
already existed for *constructor* nests and runs `beta_premise` — a conversion
exactly when the two spellings differ — per argument.

**(2) The subject's membership never travelled to the reduced type.**
The route read the structure's identity off `c.whnf(&te.ty)`, the
acceptance-only reduction, and then used the *unreduced* typing as the major
premise. `beta_spine` produced an equation whose left endpoint is the `PProd`
spine while the membership in hand was still about `N.below motive (N.s k)`,
and `retarget_set` had two unrelated sets. The fix is `whnf_typing`, which the
`Expr::App` clause already uses for precisely this composition.

## The cells

| declaration | what it is |
| --- | --- |
| `recAddN`, `recAddNZ`, `recAddNS` | **the control**: the same recursion straight onto `N.rec`, no nest, no projection |
| `addN`, `addNZ`, `addNS` | the nest, recursion on the **second** argument — `Nat.add`'s shape |
| `dblN`, `dblNZ`, `dblNS` | the nest with a **non-function** motive, `fun _ => N` — `Nat.pow`'s axis |
| `leN`, `leNZ`, `leNSZ`, `leNSS` | the nest, recursion on the **first** of two arguments, into a two-constructor result — `Nat.ble`'s shape |
| `pairFst`, `pairSnd` | a hand-written projection at a syntactic `PProd`, which certified before this change and must keep certifying |

The control is what makes the file a *comparison* rather than a measurement:
`recAddN` states the same two equations about the same recursion and certified
throughout, so a change that broke it would be visible here and not confusable
with the nest.

Both fields are projected in `pairFst`/`pairSnd`, and the two nests recurse on
*different* arguments, so a route that clamped to the first parameter or the
first field is not passed by accident.

## Why this one imports `Init.Prelude`

Every other fixture here is `prelude` and declares what it needs, and this one
cannot be: compiling a `match` needs the elaborator's own equation machinery,
and a `prelude` file that declares only `Eq`, `PUnit`, `PProd` and `Unit` fails
with *"Tactic `cases` failed: not applicable"* — measured, at `v4.29.1`. So it
does what `nat_char_equations.lean` does: imports the prelude and lets
`--#export` cut the result down to the transitive closure of the declarations
named above.

**`Nat` is not in that closure**, which is the claim the file exists to support
and is checked rather than asserted — `mini/tests/designed.rs` greps the export
for the name.

-/
import Init.Prelude

--#export N recAddN recAddNZ recAddNS
--#export addN addNZ addNS
--#export dblN dblNZ dblNS
--#export leN leNZ leNSZ leNSS
--#export pairFst pairSnd

/-- Peano-shaped, so the structural compiler has a step case to compile. **Not
    `Nat`**: a fresh declaration, with no literals, no `OfNat`, and nothing the
    kernel accelerates anywhere near it. -/
inductive N : Type where
  | z : N
  | s : N → N

-- ── the control: primitive recursion written straight onto `N.rec` ──────────

noncomputable def recAddN (n m : N) : N :=
  N.rec (motive := fun _ => N) n (fun _ ih => N.s ih) m

theorem recAddNZ (n : N) : Eq (recAddN n N.z) n := Eq.refl _
theorem recAddNS (n m : N) : Eq (recAddN n (N.s m)) (N.s (recAddN n m)) := Eq.refl _

-- ── the nest, on the second argument — `Nat.add`'s shape ────────────────────

def addN (n : N) (m : N) : N :=
  match m with
  | N.z => n
  | N.s k => N.s (addN n k)

theorem addNZ (n : N) : Eq (addN n N.z) n := Eq.refl _
theorem addNS (n m : N) : Eq (addN n (N.s m)) (N.s (addN n m)) := Eq.refl _

-- ── the nest, on the *only* argument, motive `fun _ => N` ─────────────────
--
-- `Nat.pow`'s axis: `addN`'s motive is `fun _ => N → N`, a function type, and
-- this one's is not. A route that only ever met a function-typed motive is not
-- passed by accident.

def dblN (n : N) : N :=
  match n with
  | N.z => N.z
  | N.s k => N.s (N.s (dblN k))

theorem dblNZ : Eq (dblN N.z) N.z := Eq.refl _
theorem dblNS (n : N) : Eq (dblN (N.s n)) (N.s (N.s (dblN n))) := Eq.refl _

-- ── the nest, on the **first** of two arguments — `Nat.ble`'s shape ─────────
--
-- Nested single-scrutinee matches rather than one two-discriminant match: the
-- dependent pattern matcher needs machinery `Init.Prelude` has and this
-- `prelude` file does not, and the nest it compiles to is the same either way.

def leN (n : N) (m : N) : Bool :=
  match n with
  | N.z => Bool.true
  | N.s a =>
    match m with
    | N.z => Bool.false
    | N.s b => leN a b

theorem leNZ (m : N) : Eq (leN N.z m) Bool.true := Eq.refl _
theorem leNSZ (n : N) : Eq (leN (N.s n) N.z) Bool.false := Eq.refl _
theorem leNSS (n m : N) : Eq (leN (N.s n) (N.s m)) (leN n m) := Eq.refl _

-- ── the projection that already worked, which must keep working ─────────────

def pairFst (α : Type) (β : Type) (p : PProd α β) : α := p.fst
def pairSnd (α : Type) (β : Type) (p : PProd α β) : β := p.snd
