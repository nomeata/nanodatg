import Modelgen.Mutual

/-!
# The model of a **simple inductive from five primitives**, generated

The third construction in this package, behind `--prim-models` and off by
default. Where the first two constructions remove *nesting* and *mutuality*,
this one removes the inductive declaration itself: a plain (non-mutual,
non-nested) inductive's carrier, constructors, recursor and ι rules are
emitted as ordinary `def`s and `theorem`s over a fixed basis of primitive
inductives —

    Eq   PSigma   Nat   Acc   PULiftP

— each spliced into the output at Lean's own shape if the input lacks it,
exactly as the existing prelude splice does for `Eq`. A consumer that
recognises the four interface names then needs to implement only the five
primitives (plus `Quot`), not general inductives.

**`False` is not in the basis**: it is *derived* (Church `∀ p : Prop, p`,
with the `Sort w` eliminator from `0 = 1` plus a `Nat.rec`-built family to
transport along — [`Modelgen.cfalseElim`]), so `False` models like any other
declaration. Its place is taken by **`PULiftP.{u} (p : Prop) : Sort u`**,
the lift of a proposition to a bare variable sort. Lean's *elaborator*
refuses that declaration; Lean's *kernel* takes it and grants it large
elimination by the subsingleton rule, and `addDeclCore` is the kernel. Core
itself crosses the same line twice, for `PUnit` and `PEmpty`, with
`set_option bootstrap.inductiveCheckResultingUniverse false`
(`Init/Prelude.lean:123,211`).

The Σ is **`PSigma`-shaped** — `{α : Sort u} → (α → Sort v) →
Sort (max 1 u v)` — because `Subtype`, structures with `Prop` fields, and
every `Prop`-fibred pair in the constructions below need a Σ over `Sort`,
which a `Type`-only `Sigma` cannot give without `PLift`, a sixth inductive.
`Acc` is in the basis for the recursive `Type`-valued construction, which is
not implemented here, and is therefore not yet spliced: the prelude splice's
rule is "only what a model actually needs".

## The three routes, by the carrier's sort

**Type route** — carrier sort `w` never zero:

```text
T._model.self p⃗ := Σ'(n : Nat), F n        F : a Nat.rec cases tower
F ȷ̄  := the j-th constructor's field chain  (right-nested PSigma,
        boxed and padded to exactly Sort w when the levels demand it)
F n  := PULiftP.{w} ⊥, an empty type at Sort w, for n ≥ #ctors
```

The recursor destructs the pair, cases on the tag with `Nat.rec` — the large
elimination the basis buys, and the reason `Nat` is in it — and then
destructs the chain. Two level repairs keep the chain at exactly `Sort w`:

* **A pad** closes a level gap. At a `dsingOk` level it is `D`
  ([`Modelgen.dsingAt`]); at any other level — a bare parameter in the gap,
  `PULift`'s shape — it is `PULiftP.{ℓ} ⊤` ([`Modelgen.unitAt`]), which
  exists at *every* level. **Both are definitionally canonical**: structure
  eta on `PULiftP` plus proof irrelevance on `⊤` collapses every element
  onto the canonical one, so no pad costs a transport. The `False`-Π
  singleton this replaced was not canonical and cost a `funext`.
* **A box** ([`Modelgen.boxTyOf`]) absorbs an `imax`: a Π-typed field's level
  is an `imax` chain (`Trans.mk`'s shape) and no pad subsumes an `imax` under
  a `max` — what collapses it is a never-`Prop` codomain, so the field is
  stored with its codomain wrapped as `Σ'(_ : S), D 1` and unboxed by
  projection wherever the minor consumes it; `unbox (box v) ≡ v` by βι,
  structure eta, proof irrelevance and function eta, no transport.

**Church routes** — carrier sort literally `0`, or **maybe-zero**. One
construction serves both. The carrier is the impredicative Church encoding

```text
T._model.self p⃗ ι⃗ := ∀ C : (∀ ι⃗, Prop), k⃗ → C ι⃗
```

with `k_j` constructor `j`'s telescope, `T p⃗` replaced by `C` at its
recursive fields as well as at its result ([`Modelgen.churchSwapAt`]); and at
a maybe-zero sort that same proposition under `PULiftP.{w}`, which puts it at
exactly `Sort w` for any `w`. The constructors are the folds, `up` of the
folds under a lift. There is **no transport between the two**: structure eta
gives `t ≡ up (down t)`, so `motive ι⃗ (up (down t))` and `motive ι⃗ t` are
convertible, and the maybe-zero route is the `Prop` route with a `down` at
one end and an `up` at the other.

Three recursors:

* **small elimination, no indices, no recursion** — the fold at
  `C := motive t`. Every minor's motive is closed by definitional proof
  irrelevance.
* **small elimination, otherwise** — the fold at the Church *pair*
  `Pair ι⃗ := ∀ D : Prop, (Self ι⃗ → (∀ h : Self ι⃗, motive ι⃗ h) → D) → D`
  ([`Modelgen.pairArm`]). The plain fold does not serve here: a minor premise
  wants `motive ι⃗_j (c_j f⃗)` and the fold offers `C ι⃗_j`, which proof
  irrelevance stops identifying once the index moves; and a *recursive* minor
  premise needs a carrier element to apply itself to, which only the pair's
  first component supplies.
* **large elimination** — zero constructors: Church `⊥`'s `Sort v`
  eliminator. One constructor, no indices: the subsingleton rule that minted
  the recursor says every field is a proposition, so extract each by
  instantiating the encoding at the field's own type, sequentially, with
  proof irrelevance closing the motive.

**Why the maybe-zero collapse is a model and not a cheat.** At a maybe-zero
sort the contract never forces two provably distinct elements: zero
constructors and the subsingleton shape large-eliminate and are subsingletons
anyway, and everything else there small-eliminates, so the motive lands in
`Prop` and cannot discriminate. The lift of a proposition is exactly the
right size — which is also why `PEmpty` models: `PULiftP ⊥` is *empty*, where
every type the old basis reached at a bare sort was inhabited.

**Every ι theorem is `Eq.refl`** on all three routes. On the Church routes
with a `Prop`-valued motive that is free for a reason unrelated to reduction:
both sides of every ι equation are proofs of one proposition.

## What declines, and why

* **recursive at a never-zero sort** (`List`, `Lean.Name`, …) — the carrier
  needs the tuple-tower construction for linear recursion, or W/path in
  general. `scripts/inductive-basis/LinearRec.lean` compiles the linear arm
  (three targets, every ι by `rfl`, no `funext`); it is not wired up here.
* **indexed at a never-zero sort** (the composed `T._model.aux`) — thesis
  §5.2's skeleton-plus-`good`; `scripts/inductive-basis/IndexedCarve.lean`
  compiles it on the thesis's own example.
* **an indexed subsingleton** (`HEq`) — the packed-index-equation model,
  INDUCTIVE-BASIS §3.2's degenerate `r := ⊥` case, compiled as `HEq'` in
  `scripts/inductive-basis/PropArms.lean`.
* **a recursive subsingleton** (`Inf`) — the `AccPhi` carrier of
  INDUCTIVE-BASIS §3.2, which is where `Acc` finally earns its place.
  `scripts/inductive-basis/AccPhi.lean` compiles it, *and* refutes the
  thesis's own `accφ` reduction at thesis.txt:1838.
* **indices or recursion at a maybe-zero sort** — neither is threaded
  through the lift.
* **a level gap no pad or box closes** — an `imax` in a field's level that
  boxing does not collapse (an `imax`-leveled *domain* inside the field).
  This one is a **level-incompleteness** decline, not a type error: the
  padded chain equals the carrier's level at every instantiation and Lean's
  normal-form level defeq does not see it. `MODELGEN.md` §8.6 has the
  lean4lean cross-check.
* a field mentioning `T` other than as `∀ z⃗, T p⃗ e⃗` — a **nested**
  occurrence, which is layer 1's business.
* the five **basis primitives themselves** — the exemption that makes the
  construction well-founded.
-/

open Lean Meta

namespace Modelgen

/-- The five, by name. A declaration in this set is the basis and is not
modelled — the exemption that makes the construction well-founded.

`False` is **not** among them: it is derived (Church `∀ p : Prop, p`, with
its `Sort w` eliminator from `0 = 1` plus a `Nat.rec`-built family to
transport along — [`Modelgen.cfalseElim`]), so `False` models like any other
declaration. `PULiftP` takes its place. -/
def primBasis : List Name := [`Eq, `PSigma, `Nat, `Acc, `PULiftP]

/-- **`PULiftP`**: `inductive PULiftP.{u} (p : Prop) : Sort u | up : p →
PULiftP p` — the lift of a proposition to a **bare variable sort**.

Lean's *elaborator* refuses this declaration (its resultant sort is `Prop` at
some instantiations and not others); Lean's *kernel* admits it, because the
kernel checks only the per-argument inequality `is_geq(u, 0)`, and grants it
**large elimination** by the subsingleton rule — one constructor, its one
argument a proposition. Core crosses the same line twice, for `PUnit` and
`PEmpty`, with `set_option bootstrap.inductiveCheckResultingUniverse false`
(`Init/Prelude.lean:123,211`). Nothing here goes through the elaborator: the
declaration is handed to `Environment.addDeclCore` with checking on, which is
the kernel, which takes it.

It is the basis's only type former at a bare `Sort u` that can be **empty**,
and that is what it is in the basis for: it closes the whole maybe-zero
class in one primitive — `PEmpty`, `PUnit`, `Eq`-at-`Sort v`, enums — and it
retires the `False`-Π pad, whose uniqueness cost a `funext` where
`PULiftP`'s costs a recursor call and proof irrelevance. -/
def puliftDecl : Declaration :=
  let lu := Level.param `u
  let ty : Expr := .forallE `p (.sort .zero) (.sort lu) .default
  let upTy : Expr := .forallE `p (.sort .zero)
    (.forallE `h (.bvar 0) (.app (.const `PULiftP [lu]) (.bvar 1)) .default) .implicit
  .inductDecl [`u] 1
    [{ name := `PULiftP, type := ty,
       ctors := [{ name := `PULiftP.up, type := upTy }] }] false

/-- **Lean's `Nat`**, as `Init/Prelude.lean` declares it. The models build
tags as `succ` chains, so nothing here depends on literals. -/
def natDecl : Declaration :=
  let nat : Expr := .const `Nat []
  .inductDecl [] 0
    [{ name := `Nat, type := .sort (.succ .zero)
       ctors := [{ name := `Nat.zero, type := nat },
                 { name := `Nat.succ, type := .forallE `n nat nat .default }] }] false

/-- **Lean's `PSigma`**: `{α : Sort u} → (β : α → Sort v) →
Sort (max 1 u v)` with `mk (fst : α) (snd : β fst)`. -/
def psigmaDecl : Declaration :=
  let lu := Level.param `u
  let lv := Level.param `v
  let w := mkLevelMax' (mkLevelMax' (.succ .zero) lu) lv
  let ty : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default) (.sort w) .default) .implicit
  let mkTy : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.forallE `fst (.bvar 1)
        (.forallE `snd (.app (.bvar 1) (.bvar 0))
          (mkAppN (.const `PSigma [lu, lv]) #[.bvar 3, .bvar 2]) .default)
        .default) .implicit) .implicit
  .inductDecl [`u, `v] 2
    [{ name := `PSigma, type := ty, ctors := [{ name := `PSigma.mk, type := mkTy }] }] false

/-- One primitive, checked or spliced. `check` runs on a present declaration
and says what is wrong with it; a missing one is spliced at Lean's shape and
re-checked. The pattern is [`Modelgen.ensureEq`]'s, and the name guard is
the same one. -/
def ensurePrim (n : Name) (guard : List Name) (d : Declaration)
    (check : Environment → Except String Unit) (reserved : Std.HashSet Name) :
    GenM (Array Declaration) := do
  if (← getEnv).constants.contains n then
    match check (← getEnv) with
    | .ok () => return #[]
    | .error why => declineWith (.notLeans n why)
  for g in guard do
    if reserved.contains g then declineWith (.nameTaken g)
  addChecked d
  match check (← getEnv) with
  | .ok () => return #[d]
  | .error why => badShape s!"the spliced {n} is not Lean's ({why})"

/-- `PULiftP` at the shape above, **including the large elimination the whole
maybe-zero territory rests on**: `PULiftP.rec` must carry a motive universe.
A `PULiftP` in the input that is small-eliminating is not Lean's and is
refused here rather than silently used. -/
def checkPULiftP (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `PULiftP | throw "it is not an inductive type"
  unless iv.numParams == 1 && iv.numIndices == 0 && iv.ctors == [`PULiftP.up]
      && iv.levelParams.length == 1 do
    throw "it is not a one-parameter, one-constructor lift with a single level parameter"
  let some (.recInfo rv) := env.constants.find? `PULiftP.rec | throw "PULiftP.rec is not a recursor"
  unless rv.levelParams.length == 2 do
    throw "PULiftP.rec is not large-eliminating (no motive universe)"

/-- `Nat` at Lean's shape, **including the large elimination the whole Type
route rests on**: `Nat.rec` must carry a motive universe. The commission
asked for this to be checked rather than assumed, and this is where it is
checked — on the input's own `Nat` as much as on a spliced one. -/
def checkNat (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `Nat | throw "it is not an inductive type"
  unless iv.numParams == 0 && iv.numIndices == 0 && iv.ctors == [`Nat.zero, `Nat.succ] do
    throw "it is not zero/succ with 0 parameters and 0 indices"
  unless iv.type == Expr.sort (.succ .zero) do throw "it does not land in Type"
  let some (.recInfo rv) := env.constants.find? `Nat.rec | throw "Nat.rec is not a recursor"
  unless rv.levelParams.length == 1 do
    throw "Nat.rec is not large-eliminating (no motive universe)"

def checkPSigma (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `PSigma | throw "it is not an inductive type"
  unless iv.numParams == 2 && iv.numIndices == 0 && iv.ctors == [`PSigma.mk]
      && iv.levelParams.length == 2 do
    throw "it is not a two-parameter, one-constructor Sort-polymorphic pair"
  let some (.recInfo rv) := env.constants.find? `PSigma.rec | throw "PSigma.rec is not a recursor"
  unless rv.levelParams.length == 3 do
    throw "PSigma.rec is not large-eliminating"

def ensurePULiftP (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `PULiftP [`PULiftP, `PULiftP.up] puliftDecl checkPULiftP reserved
def ensureNat (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `Nat [`Nat, `Nat.zero, `Nat.succ] natDecl checkNat reserved
def ensurePSigma (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `PSigma [`PSigma, `PSigma.mk] psigmaDecl checkPSigma reserved

/-! ## Expression kit -/

/-- `succ^j zero` — a tag, as constructor chains so the splice needs no
literal support. -/
def natNumeral : Nat → Expr
  | 0 => .const `Nat.zero []
  | j + 1 => .app (.const `Nat.succ []) (natNumeral j)

/-- `succ^j e`. -/
def natSuccs : Nat → Expr → Expr
  | 0, e => e
  | j + 1, e => .app (.const `Nat.succ []) (natSuccs j e)

def psigmaT (u v : Level) (α β : Expr) : Expr :=
  mkAppN (.const `PSigma [u, v]) #[α, β]

def psigmaMk (u v : Level) (α β fst snd : Expr) : Expr :=
  mkAppN (.const `PSigma.mk [u, v]) #[α, β, fst, snd]

def psigmaRec (s u v : Level) (α β motive m t : Expr) : Expr :=
  mkAppN (.const `PSigma.rec [s, u, v]) #[α, β, motive, m, t]

/-- `PSigma.fst`, as a `PSigma.rec`. Structure eta makes `⟨fst y, snd y⟩ ≡ y`
for a neutral `y`, which is what lets a tuple be taken apart and put back
together with no transport. -/
def psigmaFst (u v : Level) (α β y : Expr) : Expr :=
  psigmaRec u u v α β (.lam `p (psigmaT u v α β) α .default)
    (.lam `a α (.lam `b (Expr.app β (.bvar 0)).headBeta (.bvar 1) .default) .default) y

/-- `PSigma.snd`, at the motive `fun z => β (fst z)`. -/
def psigmaSnd (u v : Level) (α β y : Expr) : Expr :=
  let motive := Expr.lam `p (psigmaT u v α β)
    (Expr.app β (psigmaFst u v α β (.bvar 0))).headBeta .default
  psigmaRec v u v α β motive
    (.lam `a α (.lam `b (Expr.app β (.bvar 0)).headBeta (.bvar 0) .default) .default) y

def natRec (s : Level) (motive z sc t : Expr) : Expr :=
  mkAppN (.const `Nat.rec [s]) #[motive, z, sc, t]

/-! ### The two Church propositions, and the lift

`False` is no longer a primitive, so the two propositions the constructions
seed with are written out: `⊥ := ∀ p : Prop, p` and `⊤ := ∀ C : Prop, C → C`.
Both are pure Π — they consume no primitive at all. What they lack is `⊥`'s
`Sort w` eliminator, which [`Modelgen.cfalseElim`] supplies from `Nat` and
`Eq`. -/

/-- The always-true proposition `∀ C : Prop, C → C`, and its inhabitant. -/
def trueP : Expr :=
  .forallE `C (.sort .zero) (.forallE `c (.bvar 0) (.bvar 1) .default) .default
def trueI : Expr :=
  .lam `C (.sort .zero) (.lam `c (.bvar 0) (.bvar 0) .default) .default

/-- **Church `False`**: `∀ p : Prop, p`. Small elimination is instantiation;
large elimination is [`Modelgen.cfalseElim`]. -/
def falseP : Expr :=
  .forallE `p (.sort .zero) (.bvar 0) .default

/-- `PULiftP.{ℓ} p` — the proposition `p` at exactly `Sort ℓ`, for **any** `ℓ`
whatsoever, empty exactly when `p` is. -/
def puliftT (ℓ : Level) (p : Expr) : Expr :=
  mkAppN (.const `PULiftP [ℓ]) #[p]

/-- `PULiftP.up.{ℓ} p h`. -/
def puliftUp (ℓ : Level) (p h : Expr) : Expr :=
  mkAppN (.const `PULiftP.up [ℓ]) #[p, h]

/-- `PULiftP.rec.{v,ℓ} p motive m t` — the lift's large eliminator. -/
def puliftRec (v ℓ : Level) (p motive m t : Expr) : Expr :=
  mkAppN (.const `PULiftP.rec [v, ℓ]) #[p, motive, m, t]

/-- `down : PULiftP.{ℓ} p → p`, by the recursor at a `Prop` motive. -/
def puliftDown (ℓ : Level) (p t : Expr) : Expr :=
  puliftRec .zero ℓ p (.lam `x (puliftT ℓ p) p .default) (.lam `h p (.bvar 0) .default) t

/-- **The lift's eta is definitional.** `PULiftP` is a single-constructor,
index-free, non-recursive inductive, so the kernel's eta-for-structures fires
on it — `t ≡ up (down t)` for every `t`, at every level, `Prop` or not. So
this is `Eq.refl`, not a recursor call, and it is here only so that the one
place that needs an *equation* rather than a conversion has one.

Two consequences the construction leans on. `PULiftP ⊤` is a **definitional
singleton** at every level (eta collapses `x` onto `up (down x)`, proof
irrelevance collapses `down x` onto `⊤`'s inhabitant), so a pad built from it
needs no transport — which is what makes it a strict improvement on the
`False`-Π pad, whose uniqueness was `funext`. And `motive (up (down t))` and
`motive t` are convertible, so the maybe-zero route's recursor is the `Prop`
route's with `up`/`down` at the ends and nothing in between. -/
def puliftEta (eqi : EqInfo) (ℓ : Level) (p t : Expr) : Expr :=
  eqi.refl' ℓ (puliftT ℓ p) t

/-- An **empty** type at exactly `Sort w`, for any `w`: the lift of Church
`False`. This is the fibre beyond a tag tower's last constructor, and — at a
maybe-zero `w` — the whole of `PEmpty`'s carrier. -/
def emptyAt (w : Level) : Expr :=
  puliftT w falseP

/-- `Eq.rec.{v,ℓ} α a (fun z _ => fam z) base b h` — transport
`base : fam a` to `fam b` along `h : Eq a b`. -/
def transportAlong (eqi : EqInfo) (v ℓ : Level) (α a b h base : Expr)
    (fam : Expr → GenM Expr) : GenM Expr := do
  let motive ← withLocalDeclD `z α fun z => do
    withLocalDeclD `hz (eqi.mk' ℓ α a z) fun hz => do
      mkLambdaFVars #[z, hz] (← fam z)
  return eqi.recAt v ℓ α a motive base b h

/-- `Eq b a` from `h : Eq a b`, as one `Eq.rec` at a `Prop` motive. -/
def symmOf (eqi : EqInfo) (ℓ : Level) (α a b h : Expr) : GenM Expr :=
  transportAlong eqi .zero ℓ α a b h (eqi.refl' ℓ α a) fun z => pure (eqi.mk' ℓ α z a)

/-- **Church `False`'s `Sort v` eliminator**, which is what lets `False` leave
the basis: from `h : ∀ p : Prop, p` take `h (0 = 1) : 0 = 1`, build the family
`fun n => Nat.rec (fun _ => Sort v) (PULiftP.{v} ⊤) (fun _ _ => C) n` — whose
value at `0` is an *inhabited* type and at `1` is `C` — and transport the
inhabitant along the equation.

`Nat`'s large elimination is what makes the family; `Eq`'s is what transports;
`PULiftP` is what puts an inhabited type at `Sort v` for a **bare** `v`, which
is exactly the gap the old basis filled with `False` itself. Splice all three
before calling this. -/
def cfalseElim (eqi : EqInfo) (v : Level) (C h : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let unitAt := puliftT v trueP
  let fam := fun (n : Expr) =>
    natRec (.succ v) (.lam `x natT (.sort v) .default) unitAt
      (.lam `m natT (.lam `ih (.sort v) C .default) .default) n
  let eqn := eqi.mk' (.succ .zero) natT (natNumeral 0) (natNumeral 1)
  transportAlong eqi v (.succ .zero) natT (natNumeral 0) (natNumeral 1)
    (.app h eqn) (puliftUp v trueP trueI) (fun z => pure (fam z))

/-- Anything at all out of an inhabitant of [`Modelgen.emptyAt`]: project the
Church `⊥` out of the lift, then eliminate it. -/
def emptyAtElim (eqi : EqInfo) (v w : Level) (C e : Expr) : GenM Expr :=
  cfalseElim eqi v C (puliftDown w falseP e)

/-! ## The singleton at an arbitrary level

`Sort ℓ` for a **bare or variable** `ℓ` is out of every *other* basis former's
reach — `Eq` and `Acc` land in `Prop`, `Nat` in `Type`, `PSigma` at
`max 1 u v`, and a Π lands there only through an `imax` collapse, which needs
a `Sort ℓ`-valued *body*. `PULiftP` is the primitive that lands there
directly, for **any** `ℓ` whatsoever, and — unlike the `False`-Π family the
old basis used — it is empty exactly when its proposition is. So there are two
carriers at such a sort, not one: `PULiftP ⊤` (the singleton, below) and
`PULiftP ⊥` ([`Modelgen.emptyAt`]), and `PEmpty` is no longer out of reach.

Like [`Modelgen.dsingAt`]'s pads the singleton **is** definitionally
canonical — structure eta on `PULiftP` plus proof irrelevance on `⊤` — so
wherever one is destructed the applied minor already has the target type and
no transport rides along. This is where the
`False`-Π singleton cost a `funext`. In fact the lift's eta is *definitional*
(structure eta on `PULiftP`), so the destructor needs no transport at all and
ι is `Eq.refl` with nothing to erase. -/

/-- The singleton at exactly `Sort ℓ`: the lift of `⊤`. -/
def unitAt (ℓ : Level) : Expr := puliftT ℓ trueP

/-- Its canonical element. -/
def unitAtCanon (ℓ : Level) : Expr := puliftUp ℓ trueP trueI

/-- `Eq canon t` for `t : unitAt ℓ`. [`Modelgen.puliftEta`] proves
`Eq (up (down t)) t`, and `up (down t)` is *definitionally* the canonical
element: both components are proofs of `⊤`, and proof irrelevance closes it.
No `funext`. -/
def unitAtUniq (eqi : EqInfo) (ℓ : Level) (t : Expr) : Expr :=
  puliftEta eqi ℓ trueP t

/-- Is a pad at this level buildable? [`Modelgen.dsingAt`]'s domain, asked
before anything is spliced so that a decline costs no splice. -/
partial def dsingOk (ℓ : Level) : Bool :=
  match ℓ.normalize with
  | .succ _ => true
  | .max a b => dsingOk a && dsingOk b
  | _ => false

/-- A **definitionally-canonical singleton at exactly `Sort ℓ`**: every
element is *defeq* to the canonical one, by structure eta on `PSigma` and
proof irrelevance on the components — so a pad costs no transport and no
`funext`, and ι stays `Eq.refl`.

`D 1 := Σ'(_ : ⊤), ⊤` with `⊤ := ∀ C : Prop, C → C`; `D (a+1) :=
(α : Sort a) → D 1`, whose Π is at `imax (a+1) 1 = a+1`; `D (max a b) :=
Σ'(_ : D a), D b`. -/
partial def dsingAt (ℓ : Level) : GenM (Expr × Expr) := do
  let d1 := psigmaT .zero .zero trueP (.lam `x trueP trueP .default)
  let c1 := psigmaMk .zero .zero trueP (.lam `x trueP trueP .default) trueI trueI
  match ℓ.normalize with
  | .succ .zero => return (d1, c1)
  | .succ a =>
    return (.forallE `α (.sort a) d1 .default, .lam `α (.sort a) c1 .default)
  | .max a b =>
    let (ta, ca) ← dsingAt a
    let (tb, cb) ← dsingAt b
    let β := Expr.lam `x ta tb .default
    return (psigmaT a b ta β, psigmaMk a b ta β ca cb)
  | _ => badShape s!"no pad at Sort {ℓ}"

/-- A chain's pad: its type, its type's level, and its canonical element.
`canonical` says which of the two pad families it is: a [`Modelgen.dsingAt`]
pad, every element **defeq** to `canon` so no uniqueness proof rides along —
or, at a level `dsingOk` cannot build (a bare parameter in the gap —
`PULift`'s shape), the [`Modelgen.unitAt`] lift, whose uniqueness is
propositional and whose destruction transports along it. -/
structure Pad where
  ty : Expr
  lv : Level
  canon : Expr
  canonical : Bool

/-! ## Boxing a field whose level is an `imax`

A Π-typed field's level is an `imax` chain — `Trans.mk`'s field `(a b c : …) →
r a b → s b c → t a c` reaches `Sort (imax u₁ (imax u₂ (imax u₃ (imax u
(imax v w)))))` — and no pad absorbs an `imax`: level defeq is normal-form
equality, and a `max` does not subsume an `imax` term even when both its sides
are present. What does collapse it is making the *codomain* never-`Prop`:
`imax a b = max a b` once `b` cannot be zero. So such a field is stored
**boxed** — the same telescope, the codomain `S` wrapped as `Σ'(_ : S), D 1` —
and its level normalizes to a plain `max`. The box pad is `D 1`, every element
of which is *defeq* to canonical, so `unbox (box v) ≡ v` and `box (unbox y) ≡
y` hold by βι, structure eta, proof irrelevance and function eta alone: no
transport, and ι stays `Eq.refl`. -/

/-- Is there an `imax` anywhere in the level? Asked of normal forms: a level
the pads cannot absorb. -/
partial def levelHasIMax : Level → Bool
  | .imax .. => true
  | .max a b => levelHasIMax a || levelHasIMax b
  | .succ a => levelHasIMax a
  | _ => false

/-- The boxed type: the field's telescope unchanged, the codomain `S` wrapped
as `Σ'(_ : S), D 1`. A field that is not a Π is the degenerate case `xs = []`.
-/
def boxTyOf (t : Expr) : GenM Expr := forallTelescope t fun xs S => do
  let ℓS ← ilevel S
  let (d1, _) ← dsingAt (.succ .zero)
  mkForallFVars xs (psigmaT ℓS (.succ .zero) S (.lam `x S d1 .default))

/-- `box`: eta-expand and pair each value of the codomain with the canonical
`D 1`. -/
def boxValOf (t v : Expr) : GenM Expr := forallTelescope t fun xs S => do
  let ℓS ← ilevel S
  let (d1, c1) ← dsingAt (.succ .zero)
  mkLambdaFVars xs (psigmaMk ℓS (.succ .zero) S (.lam `x S d1 .default) (mkAppN v xs) c1)

/-- `unbox`: first projection, pointwise, by `PSigma.rec` at the codomain's
own universe. -/
def unboxValOf (t v : Expr) : GenM Expr := forallTelescope t fun xs S => do
  let ℓS ← ilevel S
  let (d1, _) ← dsingAt (.succ .zero)
  let β := Expr.lam `x S d1 .default
  let motive := Expr.lam `p (psigmaT ℓS (.succ .zero) S β) S .default
  let m := Expr.lam `fst S (.lam `snd d1 (.bvar 1) .default) .default
  mkLambdaFVars xs (psigmaRec ℓS ℓS (.succ .zero) S β motive m (mkAppN v xs))

/-! ## One constructor's chain

A constructor's field telescope becomes a right-nested `PSigma` at exactly
`Sort w`. The builders below recurse on the (progressively instantiated)
telescope expression, so nothing is stored across scopes. `pad?` closes the
chain when the field levels do not already reach `w` — and always for a
nullary constructor. `boxed` says, per field, whether the field is stored
boxed ([`Modelgen.boxTyOf`]); a later field's type always depends on the
*unboxed* value, so the recursions instantiate with `unbox` of the bound
variable and the real value stays what the minor is applied to. -/

/-- The chain's type and level. `nf` is the field count; the telescope's
trailing result type is never entered. -/
partial def chainTy (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr)
    (i : Nat := 0) : GenM (Expr × Level) := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return (p.ty, p.lv)
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  if nf == 1 && pad?.isNone then
    return (st, ℓt)
  withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (psigmaT ℓt ℓi st (← mkLambdaFVars #[xv] inner),
      (mkLevelMax' (mkLevelMax' (.succ .zero) ℓt) ℓi).normalize)

/-- The tuple `⟨v₁, ⟨v₂, …⟩⟩` at the given field values — each boxed where its
plan says so — closed by the pad's canonical element when there is one. -/
partial def chainTuple (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr)
    (vals : Array Expr) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return p.canon
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let sv ← if bx then boxValOf t vals[i]! else pure vals[i]!
  if nf == 1 && pad?.isNone then
    return sv
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  let (β, ℓi) ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let snd ← chainTuple pad? boxed (nf - 1) (rest.instantiate1 vals[i]!) vals (i + 1)
  return psigmaMk ℓt ℓi st β sv snd

/-- The recursor's destructor for one chain: from `scrut : chainTy`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields, each unboxed where the
plan boxed it. A canonical pad costs nothing — `scrut` is defeq to its
canonical element. A [`Modelgen.unitAt`] pad is discharged by transporting
the applied minor along [`Modelgen.unitAtUniq`], and on a constructor
application that proof is a closed self-equality which K-like reduction on
`Eq.rec` erases — ι stays `Eq.refl` on both. -/
partial def chainDestruct (v : Level) (eqi : EqInfo)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr) (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (vals : Array Expr := #[]) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    if p.canonical then
      -- `scrut` is defeq to the pad's canonical element, so the applied minor
      -- already has the target type.
      return minorAt vals
    -- A lift pad: transport along its eta. No axiom rides along.
    return ← transportAlong eqi v p.lv p.ty p.canon scrut
      (unitAtUniq eqi p.lv scrut) (minorAt vals) (fun z => target (wrap z))
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  if nf == 1 && pad?.isNone then
    let rv ← if bx then unboxValOf t scrut else pure scrut
    return minorAt (vals.push rv)
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  let (β, ℓi) ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let motive ← withLocalDeclD `s (psigmaT ℓt ℓi st β) fun s => do
    mkLambdaFVars #[s] (← target (wrap s))
  let m ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    withLocalDeclD `s (mkApp β xv).headBeta fun s => do
      let wrap' := fun (z : Expr) => wrap (psigmaMk ℓt ℓi st β xv z)
      mkLambdaFVars #[xv, s] (← chainDestruct v eqi pad? boxed (nf - 1)
        (rest.instantiate1 rv) s wrap' target minorAt (vals.push rv) (i + 1))
  return psigmaRec v ℓt ℓi st β motive m scrut

/-! ## The Type route's recursor tower -/

/-- What one constructor contributes, at a given parameter scope. -/
structure PCtor where
  /-- The instantiated field telescope. -/
  tele : Expr
  nf : Nat
  pad? : Option Pad
  /-- Which fields are stored boxed ([`Modelgen.boxTyOf`]). -/
  boxed : Array Bool
  /-- The chain type. -/
  chain : Expr

instance : Inhabited PCtor := ⟨⟨default, 0, none, #[], default⟩⟩

/-- `F`'s cases tower over `scrut`: `chain_j` at tag `j̄`, empty above. -/
partial def fibreTower (w : Level) (cs : Array PCtor) (j : Nat) (scrut : Expr) :
    GenM Expr := do
  if j == cs.size then
    return emptyAt w
  let natT : Expr := .const `Nat []
  let sc ← withLocalDeclD `n natT fun n' => do
    withLocalDeclD `ih (.sort w) fun ih => do
      mkLambdaFVars #[n', ih] (← fibreTower w cs (j + 1) n')
  return natRec (.succ w) (.lam `x natT (.sort w) .default) cs[j]!.chain sc scrut

/-- The recursor's cases tower over the tag: at level `j` the zero case is
constructor `j`'s destructor and the successor case descends; past the last
constructor the fibre is empty and [`Modelgen.emptyAtElim`] closes it. `scrut`
is the level's own binder; the original tag is `succ^j scrut`. -/
partial def stepTower (v w : Level) (eqi : EqInfo) (fib : Expr)
    (tgt : Expr → Expr) (minorOf : Nat → Array Expr → Expr)
    (cs : Array PCtor) (j : Nat) (scrut : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let mkAt := fun (tag tup : Expr) => psigmaMk (.succ .zero) w natT fib tag tup
  let mot ← withLocalDeclD `m natT fun m => do
    let tag := natSuccs j m
    withLocalDeclD `f (mkApp fib tag).headBeta fun f => do
      mkLambdaFVars #[m] (← mkForallFVars #[f] (tgt (mkAt tag f)))
  let zc ← do
    let c := cs[j]!
    withLocalDeclD `f c.chain fun f => do
      let target := fun (tup : Expr) => pure (tgt (mkAt (natNumeral j) tup))
      let minorAt := minorOf j
      mkLambdaFVars #[f] (← chainDestruct v eqi c.pad? c.boxed c.nf c.tele f id target minorAt)
  let sc ← withLocalDeclD `m natT fun m => do
    let inner ←
      if j + 1 == cs.size then
        let tag := natSuccs (j + 1) m
        withLocalDeclD `f (emptyAt w) fun f => do
          mkLambdaFVars #[f] (← emptyAtElim eqi v w (tgt (mkAt tag f)) f)
      else
        stepTower v w eqi fib tgt minorOf cs (j + 1) m
    withLocalDeclD `ih (mkApp mot m).headBeta fun ih =>
      mkLambdaFVars #[m, ih] inner
  return natRec (mkLevelIMax' w v).normalize mot zc sc scrut

/-- The Church minor's type: the constructor's field telescope with the
result swapped for `C`. -/
partial def churchSwap (C : Expr) (nf : Nat) (t : Expr) : GenM Expr := do
  if nf == 0 then return C
  let .forallE x d b bi := t | badShape "telescope shorter than its field count"
  withLocalDecl x bi d fun xv => do
    mkForallFVars #[xv] (← churchSwap C (nf - 1) (b.instantiate1 xv))

/-- The `k_j` binders of the Church encoding, opened in one scope. -/
partial def churchBinders (kTys : Array Expr) (j : Nat) (ks : Array Expr)
    (k : Array Expr → GenM Expr) : GenM Expr := do
  if j == kTys.size then k ks
  else withLocalDeclD (Name.mkSimple s!"k{j}") kTys[j]! fun kv =>
    churchBinders kTys (j + 1) (ks.push kv) k

/-! ## Indices and recursion in the Church encoding

Two features the encoding above does not have, and both are one rewrite of the
minor-premise types away.

**Indices.** Quantify `C` over the whole index telescope instead of over
nothing: `T' p⃗ ι⃗ := ∀ C : (∀ ι⃗, Prop), k⃗ → C ι⃗`, with each minor `k_j`
ending in `C` applied to *constructor j's own* index expressions. The
declaration's parameters are only ever context, never analysed.

**Recursion.** A recursive field `f : ∀ z⃗, T p⃗ e⃗` becomes `∀ z⃗, C e⃗` in the
minor's type and `fun z⃗ => f z⃗ C k⃗` in the fold. Strict positivity for a
single non-nested inductive admits exactly that shape (thesis.txt:647–668), so
a field that mentions `T` in any *other* position is a nested occurrence and
is declined rather than mis-rewritten. -/

/-- A field of a constructor, classified. `rec? = some nb` says the field is a
recursive occurrence under `nb` binders — `nb = 0` for a bare `T p⃗ e⃗`. -/
structure PField where
  /-- The binder telescope's length, for a recursive field. -/
  rec? : Option Nat
  deriving Inhabited

/-- Rewrite a constructor's telescope for the Church encoding: recursive
fields' types and the result both get `C` in place of `T p⃗`. Returns the
rewritten telescope and the per-field classification.

`ni` is the index count; the arguments after the first `np` of an occurrence
of `T` are its index expressions, and they are copied verbatim. -/
partial def churchSwapAt (tname : Name) (np ni : Nat) (C : Expr) (nf : Nat) (t : Expr)
    (acc : Array PField := #[]) : GenM (Expr × Array PField) := do
  if nf == 0 then
    -- the constructor's result: `T p⃗ ι⃗_j` ↦ `C ι⃗_j`
    let args := t.getAppArgs
    unless t.getAppFn.isConstOf tname && args.size == np + ni do
      badShape s!"a constructor of {tname} does not end in {tname} applied to \
        {np} parameters and {ni} indices"
    return (mkAppN C (args.extract np args.size), acc)
  let .forallE x d b bi := t | badShape "telescope shorter than its field count"
  let mut d' := d
  let mut fld : PField := { rec? := none }
  if mentionsAny #[tname] d then
    let (dd, nb) ← forallTelescope d fun zs res => do
      let args := res.getAppArgs
      unless res.getAppFn.isConstOf tname && args.size == np + ni do
        badShape s!"a field of {tname} mentions {tname} other than as a recursive \
          occurrence (∀ z, {tname} p e) — a nested occurrence, which is layer 1's business"
      for z in zs do
        if mentionsAny #[tname] (← ityp z) then
          badShape s!"a recursive field of {tname} binds an argument whose type \
            mentions {tname}"
      return (← mkForallFVars zs (mkAppN C (args.extract np args.size)), zs.size)
    d' := dd
    fld := { rec? := some nb }
  withLocalDecl x bi d' fun xv => do
    -- A later field's type never depends on a recursive one (strict
    -- positivity forbids it), so instantiating with the rewritten binder is
    -- safe exactly where it matters and irrelevant elsewhere.
    let (rest, acc') ← churchSwapAt tname np ni C (nf - 1) (b.instantiate1 xv) (acc.push fld)
    return (← mkForallFVars #[xv] rest, acc')

/-! ## Linear recursion at a never-zero sort: the tuple tower

`INDUCTIVE-BASIS.md` §3.4, compiled in `scripts/inductive-basis/LinearRec.lean`
on three targets. A **linearly recursive** declaration is one whose every
constructor has at most one recursive field, with that field not under a
binder. Constructors then split into *base* (no recursive field) and *step*
(exactly one), and the carrier is a spine-indexed tower:

```text
V 0       := Σ'(tag : Nat), Base_tag           -- a Nat.rec tag tower
V (n+1)   := Σ'(tag : Nat), Step_tag (V n)     -- another, at the shorter spine
T         := Σ'(n : Nat), V n

base ctor c_j f⃗            := ⟨0,       ⟨bⱼ, chain f⃗⟩⟩
step ctor c_j pre r post   := ⟨r.1 + 1, ⟨sⱼ, chain (pre, r.2, post)⟩⟩
```

`n` counts recursive depth, so the representation is unique and no carve is
needed. The recursor is `PSigma.rec` on the outer pair, `Nat.rec` on the
spine, the existing tag towers inside each level, and `PSigma.rec` down each
chain — and **every ι rule is `Eq.refl`**, because at a step constructor the
recursive argument is rebuilt as `⟨n, r.2⟩`, which structure eta makes
definitionally `r`, and the induction hypothesis is the spine's own `Nat.rec`
at `r.1` applied to `r.2`, which is the recursor at `r` for the same reason.
No transport, no `funext`.

What it cannot do is a constructor with **two** recursive fields: the spine is
a single `Nat` and `⟨r.1 + 1, …⟩` has exactly one predecessor to take, so two
sub-terms at spines `n₁` and `n₂` cannot both sit in one fibre `V n` unless
the spine is generalised to a tree — which is the very inductive being built.
That is plan B's territory, and `Lean.ParserDescr` lives there. -/

/-- Which field of a constructor is the recursive one, if any. Declines the
shapes the tower cannot express, each by name. -/
def recSlotOf (tname : Name) (np : Nat) (cn : Name) (nf : Nat) (tele : Expr) :
    GenM (Option Nat) := do
  let mut cur := tele
  let mut slot : Option Nat := none
  for i in [0:nf] do
    let .forallE _ d b _ := cur | badShape "field telescope shorter than its field count"
    if mentionsAny #[tname] d then
      if slot.isSome then
        badShape s!"{cn} has two recursive fields: the tuple tower's spine is one \
Nat and a constructor takes one predecessor, so a branching constructor needs the \
W/path construction (plan B)"
      unless d.getAppFn.isConstOf tname do
        badShape s!"{cn} has a recursive field that is not a bare occurrence of \
{tname} — under a binder, or nested, neither of which the tuple tower reaches"
      slot := some i
    cur := b
  return slot

/-- The constructor's field telescope with its recursive field's type replaced
by the shorter spine's fibre `V n`. The recursive occurrence sits at `Sort w`
either way, so the storage plan computed on the export's telescope is the
plan for this one too. -/
partial def spineSwap (tname : Name) (Vn : Expr) (nf : Nat) (tele : Expr) :
    GenM Expr := do
  if nf == 0 then return tele
  let .forallE x d b bi := tele | badShape "field telescope shorter than its field count"
  let d' := if mentionsAny #[tname] d then Vn else d
  withLocalDecl x bi d' fun xv => do
    mkForallFVars #[xv] (← spineSwap tname Vn (nf - 1) (b.instantiate1 xv))

/-- The same classification as [`Modelgen.churchSwapAt`] makes, without the
rewrite — used where the *values* are built, since those are bound at the
model's restored telescope and not at the export's. -/
partial def classifyCtor (tname : Name) (nf : Nat) (tele : Expr)
    (acc : Array PField := #[]) : GenM (Array PField) := do
  if nf == 0 then return acc
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  let fld : PField ←
    if mentionsAny #[tname] d then
      forallTelescope d fun zs _ => pure { rec? := some zs.size }
    else pure { rec? := none }
  withLocalDecl x bi d fun xv =>
    classifyCtor tname (nf - 1) (b.instantiate1 xv) (acc.push fld)

/-- **One `Pair`-valued premise of the strong-induction fold.**

Walks constructor `j`'s *export* telescope, binding one variable per field —
a recursive field at `∀ z⃗, Pair e⃗` rather than at its own type — and ends at

    fun D k => k (c_j elems) (fun _h => minor elems ihs)

where, for each recursive slot, `elems` holds the carrier element read out of
that slot's pair and `ihs` the induction hypothesis read out beside it, both
pointwise under the field's own binders. The minor premise takes the fields in
declaration order and then the hypotheses, which is the order Lean's recursors
use.

The index expressions are taken from the export telescope as it is walked, not
read back off the built types: `Pair` is a λ, so `Pair e⃗` is a β-redex and
whether its arguments are still visible is a fact about whoever last touched
the expression. This is the bug that cost the first two attempts. -/
partial def pairArm (tname : Name) (np ni : Nat) (us : List Level)
    (selfAt : Array Expr → Expr) (pairAt : Array Expr → GenM Expr)
    (motive : Expr) (cN : Name) (minor : Expr) (ps : Array Expr)
    (nf : Nat) (tele : Expr) (elems ihs : Array Expr) : GenM Expr := do
  if nf == 0 then
    let args := tele.getAppArgs
    let isj := args.extract np args.size
    unless isj.size == ni do
      badShape s!"a constructor of {tname} does not present {ni} index arguments"
    let sfj := selfAt isj
    let built := mkAppN (.const cN us) (ps ++ elems)
    return ← withLocalDeclD `D (.sort .zero) fun D => do
      let armTy ← withLocalDeclD `e sfj fun e => do
        let qTy ← withLocalDeclD `h sfj fun h =>
          mkForallFVars #[h] (mkAppN motive (isj.push h))
        withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
      withLocalDeclD `k armTy fun k => do
        let proof ← withLocalDeclD `h sfj fun h =>
          mkLambdaFVars #[h] (mkAppN minor (elems ++ ihs))
        mkLambdaFVars #[D, k] (mkAppN k #[built, proof])
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  if !(mentionsAny #[tname] d) then
    return ← withLocalDecl x bi d fun xv => do
      mkLambdaFVars #[xv] (← pairArm tname np ni us selfAt pairAt motive cN minor ps
        (nf - 1) (b.instantiate1 xv) (elems.push xv) ihs)
  -- a recursive field `∀ z⃗, T p⃗ e⃗`: bind it at `∀ z⃗, Pair e⃗`
  let nb ← forallTelescope d fun zs _ => pure zs.size
  let dPair ← forallBoundedTelescope d (some nb) fun zs res => do
    let a := res.getAppArgs
    mkForallFVars zs (← pairAt (a.extract np a.size))
  withLocalDecl x bi dPair fun pv => do
    let (el, ih) ← forallBoundedTelescope d (some nb) fun zs res => do
      let a := res.getAppArgs
      let ris := a.extract np a.size
      let sf := selfAt ris
      let app := mkAppN pv zs
      let mkArm := fun (k : Expr → Expr → GenM Expr) =>
        withLocalDeclD `e sf fun e => do
          let qTy ← withLocalDeclD `h sf fun h =>
            mkForallFVars #[h] (mkAppN motive (ris.push h))
          withLocalDeclD `q qTy fun q => do mkLambdaFVars #[e, q] (← k e q)
      let elArm ← mkArm fun e _ => pure e
      let el := mkAppN app #[sf, elArm]
      let ihArm ← mkArm fun _ q => pure (mkApp q el)
      let ih := mkAppN app #[mkAppN motive (ris.push el), ihArm]
      return (← mkLambdaFVars zs el, ← mkLambdaFVars zs ih)
    mkLambdaFVars #[pv] (← pairArm tname np ni us selfAt pairAt motive cN minor ps
      (nf - 1) (b.instantiate1 el) (elems.push el) (ihs.push ih))

/-! ## The model -/

/-- One constructor's storage plan, settled by level arithmetic before
anything is spliced: which fields are boxed, and the pad level, `none` where
the chain reaches `Sort w` on its own. The pad level is `1` when that already
closes the gap and `w` otherwise. -/
structure CPlan where
  boxed : Array Bool
  pad? : Option Level
  deriving Inhabited

/-- The pads of every constructor at the given parameter scope, `none` where
the plan needs none. A `dsingOk` level gets the definitionally-canonical
[`Modelgen.dsingAt`] pad; any other level — a bare parameter in the gap,
`PULift`'s shape — gets the [`Modelgen.unitAt`] lift, which exists at every
level and is discharged by transport instead. -/
def padsAt (plans : Array CPlan) :
    GenM (Array (Option Pad)) := do
  plans.mapM fun plan => do
    let some ℓ := plan.pad? | return none
    if dsingOk ℓ then
      let (t, c) ← dsingAt ℓ
      return some { ty := t, lv := ℓ, canon := c, canonical := true }
    return some { ty := unitAt ℓ, lv := ℓ, canon := unitAtCanon ℓ, canonical := true }

/-- The constructors, analysed at a parameter scope. -/
def pctorsAt (exportCtors : Array (Name × Expr)) (plans : Array CPlan)
    (pads : Array (Option Pad)) (ps : Array Expr) : GenM (Array PCtor) := do
  (Array.range exportCtors.size).mapM fun j => do
    let (_, cty) := exportCtors[j]!
    let tele ← instForall cty ps
    let nf := numForalls tele
    let boxed := plans[j]!.boxed
    let (chain, _) ← chainTy pads[j]! boxed nf tele
    return { tele, nf, pad? := pads[j]!, boxed, chain }

/-- Which route the carrier's sort admits: `Sort 0` is the Church encoding, a
never-zero sort the `Nat`-tagged sum, and a **maybe-zero** sort — `Prop` at
some instantiations, `Type` at others, `PUnit`'s and `PEmpty`'s shape — the
same Church encoding under a [`Modelgen.puliftT`]. -/
inductive PrimRoute | type | prop | bare

/-- The model of one simple inductive from the primitives, or the shape that
stopped it. **The export's declaration must already be installed**: the
recursor this restates is the one Lean minted for it, and the ι rules are
its own, restored — exactly [`Modelgen.mutualIso`]'s arrangement. -/
def primIso (tname : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (reserved : Std.HashSet Name) : GenM Iso := do
  let us := lparams.map Level.param
  let model := Name.str tname "_model"
  let selfN := Name.str model "self"
  let ctorN := fun (j : Nat) => Name.str model s!"ctor_{j}"
  let recN := Name.str model "rec_0"
  let iotaN := fun (j : Nat) => Name.str model s!"iota_0_{j}"
  let nc := exportCtors.size

  if primBasis.contains tname then
    badShape "a basis primitive (the exemption that makes the construction well-founded)"

  let taken : Name → GenM Unit := fun n => do
    if reserved.contains n || (← getEnv).constants.contains n then declineWith (.nameTaken n)
  taken selfN
  taken recN
  for j in [0:nc] do
    taken (ctorN j)
    taken (iotaN j)

  -- ── shape ──
  let mut cur := memberTy
  for _ in [0:np] do
    match cur with
    | .forallE _ _ b _ => cur := b
    | _ => badShape "fewer binders than parameters"
  let mut ni := 0
  while cur matches .forallE .. do
    let .forallE _ _ b _ := cur | unreachable!
    cur := b
    ni := ni + 1
  let .sort w := cur | badShape "the declaration does not land in a sort"
  -- Recursive means a *field* mentions the declaration — the constructor's
  -- result always does and is not entered.
  let isRec := exportCtors.any fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut r := false
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then r := true
      t := b
    return r

  -- The installed recursor: the statements below are its own, restored.
  let ern := Name.str tname "rec"
  let .recInfo rv ← constInfo ern | badShape s!"{ern} is not a recursor"
  unless rv.numMotives == 1 && rv.numMinors == nc && rv.numIndices == ni do
    badShape s!"{ern} does not have 1 motive, {nc} minors and {ni} indices"
  let large := rv.levelParams.length == lparams.length + 1
  unless (if large then rv.levelParams.tail! else rv.levelParams) == lparams do
    badShape s!"{ern} carries the level parameters {rv.levelParams}"
  let v := if large then Level.param rv.levelParams[0]! else Level.zero
  let recLs := if large then v :: us else us

  let wn := w.normalize
  let route : PrimRoute ←
    if wn.isZero then pure .prop
    else if wn.isNeverZero then pure .type
    else
      -- A carrier at a **maybe-zero** sort, `Prop` at some instantiations and
      -- `Type` at others. `PULiftP` is the basis's type former that lands
      -- there, and it is empty exactly when its proposition is, so the whole
      -- class — empty, unit, payload, enum — is the Church encoding lifted.
      pure .bare

  -- What each route can carry. The Church routes gained indices and recursion
  -- (`churchSwapAt` and the strong-induction fold below); the `Nat`-tagged sum
  -- has neither, and at a maybe-zero sort the lift would have to be threaded
  -- through both, which is not done.
  match route with
  | PrimRoute.type =>
    if ni > 0 then
      badShape "an indexed family at a never-zero sort (the skeleton-plus-good \
        translation, thesis §5.2, is not implemented — the Church routes carry \
        indices, the Nat-tagged sum does not)"
    -- Recursion is carried by the tuple tower ([`Modelgen.recSlotOf`]), which
    -- declines the shapes it cannot express — a branching constructor, or a
    -- recursive occurrence under a binder — by name, further down.
  | PrimRoute.bare =>
    if ni > 0 then
      badShape s!"an indexed family at Sort {w}: the lift carries the Church \
        encoding but the index machinery is not threaded through it"
    if isRec then
      badShape s!"a recursive inductive at Sort {w}: the strong-induction fold is \
        not threaded through the lift"
  | PrimRoute.prop =>
    -- The subsingleton (large-eliminating) arm has no strong induction: a
    -- recursive subsingleton needs the `AccPhi` carrier of INDUCTIVE-BASIS §3.2,
    -- and the packed-`Eq` model below is its degenerate `r := ⊥` case.
    if isRec && large then
      badShape "a recursive subsingleton proposition (the AccPhi carrier of \
        INDUCTIVE-BASIS §3.2 is not implemented)"

  let (eqi, eqDecls) ← ensureEq reserved
  let mut out : Array Declaration := eqDecls
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)

  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps

  let ctorPairs := (Array.range nc).map fun j => (exportCtors[j]!.1, ctorN j)
  let tbl := modelTable (← getEnv) #[tname]
    { decls := #[], levelParams := lparams, members := #[], selfNames := #[selfN]
      numAll := 1, ctors := ctorPairs, recs := #[recN], iotas := #[], spliced := #[] }

  if route matches PrimRoute.type then
    -- ════ the Type route ════
    unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
    for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensurePSigma reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensurePULiftP reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- Storage decisions — pure level arithmetic, and a decline here costs no
    -- further splice. A chain of one field is that field bare (no `PSigma`,
    -- so no built-in `1`); longer chains carry `max 1 ℓ⃗` already. A pad at
    -- `1` closes most gaps and `w` itself covers a deliberately-raised
    -- carrier — at *any* `w` now, since `PULiftP` exists at every level.
    -- What no pad absorbs is an `imax` in a field's level: those fields are
    -- boxed ([`Modelgen.boxTyOf`]) and the plan is retried on the boxed
    -- levels, which are never-zero `max`es.
    let plans : Array CPlan ← withParams fun ps =>
      exportCtors.mapM fun (cn, cty) => do
        let tele ← instForall cty ps
        let nf := numForalls tele
        forallBoundedTelescope tele (some nf) fun fs _ => do
          let tys ← fs.mapM ityp
          let ℓs ← tys.mapM ilevel
          let plan : Array Level → GenM (Option (Option Level)) := fun ms => do
            let raw := if nf == 1 then ms[0]! else (ms.foldl mkLevelMax' (.succ .zero)).normalize
            if nf > 0 then
              if ← isLevelDefEq raw w then return some none
            let withOne := (ms.foldl mkLevelMax' (.succ .zero)).normalize
            if ← isLevelDefEq withOne w then return some (some (Level.succ .zero))
            if ← isLevelDefEq (mkLevelMax' withOne w) w then return some (some w)
            return none
          if let some pad? ← plan ℓs then
            return { boxed := Array.replicate nf false, pad? }
          let boxed := ℓs.map fun ℓ => levelHasIMax ℓ.normalize
          if boxed.any id then
            let ms ← (Array.range nf).mapM fun k => do
              if boxed[k]! then ilevel (← boxTyOf tys[k]!) else pure ℓs[k]!
            if let some pad? ← plan ms then
              return { boxed, pad? }
          let raw := if nf == 1 then ℓs[0]! else (ℓs.foldl mkLevelMax' (.succ .zero)).normalize
          badShape s!"{cn}'s fields reach Sort {raw} and the carrier is Sort {w}: no \
            pad or codomain box closes the gap"

    -- A pad at a level `dsingOk` cannot build is discharged by transport
    -- along the lift's eta ([`Modelgen.unitAtUniq`]) — a recursor call and
    -- proof irrelevance. The `False`-Π pad this replaces needed `funext`
    -- here, and with it `Quot.sound` and a wait on the input's quotient; the
    -- construction now splices neither.
    let natT : Expr := .const `Nat []
    let fibreAt := fun (ps : Array Expr) => do
      let pads ← padsAt plans
      let cs ← pctorsAt exportCtors plans pads ps
      withLocalDeclD `n natT fun n =>
        return (cs, ← mkLambdaFVars #[n] (← fibreTower w cs 0 n))

    -- Which constructors carry the recursion, and where. Empty for a
    -- non-recursive declaration, in which case everything below degenerates
    -- to the single tag tower the previous tranche had.
    let slots : Array (Option Nat) ← withParams fun ps =>
      exportCtors.mapM fun (cn, cty) => do
        let tele ← instForall cty ps
        recSlotOf tname np cn (numForalls tele) tele
    let baseJ := (Array.range nc).filter fun j => slots[j]!.isNone
    let stepJ := (Array.range nc).filter fun j => slots[j]!.isSome
    -- export constructor index ↦ its tag *within its own tower*
    let tagOf : Array Nat := (Array.range nc).map fun j =>
      let tower := if slots[j]!.isNone then baseJ else stepJ
      (tower.findIdx? (· == j)).getD 0

    -- The tag tower of a set of constructors, at a parameter scope. `sub` is
    -- the shorter spine's fibre `V n`, which a step constructor's chain
    -- stores in place of its recursive field; base constructors never look
    -- at it.
    let towerAt : Array Expr → Array Nat → Expr → GenM (Array PCtor × Expr) :=
      fun ps js sub => do
      let pads ← padsAt plans
      let cs : Array PCtor ← js.mapM fun j => do
        let (_, cty) := exportCtors[j]!
        let tele0 ← instForall cty ps
        let nf := numForalls tele0
        let tele ← spineSwap tname sub nf tele0
        let pl : CPlan := plans[j]!
        let (chain, _) ← chainTy pads[j]! pl.boxed nf tele
        pure { tele, nf, pad? := pads[j]!, boxed := pl.boxed, chain }
      let fib ← withLocalDeclD `tag natT fun tg =>
        do mkLambdaFVars #[tg] (← fibreTower w cs 0 tg)
      return (cs, fib)

    -- `V : Nat → Sort w`, the spine tower: base chains at spine 0, step
    -- chains at every successor, with the predecessor's fibre plugged in.
    let spineAt := fun (ps : Array Expr) => do
      let (_, bfib) ← towerAt ps baseJ (.sort w)
      let zc := psigmaT (.succ .zero) w natT bfib
      let sc ← withLocalDeclD `n natT fun n =>
        withLocalDeclD `R (.sort w) fun R => do
          let (_, sfib) ← towerAt ps stepJ R
          mkLambdaFVars #[n, R] (psigmaT (.succ .zero) w natT sfib)
      withLocalDeclD `n natT fun n =>
        mkLambdaFVars #[n]
          (natRec (.succ w) (.lam `x natT (.sort w) .default) zc sc n)

    -- ── the carrier ──
    -- Non-recursive: one tag tower under a `Nat`. Linearly recursive: the
    -- spine tower, `Σ'(n : Nat), V n`.
    let carrierAt := fun (ps : Array Expr) => do
      if isRec then pure (psigmaT (.succ .zero) w natT (← spineAt ps))
      else do pure (psigmaT (.succ .zero) w natT (← fibreAt ps).2
    )
    let selfVal ← withParams fun ps => do mkLambdaFVars ps (← carrierAt ps)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := memberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructors ──
    for j in [0:nc] do
      let (_, cty) := exportCtors[j]!
      let ty := restore tbl cty
      let val ← withParams fun ps => do
        if !isRec then
          let (cs, fib) ← fibreAt ps
          let c := cs[j]!
          forallBoundedTelescope c.tele (some c.nf) fun fs _ => do
            let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
            mkLambdaFVars (ps ++ fs)
              (psigmaMk (.succ .zero) w natT fib (natNumeral j) tup)
        else do
          -- The binders come from the **restored** telescope: the recursive
          -- field's type there is `T._model.self p⃗`, i.e. the spine pair, and
          -- what goes into the chain is its second component.
          let spine ← spineAt ps
          let rtele ← instForall ty ps
          let nf := numForalls rtele
          forallBoundedTelescope rtele (some nf) fun fs _ => do
            let mkOuter := fun (n tup : Expr) =>
              psigmaMk (.succ .zero) w natT spine n tup
            match slots[j]! with
            | none =>
              let (bcs, bfib) ← towerAt ps baseJ (.sort w)
              let c := bcs[tagOf[j]!]!
              let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
              mkLambdaFVars (ps ++ fs) (mkOuter (natNumeral 0)
                (psigmaMk (.succ .zero) w natT bfib (natNumeral (tagOf[j]!)) tup))
            | some k =>
              let r := fs[k]!
              let rn := psigmaFst (.succ .zero) w natT spine r
              let rv2 := psigmaSnd (.succ .zero) w natT spine r
              let (scs, sfib) ← towerAt ps stepJ (mkApp spine rn).headBeta
              let c := scs[tagOf[j]!]!
              let tup ← chainTuple c.pad? c.boxed c.nf c.tele (fs.set! k rv2)
              mkLambdaFVars (ps ++ fs) (mkOuter (.app (.const `Nat.succ []) rn)
                (psigmaMk (.succ .zero) w natT sfib (natNumeral (tagOf[j]!)) tup))
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── the recursor ──
    let recTy := restore tbl rv.type
    let recVal ← forallBoundedTelescope recTy (some (np + 1 + nc + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minors := bs.extract (np + 1) (np + 1 + nc)
      let major := bs[bs.size - 1]!
      if !isRec then
        let (cs, fib) ← fibreAt ps
        let minor ←
          if nc == 0 then
            withLocalDeclD `n natT fun n => do
              withLocalDeclD `f (emptyAt w) fun f => do
                mkLambdaFVars #[n, f] (← emptyAtElim eqi v w
                  (mkApp motive (psigmaMk (.succ .zero) w natT fib n f)) f)
          else
            withLocalDeclD `n natT fun n => do
              withLocalDeclD `f (mkApp fib n).headBeta fun f => do
                mkLambdaFVars #[n, f]
                  (mkApp (← stepTower v w eqi fib (fun z => mkApp motive z)
                    (fun j vs => mkAppN minors[j]! vs) cs 0 n) f)
        mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT fib motive minor major)
      else do
        -- `PSigma.rec` on the outer pair, `Nat.rec` on the spine, the tag
        -- towers inside each level, `PSigma.rec` down each chain.
        let spine ← spineAt ps
        let mkOuter := fun (n tup : Expr) => psigmaMk (.succ .zero) w natT spine n tup
        -- the Nat.rec motive: `fun n => (x : V n) → motive ⟨n, x⟩`
        let nmot ← withLocalDeclD `n natT fun n =>
          withLocalDeclD `x (mkApp spine n).headBeta fun x => do
            mkLambdaFVars #[n] (← mkForallFVars #[x] (mkApp motive (mkOuter n x)))
        -- spine 0: the base tower
        let zc ← do
          let (bcs, bfib) ← towerAt ps baseJ (.sort w)
          withLocalDeclD `x (psigmaT (.succ .zero) w natT bfib) fun x => do
            let tgt := fun (tup : Expr) => mkApp motive (mkOuter (natNumeral 0) tup)
            let minorOf := fun (b : Nat) (vs : Array Expr) => mkAppN minors[baseJ[b]!]! vs
            let inner ← withLocalDeclD `tag natT fun tg =>
              withLocalDeclD `f (mkApp bfib tg).headBeta fun f => do
                mkLambdaFVars #[tg, f]
                  (mkApp (← stepTower v w eqi bfib tgt minorOf bcs 0 tg) f)
            let mot ← withLocalDeclD `z (psigmaT (.succ .zero) w natT bfib) fun z =>
              mkLambdaFVars #[z] (mkApp motive (mkOuter (natNumeral 0) z))
            mkLambdaFVars #[x]
              (psigmaRec v (.succ .zero) w natT bfib mot inner x)
        -- spine n+1: the step tower, with the induction hypothesis in hand
        let sc ← withLocalDeclD `n natT fun n =>
          withLocalDeclD `ih (mkApp nmot n).headBeta fun ih => do
            let sub := (mkApp spine n).headBeta
            let (scs, sfib) ← towerAt ps stepJ sub
            let nsucc := Expr.app (.const `Nat.succ []) n
            withLocalDeclD `x (psigmaT (.succ .zero) w natT sfib) fun x => do
              let tgt := fun (tup : Expr) => mkApp motive (mkOuter nsucc tup)
              let minorOf := fun (b : Nat) (vs : Array Expr) =>
                let j := stepJ[b]!
                let k := (slots[j]!).getD 0
                let sv := vs[k]!
                mkAppN minors[j]! ((vs.set! k (mkOuter n sv)).push (mkApp ih sv))
              let inner ← withLocalDeclD `tag natT fun tg =>
                withLocalDeclD `f (mkApp sfib tg).headBeta fun f => do
                  mkLambdaFVars #[tg, f]
                    (mkApp (← stepTower v w eqi sfib tgt minorOf scs 0 tg) f)
              let mot ← withLocalDeclD `z (psigmaT (.succ .zero) w natT sfib) fun z =>
                mkLambdaFVars #[z] (mkApp motive (mkOuter nsucc z))
              mkLambdaFVars #[n, ih, x]
                (psigmaRec v (.succ .zero) w natT sfib mot inner x)
        let minor ← withLocalDeclD `n natT fun n =>
          withLocalDeclD `x (mkApp spine n).headBeta fun x => do
            mkLambdaFVars #[n, x]
              (mkApp (natRec (mkLevelIMax' w v).normalize nmot zc sc n) x)
        mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT spine motive minor major)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else
    -- ════ the Church routes: `Prop`, and the maybe-zero sort under a lift ════
    --
    -- One construction serves both. At `Sort 0` the carrier is the
    -- impredicative Church encoding itself; at a **maybe-zero** sort it is
    -- that same encoding under `PULiftP`, which puts it at exactly `Sort w`
    -- for any `w`. The constructors are the folds, `up` of the folds under a
    -- lift. The recursor is the fold at the right `C`, plus — under a lift —
    -- one transport along [`Modelgen.puliftEta`], because `PULiftP p` is not
    -- itself a proposition and proof irrelevance no longer closes the
    -- "which element" question by itself.
    --
    -- Why this is a model and not a collapse: at a maybe-zero sort the
    -- contract never forces two provably distinct elements. Zero constructors
    -- and the subsingleton shape large-eliminate and are subsingletons
    -- anyway; everything else there small-eliminates, so the motive lands in
    -- `Prop` and cannot discriminate. The lift of a proposition is exactly
    -- the right size.
    let lift? : Option Level := if route matches PrimRoute.bare then some w else none

    -- The index telescope at a parameter scope, and the Church motive's type
    -- `C : ∀ ι⃗, Prop` over it. At `ni = 0` this is just `Prop` and everything
    -- below degenerates to the original non-indexed construction.
    let idxTeleAt := fun (ps : Array Expr) => instForall memberTy ps
    let motiveTyAt := fun (ps : Array Expr) => do
      forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ =>
        mkForallFVars is (.sort .zero)

    let churchAt := fun (ps : Array Expr)
        (k : Expr → Array Expr → Array Expr → GenM Expr) => do
      -- `C`, the `k_j` binders, and their types, in one scope. Each `k_j` is
      -- constructor `j`'s telescope with `T p⃗` replaced by `C` — at its
      -- recursive fields as well as at its result.
      withLocalDeclD `C (← motiveTyAt ps) fun C => do
        let kTys ← exportCtors.mapM fun (_, cty) => do
          let tele ← instForall cty ps
          return (← churchSwapAt tname np ni C (numForalls tele) tele).1
        churchBinders kTys 0 #[] (fun ks => k C ks kTys)

    if lift?.isSome then
      for d in ← ensurePULiftP reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- The bare Church proposition at a parameter *and index* scope — what
    -- sits under the lift, and the carrier itself when there is none.
    let churchPropAt := fun (ps : Array Expr) (is : Array Expr) =>
      churchAt ps fun C ks _ => mkForallFVars (#[C] ++ ks) (mkAppN C is)

    -- ── the carrier ──
    let selfVal ← withParams fun ps => do
      forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
        let pr ← churchPropAt ps is
        mkLambdaFVars (ps ++ is)
          (match lift? with | none => pr | some ℓ => puliftT ℓ pr)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := memberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructors ──
    -- The binders come from the **restored** telescope, because a recursive
    -- field's type there is `T._model.self p⃗ e⃗` — which δ-unfolds to the
    -- encoding, so the fold `fun z⃗ => f z⃗ C k⃗` typechecks. Classification is
    -- positional and read off the export's telescope.
    for j in [0:nc] do
      let (_, cty) := exportCtors[j]!
      let ty := restore tbl cty
      let nfj ← withParams fun ps => do pure (numForalls (← instForall cty ps))
      let flds ← withParams fun ps => do classifyCtor tname nfj (← instForall cty ps)
      let val ← withParams fun ps => do
        let rtele ← instForall ty ps
        forallBoundedTelescope rtele (some nfj) fun fs _ => do
          let fold ← churchAt ps fun C ks _ => do
            let args ← (Array.range nfj).mapM fun i => do
              match flds[i]!.rec? with
              | none => pure fs[i]!
              | some 0 => pure (mkAppN fs[i]! (#[C] ++ ks))
              | some nb =>
                -- exactly the field's OWN binders: `forallTelescope` would
                -- whnf through `T._model.self` and open the encoding's Π too.
                forallBoundedTelescope (← ityp fs[i]!) (some nb) fun zs _ =>
                  mkLambdaFVars zs (mkAppN (mkAppN fs[i]! zs) (#[C] ++ ks))
            mkLambdaFVars (#[C] ++ ks) (mkAppN ks[j]! args)
          match lift? with
          | none => mkLambdaFVars (ps ++ fs) fold
          | some ℓ =>
            forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
              mkLambdaFVars (ps ++ fs) (puliftUp ℓ (← churchPropAt ps is) fold)
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── the recursor ──
    if large && nc == 0 then
      for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
      for d in ← ensurePULiftP reserved do out := out.push d; spliced := spliced ++ d.getNames
    let recTy := restore tbl rv.type
    let recVal ← forallBoundedTelescope recTy (some (np + 1 + nc + ni + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minors := bs.extract (np + 1) (np + 1 + nc)
      let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
      let t := bs[bs.size - 1]!
      -- Under a lift the fold runs on `down t`. Its result lands at
      -- `motive ι⃗ (up (down t))`, which *is* `motive ι⃗ t`: structure eta on
      -- `PULiftP` gives `t ≡ up (down t)`. So there is no transport, and the
      -- two routes differ in exactly the `down` here and the `up` in the
      -- constructors above.
      let body : Expr ←
        match lift? with
        | none => pure t
        | some ℓ => do pure (puliftDown ℓ (← churchPropAt ps idxs) t)
      let goalAt := mkAppN motive (idxs.push t)
      -- `Self ι⃗`, the carrier at an index vector.
      let selfAt := fun (is : Array Expr) => mkAppN (.const selfN us) (ps ++ is)
      if !large && ni == 0 && !isRec then
        -- The plain fold, at `C := goalAt`: every minor's motive is closed by
        -- definitional proof irrelevance — under a lift too, because the two
        -- `up`s differ only in a proof of the encoding's own proposition.
        mkLambdaFVars bs (mkAppN body (#[goalAt] ++ minors))
      else if !large then
        -- ── strong induction (INDUCTIVE-BASIS §3.1) ──
        -- The plain fold cannot serve an indexed or recursive declaration: a
        -- minor premise wants `motive ι⃗_j (c_j f⃗)` and the fold only offers
        -- `C ι⃗_j`, which proof irrelevance no longer identifies with it once
        -- the index moves. So fold at the Church **pair**
        --
        --     Pair ι⃗ := ∀ D : Prop, (Self ι⃗ → (∀ h : Self ι⃗, motive ι⃗ h) → D) → D
        --
        -- of a rebuilt carrier element and a proof about *every* element at
        -- that index — the `∀ h` is what proof irrelevance collapses, and the
        -- element component is what a recursive minor premise needs an
        -- argument for. Every ι rule is still `Eq.refl`, and for a reason
        -- that has nothing to do with whether the fold reduces: the motive is
        -- `Prop`-valued, so both sides of every ι equation are proofs of one
        -- proposition.
        let pairTy ← forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
          let sf := selfAt is
          let inner ← withLocalDeclD `D (.sort .zero) fun D => do
            let armTy ← withLocalDeclD `e sf fun e => do
              let qTy ← withLocalDeclD `h sf fun h =>
                mkForallFVars #[h] (mkAppN motive (is.push h))
              withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
            mkForallFVars #[D] (.forallE `k armTy D .default)
          mkLambdaFVars is inner
        -- one `Pair`-valued premise per constructor
        let pairAt := fun (is : Array Expr) => do
          let sf := selfAt is
          withLocalDeclD `D (.sort .zero) fun D => do
            let armTy ← withLocalDeclD `e sf fun e => do
              let qTy ← withLocalDeclD `h sf fun h =>
                mkForallFVars #[h] (mkAppN motive (is.push h))
              withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
            mkForallFVars #[D] (.forallE `k armTy D .default)
        let cs ← (Array.range nc).mapM fun j => do
          let (_, cty) := exportCtors[j]!
          let tele ← instForall cty ps
          pairArm tname np ni us selfAt pairAt motive (ctorN j) minors[j]! ps
            (numForalls tele) tele #[] #[]
        let cont ← withLocalDeclD `e (selfAt idxs) fun e => do
          let qTy ← withLocalDeclD `h (selfAt idxs) fun h =>
            mkForallFVars #[h] (mkAppN motive (idxs.push h))
          withLocalDeclD `q qTy fun q => mkLambdaFVars #[e, q] (mkApp q t)
        mkLambdaFVars bs (mkAppN (mkAppN body (#[pairTy] ++ cs)) #[goalAt, cont])
      else if nc == 0 then
        -- Church `⊥` at every index: instantiate the encoding at the constant
        -- family. At `ni = 0` this is the encoding itself.
        let cf ← withLocalDeclD `p (.sort .zero) fun pv => do
          let fam ← forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ =>
            mkLambdaFVars is pv
          mkLambdaFVars #[pv] (mkApp body fam)
        mkLambdaFVars bs (← cfalseElim eqi v goalAt cf)
      else do
        -- Large elimination: one constructor, every field a proposition
        -- (the subsingleton rule, which minted this recursor, says so) —
        -- extract each by instantiating the encoding at the field's type.
        unless nc == 1 do
          badShape s!"{ern} is large-eliminating with {nc} constructors"
        if ni > 0 then
          badShape s!"an indexed subsingleton: the packed-index-equation model \
            (INDUCTIVE-BASIS §3.2's degenerate case, compiled in \
            scripts/inductive-basis/PropArms.lean as HEq') is not implemented"
        let (_, cty) := exportCtors[0]!
        let tele ← instForall cty ps
        let nf := numForalls tele
        let mut es : Array Expr := #[]
        let mut curT := tele
        for _ in [0:nf] do
          let .forallE _ ft rest _ := curT | badShape "telescope shorter than its field count"
          unless (← ilevel ft).normalize.isZero do
            badShape s!"{ern} is large-eliminating and a field is not a proposition"
          let i := es.size
          let proj ← forallBoundedTelescope tele (some nf) fun fs _ =>
            mkLambdaFVars fs fs[i]!
          es := es.push (mkAppN body #[ft, proj])
          curT := rest.instantiate1 es[i]!
        mkLambdaFVars bs (mkAppN minors[0]! es)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec

  -- ── the ι rules, every one `Eq.refl` ──
  let recTy := restore tbl rv.type
  let mut iotas : Array (Nat × Name × Name) := #[]
  unless rv.rules.length == nc do
    badShape s!"{ern} has {rv.rules.length} rules where {tname} has {nc} constructors"
  for j in [0:nc] do
    let rule := rv.rules[j]!
    let (cn, modelC) := ctorPairs[j]!
    unless rule.ctor == cn do
      badShape s!"{ern}'s rule {j} is for {rule.ctor}, not {cn}"
    let modelCTy := (← constInfo modelC).type
    let d ← forallBoundedTelescope recTy (some (np + 1 + nc)) fun pre _ => do
      let ps := pre.extract 0 np
      let motive := pre[np]!
      let cty ← instForall modelCTy ps
      forallBoundedTelescope cty (some (numForalls modelCTy - np)) fun fields res => do
        let major := mkAppN (.const modelC us) (ps ++ fields)
        -- The constructor's own index expressions, read off its result type
        -- `T._model.self p⃗ ι⃗_j`. The recursor takes them between the minors
        -- and the major, and the motive takes them before it.
        let args := res.getAppArgs
        unless res.getAppFn.isConstOf selfN && args.size == np + ni do
          badShape s!"{modelC}'s result is not {selfN} at {np} parameters and {ni} indices"
        let isj := args.extract np args.size
        let lhs := mkAppN (.const recN recLs) (pre ++ isj ++ #[major])
        let rhs := (restore tbl rule.rhs).beta (pre ++ fields)
        let α := mkAppN motive (isj.push major)
        let tel := pre ++ fields
        return Declaration.thmDecl
          { name := iotaN j, levelParams := rv.levelParams
            type := ← mkForallFVars tel (eqi.mk' v α lhs rhs)
            value := ← mkLambdaFVars tel (eqi.refl' v α lhs) }
    addChecked d
    out := out.push d
    iotas := iotas.push (0, cn, iotaN j)

  return { decls := out, levelParams := lparams, members := #[], selfNames := #[selfN]
           numAll := 1, ctors := ctorPairs, recs := #[recN], iotas, spliced }

end Modelgen
