import Modelgen.Mutual

/-!
# The model of a **simple inductive from four primitives**, generated

The third construction in this package, behind `--prim-models` and off by
default. Where the first two constructions remove *nesting* and *mutuality*,
this one removes the inductive declaration itself: a plain (non-mutual,
non-nested) inductive's carrier, constructors, recursor and ι rules are
emitted as ordinary `def`s and `theorem`s over a fixed basis of primitive
inductives —

    Eq   PSigma   Nat   PULiftP

— each spliced into the output at Lean's own shape if the input lacks it,
exactly as the existing prelude splice does for `Eq`. A consumer that
recognises the four interface names then needs to implement only the four
primitives (plus `Quot`), not general inductives — and, if the input reaches
[`Modelgen.graphArm`], `Nonempty` and the `Classical.choice` axiom beside
them. `Nonempty` is not a fifth primitive: it is `Classical.choice`'s own
domain, needs no exemption, and self-models by the Church route.

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
which a `Type`-only `Sigma` cannot give without `PLift`, a fifth inductive.

**`Acc` is not in the basis either, and used to be.** It was there for the
subsingleton-recursive **large** eliminator — the one grant the kernel makes
to a *declaration* that an emitted `def` does not inherit — and that grant is
now derived rather than assumed: [`Modelgen.graphArm`] defines the recursion
by its *graph* and extracts the value, packaged with its graph proof, with
`Classical.choice`, which gives `Acc.rec`'s exact type with ι a theorem
instead of `rfl`. `scripts/inductive-basis/AccFromChoice.lean` is the
derivation and `AccArmShapes.lean` its uniformity; `MODELGEN.md` §8.7 is the
arm. So `Acc` models like any other declaration now.

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
  exists at *every* level. **Both are definitionally canonical**, in the one
  sense the construction needs: every element is *defeq to the canonical
  one*, because the canonical one is a literal constructor application and
  eta-for-structures expands the other side against it. So no pad costs a
  transport. This is **not** the stronger claim that two *opaque* inhabitants
  collapse, which is false as a conversion — nothing eta-expands a variable
  on speculation, so the kernel refuses `x ≡ y` for two variables even though
  `x = y` is provable without an axiom.
  `scripts/inductive-basis/PULiftPEta.lean` pins both and the gap between
  them. The `False`-Π singleton this replaced was not canonical in *either*
  sense and cost a `funext`.
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
both sides of every ι equation are proofs of one proposition. **The graph arm
below is the one exception**: its recursor's value is a `Classical.choice`
application, which reduces to nothing, so its ι is proved from the graph's
single-valuedness and is propositional.

## What declines, and why

* **branching recursion at a never-zero sort** (`Lean.ParserDescr`) — the
  tuple tower ([`Modelgen.recSlotOf`]) carries *linear* recursion, and its
  spine is a single `Nat`, so a constructor with two recursive fields (or one
  under a binder) has no predecessor to take. That needs W/path, plan B.
* **indexed at a never-zero sort whose index erasure is not linear** — the
  erasure branches, and arm C below carves out of that erasure, so the family
  waits on whatever models a branching non-indexed inductive: W. 43 of the 53
  remaining occupants are the composed `T._model.aux`.
  An indexed family whose erasure *is* linear is no longer a refusal: it is
  **arm C** ([`Modelgen.primIso`]'s `armC`), thesis §5.2's
  skeleton-plus-`good` standing on a spliced inductive rather than on a
  W-type — no axioms, no per-constructor currying glue, every ι rule
  `Eq.refl`, and 29 of Mathlib's 147 declines closed.
  `scripts/inductive-basis/CarveOverSkeleton.lean` is the prototype and
  `MODELGEN.md` §8.15 the arm; `IndexedCarve.lean` is the older,
  thesis-shaped sketch.
* **a recursive declaration with no base constructor** — uninhabited, and the
  tuple tower has no spine-zero fibre to build. Surfaced by arm C's skeleton
  and named there (§8.15).
* **a recursive subsingleton whose data fields are not the conclusion's
  indices** — the graph arm's own boundary, not the class: a *recursive
  subsingleton* models, by [`Modelgen.graphArm`]. What that arm cannot reach
  is an index it cannot invert at: a constant (`mk : P 0 → P 0`) or one built
  from a proof field, which is the shape of the `below` Lean mints beside
  every recursive `Prop`. `INDUCTIVE-BASIS.md` §3.2 is the carrier and
  `MODELGEN.md` §8.7 the arm.
* **indices or recursion at a maybe-zero sort** — neither is threaded
  through the lift.
* **a level gap no pad or box closes** — an `imax` in a field's level that
  boxing does not collapse (an `imax`-leveled *domain* inside the field).
  This one is a **level-incompleteness** decline, not a type error: the
  padded chain equals the carrier's level at every instantiation and Lean's
  normal-form level defeq does not see it. `MODELGEN.md` §8.6 has the
  lean4lean cross-check, and §8.6.1 closes it — the decline is taken *here*,
  by `isLevelDefEq` below, so it needs the **elaborator's** level equality
  repaired and not only the kernel's, which is what
  `modelgen --interpose-levels` does.
* a field mentioning `T` other than as `∀ z⃗, T p⃗ e⃗` — a **nested**
  occurrence, which is layer 1's business.
* the four **basis primitives themselves** — the exemption that makes the
  construction well-founded.
-/

open Lean Meta

namespace Modelgen

/-- The four, by name. A declaration in this set is the basis and is not
modelled — the exemption that makes the construction well-founded.

**`Acc` was the fifth and is not here any more.** Its one grant — the
subsingleton-recursive large eliminator — is derived by
[`Modelgen.graphArm`], so `Acc` is an ordinary declaration and models like
one. `Nonempty` never joins this list either, though the graph arm names it:
`Classical.choice`'s domain is not an exemption, and it self-models.

`False` is **not** among them: it is derived (Church `∀ p : Prop, p`, with
its `Sort w` eliminator from `0 = 1` plus a `Nat.rec`-built family to
transport along — [`Modelgen.cfalseElim`]), so `False` models like any other
declaration. `PULiftP` takes its place. -/
def primBasis : List Name := [`Eq, `PSigma, `Nat, `PULiftP]

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

/-- **Lean's `Nonempty`**, as `Init/Prelude.lean` declares it:
`inductive Nonempty (α : Sort u) : Prop | intro (val : α) : Nonempty α`.

**It is not a basis primitive** and it is not on [`Modelgen.primBasis`]'s list.
It is here for one reason: `Classical.choice`'s *own domain* is `Nonempty`, so
the graph arm ([`Modelgen.graphArm`]) cannot state totality without naming it.
Unlike the five it does not need an exemption to keep the construction
well-founded — it is a non-recursive, small-eliminating `Prop`, so where the
input declares one the Church route models it like anything else, and the
model is emitted beside it as usual. What a *spliced* `Nonempty` costs is one
unmodelled inductive in that run's output, which is why the splice is reported
like every other. -/
def nonemptyDecl : Declaration :=
  let lu := Level.param `u
  let ty : Expr := .forallE `α (.sort lu) (.sort .zero) .default
  let introTy : Expr := .forallE `α (.sort lu)
    (.forallE `val (.bvar 0) (.app (.const `Nonempty [lu]) (.bvar 1)) .default) .implicit
  .inductDecl [`u] 1
    [{ name := `Nonempty, type := ty,
       ctors := [{ name := `Nonempty.intro, type := introTy }] }] false

def checkNonempty (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `Nonempty | throw "it is not an inductive type"
  unless iv.numParams == 1 && iv.numIndices == 0 && iv.ctors == [`Nonempty.intro]
      && iv.levelParams.length == 1 do
    throw "it is not a one-parameter, one-constructor lift with a single level parameter"
  match iv.type with
  | .forallE _ (.sort (.param _)) (.sort .zero) _ => pure ()
  | _ => throw "it is not `Sort u → Prop`"

/-- `Classical.choice`'s statement: `{α : Sort u} → Nonempty α → α`. One
builder for both uses — the input's own is compared against it with `isDefEq`
and a spliced one is declared at it, exactly as [`Modelgen.funextType`] serves
`funext`. -/
def choiceType (lu : Level) : Expr :=
  .forallE `α (.sort lu)
    (.forallE `h (.app (.const `Nonempty [lu]) (.bvar 0)) (.bvar 1) .default) .implicit

def choiceDecl : Declaration :=
  .axiomDecl { name := `Classical.choice, levelParams := [`u]
               type := choiceType (.param `u), isUnsafe := false }

def ensurePULiftP (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `PULiftP [`PULiftP, `PULiftP.up] puliftDecl checkPULiftP reserved
def ensureNonempty (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `Nonempty [`Nonempty, `Nonempty.intro] nonemptyDecl checkNonempty reserved

/-- **`Classical.choice`, the one axiom the graph arm asserts.** The input's
own where it declares one at Lean's statement; Lean's, spliced in, where it
does not. `funext` is *derived* from `Quot.sound` rather than asserted and
this one cannot be — it is an axiom in Lean too — so the asymmetry is the
subject matter's and not a shortcut. The owner's ruling stands behind it:
axiom-freedom is not a goal of this construction and the standard axioms may
be used. -/
def ensureChoice (reserved : Std.HashSet Name) : GenM (Array Declaration) := do
  match (← getEnv).constants.find? `Classical.choice with
  | some ci =>
    let [su] := ci.levelParams
      | declineWith (.notLeans `Classical.choice
          s!"it has {ci.levelParams.length} level parameters, where Lean's has 1")
    unless ← isDefEq ci.type (choiceType (.param su)) do
      declineWith (.notLeans `Classical.choice "its statement is not Lean's")
    return #[]
  | none =>
    if reserved.contains `Classical.choice then declineWith (.nameTaken `Classical.choice)
    addChecked choiceDecl
    return #[choiceDecl]
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

**The rule fires on a redex, and only on one.** Eta-for-structures expands one
side when the *other* is already a constructor application. So `t ≡ up (down
t)` holds for an opaque `t`, and `t ≡ canon` holds for a literal `canon = up
h`, but `x ≡ y` for two opaque inhabitants does **not** — the kernel refuses it
even when forced past the unifier with `@Eq.refl _ x`, because neither side
gets expanded. It is refused as a *conversion* only: `x = y` is provable, with
no axiom, by routing through `up (down ·)` where every step is a redex, so the
conversion is simply not transitive at this shape.
`scripts/inductive-basis/PULiftPEta.lean` pins all of it.

Two consequences the construction leans on, **both at a redex**. Every element
of `PULiftP ⊤` is defeq to [`Modelgen.unitAtCanon`], which is a literal `up`,
so a pad built from it needs no transport — the strict improvement on the
`False`-Π pad, whose uniqueness was `funext`. And `motive (up (down t))` and
`motive t` are convertible, so the maybe-zero route's recursor is the `Prop`
route's with `up`/`down` at the ends and nothing in between. Nowhere does the
construction compare two opaque inhabitants, so nothing rests on the claim
that fails. -/
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
canonical — *every element is defeq to [`Modelgen.unitAtCanon`]*, by structure
eta on `PULiftP` against that literal `up` plus proof irrelevance on `⊤` — so
wherever one is destructed the applied minor already has the target type and
no transport rides along. This is where the `False`-Π singleton cost a
`funext`, and it is why the destructor needs no transport at all and ι is
`Eq.refl` with nothing to erase.

**Read "canonical" narrowly.** What holds is `t ≡ canon`, where one side is a
constructor application and eta expands the other. What does *not* hold is
`x ≡ y` for two opaque inhabitants: no side is a redex, so the kernel refuses
it — see [`Modelgen.puliftEta`] and `scripts/inductive-basis/PULiftPEta.lean`.
Every use below is of the first kind. -/

/-- The singleton at exactly `Sort ℓ`: the lift of `⊤`. -/
def unitAt (ℓ : Level) : Expr := puliftT ℓ trueP

/-- Its canonical element. -/
def unitAtCanon (ℓ : Level) : Expr := puliftUp ℓ trueP trueI

/-- `Eq canon t` for `t : unitAt ℓ`. [`Modelgen.puliftEta`] proves
`Eq (up (down t)) t`, and `up (down t)` is *definitionally* the canonical
element: both components are proofs of `⊤`, and proof irrelevance closes it.
No `funext`.

**Nothing reaches this today.** [`Modelgen.padsAt`] marks both pad families
`canonical := true`, because `t ≡ canon` is a conversion the kernel performs
(the canonical element is a literal `up`, so eta expands `t` against it), so
[`Modelgen.chainDestruct`] takes its no-transport branch for the lift pad as
well as for the `D` pad. It is kept because it is the shape a caller would
need if a future pad family were canonical only *propositionally*, and it is
measured rather than assumed: forcing the lift pad through here by setting
`canonical := false` leaves every `prim_shapes` occupant modelling, and
forcing the `D` pad through here — where the proof is about the wrong type —
is red at `Tri`, `Opt`, `Dec` and `Big`. -/
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

`canonical` says whether every element is **defeq** to `canon`, in which case
no uniqueness proof rides along. **Both families set it**: the
[`Modelgen.dsingAt`] pad by `PSigma` structure eta and proof irrelevance, and
the [`Modelgen.unitAt`] lift — used at a level `dsingOk` cannot build, a bare
parameter in the gap, `PULift`'s shape — by `PULiftP` structure eta against
the literal `up` that `canon` is. The `false` case is therefore unreached
today; [`Modelgen.unitAtUniq`] is the transport it would take, and the
measurement that says so is in that docstring. -/
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

/-! ## Packing an index telescope

The subsingleton arm (INDUCTIVE-BASIS §3.2's degenerate `r := ⊥` case) states
its Henry-Ford equations as **one** `Eq` at the whole index telescope packed
into a right-nested `PSigma`, rather than one `Eq` per index. It has to: a
later index's type may mention an earlier one — `HEq`'s telescope is
`{β : Sort u} (b : β)`, which is already the dependent worst case — and
separate equations cannot be stated, let alone transported along, in that
situation.

The three functions below are driven by the *packed type* rather than by the
telescope. That is deliberate: reading a component's type back off a built
expression is only valid while nothing has beta-reduced it, and that
assumption has already cost this file two attempts (see
[`Modelgen.pairArm`]). A `PSigma` application is stable under everything the
elaborator does to it, so destructuring it is safe. -/

/-- `Σ'(x₁ : A₁) … A_n` over an opened index telescope, right-nested, with the
last index's *type* as the final component — so a one-index telescope packs to
that type alone, with no `PSigma` at all. Closed over the telescope. -/
partial def packTyOf (is : Array Expr) (k : Nat) : GenM (Expr × Level) := do
  let ty ← ityp is[k]!
  let ℓ ← ilevel ty
  if k + 1 == is.size then return (ty, ℓ)
  let (inner, ℓi) ← packTyOf is (k + 1)
  let β ← mkLambdaFVars #[is[k]!] inner
  return (psigmaT ℓ ℓi ty β,
    (mkLevelMax' (mkLevelMax' (.succ .zero) ℓ) ℓi).normalize)

/-- Read a `PSigma` application apart: its two levels, its `α` and its `β`. -/
def psigmaParts (R : Expr) : GenM (Level × Level × Expr × Expr) := do
  let args := R.getAppArgs
  unless R.getAppFn.isConstOf `PSigma && args.size == 2 do
    badShape "the packed index type is not a PSigma application"
  let [u, v] := R.getAppFn.constLevels! | badShape "PSigma carries the wrong level list"
  return (u, v, args[0]!, args[1]!)

/-- The packing of a value vector, driven by the packed type. -/
partial def packChain (n : Nat) (R : Expr) (vs : Array Expr) (k : Nat) : GenM Expr := do
  if n <= 1 then return vs[k]!
  let (u, v, α, β) ← psigmaParts R
  let snd ← packChain (n - 1) (Expr.app β vs[k]!).headBeta vs (k + 1)
  return psigmaMk u v α β vs[k]! snd

/-- The `n` components read back out of a packed term. Structure eta makes
`pack (unpack y) ≡ y`, which is what lets the recursor's motive be stated
about a packed variable and still apply to the declaration's own indices. -/
partial def unpackChain (n : Nat) (R : Expr) (y : Expr) : GenM (Array Expr) := do
  if n <= 1 then return #[y]
  let (u, v, α, β) ← psigmaParts R
  let f := psigmaFst u v α β y
  let sn := psigmaSnd u v α β y
  return #[f] ++ (← unpackChain (n - 1) (Expr.app β f).headBeta sn)

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

/-- **Does `B` factor through the constructor tag?** — the one question that
decides whether a declaration W can model is *certifiable*.

`scripts/inductive-basis/WFromPaths.lean` builds W with a path step carrying
the whole label, so `mk` has to decide `x.1 = a` at the label type; that is
`Classical.propDecidable`, and it costs `[propext, Classical.choice,
Quot.sound]` on every constant. `WTagged.lean` builds the same W with a path
step carrying only the **constructor tag**, so the test is `Fin k` equality and
the bill drops to `[propext, Quot.sound]` — the covered set, since
`Classical.choice` has been refuted as a term of the checker's language while
the other two are certified or covered.

The tagged construction needs the branch type to be a function of the tag
alone, which is exactly: **a recursive field's binder types may not mention the
constructor's own non-recursive fields.** They may mention the parameters,
which are fixed for the whole declaration. `DT | mk : (n : Nat) → (Fin n → DT)
→ DT` is the counterexample and `Lean.Expr.app : Expr → Expr → Expr` is the
common case, whose recursive fields have no binders at all and so pass
vacuously.

De Bruijn bookkeeping, since it is what the test actually is: inside a
recursive field's domain at field position `i`, having opened `j` of the
domain's own binders, indices `0 … j-1` are those binders, `j … j+i-1` are the
constructor's earlier fields, and above that the parameters. So a binder type
must have no loose bvar in `[j, j+i)`.

Non-throwing, and asked of every declaration the W arm would take, so that the
census reports the certifiable and uncertifiable populations as two numbers
rather than one. -/
def tagFactored (tname : Name) (np : Nat) (exportCtors : Array (Name × Expr)) : Bool :=
  exportCtors.all fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then
        -- peel the field's own binder telescope and check each binder type
        let mut d := dom
        let mut j := 0
        while d matches .forallE .. do
          let .forallE _ z db _ := d | unreachable!
          for m in [0:i] do
            if z.hasLooseBVar (j + m) then return false
          d := db
          j := j + 1
      t := b
      i := i + 1
    return true

/-- Which field of a constructor is the recursive one, if any. Declines the
shapes the tower cannot express, each by name. -/
def recSlotOf (tname : Name) (np : Nat) (cn : Name) (nf : Nat) (tele : Expr)
    (tagged : Bool := true) : GenM (Option Nat) := do
  -- **The W arm's bill, printed at the decline that names W.** `tagged` is
  -- [`Modelgen.tagFactored`] for the whole declaration: yes and the tagged
  -- construction models it at `[propext, Quot.sound]`, which is covered; no
  -- and it needs the classical route, which spends `Classical.choice` and is
  -- not certifiable. Two populations, so the census counts two numbers.
  let bill := s!"; B factors through the tag: {if tagged then "yes" else "no"}"
  let mut cur := tele
  let mut slot : Option Nat := none
  for i in [0:nf] do
    let .forallE _ d b _ := cur | badShape "field telescope shorter than its field count"
    if mentionsAny #[tname] d then
      if slot.isSome then
        badShape s!"{cn} has two recursive fields: the tuple tower's spine is one \
Nat and a constructor takes one predecessor, so a branching constructor needs the \
W/path construction (plan B){bill}"
      unless d.getAppFn.isConstOf tname do
        badShape s!"{cn} has a recursive field that is not a bare occurrence of \
{tname} — under a binder, or nested, neither of which the tuple tower reaches{bill}"
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

/-! ## Arm G: the recursive subsingleton, by the **graph** of the recursion

`INDUCTIVE-BASIS.md` §3.2's carrier, and the construction of
`scripts/inductive-basis/AccFromChoice.lean` emitted for an arbitrary shape.
This is the arm that takes **`Acc` out of the basis** rather than putting it
to use.

The shape: an inductive `Prop` with **one** constructor, each of whose fields
is a proposition (possibly a recursive occurrence `∀ z⃗, T p⃗ e⃗`) or a piece of
data that is *literally* one of the conclusion's indices. Lean's kernel grants
that shape a `Sort v` motive by the subsingleton rule — a grant to a
*declaration* that an emitted `def` does not inherit — and the carrier the
Church route already emits eliminates only into `Prop`. So the large
eliminator has to be built, and it is built by defining the recursion by its
**graph**:

```text
Graph ι⃗ t val  := the least relation closed under "if the value at every
                   recursive sub-argument is g, then the value at (mk f⃗) is
                   step f⃗ g⃗", impredicatively encoded — so a Prop
Graph.mk        : that closure rule, as a theorem (the graph is a fixed
                   point, not merely a pre-fixed point)
GraphInv        : inversion, with the constructor's **proof** fields
                   universally quantified rather than existentially — any two
                   are definitionally equal, so quantifying gives the caller's
Graph.inv       : inversion holds, by folding at `Graph ∧ GraphInv`
Graph.unique    : single-valuedness, by the free `Prop`-motive recursor
Graph.exists    : totality, likewise, picking sub-values with Classical.choice
rec_0 step t    := (Classical.choice (Graph.exists step t)).fst
iota            : both sides are graph points and the graph is single-valued
```

**Do not** try `Classical.choice` at a bare `Nonempty (motive a t)` instead.
That recursor typechecks and is provably *blind to its step function* — the
two `Nonempty` proofs are definitionally equal — so its ι rule is not merely
unproved but derives `False`. `AccFromChoice.lean` §4 compiles the refutation.

**ι is propositional here, not `Eq.refl`** — the value is a `Classical.choice`
application, which reduces to nothing — and this is the only arm of the three
routes for which that is true. A consumer must rewrite with `iota_0_0` where
the kernel would have reduced.

**Two lines of the recipe are shape-sensitive**, and both are mechanical:
[`Modelgen.congrChain`]'s n-ary congruence, one factor per recursive field,
and [`Modelgen.funextUp`]'s chain, one `funext` per binder of a recursive
field. `scripts/inductive-basis/AccArmShapes.lean` carries the recipe through
the three shapes that settle them.

**The axiom cost is per shape, not per arm.** `rec_0` is `Classical.choice`
uniformly; ι adds `funext` — hence the quotient and `Quot.sound` — only when
some recursive field has a binder, because that is the only thing
[`Modelgen.funextUp`] is called for. A recursive field that is a bare
occurrence contributes none, and the degenerate shape's ι costs no
`Quot.sound` at all. -/

/-- `∀ D : Prop, (A → B → D) → D` — Church conjunction, so the folds below
need no `And` and the basis needs no sixth member for one. -/
def andCOf (A B : Expr) : Expr :=
  .forallE `D (.sort .zero)
    (.forallE `k (.forallE `a A (.forallE `b B (.bvar 2) .default) .default)
      (.bvar 1) .default) .default

/-- `Eq α x z` from `Eq α x y` and `Eq α y z`, as one `Eq.rec` at a `Prop`
motive — the companion of [`Modelgen.symmOf`], and built the same way so that
nothing is added to the input that this module does not need to name. -/
def transOf (eqi : EqInfo) (ℓ : Level) (α x y z h1 h2 : Expr) : GenM Expr :=
  transportAlong eqi .zero ℓ α y z h2 h1 fun w => pure (eqi.mk' ℓ α x w)

/-- Bind a vector of **independent** locals in one scope. Independent is the
precondition and it is met at every call: the value functions `g⃗` depend only
on the constructor's fields, and the graph hypotheses `hg⃗` only on those and
on `g⃗`, which are bound first. -/
partial def withLocalsD (tys : Array (Name × Expr)) (i : Nat) (acc : Array Expr)
    (k : Array Expr → GenM Expr) : GenM Expr := do
  if i == tys.size then k acc
  else withLocalDeclD tys[i]!.1 tys[i]!.2 fun x => withLocalsD tys (i + 1) (acc.push x) k

/-- **Walk the constructor's field telescope**, binding one variable per
field — except that with `subst` set the *data* fields are **supplied** from
`is` rather than bound, because in this shape a data field is literally one of
the conclusion's indices.

That substitution is what `GraphInv` is stated by: inversion at an arbitrary
index `ι⃗` must conclude `val = step f⃗ g⃗`, whose right-hand side lands at the
quantified fields' own index expressions, so those expressions have to *be*
`ι⃗`. Quantifying the data fields instead would need the index's injectivity,
which is exactly the case `AccFromChoice.lean` records as not uniform.

`k` receives the full field vector, the ones actually bound, and the
telescope's result type. -/
partial def ctorFieldsAux (subst : Bool) (isData : Array Bool) (idxPos : Array Nat)
    (is : Array Expr) (n i : Nat) (tele : Expr) (fs bound : Array Expr)
    (k : Array Expr → Array Expr → Expr → GenM Expr) : GenM Expr := do
  if n == 0 then return ← k fs bound tele
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  if subst && isData[i]! then
    let a := is[idxPos[i]!]!
    ctorFieldsAux subst isData idxPos is (n - 1) (i + 1) (b.instantiate1 a) (fs.push a) bound k
  else
    withLocalDecl x bi d fun xv =>
      ctorFieldsAux subst isData idxPos is (n - 1) (i + 1) (b.instantiate1 xv)
        (fs.push xv) (bound.push xv) k

/-- **The `funext` chain, one per binder of a recursive field.** `pt` proves
`ga z⃗ = gb z⃗` at the field's own binders `z⃗`; this closes them one at a time,
innermost first, into `ga = gb`.

At **zero** binders it is the identity and no `funext` is reached at all —
which is why the degenerate shape's ι costs no `Quot.sound`, and why the
`funext` is asked for lazily and only when some recursive field has a
binder. -/
partial def funextUp (fx? : Option Name) (zs : Array Expr) (k : Nat)
    (ga gb pt : Expr) : GenM Expr := do
  if k == 0 then return pt
  let j := k - 1
  let z := zs[j]!
  let some fxN := fx?
    | badShape "a recursive field under a binder needs funext and none was available"
  let αz ← ityp z
  let lu ← ilevel αz
  let fa := mkAppN ga (zs.extract 0 j)
  let fb := mkAppN gb (zs.extract 0 j)
  let bty ← ityp (mkApp fa z)
  let lv ← ilevel bty
  let β ← mkLambdaFVars #[z] bty
  let h ← mkLambdaFVars #[z] pt
  funextUp fx? zs j ga gb (mkAppN (.const fxN [lu, lv]) #[αz, β, fa, fb, h])

/-- **The n-ary congruence in the recursive fields**, as an `Eq.trans` chain
with one `congrArg` per field:

```text
step f⃗ ga₁ ga₂ … = step f⃗ gb₁ ga₂ … = step f⃗ gb₁ gb₂ … = … = step f⃗ gb⃗
```

`AccFromChoice`'s single `congrArg (step x h)` is the `n = 1` case of this and
is insufficient at two recursive fields; `AccArmShapes.lean` §2 is the shape
that measures it. Each `congrArg` is one `Eq.rec`, inlined here for the same
reason [`Modelgen.funextDecl`] inlines its own. -/
def congrChain (eqi : EqInfo) (v : Level) (α : Expr) (mkStep : Array Expr → Expr)
    (ga gb pfs : Array Expr) : GenM Expr := do
  let n := ga.size
  let mixed := fun (j : Nat) => (Array.range n).map fun m => if m < j then gb[m]! else ga[m]!
  let base := mkStep ga
  let mut acc := eqi.refl' v α base
  for j in [0:n] do
    let A ← ityp ga[j]!
    let ℓA ← ilevel A
    let famAt := fun (x : Expr) => mkStep ((mixed j).set! j x)
    let factor ← transportAlong eqi .zero ℓA A ga[j]! gb[j]! pfs[j]!
      (eqi.refl' v α (famAt ga[j]!)) fun z => pure (eqi.mk' v α (famAt ga[j]!) (famAt z))
    acc ← transOf eqi v α base (mkStep (mixed j)) (mkStep (mixed (j + 1))) acc factor
  return acc

/-- Everything [`Modelgen.graphArm`] needs about the declaration it is
modelling, settled before a single declaration is emitted so that a decline
costs no splice. -/
structure GraphCtx where
  tname : Name
  np : Nat
  ni : Nat
  nf : Nat
  /-- The declaration's own levels, and the recursor's (`v` in front). -/
  us : List Level
  recLs : List Level
  lparams : List Name
  recLevels : List Name
  /-- The motive universe. -/
  v : Level
  selfN : Name
  ctorN0 : Name
  recN : Name
  indN : Name
  grN : Name
  grMkN : Name
  grInvTN : Name
  grInvN : Name
  grUniqN : Name
  grExN : Name
  recGrN : Name
  /-- The declaration's own type, and the model constructor's — **restored**,
  so a recursive field's type is `T._model.self p⃗ e⃗`. -/
  memberTy : Expr
  ctorTy : Expr
  /-- Per field: is it data (rather than a proof), and if so which index
  position it *is*; and, for a recursive field, its binder count. -/
  isData : Array Bool
  idxPos : Array Nat
  recNb : Array (Option Nat)
  eqi : EqInfo
  /-- The `funext` the `Graph.unique` congruence transports along, `none` when
  no recursive field has a binder and none is reached. -/
  fx? : Option Name
  deriving Inhabited

/-- **The graph arm**, emitting `graph`, `graph_mk`, `graph_inv_ty`,
`graph_inv`, `graph_unique`, `graph_exists`, `rec_0` and `rec_graph`. The
carrier, the constructor and the `Prop`-motive recursor `ind` are the Church
route's own and are emitted by the caller; the ι theorem is the caller's too,
because its *statement* is shared with every other arm and only its proof is
this one's. -/
def graphArm (c : GraphCtx) (recTy : Expr) : GenM (Array Declaration) := do
  let np := c.np
  let ni := c.ni
  let nf := c.nf
  -- the recursive slots, in field order
  let rs := (Array.range nf).filter fun i => c.recNb[i]!.isSome
  let nr := rs.size

  -- **One scope for the whole arm**: the parameters, the motive and the step,
  -- read off the recursor's own type rather than rebuilt. `rest` is what is
  -- left of that type — `∀ ι⃗ (t : Self ι⃗), motive ι⃗ t` — and the two
  -- declarations that need the full telescope continue it rather than
  -- reopening.
  forallBoundedTelescope recTy (some (np + 2)) fun bs rest => do
    let mut out : Array Declaration := #[]
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let step := bs[np + 1]!
    let pre := ps ++ #[motive, step]

    let selfAt := fun (is : Array Expr) => mkAppN (.const c.selfN c.us) (ps ++ is)
    let ctorAt := fun (fs : Array Expr) => mkAppN (.const c.ctorN0 c.us) (ps ++ fs)
    let motAt := fun (is : Array Expr) (t : Expr) => mkAppN motive (is.push t)
    let grAt := fun (is : Array Expr) (t val : Expr) =>
      mkAppN (.const c.grN c.recLs) (pre ++ is ++ #[t, val])
    let grInvAt := fun (is : Array Expr) (t val : Expr) =>
      mkAppN (.const c.grInvTN c.recLs) (pre ++ is ++ #[t, val])
    let idxTele ← instForall c.memberTy ps
    let ctorTele ← instForall c.ctorTy ps

    -- A recursive field's own binders, and the index vector it lands at. The
    -- telescope is opened **bounded**: `forallTelescope` would whnf through
    -- `T._model.self` and open the Church encoding's own Π as well.
    let recAt := fun (f : Expr) (nb : Nat) (k : Array Expr → Array Expr → GenM Expr) => do
      forallBoundedTelescope (← ityp f) (some nb) fun zs res => do
        let args := res.getAppArgs
        unless res.getAppFn.isConstOf c.selfN && args.size == np + ni do
          badShape s!"a recursive field of {c.tname} does not land at {c.selfN}"
        k zs (args.extract np args.size)

    -- The constructor's field telescope. `is?` supplies the data fields.
    let fields := fun (is? : Option (Array Expr))
        (k : Array Expr → Array Expr → Expr → GenM Expr) =>
      ctorFieldsAux is?.isSome c.isData c.idxPos (is?.getD #[]) nf 0 ctorTele #[] #[] k

    -- The index vector a walked telescope ends at.
    let idxOfRes := fun (res : Expr) => do
      let args := res.getAppArgs
      unless res.getAppFn.isConstOf c.selfN && args.size == np + ni do
        badShape s!"{c.ctorN0}'s result is not {c.selfN} at {np} parameters and {ni} indices"
      pure (args.extract np args.size)

    -- `g_i : ∀ z⃗_i, motive e⃗_i (f_i z⃗_i)`, the value functions.
    let gTysAt := fun (fs : Array Expr) => rs.mapM fun i => do
      let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
        mkForallFVars zs (motAt ris (mkAppN fs[i]! zs))
      pure (Name.mkSimple s!"g{i}", t)
    -- `hg_i : ∀ z⃗_i, Graph e⃗_i (f_i z⃗_i) (g_i z⃗_i)`.
    let hTysAt := fun (fs gs : Array Expr) => (Array.range nr).mapM fun j => do
      let i := rs[j]!
      let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
        mkForallFVars zs (grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs))
      pure (Name.mkSimple s!"hg{i}", t)

    -- ── `Q`, and the graph's one closure rule at it ──
    let qTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `s (selfAt is) fun s =>
        withLocalDeclD `m (motAt is s) fun m =>
          mkForallFVars (is ++ #[s, m]) (.sort .zero)
    let qStepTy := fun (Q : Expr) =>
      fields none fun fs bnd res => do
        let e ← idxOfRes res
        withLocalsD (← gTysAt fs) 0 #[] fun gs => do
          let qTys ← (Array.range nr).mapM fun j => do
            let i := rs[j]!
            let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
              mkForallFVars zs (mkAppN Q (ris ++ #[mkAppN fs[i]! zs, mkAppN gs[j]! zs]))
            pure (Name.mkSimple s!"q{i}", t)
          withLocalsD qTys 0 #[] fun qs =>
            mkForallFVars (bnd ++ gs ++ qs)
              (mkAppN Q (e ++ #[ctorAt fs, mkAppN step (fs ++ gs)]))

    -- ── `Graph` ──
    let grTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          mkForallFVars (pre ++ is ++ #[t, val]) (.sort .zero)
    let grVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          withLocalDeclD `Q qTy fun Q => do
            let body ← mkForallFVars #[Q]
              (.forallE `q (← qStepTy Q) (mkAppN Q (is ++ #[t, val])) .default)
            mkLambdaFVars (pre ++ is ++ #[t, val]) body
    let dGr := Declaration.defnDecl
      { name := c.grN, levelParams := c.recLevels, type := grTy, value := grVal
        hints := ← hintsFor grVal, safety := .safe }
    addChecked dGr
    out := out.push dGr

    -- ── `Graph.mk` ──
    let grMkTy ← fields none fun fs bnd res => do
      let e ← idxOfRes res
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs =>
          mkForallFVars (pre ++ bnd ++ gs ++ hs)
            (grAt e (ctorAt fs) (mkAppN step (fs ++ gs)))
    let grMkVal ← fields none fun fs bnd _ => do
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs =>
          withLocalDeclD `Q qTy fun Q => do
            withLocalDeclD `q (← qStepTy Q) fun q => do
              let qargs ← (Array.range nr).mapM fun j => do
                let i := rs[j]!
                recAt fs[i]! c.recNb[i]!.get! fun zs _ =>
                  mkLambdaFVars zs (mkAppN (mkAppN hs[j]! zs) #[Q, q])
              mkLambdaFVars (pre ++ bnd ++ gs ++ hs)
                (← mkLambdaFVars #[Q, q] (mkAppN q (fs ++ gs ++ qargs)))
    let dGrMk := Declaration.thmDecl
      { name := c.grMkN, levelParams := c.recLevels, type := grMkTy, value := grMkVal }
    addChecked dGrMk
    out := out.push dGrMk

    -- ── `GraphInv` ──
    -- The `k` argument's type, shared by the definition and by the two places
    -- that build or consume an inhabitant of it.
    let invArmTyAt := fun (is : Array Expr) (t val : Expr) (fs : Array Expr) (D : Expr) => do
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs => do
          let eq := c.eqi.mk' c.v (motAt is t) val (mkAppN step (fs ++ gs))
          mkForallFVars (gs ++ hs) (.forallE `he eq D .default)
    let grInvVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val => do
          let body ← fields (some is) fun fs bnd res => do
            -- With the data fields supplied as the index variables the
            -- constructor's own index expressions **are** `ι⃗`, and that is
            -- what makes the equation below statable at an arbitrary index.
            unless (← idxOfRes res) == is do
              badShape s!"{c.tname}'s constructor does not present its indices as its \
own data fields"
            withLocalDeclD `D (.sort .zero) fun D => do
              mkForallFVars (bnd ++ #[D])
                (.forallE `k (← invArmTyAt is t val fs D) D .default)
          mkLambdaFVars (pre ++ is ++ #[t, val]) body
    let dGrInvT := Declaration.defnDecl
      { name := c.grInvTN, levelParams := c.recLevels, type := grTy, value := grInvVal
        hints := ← hintsFor grInvVal, safety := .safe }
    addChecked dGrInvT
    out := out.push dGrInvT

    -- ── `Graph.inv` ──
    -- Fold at `Graph ∧ GraphInv`: the graph alone is not closed enough to
    -- rebuild the sub-values' graph facts. The `rfl` at the end is where
    -- proof irrelevance does the work — the fold's own fields and the
    -- inversion's quantified ones are two proofs of one proposition, so
    -- `step f⃗ g⃗` and `step f'⃗ g⃗` are the same term.
    let grInvThmTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          mkForallFVars (pre ++ is ++ #[t, val])
            (.forallE `g (grAt is t val) (grInvAt is t val) .default)
    let grInvThmVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          withLocalDeclD `g (grAt is t val) fun g => do
            let qArg ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
              withLocalDeclD `s (selfAt is') fun s =>
                withLocalDeclD `w (motAt is' s) fun w =>
                  mkLambdaFVars (is' ++ #[s, w]) (andCOf (grAt is' s w) (grInvAt is' s w))
            let qStepArg ← fields none fun fs bnd res => do
              let e ← idxOfRes res
              withLocalsD (← gTysAt fs) 0 #[] fun gs => do
                let ihTys ← (Array.range nr).mapM fun j => do
                  let i := rs[j]!
                  let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
                    mkForallFVars zs
                      (andCOf (grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs))
                        (grInvAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)))
                  pure (Name.mkSimple s!"ih{i}", t')
                withLocalsD ihTys 0 #[] fun ihs => do
                  -- the left projection of each `AndC`, pointwise
                  let hgs ← (Array.range nr).mapM fun j => do
                    let i := rs[j]!
                    recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
                      let gt := grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)
                      let it := grInvAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)
                      let proj ← withLocalDeclD `a gt fun a =>
                        withLocalDeclD `b it fun b => mkLambdaFVars #[a, b] a
                      mkLambdaFVars zs (mkAppN (mkAppN ihs[j]! zs) #[gt, proj])
                  let major := ctorAt fs
                  let val' := mkAppN step (fs ++ gs)
                  let aTerm := mkAppN (.const c.grMkN c.recLs) (pre ++ bnd ++ gs ++ hgs)
                  let bTerm ← fields (some e) fun fs' bnd' _ => do
                    withLocalDeclD `D (.sort .zero) fun D => do
                      withLocalDeclD `k (← invArmTyAt e major val' fs' D) fun k' =>
                        mkLambdaFVars (bnd' ++ #[D, k'])
                          (mkAppN k' (gs ++ hgs ++
                            #[c.eqi.refl' c.v (motAt e major) val']))
                  let aT := grAt e major val'
                  let bT := grInvAt e major val'
                  let pair ← withLocalDeclD `D (.sort .zero) fun D =>
                    withLocalDeclD `k (.forallE `a aT (.forallE `b bT D .default) .default)
                      fun k' => mkLambdaFVars #[D, k'] (mkAppN k' #[aTerm, bTerm])
                  mkLambdaFVars (bnd ++ gs ++ ihs) pair
            let fin ← withLocalDeclD `a (grAt is t val) fun a =>
              withLocalDeclD `b (grInvAt is t val) fun b => mkLambdaFVars #[a, b] b
            mkLambdaFVars (pre ++ is ++ #[t, val, g])
              (mkAppN g #[qArg, qStepArg, grInvAt is t val, fin])
    let dGrInv := Declaration.thmDecl
      { name := c.grInvN, levelParams := c.recLevels, type := grInvThmTy
        value := grInvThmVal }
    addChecked dGrInv
    out := out.push dGrInv

    -- ── `Graph.unique` ──
    -- Single-valuedness, by the free `Prop`-motive recursor. This is the one
    -- place `funext` enters, and only for a recursive field with binders.
    let uniqTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `a (motAt is t) fun a =>
          withLocalDeclD `b (motAt is t) fun b =>
            mkForallFVars (pre ++ is ++ #[t, a, b])
              (.forallE `ga (grAt is t a)
                (.forallE `gb (grAt is t b) (c.eqi.mk' c.v (motAt is t) a b) .default)
                .default)
    let indMotUniq ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
      withLocalDeclD `t' (selfAt is') fun t' => do
        let inner ← withLocalDeclD `a' (motAt is' t') fun a' =>
          withLocalDeclD `b' (motAt is' t') fun b' =>
            mkForallFVars #[a', b']
              (.forallE `ga' (grAt is' t' a')
                (.forallE `gb' (grAt is' t' b') (c.eqi.mk' c.v (motAt is' t') a' b')
                  .default) .default)
        mkLambdaFVars (is' ++ #[t']) inner
    let uniqVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `a (motAt is t) fun a =>
          withLocalDeclD `b (motAt is t) fun b =>
            withLocalDeclD `ga (grAt is t a) fun ga =>
              withLocalDeclD `gb (grAt is t b) fun gb => do
                let minor ← fields none fun fs bnd res => do
                  let e ← idxOfRes res
                  let major := ctorAt fs
                  let α := motAt e major
                  let ihTys ← rs.mapM fun i => do
                    let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
                      mkForallFVars zs
                        (mkAppN indMotUniq (ris ++ #[mkAppN fs[i]! zs])).headBeta
                    pure (Name.mkSimple s!"ih{i}", t')
                  withLocalsD ihTys 0 #[] fun ihs =>
                    withLocalDeclD `x (motAt e major) fun x =>
                      withLocalDeclD `y (motAt e major) fun y =>
                        withLocalDeclD `gx (grAt e major x) fun gx =>
                          withLocalDeclD `gy (grAt e major y) fun gy => do
                            let goal := c.eqi.mk' c.v α x y
                            -- the fields inversion quantifies are the **proof**
                            -- ones; the data fields are the indices and are
                            -- already fixed by the point `GraphInv` is at.
                            let pf := (Array.range nf).filterMap fun i =>
                              if c.isData[i]! then none else some fs[i]!
                            let contA ←
                              withLocalsD (← gTysAt fs) 0 #[] fun gA => do
                                withLocalsD (← hTysAt fs gA) 0 #[] fun hA =>
                                  withLocalDeclD `ea
                                    (c.eqi.mk' c.v α x (mkAppN step (fs ++ gA))) fun eA => do
                                    let contB ←
                                      withLocalsD (← gTysAt fs) 0 #[] fun gB => do
                                        withLocalsD (← hTysAt fs gB) 0 #[] fun hB =>
                                          withLocalDeclD `eb
                                            (c.eqi.mk' c.v α y (mkAppN step (fs ++ gB)))
                                            fun eB => do
                                            let pfs ← (Array.range nr).mapM fun j => do
                                              let i := rs[j]!
                                              recAt fs[i]! c.recNb[i]!.get! fun zs _ => do
                                                let pt := mkAppN (mkAppN ihs[j]! zs)
                                                  #[mkAppN gA[j]! zs, mkAppN gB[j]! zs,
                                                    mkAppN hA[j]! zs, mkAppN hB[j]! zs]
                                                funextUp c.fx? zs zs.size gA[j]! gB[j]! pt
                                            let cong ← congrChain c.eqi c.v α
                                              (fun gv => mkAppN step (fs ++ gv)) gA gB pfs
                                            let sb ← symmOf c.eqi c.v α y
                                              (mkAppN step (fs ++ gB)) eB
                                            let t2 ← transOf c.eqi c.v α
                                              (mkAppN step (fs ++ gA)) (mkAppN step (fs ++ gB))
                                              y cong sb
                                            let whole ← transOf c.eqi c.v α x
                                              (mkAppN step (fs ++ gA)) y eA t2
                                            mkLambdaFVars (gB ++ hB ++ #[eB]) whole
                                    let invB := mkAppN (.const c.grInvN c.recLs)
                                      (pre ++ e ++ #[major, y, gy])
                                    mkLambdaFVars (gA ++ hA ++ #[eA])
                                      (mkAppN invB (pf ++ #[goal, contB]))
                            let invA := mkAppN (.const c.grInvN c.recLs)
                              (pre ++ e ++ #[major, x, gx])
                            mkLambdaFVars (bnd ++ ihs ++ #[x, y, gx, gy])
                              (mkAppN invA (pf ++ #[goal, contA]))
                mkLambdaFVars (pre ++ is ++ #[t, a, b, ga, gb])
                  (mkAppN (mkAppN (.const c.indN c.us) (ps ++ #[indMotUniq, minor] ++ is ++ #[t]))
                    #[a, b, ga, gb])
    let dGrUniq := Declaration.thmDecl
      { name := c.grUniqN, levelParams := c.recLevels, type := uniqTy, value := uniqVal }
    addChecked dGrUniq
    out := out.push dGrUniq

    -- ── `Graph.exists` ──
    -- Totality, again by the `Prop`-motive recursor. `Classical.choice` picks
    -- the sub-values here, and single-valuedness above is what makes the
    -- choice harmless. The `Nonempty` is of the **PSigma of value and graph
    -- proof**, never of `motive ι⃗ t`: that is the whole difference from the
    -- route `AccFromChoice.lean` §4 refutes.
    let neAt := fun (is : Array Expr) (t : Expr) => do
      let α := motAt is t
      let β ← withLocalDeclD `val α fun val => mkLambdaFVars #[val] (grAt is t val)
      let σ := psigmaT c.v .zero α β
      let ℓσ := (mkLevelMax' (mkLevelMax' (.succ .zero) c.v) .zero).normalize
      pure (mkAppN (.const `Nonempty [ℓσ]) #[σ], σ, α, β, ℓσ)
    let grExTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t => do
        let (ne, _, _, _, _) ← neAt is t
        mkForallFVars (pre ++ is ++ #[t]) ne
    let indMotEx ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
      withLocalDeclD `t' (selfAt is') fun t' => do
        let (ne, _, _, _, _) ← neAt is' t'
        mkLambdaFVars (is' ++ #[t']) ne
    let grExVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t => do
        let minor ← fields none fun fs bnd res => do
          let e ← idxOfRes res
          let ihTys ← rs.mapM fun i => do
            let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
              let (ne, _, _, _, _) ← neAt ris (mkAppN fs[i]! zs)
              mkForallFVars zs ne
            pure (Name.mkSimple s!"ih{i}", t')
          withLocalsD ihTys 0 #[] fun ihs => do
            let pick := fun (j : Nat) (snd : Bool) => do
              let i := rs[j]!
              recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
                let (_, σ, α, β, ℓσ) ← neAt ris (mkAppN fs[i]! zs)
                let ch := mkAppN (.const `Classical.choice [ℓσ]) #[σ, mkAppN ihs[j]! zs]
                mkLambdaFVars zs
                  (if snd then psigmaSnd c.v .zero α β ch else psigmaFst c.v .zero α β ch)
            let ghat ← (Array.range nr).mapM fun j => pick j false
            let hhat ← (Array.range nr).mapM fun j => pick j true
            let (_, σ0, α0, β0, ℓσ0) ← neAt e (ctorAt fs)
            let value := mkAppN step (fs ++ ghat)
            let proof := mkAppN (.const c.grMkN c.recLs) (pre ++ fs ++ ghat ++ hhat)
            mkLambdaFVars (bnd ++ ihs)
              (mkAppN (.const `Nonempty.intro [ℓσ0])
                #[σ0, psigmaMk c.v .zero α0 β0 value proof])
        mkLambdaFVars (pre ++ is ++ #[t])
          (mkAppN (.const c.indN c.us) (ps ++ #[indMotEx, minor] ++ is ++ #[t]))
    let dGrEx := Declaration.thmDecl
      { name := c.grExN, levelParams := c.recLevels, type := grExTy, value := grExVal }
    addChecked dGrEx
    out := out.push dGrEx

    -- ── the recursor, and the graph fact about it ──
    let recVal ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      let (_, σ, α, β, ℓσ) ← neAt is t
      let ch := mkAppN (.const `Classical.choice [ℓσ])
        #[σ, mkAppN (.const c.grExN c.recLs) (pre ++ is ++ #[t])]
      mkLambdaFVars (pre ++ bs2) (psigmaFst c.v .zero α β ch)
    let dRec := Declaration.defnDecl
      { name := c.recN, levelParams := c.recLevels, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec

    let rgTy ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      mkForallFVars (pre ++ bs2)
        (grAt is t (mkAppN (.const c.recN c.recLs) (pre ++ bs2)))
    let rgVal ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      let (_, σ, α, β, ℓσ) ← neAt is t
      let ch := mkAppN (.const `Classical.choice [ℓσ])
        #[σ, mkAppN (.const c.grExN c.recLs) (pre ++ is ++ #[t])]
      mkLambdaFVars (pre ++ bs2) (psigmaSnd c.v .zero α β ch)
    let dRg := Declaration.thmDecl
      { name := c.recGrN, levelParams := c.recLevels, type := rgTy, value := rgVal }
    addChecked dRg
    out := out.push dRg

    return out

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
the plan needs none. A `dsingOk` level gets the [`Modelgen.dsingAt`] pad; any
other level — a bare parameter in the gap, `PULift`'s shape — gets the
[`Modelgen.unitAt`] lift, which exists at every level.

**Both are marked `canonical`**, and that is the measured fact rather than a
symmetry: each family's canonical element is a literal constructor
application, so the kernel converts an opaque element onto it and neither pad
costs a transport. What the lift does *not* give is a conversion between two
opaque elements; nothing here asks for one. -/
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

/-! ## Arm C's index erasure

The skeleton arm C splices is the declaration with its indices dropped: the
carrier loses its index telescope and every recursive field and every
constructor's conclusion loses its index arguments. Nothing else moves — the
field telescope is kept **exactly**, which is the whole reason this arm has no
currying glue where the W route has one lemma per constructor.

Both functions below are **raw `Expr` surgery on de Bruijn indices and not a
telescope walk**, and that is forced rather than stylistic: opening a telescope
means `withLocalDecl` at a type mentioning `T._model.skel`, which `MetaM` would
have to `inferType`, and the constant does not exist yet — it is the one being
declared. Asking for it costs an `Unknown constant` and exit 3. -/

/-- `∀ p⃗, Sort w` from the declaration's `∀ p⃗ ι⃗, Sort w`. -/
partial def eraseSelfTy (np : Nat) (w : Level) (e : Expr) : Expr :=
  if np == 0 then .sort w else
  match e with
  | .forallE x d b bi => .forallE x d (eraseSelfTy (np - 1) w b) bi
  | _ => .sort w

/-- One constructor's type with its indices erased. After `np` parameters and
`i` field binders the parameter `p_k` sits at de Bruijn index `np-1-k+i`, which
is what `skelAt` rebuilds `T._model.skel p⃗` from.

A field is recursive exactly when it mentions `tname`, and `erasureLinear` has
already established that such a field is a bare `T p⃗ e⃗` — so replacing the
whole domain is right, and a field this would corrupt has been declined. -/
partial def eraseCtorTy (tname skelN : Name) (us : List Level) (np : Nat) (e : Expr) : Expr :=
  let skelAt := fun (d : Nat) => mkAppN (.const skelN us)
    ((Array.range np).map fun k => Expr.bvar (np - 1 - k + d))
  let rec fields (i : Nat) (t : Expr) : Expr :=
    match t with
    | .forallE x dom b bi =>
      .forallE x (if mentionsAny #[tname] dom then skelAt i else dom) (fields (i + 1) b) bi
    | _ => skelAt i
  let rec params (k : Nat) (t : Expr) : Expr :=
    if k == np then fields 0 t else
    match t with
    | .forallE x dom b bi => .forallE x dom (params (k + 1) b) bi
    | _ => fields 0 t
  params 0 e

/-- The model of one simple inductive from the primitives, or the shape that
stopped it. **The export's declaration must already be installed**: the
recursor this restates is the one Lean minted for it, and the ι rules are
its own, restored — exactly [`Modelgen.mutualIso`]'s arrangement. -/
def primIso (tname : Name) (root : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (reserved : Std.HashSet Name) : GenM Iso := do
  let us := lparams.map Level.param
  -- **Where the model is built and where it is emitted can differ.** `root` is
  -- the former and `tname` the latter; they are the same name for every
  -- declaration but the handful whose model name is lost to a normalized-name
  -- collision, where [`Modelgen.genPrim`] retries under an alias root and
  -- renames the export records back (`MODELGEN.md` §8.14). So every *guard*
  -- below is about `tname`'s names — those are what reach the output and what
  -- must not collide with the input — while every name *built* is `root`'s.
  let model := Name.str root "_model"
  let emitModel := Name.str tname "_model"
  let selfN := Name.str model "self"
  let ctorN := fun (j : Nat) => Name.str model s!"ctor_{j}"
  let recN := Name.str model "rec_0"
  let iotaN := fun (j : Nat) => Name.str model s!"iota_0_{j}"
  let indN := Name.str model "ind"
  -- Arm G's **internal** names, guarded exactly like the interface's — but
  -- only when the arm is taken, so a file that declares `T._model.graph` of
  -- its own costs nothing to a declaration this arm never sees.
  let graphNames : List Name :=
    [indN, Name.str model "graph", Name.str model "graph_mk",
     Name.str model "graph_inv_ty", Name.str model "graph_inv",
     Name.str model "graph_unique", Name.str model "graph_exists",
     Name.str model "rec_graph"]
  -- Arm C's **internal** names. `skel` is the index erasure, spliced as an
  -- ordinary inductive so that the kernel mints its recursor and its ι is
  -- definitional (`MODELGEN.md` §8.10's rule: use the real type); `good` is
  -- the carving predicate. Guarded like arm G's, and only when the arm fires.
  let skelN := Name.str model "skel"
  let goodN := Name.str model "good"
  let skelCtorN := fun (j : Nat) => Name.str skelN s!"c_{j}"
  let nc := exportCtors.size

  if primBasis.contains tname then
    badShape "a basis primitive (the exemption that makes the construction well-founded)"

  -- The guard runs on the **emitted** name and, where the two differ, on the
  -- built one too: the first is the contract this run must not break and the
  -- second is a constant this run is about to add to the environment.
  let taken1 : Name → GenM Unit := fun n => do
    if reserved.contains n || (← getEnv).constants.contains n then declineWith (.nameTaken n)
  let taken : Name → GenM Unit := fun n => do
    taken1 (Modelgen.renameRoot model emitModel n)
    if model != emitModel then taken1 n
  taken selfN
  taken recN
  for j in [0:nc] do
    taken (ctorN j)
    taken (iotaN j)

  -- ── shape ──
  -- **A declaration may hide its index telescope behind a definition.** Lean
  -- stores an inductive's type as declared, so `inductive P (X) : Presieve X`
  -- comes back as `(X : C) → Presieve X` with the indices inside the `def`,
  -- and a syntactic peel finds no `Sort` at the end and no indices at all.
  -- Lean's own `numIndices` counts the *unfolded* ones — which is why the
  -- assertion against the recursor below is the cross-check on this and not a
  -- second opinion.
  --
  -- So: peel syntactically first, and only if that does not reach a sort,
  -- re-expose the telescope with a **reducing** telescope and carry on with
  -- the definitionally-equal type that has its binders written out. The retry
  -- is deliberately not the default — every shape that worked before this
  -- reaches the same `memberTy` object it always did, so nothing that was
  -- measured moves.
  let peel : Expr → Option (Nat × Level) := fun ty => Id.run do
    let mut cur := ty
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => return none
    let mut n := 0
    while cur matches .forallE .. do
      let .forallE _ _ b _ := cur | unreachable!
      cur := b
      n := n + 1
    match cur with
    | .sort w => return some (n, w)
    | _ => return none
  let (memberTy, ni, w) ←
    match peel memberTy with
    | some (n, w) => pure (memberTy, n, w)
    | none => do
      let exposed ← forallBoundedTelescope memberTy (some np) fun ps rest =>
        forallTelescopeReducing rest fun is res => do
          unless (← whnf res) matches .sort _ do
            badShape "the declaration does not land in a sort, even after unfolding \
              its result type"
          mkForallFVars (ps ++ is) (← whnf res)
      let some (n, w) := peel exposed
        | badShape "the declaration does not land in a sort"
      pure (exposed, n, w)
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

  -- **Is the index erasure linear?** — the one question arm C's reach turns
  -- on, and the same test the tuple tower applies
  -- ([`Modelgen.recSlotOf`]): at most one recursive field per constructor, and
  -- every recursive occurrence a *bare* `T p⃗ e⃗` rather than one under a
  -- binder or inside a container. Erasing the indices does not move that test
  -- — a field `T p⃗ e⃗` erases to `S p⃗`, one field either way — so it can be
  -- asked here, of the family itself, before anything is built.
  --
  -- Non-throwing on purpose: it is asked of *every* indexed family, and the
  -- ones it says no to are declined with the answer printed, so the Mathlib
  -- census measures the arm's reach instead of estimating it.
  let erasureLinear : Bool := exportCtors.all fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut nrec := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then
        nrec := nrec + 1
        unless dom.getAppFn.isConstOf tname do return false
      t := b
    return nrec <= 1

  -- What each route can carry. The Church routes gained indices and recursion
  -- (`churchSwapAt` and the strong-induction fold below); the `Nat`-tagged sum
  -- has neither, and at a maybe-zero sort the lift would have to be threaded
  -- through both, which is not done.
  match route with
  | PrimRoute.type =>
    if ni > 0 && !erasureLinear then
      badShape s!"an indexed family at a never-zero sort whose index erasure is not \
        linear (arm C splices the erasure and carves the family out of it — \
        MODELGEN.md §8.15 — so its reach is bounded by whether that erasure \
        models, and a branching erasure is W's, not the tuple tower's); \
        erasure linear: no; B factors through the tag: \
        {if tagFactored tname np exportCtors then "yes" else "no"}"
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
    -- Every shape at `Sort 0` has an arm: the fold for small elimination, arm
    -- F for the non-recursive subsingleton, and **arm G** — the graph route,
    -- [`Modelgen.graphArm`] — for the recursive one, which is what took `Acc`
    -- out of the basis. Nothing is declined here.
    pure ()

  -- ── arm G's shape, settled before anything is spliced ──
  -- A recursive subsingleton's fields are proofs and data that is *literally*
  -- one of the conclusion's indices. Which is which, and which index each data
  -- field is, is what the graph arm's `GraphInv` is stated by; a data field the
  -- index does not determine is `AccFromChoice.lean`'s one non-uniform case and
  -- is declined here rather than mis-emitted.
  let armG := (route matches PrimRoute.prop) && large && nc == 1 && isRec
  let mut gIsData : Array Bool := #[]
  let mut gIdxPos : Array Nat := #[]
  let mut gRecNb : Array (Option Nat) := #[]
  let mut gNf := 0
  if armG then
    for n in graphNames do taken n
    let (a, b, cc) ← forallBoundedTelescope memberTy (some np) fun ps _ => do
      let (cn, cty) := exportCtors[0]!
      let tele ← instForall cty ps
      let nfg := numForalls tele
      let flds ← classifyCtor tname nfg tele
      forallBoundedTelescope tele (some nfg) fun fs res => do
        let args := res.getAppArgs
        unless res.getAppFn.isConstOf tname && args.size == np + ni do
          badShape s!"{cn} does not end in {tname} at {np} parameters and {ni} indices"
        let idx := args.extract np args.size
        let mut isD : Array Bool := #[]
        let mut pos : Array Nat := #[]
        for i in [0:nfg] do
          if (← ilevel (← ityp fs[i]!)).normalize.isZero then
            isD := isD.push false
            pos := pos.push 0
          else
            let mut at? : Option Nat := none
            for k in [0:ni] do
              if idx[k]! == fs[i]! then at? := some k
            let some k := at?
              | badShape s!"{cn} has a data field the graph route cannot recover: it is \
not itself one of the conclusion's indices, so inversion would need the index's \
injectivity (AccFromChoice.lean's one non-uniform case)"
            isD := isD.push true
            pos := pos.push k
        for k in [0:ni] do
          unless (Array.range nfg).any (fun i => isD[i]! && pos[i]! == k) do
            badShape s!"{cn}'s index {k} is not one of its own data fields, so the \
graph route's inversion cannot be stated at an arbitrary index"
        return (isD, pos, flds.map (·.rec?))
    gIsData := a; gIdxPos := b; gRecNb := cc; gNf := a.size

  let (eqi, eqDecls) ← ensureEq reserved
  let mut out : Array Declaration := eqDecls
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)

  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps

  let ctorPairs := (Array.range nc).map fun j => (exportCtors[j]!.1, ctorN j)
  let tbl := modelTable (← getEnv) #[tname]
    { decls := #[], levelParams := lparams, members := #[], selfNames := #[selfN]
      numAll := 1, ctors := ctorPairs, recs := #[recN], iotas := #[], spliced := #[] }

  -- The indexed subsingleton has a different carrier from the Church routes —
  -- a packed index equation, not a fold — so it branches before them.
  -- **Any number of fields.** The arm used to decline above one, because at
  -- zero fields (`HEq`) and one (`TagS`) there is nothing to order and no
  -- fixture could catch a threading bug. `prim_shapes`'s `TagS2`, `TagS3` and
  -- `TagS4` are the two- and three-field occupants that were added to ask, and
  -- the sequential extraction below is correct at all three — kernel-accepted,
  -- statements compared, and red under the field-order mutations.
  let armF := (route matches PrimRoute.prop) && large && nc == 1 && ni > 0 && !isRec

  -- **Arm C**: an indexed family at a never-zero sort, carved out of its own
  -- index erasure. `MODELGEN.md` §8.15 and
  -- `scripts/inductive-basis/CarveOverSkeleton.lean`. Gated on the erasure being
  -- linear, because that is what decides whether the spliced skeleton will model
  -- — and a family whose skeleton does not model is a decline, never an
  -- emission.
  let armC := (route matches PrimRoute.type) && ni > 0 && erasureLinear

  -- ── the kit arm C needs: Church conjunction's two projections and its
  -- introduction, built here because [`Modelgen.andCOf`] gives the type only.
  let andCMk := fun (A B a b : Expr) => withLocalDeclD `D (.sort .zero) fun D => do
    withLocalDeclD `k (.forallE `a A (.forallE `b B D .default) .default) fun kk =>
      mkLambdaFVars #[D, kk] (mkAppN kk #[a, b])
  let andCFst := fun (A B p : Expr) => do
    let sel ← withLocalDeclD `a A fun a => withLocalDeclD `b B fun b =>
      mkLambdaFVars #[a, b] a
    pure (mkAppN p #[A, sel])
  let andCSnd := fun (A B p : Expr) => do
    let sel ← withLocalDeclD `a A fun a => withLocalDeclD `b B fun b =>
      mkLambdaFVars #[a, b] b
    pure (mkAppN p #[B, sel])

  if armF then
    -- ════ arm F: the indexed subsingleton, by one packed index equation ════
    --
    -- Shape (thesis.txt:700–710): one constructor, every field a `Prop` or a
    -- variable that literally *is* one of the output's indices. The kernel
    -- then grants a `Sort w` motive, and the model has to deliver it — the
    -- Church fold cannot, since it only eliminates into `Prop`.
    --
    -- Carrier: the constructor's `Prop` fields, Church-conjoined with **one**
    -- `Eq` at the whole index telescope packed into a `PSigma`
    -- ([`Modelgen.packTyOf`]) — the Henry-Ford equation, stated once because
    -- a later index's type may mention an earlier one:
    --
    --     T' p⃗ ι⃗ := ∀ r : Prop, (∀ f⃗, Eq Pk (pack ι⃗_ctor) (pack ι⃗) → r) → r
    --
    -- Recursor: extract the fields by small elimination (their target is a
    -- `Prop`, so no large eliminator for ∃/∧ is consumed), extract the
    -- equation the same way, and discharge the indices with a single
    -- `Eq.rec` whose motive rebuilds a carrier proof at each packed point.
    -- Every mismatch between the rebuilt proof and the caller's is closed by
    -- proof irrelevance, and `pack (unpack y) ≡ y` by structure eta is what
    -- makes the motive typecheck at all. ι is `Eq.refl`: at the constructor
    -- the stored equation *is* `Eq.refl`, and `Eq.rec`'s own ι rule fires.
    for d in ← ensurePSigma reserved do out := out.push d; spliced := spliced ++ d.getNames
    let (_, cty0) := exportCtors[0]!

    -- Everything below is built at a parameter scope and an index scope.
    let atScope := fun {α : Type} (k : Array Expr → Array Expr → Expr → Level → GenM α) =>
      withParams fun ps => do
        forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
          let (pk, ℓpk) ← packTyOf is 0
          k ps is pk ℓpk

    -- The constructor's own index expressions must be built from the
    -- parameters alone. An *index-variable field* — a fresh variable that is
    -- literally one of the output's indices — is admitted by the
    -- subsingleton rule but is not handled here; Lean's front end promotes
    -- such a field to a parameter whenever it can, so it is rare.
    let ctorIdxAt := fun (ps : Array Expr) => do
      let tele ← instForall cty0 ps
      let nf := numForalls tele
      forallBoundedTelescope tele (some nf) fun fs res => do
        let args := res.getAppArgs
        unless res.getAppFn.isConstOf tname && args.size == np + ni do
          badShape s!"{exportCtors[0]!.1} does not end in {tname} at {np} parameters \
and {ni} indices"
        let idx := args.extract np args.size
        for e in idx do
          if fs.any (fun f => e.containsFVar f.fvarId!) then
            badShape s!"{exportCtors[0]!.1} has an index-variable field: its index \
expressions mention its own fields, which the packed-equation model substitutes only \
when the front end has already promoted them to parameters"
        for f in fs do
          unless (← ilevel (← ityp f)).normalize.isZero do
            badShape s!"{exportCtors[0]!.1} has a field that is not a proposition, so \
the subsingleton rule that minted {ern} does not hold of it"
        pure idx

    -- `∀ f⃗, Eq Pk (pack ι⃗_ctor) (pack ι⃗) → r`, the encoding's one minor.
    let minorTyAt := fun (ps is : Array Expr) (pk : Expr) (ℓpk : Level) (r : Expr) => do
      let tele ← instForall cty0 ps
      let nf := numForalls tele
      let idx ← ctorIdxAt ps
      let lhs ← packChain ni pk idx 0
      let rhs ← packChain ni pk is 0
      forallBoundedTelescope tele (some nf) fun fs _ => do
        mkForallFVars fs (.forallE `heq (eqi.mk' ℓpk pk lhs rhs) r .default)

    let carrierAt := fun (ps is : Array Expr) (pk : Expr) (ℓpk : Level) =>
      withLocalDeclD `r (.sort .zero) fun r => do
        mkForallFVars #[r] (.forallE `k (← minorTyAt ps is pk ℓpk r) r .default)

    -- ── the carrier ──
    let selfVal ← atScope fun ps is pk ℓpk => do
      mkLambdaFVars (ps ++ is) (← carrierAt ps is pk ℓpk)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := memberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructor ──
    let ty := restore tbl cty0
    let cval ← withParams fun ps => do
      let rtele ← instForall ty ps
      let nf := numForalls rtele
      forallBoundedTelescope rtele (some nf) fun fs _ => do
        forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
          let (pk, ℓpk) ← packTyOf is 0
          let idx ← ctorIdxAt ps
          let pkc ← packChain ni pk idx 0
          let body ← withLocalDeclD `r (.sort .zero) fun r => do
            withLocalDeclD `k (← minorTyAt ps idx pk ℓpk r) fun kk =>
              mkLambdaFVars #[r, kk] (mkAppN kk (fs.push (eqi.refl' ℓpk pk pkc)))
          mkLambdaFVars (ps ++ fs) body
    let dCtor := Declaration.defnDecl
      { name := ctorN 0, levelParams := lparams, type := ty, value := cval
        hints := ← hintsFor cval, safety := .safe }
    addChecked dCtor
    out := out.push dCtor

    -- ── the recursor ──
    let recTy := restore tbl rv.type
    let recVal ← forallBoundedTelescope recTy (some (np + 1 + nc + ni + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minor := bs[np + 1]!
      let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
      let t := bs[bs.size - 1]!
      forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
        let (pkT, ℓpk) ← packTyOf is 0
        let pk := pkT.replaceFVars is idxs
        let idx ← ctorIdxAt ps
        let pkc ← packChain ni pk idx 0
        let tele ← instForall cty0 ps
        let nf := numForalls tele
        -- extract the fields, sequentially: a later field's type is
        -- instantiated at the earlier extractions.
        let eqTy := eqi.mk' ℓpk pk pkc (← packChain ni pk idxs 0)
        let mut es : Array Expr := #[]
        let mut curT := tele
        for _ in [0:nf] do
          let .forallE _ ft rest _ := curT | badShape "telescope shorter than its field count"
          let i := es.size
          let proj ← forallBoundedTelescope tele (some nf) fun fs _ => do
            withLocalDeclD `h eqTy fun h => mkLambdaFVars (fs.push h) fs[i]!
          es := es.push (mkAppN t #[ft, proj])
          curT := rest.instantiate1 es[i]!
        -- and the equation
        let eqProj ← forallBoundedTelescope tele (some nf) fun fs _ =>
          withLocalDeclD `h eqTy fun h => mkLambdaFVars (fs.push h) h
        let heq := mkAppN t #[eqTy, eqProj]
        -- one `Eq.rec` at the packed point: the motive rebuilds a carrier
        -- proof at each `y`, and `pack (unpack y) ≡ y` makes it typecheck.
        let fam := fun (y : Expr) (h : Expr) => do
          let ys ← unpackChain ni pk y
          let rebuilt ← withLocalDeclD `r (.sort .zero) fun r => do
            withLocalDeclD `k (← minorTyAt ps ys pk ℓpk r) fun kk =>
              mkLambdaFVars #[r, kk] (mkAppN kk (es.push h))
          pure (mkAppN motive (ys.push rebuilt))
        let motiveE ← withLocalDeclD `y pk fun y => do
          withLocalDeclD `hy (eqi.mk' ℓpk pk pkc y) fun hy => do
            mkLambdaFVars #[y, hy] (← fam y hy)
        let pki ← packChain ni pk idxs 0
        mkLambdaFVars bs (eqi.recAt v ℓpk pk pkc motiveE (mkAppN minor es) pki heq)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else if armC then
    -- ════ arm C: an indexed family, carved out of its spliced erasure ════
    --
    -- Thesis §5.2's skeleton-plus-`good`, but standing on a **real inductive**
    -- rather than on a W-type. `MODELGEN.md` §8.10's rule is what picks the
    -- shape: the thing the carve needs underneath it is a non-indexed
    -- inductive with the same constructor telescopes, and that is a
    -- declaration we can *splice* — so we splice it, the kernel mints its
    -- recursor, and everything below is written against the genuine article
    -- with its definitional ι. §8.13's splice-and-model then models it like
    -- any other spliced inductive, and `Iso.requires` withdraws the whole
    -- model if it cannot.
    --
    --     skel p⃗           := T with its indices erased  (spliced inductive)
    --     good p⃗ s y       := skel.rec … — `Eq Pk e⃗_j y`, conjoined with the
    --                         child's own goodness at its own index
    --     T._model.self p⃗ ι⃗ := Σ'(s : skel p⃗), good p⃗ s (pack ι⃗)
    --
    -- What this buys over carving out of W, all of it measured in
    -- `CarveOverSkeleton.lean`: **no per-constructor currying glue** (a
    -- spliced skeleton keeps the field telescope, so the minor `skel.rec`
    -- wants is the minor `T.rec` wants — no `B a ≅ Fin k` iso, no eta lemma,
    -- no `funext`), **ι by `Eq.refl`** (the shared block below proves every
    -- rule that way, unchanged), and **no axioms at all**.
    --
    -- Three reductions carry the ι rules and each is load-bearing:
    -- definitional proof irrelevance (`⟨s, h⟩ ≡ ⟨s, h'⟩`, so the carved
    -- component never obstructs), the skeleton's own ι, and `PSigma`'s
    -- structure eta (`⟨t.1, t.2⟩ ≡ t`, and `unpack (pack ι⃗) ≡ ι⃗`).
    unless large do
      badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
    for n in [skelN, goodN] do taken n
    for j in [0:nc] do taken (skelCtorN j)
    for d in ← ensurePSigma reserved do out := out.push d; spliced := spliced ++ d.getNames

    let skelSelf := fun (ps : Array Expr) => mkAppN (.const skelN us) ps
    -- The index telescope packed into one `PSigma` ([`Modelgen.packTyOf`]),
    -- at a parameter scope. Closed over the telescope, so it depends on `ps`
    -- alone.
    let pkAt := fun (ps : Array Expr) => do
      forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => packTyOf is 0
    -- `fun s => good p⃗ s y` — the carve's predicate as `PSigma`'s `β`.
    let βOf := fun (ps : Array Expr) (y : Expr) =>
      withLocalDeclD `s (skelSelf ps) fun s =>
        mkLambdaFVars #[s] (mkAppN (.const goodN us) (ps ++ #[s, y]))

    -- ── the skeleton, spliced ──
    -- Each constructor keeps its field telescope; only the recursive field's
    -- type and the codomain lose their indices. [`Modelgen.spineSwap`] does
    -- the first and is the tuple tower's own swap, which is the same swap
    -- because `erasureLinear` has already said the recursive occurrence is a
    -- bare `T p⃗ e⃗`.
    let skelDecl : Declaration :=
      .inductDecl lparams np
        [{ name := skelN, type := eraseSelfTy np w memberTy,
           ctors := (List.range nc).map fun j =>
             { name := skelCtorN j,
               type := eraseCtorTy tname skelN us np exportCtors[j]!.2 } }] false
    addChecked skelDecl
    out := out.push skelDecl
    spliced := spliced.push skelN

    let skelRecN := Name.str skelN "rec"
    let some (.recInfo srv) := (← getEnv).find? skelRecN
      | badShape s!"the kernel minted no recursor for the spliced {skelN}"
    unless srv.levelParams.length == lparams.length + 1 do
      badShape s!"{skelRecN} is not large-eliminating, so the carve cannot state \
        a recursor at an arbitrary motive"
    let skelRec := fun (m : Level) (ps : Array Expr) (mot : Expr)
        (minors : Array Expr) (t : Expr) =>
      mkAppN (.const skelRecN (m :: us)) (ps ++ #[mot] ++ minors ++ #[t])

    -- Constructor `j`'s **index expressions** and its recursive slot's
    -- **child indices**, read off the export's own telescope and re-expressed at
    -- whatever field vector the caller has opened — the erased one when building
    -- `good`, the restored one when building the constructor. The substitution
    -- is sound because an index expression can only mention parameters and
    -- *non-recursive* fields: there is no way to compute an index out of a
    -- recursive field before the type exists.
    let ctorIdxAt := fun (ps gs : Array Expr) (j : Nat) => do
      let (cn, cty) := exportCtors[j]!
      let tele ← instForall cty ps
      let nf := numForalls tele
      forallBoundedTelescope tele (some nf) fun fs res => do
        let args := res.getAppArgs
        unless res.getAppFn.isConstOf tname && args.size == np + ni do
          badShape s!"{cn} does not end in {tname} at {np} parameters and {ni} indices"
        let idx := (args.extract np args.size).map (·.replaceFVars fs gs)
        let mut slot? : Option (Nat × Array Expr) := none
        for i in [0:nf] do
          let ft ← ityp fs[i]!
          if mentionsAny #[tname] ft then
            let fargs := ft.getAppArgs
            unless ft.getAppFn.isConstOf tname && fargs.size == np + ni do
              badShape s!"{cn}'s recursive field is not {tname} at {np} parameters \
                and {ni} indices"
            slot? := some (i, (fargs.extract np fargs.size).map (·.replaceFVars fs gs))
        pure (idx, slot?)

    -- ── `good`, by the skeleton's own recursor ──
    -- The motive is `fun _ => Pk → Prop`, which is a `Prop`, so this uses only
    -- the skeleton's **small** elimination. The large one is spent once, on
    -- the recursor below.
    let goodTy ← withParams fun ps => do
      let (pk, _) ← pkAt ps
      withLocalDeclD `s (skelSelf ps) fun s => withLocalDeclD `y pk fun y =>
        mkForallFVars (ps ++ #[s, y]) (.sort .zero)
    let goodVal ← withParams fun ps => do
      let (pk, ℓpk) ← pkAt ps
      let predTy := Expr.forallE `y pk (.sort .zero) .default
      let mot ← withLocalDeclD `s (skelSelf ps) fun s => mkLambdaFVars #[s] predTy
      let minors ← (Array.range nc).mapM fun j => do
        let tele ← instForall exportCtors[j]!.2 ps
        let nf := numForalls tele
        let swapped ← spineSwap tname (skelSelf ps) nf tele
        forallBoundedTelescope swapped (some nf) fun gs _ => do
          let (idx, slot?) ← ctorIdxAt ps gs j
          let pkc ← packChain ni pk idx 0
          match slot? with
          | none =>
            let body ← withLocalDeclD `y pk fun y =>
              mkLambdaFVars #[y] (eqi.mk' ℓpk pk pkc y)
            mkLambdaFVars gs body
          | some (_, chi) =>
            let pkchi ← packChain ni pk chi 0
            withLocalDeclD `ih predTy fun ih => do
              let body ← withLocalDeclD `y pk fun y =>
                mkLambdaFVars #[y] (andCOf (eqi.mk' ℓpk pk pkc y) (mkApp ih pkchi))
              mkLambdaFVars (gs.push ih) body
      -- **The motive's universe is `imax ℓpk 1`, not `0`.** `Pk → Prop` is a
      -- *predicate type*, and its codomain is the type `Prop`, which lives in
      -- `Sort 1` — so the fold is a `Sort 1`-valued elimination and not a
      -- propositional one. Asked of the expression rather than assumed: the
      -- first attempt passed `0` and the kernel said `skel α → Type`.
      let mGood ← ilevel predTy
      withLocalDeclD `s (skelSelf ps) fun s => withLocalDeclD `y pk fun y =>
        mkLambdaFVars (ps ++ #[s, y]) (mkApp (skelRec mGood ps mot minors s) y)
    let dGood := Declaration.defnDecl
      { name := goodN, levelParams := lparams, type := goodTy, value := goodVal
        hints := ← hintsFor goodVal, safety := .safe }
    addChecked dGood
    out := out.push dGood

    -- ── the carrier ──
    let selfVal ← withParams fun ps => do
      let (pk, _) ← pkAt ps
      forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
        let β ← βOf ps (← packChain ni pk is 0)
        mkLambdaFVars (ps ++ is) (psigmaT w .zero (skelSelf ps) β)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := memberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructors ──
    for j in [0:nc] do
      let ty := restore tbl exportCtors[j]!.2
      let val ← withParams fun ps => do
        let (pk, ℓpk) ← pkAt ps
        let rtele ← instForall ty ps
        let nf := numForalls rtele
        forallBoundedTelescope rtele (some nf) fun fs _ => do
          let (idx, slot?) ← ctorIdxAt ps fs j
          let pkc ← packChain ni pk idx 0
          let mut gs := fs
          let mut proof := eqi.refl' ℓpk pk pkc
          if let some (k, chi) := slot? then
            let pkchi ← packChain ni pk chi 0
            let βchi ← βOf ps pkchi
            let sk := psigmaFst w .zero (skelSelf ps) βchi fs[k]!
            let sn := psigmaSnd w .zero (skelSelf ps) βchi fs[k]!
            gs := gs.set! k sk
            proof ← andCMk (eqi.mk' ℓpk pk pkc pkc)
              (mkAppN (.const goodN us) (ps ++ #[sk, pkchi])) proof sn
          let β ← βOf ps pkc
          mkLambdaFVars (ps ++ fs)
            (psigmaMk w .zero (skelSelf ps) β
              (mkAppN (.const (skelCtorN j) us) (ps ++ gs)) proof)
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── the recursor ──
    -- One `skel.rec` at the motive `fun s => ∀ y h, C (unpack y) ⟨s, h⟩`, and
    -- one `Eq.rec` per constructor to move the conclusion from the
    -- constructor's own index to the caller's. The index equation is the
    -- first component of the `good` proof the major already carries, so
    -- nothing per-constructor is *proved* here — it is extracted.
    let recTy := restore tbl rv.type
    let recVal ← forallBoundedTelescope recTy (some (np + 1 + nc + ni + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minors := bs.extract (np + 1) (np + 1 + nc)
      let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
      let t := bs[bs.size - 1]!
      let (pk, ℓpk) ← pkAt ps
      -- `∀ (y : Pk) (h : good p⃗ s y), motive (unpack y) ⟨s, h⟩` at a given
      -- skeleton element — the skeleton recursor's motive, and the type of the
      -- induction hypothesis at a recursive field.
      let atSkel := fun (s : Expr) => withLocalDeclD `y pk fun y => do
        let βy ← βOf ps y
        withLocalDeclD `h (mkAppN (.const goodN us) (ps ++ #[s, y])) fun h => do
          let ys ← unpackChain ni pk y
          mkForallFVars #[y, h]
            (mkAppN motive (ys.push (psigmaMk w .zero (skelSelf ps) βy s h)))
      let (sMotive, m) ← withLocalDeclD `s (skelSelf ps) fun s => do
        let inner ← atSkel s
        pure (← mkLambdaFVars #[s] inner, ← ilevel inner)
      let sMinors ← (Array.range nc).mapM fun j => do
        let tele ← instForall exportCtors[j]!.2 ps
        let nf := numForalls tele
        let swapped ← spineSwap tname (skelSelf ps) nf tele
        forallBoundedTelescope swapped (some nf) fun gs _ => do
          let (idx, slot?) ← ctorIdxAt ps gs j
          let pkc ← packChain ni pk idx 0
          let head := mkAppN (.const (skelCtorN j) us) (ps ++ gs)
          -- `B` is the second conjunct of `good p⃗ head y`, absent when the
          -- constructor has no recursive field.
          let bOf : GenM (Option (Expr × Expr × Array Expr)) :=
            match slot? with
            | none => pure none
            | some (k, chi) => do
              let pkchi ← packChain ni pk chi 0
              pure (some (mkAppN (.const goodN us) (ps ++ #[gs[k]!, pkchi]), pkchi, chi))
          let b? ← bOf
          let body := fun (ih? : Option Expr) => withLocalDeclD `y pk fun y => do
            let aTy := eqi.mk' ℓpk pk pkc y
            withLocalDeclD `h (mkAppN (.const goodN us) (ps ++ #[head, y])) fun h => do
              let (he, hc?) ← match b? with
                | none => pure (h, none)
                | some (bTy, _, _) => do
                  pure (← andCFst aTy bTy h, some (← andCSnd aTy bTy h))
              -- the motive of the index transport: rebuild the carve proof at
              -- each point, which proof irrelevance then identifies with `h`.
              let motiveE ← withLocalDeclD `y2 pk fun y2 => do
                withLocalDeclD `hh (eqi.mk' ℓpk pk pkc y2) fun hh => do
                  let β2 ← βOf ps y2
                  let reb ← match b?, hc? with
                    | some (bTy, _, _), some hc =>
                      andCMk (eqi.mk' ℓpk pk pkc y2) bTy hh hc
                    | _, _ => pure hh
                  let ys ← unpackChain ni pk y2
                  mkLambdaFVars #[y2, hh]
                    (mkAppN motive (ys.push (psigmaMk w .zero (skelSelf ps) β2 head reb)))
              -- the minor premise, at the carrier's own fields
              let mut args := gs
              let mut extra : Array Expr := #[]
              if let (some (k, _), some (bTy, pkchi, _), some hc, some ih) :=
                  (slot?, b?, hc?, ih?) then
                let βchi ← βOf ps pkchi
                let _ := bTy
                args := args.set! k (psigmaMk w .zero (skelSelf ps) βchi gs[k]! hc)
                extra := #[mkAppN ih #[pkchi, hc]]
              let base := mkAppN minors[j]! (args ++ extra)
              mkLambdaFVars #[y, h] (eqi.recAt v ℓpk pk pkc motiveE base y he)
          match slot? with
          | none => mkLambdaFVars gs (← body none)
          | some (k, _) =>
            withLocalDeclD `ih (← atSkel gs[k]!) fun ih => do
              mkLambdaFVars (gs.push ih) (← body (some ih))
      let pki ← packChain ni pk idxs 0
      let βi ← βOf ps pki
      let t1 := psigmaFst w .zero (skelSelf ps) βi t
      let t2 := psigmaSnd w .zero (skelSelf ps) βi t
      mkLambdaFVars bs (mkAppN (skelRec m ps sMotive sMinors t1) #[pki, t2])
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else if route matches PrimRoute.type then
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
        recSlotOf tname np cn (numForalls tele) tele (tagFactored tname np exportCtors)
    let baseJ := (Array.range nc).filter fun j => slots[j]!.isNone
    let stepJ := (Array.range nc).filter fun j => slots[j]!.isSome
    -- **A recursive declaration with no base constructor**, which Lean accepts
    -- and which is uninhabited. The spine tower cannot express it: spine 0 is
    -- the tower over the *base* constructors, and with none there is no fibre
    -- for [`Modelgen.stepTower`] to destruct at — it would read `cs[0]` of an
    -- empty array. It reached that read before this guard existed, and the
    -- resulting non-fatal `panic!` returned a default `PCtor` whose chain has
    -- no fields, so the declaration declined with "a chain with no fields
    -- needs a pad" — a true refusal reached by an out-of-bounds read, and a
    -- reason that named nothing. Nothing in the corpus has this shape, which
    -- is why it went unseen; `tests/prim_carve.lean`'s `NoBase` is the
    -- occupant that found it, through arm C's skeleton.
    if isRec && baseJ.isEmpty then
      badShape s!"{tname} is recursive with no base constructor, so it is uninhabited \
        and the tuple tower has no spine-zero fibre to build"
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

    -- **Arm G's prelude, asked for before anything is emitted.** The graph
    -- route pairs a value with its graph proof (`PSigma`) and extracts it with
    -- `Classical.choice`, whose own domain is `Nonempty`; and `Graph.unique`
    -- transports along a `funext` — but only when a recursive field has a
    -- binder, because [`Modelgen.funextUp`] is the only caller and it is the
    -- identity at none. That is the whole of why the axiom cost is per shape.
    let mut gFx? : Option Name := none
    if armG then
      for d in ← ensurePSigma reserved do out := out.push d; spliced := spliced ++ d.getNames
      for d in ← ensureNonempty reserved do out := out.push d; spliced := spliced ++ d.getNames
      for d in ← ensureChoice reserved do out := out.push d; spliced := spliced ++ d.getNames
      if (Array.range gNf).any (fun i => (gRecNb[i]!.getD 0) > 0) then
        let (fxN, fxDecls) ← ensureFunext model eqi reserved
        for d in fxDecls do out := out.push d; spliced := spliced ++ d.getNames
        gFx? := some fxN

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
    -- **One fold, two consumers.** Arm G's `ind` — the free `Prop`-motive
    -- recursor the graph route folds at — *is* the strong-induction fold
    -- below at `v := 0`, so the arm forces the small-elimination branches and
    -- takes the result as `ind` instead of as `rec_0`. Building it a second
    -- time by hand would be a second thing to keep in step.
    let indTy :=
      if armG then recTy.instantiateLevelParams [rv.levelParams[0]!] [.zero] else recTy
    let large := large && !armG
    let recVal ← forallBoundedTelescope indTy (some (np + 1 + nc + ni + 1)) fun bs _ => do
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
    if armG then
      -- ════ arm G: the recursive subsingleton, by the graph ════
      -- The carrier and the constructor above are already the graph route's
      -- own — `CAcc` and `CAcc.intro` cost no primitive whatsoever — and so is
      -- the `Prop`-motive recursor just built. What is emitted here is the
      -- large eliminator the kernel granted the *declaration* and an emitted
      -- `def` does not inherit.
      let dInd := Declaration.thmDecl
        { name := indN, levelParams := lparams, type := indTy, value := recVal }
      addChecked dInd
      out := out.push dInd
      let ctx : GraphCtx :=
        { tname, np, ni, nf := gNf, us, recLs, lparams, recLevels := rv.levelParams, v
          selfN, ctorN0 := ctorN 0, recN, indN
          grN := Name.str model "graph", grMkN := Name.str model "graph_mk"
          grInvTN := Name.str model "graph_inv_ty", grInvN := Name.str model "graph_inv"
          grUniqN := Name.str model "graph_unique", grExN := Name.str model "graph_exists"
          recGrN := Name.str model "rec_graph"
          memberTy, ctorTy := restore tbl exportCtors[0]!.2
          isData := gIsData, idxPos := gIdxPos, recNb := gRecNb, eqi, fx? := gFx? }
      for d in ← graphArm ctx recTy do out := out.push d
    else
      let dRec := Declaration.defnDecl
        { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
          hints := ← hintsFor recVal, safety := .safe }
      addChecked dRec
      out := out.push dRec

  -- ── the ι rules ──
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
        -- **Every ι theorem is `Eq.refl` except arm G's.** There the value is
        -- a `Classical.choice` application, which reduces to nothing, so the
        -- rule is proved instead: both sides are graph points at this
        -- constructor and the graph is single-valued. The *statement* is the
        -- shared one above either way, which is what keeps the oracle's
        -- syntactic comparison honest across the arms.
        let proof ←
          if !armG then pure (eqi.refl' v α lhs) else do
            let rsI := (Array.range gNf).filter fun i => gRecNb[i]!.isSome
            let atSlot := fun (nm : Name) => rsI.mapM fun i => do
              let fty ← ityp fields[i]!
              forallBoundedTelescope fty (some (gRecNb[i]!.getD 0)) fun zs r2 => do
                let a2 := r2.getAppArgs
                mkLambdaFVars zs (mkAppN (.const nm recLs)
                  (pre ++ a2.extract np a2.size ++ #[mkAppN fields[i]! zs]))
            let ghat ← atSlot recN
            let hhat ← atSlot (Name.str model "rec_graph")
            let gv := mkAppN (.const (Name.str model "rec_graph") recLs)
              (pre ++ isj ++ #[major])
            let gw := mkAppN (.const (Name.str model "graph_mk") recLs)
              (pre ++ fields ++ ghat ++ hhat)
            pure (mkAppN (.const (Name.str model "graph_unique") recLs)
              (pre ++ isj ++ #[major, lhs, rhs, gv, gw]))
        return Declaration.thmDecl
          { name := iotaN j, levelParams := rv.levelParams
            type := ← mkForallFVars tel (eqi.mk' v α lhs rhs)
            value := ← mkLambdaFVars tel proof }
    addChecked d
    out := out.push d
    iotas := iotas.push (0, cn, iotaN j)

  return { decls := out, levelParams := lparams, members := #[], selfNames := #[selfN]
           numAll := 1, ctors := ctorPairs, recs := #[recN], iotas, spliced
           requires := if armC then #[skelN] else #[]
           emitAs? := if root == tname then none else some (root, tname) }

end Modelgen
