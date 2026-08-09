import Modelgen.Mutual

/-!
# The model of a **simple inductive from five primitives**, generated

The third construction in this package, behind `--prim-models` and off by
default. Where the first two constructions remove *nesting* and *mutuality*,
this one removes the inductive declaration itself: a plain (non-mutual,
non-nested, non-indexed, non-recursive) inductive's carrier, constructors,
recursor and ι rules are emitted as ordinary `def`s and `theorem`s over a
fixed basis of primitive inductives —

    Eq   False   PSigma   Nat   Acc

— each spliced into the output at Lean's own shape if the input lacks it,
exactly as the existing prelude splice does for `Eq`, the quotient and
`funext`. A consumer that recognises the four interface names then needs to
implement only the five primitives (plus `Quot`), not general inductives.

The commission named the basis `{Eq, False, Sigma, Acc, Nat}`. Verified
rather than inherited (`scripts/prim-basis/Derivations.lean`, compiled at
the pinned toolchain): the Σ must be **`PSigma`-shaped** — `{α : Sort u} →
(α → Sort v) → Sort (max 1 u v)` — because `Subtype`, structures with
`Prop` fields, and every `Prop`-fibred pair in the constructions below need
a Σ over `Sort`, which a `Type`-only `Sigma` cannot give without `PLift`, a
sixth inductive. `Acc` is in the basis for the recursive construction
(plan B, not implemented here) and is therefore not yet spliced: the
prelude splice's rule is "only what a model actually needs".

## The three routes

**Type route** — carrier sort `w` never zero:

```text
T._model.self p⃗ := Σ'(n : Nat), F n        F : a Nat.rec cases tower
F ȷ̄  := the j-th constructor's field chain  (right-nested PSigma,
        boxed and padded to exactly Sort w when the levels demand it)
F n  := an empty type at Sort w for n ≥ #ctors  (Σ'(h : False), False.rec h)
```

The recursor destructs the pair, cases on the tag with `Nat.rec` — the
large elimination the basis buys, and the reason `Nat` is in it — and then
destructs the chain. Two level repairs keep the chain at exactly `Sort w`:

* **A pad** closes a level gap. At a `dsingOk` level the pad is `D`
  ([`Modelgen.dsingAt`]), every element *defeq* to canonical — no
  transport. At any other level — a bare parameter in the gap, `PULift`'s
  shape — it is the `False`-Π singleton `(h : False) → False.rec (fun _ =>
  Sort ℓ) h`, at exactly `Sort ℓ` because `imax 0 ℓ = ℓ`; its uniqueness is
  `funext` at a pointwise `False.rec`, the destructor transports along it,
  and on a constructor application the transport sits on a closed
  self-equality that K-like reduction on `Eq.rec` erases.
* **A box** ([`Modelgen.boxTyOf`]) absorbs an `imax`: a Π-typed field's
  level is an `imax` chain (`Trans.mk`'s shape) and no pad subsumes an
  `imax` under a `max` — what collapses it is a never-`Prop` codomain, so
  the field is stored with its codomain wrapped as `Σ'(_ : S), D 1` and
  unboxed by projection wherever the minor consumes it; `unbox (box v) ≡ v`
  by βι, structure eta, proof irrelevance and function eta, no transport.

**Every ι theorem is `Eq.refl`** on all routes.

**Prop route** — carrier sort `0`: the impredicative Church encoding
`∀ C : Prop, (∀ f⃗₀, C) → … → C`. At a `Prop` motive the dependent recursor
is the fold itself — the motive's proof argument is definitionally
irrelevant. When the export's recursor is large-eliminating the
subsingleton rule holds, so (non-indexed) every field is a proposition and
is **extracted** by instantiating the encoding at the field's own type;
proof irrelevance closes the motive.

**Singleton route** — carrier at a *variable* sort (`Prop` at some
instantiations, `Type` at others: `PUnit : Sort u`). The basis reaches such
a sort exactly once: the `False`-Π singleton above, which is a type at any
`Sort w` and is inhabited. So a one-constructor, no-field declaration
models with it as carrier, the canonical element as constructor, and the
recursor a transport along the singleton's uniqueness — erased on the
constructor by K-like reduction, so ι is `Eq.refl` here too.

## What declines, and why

* **recursive** (`List`, `Lean.Name`, …) — the carrier needs the W/path
  construction (plan B). Not implemented; the reason is printed.
* **indexed** (`HEq`, `Nat.le`, the composed `T._model.aux`) — the
  skeleton-plus-`good` translation (thesis §5.2) is not implemented.
* **an empty carrier at a variable sort** (`PEmpty : Sort u`) — not
  constructible over the basis: every basis former lands at `0`, `1` or
  `max 1 ·`, a Π reaches a bare `u` only through an `imax` collapse whose
  body is already at `Sort u`, and the one `Sort u`-valued family with no
  `Sort u` seed is `False.rec`'s over the empty domain — whose Π is
  *inhabited*. A model of `PEmpty.rec` would be a closed term that, at
  `motive := fun _ => False`, proves `False`.
* **a variable-sort carrier that is not the singleton** (several
  constructors, or fields) — the singleton is the fragment's only type at
  such a sort.
* **a level gap no pad or box closes** — an `imax` in a field's level that
  boxing does not collapse (an `imax`-leveled *domain* inside the field).
* the five **basis primitives themselves** — the exemption that makes the
  construction well-founded.
-/

open Lean Meta

namespace Modelgen

/-- The five, by name. A declaration in this set is the basis and is not
modelled — the exemption that makes the construction well-founded. -/
def primBasis : List Name := [`Eq, `False, `PSigma, `Nat, `Acc]

/-- **Lean's `False`**: `inductive False : Prop`, no constructors. -/
def falseDecl : Declaration :=
  .inductDecl [] 0 [{ name := `False, type := .sort .zero, ctors := [] }] false

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

def checkFalse (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `False | throw "it is not an inductive type"
  unless iv.numParams == 0 && iv.numIndices == 0 && iv.ctors.isEmpty do
    throw s!"it has {iv.numParams} parameters, {iv.numIndices} indices and \
      {iv.ctors.length} constructors, where Lean's has 0, 0 and 0"
  unless iv.type == Expr.sort .zero do throw "it does not land in Prop"

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

def ensureFalse (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `False [`False] falseDecl checkFalse reserved
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

def natRec (s : Level) (motive z sc t : Expr) : Expr :=
  mkAppN (.const `Nat.rec [s]) #[motive, z, sc, t]

def falseRec (v : Level) (motive h : Expr) : Expr :=
  mkAppN (.const `False.rec [v]) #[motive, h]

/-- The fibre of [`Modelgen.emptyAt`]: `fun (h : False) => False.rec
(fun _ => Sort w) h`. -/
def emptyAtFibre (w : Level) : Expr :=
  .lam `h (.const `False [])
    (falseRec (.succ w) (.lam `x (.const `False []) (.sort w) .default) (.bvar 0)) .default

/-- An empty type at exactly `Sort w`, `w` never zero:
`Σ'(h : False), False.rec (fun _ => Sort w) h` is at `Sort (max 1 0 w)`. -/
def emptyAt (w : Level) : Expr :=
  psigmaT .zero w (.const `False []) (emptyAtFibre w)

/-- `False` out of an inhabitant of [`Modelgen.emptyAt`], by projection. -/
def emptyAtFst (w : Level) (e : Expr) : Expr :=
  let fls : Expr := .const `False []
  let motive : Expr := .lam `t (emptyAt w) fls .default
  let m : Expr := .lam `h fls
    (.lam `s (Expr.app (emptyAtFibre w) (.bvar 0)).headBeta (.bvar 1) .default) .default
  psigmaRec .zero .zero w fls (emptyAtFibre w) motive m e

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

/-! ## The singleton at an arbitrary level

`Sort ℓ` for a **bare or variable** `ℓ` is out of every basis former's reach —
`Eq`, `False` and `Acc` land in `Prop`, `Nat` in `Type`, `PSigma` at
`max 1 u v` — and a Π lands there only through an `imax` collapse, which needs
a `Sort ℓ`-valued *body*. The one such family the basis builds without a
`Sort ℓ` seed is `False.rec (fun _ => Sort ℓ)`, over the empty domain; its Π
`(h : False) → False.rec (fun _ => Sort ℓ) h` sits at `imax 0 ℓ = ℓ` exactly,
for **any** `ℓ` whatsoever. A function out of `False` is inhabited, so this is
a singleton — and it is the *only* carrier shape the fragment has at such a
sort, which is why `PUnit` models and `PEmpty` (below) cannot.

Unlike [`Modelgen.dsingAt`]'s pads it is **not definitionally canonical**: two
inhabitants are `funext`-equal, not defeq. So wherever one is destructed the
applied minor is transported along [`Modelgen.falsePiUniq`], and on a
constructor application that proof is a *closed self-equality* which the
kernel's K-like reduction on `Eq.rec` erases — ι stays `Eq.refl`. -/

/-- `False.rec (fun _ => Sort ℓ) h`. -/
def sortFamOverFalse (ℓ : Level) (h : Expr) : Expr :=
  falseRec (.succ ℓ) (.lam `x (.const `False []) (.sort ℓ) .default) h

/-- The singleton at exactly `Sort ℓ`: `(h : False) → False.rec (fun _ =>
Sort ℓ) h`, at `imax 0 ℓ = ℓ` because the domain is a proposition. -/
def falsePiAt (ℓ : Level) : Expr :=
  .forallE `h (.const `False []) (sortFamOverFalse ℓ (.bvar 0)) .default

/-- Its canonical element, by a second `False.rec` at the dependent motive. -/
def falsePiCanon (ℓ : Level) : Expr :=
  .lam `h (.const `False [])
    (falseRec ℓ (.lam `h' (.const `False []) (sortFamOverFalse ℓ (.bvar 0)) .default) (.bvar 0))
    .default

/-- `Eq f t` for `f, t : falsePiAt ℓ` — `funext` at the pointwise proof
`fun h => False.rec _ h`. `f` is always the canonical element (possibly under
a definition's name), so on a constructor application this is a neutral proof
of a closed self-equality and K-like reduction erases the transport built on
it. -/
def falsePiUniq (eqi : EqInfo) (fx : Name) (ℓ : Level) (f t : Expr) : Expr :=
  let fls : Expr := .const `False []
  let fam := Expr.lam `h fls (sortFamOverFalse ℓ (.bvar 0)) .default
  let pointwise := Expr.lam `h fls
    (falseRec .zero
      (.lam `h' fls
        (eqi.mk' ℓ (sortFamOverFalse ℓ (.bvar 0)) (.app f (.bvar 0)) (.app t (.bvar 0)))
        .default)
      (.bvar 0)) .default
  mkAppN (.const fx [.zero, ℓ]) #[fls, fam, f, t, pointwise]

/-- The always-true proposition `∀ C : Prop, C → C`, and its inhabitant.
Pure Π — it consumes no primitive at all. -/
def trueP : Expr :=
  .forallE `C (.sort .zero) (.forallE `c (.bvar 0) (.bvar 1) .default) .default
def trueI : Expr :=
  .lam `C (.sort .zero) (.lam `c (.bvar 0) (.bvar 0) .default) .default

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
`PULift`'s shape), the [`Modelgen.falsePiAt`] singleton, whose uniqueness is
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
canonical element. A [`Modelgen.falsePiAt`] pad is discharged by transporting
the applied minor along [`Modelgen.falsePiUniq`], and on a constructor
application that proof is a closed self-equality which K-like reduction on
`Eq.rec` erases — ι stays `Eq.refl` on both. -/
partial def chainDestruct (v : Level) (eqi : EqInfo) (fx? : Option Name)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr) (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (vals : Array Expr := #[]) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    if p.canonical then
      -- `scrut` is defeq to the pad's canonical element, so the applied minor
      -- already has the target type.
      return minorAt vals
    -- The plan ensured `funext` before planning a non-canonical pad.
    let some fx := fx? | badShape "a non-canonical pad and no funext to discharge it"
    return ← transportAlong eqi v p.lv p.ty p.canon scrut
      (falsePiUniq eqi fx p.lv p.canon scrut) (minorAt vals) (fun z => target (wrap z))
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
      mkLambdaFVars #[xv, s] (← chainDestruct v eqi fx? pad? boxed (nf - 1)
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
constructor the fibre is empty and `False.rec` closes it. `scrut` is the
level's own binder; the original tag is `succ^j scrut`. -/
partial def stepTower (v w : Level) (eqi : EqInfo) (fx? : Option Name) (fib motive : Expr)
    (minors : Array Expr) (cs : Array PCtor) (j : Nat) (scrut : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let mkAt := fun (tag tup : Expr) => psigmaMk (.succ .zero) w natT fib tag tup
  let mot ← withLocalDeclD `m natT fun m => do
    let tag := natSuccs j m
    withLocalDeclD `f (mkApp fib tag).headBeta fun f => do
      mkLambdaFVars #[m] (← mkForallFVars #[f] (mkApp motive (mkAt tag f)))
  let zc ← do
    let c := cs[j]!
    withLocalDeclD `f c.chain fun f => do
      let target := fun (tup : Expr) => pure (mkApp motive (mkAt (natNumeral j) tup))
      let minorAt := fun (vs : Array Expr) => mkAppN minors[j]! vs
      mkLambdaFVars #[f] (← chainDestruct v eqi fx? c.pad? c.boxed c.nf c.tele f id target minorAt)
  let sc ← withLocalDeclD `m natT fun m => do
    let inner ←
      if j + 1 == cs.size then
        let tag := natSuccs (j + 1) m
        withLocalDeclD `f (emptyAt w) fun f =>
          mkLambdaFVars #[f] (falseRec v
            (.lam `h (.const `False []) (mkApp motive (mkAt tag f)) .default)
            (emptyAtFst w f))
      else
        stepTower v w eqi fx? fib motive minors cs (j + 1) m
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
`PULift`'s shape — gets the [`Modelgen.falsePiAt`] singleton, which exists at
every level and is discharged by transport instead. -/
def padsAt (plans : Array CPlan) :
    GenM (Array (Option Pad)) := do
  plans.mapM fun plan => do
    let some ℓ := plan.pad? | return none
    if dsingOk ℓ then
      let (t, c) ← dsingAt ℓ
      return some { ty := t, lv := ℓ, canon := c, canonical := true }
    return some { ty := falsePiAt ℓ, lv := ℓ, canon := falsePiCanon ℓ, canonical := false }

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

/-- Which route the carrier's sort admits: `Sort 0` is the Church encoding,
a never-zero sort the `Nat`-tagged sum, and a **variable** sort — `Prop` at
some instantiations, `Type` at others, `PUnit`'s shape — the one carrier the
fragment has there, the [`Modelgen.falsePiAt`] singleton. -/
inductive PrimRoute | type | prop | singleton

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
  if ni > 0 then
    badShape "an indexed family (the skeleton-plus-good translation is not implemented)"
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
  unless rv.numMotives == 1 && rv.numMinors == nc && rv.numIndices == 0 do
    badShape s!"{ern} does not have 1 motive, {nc} minors and 0 indices"
  let large := rv.levelParams.length == lparams.length + 1
  unless (if large then rv.levelParams.tail! else rv.levelParams) == lparams do
    badShape s!"{ern} carries the level parameters {rv.levelParams}"
  let v := if large then Level.param rv.levelParams[0]! else Level.zero
  let recLs := if large then v :: us else us

  let wn := w.normalize
  let route : PrimRoute ←
    if wn.isZero then pure .prop
    else if wn.isNeverZero then pure .type
    else do
      -- A carrier at a **variable** sort, `Prop` at some instantiations and
      -- `Type` at others. The basis has exactly one type at such a sort — the
      -- inhabited `False`-Π singleton ([`Modelgen.falsePiAt`]) — so exactly
      -- the singleton shape models there.
      unless nc == 1 do
        badShape (if nc == 0 then
            s!"an empty carrier at Sort {w}: every type the basis builds at a \
              bare-parameter sort is a Π reached through an imax collapse, and the only \
              Sort-valued family there without a Sort {w} seed is False.rec's, over the \
              empty domain — inhabited, so an empty carrier is not constructible, and a \
              model of {ern} would prove False"
          else
            s!"a carrier at Sort {w} with {nc} constructors: the only carrier the basis \
              builds at a bare-parameter sort is the inhabited False-Π singleton")
      let nf0 ← forallBoundedTelescope memberTy (some np) fun ps _ => do
        pure (numForalls (← instForall exportCtors[0]!.2 ps))
      unless nf0 == 0 do
        badShape s!"a carrier at Sort {w} whose constructor has fields: the only carrier \
          the basis builds at a bare-parameter sort is the False-Π singleton"
      pure .singleton

  if isRec then
    badShape (match route with
      | .type =>
        "a recursive Type-valued inductive (the carrier needs the W/path construction — \
          plan B, not implemented)"
      | _ => "a recursive proposition (the Church induction derivation is not implemented)")

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
    for d in ← ensureFalse reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- Storage decisions — pure level arithmetic, and a decline here costs no
    -- further splice. A chain of one field is that field bare (no `PSigma`,
    -- so no built-in `1`); longer chains carry `max 1 ℓ⃗` already. A pad at
    -- `1` closes most gaps and `w` itself covers a deliberately-raised
    -- carrier — at *any* `w` now, since `falsePiAt` exists at every level.
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

    -- A pad at a level `dsingOk` cannot build is discharged by transport,
    -- and the transport's uniqueness proof is `funext` at a pointwise
    -- `False.rec` — so `funext` (and whatever deriving it splices) is
    -- ensured exactly when such a pad is planned.
    let fx? ← do
      if plans.any (fun pl => pl.pad?.any (fun ℓ => !dsingOk ℓ)) then
        let (n, ds) ← ensureFunext model eqi reserved
        for d in ds do out := out.push d; spliced := spliced ++ d.getNames
        pure (some n)
      else pure none

    let natT : Expr := .const `Nat []
    let fibreAt := fun (ps : Array Expr) => do
      let pads ← padsAt plans
      let cs ← pctorsAt exportCtors plans pads ps
      withLocalDeclD `n natT fun n =>
        return (cs, ← mkLambdaFVars #[n] (← fibreTower w cs 0 n))

    -- ── the carrier ──
    let selfVal ← withParams fun ps => do
      let (_, fib) ← fibreAt ps
      mkLambdaFVars ps (psigmaT (.succ .zero) w natT fib)
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
        let (cs, fib) ← fibreAt ps
        let c := cs[j]!
        forallBoundedTelescope c.tele (some c.nf) fun fs _ => do
          let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
          mkLambdaFVars (ps ++ fs)
            (psigmaMk (.succ .zero) w natT fib (natNumeral j) tup)
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
      let (cs, fib) ← fibreAt ps
      let minor ←
        if nc == 0 then
          withLocalDeclD `n natT fun n => do
            withLocalDeclD `f (emptyAt w) fun f =>
              mkLambdaFVars #[n, f] (falseRec v
                (.lam `h (.const `False [])
                  (mkApp motive (psigmaMk (.succ .zero) w natT fib n f)) .default)
                (emptyAtFst w f))
        else
          withLocalDeclD `n natT fun n => do
            withLocalDeclD `f (mkApp fib n).headBeta fun f => do
              mkLambdaFVars #[n, f]
                (mkApp (← stepTower v w eqi fx? fib motive minors cs 0 n) f)
      mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT fib motive minor major)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else if route matches PrimRoute.prop then
    -- ════ the Prop route ════
    let churchAt := fun (ps : Array Expr)
        (k : Expr → Array Expr → Array Expr → GenM Expr) => do
      -- `C`, the `k_j` binders, and their types, in one scope.
      withLocalDeclD `C (.sort .zero) fun C => do
        let kTys ← exportCtors.mapM fun (_, cty) => do
          let tele ← instForall cty ps
          churchSwap C (numForalls tele) tele
        churchBinders kTys 0 #[] (fun ks => k C ks kTys)

    -- ── the carrier ──
    let selfVal ← withParams fun ps => do
      churchAt ps fun C ks _ => do
        mkLambdaFVars ps (← mkForallFVars (#[C] ++ ks) C)
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
        let tele ← instForall cty ps
        forallBoundedTelescope tele (some (numForalls tele)) fun fs _ =>
          churchAt ps fun C ks _ =>
            mkLambdaFVars (ps ++ fs ++ #[C] ++ ks) (mkAppN ks[j]! fs)
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── the recursor ──
    if large && nc == 0 then
      for d in ← ensureFalse reserved do out := out.push d; spliced := spliced ++ d.getNames
    let recTy := restore tbl rv.type
    let recVal ← forallBoundedTelescope recTy (some (np + 1 + nc + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minors := bs.extract (np + 1) (np + 1 + nc)
      let t := bs[bs.size - 1]!
      if !large then
        -- The fold, at `C := motive t`: every minor's motive is closed by
        -- definitional proof irrelevance.
        mkLambdaFVars bs (mkAppN t (#[mkApp motive t] ++ minors))
      else if nc == 0 then
        mkLambdaFVars bs (falseRec v
          (.lam `h (.const `False []) (mkApp motive t) .default)
          (mkApp t (.const `False [])))
      else do
        -- Large elimination: one constructor, every field a proposition
        -- (the subsingleton rule, which minted this recursor, says so) —
        -- extract each by instantiating the encoding at the field's type.
        unless nc == 1 do
          badShape s!"{ern} is large-eliminating with {nc} constructors and no indices"
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
          es := es.push (mkAppN t #[ft, proj])
          curT := rest.instantiate1 es[i]!
        mkLambdaFVars bs (mkAppN minors[0]! es)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else
    -- ════ the singleton route: one constructor, no fields, a variable sort ════
    -- The carrier is `(h : False) → False.rec (fun _ => Sort w) h` — at
    -- exactly `Sort w` because `imax 0 w = w` — and the constructor its
    -- canonical element. Any element is `funext`-equal to it (pointwise from
    -- `h : False`), so the recursor transports the minor along that proof;
    -- at the constructor the proof is a closed self-equality and K-like
    -- reduction on `Eq.rec` erases the transport, so ι is `Eq.refl` here as
    -- on the other two routes.
    for d in ← ensureFalse reserved do out := out.push d; spliced := spliced ++ d.getNames
    let (fxN, fxDecls) ← ensureFunext model eqi reserved
    for d in fxDecls do out := out.push d; spliced := spliced ++ d.getNames

    -- ── the carrier ──
    let selfVal ← withParams fun ps => mkLambdaFVars ps (falsePiAt w)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := memberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructor ──
    let ty := restore tbl exportCtors[0]!.2
    let val ← withParams fun ps => mkLambdaFVars ps (falsePiCanon w)
    let dCtor := Declaration.defnDecl
      { name := ctorN 0, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked dCtor
    out := out.push dCtor

    -- ── the recursor ──
    let recTy := restore tbl rv.type
    let recVal ← forallBoundedTelescope recTy (some (np + 1 + 1 + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minor := bs[np + 1]!
      let major := bs[bs.size - 1]!
      let selfT := mkAppN (.const selfN us) ps
      let ctorE := mkAppN (.const (ctorN 0) us) ps
      mkLambdaFVars bs (← transportAlong eqi v w selfT ctorE major
        (falsePiUniq eqi fxN w ctorE major) minor (fun z => pure (mkApp motive z)))
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
      forallBoundedTelescope cty (some (numForalls modelCTy - np)) fun fields _ => do
        let major := mkAppN (.const modelC us) (ps ++ fields)
        let lhs := mkAppN (.const recN recLs) (pre.push major)
        let rhs := (restore tbl rule.rhs).beta (pre ++ fields)
        let α := mkApp motive major
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
