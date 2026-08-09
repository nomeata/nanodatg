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

## The two routes

**Type route** — carrier sort `w` never zero:

```text
T._model.self p⃗ := Σ'(n : Nat), F n        F : a Nat.rec cases tower
F ȷ̄  := the j-th constructor's field chain  (right-nested PSigma,
        padded to exactly Sort w by a Sing when the levels demand it)
F n  := an empty type at Sort w for n ≥ #ctors  (Σ'(h : False), False.rec h)
```

The recursor destructs the pair, cases on the tag with `Nat.rec` — the
large elimination the basis buys, and the reason `Nat` is in it — and then
destructs the chain. A pad is discharged by transporting along its
uniqueness proof (`funext`-derived); on a constructor application the
transport sits on a closed self-equality, which proof irrelevance plus ι
erase, so **every ι theorem is `Eq.refl`**.

`Sing ℓ` is an inhabited, propositionally-singleton type at exactly
`Sort ℓ`, built by recursion on the level: `Sing (a+1) := (α : Sort a) →
Σ'(f : α → α), Eq f id` — the Π lands at `imax (a+1) (max 1 a) = a+1`
exactly because the body is never `Prop` — and `Sing (max a b) :=
Σ'(_ : Sing a), Sing b`. A level whose normal form is neither a successor
nor a `max` of constructible sides has no `Sing`, and a shape that needs
one there declines.

**Prop route** — carrier sort `0`: the impredicative Church encoding
`∀ C : Prop, (∀ f⃗₀, C) → … → C`. At a `Prop` motive the dependent recursor
is the fold itself — the motive's proof argument is definitionally
irrelevant. When the export's recursor is large-eliminating the
subsingleton rule holds, so (non-indexed) every field is a proposition and
is **extracted** by instantiating the encoding at the field's own type;
proof irrelevance closes the motive. ι is `Eq.refl` on both counts.

## What declines, and why

* **recursive** (`List`, `Lean.Name`, …) — the carrier needs the W/path
  construction (plan B). Not implemented; the reason is printed.
* **indexed** (`HEq`, `Nat.le`, the composed `T._model.aux`) — the
  skeleton-plus-`good` translation (thesis §5.2) is not implemented.
* **sort-variable carriers** (`PUnit : Sort u`, `PEmpty : Sort u`) — a
  carrier that reaches `Prop` at some instantiations and `Type` at others
  has no uniform model in this fragment; `monomorph` resolves the variable
  and the monomorphized file models.
* **a `Sing`-less level** — a pad is needed and the level's normal form is
  not constructible.
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

/-- A chain's pad: its type, its type's level, and its canonical element —
to which every element is **defeq** ([`Modelgen.dsingAt`]), so no
uniqueness proof rides along. -/
structure Pad where
  ty : Expr
  lv : Level
  canon : Expr

/-! ## One constructor's chain

A constructor's field telescope becomes a right-nested `PSigma` at exactly
`Sort w`. The builders below recurse on the (progressively instantiated)
telescope expression, so nothing is stored across scopes. `pad?` closes the
chain when the field levels do not already reach `w` — and always for a
nullary constructor. -/

/-- The chain's type and level. `nf` is the field count; the telescope's
trailing result type is never entered. -/
partial def chainTy (pad? : Option Pad) (nf : Nat) (tele : Expr) :
    GenM (Expr × Level) := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return (p.ty, p.lv)
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let ℓt ← ilevel t
  if nf == 1 && pad?.isNone then
    return (t, ℓt)
  withLocalDeclD x t fun xv => do
    let (inner, ℓi) ← chainTy pad? (nf - 1) (rest.instantiate1 xv)
    return (psigmaT ℓt ℓi t (← mkLambdaFVars #[xv] inner),
      (mkLevelMax' (mkLevelMax' (.succ .zero) ℓt) ℓi).normalize)

/-- The tuple `⟨v₁, ⟨v₂, …⟩⟩` at the given field values, closed by the
pad's canonical element when there is one. -/
partial def chainTuple (pad? : Option Pad) (nf : Nat) (tele : Expr)
    (vals : Array Expr) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return p.canon
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  if nf == 1 && pad?.isNone then
    return vals[i]!
  let ℓt ← ilevel t
  let (β, ℓi) ← withLocalDeclD x t fun xv => do
    let (inner, ℓi) ← chainTy pad? (nf - 1) (rest.instantiate1 xv)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let snd ← chainTuple pad? (nf - 1) (rest.instantiate1 vals[i]!) vals (i + 1)
  return psigmaMk ℓt ℓi t β vals[i]! snd

/-- The recursor's destructor for one chain: from `scrut : chainTy`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields; a pad is discharged by
transporting the applied minor along the pad's uniqueness, and on a
constructor application `uniq canon` is a closed self-equality that proof
irrelevance plus ι erase. -/
partial def chainDestruct (v : Level) (pad? : Option Pad)
    (nf : Nat) (tele : Expr) (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (vals : Array Expr := #[]) : GenM Expr := do
  if nf == 0 then
    let some _ := pad? | badShape "a chain with no fields needs a pad"
    -- `scrut` is defeq to the pad's canonical element, so the applied minor
    -- already has the target type.
    return minorAt vals
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  if nf == 1 && pad?.isNone then
    return minorAt (vals.push scrut)
  let ℓt ← ilevel t
  let (β, ℓi) ← withLocalDeclD x t fun xv => do
    let (inner, ℓi) ← chainTy pad? (nf - 1) (rest.instantiate1 xv)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let motive ← withLocalDeclD `s (psigmaT ℓt ℓi t β) fun s => do
    mkLambdaFVars #[s] (← target (wrap s))
  let m ← withLocalDeclD x t fun xv => do
    withLocalDeclD `s (mkApp β xv).headBeta fun s => do
      let wrap' := fun (z : Expr) => wrap (psigmaMk ℓt ℓi t β xv z)
      mkLambdaFVars #[xv, s] (← chainDestruct v pad? (nf - 1)
        (rest.instantiate1 xv) s wrap' target minorAt (vals.push xv))
  return psigmaRec v ℓt ℓi t β motive m scrut

/-! ## The Type route's recursor tower -/

/-- What one constructor contributes, at a given parameter scope. -/
structure PCtor where
  /-- The instantiated field telescope. -/
  tele : Expr
  nf : Nat
  pad? : Option Pad
  /-- The chain type. -/
  chain : Expr

instance : Inhabited PCtor := ⟨⟨default, 0, none, default⟩⟩

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
partial def stepTower (v w : Level) (fib motive : Expr)
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
      mkLambdaFVars #[f] (← chainDestruct v c.pad? c.nf c.tele f id target minorAt)
  let sc ← withLocalDeclD `m natT fun m => do
    let inner ←
      if j + 1 == cs.size then
        let tag := natSuccs (j + 1) m
        withLocalDeclD `f (emptyAt w) fun f =>
          mkLambdaFVars #[f] (falseRec v
            (.lam `h (.const `False []) (mkApp motive (mkAt tag f)) .default)
            (emptyAtFst w f))
      else
        stepTower v w fib motive minors cs (j + 1) m
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

/-- The pads of every constructor at the given parameter scope, `none` where
the chain reaches `Sort w` on its own. Pad decisions are level arithmetic
and were made (and possibly declined) before anything was spliced; the pad
level is `1` when that already closes the gap and `w` otherwise. -/
def padsAt (padPlan : Array (Option Level)) :
    GenM (Array (Option Pad)) := do
  padPlan.mapM fun plan => do
    let some ℓ := plan | return none
    let (t, c) ← dsingAt ℓ
    return some { ty := t, lv := ℓ, canon := c }

/-- The constructors, analysed at a parameter scope. -/
def pctorsAt (exportCtors : Array (Name × Expr)) (pads : Array (Option Pad))
    (ps : Array Expr) : GenM (Array PCtor) := do
  (Array.range exportCtors.size).mapM fun j => do
    let (_, cty) := exportCtors[j]!
    let tele ← instForall cty ps
    let nf := numForalls tele
    let (chain, _) ← chainTy pads[j]! nf tele
    return { tele, nf, pad? := pads[j]!, chain }

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
  let typeRoute ←
    if wn.isZero then pure false
    else if wn.isNeverZero then pure true
    else badShape s!"a carrier at Sort {w}, which reaches Prop at some instantiations \
      and Type at others (monomorph resolves the variable)"

  if isRec then
    badShape (if typeRoute then
        "a recursive Type-valued inductive (the carrier needs the W/path construction — \
          plan B, not implemented)"
      else
        "a recursive proposition (the Church induction derivation is not implemented)")

  let (eqi, eqDecls) ← ensureEq reserved
  let mut out : Array Declaration := eqDecls
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)

  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps

  let ctorPairs := (Array.range nc).map fun j => (exportCtors[j]!.1, ctorN j)
  let tbl := modelTable (← getEnv) #[tname]
    { decls := #[], levelParams := lparams, members := #[], selfNames := #[selfN]
      numAll := 1, ctors := ctorPairs, recs := #[recN], iotas := #[], spliced := #[] }

  if typeRoute then
    -- ════ the Type route ════
    unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
    for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensurePSigma reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureFalse reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- Pad decisions — pure level arithmetic, and a decline here costs no
    -- splice. A chain of one field is that field bare (no `PSigma`, so no
    -- built-in `1`); longer chains carry `max 1 ℓ⃗` already. A pad at `1`
    -- closes most gaps; `w` itself covers a deliberately-raised carrier
    -- when it is constructible.
    let padPlan : Array (Option Level) ← withParams fun ps =>
      exportCtors.mapM fun (cn, cty) => do
        let tele ← instForall cty ps
        let nf := numForalls tele
        let ℓs ← forallBoundedTelescope tele (some nf) fun fs _ =>
          fs.mapM fun f => do ilevel (← ityp f)
        let raw := if nf == 1 then ℓs[0]! else (ℓs.foldl mkLevelMax' (.succ .zero)).normalize
        if nf > 0 then
          if ← isLevelDefEq raw w then return none
        let withOne := (ℓs.foldl mkLevelMax' (.succ .zero)).normalize
        if ← isLevelDefEq withOne w then return some (Level.succ .zero)
        if dsingOk w then
          if ← isLevelDefEq (mkLevelMax' withOne w) w then return some w
        badShape s!"{cn}'s fields reach Sort {raw} and the carrier is Sort {w}: no \
          buildable pad closes the gap"

    let natT : Expr := .const `Nat []
    let fibreAt := fun (ps : Array Expr) => do
      let pads ← padsAt padPlan
      let cs ← pctorsAt exportCtors pads ps
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
          let tup ← chainTuple c.pad? c.nf c.tele fs
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
                (mkApp (← stepTower v w fib motive minors cs 0 n) f)
      mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT fib motive minor major)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else
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
