import Lean
import Modelgen.Plan

/-!
# The model of a nested inductive, generated

A port of `mini/src/nested_ev.rs` to `MetaM`. Given a nested declaration and
its specialisation ([`Modelgen.plan`]), this emits ordinary Lean declarations —
the block under fresh names, a carrier, one `pack`/`unpack` pair per mimic with
**both round trips as theorems**, the declared type's own constructors, one
recursor per block member, one congruence per mimic, and **every one of those
recursors' ι rules, as theorems with proofs**. Every declaration goes through
`Environment.addDeclCore` with checking on, so a proof this module builds and
the kernel rejects is a decline, never an emission.

`mini/tests/fixtures/nested_model.lean` is this development written by hand at
`Tree`; it is the clearest statement of the target shape that exists.

## What the fvar telescope buys

The Rust writes every term at an explicit de Bruijn depth, and its header says
that "a term read at the wrong depth is the failure mode this project has paid
for most often — three of the indexed row's five layers were exactly that".
None of that arithmetic survives here: an occurrence is stored once, relative
to the block's parameter telescope, and [`Modelgen.Gen.occAt`] instantiates it
at whatever parameter `fvar`s are in scope. There is no shift in this file, and
every minor's binder telescope is read off the recursor's **own** minor type
rather than reconstructed.

## Two things that are forced, and one that is not a workaround

* **The model may not reuse `T`.** `T` is a primitive inductive and the block
  member `B₀` is a different constant; they are not convertible. So the model
  declares `T._model.self : ∀p⃗, Sort u := B₀ p⃗` and rewrites `T ↦
  T._model.self` everywhere. Identifying the two is the *keying* step and
  belongs to the consumer.
* **`unpack`'s motive vector is forced.** A block recursor carries one motive
  per member at one motive universe, so the members `unpack` does not
  eliminate into still need a motive at that sort: the identity at the root and
  the occurrence at each mimic.
* **`congrCtor` cannot be a single named lemma** — each step of the fold
  abstracts a different position of the same constructor — so
  [`Modelgen.Gen.foldCongr`] builds it inline. `congrPack` per mimic *can* be a
  declaration, because the root's fold moves `pack` and one lemma covers every
  position.
-/

open Lean Meta

namespace Modelgen

/-- Why a nested declaration's model could not be built. Each is a shape. -/
inductive Decline where
  | indexed
  | dependentFields
  | noEq
  | nameTaken (n : Name)
  /-- Two mimics whose containers mention each other, so `pack` would have to
  be mutually recursive. -/
  | cyclicMimics
  | malformed (msg : String)
  deriving Inhabited

/-- The word that reaches a report line. -/
def Decline.label : Decline → String
  | .indexed => "nested model with indices"
  | .dependentFields => "nested model with dependent fields"
  | .noEq => "nested model without Eq"
  | .nameTaken n => s!"nested model name taken ({n})"
  | .cyclicMimics => "nested model with mutually recursive occurrences"
  | .malformed m => s!"nested model shape: {m}"

/-- `Eq`, `Eq.refl` and `Eq.rec` at the arities the round trips need. The
export's own — this module does not fabricate an equality Lean never wrote. -/
structure EqInfo where
  eqN : Name
  reflN : Name
  recN : Name
  deriving Inhabited

/-- Read the three constants and check the recursor is Lean's shape:
`Eq.rec α a motive base b h`, two parameters and one index. -/
def EqInfo.read (env : Environment) : Except Decline EqInfo := do
  let eq := `Eq
  let some (.inductInfo iv) := env.constants.find? eq | throw .noEq
  unless iv.numParams == 2 && iv.numIndices == 1 && iv.ctors.length == 1 do throw .noEq
  let rc := Name.str eq "rec"
  let some (.recInfo rv) := env.constants.find? rc | throw .noEq
  unless rv.numParams == 2 && rv.numMotives == 1 && rv.numMinors == 1 && rv.numIndices == 1 do
    throw .noEq
  let rf := Name.str eq "refl"
  unless env.constants.contains rf do throw .noEq
  return { eqN := eq, reflN := rf, recN := rc }

/-- `Eq.{u} α a b`. -/
def EqInfo.mk' (e : EqInfo) (u : Level) (α a b : Expr) : Expr :=
  mkAppN (.const e.eqN [u]) #[α, a, b]

/-- `Eq.refl.{u} α a`. -/
def EqInfo.refl' (e : EqInfo) (u : Level) (α a : Expr) : Expr :=
  mkAppN (.const e.reflN [u]) #[α, a]

/-- `Eq.rec.{v,u} α a motive base b h`. The motive sits at `Prop` wherever an
*equation* is transported and at the eliminator's own universe wherever a
*value* is; each caller passes `v` explicitly for that reason. -/
def EqInfo.recAt (e : EqInfo) (v u : Level) (α a motive base b h : Expr) : Expr :=
  mkAppN (.const e.recN [v, u]) #[α, a, motive, base, b, h]

/-! ## Restoring: rewriting the block's names to the model's -/

/-- Rewrite every name the specialisation introduced back to what it stands
for. A head that consumes `p` arguments has them substituted into its
replacement — that is how `Tree._nested.1 α` becomes `List (Tree α)` under a
parameter — and a head that consumes none is a plain rename. -/
partial def restore (heads : Std.HashMap Name (Nat × Expr)) (e : Expr) : Expr :=
  if heads.isEmpty then e else
  match e with
  | .const n _ => match heads[n]? with
    | some (0, repl) => repl
    | _ => e
  | .app .. =>
    let h := e.getAppFn
    let args := e.getAppArgs.map (restore heads)
    match h with
    | .const n _ =>
      match heads[n]? with
      | some (take, repl) =>
        if args.size ≥ take then
          mkAppN (repl.instantiateRev (args.extract 0 take)) (args.extract take args.size)
        else mkAppN h args
      | none => mkAppN h args
    | _ => mkAppN (restore heads h) args
  | .lam n t b bi => .lam n (restore heads t) (restore heads b) bi
  | .forallE n t b bi => .forallE n (restore heads t) (restore heads b) bi
  | .letE n t v b nd => .letE n (restore heads t) (restore heads v) (restore heads b) nd
  | .proj tn i s => .proj tn i (restore heads s)
  | _ => e

/-! ## The generator -/

/-- The generator's read-only context. -/
structure Gen where
  /-- `T._model`. -/
  model : Name
  /-- `R_k._model.self` for each **real** member `R_k` — the carriers. One
  unless the declaration is a mutual block. -/
  selfNames : Array Name
  /-- How many block members are the export's own; the rest are mimics. Written
  `r` throughout: member `k` is real iff `k < r`, and mimic `k − r` otherwise. -/
  numAll : Nat
  np : Nat
  /-- The block's resultant sort. -/
  u : Level
  /-- **The declaration's own level parameters, as levels.** Every generated
  constant carries exactly these, in the export's own order, so a reference to
  one is written at `g.us` and a block recursor at `v :: g.us`. Empty for a
  monomorphic declaration, which is why nothing in the fixture set noticed
  their absence. -/
  us : List Level
  /-- The block's members, root first: `T._model.0`, `T._model.1`, … -/
  members : Array Name
  /-- Each member's constructor names, in order. -/
  blockCtors : Array (Array Name)
  /-- The occurrences, each at the block's parameter telescope depth, with the
  export's `T` already rewritten to the carrier. -/
  occs : Array Expr
  eqi : EqInfo

/-- The generator's monad: `MetaM`, with a *shape* decline as its own error so
that a declaration this module cannot write is never confused with one the
kernel rejected. -/
abbrev GenM := ExceptT Decline MetaM

def declineWith (d : Decline) : GenM α := throwThe Decline d
def badShape (msg : String) : GenM α := declineWith (.malformed msg)

/-- `Meta.inferType`, at the generator's monad. -/
def ityp (e : Expr) : GenM Expr := inferType e

def constInfo (n : Name) : GenM ConstantInfo := do
  let some ci := (← getEnv).constants.find? n | badShape s!"{n} is not declared"
  return ci

/-- The container's constructors. -/
def ctorsOf (c : Name) : GenM (Array Name) := do
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  return iv.ctors.toArray

/-- How many fields a constructor has. -/
def numFieldsOf (c : Name) : GenM Nat := do
  let .ctorInfo cv ← constInfo c | badShape s!"{c} is not a constructor"
  return cv.numFields

/-- Peel `args.size` `∀` binders, substituting as it goes. -/
def instForall (ty : Expr) (args : Array Expr) : GenM Expr := do
  let mut cur := ty
  for a in args do
    match cur with
    | .forallE _ _ b _ => cur := b.instantiate1 a
    | _ => badShape "too few binders to instantiate"
  return cur

/-- A constructor's type at the given levels with `qs` substituted for its
leading binders, leaving the field telescope. -/
def instCtor (cn : Name) (ls : List Level) (qs : Array Expr) : GenM Expr := do
  let ci ← constInfo cn
  instForall (ci.type.instantiateLevelParams ci.levelParams ls) qs

/-- Open a type's telescope, with the binder types. -/
def withFields (ty : Expr) (k : Array Expr → Array Expr → GenM α) : GenM α := do
  forallTelescope ty fun fs _ => do k fs (← fs.mapM ityp)

/-- **The dependency the congruence fold cannot survive, and only that one.**

The fold replaces one *packed* position of a constructor application at a time,
so a field whose type mentions an earlier packed field is ill-typed at every
intermediate stage. A dependency on a field that does **not** move is never
touched by the fold, and Lean supports it — `node : (n : N) → Vec N n → List
DTree → DTree` and `node : List ETree → (n : N) → Vec N n → ETree` are both
`dependent_fields.lean`, and both are models now.

A dependency *on* a packed field is out of reach for a different reason: Lean
does not support it either. `node : (l : List GTree) → Len l N.z → GTree` fails
Lean's own nested compilation with `unknown constant 'GTree'`, because the
auxiliary block replaces `List GTree` with a fresh member and `Len l` is then
about a constant that does not yet exist. -/
def noDepOnPacked (packed : Array Expr) (fs tys : Array Expr) : GenM Unit := do
  for i in [0:tys.size] do
    for j in [0:i] do
      if packed.contains fs[j]! && tys[i]!.containsFVar fs[j]!.fvarId! then
        declineWith .dependentFields

/-- Read `n` minor premise types off a recursor application. -/
def withMinorTypes (recApp : Expr) (n : Nat) (k : Array Expr → GenM α) : GenM α := do
  let ty ← ityp recApp
  forallBoundedTelescope ty (some n) fun mvars _ => do
    k (← mvars.mapM ityp)

namespace Gen

def packName (g : Gen) (i : Nat) : Name := .str g.model s!"pack_{i}"
def unpackName (g : Gen) (i : Nat) : Name := .str g.model s!"unpack_{i}"
def retractName (g : Gen) (i : Nat) : Name := .str g.model s!"unpackPack_{i}"
def sectionName (g : Gen) (i : Nat) : Name := .str g.model s!"packUnpack_{i}"
def ctorName (g : Gen) (j : Nat) : Name := .str g.model s!"ctor_{j}"
def recName (g : Gen) (k : Nat) : Name := .str g.model s!"rec_{k}"
def congrPackName (g : Gen) (i : Nat) : Name := .str g.model s!"congrPack_{i}"
def iotaName (g : Gen) (k j : Nat) : Name := .str g.model s!"iota_{k}_{j}"

/-- Is block member `k` one of the export's own, rather than a mimic? -/
def isReal (g : Gen) (k : Nat) : Bool := k < g.numAll

/-- The mimic index of a block member that is not real. -/
def mimicOf (g : Gen) (k : Nat) : Nat := k - g.numAll

/-- Occurrence `i` at the parameter `fvar`s in scope. -/
def occAt (g : Gen) (i : Nat) (ps : Array Expr) : Expr := g.occs[i]!.instantiateRev ps

/-- `Bₖ p⃗`. -/
def memAt (g : Gen) (k : Nat) (ps : Array Expr) : Expr := mkAppN (.const g.members[k]! g.us) ps

/-- `f p⃗ x` — every generated map takes the parameters first. -/
def call (g : Gen) (f : Name) (ps : Array Expr) (x : Expr) : Expr :=
  mkAppN (.const f g.us) (ps.push x)

/-- `Bₖ.c p⃗ args`. -/
def blockCtorAt (g : Gen) (k : Nat) (c : Name) (ps args : Array Expr) : Expr :=
  mkAppN (.const (.str g.members[k]! (lastStr c)) g.us) (ps ++ args)

/-- Which block member a field's type is at, if any. -/
def memberOf (g : Gen) (t : Expr) : Option Nat :=
  match t.getAppFn with
  | .const n _ => g.members.findIdx? (· == n)
  | _ => none

/-- `(member, constructor)` for every constructor of the block, in the order
`Bₖ.rec` binds its minors. -/
def ctorPairs (g : Gen) : Array (Nat × Name) :=
  (Array.range g.members.size).flatMap fun k => g.blockCtors[k]!.map (k, ·)

/-- The total number of the block's constructors — the recursors' minor count. -/
def numMinors (g : Gen) : Nat := g.ctorPairs.size

/-- `Bₖ.rec`, the block's own. -/
def blockRec (g : Gen) (k : Nat) : Name := .str g.members[k]! "rec"

/-- `Bₖ.rec` at motive universe `v`. Lean puts the motive universe **first**
and the block's own level parameters after it, and it mints the same fresh
name for `T._model.0.rec` as for `T.rec` because both are generated from the
same level parameter list. -/
def blockRecAt (g : Gen) (k : Nat) (v : Level) : Expr :=
  .const (g.blockRec k) (v :: g.us)

/-- The container of occurrence `i` at `ps`: its name, level list and the
arguments it is applied to. -/
def container (g : Gen) (i : Nat) (ps : Array Expr) :
    GenM (Name × List Level × Array Expr) := do
  let occ := g.occAt i ps
  let .const c cls := occ.getAppFn | badShape "the occurrence is not headed by a constant"
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  if iv.numIndices != 0 then declineWith .indexed
  return (c, cls, occ.getAppArgs)

/-- The real container constructor a mimic's constructor stands for, by its
last name component — the correspondence [`Modelgen.plan`] built it from. -/
def realCtor (g : Gen) (i : Nat) (ps : Array Expr) (cn : Name) : GenM Name := do
  let (c, _, _) ← g.container i ps
  let last := lastStr cn
  let some r := (← ctorsOf c).find? (fun r => lastStr r == last)
    | badShape s!"no real constructor for {cn}"
  return r

/-- **One congruence per moving argument.** From `pⱼ : Eq lhsⱼ rhsⱼ` at the
positions that move, build `Eq (f lhs⃗) (f rhs⃗)` by transporting one position at
a time: at step `j` the accumulator proves `Eq (f lhs⃗) (f mix(j))`, where
`mix(j)` is `rhs` below `j` and `lhs` at and above it.

This is where a constructor with **two or more** moving positions is paid for,
and it is why the fold exists rather than a single transport. It is also why
`congrCtor` is not a declaration: each step abstracts a *different* position of
the same constructor, so a named lemma would be one per position. -/
def foldCongr (g : Gen) (goalTy : Expr) (fieldTys lhs rhs : Array Expr)
    (proofs : Array (Option Expr)) (rebuild : Array Expr → Expr) : GenM Expr := do
  let n := lhs.size
  let start := rebuild lhs
  let mut acc := g.eqi.refl' g.u goalTy start
  for j in [0:n] do
    let some p := proofs[j]! | continue
    if lhs[j]! == rhs[j]! then continue
    let α := fieldTys[j]!
    let mot ← withLocalDeclD `x α fun x => do
      withLocalDeclD `hx (g.eqi.mk' g.u α lhs[j]! x) fun hx => do
        let mix := (Array.range n).map fun k =>
          if k < j then rhs[k]! else if k == j then x else lhs[k]!
        mkLambdaFVars #[x, hx] (g.eqi.mk' g.u goalTy start (rebuild mix))
    acc := g.eqi.recAt .zero g.u α lhs[j]! mot acc rhs[j]! p
  return acc

/-- The value-transport counterpart of [`Modelgen.Gen.foldCongr`]: from
`v : M (f lhs⃗)` and `pⱼ : Eq lhsⱼ rhsⱼ`, produce `M (f rhs⃗)`, one position at a
time. The motive lands at the eliminator's universe, which is the one place in
this file an `Eq.rec` is not `Prop`-valued. -/
def foldValue (g : Gen) (v : Level) (m0 : Expr) (fieldTys lhs rhs : Array Expr)
    (proofs : Array (Option Expr)) (rebuild : Array Expr → Expr) (base : Expr) :
    GenM Expr := do
  let n := lhs.size
  let mut acc := base
  for j in [0:n] do
    let some p := proofs[j]! | continue
    if lhs[j]! == rhs[j]! then continue
    let α := fieldTys[j]!
    let mot ← withLocalDeclD `x α fun x => do
      withLocalDeclD `hx (g.eqi.mk' g.u α lhs[j]! x) fun hx => do
        let mix := (Array.range n).map fun k =>
          if k < j then rhs[k]! else if k == j then x else lhs[k]!
        mkLambdaFVars #[x, hx] (mkApp m0 (rebuild mix))
    acc := g.eqi.recAt v g.u α lhs[j]! mot acc rhs[j]! p
  return acc

/-! ### pack -/

/-- `fun f⃗ ih⃗ => Bᵢ.c p⃗ g⃗`, where a field recursive in the container is its own
induction hypothesis, a field at another mimic is packed, and anything else —
a plain field, or one at the root, which the block types at `B₀ p⃗` and
`T._model.self p⃗` unfolds to — goes through untouched. -/
def packMinor (g : Gen) (i member : Nat) (ps : Array Expr) (cn : Name) (mty : Expr) :
    GenM Expr := do
  let occ := g.occAt i ps
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ityp
    let recs := (Array.range n).filter fun x => ftys[x]! == occ
    let mut args : Array Expr := #[]
    for x in [0:n] do
      if let some t := recs.findIdx? (· == x) then
        args := args.push ihs[t]!
      else if let some o := (Array.range g.occs.size).find? (g.occAt · ps == ftys[x]!) then
        args := args.push (g.call (g.packName o) ps fields[x]!)
      else
        args := args.push fields[x]!
    mkLambdaFVars bs (g.blockCtorAt member cn ps args)

/-- `packᵢ := C.rec q⃗ (fun _ => Bᵢ p⃗) minors…`, partially applied — its type is
`∀ _ : occᵢ, Bᵢ p⃗` on the nose, the motive being constant.

The recursor's level list is `u :: cls` and not `u :: C`'s *declared*
parameters: a polymorphic container instantiated at a concrete level — `List.{0}
Syntax` — is exactly `Lean.Syntax`'s shape, and writing the declared parameter
there leaves a free universe variable. -/
def packValue (g : Gen) (i member : Nat) (ps : Array Expr) : GenM Expr := do
  let (c, cls, qs) ← g.container i ps
  let occ := g.occAt i ps
  let motive : Expr := .lam `x occ (g.memAt member ps) .default
  let head : Expr := .const (.str c "rec") (g.u :: cls)
  let cs ← ctorsOf c
  let pre := qs.push motive
  let minors ← withMinorTypes (mkAppN head pre) cs.size fun mtys =>
    (Array.range cs.size).mapM fun t => g.packMinor i member ps cs[t]! mtys[t]!
  return mkAppN head (pre ++ minors)

/-! ### unpack -/

/-- A member's minor for `unpack`: at the root, rebuild the constructor; at a
mimic, build the **real** container's constructor, taking each field at another
mimic from its induction hypothesis. -/
def unpackMinor (g : Gen) (k : Nat) (ps : Array Expr) (cn : Name) (mty : Expr) :
    GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ityp
    let recs := (Array.range n).filter fun x => (g.memberOf ftys[x]!).isSome
    let mut args : Array Expr := #[]
    for x in [0:n] do
      match g.memberOf ftys[x]! with
      | some m =>
        if !g.isReal m then
          -- A field at a *mimic* is unpacked, and its unpacked value is exactly
          -- this recursor's induction hypothesis for it.
          let some t := recs.findIdx? (· == x) | badShape "no hypothesis for a mimic field"
          args := args.push ihs[t]!
        else
          -- A field at a **real** member passes through: the block types it at
          -- `Bₘ p⃗`, and the real constructor wants `Rₘ._model.self p⃗`, which is
          -- that by δ.
          args := args.push fields[x]!
      | none =>
        args := args.push fields[x]!
    let body ←
      if g.isReal k then
        pure (g.blockCtorAt k cn ps fields)
      else do
        let (_, cls, qs) ← g.container (g.mimicOf k) ps
        let real ← g.realCtor (g.mimicOf k) ps cn
        pure (mkAppN (.const real cls) (qs ++ args))
    mkLambdaFVars bs body

/-- `unpackᵢ := Bᵢ.rec p⃗ motives… minors…`, partially applied.

The motive at the root is `fun _ => B₀ p⃗` and at each mimic the occurrence:
that is the only choice inhabited for every block whatever its constructors
are, and `fun _ => Bⱼ` would not do because `unpack₁` for `Box BTree` needs
`unpack₂`'s result as its `mk` field. -/
def unpackValue (g : Gen) (member : Nat) (ps : Array Expr) : GenM Expr := do
  let motives := (Array.range g.members.size).map fun k =>
    Expr.lam `b (g.memAt k ps)
      (if g.isReal k then g.memAt k ps else g.occAt (g.mimicOf k) ps) .default
  let head : Expr := g.blockRecAt member g.u
  let pre := ps ++ motives
  let pairs := g.ctorPairs
  let minors ← withMinorTypes (mkAppN head pre) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t => g.unpackMinor pairs[t]!.1 ps pairs[t]!.2 mtys[t]!
  return mkAppN head (pre ++ minors)

/-! ### the two round trips -/

/-- `unpackPackᵢ : ∀p⃗ l, Eq (unpackᵢ p⃗ (packᵢ p⃗ l)) l`, by the container's own
recursor, one congruence per field the round trip moves. -/
def retractValue (g : Gen) (i : Nat) (ps : Array Expr) : GenM Expr := do
  let (c, cls, qs) ← g.container i ps
  let occ := g.occAt i ps
  let trip := fun (x : Expr) => g.call (g.unpackName i) ps (g.call (g.packName i) ps x)
  let motive ← withLocalDeclD `l occ fun l =>
    mkLambdaFVars #[l] (g.eqi.mk' g.u occ (trip l) l)
  let head : Expr := .const (.str c "rec") (.zero :: cls)
  let cs ← ctorsOf c
  let pre := qs.push motive
  let minors ← withMinorTypes (mkAppN head pre) cs.size fun mtys =>
    (Array.range cs.size).mapM fun t => do
      let cn := cs[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ityp
        let recs := (Array.range n).filter fun x => ftys[x]! == occ
        let mut lhs : Array Expr := #[]
        let mut proofs : Array (Option Expr) := #[]
        for x in [0:n] do
          if let some t := recs.findIdx? (· == x) then
            lhs := lhs.push (trip fields[x]!)
            proofs := proofs.push (some ihs[t]!)
          else if let some o := (Array.range g.occs.size).find? (g.occAt · ps == ftys[x]!) then
            lhs := lhs.push (g.call (g.unpackName o) ps (g.call (g.packName o) ps fields[x]!))
            proofs := proofs.push (some (g.call (g.retractName o) ps fields[x]!))
          else
            lhs := lhs.push fields[x]!
            proofs := proofs.push none
        let rebuild := fun (a : Array Expr) => mkAppN (.const cn cls) (qs ++ a)
        mkLambdaFVars bs (← g.foldCongr occ ftys lhs fields proofs rebuild)
  return mkAppN head (pre ++ minors)

/-- The section's motive at member `k`, applied to `x`. **The round trip only
where the round trip exists**: a mimic this development has not reached yet has
no `pack`, so its motive is reflexivity — which is all its own minors need,
because the emission order is topological and a field at a mimic is always at a
*deeper* one. -/
def sectionMotive (g : Gen) (k : Nat) (ps : Array Expr) (x : Expr)
    (live : Nat → Bool) : Expr :=
  let ty := g.memAt k ps
  if live k then
    let i := g.mimicOf k
    g.eqi.mk' g.u ty (g.call (g.packName i) ps (g.call (g.unpackName i) ps x)) x
  else
    g.eqi.mk' g.u ty x x

/-- `packUnpackᵢ : ∀p⃗ b, Eq (packᵢ p⃗ (unpackᵢ p⃗ b)) b`, by the block's
recursor. -/
def sectionValue (g : Gen) (i member : Nat) (ps : Array Expr) (done : Array Bool) :
    GenM Expr := do
  let live := fun (k : Nat) =>
    !g.isReal k && (g.mimicOf k == i || done[g.mimicOf k]!)
  let motives ← (Array.range g.members.size).mapM fun k =>
    withLocalDeclD `b (g.memAt k ps) fun b =>
      mkLambdaFVars #[b] (g.sectionMotive k ps b live)
  let head : Expr := g.blockRecAt member .zero
  let pre := ps ++ motives
  let pairs := g.ctorPairs
  let minors ← withMinorTypes (mkAppN head pre) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t => do
      let (k, cn) := pairs[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ityp
        let recs := (Array.range n).filter fun x => (g.memberOf ftys[x]!).isSome
        let ty := g.memAt k ps
        let rebuild := fun (a : Array Expr) => g.blockCtorAt k cn ps a
        if !live k then
          mkLambdaFVars bs (g.eqi.refl' g.u ty (rebuild fields))
        else
          let mut lhs : Array Expr := #[]
          let mut proofs : Array (Option Expr) := #[]
          for x in [0:n] do
            match g.memberOf ftys[x]! with
            | some m =>
              if live m then
                let some t := recs.findIdx? (· == x) | badShape "no hypothesis for a member field"
                let o := g.mimicOf m
                lhs := lhs.push
                  (g.call (g.packName o) ps (g.call (g.unpackName o) ps fields[x]!))
                proofs := proofs.push (some ihs[t]!)
              else
                lhs := lhs.push fields[x]!
                proofs := proofs.push none
            | none =>
              lhs := lhs.push fields[x]!
              proofs := proofs.push none
          mkLambdaFVars bs (← g.foldCongr ty ftys lhs fields proofs rebuild)
  return mkAppN head (pre ++ minors)

/-! ### the declared type's own constructors -/

/-- `T._model.ctor_j := fun p⃗ f⃗ => B₀.c p⃗ g⃗`, where a field the block types at a
**mimic** is packed on the way in and everything else passes through. The field
telescope is read off the *export's* declared type, so the parameters this binds
are the ones the export declared and not ones reconstructed here. -/
def ctorValue (g : Gen) (k j : Nat) (realTy : Expr) (ps : Array Expr) : GenM Expr := do
  let cn := g.blockCtors[k]![j]!
  let blkTys ← withFields (← instCtor cn g.us ps) fun _ tys => pure tys
  forallTelescope (← instForall realTy ps) fun fields _ => do
    if fields.size != blkTys.size then
      badShape s!"{cn}: the export declares {fields.size} fields, the block {blkTys.size}"
    let mut args : Array Expr := #[]
    for x in [0:fields.size] do
      match g.memberOf blkTys[x]! with
      | some m =>
        if !g.isReal m then args := args.push (g.call (g.packName (g.mimicOf m)) ps fields[x]!)
        else args := args.push fields[x]!
      | none => args := args.push fields[x]!
    mkLambdaFVars fields (g.blockCtorAt k cn ps args)

/-! ### the recursors -/

/-- **The block's motive vector** — the caller's own at the root, the caller's
composed with `unpack` at each mimic. -/
def blockMotives (g : Gen) (ps motives : Array Expr) : GenM (Array Expr) :=
  (Array.range g.members.size).mapM fun j =>
    if g.isReal j then pure motives[j]!
    else withLocalDeclD `b (g.memAt j ps) fun b =>
      mkLambdaFVars #[b] (mkApp motives[j]! (g.call (g.unpackName (g.mimicOf j)) ps b))

/-- One minor of the block's recursor, built from the caller's own.

The caller's minor wants the fields at their **real** types, so a field the
block holds at a mimic is unpacked on the way in; the induction hypotheses pass
through, because the block's are already at the composed motive. **Only a root
constructor with a packed field transports**, and it transports along
`packUnpack`, one position at a time. -/
def recMinor (g : Gen) (j : Nat) (cn : Name) (mty sT : Expr) (ps motives : Array Expr)
    (v : Level) : GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ityp
    let mut real : Array Expr := #[]
    for x in [0:n] do
      match g.memberOf ftys[x]! with
      | some m =>
        if !g.isReal m then real := real.push (g.call (g.unpackName (g.mimicOf m)) ps fields[x]!)
        else real := real.push fields[x]!
      | none => real := real.push fields[x]!
    let body := mkAppN sT (real ++ ihs)
    if !g.isReal j then
      mkLambdaFVars bs body
    else
      -- The caller's minor lands at `Mⱼ (T._model.ctor f⃗_real)`, which unfolds
      -- to `Mⱼ (Bⱼ.c (pack (unpack f⃗)))`, and the block hands it `Mⱼ (Bⱼ.c f⃗)`.
      let mut lhs : Array Expr := #[]
      let mut proofs : Array (Option Expr) := #[]
      for x in [0:n] do
        match g.memberOf ftys[x]! with
        | some m =>
          if !g.isReal m then
            let o := g.mimicOf m
            lhs := lhs.push
              (g.call (g.packName o) ps (g.call (g.unpackName o) ps fields[x]!))
            proofs := proofs.push (some (g.call (g.sectionName o) ps fields[x]!))
          else
            lhs := lhs.push fields[x]!
            proofs := proofs.push none
        | none =>
          lhs := lhs.push fields[x]!
          proofs := proofs.push none
      let rebuild := fun (a : Array Expr) => g.blockCtorAt j cn ps a
      mkLambdaFVars bs (← g.foldValue v motives[j]! ftys lhs fields proofs rebuild body)

/-- **The block's minor vector**, in the block's own order — every member's
constructors, member by member, which is the order `Bₖ.rec` binds them in and
the order the caller's own minors arrive in. -/
def blockMinors (g : Gen) (ps motives minors : Array Expr) (v : Level) :
    GenM (Array Expr) := do
  let bm ← g.blockMotives ps motives
  let head : Expr := g.blockRecAt 0 v
  let pairs := g.ctorPairs
  withMinorTypes (mkAppN head (ps ++ bm)) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t =>
      g.recMinor pairs[t]!.1 pairs[t]!.2 mtys[t]! minors[t]! ps motives v

/-- **One member's recursor, as the model restates it.** Read once and used by
both the recursor and its ι rules, which share the `np + nm + nmin` binders and
differ only past them. -/
structure RecShape where
  k : Nat
  /-- `Bₖ.rec`, the block's own. -/
  src : Name
  /-- The motive universe, the recursor's single level parameter. -/
  v : Level
  lparams : List Name
  nm : Nat
  nmin : Nat
  /-- The declared type, at the model's names. -/
  ty : Expr
  deriving Inhabited

/-- `Bₖ.rec`'s statement at the model's names — the same table `nested::add`
restores the *export's* recursor with, one set of names along, so
`T._model.rec_k` and `T.rec_k` are the same statement about different
constants. -/
def recShape (g : Gen) (k : Nat) (heads : Std.HashMap Name (Nat × Expr)) :
    GenM RecShape := do
  let src := g.blockRec k
  let .recInfo rv ← constInfo src | badShape s!"{src} is not a recursor"
  if rv.numIndices != 0 then declineWith .indexed
  -- The motive universe first, the block's own after it — and the block's own
  -- are the declaration's, because that is what the block was declared with.
  let lp :: rest := rv.levelParams | badShape s!"{src} has no motive universe"
  unless rest.map Level.param == g.us do
    badShape s!"{src} carries the level parameters {rv.levelParams}"
  if rv.numMotives != g.members.size then badShape s!"{src} has {rv.numMotives} motives"
  return { k, src, v := .param lp, lparams := rv.levelParams
           nm := rv.numMotives, nmin := rv.numMinors, ty := restore heads rv.type }

/-- The value of `T._model.rec_k`: the block's recursor at a **shifted motive
vector** — the caller's own at the root, the caller's composed with `unpack` at
each mimic. At a mimic the major itself has to move: the block eliminates `Bₖ`
and the export eliminates `occₖ`, so the recursor runs at `pack major` and the
result comes back along the **retraction** `unpackPack`. -/
def recValue (g : Gen) (sh : RecShape) : GenM Expr := do
  forallBoundedTelescope sh.ty (some (g.np + sh.nm + sh.nmin + 1)) fun bs _ => do
    let ps := bs.extract 0 g.np
    let motives := bs.extract g.np (g.np + sh.nm)
    let minors := bs.extract (g.np + sh.nm) (g.np + sh.nm + sh.nmin)
    let major := bs[bs.size - 1]!
    let bm ← g.blockMotives ps motives
    let bmin ← g.blockMinors ps motives minors sh.v
    let head : Expr := g.blockRecAt sh.k sh.v
    let pre := ps ++ bm ++ bmin
    let value ←
      if g.isReal sh.k then
        pure (mkAppN head (pre.push major))
      else do
        let o := g.mimicOf sh.k
        let occ := g.occAt o ps
        let pk := g.call (g.packName o) ps major
        let base := mkAppN head (pre.push pk)
        let trip := g.call (g.unpackName o) ps pk
        let mot ← withLocalDeclD `x occ fun x =>
          withLocalDeclD `h (g.eqi.mk' g.u occ trip x) fun h =>
            mkLambdaFVars #[x, h] (mkApp motives[sh.k]! x)
        pure (g.eqi.recAt sh.v g.u occ trip mot base major
          (g.call (g.retractName o) ps major))
    mkLambdaFVars bs value

/-! ### the congruence the ι rules are stated along -/

/-- **`congrPackᵢ : ∀p⃗ l₀ l, Eq l₀ l → Eq (packᵢ l₀) (packᵢ l)`.**

Needed for a reason that is not obvious. The ι rule of a **root** constructor
with a packed field has, on its left, the transport `recₖ`'s minor performs —
along `packUnpack (pack f)`. Proving it means `Eq.rec` on `unpackPack f`, whose
motive has to name a proof of `Eq (pack (unpack (pack f))) (pack x)` for the
abstracted `x`, and only a *congruence* of `pack` is that. Proof irrelevance
then identifies the two at `x := f`, which is where the triangle identity would
otherwise have to be proved. -/
def congrPackDecl (g : Gen) (i : Nat) (ps : Array Expr) : GenM (Expr × Expr) := do
  let occ := g.occAt i ps
  let mem := g.memAt (i + g.numAll) ps
  let pk := fun (x : Expr) => g.call (g.packName i) ps x
  withLocalDeclD `l0 occ fun l0 => withLocalDeclD `l occ fun l =>
    withLocalDeclD `h (g.eqi.mk' g.u occ l0 l) fun h => do
      let tel := (ps.push l0).push l |>.push h
      let ty ← mkForallFVars tel (g.eqi.mk' g.u mem (pk l0) (pk l))
      let mot ← withLocalDeclD `x occ fun x =>
        withLocalDeclD `hx (g.eqi.mk' g.u occ l0 x) fun hx =>
          mkLambdaFVars #[x, hx] (g.eqi.mk' g.u mem (pk l0) (pk x))
      let base := g.eqi.refl' g.u mem (pk l0)
      let val ← mkLambdaFVars tel (g.eqi.recAt .zero g.u occ l0 mot base l h)
      return (ty, val)

end Gen

/-! ## The ι rules -/

/-- Where one packed position of a rule stands in the transport fold. -/
inductive Move where
  /-- At `unpackᵢ (packᵢ f)`, where the reduced left-hand side leaves it. -/
  | source
  /-- At `f`, having been transported along `unpackPackᵢ f`. -/
  | target
  /-- At the motive's own variable, along the motive's own equation — the
  position this step of the fold is abstracting. -/
  | abstract (x hx : Expr)
  deriving Inhabited

/-- **One ι rule of `T._model.rec_k`, under construction.**

The theorem's binder telescope is the recursor's own — `p⃗ M⃗ S⃗` — with the
constructor's **export-side** fields on the end, so a rule of `rec_1` binds
`List Tree`'s fields and not the mimic's. -/
structure Rule where
  g : Gen
  k : Nat
  v : Level
  ps : Array Expr
  motives : Array Expr
  minors : Array Expr
  /-- This constructor's minor, in the block-wide order. -/
  minorIx : Nat
  /-- The export-side constructor as it is applied: `T._model.ctor_j` at the
  root, or the real container's constructor at a mimic. -/
  head : Name
  headLevels : List Level
  headPrefix : Array Expr
  /-- The export-side fields the theorem binds, and their types. -/
  fields : Array Expr
  extTys : Array Expr
  /-- The block constructor's name and its field types. -/
  bcn : Name
  blkTys : Array Expr
  /-- Which block member each field sits at, if any. -/
  mem : Array (Option Nat)
  /-- The fields at a **mimic**, in order — the positions the fold moves. -/
  moving : Array Nat

namespace Rule

def n (r : Rule) : Nat := r.fields.size

/-- The export-side constructor applied to `vals`. -/
def build (r : Rule) (vals : Array Expr) : Expr :=
  mkAppN (.const r.head r.headLevels) (r.headPrefix ++ vals)

/-- `T._model.rec_m p⃗ M⃗ S⃗ x`. -/
def recCall (r : Rule) (m : Nat) (x : Expr) : Expr :=
  mkAppN (.const (r.g.recName m) (r.v :: r.g.us)) (r.ps ++ r.motives ++ r.minors ++ #[x])

/-- `p⃗ M''⃗ S''⃗` — everything a block recursor takes before its major. -/
def blkPrefix (r : Rule) : GenM (Array Expr) := do
  let bm ← r.g.blockMotives r.ps r.motives
  let bmin ← r.g.blockMinors r.ps r.motives r.minors r.v
  return r.ps ++ bm ++ bmin

/-- `congrPack_o p⃗ l₀ l h`. -/
def congrPack (r : Rule) (o : Nat) (l0 l h : Expr) : Expr :=
  mkAppN (.const (r.g.congrPackName o) r.g.us) (r.ps ++ #[l0, l, h])

/-- **The two sides at one stage of the fold** — the type they live at, the
left, and the right.

The left is the *reduced* left: the recursor unfolded, the block's ι rule fired
and the minor β-reduced, which at the root is a chain of transports over `pack`
and at a mimic is one transport of the whole constructor application. The right
is the rule, with each moved position's induction hypothesis at
`T._model.rec_m`. -/
def sides (r : Rule) (mv : Array Move) : GenM (Expr × Expr × Expr) := do
  let g := r.g
  let blk ← if r.moving.isEmpty then pure #[] else r.blkPrefix
  let mut srcVals : Array Expr := #[]
  let mut srcIhs : Array Expr := #[]
  let mut vals : Array Expr := #[]
  let mut ihs : Array Expr := #[]
  for x in [0:r.n] do
    let f := r.fields[x]!
    match r.mem[x]! with
    | none =>
      srcVals := srcVals.push f
      vals := vals.push f
    -- A field at a **real** member does not move: `pack` passes it through, so
    -- both sides hold it at `f` and its hypothesis is `T._model.rec_m` on the
    -- nose.
    | some m =>
      if g.isReal m then
        let ih := r.recCall m f
        srcVals := srcVals.push f; srcIhs := srcIhs.push ih
        vals := vals.push f; ihs := ihs.push ih
      else
        let o := g.mimicOf m
        let pk := g.call (g.packName o) r.ps f
        let y := g.call (g.unpackName o) r.ps pk
        let w := mkAppN (g.blockRecAt m r.v) (blk.push pk)
        srcVals := srcVals.push y; srcIhs := srcIhs.push w
        match mv[x]! with
        | .source =>
          vals := vals.push y; ihs := ihs.push w
        -- Already moved: the value is the field and the hypothesis is
        -- `T._model.rec_m` at it, which δ-unfolds to exactly the transport the
        -- step below produced.
        | .target =>
          vals := vals.push f; ihs := ihs.push (r.recCall m f)
        -- Being moved: the value is the motive's own variable and the transport
        -- is along its equation. At `x := y` and `hx := Eq.refl` this ι-reduces
        -- back to `w`, which is what makes the previous stage this step's base.
        | .abstract xv hv =>
          let occ := g.occAt o r.ps
          let mot ← mkLambdaFVars #[xv, hv] (mkApp r.motives[m]! xv)
          ihs := ihs.push (g.eqi.recAt r.v g.u occ y mot w xv hv)
          vals := vals.push xv
  let apply := fun (vs is : Array Expr) => mkAppN r.minors[r.minorIx]! (vs ++ is)
  let base := apply srcVals srcIhs
  let rhs := apply vals ihs
  let ty := mkApp r.motives[r.k]! (r.build vals)
  let lhs ←
    if g.isReal r.k then do
      -- A real member's minor lands at `M_k (T._model.ctor_j f⃗)`, which unfolds
      -- to `M_k (B_k.c (pack (unpack f⃗)))`, and the block hands it
      -- `M_k (B_k.c f⃗)`.
      let mut blLhs : Array Expr := #[]
      let mut blRhs : Array Expr := #[]
      let mut proofs : Array (Option Expr) := #[]
      for x in [0:r.n] do
        match r.mem[x]! with
        | some m =>
          if !g.isReal m then
            let o := g.mimicOf m
            blLhs := blLhs.push (g.call (g.packName o) r.ps srcVals[x]!)
            blRhs := blRhs.push (g.call (g.packName o) r.ps vals[x]!)
            proofs := proofs.push <|
              match mv[x]! with
              | .source => none
              | .target =>
                some (r.congrPack o srcVals[x]! vals[x]!
                  (g.call (g.retractName o) r.ps r.fields[x]!))
              | .abstract xv hv => some (r.congrPack o srcVals[x]! xv hv)
          else
            blLhs := blLhs.push vals[x]!
            blRhs := blRhs.push vals[x]!
            proofs := proofs.push none
        | none =>
          blLhs := blLhs.push vals[x]!
          blRhs := blRhs.push vals[x]!
          proofs := proofs.push none
      let rebuild := fun (a : Array Expr) => g.blockCtorAt r.k r.bcn r.ps a
      g.foldValue r.v r.motives[r.k]! r.blkTys blLhs blRhs proofs rebuild base
    else do
      -- A mimic's rule transports the **whole** constructor application: `recₖ`
      -- runs at `packᵢ (c f⃗)` and comes back along `unpackPackᵢ (c f⃗)`, whose
      -- reduct is the congruence of `c` over the packed positions.
      let i := g.mimicOf r.k
      let occ := g.occAt i r.ps
      let a0 := r.build srcVals
      let b0 := r.build vals
      let proofs := (Array.range r.n).map fun x =>
        match r.mem[x]! with
        | some m =>
          if !g.isReal m then
            match mv[x]! with
            | .source => none
            | .target => some (g.call (g.retractName (g.mimicOf m)) r.ps r.fields[x]!)
            | .abstract _ hv => some hv
          else none
        | none => none
      let p ← g.foldCongr occ r.extTys srcVals vals proofs r.build
      let mot ← withLocalDeclD `x occ fun xv =>
        withLocalDeclD `hx (g.eqi.mk' g.u occ a0 xv) fun hv =>
          mkLambdaFVars #[xv, hv] (mkApp r.motives[r.k]! xv)
      pure (g.eqi.recAt r.v g.u occ a0 mot base b0 p)
  return (ty, lhs, rhs)

/-- **The equation**: `Eq (recₖ p⃗ M⃗ S⃗ (c f⃗)) (Sⱼ f⃗ ih⃗)`, at the recursor's own
motive universe. Free of the fold: each induction hypothesis is the model's
**constant** `T._model.rec_m` rather than its unfolding, because that is what
the export's own rule says and what the keying will read. -/
def statement (r : Rule) : Expr :=
  let all := r.fields
  let ihs := (Array.range r.n).filterMap fun x =>
    (r.mem[x]!).map fun m => r.recCall m all[x]!
  let major := r.build all
  let ty := mkApp r.motives[r.k]! major
  r.g.eqi.mk' r.v ty (r.recCall r.k major) (mkAppN r.minors[r.minorIx]! (all ++ ihs))

/-- The proof: `Eq.refl` with nothing to move, and otherwise one `Eq.rec` on
`unpackPackᵢ f` per packed position, from a base where every one of them is
still at the source and both sides are the same term. -/
def value (r : Rule) : GenM Expr := do
  let g := r.g
  let mut mv := Array.replicate r.n Move.source
  let (ty0, _, rhs0) ← r.sides mv
  let mut acc := g.eqi.refl' r.v ty0 rhs0
  for x in r.moving do
    let some m := r.mem[x]! | badShape "a moving position with no member"
    let o := g.mimicOf m
    let f := r.fields[x]!
    let y := g.call (g.unpackName o) r.ps (g.call (g.packName o) r.ps f)
    let h := g.call (g.retractName o) r.ps f
    let occ := g.occAt o r.ps
    -- The motive is the whole equation with this position abstracted; at
    -- `x := unpackᵢ (packᵢ f)` and `hx := Eq.refl` every transport it
    -- introduced ι-reduces away and what is left is the accumulator's own type.
    let mot ← withLocalDeclD `x occ fun xv =>
      withLocalDeclD `hx (g.eqi.mk' g.u occ y xv) fun hv => do
        let (ty2, l2, r2) ← r.sides (mv.set! x (.abstract xv hv))
        mkLambdaFVars #[xv, hv] (g.eqi.mk' r.v ty2 l2 r2)
    acc := g.eqi.recAt .zero g.u occ y mot acc f h
    mv := mv.set! x Move.target
  return acc

end Rule

/-! ## The driver -/

/-- Everything one nested declaration's model came to. -/
structure Iso where
  /-- Every generated declaration, in dependency order and already accepted. -/
  decls : Array Declaration
  /-- The declaration's own level parameters — the export's, in the export's
  order. Every generated constant carries these; a recursor and its ι theorems
  carry their motive universe in front of them. -/
  levelParams : List Name
  /-- The block's members: the export's own in `all` order, then the mimics. -/
  members : Array Name
  /-- `R_k._model.self` per **real** member, in `all` order. One unless the
  declaration is a mutual block. -/
  selfNames : Array Name
  /-- How many of `members` are the export's own. -/
  numAll : Nat
  /-- `(the export's constructor, the model's)`, in declaration order. -/
  ctors : Array (Name × Name)
  /-- `T._model.rec_k`, in member order. -/
  recs : Array Name
  /-- `(member, the rule's constructor as the export names it, the theorem)`. -/
  iotas : Array (Nat × Name × Name)
  deriving Inhabited

def hintsFor (v : Expr) : GenM ReducibilityHints := do
  return .regular (getMaxHeight (← getEnv) v + 1)

/-- Add a generated declaration, **with checking**. A proof this module builds
and the kernel rejects is a decline, never an emission. -/
def addChecked (d : Declaration) : GenM Unit := do
  match (← getEnv).addDeclCore 0 d none true with
  | .ok e => setEnv e
  | .error ex =>
    badShape s!"{d.getTopLevelNames} rejected by the kernel: {← (ex.toMessageData {}).toString}"

/-- **The ι rules of one member's recursor**, one per rule `Bₖ.rec` carries, in
the order it carries them.

Each comes back as `(the export's constructor, the theorem's name, the
theorem)`. The constructor is the key the *installed* `T.rec_k` files its rule
under — `Tree.node` at the root, `List.cons` at a mimic — so a consumer can line
the two up without knowing how the block was named. -/
def Gen.iotaDecls (g : Gen) (sh : Gen.RecShape) (ctorTys : Array (Name × Name × Expr)) :
    GenM (Array (Name × Name × Declaration)) := do
  let minorBase := (Array.range sh.k).foldl (fun a i => a + g.blockCtors[i]!.size) 0
  -- The export's constructors are flattened in `all` order, so a **real**
  -- member's `j`-th is at this offset; a mimic's key is the real container's.
  let ctorBase := (Array.range (min sh.k g.numAll)).foldl
    (fun a i => a + g.blockCtors[i]!.size) 0
  let cs := g.blockCtors[sh.k]!
  (Array.range cs.size).mapM fun j =>
    forallBoundedTelescope sh.ty (some (g.np + sh.nm + sh.nmin)) fun pre _ => do
      let ps := pre.extract 0 g.np
      let motives := pre.extract g.np (g.np + sh.nm)
      let minors := pre.extract (g.np + sh.nm) pre.size
      let bcn := cs[j]!
      let blkTys ← withFields (← instCtor bcn g.us ps) fun _ tys => pure tys
      let mem := blkTys.map g.memberOf
      -- **A recursive field the head of whose type is not a member is one this
      -- module cannot write.** `Bₖ.rec`'s rule gives an induction hypothesis to
      -- a field of type `∀ …, Bₘ …` as well, and the right-hand side below has
      -- none for it, so the statement would be a different equation from the
      -- one the recursor obeys. A decline rather than a wrong theorem.
      --
      -- Recursiveness is read the way Lean reads it — after `whnf`, through
      -- the `∀` telescope — and not by asking whether a member is *mentioned*.
      -- `Ctr.mk : (x : α) → P x → Ctr α P` at `Ctr KTree (fun _ => N)` gives
      -- the block a field `(fun x : B₀ => N) x`, which mentions `B₀` in a
      -- binder it discards and gets no induction hypothesis;
      -- `dependent_fields.lean`'s `KTree` is that fixture.
      for x in [0:blkTys.size] do
        if (mem[x]!).isNone then
          let isRec ← forallTelescope (← whnf blkTys[x]!) fun _ res => do
            return (g.memberOf (← whnf res)).isSome
          if isRec then badShape s!"{bcn} has a recursive field under a binder"
      let key : Name × Name × List Level × Array Expr × Expr ←
        if g.isReal sh.k then do
          let (exportC, modelC, mty) := ctorTys[ctorBase + j]!
          pure (exportC, modelC, g.us, ps, ← instForall mty ps)
        else do
          let real ← g.realCtor (g.mimicOf sh.k) ps bcn
          let (_, cls, qs) ← g.container (g.mimicOf sh.k) ps
          pure (real, real, cls, qs, ← instCtor real cls qs)
      let (exportKey, head, hls, hpre, ectorTy) := key
      withFields ectorTy fun fields extTys => do
        if fields.size != blkTys.size then
          badShape s!"{bcn}: the export binds {fields.size} fields, the block {blkTys.size}"
        let moving := (Array.range blkTys.size).filter fun x =>
          match mem[x]! with | some m => !g.isReal m | none => false
        let r : Rule :=
          { g, k := sh.k, v := sh.v, ps, motives, minors, minorIx := minorBase + j
            head, headLevels := hls, headPrefix := hpre
            fields, extTys, bcn, blkTys, mem, moving }
        let tel := pre ++ fields
        let ty ← mkForallFVars tel r.statement
        let val ← mkLambdaFVars tel (← r.value)
        let nm := g.iotaName sh.k j
        return (exportKey, nm,
          .thmDecl { name := nm, levelParams := sh.lparams, type := ty, value := val })

/-- **Build the model, or say which shape stopped it.**

The whole of the checker interaction is [`Modelgen.addChecked`], once per
generated declaration. Nothing is emitted unchecked. -/
def iso (all : Array Name) (lparams : List Name) (numParams : Nat)
    (exportCtors : Array (Array (Name × Expr))) (pl : Plan)
    (reserved : Std.HashSet Name) : GenM Iso := do
  -- **The declaration's own level parameters are carried, not refused.** Every
  -- generated constant is declared at `lparams` and referenced at `us`; a
  -- recursor is declared at its motive universe *followed by* `lparams`, which
  -- is the order Lean itself writes. `poly_nested.lean` is the fixture, and it
  -- is arranged so that a generator writing a container's *declared* parameter
  -- where the occurrence's instantiation belongs cannot pass.
  let us := lparams.map Level.param
  let np := numParams
  let r := pl.numAll
  let some root := all[0]? | badShape "the declaration has no members"
  let some rootT := pl.types[0]? | badShape "the plan has no members"
  -- The block's resultant sort; anything left over after the parameters is an
  -- index telescope this module does not write. **Every real member's, not
  -- just the first's**: a mutual block whose members land at different sorts
  -- would give `Eq` two universes and one `g.u` to write them at.
  let sortOf : Expr → GenM Level := fun t => do
    let mut cur := t
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => badShape "the declaration has fewer binders than parameters"
    let .sort u := cur | declineWith .indexed
    return u
  let u ← sortOf rootT.type
  for k in [0:r] do
    unless (← sortOf pl.types[k]!.type) == u do
      badShape "a mutual block whose members land at different sorts"
  let model := Name.str root "_model"
  let b := fun (i : Nat) => Name.num model i
  -- **One carrier per real member.** `A.rec` and `B.rec` are distinct
  -- recursors over distinct majors, and a consumer keys `⟦A⟧` and `⟦B⟧`
  -- separately; a single carrier could stand for only one of them. For a
  -- one-member block this is `T._model.self` and nothing has moved.
  let selfNames := all.extract 0 r |>.map fun n => Name.str (Name.str n "_model") "self"
  -- **The whole file, not just the prefix.** `mini/tests/fixtures/nested_
  -- keying.lean` declares `UTree._model.self` itself, *after* `UTree`, exactly
  -- so that a consumer keying on the convention is not fooled by it. A guard
  -- that only looked at the environment as it stands would generate a second
  -- `UTree._model.self` and emit an export with a duplicate declaration.
  let taken : Name → GenM Unit := fun n => do
    if reserved.contains n || (← getEnv).constants.contains n then declineWith (.nameTaken n)
  for i in [0:pl.types.size] do taken (b i)
  for n in selfNames do taken n
  let eqi ← match EqInfo.read (← getEnv) with
    | .ok e => pure e
    | .error d => declineWith d
  let mut out : Array Declaration := #[]

  -- ── 1. the block, renamed ──────────────────────────────────────────────
  --
  -- Member 0 is the export's own `T` and must not keep that name: `T` is a
  -- primitive inductive in the caller's environment and this development is
  -- about a different constant.
  let ren : Std.HashMap Name (Nat × Expr) :=
    (Array.range pl.types.size).foldl
      (fun m i => m.insert pl.types[i]!.name (0, .const (b i) us)) {}
  let blockCtors := (Array.range pl.types.size).map fun i =>
    pl.types[i]!.ctors.map fun (cn, _) => Name.str (b i) (lastStr cn)
  let its : List InductiveType := (Array.range pl.types.size).toList.map fun i =>
    { name := b i, type := pl.types[i]!.type
      ctors := (Array.range pl.types[i]!.ctors.size).toList.map fun j =>
        { name := blockCtors[i]![j]!, type := restore ren pl.types[i]!.ctors[j]!.2 } }
  let blockDecl := Declaration.inductDecl lparams np its false
  addChecked blockDecl
  out := out.push blockDecl

  -- ── 2. the carriers, one per real member ───────────────────────────────
  let b0ty := (← constInfo (b 0)).type
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope b0ty (some np) fun ps _ => k ps
  for k in [0:r] do
    let carrier ← withParams fun ps => mkLambdaFVars ps (mkAppN (.const (b k) us) ps)
    let selfDecl := Declaration.defnDecl
      { name := selfNames[k]!, levelParams := lparams, type := pl.types[k]!.type, value := carrier
        hints := ← hintsFor carrier, safety := .safe }
    addChecked selfDecl
    out := out.push selfDecl

  -- Every occurrence, with the export's own members rewritten to their carriers.
  let toSelf : Std.HashMap Name (Nat × Expr) :=
    (Array.range r).foldl (fun m k => m.insert all[k]! (0, .const selfNames[k]! us)) {}
  let occs := pl.mimics.map fun m => restore toSelf m.occ
  let g : Gen := { model, selfNames, numAll := r, np, u, us
                   members := (Array.range pl.types.size).map b
                   blockCtors, occs, eqi }

  -- **The emission order is topological, and that has to be checked.**
  -- `nested_ev.rs` asserts it instead — "nesting strictly decreases, so this is
  -- a topological order and a cycle cannot arise" — and that is false for a
  -- container which is *itself* a nested inductive.
  -- `modelgen/tests/nest_through_nested.lean` is the witness: `T` nests into
  -- `Tree T`, `Tree`'s own `node` field is `List (Tree T)`, and *that* copy's
  -- `cons` head is `Tree T` again, so `pack₀` and `pack₁` call each other.
  -- A cycle here is a genuine limitation, not a bad ordering.
  for i in [0:pl.mimics.size] do
    for (_, cty) in pl.types[i + r]!.ctors do
      for j in [0:i] do
        if mentions pl.mimics[j]!.name cty then declineWith .cyclicMimics

  -- **Dependent fields, checked once and only where they bite.** Every
  -- congruence fold in this file moves the *packed* positions of one of the
  -- block's constructors, so the condition is the same for all of them and is
  -- settled here rather than at each telescope: no field's type may mention an
  -- earlier field the block holds at a mimic. See [`Modelgen.noDepOnPacked`].
  discard <| withParams fun ps => do
    for k in [0:pl.types.size] do
      for cn in blockCtors[k]! do
        forallTelescope (← instCtor cn us ps) fun fs _ => do
          let tys ← fs.mapM ityp
          let packed := (Array.range fs.size).filterMap fun x =>
            match g.memberOf tys[x]! with
            | some m => if m > 0 then some fs[x]! else none
            | none => none
          noDepOnPacked packed fs tys

  -- ── 3. pack, unpack, and the two round trips, per mimic ────────────────
  --
  -- Deeper mimics first: `packᵢ` for a container whose field is another
  -- occurrence calls that occurrence's `pack`, and discovery order puts the
  -- deeper one later. Nesting strictly decreases, so this is a topological
  -- order and a cycle cannot arise.
  let mut done := Array.replicate pl.mimics.size false
  for ii in [0:pl.mimics.size] do
    let i := pl.mimics.size - 1 - ii
    let member := i + r
    for n in [g.packName i, g.unpackName i, g.retractName i, g.sectionName i] do taken n
    let four ← withParams fun ps => do
      let occ := g.occAt i ps
      let mem := g.memAt member ps
      let packTy ← mkForallFVars ps (.forallE `l occ mem .default)
      let packVal ← mkLambdaFVars ps (← g.packValue i member ps)
      let unpackTy ← mkForallFVars ps (.forallE `b mem occ .default)
      let unpackVal ← mkLambdaFVars ps (← g.unpackValue member ps)
      let retTy ← withLocalDeclD `l occ fun l =>
        mkForallFVars (ps.push l)
          (eqi.mk' u occ (g.call (g.unpackName i) ps (g.call (g.packName i) ps l)) l)
      let retVal ← mkLambdaFVars ps (← g.retractValue i ps)
      let secTy ← withLocalDeclD `b mem fun x =>
        mkForallFVars (ps.push x)
          (eqi.mk' u mem (g.call (g.packName i) ps (g.call (g.unpackName i) ps x)) x)
      let secVal ← mkLambdaFVars ps (← g.sectionValue i member ps done)
      return #[(g.packName i, packTy, packVal, false), (g.unpackName i, unpackTy, unpackVal, false),
               (g.retractName i, retTy, retVal, true), (g.sectionName i, secTy, secVal, true)]
    for (nm, ty, val, isThm) in four do
      let hint ← hintsFor val
      let d : Declaration :=
        if isThm then .thmDecl { name := nm, levelParams := lparams, type := ty, value := val }
        else .defnDecl { name := nm, levelParams := lparams, type := ty, value := val
                         hints := hint, safety := .safe }
      addChecked d
      out := out.push d
    done := done.set! i true

  -- ── 4. the declared type's own constructors ────────────────────────────
  --
  -- After the maps, because a field at a mimic is packed on the way in. The
  -- model's constructor carries the **export's** declared type with `T`
  -- rewritten to the carrier, so that the keying is an alias.
  --
  -- **Flattened over the real members, in the export's `all` order**: for a
  -- mutual block `T._model.ctor_j` runs over `A`'s constructors and then `B`'s,
  -- which is the order the block's minors arrive in.
  let mut ctors : Array (Name × Name) := #[]
  let mut ctorTys : Array (Name × Name × Expr) := #[]
  for k in [0:r] do
    for jj in [0:exportCtors[k]!.size] do
      let (cn, cty) := exportCtors[k]![jj]!
      let j := ctorTys.size
      let nm := g.ctorName j
      taken nm
      let ty := restore toSelf cty
      let val ← withParams fun ps => do mkLambdaFVars ps (← g.ctorValue k jj ty ps)
      let d := Declaration.defnDecl
        { name := nm, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d
      ctors := ctors.push (cn, nm)
      ctorTys := ctorTys.push (cn, nm, ty)

  -- ── 5. one recursor per block member ───────────────────────────────────
  let mut heads : Std.HashMap Name (Nat × Expr) := {}
  for k in [0:r] do
    heads := heads.insert (b k) (0, .const selfNames[k]! us)
  for k in [0:r] do
    let base := (Array.range k).foldl (fun a i => a + exportCtors[i]!.size) 0
    for jj in [0:exportCtors[k]!.size] do
      heads := heads.insert (Name.str (b k) (lastStr exportCtors[k]![jj]!.1))
        (0, .const (g.ctorName (base + jj)) us)
  for i in [0:pl.mimics.size] do
    heads := heads.insert (b (i + r)) (np, occs[i]!)
    for (mc, real) in pl.mimics[i]!.ctors do
      -- The real constructor's own parameters mention the **export's** members,
      -- because the mimic table is built before the model exists.
      heads := heads.insert (Name.str (b (i + r)) (lastStr mc)) (np, restore toSelf real)
  for k in [0:pl.types.size] do
    taken (g.recName k)
    heads := heads.insert (Name.str (b k) "rec") (0, .const (g.recName k) us)
  let mut shapes : Array Gen.RecShape := #[]
  for k in [0:pl.types.size] do
    let sh ← g.recShape k heads
    let val ← g.recValue sh
    let d := Declaration.defnDecl
      { name := g.recName k, levelParams := sh.lparams, type := sh.ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d
    shapes := shapes.push sh

  -- ── 6. the congruences the ι rules are stated along ────────────────────
  for i in [0:pl.mimics.size] do
    taken (g.congrPackName i)
    let (ty, val) ← withParams fun ps => g.congrPackDecl i ps
    let d := Declaration.thmDecl
      { name := g.congrPackName i, levelParams := lparams, type := ty, value := val }
    addChecked d
    out := out.push d

  -- ── 7. the ι rules themselves ──────────────────────────────────────────
  let mut iotas : Array (Nat × Name × Name) := #[]
  for k in [0:shapes.size] do
    for (key, nm, d) in ← g.iotaDecls shapes[k]! ctorTys do
      taken nm
      addChecked d
      out := out.push d
      iotas := iotas.push (k, key, nm)

  return { decls := out, levelParams := lparams, members := g.members, selfNames
           numAll := r, ctors
           recs := (Array.range pl.types.size).map g.recName, iotas }

end Modelgen
