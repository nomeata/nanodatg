import Modelgen.Format

/-!
# `monomorph` — universe levels, removed from an export

The pass duplicates each declaration once per **ground instantiation** it is
used at, substitutes numerals for its universe parameters, and rewrites every
constant occurrence to name the copy it means. The output's level parameters
are gone: every `Sort` is `Sort n` for a numeral `n`, and every constant is
used at no levels at all — with two exceptions, both named in `MONOMORPH.md`
and both deliberate: mode A's recursors keep their elimination universe, and
the built-ins are carried through untouched.

The contract a consumer is written against is `MONOMORPH.md` §1. What is
written here is the implementation of it.

## Why this is a single backward pass and not a fixpoint

An export file is topologically sorted: a declaration can only mention
declarations that appear before it. Walking the file **backwards** therefore
reaches `d` only after every user of `d`, so `d`'s set of demanded
instantiations is complete when it is read, and emitting `d`'s copies pushes
demand only onto declarations that are still ahead in the walk. No revisiting,
no fixpoint, and termination is the length of the file.

Topological sortedness is a property of the exporter and not of the format, so
[`checkOrder`] **asserts** it rather than assuming it; a file that violates it
is refused by name and index rather than silently under-instantiated.

The DAG is over declaration **groups**, not declarations: an inductive block,
its constructors and its recursors mention one another cyclically, and so do
the members of a mutual `def` block. A group is one node, collects one demand
set, and is emitted whole.
-/

open Lean Meta

namespace Modelgen
namespace Mono

/-- One ground instantiation: a natural number per universe parameter, in the
declaration's own parameter order. -/
abbrev Inst := Array Nat

/-- Which recursor treatment, and what an unused declaration defaults to. -/
structure Opts where
  /-- **Mode B.** Substitute a numeral for the recursor's elimination universe
  too, so the output has no level parameter anywhere. The result is not
  acceptable to a kernel that mints recursors itself. -/
  monoRecursors : Bool := false
  /-- The instantiations a declaration nothing demands is emitted at. -/
  defaults : Array Nat := #[0]
  /-- Replay the **output** with the kernel's checking on. Mode A's oracle. -/
  check : Bool := false
  deriving Inhabited

/-! ## The naming scheme

`MONOMORPH.md` §1 is the contract; this is the code it describes. -/

/-- `succ^n zero`. -/
def natLevel : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (natLevel n)

/-- The marker: a `Name.str` component `_at`, then one `Name.num` per level. -/
def atName (base : Name) (σ : Inst) : Name :=
  σ.foldl (fun n k => .num n k) (.str base "_at")

/-- `full` at `σ`, where `owner` is the prefix that carries the marker. Empty
`σ` is the identity, so a monomorphic declaration keeps its name exactly. -/
def monoName (owner full : Name) (σ : Inst) : Name :=
  if σ.isEmpty then full else full.replacePrefix owner (atName owner σ)

/-- Mode B's suffix for a recursor at elimination universe `w`. -/
def elimName (n : Name) (w : Nat) : Name := .num (.str n "_elim") w

/-- Whether any component of `n` spells one of the two markers. A file that
already uses one is refused: the scheme would not be invertible on it. -/
def usesMarker : Name → Bool
  | .anonymous => false
  | .num p _ => usesMarker p
  | .str p s => s == "_at" || s == "_elim" || usesMarker p

/-! ## Groups -/

/-- What the pass needs to know about one name the file introduces. -/
structure Info where
  /-- The group that declares it. -/
  group : Nat
  /-- The prefix the `_at` marker is inserted after. For a block member it is
  the member itself; for a constructor its inductive; for a recursor the member
  in whose namespace it lives. -/
  owner : Name
  /-- A recursor's own elimination universe, when it has one. -/
  elim : Option Name := none
  deriving Inhabited

/-- One node of the declaration DAG. -/
structure Group where
  /-- Indices into `Export.decls`, in file order. -/
  decls : Array Nat := #[]
  /-- The level parameters every member of the group shares. -/
  levelParams : List Name := []
  isInd : Bool := false
  /-- The block's elimination universes, one per recursor that has one. -/
  elims : Array Name := #[]
  deriving Inhabited

/-- The names one record introduces, paired with the owner each is renamed
under. -/
def introOf (d : EDecl) : Array (Name × Name × Option Name) :=
  match d with
  | .ax n .. | .defn n .. | .thm n .. | .opaq n .. | .quot n .. => #[(n, n, none)]
  | .induct ts cs rs => Id.run do
    let members := ts.toArray.map (·.name)
    let blockLp := match ts with | t :: _ => t.levelParams | [] => []
    let mut out : Array (Name × Name × Option Name) := #[]
    for t in ts do out := out.push (t.name, t.name, none)
    for c in cs do out := out.push (c.name, c.induct, none)
    for r in rs do
      -- The longest member name that is a prefix of the recursor's: a real
      -- member's recursor lives in its own namespace, a mimic's in the first
      -- member's (`nest_mutual_both` measured that).
      let mut owner := members[0]!
      for m in members do
        if m.isPrefixOf r.name && owner.getNumParts ≤ m.getNumParts then owner := m
      let elim := r.levelParams.filter (fun p => !blockLp.contains p)
      out := out.push (r.name, owner, elim.head?)
    return out

/-- Partition the file into groups and index every name it introduces.

An inductive record is one group. A `def`/`thm`/`opaque` record joins the group
of any name in its `all` field that has been seen, and starts a new one
otherwise. -/
def buildGroups (x : Export) : Except String (Array Group × Std.HashMap Name Info) := do
  let mut groups : Array Group := #[]
  let mut info : Std.HashMap Name Info := {}
  -- A name promised by an earlier record's `all` field, and the group it joins.
  let mut promised : Std.HashMap Name Nat := {}
  for i in [0 : x.decls.size] do
    let d := x.decls[i]!
    let lp := match d with
      | .ax _ lp .. | .defn _ lp .. | .thm _ lp .. | .opaq _ lp .. | .quot _ lp .. => lp
      | .induct ts _ _ => match ts with | t :: _ => t.levelParams | [] => []
    -- The block's level parameters must be shared, or the group cannot be
    -- instantiated as one.
    match d with
    | .induct ts cs rs =>
      for t in ts do
        unless t.levelParams == lp do
          throw s!"{t.name}: an inductive block whose members differ in their level parameters"
      for c in cs do
        unless c.levelParams == lp do
          throw s!"{c.name}: a constructor whose level parameters are not its block's"
      for r in rs do
        unless (r.levelParams.filter (fun p => !lp.contains p)).length ≤ 1 do
          throw s!"{r.name}: a recursor with more than one elimination universe"
    | _ => pure ()
    -- **A duplicate universe parameter is a lie monomorphization would erase.**
    -- `vendor/arena-tests/bad/tutorial/016_tut06_bad01.ndjson` declares
    -- `tut06_bad01.{u, u}`; nanoda's `no_dupes_all_params` rejects it, and the
    -- copy at `σ` has no parameters at all and is perfectly well typed. The
    -- pass must not launder that, so it refuses the file.
    unless lp.eraseDups.length == lp.length do
      throw s!"{d.names}: a duplicate universe parameter in {lp}"
    let allF := match d with
      | .defn _ _ _ _ _ _ a | .thm _ _ _ _ a | .opaq _ _ _ _ _ a => a
      | _ => []
    let gi := match allF.findSome? (promised[·]?) with
      | some g => g
      | none => groups.size
    if gi == groups.size then groups := groups.push {}
    let g := groups[gi]!
    -- A joined record must agree on the level parameters, for the same reason.
    unless g.decls.isEmpty || g.levelParams == lp do
      throw s!"{d.names}: a mutual block whose members differ in their level parameters"
    let mut elims := g.elims
    if let .induct _ _ rs := d then
      for r in rs do
        for p in r.levelParams do
          unless lp.contains p || elims.contains p do elims := elims.push p
    groups := groups.set! gi
      { decls := g.decls.push i, levelParams := lp
        isInd := g.isInd || (match d with | .induct .. => true | _ => false)
        elims }
    for (n, owner, elim) in introOf d do
      info := info.insert n { group := gi, owner, elim }
    for n in allF do promised := promised.insert n gi
  return (groups, info)

/-! ## Levels -/

/-- Substitute the instantiation into a level and simplify. A parameter the
instantiation does not bind — mode A's elimination universe, or any parameter
of a carried declaration — is left standing. -/
partial def substLevel (env : Std.HashMap Name Nat) : Level → Level
  | .zero => .zero
  | .succ a => .succ (substLevel env a)
  | .max a b => mkLevelMax' (substLevel env a) (substLevel env b)
  | .imax a b => mkLevelIMax' (substLevel env a) (substLevel env b)
  | .param n => match env[n]? with | some k => natLevel k | none => .param n
  | l@(.mvar _) => l

/-- The level as a numeral, or `none` if a parameter survived. -/
def evalLevel (env : Std.HashMap Name Nat) (l : Level) : Option Nat :=
  (substLevel env l).normalize.toNat

/-! ## The built-ins, carried through untouched

`MONOMORPH.md` §3 is the list and the argument for it. -/

/-- The seed: names a kernel recognises and cannot be told about a copy of.
`Quot` and its three companions are recognised **structurally**, by the export's
own `quot` record kind, and are not in this list. -/
def builtinSeed : Array Name :=
  #[ -- The equality the round trips and the ι rules are stated with.
     `Eq, `Eq.refl,
     -- The standard axioms.
     `propext, `Classical.choice, `Quot.sound,
     -- Everything a kernel mints when it expands a literal
     -- (`checker/src/util.rs`'s `mk_name_cache`, name for name).
     `eagerReduce, `Nat, `Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul,
     `Nat.pow, `Nat.mod, `Nat.div, `Nat.beq, `Nat.ble, `Nat.gcd, `Nat.xor,
     `Nat.land, `Nat.lor, `Nat.shiftLeft, `Nat.shiftRight,
     `String, `String.ofList, `Bool, `Bool.true, `Bool.false,
     `Char, `Char.ofNat, `List, `List.nil, `List.cons ]

/-! ## The reference set of a group -/

/-- Every constant an expression mentions, with the level arguments it mentions
it at, and every structure a projection names. -/
partial def collectConsts (e : Expr) :
    StateM (Std.HashSet Expr × Array (Name × List Level) × Bool) Unit := do
  if (← get).1.contains e then return
  modify fun (s, o, p) => (s.insert e, o, p)
  match e with
  | .const n us => modify fun (s, o, p) => (s, o.push (n, us), p)
  | .app f a => collectConsts f; collectConsts a
  | .lam _ t b _ | .forallE _ t b _ => collectConsts t; collectConsts b
  | .letE _ t v b _ => collectConsts t; collectConsts v; collectConsts b
  | .proj _ _ s => modify (fun (s, o, _) => (s, o, true)); collectConsts s
  | .mdata _ b => collectConsts b
  | _ => pure ()

/-- The roots of a record: every expression it carries. -/
def rootsOf : EDecl → Array Expr
  | .ax _ _ t _ => #[t]
  | .defn _ _ t v .. | .thm _ _ t v _ | .opaq _ _ t v .. => #[t, v]
  | .quot _ _ t _ => #[t]
  | .induct ts cs rs => Id.run do
    let mut out : Array Expr := #[]
    for t in ts do out := out.push t.type
    for c in cs do out := out.push c.type
    for r in rs do
      out := out.push r.type
      for rr in r.rules do out := out.push rr.rhs
    return out


/-- Whether `e` contains a projection. Memoised on the DAG: the answer does not
depend on the binder context, which is exactly why the *rewrite* can be cached
below the projection-free subterms and nowhere else. -/
partial def hasProj (cache : IO.Ref (Std.HashMap Expr Bool)) (e : Expr) : IO Bool := do
  match (← cache.get)[e]? with
  | some b => return b
  | none =>
    let b ←
      match e with
      | .proj .. => pure true
      | .app f a => pure ((← hasProj cache f) || (← hasProj cache a))
      | .lam _ t b _ | .forallE _ t b _ => pure ((← hasProj cache t) || (← hasProj cache b))
      | .letE _ t v b _ =>
        pure ((← hasProj cache t) || (← hasProj cache v) || (← hasProj cache b))
      | .mdata _ b => hasProj cache b
      | _ => pure false
    cache.modify (·.insert e b)
    return b

/-! ## The rewrite -/

/-- Everything one copy of one group needs. -/
structure RwCtx where
  info : Std.HashMap Name Info
  carried : Std.HashSet Nat
  opts : Opts
  /-- The level parameters this copy binds, and to what. Mode A leaves a
  recursor's elimination universe out of it, which is what keeps it standing. -/
  env : Std.HashMap Name Nat
  /-- The group's instantiation, for the names the group itself introduces. -/
  sigma : Inst
  /-- **How many level parameters each already-emitted recursor came out with.**

  Monomorphizing moves the elimination universe in *both* directions, and the
  file's references have to follow. `Exists.{u}` is small-eliminating — its
  recursor has no universe of its own — but `Exists._at.0`'s constructor fields
  are propositions, so the kernel mints `Exists._at.0.rec.{u_1}` and a reference
  at no levels is now ill-formed. `PUnit.{u}` moves the other way, into K-like
  reduction. Emission is forward and the file is topologically sorted, so the
  block's own answer is known before anything can mention it. -/
  recArity : Std.HashMap Name Nat := {}

/-- A level under this copy's instantiation, simplified. -/
def RwCtx.level (c : RwCtx) (l : Level) : Level := (substLevel c.env l).normalize

/-- A name the group itself introduces, at this copy. -/
def RwCtx.own (c : RwCtx) (n : Name) : Name :=
  match c.info[n]? with
  | some i => if c.carried.contains i.group then n else monoName i.owner n c.sigma
  | none => n

/-- The rewrite state: the memo for projection-free subterms, and the levels
that did not come out ground. -/
abbrev RwState := Std.HashMap Expr Expr × Array String

/-- A constant occurrence, rewritten: which copy it names, and at which levels.

Three outcomes, and they are the whole of §1.2. A **carried** target keeps its
name and takes numerals for its level arguments. An ordinary target becomes the
copy at the instantiation the arguments evaluate to, at no levels. A
**recursor** splits its argument list: the head is the elimination universe,
which mode A keeps and mode B folds into the name. -/
def RwCtx.const (c : RwCtx) (n : Name) (us : List Level) : Name × List Level × Array String :=
  let us' := us.map c.level
  let ground (what : String) (ls : List Level) : Array Nat × Array String :=
    ls.foldl (fun (a, e) l =>
      match l.toNat with
      | some k => (a.push k, e)
      | none => (a.push 0, e.push s!"{n}: {what} did not evaluate to a numeral")) (#[], #[])
  match c.info[n]? with
  | none => (n, us', #[])
  | some i =>
    if c.carried.contains i.group then (n, us', #[])
    else match i.elim, us' with
      | some _, w :: rest =>
        let (σ, e1) := ground "a level argument" rest
        let base := monoName i.owner n σ
        match c.recArity[base]?.getD 1 with
        | 0 =>
          -- The block became small-eliminating at `σ`; the recursor has no
          -- universe left to take one.
          (base, [],
            if w.toNat == some 0 then e1
            else e1.push s!"{n}: eliminates into a nonzero universe, but its copy at this \
              instantiation is small-eliminating")
        | _ => (base, [w], e1)
      | _, _ =>
        let (σ, e1) := ground "a level argument" us'
        let base := monoName i.owner n σ
        match i.elim, c.recArity[base]? with
        -- The block became large-eliminating at `σ`. The original recursor
        -- eliminated into `Prop`, so the copy is used at `0`.
        | none, some 1 => (base, [natLevel 0], e1)
        | _, _ => (base, [], e1)

/-- The rewrite, on a subterm with no projection in it. Memoised: the result
does not depend on the binder context. -/
partial def rwPure (c : RwCtx) (e : Expr) : StateM RwState Expr := do
  match (← get).1[e]? with
  | some r => return r
  | none =>
    let r ←
      match e with
      | .const n us =>
        let (n', us', errs) := c.const n us
        modify (fun (m, es) => (m, es ++ errs))
        pure (.const n' us')
      | .sort l => pure (.sort (c.level l))
      | .app f a => pure (.app (← rwPure c f) (← rwPure c a))
      | .lam n t b bi => pure (.lam n (← rwPure c t) (← rwPure c b) bi)
      | .forallE n t b bi => pure (.forallE n (← rwPure c t) (← rwPure c b) bi)
      | .letE n t v b nd => pure (.letE n (← rwPure c t) (← rwPure c v) (← rwPure c b) nd)
      | .mdata _ b => rwPure c b
      | .proj s i b => pure (.proj s i (← rwPure c b))   -- unreachable; see `rw`
      | _ => pure e
    modify (fun (m, es) => (m.insert e r, es))
    return r

/-- **The structure a projection names, read off the projected term's type.**

`Expr.proj` carries the structure's name but not its level arguments, and Lean's
own `inferProjType` rejects a projection whose name is not the head of the
inferred type — so the name has to move to the right copy, and the copy is only
determined by that type. This is the one place the pass needs a typechecker,
and it is why the input is replayed into an environment at all.

`fvars` are the enclosing binders, with their **original** types, so this runs
against the environment the export itself describes. -/
def projHead (fvars : Array Expr) (s : Expr) : MetaM (Option (Name × List Level)) := do
  let ty ← whnf (← inferType (s.instantiateRev fvars))
  match ty.getAppFn with
  | .const n us => return some (n, us)
  | _ => return none

/-- Collect the `(structure, levels)` of every projection in `e`. Descends only
into subterms that have one. -/
partial def projScan (cache : IO.Ref (Std.HashMap Expr Bool)) (out : IO.Ref (Array (Name × List Level)))
    (fvars : Array Expr) (e : Expr) : MetaM Unit := do
  unless ← hasProj cache e do return
  match e with
  | .proj _ _ s =>
    if let some r ← projHead fvars s then out.modify (·.push r)
    projScan cache out fvars s
  | .app f a => projScan cache out fvars f; projScan cache out fvars a
  | .lam n t b bi =>
    projScan cache out fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => projScan cache out (fvars.push x) b
  | .forallE n t b bi =>
    projScan cache out fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => projScan cache out (fvars.push x) b
  | .letE n t v b _ =>
    projScan cache out fvars t; projScan cache out fvars v
    withLetDecl n (t.instantiateRev fvars) (v.instantiateRev fvars) fun x =>
      projScan cache out (fvars.push x) b
  | .mdata _ b => projScan cache out fvars b
  | _ => pure ()

/-- The rewrite. Projection-free subterms go through [`rwPure`], which is
memoised; the rest is walked in `MetaM` so that [`projHead`] has a local
context. `e` is the **original** expression throughout, so the fvars carry the
original types and inference sees the environment the export describes. -/
partial def rw (c : RwCtx) (cache : IO.Ref (Std.HashMap Expr Bool)) (st : IO.Ref RwState)
    (fvars : Array Expr) (e : Expr) : MetaM Expr := do
  unless ← hasProj cache e do
    let (r, s) := (rwPure c e).run (← st.get)
    st.set s
    return r
  match e with
  | .proj s i b =>
    let b' ← rw c cache st fvars b
    match ← projHead fvars b with
    | some (n, us) =>
      let (n', _, errs) := c.const n us
      if !errs.isEmpty then st.modify fun (m, es) => (m, es ++ errs)
      return .proj n' i b'
    | none =>
      st.modify fun (m, es) => (m, es.push s!"a projection of {s} whose type is not an application \
        of a constant")
      return .proj s i b'
  | .app f a => return .app (← rw c cache st fvars f) (← rw c cache st fvars a)
  | .lam n t b bi =>
    let t' ← rw c cache st fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => do
      return .lam n t' (← rw c cache st (fvars.push x) b) bi
  | .forallE n t b bi =>
    let t' ← rw c cache st fvars t
    withLocalDecl n bi (t.instantiateRev fvars) fun x => do
      return .forallE n t' (← rw c cache st (fvars.push x) b) bi
  | .letE n t v b nd =>
    let t' ← rw c cache st fvars t
    let v' ← rw c cache st fvars v
    withLetDecl n (t.instantiateRev fvars) (v.instantiateRev fvars) fun x => do
      return .letE n t' v' (← rw c cache st (fvars.push x) b) nd
  | .mdata _ b => rw c cache st fvars b
  | _ => return e

/-! ## The sweep -/

private def addInst (a : Array Inst) (i : Inst) : Array Inst :=
  if a.contains i then a else a.push i

private def addNat (a : Array Nat) (i : Nat) : Array Nat :=
  if a.contains i then a else a.push i

/-- What one run did. -/
structure Report where
  groups : Nat := 0
  /-- Declarations in and out — block members, constructors and recursors
  counted one each, which is the figure a checker sees. -/
  declsIn : Nat := 0
  declsOut : Nat := 0
  recordsIn : Nat := 0
  recordsOut : Nat := 0
  /-- Groups left alone, by their first name. -/
  carried : Array Name := #[]
  /-- Groups nothing in the file demanded, which took the default. -/
  defaulted : Nat := 0
  /-- Copies per group, as a histogram. -/
  hist : Array (Nat × Nat) := #[]
  errors : Array String := #[]
  /-- Recursors the kernel minted differently from the substitution — the
  `Prop`-at-`σ` effect, counted rather than argued. -/
  recRegen : Nat := 0
  /-- Monomorphized declarations the replay would not take. -/
  rejected : Nat := 0
  /-- The pass refused the file whole; the output is the input. -/
  refused : Option String := none
  deriving Inhabited

/-- How many declarations a record carries. -/
def declCount : EDecl → Nat
  | .induct ts cs rs => ts.length + cs.length + rs.length
  | _ => 1

/-! ## The driver -/

/-- An export record as a kernel declaration, for the replay. A trimmed copy of
`Modelgen.toDeclaration`: this module deliberately does not import
`Modelgen.Driver`, whose transitive `Modelgen.Model` is under active
development by other work. The shared layer is `Modelgen.Format`. -/
def toDeclaration (env : Environment) : EDecl → Option Declaration
  | .ax n lp t u => some <| .axiomDecl { name := n, levelParams := lp, type := t, isUnsafe := u }
  | .defn n lp t v h sf _ => some <| .defnDecl
      { name := n, levelParams := lp, type := t, value := v
        hints := (match h with
          | .abbrev => .abbrev | .opaque => .opaque | .regular k => .regular k.toUInt32)
        safety := (match sf with
          | "unsafe" => .unsafe | "partial" => .partial | _ => .safe) }
  | .thm n lp t v _ => some <| .thmDecl { name := n, levelParams := lp, type := t, value := v }
  | .opaq n lp t v u _ => some <| .opaqueDecl
      { name := n, levelParams := lp, type := t, value := v, isUnsafe := u }
  | .quot .. => if env.constants.contains `Quot then none else some .quotDecl
  | .induct ts cs _ =>
    let its := ts.map fun t =>
      ({ name := t.name, type := t.type
         ctors := (cs.filter (·.induct == t.name)).map fun c =>
           ({ name := c.name, type := c.type } : Constructor) } : InductiveType)
    match ts with
    | [] => none
    | t :: _ => some <| .inductDecl t.levelParams t.numParams its t.isUnsafe

/-- One record, at one instantiation. Always **mode A**: mode B is a pure
post-pass over this ([`foldElim`]), which is what makes "B is A with the
eliminating universe folded into the name" true by construction rather than by
two parallel implementations.

`keepParams` is the carried case: a built-in keeps its name and its level
parameters, and only its *references* move to the copies they mean. -/
def emitOne (c : RwCtx) (cache : IO.Ref (Std.HashMap Expr Bool)) (st : IO.Ref RwState)
    (keepParams : Bool) (blockLp : List Name) (d : EDecl) : MetaM EDecl := do
  let E (e : Expr) : MetaM Expr := rw c cache st #[] e
  let lp (orig : List Name) : List Name := if keepParams then orig else []
  match d with
  | .ax n l t u => return .ax (c.own n) (lp l) (← E t) u
  | .defn n l t v h sf all =>
    return .defn (c.own n) (lp l) (← E t) (← E v) h sf (all.map c.own)
  | .thm n l t v all => return .thm (c.own n) (lp l) (← E t) (← E v) (all.map c.own)
  | .opaq n l t v u all => return .opaq (c.own n) (lp l) (← E t) (← E v) u (all.map c.own)
  -- The four `quot` records are carried verbatim: they mention nothing but
  -- `Quot`, `Sort` and themselves, and `Declaration.quotDecl` is a unit.
  | .quot n l t k => return .quot n l t k
  | .induct ts cs rs => do
    let ts' ← ts.mapM fun t => do
      return { t with name := c.own t.name, levelParams := lp t.levelParams
                      type := ← E t.type, all := t.all.map c.own, ctors := t.ctors.map c.own }
    let cs' ← cs.mapM fun x => do
      return { x with name := c.own x.name, levelParams := lp x.levelParams
                      type := ← E x.type, induct := c.own x.induct }
    let rs' ← rs.mapM fun r => do
      let relim := r.levelParams.filter (fun p => !blockLp.contains p)
      return { r with name := c.own r.name
                      levelParams := (if keepParams then r.levelParams else relim)
                      type := ← E r.type, all := r.all.map c.own
                      rules := ← r.rules.mapM fun rr => do
                        return { rr with ctor := c.own rr.ctor, rhs := ← E rr.rhs } }
    return .induct ts' cs' rs'

/-- **The recursors the kernel mints for the monomorphized block**, in place of
the ones the substitution produced.

This is not a nicety. Substituting `σ` into an inductive changes properties the
kernel *derives* from the block rather than reads off it: `PUnit.{u}` at `u = 0`
is a `Prop` with one argument-free constructor, which is **K-like**, and the
export's `k : false` becomes a lie. Large elimination can move the same way. So
the block is replayed and its recursors are read back, which makes mode A's
output kernel-consistent by construction and turns the whole question into a
measurement: [`Report.recRegen`] counts the recursors that came back different. -/
def kernelRecs (env : Environment) (rs : List ERec) : List ERec × Nat := Id.run do
  let mut out : Array ERec := #[]
  let mut diff := 0
  for r in rs do
    match env.constants.find? r.name with
    | some (.recInfo rv) =>
      let k : ERec :=
        { name := rv.name, levelParams := rv.levelParams, type := rv.type, all := rv.all
          numParams := rv.numParams, numIndices := rv.numIndices, numMotives := rv.numMotives
          numMinors := rv.numMinors, k := rv.k, isUnsafe := rv.isUnsafe
          rules := rv.rules.map fun x => { ctor := x.ctor, nfields := x.nfields, rhs := x.rhs } }
      -- The elimination universe's *name* is Lean's to choose, so compare the
      -- statement with the export's name put back.
      let renamed :=
        match r.levelParams, rv.levelParams with
        | [a], [b] => k.type.instantiateLevelParams [b] [.param a]
        | _, _ => k.type
      unless renamed == r.type && k.k == r.k && k.numMotives == r.numMotives
          && k.numMinors == r.numMinors && k.numIndices == r.numIndices do
        diff := diff + 1
      out := out.push k
    | _ => out := out.push r
  return (out.toList, diff)

/-! ## Mode B

The eliminating universe, folded into the name. A pure pass over mode A's own
output: the only level parameter mode A leaves standing is a recursor's, every
use of it in the file is at a numeral, and this replaces each recursor by one
copy per numeral used. -/

/-- Rewrite every reference `r.{k}` to a recursor in `elimOf` into `r._elim.k`. -/
partial def foldRefs (elimOf : Std.HashSet Name) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  match (← get)[e]? with
  | some r => return r
  | none => pure ()
  let r ←
    match e with
    | .const n [l] => pure <| if elimOf.contains n then .const (elimName n (l.toNat.getD 0)) [] else e
    | .app f a => pure (.app (← foldRefs elimOf f) (← foldRefs elimOf a))
    | .lam n t b bi => pure (.lam n (← foldRefs elimOf t) (← foldRefs elimOf b) bi)
    | .forallE n t b bi => pure (.forallE n (← foldRefs elimOf t) (← foldRefs elimOf b) bi)
    | .letE n t v b nd =>
      pure (.letE n (← foldRefs elimOf t) (← foldRefs elimOf v) (← foldRefs elimOf b) nd)
    | .proj s i b => pure (.proj s i (← foldRefs elimOf b))
    | .mdata _ b => foldRefs elimOf b
    | _ => pure e
  modify (·.insert e r)
  return r

/-- Every recursor with an eliminating universe of its own, and the numerals the
file uses it at. -/
def elimUses (x : Export) (defaults : Array Nat) : Std.HashMap Name (Array Nat) := Id.run do
  let mut ws : Std.HashMap Name (Array Nat) := {}
  for d in x.decls do
    if let .induct _ _ rs := d then
      for r in rs do
        if r.levelParams.length == 1 then ws := ws.insert r.name #[]
  let mut seen : Std.HashSet Expr := {}
  for d in x.decls do
    for root in rootsOf d do
      let mut stack : Array Expr := #[root]
      while stack.size > 0 do
        let e := stack[stack.size - 1]!
        stack := stack.pop
        if seen.contains e then continue
        seen := seen.insert e
        match e with
        | .const n [l] =>
          if let some a := ws[n]? then
            if let some k := l.toNat then ws := ws.insert n (addNat a k)
        | .app f a => stack := (stack.push f).push a
        | .lam _ t b _ | .forallE _ t b _ => stack := (stack.push t).push b
        | .letE _ t v b _ => stack := ((stack.push t).push v).push b
        | .proj _ _ b | .mdata _ b => stack := stack.push b
        | _ => pure ()
  for (n, a) in ws.toArray do if a.isEmpty then ws := ws.insert n defaults
  return ws

/-- **Mode B.** -/
def foldElim (x : Export) (defaults : Array Nat) : Export := Id.run do
  let ws := elimUses x defaults
  let names : Std.HashSet Name := ws.toArray.foldl (fun s (n, _) => s.insert n) {}
  let fold (e : Expr) : Expr := (foldRefs names e).run' {}
  let mut out : Array EDecl := #[]
  for d in x.decls do
    out := out.push <|
      match d with
      | .ax n l t u => .ax n l (fold t) u
      | .defn n l t v h sf a => .defn n l (fold t) (fold v) h sf a
      | .thm n l t v a => .thm n l (fold t) (fold v) a
      | .opaq n l t v u a => .opaq n l (fold t) (fold v) u a
      | .quot n l t k => .quot n l t k
      | .induct ts cs rs =>
        let rs' := rs.flatMap fun r =>
          match r.levelParams, ws[r.name]? with
          | [u], some vals => vals.toList.map fun w =>
            let sub (e : Expr) : Expr := fold (e.instantiateLevelParams [u] [natLevel w])
            { r with name := elimName r.name w, levelParams := [], type := sub r.type
                     rules := r.rules.map fun rr => { rr with rhs := sub rr.rhs } }
          | _, _ => [{ r with type := fold r.type
                              rules := r.rules.map fun rr => { rr with rhs := fold rr.rhs } }]
        .induct (ts.map fun t => { t with type := fold t.type })
          (cs.map fun c => { c with type := fold c.type }) rs'
  return { x with decls := out }

/-- **The pass.** -/
def monomorphize (x : Export) (opts : Opts) : MetaM (Export × Report) := do
  let mut rep : Report :=
    { recordsIn := x.decls.size, declsIn := x.decls.foldl (fun a d => a + declCount d) 0 }
  -- The markers must not already be in use, or the scheme is not invertible.
  for d in x.decls do
    for n in d.names do
      if usesMarker n then
        return (x, { rep with refused := some s!"the file already declares {n}, which spells a marker" })
  let base ← getEnv
  let (groups, info) ←
    match buildGroups x with
    | .error e => return (x, { rep with refused := some e })
    | .ok r => pure r
  rep := { rep with groups := groups.size }

  -- ── The reference set of each group: every constant it mentions, at the
  -- level arguments it mentions it at.
  let mut refs : Array (Array (Name × List Level)) := Array.replicate groups.size #[]
  let mut anyProj := false
  for gi in [0 : groups.size] do
    let mut seen : Std.HashSet Expr := {}
    let mut out : Array (Name × List Level) := #[]
    let mut p := false
    for di in groups[gi]!.decls do
      for r in rootsOf x.decls[di]! do
        let ((), (s, o, q)) := (collectConsts r).run (seen, out, p)
        seen := s; out := o; p := q
    refs := refs.set! gi out
    if p then anyProj := true

  -- ── The projections. `Expr.proj` does not carry the structure's level
  -- arguments, so they are inferred — which needs the input replayed. A file
  -- with no projection never pays for this, and a file the kernel will not
  -- replay at all is refused whole rather than half done.
  let projCache ← IO.mkRef ({} : Std.HashMap Expr Bool)
  if anyProj then
    for gi in [0 : groups.size] do
      for di in groups[gi]!.decls do
        let d := x.decls[di]!
        if let some dcl := toDeclaration (← getEnv) d then
          match (← getEnv).addDeclCore 0 dcl none false with
          | .ok e => setEnv e
          | .error ex =>
            let msg ← (ex.toMessageData {}).toString
            return (x, { rep with refused := some s!"{d.names} did not replay: {msg}" })
        let out ← IO.mkRef (#[] : Array (Name × List Level))
        for r in rootsOf d do projScan projCache out #[] r
        refs := refs.set! gi (refs[gi]! ++ (← out.get))

  -- ── Topological sortedness, asserted rather than assumed.
  for gi in [0 : groups.size] do
    for (n, _) in refs[gi]! do
      if let some i := info[n]? then
        if i.group > gi then
          return (x, { rep with refused := some s!"the file is not topologically sorted: group {gi} \
            mentions {n}, which group {i.group} declares" })

  -- ── The carried set: the built-ins, closed under "mentioned at a level a
  -- copy could not be chosen for".
  let seed : Std.HashSet Name := builtinSeed.foldl (·.insert ·) {}
  let mut carried : Std.HashSet Nat := {}
  for gi in [0 : groups.size] do
    let d := x.decls[groups[gi]!.decls[0]!]!
    match d with
    | .quot .. => carried := carried.insert gi
    | _ => if (introOf d).any (fun (n, _, _) => seed.contains n) then carried := carried.insert gi
  let mut changed := true
  while changed do
    changed := false
    for gi in [0 : groups.size] do
      if carried.contains gi then
        for (n, us) in refs[gi]! do
          if let some i := info[n]? then
            unless carried.contains i.group do
              if us.any (fun l => (l.toNat).isNone) then
                carried := carried.insert i.group
                changed := true

  -- ── The backward sweep.
  let mut demand : Array (Array Inst) := Array.replicate groups.size #[]
  let mut elimD : Array (Array Nat) := Array.replicate groups.size #[]
  let mut errors : Array String := #[]
  let mut defaulted := 0
  for k in [0 : groups.size] do
    let gi := groups.size - 1 - k
    let g := groups[gi]!
    let isCarried := carried.contains gi
    if !isCarried && demand[gi]!.isEmpty then
      defaulted := defaulted + 1
      let mut ds : Array Inst := #[]
      for l in opts.defaults do ds := addInst ds (Array.replicate g.levelParams.length l)
      demand := demand.set! gi ds
    let sigmas := if isCarried then #[(#[] : Inst)] else demand[gi]!
    let ws := if g.elims.isEmpty then #[0] else
      (if elimD[gi]!.isEmpty then opts.defaults else elimD[gi]!)
    if !g.elims.isEmpty && elimD[gi]!.isEmpty then
      elimD := elimD.set! gi opts.defaults
    for σ in sigmas do
      for w in ws do
        let mut env : Std.HashMap Name Nat := {}
        unless isCarried do
          for (p, v) in g.levelParams.zip σ.toList do env := env.insert p v
          for p in g.elims do env := env.insert p w
        for (n, us) in refs[gi]! do
          let some i := info[n]? | continue
          if carried.contains i.group then continue
          let us' := us.map (fun l => (substLevel env l).normalize)
          let (wv, rest) := match i.elim, us' with
            | some _, a :: r => (a.toNat, r)
            | _, r => (none, r)
          if rest.any (fun l => l.toNat.isNone) then
            errors := errors.push s!"{n}: a level argument did not evaluate to a numeral"
            continue
          let σt : Inst := (rest.map (fun l => l.toNat.getD 0)).toArray
          if i.group == gi then
            unless demand[gi]!.contains σt do
              errors := errors.push s!"{n}: the group demands itself at a new instantiation"
          else
            demand := demand.set! i.group (addInst demand[i.group]! σt)
          if let some wk := wv then
            if i.group == gi then
              unless elimD[gi]!.contains wk do
                errors := errors.push s!"{n}: the group demands itself at a new eliminating universe"
            else elimD := elimD.set! i.group (addNat elimD[i.group]! wk)
  rep := { rep with defaulted }

  -- ── Emission, forward, so the output keeps the input's order, and so that
  -- each monomorphized block can be replayed into `monoEnv` before the next
  -- one needs its constants.
  let errRef ← IO.mkRef errors
  let mut monoEnv := base
  let mut recRegen := 0
  let mut addFailed : Array String := #[]
  let mut out : Array EDecl := #[]
  let mut hist : Std.HashMap Nat Nat := {}
  let mut recArity : Std.HashMap Name Nat := {}
  for gi in [0 : groups.size] do
    let g := groups[gi]!
    let isCarried := carried.contains gi
    let sigmas := if isCarried then #[(#[] : Inst)] else demand[gi]!
    hist := hist.insert sigmas.size ((hist[sigmas.size]?.getD 0) + 1)
    for σ in sigmas do
      let mut env : Std.HashMap Name Nat := {}
      unless isCarried do
        for (p, v) in g.levelParams.zip σ.toList do env := env.insert p v
      let c : RwCtx := { info, carried, opts, env, sigma := σ, recArity }
      let st ← IO.mkRef (({}, #[]) : RwState)
      for di in g.decls do
        let mut e ← emitOne c projCache st isCarried g.levelParams x.decls[di]!
        -- Replay, so that a block's recursors are the kernel's own and so that
        -- the next block can be elaborated against this one.
        if let some dcl := toDeclaration monoEnv e then
          match monoEnv.addDeclCore 0 dcl none opts.check with
          | .ok m =>
            monoEnv := m
            if let .induct ts cs rs := e then
              let (rs', d) := kernelRecs monoEnv rs
              recRegen := recRegen + d
              e := .induct ts cs rs'
          | .error ex =>
            addFailed := addFailed.push s!"{e.names}: {← (ex.toMessageData {}).toString}"
        if let .induct _ _ rs := e then
          for r in rs do recArity := recArity.insert r.name r.levelParams.length
        out := out.push e
      errRef.modify (· ++ (← st.get).2)
  let mut carriedNames : Array Name := #[]
  for gi in [0 : groups.size] do
    if carried.contains gi then
      carriedNames := carriedNames.push (x.decls[groups[gi]!.decls[0]!]!.names[0]!)
  -- Every output name is a distinct one. The marker guard is what makes the
  -- scheme *invertible*; this is what makes it collision-free, and it is a
  -- check rather than an argument.
  let mut seenNames : Std.HashSet Name := {}
  for d in out do
    for n in d.names do
      if seenNames.contains n then
        return (x, { rep with refused := some s!"two output declarations are both named {n}" })
      seenNames := seenNames.insert n
  let y : Export := { x with decls := out }
  let y := if opts.monoRecursors then foldElim y opts.defaults else y
  rep := { rep with
    errors := (← errRef.get) ++ addFailed, carried := carriedNames
    recRegen, rejected := addFailed.size
    recordsOut := y.decls.size, declsOut := y.decls.foldl (fun a d => a + declCount d) 0
    hist := hist.toArray.qsort (fun a b => a.1 < b.1) }
  return (y, rep)
