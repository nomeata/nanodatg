import Modelgen.Model

/-!
# The filter

`.ndjson` in, `.ndjson` out. The input is **trusted**: every declaration is
replayed into a `Lean.Environment` with checking off, because the owner's
instruction is to trust the export and that is where the speed comes from. Only
the declarations this tool *generates* are checked, and they are checked by the
kernel, one at a time.

Before each nested inductive the output carries that declaration's model. The
input's own records are otherwise unchanged, and a file with no nested
inductive is copied **byte for byte** rather than re-serialised.

## Why the whole file is re-interned when anything is spliced

`nanoda`'s parser rejects a back-reference that is not the current count, so a
model cannot be inserted into an existing file with fresh high indices. When
there is a model to write, [`Modelgen.Export.render`] re-interns from scratch.

## The free oracle

Lean's kernel builds the nested construction itself: given `Tree`'s
`inductDecl` it generates **both** `Tree.rec` and `Tree.rec_1`, at the shapes
the export declares. So replaying the input already compares every recursor in
the file against Lean's own, and `--check-recursors` reports the difference.
That is `mini/tests/mutual.rs`'s `the_generated_recursors_are_the_ones_lean_
exports` obtained for nothing, over the whole corpus rather than the fixtures.
-/

open Lean Meta

namespace Modelgen

/-- What one run did. -/
structure Report where
  generated : Array (Name × Nat) := #[]
  declined : Array (Name × String) := #[]
  /-- Recursors whose replayed shape differs from the export's own. -/
  recMismatch : Array Name := #[]
  recChecked : Nat := 0
  /-- Statements compared against the installed recursors' own rules, and the
  ones that did not match. -/
  stmtChecked : Nat := 0
  stmtErrors : Array String := #[]
  /-- The input stopped replaying here: a declaration Lean's kernel will not
  load at all. The filter then becomes the identity, which is what a filter
  should be when it can do nothing. -/
  unreplayable : Option String := none
  deriving Inhabited

def hintsOf : ReducibilityHints → EHints
  | .abbrev => .abbrev
  | .opaque => .opaque
  | .regular h => .regular h.toNat

def hintsTo : EHints → ReducibilityHints
  | .abbrev => .abbrev
  | .opaque => .opaque
  | .regular h => .regular h.toUInt32

def safetyOf : String → DefinitionSafety
  | "unsafe" => .unsafe
  | "partial" => .partial
  | _ => .safe

/-- An export record as a kernel declaration. `none` for the three `quot`
records that `Declaration.quotDecl` already covers. -/
def toDeclaration (env : Environment) : EDecl → Option Declaration
  | .ax n lp t u => some <| .axiomDecl { name := n, levelParams := lp, type := t, isUnsafe := u }
  | .defn n lp t v h sf _ => some <| .defnDecl
      { name := n, levelParams := lp, type := t, value := v
        hints := hintsTo h, safety := safetyOf sf }
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

/-- Read one inductive block back out of the environment, including the
recursors the **kernel** generated for it. -/
def indEDecl (names : Array Name) : MetaM EDecl := do
  let env ← getEnv
  let mut ts : Array EIndType := #[]
  let mut cs : Array ECtor := #[]
  let mut rs : Array ERec := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    ts := ts.push
      { name := iv.name, levelParams := iv.levelParams, type := iv.type, all := iv.all
        ctors := iv.ctors, numParams := iv.numParams, numIndices := iv.numIndices
        numNested := iv.numNested, isRec := iv.isRec, isReflexive := iv.isReflexive
        isUnsafe := iv.isUnsafe }
    for cn in iv.ctors do
      let some (.ctorInfo cv) := env.constants.find? cn | throwError "{cn} is not a constructor"
      cs := cs.push
        { name := cv.name, levelParams := cv.levelParams, type := cv.type, cidx := cv.cidx
          numParams := cv.numParams, numFields := cv.numFields, induct := cv.induct
          isUnsafe := cv.isUnsafe }
  for n in names do
    if let some (.recInfo rv) := env.constants.find? (Name.str n "rec") then
      rs := rs.push
        { name := rv.name, levelParams := rv.levelParams, type := rv.type, all := rv.all
          numParams := rv.numParams, numIndices := rv.numIndices, numMotives := rv.numMotives
          numMinors := rv.numMinors, k := rv.k, isUnsafe := rv.isUnsafe
          rules := rv.rules.map fun r =>
            { ctor := r.ctor, nfields := r.nfields, rhs := r.rhs } }
  return .induct ts.toList cs.toList rs.toList

/-- A generated declaration as an export record. -/
def toEDecl : Declaration → MetaM EDecl
  | .defnDecl v => return .defn v.name v.levelParams v.type v.value (hintsOf v.hints) "safe" [v.name]
  | .thmDecl v => return .thm v.name v.levelParams v.type v.value [v.name]
  | .axiomDecl v => return .ax v.name v.levelParams v.type v.isUnsafe
  | .opaqueDecl v => return .opaq v.name v.levelParams v.type v.value v.isUnsafe [v.name]
  | .inductDecl _ _ ts _ => indEDecl (ts.toArray.map (·.name))
  | d => throwError "cannot serialise {d.getTopLevelNames}"

/-- Compare the export's own recursors against the ones the kernel just
regenerated. Returns the names that differ. -/
def checkRecs (rs : List ERec) : MetaM (Nat × Array Name) := do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut n := 0
  for r in rs do
    n := n + 1
    let some (.recInfo rv) := env.constants.find? r.name | bad := bad.push r.name; continue
    let sameRules :=
      rv.rules.length == r.rules.length &&
      (rv.rules.zip r.rules).all fun (a, b) => a.ctor == b.ctor && a.rhs == b.rhs
    unless rv.type == r.type && rv.numMotives == r.numMotives && rv.numMinors == r.numMinors
        && rv.numParams == r.numParams && rv.numIndices == r.numIndices && rv.k == r.k
        && sameRules do
      bad := bad.push r.name
  return (n, bad)

/-- The export's names rewritten to the model's: the carrier for `T`, the
model's constructor for each of `T`'s, and `T._model.rec_k` for `T.rec_k`. -/
def modelTable (env : Environment) (all : Array Name) (is : Iso) :
    Std.HashMap Name (Nat × Expr) := Id.run do
  let us := is.levelParams.map Level.param
  let mut t : Std.HashMap Name (Nat × Expr) := {}
  for k in [0:is.numAll] do
    t := t.insert all[k]! (0, .const is.selfNames[k]! us)
  for (exportC, modelC) in is.ctors do
    t := t.insert exportC (0, .const modelC us)
  for k in [0:is.recs.size] do
    let ern := exportRecName all k
    let ls := match env.constants.find? ern with
      | some ci => ci.levelParams.map Level.param
      | none => []
    t := t.insert ern (0, .const is.recs[k]! ls)
  return t

/-- **The model's recursors and ι theorems state the export's own.**

`addDeclCore` says the generator's proof proves the generator's *statement*, and
a generator that stated a different well-typed equation — the rule of the wrong
member, the induction hypothesis at `T.rec` where the export says `T.rec_1`, a
minor applied to its fields in the wrong order — would satisfy it and be wrong.
So every emitted statement is rebuilt here from the rule the **installed**
`T.rec_k` carries, reading the constructor's field telescope off the recursor's
own major type rather than off the plan, and compared syntactically.

This is `mini/tests/nested.rs`'s `check_recursors` and `check_iotas`, ported. It
is what forced a real bug out of the Rust — recursors rewritten at no levels. -/
def checkModel (all : Array Name) (np : Nat) (is : Iso) : MetaM (Nat × Array String) := do
  let env ← getEnv
  let tbl := modelTable env all is
  let mut n := 0
  let mut errs : Array String := #[]
  for k in [0:is.recs.size] do
    let ern := exportRecName all k
    let some (.recInfo rv) := env.constants.find? ern
      | errs := errs.push s!"{ern} was not installed"; continue
    let some mi := env.constants.find? is.recs[k]!
      | errs := errs.push s!"{is.recs[k]!} was not generated"; continue
    let want := restore tbl rv.type
    unless mi.type == want do
      errs := errs.push s!"{is.recs[k]!} is not {ern} at the model"
    n := n + 1
    let mine := is.iotas.filter (·.1 == k)
    unless mine.size == rv.rules.length do
      errs := errs.push s!"{is.recs[k]!} has {mine.size} ι theorems against {ern}'s \
        {rv.rules.length} rules"
      continue
    -- **A block that eliminates only into `Prop` has no motive universe**, and
    -- then the rule's `Eq` is at `Prop` and the recursor's level list is the
    -- declaration's own. `S : Prop | mk : PL S → S` is one; `Eq` itself is
    -- `Prop` and has a motive universe, so this is read off the level list and
    -- not off the sort.
    let large := rv.levelParams.length == is.levelParams.length + 1
    let v ← if large then
        match rv.levelParams[0]? with
        | some lp => pure (Level.param lp)
        | none => pure Level.zero
      else pure Level.zero
    let recLs := if large then v :: is.levelParams.map Level.param
                 else is.levelParams.map Level.param
    let nb := np + rv.numMotives + rv.numMinors
    -- **The indices sit between the minors and the major.** A rule binds no
    -- index of its own — they are determined by the constructor's result — so
    -- the ι theorem's telescope is still `p⃗ M⃗ S⃗ f⃗` and the index vector is
    -- read off the major's own type below.
    let ni := rv.numIndices
    let (es, extra) ← forallBoundedTelescope want (some (nb + ni + 1)) fun bs _ => do
      let pre := bs.extract 0 nb
      let ps := bs.extract 0 np
      let motiveK := bs[np + k]!
      let majorTy ← inferType bs[nb + ni]!
      let mut es : Array String := #[]
      let mut cnt := 0
      for (rule, mineJ) in rv.rules.zip mine.toList do
        let (_, key, thm) := mineJ
        unless rule.ctor == key do
          es := es.push s!"{thm} is about {key}, not {ern}'s rule for {rule.ctor}"
          continue
        -- The constructor as it is applied, and its field telescope: at the
        -- root the model's own constructor, at a mimic the **real** container's
        -- at the arguments the major's own type carries — which is where this
        -- reads the occurrence from rather than from the plan.
        let (headC, hls, hpre, cty) ←
          if k < is.numAll then do
            let some (_, modelC) := is.ctors.find? (·.1 == key)
              | es := es.push s!"{key} has no model constructor"; continue
            let some ci := env.constants.find? modelC
              | es := es.push s!"{modelC} was not generated"; continue
            pure (modelC, is.levelParams.map Level.param, ps, ← instantiateForall ci.type ps)
          else do
            let .const _ cls := majorTy.getAppFn
              | es := es.push s!"{ern}'s major is not a type"; continue
            -- The container at its **parameters**: the major's own type is the
            -- occurrence at this recursor's indices, and the indices are the
            -- last `ni` arguments of it.
            let mas := majorTy.getAppArgs
            let qs := mas.extract 0 (mas.size - ni)
            let some ci := env.constants.find? key
              | es := es.push s!"{key} is not declared"; continue
            pure (key, cls, qs,
              ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams cls) qs)
        let e ← forallTelescope cty fun fields _ => do
          let major := mkAppN (.const headC hls) (hpre ++ fields)
          let mas := (← inferType major).getAppArgs
          let idxs := mas.extract (mas.size - ni) mas.size
          let lhs := mkAppN (.const is.recs[k]! recLs) ((pre ++ idxs).push major)
          -- The rule's own right-hand side, at the model's names. Lean states it
          -- as `fun p⃗ M⃗ S⃗ f⃗ => …`, which is this telescope exactly.
          let rhs := (restore tbl rule.rhs).beta (pre ++ fields)
          let body := mkAppN (.const `Eq [v]) #[mkAppN motiveK (idxs.push major), lhs, rhs]
          let wantTy ← mkForallFVars (pre ++ fields) body
          let some ti := env.constants.find? thm | return some s!"{thm} was not generated"
          if ti.levelParams != rv.levelParams then
            return some s!"{thm} is not at {ern}'s motive universe"
          if ti.type != wantTy then return some s!"{thm} is not {ern}'s rule for {rule.ctor}"
          return none
        if let some m := e then es := es.push m
        cnt := cnt + 1
      return (es, cnt)
    n := n + extra
    errs := errs ++ es
  return (n, errs)

/-- **The filter.** -/
def runFilter (x : Export) (checkRecursors : Bool) : MetaM (Array EDecl × Report) := do
  let mut out : Array EDecl := #[]
  let mut rep : Report := {}
  -- Held back until the export's own declaration is installed, so the
  -- statements can be compared against the recursors it then mints.
  let mut pending : Array (Array Name × Nat × Iso) := #[]
  -- Every name the input declares anywhere, so that a model cannot collide
  -- with one the file itself introduces *later*.
  let reserved : Std.HashSet Name :=
    x.decls.foldl (fun s d => d.names.foldl (·.insert ·) s) {}
  for d in x.decls do
    -- The model, if this is a nested declaration. Generated **before** the
    -- declaration is added, which is where `mini/src/nested.rs` also stands:
    -- nothing in the model mentions `T`.
    if let .induct ts cs _ := d then
      -- **A mutual block whose members nest is one block, not several.** Lean
      -- specialises the whole block at once — `nest_mutual_both`'s `A`/`B`
      -- become four members with four recursors over one shared motive vector
      -- — so the model does too, under the first member's `_model` namespace
      -- and with one carrier per real member.
      if let t :: _ := ts then
        if ts.any (·.numNested > 0) then
          let all := ts.toArray.map (·.name)
          let ctorsOfMember := fun (n : Name) =>
            (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
          let ptypes : Array PType := ts.toArray.map fun m =>
            { name := m.name, type := m.type, ctors := ctorsOfMember m.name }
          match plan (← getEnv) t.levelParams t.numParams ptypes with
          | .error e => rep := { rep with declined := rep.declined.push (t.name, e) }
          | .ok none => pure ()
          | .ok (some pl) =>
            let saved ← getEnv
            let ctors := all.map ctorsOfMember
            match ← (iso all t.levelParams t.numParams ctors pl reserved).run with
            | .error dec =>
              setEnv saved
              rep := { rep with declined := rep.declined.push (t.name, dec.label) }
            | .ok is =>
              for gd in is.decls do out := out.push (← toEDecl gd)
              rep := { rep with generated := rep.generated.push (t.name, is.decls.size) }
              pending := pending.push (all, t.numParams, is)
    -- Replay, unchecked: the input is trusted. Lean's kernel still runs the
    -- *inductive* elaboration, which is not skippable, so a deliberately
    -- ill-formed inductive stops the replay here. Nothing has been spliced yet
    -- when that happens, so the file passes through untouched.
    if let some dcl := toDeclaration (← getEnv) d then
      -- `Environment.addDeclCore` and not `Kernel.Environment.
      -- addDeclWithoutChecking`, even though the elaborator-side bookkeeping is
      -- unwanted here: `Environment.find?` — which `MetaM`'s `inferType` goes
      -- through — reads the *imported* half of the constant map and then the
      -- **async** map, so a constant added at the kernel level is invisible to
      -- it and the generator cannot so much as name `List.rec`. The price is
      -- one `panic!` from `AsyncConsts.add` on
      -- `vendor/arena-tests/good/perf/grind-ring-5.ndjson`, where two private
      -- names from different modules normalise alike — normal in an export,
      -- which is many modules flattened into one file, and impossible during
      -- elaboration. It is not fatal: the entry is dropped from an index this
      -- tool never reads, and that file's model is still accepted by `nanoda`.
      match (← getEnv).addDeclCore 0 dcl none false with
      | .ok e => setEnv e
      | .error ex =>
        let msg ← (ex.toMessageData {}).toString
        return (x.decls, { rep with unreplayable := some s!"{d.names}: {msg}" })
    for (all, np, is) in pending do
      let (m, errs) ← checkModel all np is
      rep := { rep with stmtChecked := rep.stmtChecked + m, stmtErrors := rep.stmtErrors ++ errs }
    pending := #[]
    if checkRecursors then
      if let .induct _ _ rs := d then
        let (n, b) ← checkRecs rs
        rep := { rep with recChecked := rep.recChecked + n, recMismatch := rep.recMismatch ++ b }
    out := out.push d
  return (out, rep)

end Modelgen
