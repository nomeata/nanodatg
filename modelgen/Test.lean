import Modelgen.Driver

/-!
# The tool's own oracles, as a test

Run from the repository root: `lake exe test [ROOT]`.

Four axes, and each one has an occupant that would pass the other three:

1. **The counts.** One declaration for the block, one for the carrier, four per
   mimic, one per constructor, one per recursor, one congruence per mimic and
   **one ι theorem per rule of every recursor**. A generator that quietly
   emitted fewer — dropping a round trip, or a mimic, or one constructor's rule
   — still typechecks and measures nothing, so the table is pinned.
2. **The kernel.** Every generated declaration goes through
   `Environment.addDeclCore` with checking on, inside the tool. An `ok` here is
   Lean's answer and not the generator's.
3. **The statements.** Each recursor and each ι theorem is rebuilt from the rule
   the **installed** `T.rec_k` carries and compared syntactically
   ([`Modelgen.checkModel`]). Well-typedness is not the claim: a generator that
   stated a different well-typed equation — the rule of the wrong member, the
   hypothesis at `T.rec` where the export says `T.rec_1` — would satisfy axis 2.
4. **The round trip.** `parse (render (parse t)) = parse t`, structurally, and
   a file with no nested inductive comes out byte for byte.

## The ordering axis, and why `Lean.Syntax` is the test for it

Two atoms cannot distinguish an ordering. The mimic discovery order decides
which generated `rec_k` states which of the export's rules, and every fixture in
`mini/tests/fixtures` has at most **two** mimics — reversing the order there
swaps two things and axis 3 catches it only if the two differ in shape.
`Lean.Syntax` has **three** block members (`Syntax`, the `Array Syntax` mimic,
the `List Syntax` mimic) with three distinct recursors, so it is the
case that pins the order rather than a permutation of it. It needs
`vendor/arena-tests`, which is gitignored, and is skipped when absent.
-/

open Lean Meta Modelgen

/-- `(fixture, [(declaration, model size)], [(declaration, decline)])`. -/
abbrev Row := String × List (String × Nat) × List (String × String)

/-- Read off `MEASUREMENTS.md`'s table and off `mini/tests/nested.rs`'s
`the_nested_isomorphism_is_generated_and_the_kernel_accepts_it`, which pins the
same eight numbers for the Rust generator. -/
def expected : List Row :=
  [ ("nested_iota", [("Tree", 15), ("BTree", 24), ("PT", 15)], [])
  , ("nested_deep", [("DTree", 23)], [])
  , ("nested_shapes", [("Tree", 15), ("PTree", 14), ("DTree", 23), ("BTree", 14)], [])
  , ("nested_iota_arm", [("Tree", 15)], [])
    -- `nested_keying.lean` declares `UTree._model.self` itself, *after*
    -- `UTree`, so that a consumer keying on the convention is not fooled by it.
    -- The guard therefore has to scan the whole file and not just the prefix;
    -- `Tree` in the same file is the atom that says the guard is not simply
    -- refusing everything.
  , ("nested_keying", [("Tree", 15)], [("UTree", "nested model name taken (UTree._model.self)")])
  ]

/-- **The refusal paths, each with a fixture that reaches it.** The generator
seat reported that `nested_ev::Reason`'s guards "keep their arguments and gain
no occupant" — no fixture in the tree reaches any refusal except `NameTaken`,
so five guards were known only by inspection. These are written for exactly
that hole, under `modelgen/tests/` rather than in `mini/tests/fixtures`, and
`export.sh` builds them with the repository's own exporter.

**A decline is compared by prefix**, so that a fixture may pin *which shape*
stopped the generator without pinning the wording of a kernel diagnostic
quoted inside it.

Most of these are shapes **Lean accepts and this does not** — every `.lean`
here is one Lean's own kernel loaded, and `--check-recursors` compares the
recursors it minted against the export's on every run. The five axis files are
named for the shape rather than for the refusal, because the refusal is what
is meant to go away. `poly_nested` and `dependent_fields` no longer decline —
their models are `expectedOwn`'s first two rows — and the three that remain
are:

* `indexed_decl` — the declaration has indices.
* `indexed_container` — a container it nests into has indices.
* `infinitary` — a constructor field recursive under a binder, in all three
  places one can sit relative to the nesting.

Three refusals are not of that kind:

* `decline_no_eq` — the export declares no `Eq`. The round trips are
  equations; this tool does not fabricate an equality Lean never wrote, and
  there is nothing here to fix.
* `nest_through_mutual` — a mutual block one of whose members nests. **Lean
  supports it and exports it**: `A`/`B` come back with `numNested = 1` and
  three recursors, `A.rec`, `B.rec` and `A.rec_1`. Nothing in the 205-file
  corpus has the shape, so it was neither covered nor known to decline.
* `nest_mutual_both` — the same axis, **non-degenerately**: `A` nests at `List
  B`, `B` nests at `Box A`, so there are four block members, two mimics at two
  distinct containers, and four recursors sharing one motive and minor vector.
  With only one member nesting, a single carrier and a per-member carrier
  family are the same thing; here they are not.
* `nest_through_nested` — nesting through a container that is *itself* a
  nested inductive. This refutes a load-bearing sentence in
  `mini/src/nested_ev.rs`: "nesting strictly decreases, so this is a
  topological order and a cycle cannot arise". `T` nests into `Tree T`;
  `Tree`'s own `node` field is `List (Tree T)`; *that* copy's `cons` head is
  `Tree T` again. `pack₀` and `pack₁` call each other and no emission order
  exists. `Tree` in the same file still gets its model, so the fixture
  distinguishes the cycle check from a refusal to do anything. -/
def expectedOwn : List Row :=
  [ ("poly_nested", [("PTree", 15), ("QTree", 22)], [])
  , ("indexed_decl", [],
      [ ("ITree", "nested model with indices")
      , ("I2", "nested model with indices") ])
  , ("indexed_container", [],
      [ ("VTree", "nested model with indices")
      , ("WTree", "nested model with indices") ])
  , ("dependent_fields", [("DTree", 15), ("ETree", 15), ("KTree", 15)], [])
  , ("infinitary", [],
      [ ("FTree", "nested model shape: FTree._model.0.branch has a recursive field under a binder")
        -- A field at a **mimic** under a binder is not caught by that guard —
        -- it is `HTree._model.ctor_1` that the kernel then rejects, because the
        -- constructor wants `N → HTree._model.1` and the export's type says
        -- `N → HTree._model.self`. A shape decline all the same, but a late one.
      , ("HTree", "nested model shape: [HTree._model.ctor_1] rejected by the kernel:") ])
  , ("decline_no_eq", [], [("Tree", "nested model without Eq")])
  , ("nest_through_mutual", [], [("A", "nested model in a mutual block")])
  , ("nest_mutual_both", [], [("A", "nested model in a mutual block")])
  , ("nest_through_nested", [("Tree", 15)],
      [("T", "nested model with mutually recursive occurrences")])
  ]

structure TAcc where
  failures : Array String := #[]
  checks : Nat := 0

def check (a : TAcc) (ok : Bool) (msg : String) : TAcc :=
  { a with checks := a.checks + 1, failures := if ok then a.failures else a.failures.push msg }

def runOne (root : String) (a : TAcc) (r : Row) (dir := "mini/tests/fixtures") : IO TAcc := do
  let (name, want, wantDeclined) := r
  let path := s!"{root}/{dir}/{name}.ndjson"
  let text ← IO.FS.readFile path
  let .ok x := Modelgen.parse text | do
    return check a false s!"{name}: does not parse"
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<test>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, rep), _) ←
    Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (runFilter x true)) ctx { env }
  let mut a := a
  -- axis 1: the counts, in order
  let got := rep.generated.toList.map fun (n, k) => (n.toString, k)
  a := check a (got == want) s!"{name}: models are {got}, expected {want}"
  let gotD := rep.declined.toList.map fun (n, w) => (n.toString, w)
  -- By **prefix**: which shape stopped the generator is the claim, and a
  -- kernel diagnostic quoted inside the message is not.
  let declinesMatch :=
    gotD.length == wantDeclined.length &&
    (gotD.zip wantDeclined).all fun ((gn, gw), (wn, ww)) => gn == wn && ww.isPrefixOf gw
  a := check a declinesMatch s!"{name}: declines are {gotD}, expected {wantDeclined}"
  -- axis 3: the statements, against the installed recursors' own rules
  a := check a rep.stmtErrors.isEmpty s!"{name}: {rep.stmtErrors}"
  -- A fixture whose only declarations are refusals has nothing to compare;
  -- one that generated a model must have compared something.
  a := check a (rep.generated.isEmpty || rep.stmtChecked > 0)
    s!"{name}: a model was generated and no statement was compared"
  a := check a rep.recMismatch.isEmpty
    s!"{name}: the export's recursors differ from Lean's own: {rep.recMismatch}"
  -- axis 4: the round trip
  let out := ({ x with decls }).render
  match Modelgen.parse out with
  | .error e => a := check a false s!"{name}: the output does not parse: {e}"
  | .ok y =>
    a := check a (y.decls == decls) s!"{name}: the output does not read back as it was written"
    a := check a (y.decls.size == decls.size) s!"{name}: declaration count changed on the round trip"
  -- axis 4b: the identity on a file with nothing to splice
  let plainPath := s!"{root}/mini/tests/fixtures/nat_char_equations.ndjson"
  if ← System.FilePath.pathExists plainPath then
    let t ← IO.FS.readFile plainPath
    let .ok p := Modelgen.parse t | return check a false "nat_char_equations does not parse"
    let ((d2, r2), _) ←
      Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (runFilter p false)) ctx { env }
    a := check a r2.generated.isEmpty "nat_char_equations should have no model"
    a := check a (d2 == p.decls) "nat_char_equations is not passed through unchanged"
  return a

/-- `Lean.Syntax`: three block members, three recursors, the only case in reach
that can distinguish an ordering from a permutation of it. -/
def runSyntax (root : String) (a : TAcc) : IO TAcc := do
  let path := s!"{root}/vendor/arena-tests/good/init-prelude.ndjson"
  unless ← System.FilePath.pathExists path do
    IO.println "  (skipping Lean.Syntax: vendor/arena-tests is not present)"
    return a
  let text ← IO.FS.readFile path
  let .ok x := Modelgen.parse text | return check a false "init-prelude does not parse"
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<test>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((_, rep), _) ←
    Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (runFilter x true)) ctx { env }
  let mut a := a
  let got := rep.generated.toList.map fun (n, k) => (n.toString, k)
  a := check a (got == [("Lean.Syntax", 26)]) s!"Lean.Syntax: models are {got}"
  a := check a rep.stmtErrors.isEmpty s!"Lean.Syntax: {rep.stmtErrors}"
  -- three members, three recursors, seven ι rules — 10 statements
  a := check a (rep.stmtChecked == 10) s!"Lean.Syntax: {rep.stmtChecked} statements, expected 10"
  a := check a rep.recMismatch.isEmpty s!"Lean.Syntax: recursors differ: {rep.recMismatch}"
  return a

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let root := args.head?.getD ".."
  let mut a : TAcc := {}
  for r in expected do
    a ← runOne root a r
  for r in expectedOwn do
    a ← runOne root a r (dir := "modelgen/tests")
  a ← runSyntax root a
  IO.println s!"{a.checks} checks, {a.failures.size} failed"
  for f in a.failures do IO.println s!"  FAIL {f}"
  return if a.failures.isEmpty then 0 else 1
