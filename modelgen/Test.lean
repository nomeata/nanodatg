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
is meant to go away. `poly_nested`, `dependent_fields`, `indexed_decl`,
`indexed_container` and `nest_index_cross` no longer decline at all, so what
remains is **one**:

* `infinitary` — only its `HTree`, a field at a *mimic* under a binder.

**`indexed_container` and `nest_index_cross` are the axis that just closed**,
and they are here rather than in the passing list above because they are what
says it closed. `VTree` is the shape; `WTree` says one mimic serves two index
values, because the occurrence is the container at its *parameters*; `UTree` is
the non-degenerate one, since a single index at a constant value cannot
distinguish a telescope that is threaded from one that is dropped — `Tab α :
N → N → Type` has two, `UTree.node` sits at two differing values, and `Tab`'s
own recursion moves them one at a time. `nest_index_cross` is that shape
crossed with the *declaration's* own indices (`CTree`), with a mutual block
(`PA`/`PB`), and with a cycle of mimics whose family recursors are themselves
indexed (`XT` over `ITr`).

Two refusals are not of that kind:

* `decline_no_eq` — the export declares no `Eq`. The round trips are
  equations; this tool does not fabricate an equality Lean never wrote, and
  there is nothing here to fix.
* `nest_through_nested`, below.

**`nest_through_mutual` and `nest_mutual_both` are no longer refusals at all.**
A mutual block whose members nest is a shape Lean has and nothing in the
205-file corpus does, so it was neither covered nor known to decline; it is
now generated. `nest_mutual_both` is the non-degenerate fixture for it — `A`
nests at `List B` and `B` at `Box A`, four block members, two mimics at two
distinct containers, and four recursors `A.rec`, `B.rec`, `A.rec_1`, `A.rec_2`
over one shared motive and minor vector — because with only one member nesting
a single carrier and a per-member carrier family are the same object.
**`nest_through_nested` and `nest_cycle_group` are no longer refusals either.**
Nesting through a container that is *itself* a nested inductive refutes a
load-bearing sentence in `mini/src/nested_ev.rs` — "nesting strictly decreases,
so this is a topological order and a cycle cannot arise". `T` nests into `Tree
T`; `Tree`'s own `node` field is `List (Tree T)`; *that* copy's `cons` head is
`Tree T` again, so `pack₀` and `pack₁` are mutually recursive and no emission
order exists. They are not two recursions but one, and Lean already generated
it: `Tree.rec` and `Tree.rec_1`, over a single motive and minor vector.

`nest_cycle_group` is the non-degenerate fixture for that, because
`nest_through_nested`'s single cycle cannot distinguish two things.
`U.mk : List (Tree U) → U` puts a container that anchors **nothing** (`List`
is not nested) at mimic 0, so the family has to be found from mimic 1 and the
mimic-to-family mapping is the transposition rather than the identity.
`V.mk : Box (Tree V) → V` puts an ordinary mimic **outside** the cycle and
depending on it, so the condensation is a real DAG and the cycle has to be
emitted first.

**`nest_mutual_cycle` is the two family axes at once**, because nothing says
they compose. `P`/`Q` is a mutual block that nests through a nested container:
five block members, five recursors over one shared vector, a cyclic pair of
mimics beside an ordinary one, and a carrier family. `R`/`S` crosses the mutual
axis with a level parameter of the declaration's own.

**`nest_family_edges` is the pair of edges two members cannot reach.** A mutual
block of **three** — with two, `A.rec_1` is equally "the first member's
namespace" and "the previous member's", and only three say which. And a cycle
whose family is a **mutually recursive pair of containers** rather than a
nested one, which is the other arm of the family lookup: `C`'s block has two
real members and no nesting where `Tree`'s has one and one.

**`nest_mutual_index` is the mutual axis crossed with the declaration's own
indices**, which nothing tested: `nest_mutual_both` has no index anywhere and
`indexed_decl` is not mutual, so a treatment that read the first member's index
count for every member passes both. `MA : N → Type` and `MB : N → N → Type`
have index telescopes of **different lengths** and the two mimics have none, so
one motive vector carries three distinct arities; each member has a recursive
field whose index differs from its result's, and both members nest. -/
def expectedOwn : List Row :=
  [ ("poly_nested", [("PTree", 15), ("QTree", 22)], [])
  , ("indexed_decl", [("ITree", 15), ("I2", 15), ("I3", 15)], [])
  , ("indexed_container", [("VTree", 15), ("WTree", 17), ("UTree", 16)], [])
  , ("nest_index_cross", [("ITr", 15), ("CTree", 15), ("PA", 29), ("XT", 21)], [])
  , ("dependent_fields", [("DTree", 15), ("ETree", 15), ("KTree", 15)], [])
    -- `HTree` is the one shape in this file that is still open, and the
    -- obstruction is the proof and not the statement: the block types
    -- `(N → List HTree)` at `N → B₁`, so the recursor's minor would transport
    -- along `(fun n => pack₀ (unpack₀ (f n))) = f`, which is **funext**.
  , ("infinitary", [("FTree", 17), ("GTree", 15), ("ZTree", 22)],
      [("HTree", "nested model shape: HTree._model.0.node has a field at a mimic under a binder")])
  , ("decline_no_eq", [], [("Tree", "nested model without Eq")])
  , ("nest_through_mutual", [("A", 19)], [])
  , ("nest_mutual_both", [("A", 28)], [])
  , ("nest_through_nested", [("Tree", 15), ("T", 23)], [])
  , ("nest_cycle_group", [("Tree", 15), ("U", 23), ("V", 30)], [])
  , ("nest_mutual_cycle", [("Tree", 15), ("P", 37), ("R", 21)], [])
  , ("nest_family_edges", [("A1", 34), ("X", 23)], [])
  , ("nest_mutual_index", [("MA", 32)], [])
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
