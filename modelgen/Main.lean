import Modelgen.Driver

/-!
`modelgen IN.ndjson [-o OUT.ndjson] [--check-recursors] [--quiet]`
-/

open Lean Meta Modelgen

structure Opts where
  input : String := ""
  output : Option String := none
  checkRecursors : Bool := false
  quiet : Bool := false

def parseArgs : List String → Except String Opts
  | [] => .error "usage: modelgen IN.ndjson [-o OUT.ndjson] [--check-recursors] [--quiet]"
  | args => go args {}
where
  go : List String → Opts → Except String Opts
    | [], o => if o.input.isEmpty then .error "no input file" else .ok o
    | "-o" :: p :: rest, o => go rest { o with output := some p }
    | "--check-recursors" :: rest, o => go rest { o with checkRecursors := true }
    | "--quiet" :: rest, o => go rest { o with quiet := true }
    | a :: rest, o =>
      if a.startsWith "-" then .error s!"unknown flag {a}" else go rest { o with input := a }

def run (o : Opts) : IO UInt32 := do
  let text ← IO.FS.readFile o.input
  let x ←
    match Modelgen.parse text with
    | .error e => IO.eprintln s!"{o.input}: parse error: {e}"; return 1
    | .ok x => pure x
  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<modelgen>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, rep), _) ←
    (Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (runFilter x o.checkRecursors)) ctx { env })
  unless o.quiet do
    if let some why := rep.unreplayable then
      IO.println s!"{o.input}: passed through unchanged — {why}"
    for (n, k) in rep.generated do IO.println s!"{n}: model of {k} declarations"
    for (n, why) in rep.declined do IO.println s!"{n}: declined — {why}"
    unless rep.stmtChecked == 0 do
      IO.println s!"statements: {rep.stmtChecked} compared against the installed recursors' \
        own rules, {rep.stmtErrors.size} differ"
      for e in rep.stmtErrors do IO.println s!"  ! {e}"
    if o.checkRecursors then
      IO.println s!"recursors: {rep.recChecked} checked against Lean's own, \
        {rep.recMismatch.size} differ{if rep.recMismatch.isEmpty then "" else s!": {rep.recMismatch}"}"
  match o.output with
  | none => pure ()
  | some p =>
    -- A file with nothing to splice is copied byte for byte; re-interning is
    -- only forced because `nanoda` requires continuous back-references.
    if rep.generated.isEmpty || rep.unreplayable.isSome then IO.FS.writeFile p text
    else IO.FS.writeFile p ({ x with decls }.render)
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok o => run o
