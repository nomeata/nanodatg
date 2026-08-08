import Modelgen.Mono

/-!
`monomorph IN.ndjson [-o OUT.ndjson] [--mono-recursors] [--default 0,1] [--quiet]`

The contract the output satisfies is `MONOMORPH.md` §1.
-/

open Lean Meta Modelgen Modelgen.Mono

structure Opts' where
  input : String := ""
  output : Option String := none
  opts : Mono.Opts := {}
  quiet : Bool := false

def usage : String :=
  "usage: monomorph IN.ndjson [-o OUT.ndjson] [--mono-recursors] [--default N[,N...]] [--check] [--quiet]"

def parseArgs : List String → Except String Opts'
  | [] => .error usage
  | args => go args {}
where
  go : List String → Opts' → Except String Opts'
    | [], o => if o.input.isEmpty then .error "no input file" else .ok o
    | "-o" :: p :: rest, o => go rest { o with output := some p }
    | "--mono-recursors" :: rest, o =>
      go rest { o with opts := { o.opts with monoRecursors := true } }
    | "--default" :: s :: rest, o =>
      let ds := (s.splitOn ",").filterMap (·.trimAscii.toString.toNat?)
      if ds.isEmpty then .error s!"--default wants a comma-separated list of naturals, got {s}"
      else go rest { o with opts := { o.opts with defaults := ds.toArray } }
    | "--check" :: rest, o => go rest { o with opts := { o.opts with check := true } }
    | "--quiet" :: rest, o => go rest { o with quiet := true }
    | a :: rest, o =>
      if a.startsWith "-" then .error s!"unknown flag {a}" else go rest { o with input := a }

def run (o : Opts') : IO UInt32 := do
  let text ← IO.FS.readFile o.input
  let x ←
    match Modelgen.parse text with
    | .error e => IO.eprintln s!"{o.input}: parse error: {e}"; return 1
    | .ok x => pure x
  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<monomorph>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((y, rep), _) ←
    Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (monomorphize x o.opts)) ctx { env }
  unless o.quiet do
    match rep.refused with
    | some why => IO.println s!"{o.input}: passed through unchanged — {why}"
    | none =>
      IO.println s!"{o.input}: {rep.declsIn} declarations in, {rep.declsOut} out \
        ({rep.recordsIn} → {rep.recordsOut} records), {rep.groups} groups, \
        {rep.carried.size} carried, {rep.defaulted} defaulted"
      IO.println s!"  copies per group: {rep.hist.toList}"
      IO.println s!"  carried: {rep.carried.toList}"
      IO.println s!"  recursors the kernel minted differently: {rep.recRegen}; \
        declarations the replay rejected: {rep.rejected}"
      unless rep.errors.isEmpty do
        IO.println s!"  {rep.errors.size} problems:"
        for e in rep.errors.toList.eraseDups.take 20 do IO.println s!"    ! {e}"
  match o.output with
  | none => pure ()
  | some p =>
    if rep.refused.isSome then IO.FS.writeFile p text
    else
      -- Streamed, not rendered: the whole file as one `String` is what
      -- `MONOMORPH.md` §9.5 measured failing on Mathlib.
      let h ← IO.FS.Handle.mk p .write
      y.writeTo (IO.FS.Stream.ofHandle h)
  return if rep.errors.isEmpty then 0 else 2

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok o => run o
