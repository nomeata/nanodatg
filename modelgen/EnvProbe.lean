import Modelgen.Driver

/-!
`envprobe IN.ndjson [P|A|B|C]` — **what a replayed export is visible as, and
whether Lean's kernel takes it.**

`MODELGEN.md` §6.6 and §6.7 rest on three facts about Lean's environment that
nothing else in this repository can produce a number for, and this is the
program that produced them. It is not a test: `Test.lean`'s `runEnvProbe` pins
the same two properties on a fixture so a toolchain bump cannot make this
document stale silently. What this adds is *scale* — the counts in §6.6 are
Mathlib's and take twenty minutes and 24 GB to obtain.

* **`P`** — parse and stop. Says how much of the pass's peak is the parsed
  export rather than the environment built from it.
* **`A`** — parse, then replay through `Environment.addDeclCore`, which is
  what `Modelgen.runFilter` does. Counts and prints the names that are in the
  **kernel** constant map and invisible to `Environment.find?`: the
  `AsyncConsts.add` panic's victims, and the auxiliary `T.rec_k` of every
  nested inductive, which `Declaration.getNames` documents itself as omitting.
* **`B`** — parse, then replay through
  `Kernel.Environment.addDeclWithoutChecking` and hand the result to
  `Environment.ofKernelEnv`, which is `lean4checker`'s loading model. Counts how
  many names survive into `Environment.find?`, which is the lookup `MetaM` uses.

* **`C`** — parse, then replay through `Environment.addDeclCore` **with
  checking on**, and report how many declarations the kernel *rejected*, with
  the first few reasons. This is the whole-output oracle: `modelgen` checks
  each declaration it generates as it generates it, against the environment it
  has built so far, and `C` asks the independent question — does the emitted
  file, read back from bytes and replayed from nothing, typecheck end to end.
  `A` deliberately swallows rejections (it is asking about visibility, not
  validity); `C` is the mode that counts them.

No argument: `A` then `B`. Both replays in one process needs twice the memory of
one, so on anything Mathlib-sized pass a mode.
-/

open Lean Meta Modelgen

def probeA (x : Export) (names : Array Name) (env0 : Environment) : IO Unit := do
  let mut env := env0
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      match env.addDeclCore 0 dcl none false with
      | .ok e => env := e
      | .error _ => pure ()
  let kenv := env.toKernelEnv
  let mut lost : Array Name := #[]
  for n in names do
    if (kenv.find? n).isSome && (env.find? n).isNone then lost := lost.push n
  IO.println s!"A addDeclCore: {names.size} names, {lost.size} in the kernel map and \
    invisible to Environment.find?"
  for n in lost do IO.println s!"  lost {n}"

/-- Replay with the kernel switched on, and count what it refuses. -/
def probeC (x : Export) (env0 : Environment) : IO Unit := do
  let mut env := env0
  let mut ok := 0
  let mut bad : Array String := #[]
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      match env.addDeclCore 0 dcl none true with
      | .ok e => env := e; ok := ok + 1
      | .error ex =>
        bad := bad.push s!"{dcl.getTopLevelNames}: {← (ex.toMessageData {}).toString}"
  IO.println s!"C checked replay: {ok} accepted, {bad.size} rejected"
  for m in bad[0:10] do IO.println s!"  rejected {m}"

def probeB (x : Export) (names : Array Name) (env0 : Environment) : IO Unit := do
  let mut kenv := env0.toKernelEnv
  for d in x.decls do
    if let some dcl := toDeclaration (Environment.ofKernelEnv kenv) d then
      match kenv.addDeclWithoutChecking dcl with
      | .ok e => kenv := e
      | .error _ => pure ()
  let envB := Environment.ofKernelEnv kenv
  let mut visB := 0
  let mut visK := 0
  for n in names do
    if (envB.find? n).isSome then visB := visB + 1
    if (kenv.find? n).isSome then visK := visK + 1
  IO.println s!"B kernel replay: {visK} of {names.size} in Kernel.Environment.find?, \
    {visB} visible to Environment.find? after ofKernelEnv"

def main (args : List String) : IO UInt32 := do
  let path :: rest := args | do IO.eprintln "usage: envprobe IN.ndjson [P|A|B]"; return 1
  let text ← IO.FS.readFile path
  let .ok x := Modelgen.parse text (analyse := false) | do IO.eprintln s!"{path}: parse error"; return 2
  initSearchPath (← findSysroot)
  let env0 ← importModules #[] {}
  let mut names : Array Name := #[]
  for d in x.decls do names := names ++ d.names.toArray
  if rest == ["P"] then
    IO.println s!"P parse only: {x.decls.size} records, {names.size} names"
    return 0
  if rest == ["C"] then probeC x env0; return 0
  unless rest == ["B"] do probeA x names env0
  unless rest == ["A"] do probeB x names env0
  return 0
