/-
LevelSurvey.lean — how complete is level definitional equality, in Lean and
in lean4lean, and does either one close `modelgen`'s `BoxF` decline?

This file does NOT compile against this repository's toolchain alone: it
imports `Lean4Lean.Level`, so it needs a lean4lean checkout. Reproduce with

  git clone https://github.com/digama0/lean4lean vendor-l4l/lean4lean
  cd vendor-l4l/lean4lean && git checkout 3dc52e0
  echo leanprover/lean4:v4.29.1 > lean-toolchain      # ours; upstream differs
  lake build
  cp <this file> . && T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T LEAN_PATH=$PWD/.lake/build/lib/lean \
    $T/bin/lean LevelSurvey.lean

Pinned revision: 3dc52e0 "Prove Expr cached flag correctness (#19)".
`vendor-l4l/` is gitignored, like `/vendor`.

It prints four judgements per pair: `sem` (brute-force semantic equality over
all assignments in 0..4), `lean` (`Level.isEquiv`, Lean's normal-form
comparison), `l4l` (lean4lean's experimental `Level.isEquiv'`), and `fix` (a
candidate repair of `isEquiv'`, below).

Findings, and `MODELGEN.md` §8.6 records them:

  * lean4lean is strictly more complete than Lean — it buys four imax
    distributivity/associativity laws Lean lacks.
  * It still does NOT absorb an `imax` into a `max` that dominates it, which
    is the one law `modelgen`'s `BoxF` decline needs. So the decline stands
    under both, and it is a level-arithmetic gap, not a type error: the last
    three rows show the field level, and the two pad candidates the planner
    tries, all semantically equal to the carrier's level at every assignment.
  * `isEquivFix` is the candidate repair. lean4lean's normal form is a map
    keyed by variable sets; `imax` paths leave entries with `const = 0` and
    no variables — keys that subsumption emptied but did not erase — and
    `isEquiv'` compares them structurally. Dropping empty entries first turns
    every semantically-true pair here true and leaves both false pairs false.
    That is a measurement on twelve pairs, not a completeness proof.

lean4lean documents the incompleteness itself, in its `divergences.md`:
`normalize'`/`isEquiv'`/`geq'` are "an experimental new algorithm … intended
to be complete for level algebra … currently known to be incomplete in cases
where Lean's algorithm is not", with the plan of record being to verify
Lean's original algorithm instead.
-/
import Lean4Lean.Level

open Lean

/-- Semantic evaluation of a level under an assignment. -/
partial def evalL (σ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => evalL σ l + 1
  | .max a b => Nat.max (evalL σ a) (evalL σ b)
  | .imax a b => let n := evalL σ b; if n = 0 then 0 else Nat.max (evalL σ a) n
  | .param n => σ n
  | .mvar _ => 0

def vars := [`u, `v, `w]

/-- brute-force semantic equality over all assignments in `0..N` -/
def semEq (N : Nat) (a b : Level) : Bool := Id.run do
  for i in [0:N+1] do
    for j in [0:N+1] do
      for k in [0:N+1] do
        let σ : Name → Nat := fun n =>
          if n == `u then i else if n == `v then j else if n == `w then k else 0
        if evalL σ a != evalL σ b then return false
  return true

def u : Level := .param `u
def v : Level := .param `v
def w : Level := .param `w
def mx := Level.max
def imx := Level.imax
def s := Level.succ
def one : Level := s .zero
def two : Level := s one

def pairs : List (String × Level × Level) := [
  ("max 1 u v  ~  max 1 (imax u v) u v",
    mx one (mx u v), mx one (mx (imx u v) (mx u v))),
  ("imax u u  ~  u", imx u u, u),
  ("imax u (u+1)  ~  u+1", imx u (s u), s u),
  ("max u (imax u v)  ~  max u (imax u v)+0", mx u (imx u v), mx u (imx u v)),
  ("imax (max u v) w  ~  max (imax u w) (imax v w)",
    imx (mx u v) w, mx (imx u w) (imx v w)),
  ("imax u (max v w)  ~  max (imax u v) (imax u w)",
    imx u (mx v w), mx (imx u v) (imx u w)),
  ("max 1 u  ~  max 1 (imax v u) u", mx one u, mx one (mx (imx v u) u)),
  ("max u v  ~  max u v (imax u v)", mx u v, mx (mx u v) (imx u v)),
  ("max 2 v  ~  imax 2 v", two, imx two v),
  ("imax u (imax v w)  ~  imax (max u v) w", imx u (imx v w), imx (mx u v) w),
  ("u+1  ~  max 1 (u+1)", s u, mx one (s u)),
  ("max u (u+1)  ~  u+1", mx u (s u), s u),
  ("imax 1 u  ~  u", imx one u, u),
  ("max 1 (imax u v)  ~  max 1 v (imax u v)", mx one (imx u v), mx one (mx v (imx u v))),
  -- modelgen's `BoxF` decline (tests/prim_declines.lean): the field's level
  -- against the carrier's, with the pad the planner would try.
  ("BoxF field alone: imax (imax u v) v  ~  max 1 u v",
    imx (imx u v) v, mx one (mx u v)),
  ("BoxF padded at w:  max 1 (imax (imax u v) v) (max 1 u v)  ~  max 1 u v",
    mx (mx one (imx (imx u v) v)) (mx one (mx u v)), mx one (mx u v)),
  ("BoxF padded at max 1 u: max (imax (imax u v) v) (max 1 u)  ~  max 1 u v",
    mx (imx (imx u v) v) (mx one u), mx one (mx u v))
]

/-- lean4lean's `isEquiv'`, but ignoring `NormLevel` entries that carry no
information (`const = 0` and no vars) — these are keys created by `imax` paths
that subsumption emptied but did not erase. -/
def isEquivFix (a b : Level) : Bool :=
  let strip (m : Level.Normalize.NormLevel) : List (List Name × Level.Normalize.Node) :=
    m.toList.filter fun (_, n) => !(n.const == 0 && n.var.isEmpty)
  let na := strip (Level.Normalize.normalize a)
  let nb := strip (Level.Normalize.normalize b)
  na.length == nb.length && (na.zip nb).all fun ((p1, n1), (p2, n2)) => p1 == p2 && n1 == n2

#eval show IO Unit from do
  IO.println s!"{"pair".pushn ' ' 42} sem  lean  l4l  fix"
  for (name, a, b) in pairs do
    let se := semEq 4 a b
    let le := Level.isEquiv a b
    let l4 := Level.isEquiv' a b
    let fx := isEquivFix a b
    let flag := if fx != se then "  UNSOUND-OR-INCOMPLETE-FIX" else if se != l4 then "  <-- l4l incomplete, fix helps" else ""
    IO.println s!"{name.pushn ' ' (46 - name.length)} {se}  {le}  {l4}  {fx}{flag}"
