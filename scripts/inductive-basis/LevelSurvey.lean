/-
LevelSurvey.lean — how complete is level definitional equality, in Lean, in
lean4lean, and in lean4lean with `modelgen`'s local prune patch applied?

This file does NOT compile against this repository's toolchain alone: it
imports `Lean4Lean.Level`, so it needs a lean4lean checkout with the patch in
`lean4lean-level-prune.patch` beside this file. Reproduce with

  git clone https://github.com/digama0/lean4lean vendor-l4l/lean4lean
  cd vendor-l4l/lean4lean && git checkout 3dc52e0
  echo leanprover/lean4:v4.29.1 > lean-toolchain      # ours; upstream differs
  git apply ../../scripts/inductive-basis/lean4lean-level-prune.patch
  lake build
  cp ../../scripts/inductive-basis/LevelSurvey.lean .
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  P=$PWD/.lake/build/lib/lean:$PWD/.lake/packages/batteries/.lake/build/lib/lean
  env -u LEAN_PATH LEAN_SYSROOT=$T LEAN_PATH=$P $T/bin/lean LevelSurvey.lean

Pinned revision: 3dc52e0 "Prove Expr cached flag correctness (#19)".
`vendor-l4l/` is gitignored, like `/vendor`. The clone's `origin/master` is 24
commits further on, but `Lean4Lean/Level.lean`'s `Normalize` namespace — the
function under test — is byte-identical across that gap, so these rows cannot
move; see MODELGEN.md §8.6.

Four judgements per pair: `sem` (brute force over all assignments in 0..4),
`lean` (`Level.isEquiv`), `l4lStock`, `l4lPatch`. MODELGEN.md §8.6 records the
table and what it settles. In one line: the patch agrees with `sem` on every
row here and on 33,670 fuzzed pairs, which is a measurement against a bounded
oracle and **not a completeness proof**; it closes `modelgen`'s `BoxF` level
identity, which Lean and stock lean4lean both reject; and `BoxF` remains a
decline regardless, because the contract is that a proof Lean's kernel rejects
is a decline, never an emission.
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

/-!
This version of the survey is run against the LOCALLY PATCHED
`Lean4Lean/Level.lean` in `vendor-l4l/lean4lean`, which keeps the stock
predicate as `Level.isEquiv'Stock` and makes `Level.isEquiv'` compare pruned
normal forms.  Columns:

  sem        brute-force semantic equality over all assignments in 0..4
  lean       `Lean.Level.isEquiv`   (Lean's own normal-form comparison)
  l4lStock   `Lean.Level.isEquiv'Stock` (lean4lean as shipped at 3dc52e0)
  l4lPatch   `Lean.Level.isEquiv'`      (the nanodatg local patch)
-/

def pad (s : String) (n : Nat) : String := s.pushn ' ' (n - s.length)

#eval show IO Unit from do
  IO.println s!"{pad "pair" 46} sem    lean   l4lStock  l4lPatch"
  let mut unsound := 0
  let mut helped := 0
  let mut stillIncomplete := 0
  for (name, a, b) in pairs do
    let se := semEq 4 a b
    let le := Level.isEquiv a b
    let st := Level.isEquiv'Stock a b
    let px := Level.isEquiv' a b
    if px && !se then unsound := unsound + 1
    if px && !st then helped := helped + 1
    if se && !px then stillIncomplete := stillIncomplete + 1
    let flag :=
      if px && !se then "  *** UNSOUND ***"
      else if se && !px then "  <-- still incomplete"
      else if px && !st then "  <-- patch closes this"
      else ""
    IO.println s!"{pad name 46} {pad s!"{se}" 6} {pad s!"{le}" 6} {pad s!"{st}" 9} {pad s!"{px}" 9}{flag}"
  IO.println ""
  IO.println s!"patched-true-but-semantically-false (unsound) : {unsound}"
  IO.println s!"semantically-true-but-patched-false (gaps)    : {stillIncomplete}"
  IO.println s!"pairs the patch newly closes over stock       : {helped}"
