/-
SortPolyNeg.lean — negative probes companion to SortPolyProbe.lean.

Pins, at leanprover/lean4:v4.29.1, with Lean's own error messages:
  N1. the kernel's one per-argument level rule — an argument whose level is
      not provably (`is_geq`) below the resultant level is refused even with
      the elaborator's resultant-universe check disabled;
  N2. the elaborator's blanket refusal of maybe-zero resultant sorts, which
      SortPolyProbe.lean's kernel-level positives are admitted behind;
  N3. Lean's level definitional equality is normal-form equality, NOT
      semantic equality: max 1 u v and max 1 (imax u v) u v agree at every
      instantiation, yet do not unify. (This is why exact-level carrier
      placement cannot in general be had by padding a PSigma chain, and why
      the basis needs a level-constrained lift or the checker a complete
      level arithmetic.)

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean SortPolyNeg.lean

Expected: 0 errors (all failures are pinned with #guard_msgs).
-/
universe u v

-- N1: the kernel's per-argument level rule.
/--
error: Invalid universe level in constructor `N1.mk`: Parameter has type
  α
at universe level
  v+1
which is not less than or equal to the inductive type's resulting universe level
  u
-/
#guard_msgs in
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive N1 (α : Type v) : Sort u
  | mk : α → N1 α

-- N2: the elaborator's blanket maybe-zero refusal (kernel-admissible shape).
/--
error: Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
-/
#guard_msgs in
inductive N2 : Sort u
  | unit

-- N3: max does not absorb a semantically dominated imax.
/--
error: Type mismatch
  PUnit
has type
  Sort (max 1 (imax u v) u v)
of sort `Type (max 1 (imax u v) u v)` but is expected to have type
  Sort (max 1 u v)
of sort `Type (max 1 u v)`
-/
#guard_msgs in
example : Sort (max 1 u v) := PUnit.{max 1 (imax u v) u v}
