/-
# A block where only one member is recursive

A `mutual … end` block is one declaration to the kernel whether or not its
members actually refer to one another. This file is the degenerate end of that:
`OA` is recursive (directly, and through `OB`), `OB` refers to nothing, and `OC`
refers to `OB` but nothing refers to `OC`.

**All three are still one block**, with one shared motive telescope and one
shared minor telescope, and `OB.rec` and `OC.rec` therefore take motives and
minors for constructors they can never reach. That is the thing to get right: a
builder that computes each member's recursor from *that member's* reachable
constructors produces an `OB.rec` with two motives instead of three and one
minor instead of five, which is a different constant from the one Lean exports,
and every later use of it is ill-typed against the real one.

The export's `isRec` flag differs across the three members while `all` does not,
so this is also the file that says mini reads block membership from `all` and
not from whether recursion is present.

# Why the recursion is arranged this way

`OA.self : OA → OA` is *direct* recursion inside a mutual block, which is the
case a builder that only looks for cross-member occurrences misses. `OA.fromB`
is the cross-member occurrence, so `OA`'s two constructors need induction
hypotheses at two different motives. `OB` is a two-constructor enumeration with
no fields, so its minors are plain values and its `rec` is the one most likely
to be silently built as a non-mutual recursor. `OC` is downstream-only: nothing
in the block mentions it, so if block membership were inferred from the
reachability graph rather than read, `OC` would fall out of the block entirely.
-/
prelude

--#export OA OB OC
--#export oaTy obTy ocTy oaSelf oaFromB ocFromB

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

mutual

/-- The only recursive member: direct recursion *and* a cross-member field. -/
inductive OA : Type where
  | fromB : OB → OA
  | self : OA → OA

/-- A plain enumeration that happens to be inside the block. -/
inductive OB : Type where
  | b0 : OB
  | b1 : OB

/-- Downstream only: it mentions `OB`, and nothing mentions it. -/
inductive OC : Type where
  | fromB : OB → OC

end

def oaTy : Type := OA
def obTy : Type := OB
def ocTy : Type := OC
def oaSelf (a : OA) : OA := OA.self a
def oaFromB (b : OB) : OA := OA.fromB b
def ocFromB (b : OB) : OC := OC.fromB b
