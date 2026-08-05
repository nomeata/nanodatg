/-
# Three members in a cycle, and every position pinned by an application

**Two mutually recursive types cannot distinguish a permutation from a clamp.**
A mutual block's recursor takes *one motive per member of the block* and *one
minor per constructor of every member*, and both lists are ordered by the
block's declaration order. With two members, a builder that reverses the motive
list and a builder that emits the second motive twice produce the same wrong
answer on half the cases and the *right* answer on the other half; with three,
`A B C` versus `C B A` versus `A A A` are three different types.

So the block here is a **cycle**: `A` holds a `B`, `B` holds a `C`, `C` holds an
`A`. No member's constructor list is a rotation of another's — `A`'s recursive
field is at `B`, `B`'s at `C`, `C`'s at `A` — so the motive a minor's induction
hypothesis is stated at is different for each of the three, and a builder that
uses "the motive of the type being eliminated" rather than "the motive of the
field's own type" is wrong at all three minors rather than accidentally right.

# The recursors are applied positionally, on purpose

`aSize` and `cSize` are `@A.rec`/`@C.rec` with **every argument given
positionally**: three motives, then six minors, in block order. Named arguments
(`motive_1 := …`) would let Lean re-order them and the fixture would stop
measuring the order. Applying two *different* members' recursors to the *same*
argument list is the other half of the claim: `A.rec` and `C.rec` of a mutual
block share their motive and minor telescopes exactly and differ only in the
major argument's type and the result motive, so the two `def`s here typecheck
against the same spine and would not if the shared prefix were built per member.

Both are `noncomputable`: Lean's code generator refuses a bare recursor
application, and the compiler's opinion is not what is under test.
-/
prelude

--#export A B C
--#export aTy bTy cTy aOfB bOfC cOfA aSize cSize

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- The result type of the two recursor applications. Not `Nat`: `Nat` is a
    literal-carrying inductive and would drag `Expr.natLit` into a file that is
    about member order. -/
inductive N : Type where
  | z : N
  | s : N → N

mutual

/-- Recursive through `B`. -/
inductive A : Type where
  | a0 : A
  | aB : B → A

/-- Recursive through `C`. -/
inductive B : Type where
  | b0 : B
  | bC : C → B

/-- Recursive through `A`, closing the cycle. -/
inductive C : Type where
  | c0 : C
  | cA : A → C

end

def aTy : Type := A
def bTy : Type := B
def cTy : Type := C
def aOfB (b : B) : A := A.aB b
def bOfC (c : C) : B := B.bC c
def cOfA (a : A) : C := C.cA a

/-- Three motives, six minors, positional. -/
noncomputable def aSize : A → N :=
  @A.rec (fun _ => N) (fun _ => N) (fun _ => N)
    N.z (fun _ ih => N.s ih)
    N.z (fun _ ih => N.s ih)
    N.z (fun _ ih => N.s ih)

/-- The same spine, a different major type and a different result motive. -/
noncomputable def cSize : C → N :=
  @C.rec (fun _ => N) (fun _ => N) (fun _ => N)
    N.z (fun _ ih => N.s ih)
    N.z (fun _ ih => N.s ih)
    N.z (fun _ ih => N.s ih)
