/-
# A class-(P) declaration that is recursive, with an interleaved field mask

**No non-indexed class-(P) declaration in the corpus is recursive.** `Exists`,
`PredWithTypeField`, `PropStructure` and `BoolProp` are all non-recursive, so
their field masks are `Plain, Plain, …` and every permutation question about
them is the identity. `derived::inductive::family::trunc_rec`'s `minor_atoms` is
positional against the **Lean field spine** — fields in declared order, then the
induction hypotheses — while the carrier's own order is plains-then-recs, and
whenever the mask interleaves the two differ by a permutation. That permutation
is the part of the class-(P) theorem most likely to be wrong, it has a synthetic
unit fixture in `derived/` that says so, and this is the export-level witness it
does not have.

`PTree.node` is the shape:

    node : (a : A) → (l : PTree) → (b : B) → (r : PTree) → (c : C) → PTree
           Plain     Rec           Plain     Rec           Plain

Five fields, three of them plain, and **the three plain field types are
distinct** — `A`, `B`, `C` are inductives with one, two and three constructors.
That is deliberate: if the plain fields all had the same type, every permutation
of them would be invisible, which is the mistake three tests on this project
already made. Two recursive fields, not one: with one, `Plain, Rec, Plain` and
plains-then-recs differ only in where a single element moved and several
orderings coincide. With two, `Plain Rec Plain Rec Plain` distinguishes the true
interleaving from plains-then-recs, from recs-then-plains, and from a reversal.

`PList` is the same class with a single interleaved recursive field, as the
smaller sibling: if `PTree` fails and `PList` passes, the failure is in the
two-recursive-field case specifically.

`PTree` and `PList` are class (P) and not class (S) because each has **two**
constructors, so Carneiro §2.6.2's second reason ("at most one constructor")
fails outright, and `Prop` is not provably nonzero so the first fails too. Each
also has a **closed** constructor, so the proposition is inhabited: a `Prop`
that is provably empty passes the truncation clause vacuously — `‖∅‖ = ∅` — and
the ι-rule can never fire on it. That is exactly the accident that made the
`Quot` equivalence-class clause look right.

# What this reaches today, and what it does not

* `ptreeTy` / `plistTy` reach `⟦PTree⟧` and `⟦PList⟧` and **derive**. That is
  new coverage on its own: `zoneb::build_trunc` truncates the ordinary §5.2
  carrier over the *erased* declaration, and no corpus class-(P) declaration is
  recursive, so a recursive erased declaration has never been through it.
* `ptreeLeaf` / `ptreeNode` / `plistNil` / `plistCons` reach the constructors
  and **do not**: `build_trunc` stores the carrier and no constructor at all, so
  they report `no-interp(PTree.leaf)` and friends.

So the interleaved-mask claim is **not yet reachable end to end** — the recursor
`trunc_rec` states sits behind a constructor interpretation that does not exist.
The test records the frontier where it actually is rather than asserting a
success this file cannot yet witness; when the class-(P) constructors are wired,
the negative rows here invert and the file becomes the mask test it was built to
be.
-/
prelude

--#export A B C PTree PList
--#export ptreeTy ptreeLeaf ptreeNode plistTy plistNil plistCons

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- One constructor. -/
inductive A : Type where
  | a0 : A

/-- Two constructors. -/
inductive B : Type where
  | b0 : B
  | b1 : B

/-- Three constructors — three, because two atoms cannot distinguish an
    ordering. -/
inductive C : Type where
  | c0 : C
  | c1 : C
  | c2 : C

/-- Class (P), recursive, non-indexed, mask `Plain Rec Plain Rec Plain` with
    three *distinct* plain field types. -/
inductive PTree : Prop where
  | leaf : PTree
  | node : (a : A) → (l : PTree) → (b : B) → (r : PTree) → (c : C) → PTree

/-- The same class with one recursive field: mask `Plain Rec Plain`. -/
inductive PList : Prop where
  | nil  : PList
  | cons : (a : A) → (t : PList) → (b : B) → PList

def ptreeTy : Prop := PTree
def ptreeLeaf : PTree := PTree.leaf
def ptreeNode (a : A) (l : PTree) (b : B) (r : PTree) (c : C) : PTree :=
  PTree.node a l b r c
def plistTy : Prop := PList
def plistNil : PList := PList.nil
def plistCons (a : A) (t : PList) (b : B) : PList := PList.cons a t b
