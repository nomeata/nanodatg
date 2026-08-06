/-
# Why a nested inductive is **not** the same dance

The mutual arc works because a `mutual … end` block can be *replaced* by an
auxiliary inductive: the members are new names, the encoding is free to define
them, and every recursor rule comes out definitionally
(`mutual_aux_encoding.lean`). The obvious next move is to do the same to a
nested declaration, since Lean's own nested compiler reduces

```text
inductive Tree | leaf | node : List Tree → Tree
```

to the *mutual block* `{Tree, ListTree}` that `mutual_expr_stmt_ast.lean`
spells out by hand — and zone A already takes such a block.

**It does not work, and this file is the measurement rather than the argument.**

# The one thing that is different, and it is fatal

In a mutual block every member is a name the encoding introduces. In a nested
declaration, `List` is a constant that **already exists**, with an
interpretation already fixed by its own declaration, and `List Tree` is an
application of it. The encoding can define `Tree` and it can define a
specialised copy `LT`, but it cannot define `List Tree` — so the two are
different types related by a pair of maps

```text
toAux   : List Tree → LT      -- by `List.rec`
fromAux : LT → List Tree      -- by `Aux.rec` at the tag-packed motive
```

and every constructor and every recursor rule the export declares is stated at
`List Tree` while the encoding computes at `LT`. Bridging them needs
`fromAux (toAux l) ≡ l`, which is a **propositional** round trip and not a
definitional one. `mini/tests/nested.rs` builds exactly that theorem out of the
constants below and asserts the kernel **rejects** it — with the same theorem at
two *closed* arguments accepted as the controls, because the round trip does
hold one ι step at a time and what fails is holding it uniformly.

Carneiro says the same thing in one line — `thesis.txt:902`, on how Lean differs
from Coq: mutual inductives, nested inductive types and coinductive types "can
all be encoded using regular inductives, although **some definitional equalities
may fail to hold in the encodings**". This file is *which* equality, for *this*
encoding.

# Where the rest of this lives

This fixture is one leg of a three-legged record and is not self-sufficient:
the write-up is `MINI-DESIGN.md` §9 ("Nesting is not this dance"), the assertion
is `mini/tests/nested.rs`, and the declaration-side shapes are
`nested_shapes.lean`. Nothing here is *used* by the checker — the file exists so
that the finding is re-measured on every run instead of remembered.

# What Lean's kernel does instead, read off the export

`scripts/export-fixture.sh` on a nested `Tree` emits **one** `Declar::Inductive`
with `all = [Tree]` and `numNested = 1`, and **two** recursors:

| constant | motives | minors | rules for |
| --- | --- | --- | --- |
| `Tree.rec` | 2 | 4 | `Tree.leaf`, `Tree.node` |
| `Tree.rec_1` | 2 | 4 | `List.nil`, `List.cons` |

So the un-specialisation has already happened in the exporter, and what the
kernel keeps is a *primitive* `Tree.rec_1` that eliminates the **real**
`List Tree` and ι-reduces on the **real** `List`'s constructors. That is a
reduction rule no encoding produces: it is a recursor for one type computing on
another type's constructors. `nested_shapes.lean` is the fixture that measures
the declaration side.

# The file compiles, and that is deliberate

Everything here is well-typed Lean. The refutation is not that something fails
to elaborate — it is that one *particular* equation between well-typed terms is
not definitional, and that has to be asserted by a checker rather than by a
comment, or it rots. `mini`'s kernel is the checker that asserts it.
-/
prelude

--#export Eq List Tag Aux Tree LT toAux fromAux treeLeaf treeNode

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. The test builds its theorem
    with this. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The container being nested into. It exists *before* `Tree` and has its own
    interpretation, which is the whole difficulty. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- The tag of the specialised block `{Tree, ListTree}`. -/
inductive Tag : Type where
  | t0 : Tag
  | t1 : Tag

/-- The specialised block, encoded exactly as `mutual_aux` would encode it:
    `Tree`'s two constructors and the specialised `List`'s two, under one
    tag-indexed inductive. -/
inductive Aux : Tag → Type where
  | leaf : Aux Tag.t0
  | node : Aux Tag.t1 → Aux Tag.t0
  | nil  : Aux Tag.t1
  | cons : Aux Tag.t0 → Aux Tag.t1 → Aux Tag.t1

def Tree : Type := Aux Tag.t0

/-- The specialised copy of `List Tree`. Isomorphic to it, and not it. -/
def LT : Type := Aux Tag.t1

/-- One way, by `List.rec`. -/
noncomputable def toAux : List Tree → LT :=
  @List.rec Tree (fun _ => LT) Aux.nil (fun h _ ih => Aux.cons h ih)

/-- The other way, by `Aux.rec` at the tag-packed motive — the same packing
    `mutual_aux` builds. -/
noncomputable def fromAux : LT → List Tree :=
  @Aux.rec (@Tag.rec (fun t => Aux t → Type) (fun _ => Tree) (fun _ => List Tree))
    Aux.leaf
    (fun l _ => Aux.node l)
    List.nil
    (fun _ _ ih1 ih2 => List.cons ih1 ih2)
    Tag.t1

def treeLeaf : Tree := Aux.leaf

/-- What `Tree.node : List Tree → Tree` would have to be. It typechecks — the
    encoding gets this far. -/
noncomputable def treeNode (l : List Tree) : Tree := Aux.node (toAux l)
