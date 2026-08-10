/- **The W arm** (`--prim-models`), `MODELGEN.md` §8.16 — the shapes the tuple
   tower cannot express and the tagged W construction can.

   `Wt` is `scripts/inductive-basis/WEmitted.lean`'s target, transcribed: six
   constructors chosen so that every shape the emitted scheme has to handle
   appears exactly once.

   * `leaf` — data, **no** children. The branch tower is empty at every index.
   * `one` — **no** data, one plain child. The data tower is the bare unit.
   * `two` — data **and two** plain children, which is where a dispatch that is
     right differs from one with its arms swapped.
   * `mix` — a plain child **and** an infinitary one **in the same
     constructor**, so the two towers are at different depths in one cascade.
   * `gap` — **data on both sides of a child**: the data tower and the branch
     tower index *different* subsequences of one telescope, and a generator
     that built the data from "the fields before the first recursive one"
     passes every other arm here.
   * `alt` — `leaf`'s shape at another tag. Two constructors of the same shape
     sharing a tag is **not** a type error, so this is the one mutation with no
     type error behind it, and the ι rule is what catches it.

   The other three targets are the parts `Wt` is monomorphic about:

   * `Tree` — a **parameter** and a **level parameter**, with the same
     branching. The towers are built at a parameter scope and the carrier is
     `Type u` for a variable `u`, which is what the terminating unit at exactly
     `Sort w` exists for.
   * `Br` — an infinitary child whose binder type is a **parameter** rather
     than a ground type, so the branch tower's own universe is variable too.
   * `Dep` — a non-recursive field whose type **depends on an earlier one**,
     beside a branching pair: the data tower is a dependent Σ-chain and this is
     what says so.

   `Bad` is the boundary from the other side and stays a decline: its
   infinitary child's binder type mentions an **earlier field**, so the branch
   type does not factor through the tag and there is no `B' : K → Type u` to
   give the core. `Modelgen.tagFactored` is the test and this is its fixture. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive P : Type where
  | one : P
  | two : P

inductive Q : Type where
  | a : Q
  | b : Q
  | c : Q

/-- Written with `P.rec` rather than a `match`: the equation compiler wants
`PProd`, and a `prelude` fixture has none. -/
def PFam (k : P) : Type := @P.rec (fun _ => Type) P Q k

inductive Wt : Type where
  | leaf : P → Wt
  | one : Wt → Wt
  | two : Q → Wt → Wt → Wt
  | mix : Wt → (P → Wt) → Wt
  | gap : P → Wt → Q → Wt → Wt
  | alt : P → Wt

inductive Tree (α : Type u) : Type u where
  | tip : α → Tree α
  | bin : Tree α → Tree α → Tree α

inductive Br (α : Type u) : Type u where
  | z : Br α
  | lim : (α → Br α) → Br α

inductive Dep : Type where
  | nil : Dep
  | mk : (k : P) → PFam k → Dep → Dep → Dep

inductive Bad : Type where
  | tip : Bad
  | lim : (k : P) → (PFam k → Bad) → Bad → Bad
