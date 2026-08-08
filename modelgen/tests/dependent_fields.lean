/- **A constructor field's type mentions an earlier field.** Lean supports it,
   and the congruence fold only needs the fields it *moves* to be independent:
   a packed position is replaced one at a time, so a later field whose type
   mentions a *packed* one would be left ill-typed, and a later field whose
   type mentions a plain one is not touched at all.

   Both orders are here, because a guard phrased as "nothing depends on
   anything after the last moved field" would pass one and fail the other:

   * `DTree.node : (n : N) → Vec N n → List DTree → DTree` — the dependency is
     **before** the moved field.
   * `ETree.node : List ETree → (n : N) → Vec N n → ETree` — the dependency is
     **after** it.

   A field whose type depends on a **moved** field is not here, because Lean
   does not support it either: `node : (l : List GTree) → Len l N.z → GTree`
   fails Lean's own nested compilation with `unknown constant 'GTree'` — the
   auxiliary block replaces `List GTree` with a fresh member and `Len l` is
   then about a constant that does not exist yet. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

--#export Eq N List Vec DTree ETree

inductive DTree : Type where
  | leaf : DTree
  | node : (n : N) → Vec N n → List DTree → DTree

inductive ETree : Type where
  | leaf : ETree
  | node : List ETree → (n : N) → Vec N n → ETree
