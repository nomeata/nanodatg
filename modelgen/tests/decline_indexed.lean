/- The nested declaration carries an **index**. `Reason::Indexed` has no
   occupant in the fixture tree; this is one. -/
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

--#export Eq N List ITree

inductive ITree : N → Type where
  | leaf : ITree N.z
  | node : List (ITree N.z) → ITree (N.s N.z)
