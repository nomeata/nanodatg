/- The **declaration** carries a universe parameter. `nested_ev::Reason::
   Polymorphic` has no occupant in the fixture tree; this is one. -/
prelude
universe u v
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a
inductive List (α : Type u) : Type u where
  | nil : List α
  | cons : α → List α → List α

--#export Eq List PTree

inductive PTree (α : Type u) : Type u where
  | leaf : α → PTree α
  | node : List (PTree α) → PTree α
