/- The container's constructor has a **functional** field, so the mimic gets a
   field `N → B₀` — recursive under a binder. `Bₖ.rec`'s rule gives that an
   induction hypothesis and the ι statement writes none, so it is a decline
   rather than a wrong theorem. -/
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

--#export Eq N List Fn Tree

inductive Fn (α : Type) : Type where
  | mk : (N → α) → Fn α

inductive Tree : Type where
  | leaf : Tree
  | node : Fn Tree → Tree
