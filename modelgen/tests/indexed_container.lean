/- **The container the declaration nests into carries indices.** Lean supports
   it. `VTree.rec_1` comes back with `numIndices = 1` and a mimic motive
   `(a : N) → Vec VTree a → Sort u`: the occurrence is the container at its
   **parameters** and the index rides outside it, so a mimic is indexed even
   when the declaration is not.

   `WTree` nests into the *same* container at **two different indices**,
   `Vec WTree N.z` and `Vec WTree (N.s N.z)`. One mimic serves both, and a
   treatment that keyed a mimic on the whole application rather than on the
   container at its parameters would produce a block with a member Lean does
   not have — the same discrimination `nested_shapes`' `listOfN` decoy makes
   for the unindexed case. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

--#export Eq N Vec VTree WTree

inductive VTree : Type where
  | leaf : VTree
  | node : Vec VTree (N.s N.z) → VTree

inductive WTree : Type where
  | leaf : WTree
  | one : Vec WTree N.z → WTree
  | two : Vec WTree (N.s N.z) → WTree
