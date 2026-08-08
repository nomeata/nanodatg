/- The export declares no `Eq`: the round trips are equations and this tool
   does not fabricate an equality Lean never wrote. -/
prelude
inductive N : Type where
  | z : N
  | s : N → N
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

--#export N List Tree

inductive Tree : Type where
  | leaf : Tree
  | node : List Tree → Tree
