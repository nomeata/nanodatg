/- **The nested occurrence is inside a lambda in a container argument**, which
   is §5.1's one gap. `Lean.Json` and `Lean.PrefixTreeNode` are this shape and
   they are the only two of Mathlib's 41 nested declarations `modelgen`
   declines (§6.3).

   `Ctr α P` in `dependent_fields.lean` already nests at a container with a
   **family** parameter — `Ctr KTree (fun _ => N)` — but the nested type is the
   *first* argument there and the lambda is a constant function of an unrelated
   type. Here the lambda is where the recursion is. `OK` is the discriminating
   control: the **same container**, nested in the argument the other one nests
   in, and it gets a model.

   * `OK.mk : RB OK (fun _ => N) → OK` — `dependent_fields.lean`'s shape at
     this file's container. **A model.**
   * `JT.obj : RB N (fun _ => JT) → JT` — `Lean.Json`'s `obj (kvPairs : RBNode
     String (fun _ => Json))` with `String` shrunk to `N`. **Declined.**
   * `PT.node : N → RB N (fun _ => PT) → PT` — `Lean.PrefixTreeNode` without
     its parameters, so the decline is not `JT`'s constructor arrangement.
     **Declined.**

   What the kernel says is that the induction hypothesis for the container's
   own recursive field arrives at the **root** member rather than at the mimic:

       RB.node N (fun x => JT._model.self) a_ih✝² k a✝¹ a_ih✝¹
       argument has type JT._model.0
       but function has type (RB N fun x => JT._model.self) → …
-/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive RB (α : Type) (β : α → Type) : Type where
  | leaf : RB α β
  | node : RB α β → (k : α) → β k → RB α β → RB α β

--#export Eq N RB OK JT PT

inductive OK : Type where
  | mk : RB OK (fun _ => N) → OK

inductive JT : Type where
  | null : JT
  | obj : RB N (fun _ => JT) → JT

inductive PT : Type where
  | node : N → RB N (fun _ => PT) → PT
