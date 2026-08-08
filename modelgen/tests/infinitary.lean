/- **A constructor field recursive under a binder.** Lean supports infinitary
   constructors, and there are three places one can sit relative to the
   nesting. All three are here, because they are handled by different code:

   * `FTree.branch : (N → FTree) → FTree` — the **root's** own field, under a
     binder. The block types it `N → B₀`, and `B₀.rec`'s minor for it carries
     `(n : N) → motive₀ (f n)`.
   * `Fn.mk : (N → α) → Fn α`, reached as `FTree.node : Fn FTree → FTree` — the
     **mimic's** field. `B₁.mk : (N → B₀) → B₁`, and `B₁.rec`'s rule gives that
     an induction hypothesis too.
   * `HTree.node : (N → List HTree) → HTree` — a field at a **mimic** under a
     binder. Lean accepts it; `HTree.rec_1`'s minor for `node` binds
     `a : N → List HTree` with `(a_1 : N) → motive_2 (a a_1)`. -/
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

--#export Eq N List Fn FTree HTree

inductive Fn (α : Type) : Type where
  | mk : (N → α) → Fn α
  | pure : α → Fn α

inductive FTree : Type where
  | leaf : FTree
  | branch : (N → FTree) → FTree
  | node : Fn FTree → FTree

inductive HTree : Type where
  | leaf : HTree
  | node : (N → List HTree) → HTree
