/- **The third construction's refusals** (`--prim-models`), one fixture per
   decline path of `Modelgen/Simple.lean`, each asserting the refusal and
   its printed reason:

   * `Lst` — **recursive, `Type`-valued**: the carrier needs the W/path
     construction (plan B), which is not implemented.
   * `Inf` — **recursive proposition**: the Church induction derivation is
     not implemented.
   * `Idx` — an **indexed family** (`P` beside it is its index's type, and
     models — the guard is not refusing everything).
   * `PE` — an **empty carrier at a variable sort** (`PEmpty`'s shape):
     not constructible over the basis — every type it builds at a
     bare-parameter sort is the inhabited `False`-Π singleton, and a model
     of `PE.rec` would prove `False`.
   * `PM` — a variable-sort carrier with **two constructors**: the
     singleton is the fragment's only type at such a sort.
   * `PF` — a variable-sort carrier whose constructor has a **field**:
     same boundary, from the field side.
   * `BoxF` — a field whose level keeps an `imax` even boxed: the imax
     sits on a *domain* of the field's own telescope, where wrapping the
     codomain does not reach.

   The basis-primitive exemption and the name guard have their fixtures in
   the corpus run (`Eq`, `Nat`, `False` decline as basis on `init-prelude`)
   and in `mutual_keying`'s pattern respectively. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Lst (α : Type u) : Type u where
  | nil : Lst α
  | cons : α → Lst α → Lst α

inductive Inf : Prop where
  | mk : Inf → Inf

inductive P : Type where
  | one : P
  | two : P

inductive Idx : P → Prop where
  | mk : Idx P.one

inductive PE : Sort u where

inductive PM : Sort u where
  | a : PM
  | b : PM

inductive PF : Sort u where
  | mk : ((C : Prop) → C → C) → PF

inductive BoxF (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : ((α → β) → β) → BoxF α β
