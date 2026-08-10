/- **The third construction's refusals** (`--prim-models`), one fixture per
   decline path of `Modelgen/Simple.lean`, each asserting the refusal and
   its printed reason:

   * `Lst` — **recursive, `Type`-valued**: the carrier needs the W/path
     construction (plan B), which is not implemented.
   * `Inf` — **recursive proposition**: the Church induction derivation is
     not implemented.
   * `Idx` — an **indexed family** (`P` beside it is its index's type, and
     models — the guard is not refusing everything).
   * `BoxF` — a field whose level keeps an `imax` even boxed: the imax
     sits on a *domain* of the field's own telescope, where wrapping the
     codomain does not reach.

   The three variable-sort shapes this file used to carry — an empty
   carrier, a two-constructor carrier and a carrier whose constructor has a
   field — are **no longer refusals**: `PULiftP` reaches a bare `Sort u`
   with a carrier that can be empty, and they live in `prim_shapes.lean` as
   `PE`, `PM`, `PF`, `PT` and `PI`. `False` is no longer a refusal either;
   it is derived, and models.

   The basis-primitive exemption and the name guard have their fixtures in
   the corpus run (`Eq` and `Nat` decline as basis on `init-prelude`) and in
   `mutual_keying`'s pattern respectively. -/
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

inductive BoxF (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : ((α → β) → β) → BoxF α β
