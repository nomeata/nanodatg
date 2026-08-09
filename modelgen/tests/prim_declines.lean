/- **The third construction's refusals** (`--prim-models`), one fixture per
   decline path of `Modelgen/Simple.lean`, each asserting the refusal and
   its printed reason:

   * `Lst` — **recursive, `Type`-valued**: the carrier needs the W/path
     construction (plan B), which is not implemented.
   * `Inf` — **recursive proposition**: the Church induction derivation is
     not implemented.
   * `Idx` — an **indexed family** (`P` beside it is its index's type, and
     models — the guard is not refusing everything).
   * `PU` — a **sort-variable carrier** `Sort u`, which reaches `Prop` at
     some instantiations and `Type` at others; `monomorph` resolves it.
   * `UL` — `PULift`'s shape: a carrier raised by a level (`r`) that no
     field reaches and that has no buildable pad (`max` over a bare
     parameter is neither a successor nor a `max` of buildable sides).

   The basis-primitive exemption and the name guard have their fixtures in
   the corpus run (`Eq`, `Nat`, `False` decline as basis on `init-prelude`)
   and in `mutual_keying`'s pattern respectively. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe r s u

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

inductive PU : Sort u where
  | mk : PU

inductive UL (α : Sort s) : Sort (max s r 1) where
  | up : α → UL α
