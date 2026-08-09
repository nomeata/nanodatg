/- **The third construction's positive shapes** (`--prim-models`,
   `Modelgen/Simple.lean`), one per route variant:

   * `Tri` — a **three**-element enumeration, because two atoms cannot
     distinguish an ordering: three nullary constructors pin tag order and
     the `D 1` pads (`Σ'(_ : ⊤), ⊤`) all three chains are.
   * `Boxed` — a structure with a **dependent `Prop` field**: the chain
     `Σ'(val : α), Eq val val` reaches `Sort (u+1)` on its own, no pad.
   * `Opt` — a parameter and a **nullary constructor at `Type u`**, whose
     chain is the pad alone, at the successor form `D (u+1) = (α : Sort u) →
     D 1`.
   * `Big` — a **deliberately-raised carrier** (`Type 1` over a `Type 0`
     field), the one shape whose pad is `D w` at `w` above both `1` and the
     fields.
   * `Dec` — a `Type`-valued sum whose fields are **propositions**, so both
     chains need the `D 1` pad tier (`max 1 0 ≠ 0`).
   * `Sub` — a `Sort (max 1 u)` carrier with a `Sort u` field and a `Prop`
     field: the `PSigma` chain lands on the declared level exactly.
   * `Emp` — **no constructors**: the fibre is empty at every tag and the
     recursor is `False.rec` under two destructions.
   * `Tor` — a `Prop` with three constructors: small elimination, the Church
     fold at a `Prop` motive.
   * `Conj` — a `Prop` structure with **dependent** propositional fields:
     large elimination by sequential extraction, the second field's type
     instantiated at the first's extraction and closed by definitional
     proof irrelevance.
   * `PU` — a **variable-sort singleton** (`PUnit`'s shape): the carrier is
     the `False`-Π singleton at exactly `Sort u`, the recursor a transport
     along its `funext`-derived uniqueness — this is the model that splices
     the quotient, `Quot.sound` and `PU._model.funext`.
   * `UL` — `PULift`'s shape: a carrier raised by a level (`r`) no field
     reaches, whose pad level is not `dsingOk` — the `False`-Π pad,
     discharged by transport in the destructor.
   * `TrL` — `Trans`'s shape: a Π-typed field at an **imax** level, stored
     **boxed** (codomain wrapped `Σ'(_ : S), D 1`) so the level collapses
     to the carrier's never-zero `max`; the recursor unboxes by projection
     and needs no transport at all.

   The file declares `Eq` and nothing else of the basis, so one run splices
   `Nat`, `PSigma` and `False` and the report names them — and, at `PU`,
   the quotient and `Quot.sound` behind the spliced `funext`. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe r s u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Tri : Type where
  | a : Tri
  | b : Tri
  | c : Tri

inductive Boxed (α : Type u) : Type u where
  | mk : (val : α) → Eq val val → Boxed α

inductive Opt (α : Type u) : Type u where
  | none : Opt α
  | some : α → Opt α

inductive Big : Type 1 where
  | mk : (Prop → Prop) → Big

inductive Dec (p : Prop) : Type where
  | isF : ((h : p) → Eq p p) → Dec p
  | isT : p → Dec p

inductive Sub (α : Sort u) (p : α → Prop) : Sort (max 1 u) where
  | mk : (val : α) → p val → Sub α p

inductive Emp : Type where

inductive Tor (a b c : Prop) : Prop where
  | l : a → Tor a b c
  | m : b → Tor a b c
  | r : c → Tor a b c

inductive Conj (a : Prop) (b : a → Prop) : Prop where
  | mk : (ha : a) → b ha → Conj a b

inductive PU : Sort u where
  | mk : PU

inductive UL (α : Sort s) : Sort (max s r 1) where
  | up : α → UL α

inductive TrL (α : Sort u) (r : α → α → Sort v) : Sort (max 1 u v) where
  | mk : ((a b : α) → r a b) → TrL α r
