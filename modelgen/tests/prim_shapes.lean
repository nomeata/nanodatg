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
     recursor is Church-`⊥`'s `Sort w` eliminator under two destructions.
   * `Tor` — a `Prop` with three constructors: small elimination, the Church
     fold at a `Prop` motive.
   * `IdxP` — an **indexed** `Prop` with two constructors landing at
     *different* indices: small elimination, so the carrier is the Church
     encoding with `C` quantified over the index telescope. Non-recursive —
     it isolates indices from recursion.
   * `Le3` — **indexed and recursive**, three constructors with pairwise
     distinguishable telescopes (nullary; one recursive field; a recursive
     field *followed* by a non-recursive one) landing at three different
     indices. This is the strong-induction
     fold: three atoms, because a two-constructor family cannot catch a
     minor-order bug, and distinguishable telescopes, because ι is `rfl` by
     proof irrelevance here and so cannot catch one either — what catches a
     permutation is the minor premise failing to typecheck.
   * `Conj` — a `Prop` structure with **dependent** propositional fields:
     large elimination by sequential extraction, the second field's type
     instantiated at the first's extraction and closed by definitional
     proof irrelevance.
   * `PU` — a **variable-sort singleton** (`PUnit`'s shape): the carrier is
     `PULiftP ⊤` at exactly `Sort u`, the recursor a transport along the
     lift's eta.
   * `PE` — a **variable-sort empty carrier** (`PEmpty`'s shape): the
     carrier is `PULiftP ⊥`, and the recursor — zero minor premises — is
     Church-`⊥`'s `Sort w` eliminator after the lift is projected away.
     This is the shape the old basis could not reach at all.
   * `PM` — a variable-sort carrier with **two** constructors: small
     elimination, so the lift of the Church encoding serves both.
   * `PT` — a variable-sort carrier with **three** constructors carrying
     **distinguishable** field telescopes. Three atoms, not two: with three
     nullary constructors a minor-order bug is invisible (the motive is
     `Prop`-valued and proof irrelevance closes it), so the fields are what
     make a permutation a type error.
   * `PF` — a variable-sort carrier whose constructor has a **field**.
   * `PI` — a variable-sort carrier whose field is at the **carrier's own**
     sort (`is_geq(u,u)`, the kernel's admission at its tightest): small
     elimination, and the model collapses the payload, which the contract
     permits because a `Prop`-valued motive cannot discriminate.
   * `UL` — `PULift`'s shape: a carrier raised by a level (`r`) no field
     reaches, whose pad level is not `dsingOk` — the `PULiftP ⊤` pad,
     discharged by transport in the destructor.
   * `TrL` — `Trans`'s shape: a Π-typed field at an **imax** level, stored
     **boxed** (codomain wrapped `Σ'(_ : S), D 1`) so the level collapses
     to the carrier's never-zero `max`; the recursor unboxes by projection
     and needs no transport at all.

   The file declares `Eq` and nothing else of the basis, so one run splices
   `Nat`, `PSigma` and `PULiftP` and the report names them. Nothing here
   splices the quotient, `Quot.sound` or a `funext`: the lift's eta replaced
   the one construction that needed them. -/
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

inductive IdxP : Tri → Prop where
  | at_a : IdxP Tri.a
  | at_b : IdxP Tri.b

inductive Le3 (q : Prop) : Tri → Prop where
  | base : Le3 q Tri.a
  | up : Le3 q Tri.a → Le3 q Tri.b
  | tagged : Le3 q Tri.b → q → Le3 q Tri.c

inductive PU : Sort u where
  | mk : PU

inductive PE : Sort u where

inductive PM : Sort u where
  | a : PM
  | b : PM

inductive PT (p q : Prop) : Sort u where
  | x : p → PT p q
  | y : q → PT p q
  | z : p → q → PT p q

inductive PF : Sort u where
  | mk : ((C : Prop) → C → C) → PF

inductive PI (α : Sort u) : Sort u where
  | mk : α → PI α

inductive UL (α : Sort s) : Sort (max s r 1) where
  | up : α → UL α

inductive TrL (α : Sort u) (r : α → α → Sort v) : Sort (max 1 u v) where
  | mk : ((a b : α) → r a b) → TrL α r
