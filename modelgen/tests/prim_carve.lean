/- **Arm C**: an indexed family at a never-zero sort, modelled by carving it
   out of its own **index erasure** — thesis §5.2's skeleton-plus-`good`,
   standing on a spliced inductive rather than on a W-type. `MODELGEN.md`
   §8.15 is the arm and `scripts/inductive-basis/CarveOverSkeleton.lean` the
   prototype it was built from.

   Every occupant here declined before the arm landed, all with the one
   reason "an indexed family at a never-zero sort". Each is chosen for a
   discrimination the others do not make.

   * `Vc` — the base case: one index, linear recursion, and the index *moves*
     (`N.s n`) so the child's index and the result's differ.

   * `Two2` — **two constructors at the same index**. `Vc`'s two are separated
     by their index (`N.z` versus `N.s n`), so a model that lost the
     constructor tag entirely could still pass `Vc`'s pins; `Two2.l n` and
     `Two2.r n _` both live at `n`, so the recursor has to tell them apart on
     its own. This is `CarveOverSkeleton.lean`'s `Two` and it is here for the
     same reason.

   * `Bl` — an index **telescope of length two**, packed into one `PSigma`.
     Two indices are not enough on their own: `bin` moves the first and leaves
     the second, `wide` moves the second and leaves the first, so a treatment
     that swapped the two, or applied one where the other belongs, is a type
     error in one of the two constructors rather than invisible in both.

   * `Fn` — an indexed family with **no recursion at all**, so `good` has no
     conjunction and the whole carve is one index equation. The arm's
     zero-recursive-field branch is otherwise unreached.

   * `Vec` — **parameterised**. Everything above is parameter-free, and a
     parameter is threaded through the skeleton's own type, its constructors,
     `good`, the carrier and the recursor; nothing without one would notice a
     parameter dropped in any of those five places.

   * `Tri3` — **three non-recursive fields**, with the recursive field's index
     read off the *first* and the conclusion's off the *third*. Two fields
     cannot distinguish an order that is preserved from one that is reversed,
     and a constructor whose child index and result index come from the same
     field cannot distinguish reading one for the other.

   Two negatives, and they are the arm's two boundaries rather than incidental
   refusals:

   * `Br` — an indexed family whose erasure **branches**. Arm C splices the
     erasure and the erasure has to model; a branching one is W's territory,
     not the tuple tower's, so this declines *before* anything is spliced,
     with `erasure linear: no`.

   * `IBox` and `NoBase` — two indexed families whose erasure is linear and
     **still does not model**, so the skeleton is spliced, the prim pass
     cannot model it, and the whole emission is **withdrawn**: §8.15's rule
     that a family whose skeleton does not model produces no emission, so that
     nothing unmodelled ever reaches a consumer. Without them that rule would
     be a comment. They withdraw for *different* inner reasons, which is what
     pins that the decline carries the skeleton's own reason rather than only
     the fact of failure: `IBox`'s erasure is `prim_declines`' `BoxF`, whose
     field keeps an `imax` even boxed, and `NoBase`'s erasure is linearly
     recursive with **no base constructor**.

   `NoBase` is worth a second sentence, because arm C is how the shape came to
   light. `NoBase._model.skel` is `S | mk : N → S → S` — an *uninhabited*
   linearly recursive inductive, which Lean accepts and the tuple tower does
   not model: its spine's zero fibre is a chain of no fields and the plan
   gives it no pad. That is a gap in the **Type route** and not in arm C, it
   predates this arm, and nothing in the corpus had reached it because every
   linearly recursive occupant there has a base constructor. It is recorded
   rather than fixed. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

inductive Vc : N → Type where
  | nil : Vc N.z
  | cons : (n : N) → Vc n → Vc (N.s n)

inductive Two2 : N → Type where
  | l : (n : N) → Two2 n
  | r : (n : N) → Two2 (N.s n) → Two2 n

inductive Bl : N → N → Type where
  | tip : Bl N.z N.z
  | bin : (a b : N) → Bl a b → Bl (N.s a) b
  | wide : (a b : N) → Bl a b → Bl a (N.s b)

inductive Fn : N → Type where
  | fz : (n : N) → Fn (N.s n)
  | fs : (n : N) → Fn (N.s (N.s n))

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

inductive Tri3 : N → Type where
  | base : Tri3 N.z
  | mk : (a : N) → (b : N) → (c : N) → Tri3 a → Tri3 (N.s c)

inductive Br : N → Type where
  | leaf : Br N.z
  | node : (m n : N) → Br m → Br n → Br (N.s N.z)

inductive IBox (α : Sort u) (β : Sort v) : N → Sort (max 1 u v) where
  | mk : ((α → β) → β) → IBox α β N.z

inductive NoBase : N → Type where
  | mk : (n : N) → NoBase n → NoBase (N.s n)
