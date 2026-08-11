/- **The index axis of the one-constructor `Prop`** (`--prim-models`,
   `Modelgen/Simple.lean`), as a grid rather than as a list of the shapes the
   corpus happens to contain.

   # What the axis is

   The kernel grants a `Sort v` motive to a one-constructor `Prop` exactly when
   every constructor field is either a **proof** or a piece of **data that is
   literally one of the conclusion's index arguments** — by identity, not by
   occurrence (`vendor/nanoda_lib-upstream/src/inductive.rs`,
   `large_elim_test_aux`; `MODELGEN.md` §8.17 has the probe that measured it
   against Lean's own kernel). That rule is not a technicality: a model of a
   `Prop` can extract its proof fields by small elimination and has *no way
   whatever* to extract data, so **the index vector is the only place data can
   come back from**, and the kernel's rule is what guarantees it is there.

   So each index position is one of two things, and the whole axis is which:

   * a **pivot** — literally one of the constructor's data fields. The model
     substitutes the recursor's own index argument for it.
   * anything else — an arbitrary term over the parameters, the data fields and
     the *proof* fields. Nothing can be recovered from such a position, so it is
     discharged by a **Henry-Ford equation at the non-pivot subsequence**.

   Read that way the two arms' old limits were **one** limit seen from its two
   ends: arm F took only all-non-pivot index vectors and arm G only all-pivot
   ones, and everything between them fell through the gap —
   `CategoryTheory.Functor.IsHomLift` and `Acc.below`, the corpus's last two
   non-exempt declines, one on each side. Arm F now covers its whole row.

   |            | ground | pivot | expr over data | expr over proof |
   |------------|--------|-------|----------------|-----------------|
   | non-rec, F | `Fg`   | `Fall3`, `Fdup`, `Fdep` | `Fdup`, `Fdep` | `Fxh` |
   | rec, G     | `BadC` (`prim_graph`) | `Rv` | — | `Rxh`, `Rvx` |

   Arm F's row models. Arm G's row declines but for `Rv`, at the arm's own
   named reason, and `Rxh` and `Rvx` are `Inf.below` and `Acc.below` written
   deliberately rather than met by accident.

   # Why every cell needs a leading non-pivot

   Lean's front end **promotes** a leading index that is a bare constructor
   field into a *parameter*, at which point the shape is not indexed at all:
   `inductive A : N → Prop | mk (x : N) : A x` arrives as `np=1, ni=0`. A pivot
   is therefore only reachable behind a position that cannot be promoted — a
   constant, or a term. Every cell below is written that way, and that is a
   fact about the corpus too: `MixI`'s header in `prim_declines.lean` said it
   first.

   # The occupants and the mutations, red at one apiece

   * `Fg` — the **control**: one ground index, no pivot at all. Arm F exactly
     as it was before the split, and green under every mutation below, which
     is what says the new cells and not the old path are what they measure.
   * `Fdup` — **one** data field at **two** index positions. Only *one* of them
     can be the pivot; the other is an ordinary non-pivot and the equation
     carries it. (Which one is free: taking the first rather than the last is
     green, and that is measured, not assumed.)
   * `Fdep` — a non-pivot index whose **type mentions a pivot** (`Fam n` at the
     pivot `n`), with a second non-pivot before it. The packed subsequence is
     built at an opened telescope and instantiated at the caller's indices, and
     this is the cell where that instantiation is not the identity and where
     the non-pivot positions are not a prefix.
   * `Fall3` — **every** index a pivot, at three, mapped on by a 3-cycle. There
     is then nothing left to equate: the carrier is a bare Church conjunction,
     no `PSigma` is packed and no `Eq.rec` is built. Three and not two, because
     with two pivots a wrong field↦index map is a transposition.
   * `Fxh` — a non-pivot index that is an expression over a **proof** field
     (`k h`), and no data fields at all: `Inf.below`'s shape without the
     recursion. **Green under every mutation in the sweep, and that is the
     finding rather than a gap** — see below.
   * `Fmid` — the **refusal**.
   * `Rv` — arm G's control, `Acc`'s own shape; `Rxh` and `Rvx` its two
     refusals.

   | mutation | red |
   |---|---|
   | **A** the data fields' pivot assignments rotated among themselves | `Fall3` |
   | **B** *every* occurrence of a data field marked a pivot, not just the chosen one | `Fdup` |
   | **F** the packed type not instantiated at the caller's index vector | `Fdep` |
   | **E** the unpacked components written back at the identity positions | `Fdep` |
   | **N** the non-pivot positions taken as a prefix rather than as the complement | `Fdep` |
   | **H** the rebuilt carrier handed every field rather than the bound ones | `Fdep`, `Fdup` |
   | **C** the whole index vector packed rather than the non-pivot subsequence | every cell with a pivot; `Fg` and `Fxh` green |
   | **D** the non-pivot subsequence reversed | nothing here; `prim_shapes`'s `Hq` and the W core's `HEq`, whose packs are dependent |

   **C and D cascade.** A decline moves a splice, so both take out the whole W
   core fragment in `prim_declines`, `prim_carve` and `prim_w`; the columns
   above are read off `prim_idx`, `prim_shapes` and `prim_graph`, where nothing
   is spliced downstream. That caveat is `MODELGEN.md` §8.7's and it bit again.

   # Four cells were built and dropped, and one finding is why

   `Fxd` (a non-pivot expression over a data field beside its pivot,
   `IsHomLift`'s core at one of each), `Fall` (two pivots rather than three)
   and `Fperm` (`IsHomLift`'s **own** six-index pattern — expr, expr, pivot,
   pivot, expr, pivot, three data fields on a 3-cycle) are each red only under
   mutations that `Fdup`, `Fdep` or `Fall3` are also red under. No mutation in
   the sweep separates them, so by this file's rule they measured nothing the
   survivors do not, and they are gone. `IsHomLift` itself is not lost with
   them: it is a **corpus** row, and it moves from decline to model there.

   `Fp` — an index that is **literally a proof field** — was dropped for a
   sharper reason, and it is worth keeping the sentence. The mutation built for
   it was the pivot test written as "is a *variable*" rather than "is *data*",
   which marks such a position a pivot and drops it from the equation. It is
   **green**, at every occupant, and so is every other mutation at `Fxh`. The
   reason is one fact: a pivot and an extraction at a proof position are two
   proofs of one proposition, so the kernel cannot tell them apart, and no
   threading bug on the proof half of this axis can produce a term that fails
   to typecheck. **The proof column of the grid is free.** `Fxh` stays as the
   witness that it is inhabited and works; `Fp` would have been a second
   witness of the same nothing.

   # The refusal, and it is a real one

   `Fmid : (α : Type) → α → α → Prop` with `mk (x : N) : Fmid N x N.z` is a
   pivot whose *own type* is the ground index before it. The model reads a data
   field off the recursor's index argument, and there that argument's type is
   index 0 — an arbitrary `Type`, which only the equation says is `N` — so the
   field cannot be used without a transport this arm does not build. It is the
   one place the two halves of the axis fail to compose, and **neither corpus
   target is on the wrong side of it**: `IsHomLift`'s `φ : a ⟶ b` names only
   pivots and `Acc.below`'s `a : α` only a parameter.

   # Arm G's two, and what closes them

   `Rxh` and `Rvx` decline at the same generalisation arm F now has, on the
   other arm: `GraphInv ι⃗ t val` concludes `val = step f⃗ g⃗`, whose right-hand
   side lands at the constructor's index expressions, and with a non-pivot
   among them the two sides sit at different indices, so the equation needs a
   transport along the very packed equation arm F carries. `MODELGEN.md` §8.17
   writes that construction out. It is not built, and these two — with
   `Inf.below`, `Rv.below` and the rest Lean mints beside a recursive `Prop` —
   are what go green when it is.

   `Inf` and `N` beside them are the controls that say the arms are not
   swallowing the file: `Inf` is arm G's degenerate positive and `N` an
   ordinary `Type`-route model. -/
prelude

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

inductive Fam : N → Type where
  | c (n : N) : Fam n

inductive Inf : Prop where
  | mk : Inf → Inf

-- ── arm F: the non-recursive row ──

inductive Fg : N → Prop where
  | mk : Fg N.z

inductive Fdup (o : N → N) : N → N → N → Prop where
  | mk (a : N) : Fdup o (o a) a a

inductive Fdep (o : N → N) : N → (n : N) → Fam n → Prop where
  | mk (k : N) : Fdep o (o k) k (Fam.c k)

inductive Fall3 : N → N → N → Prop where
  | mk (a b c : N) : Fall3 c a b

inductive Fxh (q : Prop) (k : q → N) : N → Prop where
  | mk (h : q) : Fxh q k (k h)

inductive Fmid : (α : Type) → α → α → Prop where
  | mk (x : N) : Fmid N x N.z

-- ── arm G: the recursive row ──

inductive Rv (r : N → N → Prop) : N → Prop where
  | mk (x : N) (h : (y : N) → r y x → Rv r y) : Rv r x

inductive Rxh (mo : Inf → Prop) : Inf → Prop where
  | mk (a : Inf) (b : Rxh mo a) (m : mo a) : Rxh mo (Inf.mk a)

inductive Rvx (r : N → N → Prop) (mo : (a : N) → Rv r a → Prop) :
    (a : N) → Rv r a → Prop where
  | intro (x : N) (h : (y : N) → r y x → Rv r y)
          (b : (y : N) → (a : r y x) → Rvx r mo y (h y a))
          (m : (y : N) → (a : r y x) → mo y (h y a)) : Rvx r mo x (Rv.mk x h)
