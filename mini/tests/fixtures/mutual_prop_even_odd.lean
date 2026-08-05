/-
# A `Prop`-valued mutual family, and why the block size decides the eliminator

`Even`/`Odd` is the classic mutual `Prop`, and it is here for that reason. What
it *measures* is the eliminator trichotomy at a mutual block, where the rule is
not the rule for a single declaration.

For a single `Prop`-valued inductive, large elimination is allowed when the type
has at most one constructor and every field is either a proof or appears in the
result — mini's `elimToSort` walk. **For a block of more than one type, large
elimination is refused outright**, whatever the members look like: an eliminator
that could take a proof of `Even n` to data would, through the shared minors,
take a proof of `Odd n` to data too, and there is no single-constructor argument
covering a family. So every recursor here eliminates only into `Prop`, its
motive level is `0`, and it carries no extra level parameter — where a
`Type`-valued block's recursor carries the fresh `u`.

`mini/src/kernel.rs`'s `elim_to_sort` carried a `TODO (mini-lean's own): mutual
inductives should return false` on its zero-constructor branch for as long as
mini declined mutual blocks at the parser. `kernel::add_block` closes it: the
block-size test comes *before* the constructor-count tests, so an empty `Prop`
inside a block no longer falls through to `true`.

# Three blocks, and the third is the one that isolates the rule

`Even`/`Odd` and `M0`/`M1`/`M2` both have **two** constructors in their first
member, and `elimToSort` refuses large elimination for a single `Prop` with two
constructors as well — so on those two blocks the block-size rule and the
constructor-count rule agree, and deleting the block-size rule changes nothing.
`Sa`/`Sb` is the separating case for **large elimination**: `Sa` has one
constructor whose only field is a proof, which is exactly the shape a *single*
`Prop` may eliminate large from. Its recursor's level parameter list is empty,
and it is empty only because the block has two members.

`Ka`/`Kb` is the separating case for the **K-rule**, which has its own block-size
condition and would otherwise be untested here: `Ka` has one constructor with no
fields at all, so a single `Ka` would be K-like. `Ka.rec` must not be, and
neither must `Kb.rec` — a K-rule computed for the block's first member and hung
on every member's recursor would fire on a major argument of the wrong type.

# Two of the blocks, because one cannot separate "mutual" from "Prop"

`Even`/`Odd` is a **two**-member block, and two members cannot distinguish a
permutation from a clamp. `M0`/`M1`/`M2` is the same family shape at three
members, so the motive and minor order is pinned here as it is in
`mutual_three_way_cycle.lean`, and having both in one file holds everything
except the member count fixed between them. If the two-member block behaves and
the three-member one does not, the difference is order; if both fail, it is
`Prop`.

Both blocks are indexed by `N`, because a `Prop`-valued mutual family that is
*not* indexed is a family of constants and its recursion says nothing.

# `PUnit` and `PProd` are here to make Lean's own aux generation work

Lean generates `below`/`brecOn` beside a mutual block, and for a `Prop`-valued
one those need `PUnit` and `PProd`. Neither is exported — nothing in the
`--#export` list depends on them — and neither is what the file is about; they
are the `prelude` tax, like the three `unsafe axiom`s every fixture carries.
`bootstrap.inductiveCheckResultingUniverse` is off for `PUnit` for the reason
Lean core turns it off for its own: a `Sort u` inductive with one nullary
constructor is exactly the shape the check rejects.
-/
prelude

--#export Even Odd M0 M1 M2 Sa Sb
--#export evenTy oddTy evenZero evenTwo oddOne m0Ty m1Ty m2Ty m0Zero m1One m2Two
--#export saTy sbTy sbMk0 sbMk1 Ka Kb kaTy kbTy kaMk kbMk

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

structure PProd (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β

/-- The subject of the predicates. -/
inductive N : Type where
  | z : N
  | s : N → N

mutual

/-- The classic, member one. -/
inductive Even : N → Prop where
  | zero : Even N.z
  | succ : (n : N) → Odd n → Even (N.s n)

/-- The classic, member two. -/
inductive Odd : N → Prop where
  | succ : (n : N) → Even n → Odd (N.s n)

end

mutual

/-- The same shape at three members: divisibility by three, member zero. -/
inductive M0 : N → Prop where
  | zero : M0 N.z
  | succ : (n : N) → M2 n → M0 (N.s n)

/-- Member one. -/
inductive M1 : N → Prop where
  | succ : (n : N) → M0 n → M1 (N.s n)

/-- Member two. -/
inductive M2 : N → Prop where
  | succ : (n : N) → M1 n → M2 (N.s n)

end

mutual

/-- **One** constructor in the block's *first* member, and its only field is a
    proof — so `elimToSort`'s per-constructor walk says `true` and the block
    size is the only thing that says otherwise. `Even` and `M0` both have two
    constructors, which is a second reason to refuse large elimination and
    therefore hides the first. -/
inductive Sa : Prop where
  | mk : Sb → Sa

/-- The other member, so that the block is a block. -/
inductive Sb : Prop where
  | mk0 : Sb
  | mk1 : Sa → Sb

end

mutual

/-- One constructor, **no fields** — the shape a single inductive proposition
    gets a K-rule for. Being in a block is the only reason it does not. -/
inductive Ka : Prop where
  | mk : Ka

/-- The other member, so that the block is a block. -/
inductive Kb : Prop where
  | mk : Ka → Kb

end

def evenTy (n : N) : Prop := Even n
def oddTy (n : N) : Prop := Odd n
def evenZero : Even N.z := Even.zero
def oddOne : Odd (N.s N.z) := Odd.succ N.z Even.zero
def evenTwo : Even (N.s (N.s N.z)) := Even.succ (N.s N.z) (Odd.succ N.z Even.zero)
def m0Ty (n : N) : Prop := M0 n
def m1Ty (n : N) : Prop := M1 n
def m2Ty (n : N) : Prop := M2 n
def m0Zero : M0 N.z := M0.zero
def m1One : M1 (N.s N.z) := M1.succ N.z M0.zero
def m2Two : M2 (N.s (N.s N.z)) := M2.succ (N.s N.z) (M1.succ N.z M0.zero)
def saTy : Prop := Sa
def sbTy : Prop := Sb
def sbMk0 : Sb := Sb.mk0
def sbMk1 (a : Sa) : Sb := Sb.mk1 a
def kaTy : Prop := Ka
def kbTy : Prop := Kb
def kaMk : Ka := Ka.mk
def kbMk (a : Ka) : Kb := Kb.mk a
