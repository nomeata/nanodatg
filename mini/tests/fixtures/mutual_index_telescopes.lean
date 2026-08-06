/-
# Index telescopes that differ from member to member

`mutual_aux` used to require every member of a block to carry the *same* index
telescope, because `Aux` had one. It does not any more: the telescopes live in
the **tag**, `Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗`, one constructor per member carrying that
member's own indices as fields, and `Aux (p⃗) : Tag p⃗ → Sort u` has no index
telescope at all. A block whose members are unindexed is then the case where
every tag constructor is nullary — the encoding this was, reached as a
degeneracy rather than as a branch.

`mutual_index_sorts.lean`'s `HA`/`HB` block is the **arity** axis at two
members: one index against none. This file is the two axes that leaves open.

| axis | held how |
| --- | --- |
| how many members share | **`MA`/`MB`/`MC`: two share, one differs** |
| where the odd member is | **in the middle**, so clamping to the first *or* the last member is wrong |
| the index **type**, at equal arity | **`DA : N → _` against `DB : Bit → _`** |
| which member fixes `Tag`'s universe | **`EA`/`EB`: the first member has no indices at all** |

# Why the odd member is in the middle

Two members separate "reads the telescope off the wrong member" from nothing at
all, and that is what `HA`/`HB` does. Three do not automatically do better: with
the differing member at an end, a builder that clamps to the first member and a
builder that clamps to the last are wrong on *different* members, but each is
still wrong on exactly one and either would be caught. Putting the odd one in
the middle is what makes both clamps wrong on **`MB` and nothing else**, so the
fixture cannot pass by a builder happening to pick the end the odd member is
not at. `MA` and `MC` share `N`; `MB` has none.

# Every constructor crosses a telescope boundary

The point is not that the members have different telescopes; it is that a
*recursive occurrence* is at another member's telescope. Five of the six
constructors here hold a field of a member whose index arity differs from the
one being built:

| constructor | builds at | holds a | so the ι rule's ih is at |
| --- | --- | --- | --- |
| `MA.mk` | arity 1 | `MB` | arity 0 |
| `MA.step` | arity 1 | `MC n` | arity 1 |
| `MB.wrap` | arity 0 | `MA n` | arity 1 |
| `MC.mk` | arity 1 | `MA n` | arity 1 |
| `MC.flat` | arity 1 | `MB` | arity 0 |
| `DB.mk` | `Bit` | `DA n` | `N` |

A builder that took a recursive field's tag telescope from the constructor's
*owner* rather than from the field's own type is wrong at `MA.mk`, `MB.wrap`,
`MC.flat` and `DB.mk`.

# The rules are fired, not inspected

`maSize`, `mbSize` and `mcSize` are three `def`s over the **same** three motives
and the same six minors — which is the only way the right-hand sides below are
sayable, because the induction hypothesis a mutual ι rule produces is literally
`MB.rec motives minors …` with the caller's own prefix. The motive telescope is
itself the thing under test: `MA`'s motive is `∀ n, MA n → Sort v` and `MB`'s is
`MB → Sort v`, so a packed motive built at one shared telescope does not
typecheck here at all.

The four `Eq`-theorems then force mini's whnf to fire a rule whose ih is at a
*different* member's telescope from the rule's own, in both directions (arity 1
producing an ih at arity 0, and arity 0 producing one at arity 1) and across the
index-type boundary (`Bit` producing an ih at `N`).

# The third block, and the only thing `Tag`'s universe is read from

`Tag` carries index *values*, so it must be declared above every index type's
own sort — `W = max(1, s₁ … s_k)` over **every member's** indices, which
`kernel::sort_under` answers because an index of type `N` is at `Sort 1` only
because `N`'s declaration says so.

With one shared telescope, "every member's" and "the first member's" were the
same set. They are not any more, and nothing else separates them: every index
in this file's first two blocks and in every other fixture is at `Sort 1`, so a
`W` computed from member 0 alone comes out right everywhere.

`EA`/`EB` is where it does not. `EA : Prop` has **no indices**, so member 0
contributes only the floor `1`; `EB : Type 1 → Prop` has an index at `Type 1`,
whose sort is `Sort 3`. The tag has to be `Sort 3`, and only the *second*
member says so. A `W` read off member 0 gives `Sort 1`, `Tag.t1`'s field
`γ : Type 1` then fails the kernel's `sⱼ ≤ W`, and the block declines instead
of encoding.

This is also the pairing the two new things make possible at once — unequal
telescopes *and* a large index sort — which could not be written down before
because the members had to agree.

`PUnit` and `PProd` are the `prelude` tax for a `Prop`-valued mutual block:
Lean's own `below`/`brecOn` generation needs them. Neither is exported.

`Eq` is declared here because the file is `prelude`; it is also what makes the
encoder state its own recursor rules as theorems, so those are checked too.
-/
prelude

--#export MA MB MC DA DB EA EB
--#export maTy mbTy mcTy daTy dbTy eaTy ebTy
--#export maMk maStep mbBase mbWrap mcMk mcFlat daMk daStep dbBase dbMk
--#export maSize mbSize mcSize daSize dbSize
--#export maFromMb mbFromMa mcFromMb dbFromDa
--#export eaMk ebBase ebAny

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

structure PProd (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β

/-- The first block's index type, and what the sizes return. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The second block's *other* index type, at the same arity and the same
    sort as `N`, so that only the type differs. -/
inductive Bit : Type where
  | b0 : Bit
  | b1 : Bit

mutual

/-- One index. Holds an unindexed member and an indexed one. -/
inductive MA : N → Type where
  | mk : MB → MA N.z
  | step : (n : N) → MC n → MA (N.s n)

/-- **None** — the odd member, and it is in the middle. -/
inductive MB : Type where
  | base : MB
  | wrap : (n : N) → MA n → MB

/-- One index again, sharing `MA`'s. -/
inductive MC : N → Type where
  | mk : (n : N) → MA n → MC (N.s n)
  | flat : MB → MC N.z

end

mutual

/-- Indexed by `N`. -/
inductive DA : N → Type where
  | mk : DB Bit.b0 → DA N.z
  | step : (n : N) → DA n → DA (N.s n)

/-- Indexed by `Bit` — same arity, different type. -/
inductive DB : Bit → Type where
  | base : DB Bit.b0
  | mk : (n : N) → DA n → DB Bit.b1

end

mutual

/-- **No indices at all, and it is the first member.** -/
inductive EA : Prop where
  | mk : EB Type → EA

/-- Indexed by `Type 1`, whose own sort is `Sort 3`. `base` gives the index a
    closed value and `any` a variable, so `fixedIndicesToParams` leaves it an
    index. -/
inductive EB : Type 1 → Prop where
  | base : EB Type
  | any : (γ : Type 1) → EB γ

end

def maTy (n : N) : Type := MA n
def mbTy : Type := MB
def mcTy (n : N) : Type := MC n
def daTy (n : N) : Type := DA n
def dbTy (b : Bit) : Type := DB b
def eaTy : Prop := EA
def ebTy (γ : Type 1) : Prop := EB γ

def mbBase : MB := MB.base
def maMk (b : MB) : MA N.z := MA.mk b
def maStep (n : N) (c : MC n) : MA (N.s n) := MA.step n c
def mbWrap (n : N) (a : MA n) : MB := MB.wrap n a
def mcMk (n : N) (a : MA n) : MC (N.s n) := MC.mk n a
def mcFlat (b : MB) : MC N.z := MC.flat b

def dbBase : DB Bit.b0 := DB.base
def daMk (x : DB Bit.b0) : DA N.z := DA.mk x
def daStep (n : N) (a : DA n) : DA (N.s n) := DA.step n a
def dbMk (n : N) (a : DA n) : DB Bit.b1 := DB.mk n a

/-- Three motives at **two different telescopes** and six minors, positional;
    the same list in all three. -/
noncomputable def maSize : (n : N) → MA n → N :=
  @MA.rec (fun _ _ => N) (fun _ => N) (fun _ _ => N)
    (fun _ ih => N.s ih) (fun _ _ ih => N.s ih)
    N.z (fun _ _ ih => N.s ih)
    (fun _ _ ih => N.s ih) (fun _ ih => N.s ih)

noncomputable def mbSize : MB → N :=
  @MB.rec (fun _ _ => N) (fun _ => N) (fun _ _ => N)
    (fun _ ih => N.s ih) (fun _ _ ih => N.s ih)
    N.z (fun _ _ ih => N.s ih)
    (fun _ _ ih => N.s ih) (fun _ ih => N.s ih)

noncomputable def mcSize : (n : N) → MC n → N :=
  @MC.rec (fun _ _ => N) (fun _ => N) (fun _ _ => N)
    (fun _ ih => N.s ih) (fun _ _ ih => N.s ih)
    N.z (fun _ _ ih => N.s ih)
    (fun _ _ ih => N.s ih) (fun _ ih => N.s ih)

noncomputable def daSize : (n : N) → DA n → N :=
  @DA.rec (fun _ _ => N) (fun _ _ => N)
    (fun _ ih => N.s ih) (fun _ _ ih => N.s ih)
    N.z (fun _ _ ih => N.s ih)

noncomputable def dbSize : (b : Bit) → DB b → N :=
  @DB.rec (fun _ _ => N) (fun _ _ => N)
    (fun _ ih => N.s ih) (fun _ _ ih => N.s ih)
    N.z (fun _ _ ih => N.s ih)

/-- Arity 1 producing an ih at arity **0**. -/
theorem maFromMb (b : MB) : Eq (maSize N.z (MA.mk b)) (N.s (mbSize b)) := Eq.refl _

/-- Arity 0 producing an ih at arity **1**. -/
theorem mbFromMa (n : N) (a : MA n) : Eq (mbSize (MB.wrap n a)) (N.s (maSize n a)) :=
  Eq.refl _

/-- The third member, at the index value `N.z` its own `flat` fixes. -/
theorem mcFromMb (b : MB) : Eq (mcSize N.z (MC.flat b)) (N.s (mbSize b)) := Eq.refl _

/-- Across the index *type* boundary: indexed by `Bit`, ih indexed by `N`. -/
theorem dbFromDa (n : N) (a : DA n) : Eq (dbSize Bit.b1 (DB.mk n a)) (N.s (daSize n a)) :=
  Eq.refl _

theorem eaMk (x : EB Type) : EA := EA.mk x
theorem ebBase : EB Type := EB.base
theorem ebAny (γ : Type 1) : EB γ := EB.any γ
