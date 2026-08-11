/-
# A class-(S) declaration whose field type depends on an earlier field

**This fixture exists ahead of the code it tests, and it is a placeholder on
purpose. Read the last section before touching it.**

# The trap

`mini::class_s` retains, per plain field, a typing `⊢ ⟦βⱼ⟧ ∈ U₀`. For **every**
class-(S) declaration in the corpus that typing is scope-dependent in a way that
hides where it came from:

* `And a b`'s two field types are the parameters `a` and `b`;
* `ProjDataIndex p`'s field type is the parameter `p`;
* `PUnit` has no fields at all.

So `⊢ ⟦βⱼ⟧ ∈ U₀` is literally the parameter binder's own scope assumption —
`[a ∈ U₀] ⊢ a ∈ U₀` — and a hypothesis-carrying theorem cannot be `inst_all`'d.
An eliminator build that takes `Pⱼ` from **its own nest's parameter scope** and
one that takes it from `ClassS::field_sort` therefore agree on all three, and on
all six of their pairs. **The corpus cannot distinguish the two sources.**

A build written against the parameter scope is wrong for any declaration whose
field type is neither a parameter nor closed — and there is no such declaration
in 91 files. This is the `scope_vars` shape again: a bug structurally invisible
to every witness. The difference is that this time it is known in advance, and
this file is what will catch it.

# The declarations

| declaration | field types | what it is |
| --- | --- | --- |
| `AndLike a b` | the parameters `a`, `b` | the corpus shape — `And`. **Control.** |
| `Closed` | the closed constants `Tru`, `Tru2` | the other corpus shape. **Control.** |
| `Dep2 α β` | `α`, then `β a` | the minimal dependent case |
| `Dep3 α β γ` | `α`, then `β a`, then `γ a b` | **the target** |

`Dep2`'s second field type `β a` is a parameter *applied to an earlier field*:
neither a parameter nor closed, which is exactly what `field_sort` exists for.

**Three fields, not two, and `Void3`'s reasoning applies verbatim.**
`LePropFields::steps` (`d3388b4`) is a prefix fold, and at two fields the prefix
*is* everything: a rule that threads the parameters plus a **fixed one-field
prefix** is right for `Dep2`'s `β a` and wrong for `Dep3`'s `γ a b`. Only the
third field separates "fold the whole prefix" from "take the first of it".

The two controls are in the same file so that a failure is diagnosable on sight.
If `Dep2`/`Dep3` fail while `AndLike`/`Closed` pass, the split is precisely
parameter-scope versus `field_sort` and nothing else.

# What this pins today, and why it is not a regression when it breaks

`062_andRec`'s eliminator is being written now; today every one of these
declarations stops at `recursor(_: class (S) eliminator)`. The expectations in
`designed.rs` are that decline, exactly as `squash_at_nonzero_sigma.lean`'s are.

When the class-(S) eliminator lands there are two outcomes and **both are
useful**:

* all four derive — the general case was got right, and the test is updated to
  say so;
* `AndLike` and `Closed` derive while `Dep2` and `Dep3` do not — **that is the
  signal this fixture was built to produce.** It is not a regression and the
  test must not be weakened to make the suite green. It means `Pⱼ` is coming
  from the parameter scope, and the corpus would have said everything was fine.

# Open question this file answers first

Whether Lean puts these in class (S) at all. One constructor whose fields are
all propositions is large-eliminating by Carneiro §2.6.2 reason 2, and `Prop` is
not provably nonzero, so class (S) is expected — but the classification is
adjudicated by the exported recursor in `designed.rs`, not by expectation. **If
a dependent-field declaration came back small, that would be the finding**, and
it would bear on whether class-(S) field types can be dependent at all.
-/
prelude
universe u

--#export AndLike AndLike.rec Tru Tru2 Closed Closed.rec Dep2 Dep2.rec Dep3 Dep3.rec
--#export andLikeTy andLikeMk andLikeRec closedTy closedMk closedRec
--#export dep2Ty dep2Mk dep2Rec dep3Ty dep3Mk dep3Rec

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- **Control.** Both field types are parameters — `And`, the corpus shape. -/
inductive AndLike (a : Prop) (b : Prop) : Prop where
  | mk : a → b → AndLike a b

/-- An inhabited closed `Prop`. Inhabited on purpose: a provably empty `Prop`
    passes clauses vacuously, which is how the `Quot` equivalence-class clause
    looked right. -/
inductive Tru : Prop where
  | triv : Tru

/-- A second, *different* inhabited closed `Prop`. Different because two
    fields of the same type make every permutation of them invisible. -/
inductive Tru2 : Prop where
  | triv : Tru2

/-- **Control.** Both field types are closed — the other corpus shape. Two
    fields, of two distinct types, so that it is comparable with `AndLike`
    and so that their order is observable. -/
inductive Closed : Prop where
  | mk : Tru → Tru2 → Closed

/-- The minimal dependent case: field 1's type is a parameter applied to
    field 0. -/
inductive Dep2 (α : Prop) (β : α → Prop) : Prop where
  | mk : (a : α) → β a → Dep2 α β

/-- **The target.** Three fields in a chain, so that a fold over the whole
    prefix is distinguishable from one over a fixed prefix of it. -/
inductive Dep3 (α : Prop) (β : α → Prop) (γ : (a : α) → β a → Prop) : Prop where
  | mk : (a : α) → (b : β a) → γ a b → Dep3 α β γ

-- The use sites. `mini::ledger::run` opens no pair for an `Inductive`, so
-- without these the file is accepted with an empty ledger and measures nothing.
-- Each declaration gets three, so that a failure in the carrier, the
-- constructor and the eliminator are distinguishable from each other.
--
-- The recursor aliases are written `@T.rec` with **no type ascription**, so the
-- same source is valid whether Lean makes the declaration large- or
-- small-eliminating; the export says which. They are `noncomputable` because
-- Lean's code generator refuses a computable `def` that applies a recursor.

noncomputable def andLikeTy (a : Prop) (b : Prop) : Prop := AndLike a b
noncomputable def andLikeMk (a : Prop) (b : Prop) (x : a) (y : b) : AndLike a b :=
  AndLike.mk x y
noncomputable def andLikeRec := @AndLike.rec

noncomputable def closedTy : Prop := Closed
noncomputable def closedMk (x : Tru) (y : Tru2) : Closed := Closed.mk x y
noncomputable def closedRec := @Closed.rec

noncomputable def dep2Ty (α : Prop) (β : α → Prop) : Prop := Dep2 α β
noncomputable def dep2Mk (α : Prop) (β : α → Prop) (a : α) (b : β a) : Dep2 α β :=
  Dep2.mk a b
noncomputable def dep2Rec := @Dep2.rec

noncomputable def dep3Ty (α : Prop) (β : α → Prop) (γ : (a : α) → β a → Prop) : Prop :=
  Dep3 α β γ
noncomputable def dep3Mk (α : Prop) (β : α → Prop) (γ : (a : α) → β a → Prop)
    (a : α) (b : β a) (c : γ a b) : Dep3 α β γ :=
  Dep3.mk a b c
noncomputable def dep3Rec := @Dep3.rec
