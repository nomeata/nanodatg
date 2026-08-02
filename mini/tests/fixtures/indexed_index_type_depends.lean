/-
# An indexed family whose index types mention earlier binders

**What breaks if `depthTy` stops deriving, or if `Depth` starts reporting an
`ind-spec(... index ...)` reason.** `zoneb::spec_of` abstracts index `k`'s
interpreted type over `scope_vars(np + k)` — the parameters, then the indices
*before* `k` — and hands that abstraction to `derived::define_abbrev`, which
refuses a body mentioning a variable it was not given. An off-by-one there is a
*silent* wrong answer on every declaration whose index types are closed, because
`define_abbrev` accepts any parameter list for a closed body. `RBTree`'s two
index types are `Color` and `N`: both closed. `SortElimProp`/`SortElimProp2`'s
are no better. The whole corpus certifies nothing about this abstraction, and
the one declaration that caught the last off-by-one — `Acc`, whose index type is
the parameter `α` — caught it by luck.

`Depth` is the minimum shape at which a wrong abstraction differs from a right
one, plus one:

* **three** parameters, so that "drop the outermost" and "drop the innermost"
  are distinguishable from each other and from "drop two";
* **three** indices, so that "abstract over the earlier indices" is
  distinguishable from "abstract over *an* earlier index" and from "abstract
  over none". Two indices cannot tell `scope_vars(np + k)` from
  `scope_vars(np + 1)`;
* each index type mentions a **different** set of earlier binders:
  `w : Wrap α` mentions parameter 0; `j : β w` mentions parameter 1 *and* index
  0; `k : γ w j` mentions parameter 2 *and both* earlier indices. No single
  wrong abstraction is right for all three, and the third is the only place a
  rule that stops at one earlier index would show.

# Why the result index is `Wrap.wrap a` and not the field `a`

**Lean promotes a fixed index to a parameter.** `fixedIndicesToParams` turns an
index that is the same variable in every constructor result and every recursive
occurrence into a parameter, and the promotion is *invisible in the source*: it
shows up only as `numIndices` in the export. The first draft of this fixture
indexed `mk`'s result at its own field variables and Lean exported
`numParams=5, numIndices=0` — an ordinary non-indexed declaration, testing none
of the above. Making index 0's result term **computed** blocks the promotion,
and because parameters must be a prefix it blocks it for indices 1 and 2 too.
Lean confirms it: this file exports `numParams=3, numIndices=3`.

That is also the strongest argument for generating these fixtures from real
`.lean` sources rather than hand-writing `.ndjson`. A hand-written export
claiming `numIndices=3` for the first draft's declaration would be a shape Lean
never produces, and the test would have passed against it while measuring
nothing.

# What derives, and what does not

`zoneb::build_indexed` builds the type former and, as its header says, **not the
constructors**. So `depthTy` derives and `depthMk` reports
`no-interp(Depth.mk)`. The claim this fixture makes is about the index-type
abstraction, and `⟦Depth⟧` existing at all is that claim: the walk had to
abstract all three index types correctly to produce a `well_formed`
`IndexedDeclSpec` and then carve the carrier out of the skeleton.
-/
prelude

--#export Wrap Wrap.wrap Depth Depth.mk depthTy depthMk

-- `Init.Prelude`'s first three declarations. The code generator will not accept
-- an `inductive` without them; they are `unsafe`, so `lean4export` does not
-- emit them and the checker never sees them.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- A constant to compute a result index with, and to build index types out
    of, so that the index types are genuinely different terms. -/
inductive Wrap (α : Type) : Type where
  | wrap : α → Wrap α

/-- Three parameters, three indices, and each index type mentions a different
    set of earlier binders. The result index at position 0 is computed, which
    is what stops Lean promoting the whole telescope to parameters. -/
inductive Depth (α : Type) (β : Wrap α → Type) (γ : (w : Wrap α) → β w → Type) :
    (w : Wrap α) → (j : β w) → (k : γ w j) → Type where
  | mk : (a : α) → (j : β (Wrap.wrap a)) → (k : γ (Wrap.wrap a) j) →
         Depth α β γ (Wrap.wrap a) j k

-- The use sites. Without these the export declares only inductives, and
-- `mini::ledger::run` opens no pair for an inductive: the file would be
-- accepted with an empty ledger and would measure nothing.

/-- Reaches `⟦Depth⟧` — the type former, which is what the index-type
    abstraction has to be right for. -/
def depthTy (α : Type) (β : Wrap α → Type) (γ : (w : Wrap α) → β w → Type)
    (w : Wrap α) (j : β w) (k : γ w j) : Type :=
  Depth α β γ w j k

/-- Reaches `⟦Depth.mk⟧`, which `build_indexed` does not build. Here so that the
    absence is measured rather than assumed. -/
def depthMk (α : Type) (β : Wrap α → Type) (γ : (w : Wrap α) → β w → Type)
    (a : α) (j : β (Wrap.wrap a)) (k : γ (Wrap.wrap a) j) :
    Depth α β γ (Wrap.wrap a) j k :=
  Depth.mk a j k
