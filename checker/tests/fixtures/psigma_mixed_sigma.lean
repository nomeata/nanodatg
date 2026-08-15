/-
# `PSigma'` and `PSigma` at **mixed** σ — `(0,1)` and `(1,0)`

**This fixture exists because a basis member had an instantiation nobody had
ever run.**

`MODEL-BASIS.md` §3.1 makes `PSigma'` one of the five inductives the checker
must keep its own clause for after the model pivot. §3.3 measures it at
`σ = (0,0)` (green, class-(P) truncation carrier) and at `σ = (1,1)` (declines,
`ind-spec(PSigma': class (P) above Prop)`). §8.6 records the **mixed**
instantiations as not established, and they are not reachable by accident:
`instantiations::DEFAULT_LEVELS` seeds a defaulted declaration at
`vec![l; nparams]`, which is uniform by construction, so no default can ever be
mixed. A mixed σ appears only if some declaration *demands* one, and no file in
`vendor/arena-tests` or `checker/tests/fixtures` did. **Skip is not pass**: the
mixed carrier was absent, not passing.

It is a production shape rather than a curiosity.
`vendor/lean-inductive-models/src/InductiveModels/Simple.lean:26-27` builds
`False`'s role out of the basis as `PSigma'.{0,u} (fun _ : p => PUnit.{u})` —
a `Prop` first component under a `Sort u` second — and `:56` pads every Type-route
constructor chain with `PSigma'.{0,w} ⊥ (fun _ => PUnit.{w})`. Every model the
external tool emits on the Type route therefore contains a mixed `PSigma'`.

# The two declarations, and why the second one is the point

`PSigma'` and `PSigma` are **the same instantiated declaration at every mixed
σ**. They differ only in the declared resultant sort — `Sort (max u v)` against
`Sort (max 1 u v)` — and at `(0,1)` and at `(1,0)` both of those evaluate to
`Sort 1`. Same parameters, same constructor, same fields, same ground result.

That difference is invisible to σ and decisive to the checker, because
`zoneb::large_eliminating` reads **the declaration's own level expression and
never σ's** (`zoneb.rs:1149`). `max u v` is not `provably_nonzero`, so `PSigma'`
is class (P) at every σ and `build_trunc` declines every σ whose ground
resultant level is not `0`. `max 1 u v` *is* provably nonzero, so `PSigma` takes
the data route at every σ, mixed included.

**That is not a bug and this fixture does not ask for it to be fixed.** Deciding
the class per instantiation would hand a W-type to a declaration that is a `Prop`
at `u := 0` — `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3, pinned by
`zoneb::tests::a_possibly_prop_declaration_never_acquires_a_w_type`. The licence
to pick a carrier per σ is what "basis member" buys, for five name-keyed
declarations, and nothing else.

So the pair is a **control**: `PSigma` measures what the general machinery does
with one `Prop` field and one data field at rung 1, which is exactly the carrier
a per-σ `PSigma'` clause would have to reach, and it measures it on the identical
instantiated shape rather than on an analogy.

# Both mixed σ, and both orders

`(0,1)` and `(1,0)` are both here because they are not interchangeable: at
`(0,1)` the *first* component is the proposition and the fibre is data, at
`(1,0)` the first is data and the fibre is the proposition. A checker that
sorted, `max`-ed or otherwise normalised σ would collapse them into one, and two
rows that read `σ=[0, 1]` and `σ=[1, 0]` are what refuses that.

# Every σ is demanded, none is defaulted

The four instantiations of each type are demanded by name rather than left to
`DEFAULT_LEVELS`. A defaulted declaration is seeded uniformly, so relying on the
default would make the uniform half of this fixture a hostage to that constant
and would leave the mixed half unreachable. `instantiations::compute_in`'s
default pass fires only for a declaration nothing demands, so with the eight
`def`s below neither type is defaulted at all and the fixture measures the same
eight pairs whatever `DEFAULT_LEVELS` becomes.

The `def`s return the *type former applied*, not an inhabitant: a mixed pair has
no closed inhabitant without a closed proposition to put in it, and an
inhabitant is not what is being measured.
-/
prelude
universe u v

--#export PSigma' PSigma'.mk PSigma'.rec PSigma PSigma.mk PSigma.rec tight00 tight01 tight10 tight11 wide00 wide01 wide10 wide11

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

set_option genSizeOf false

-- `bootstrap.inductiveCheckResultingUniverse` is how `Init.Prelude` declares
-- `PUnit.{u}` and `PProd.{u,v}`; it is off here for the same reason, so that
-- the resultant sort stays `max u v` with no built-in `1`. That is the whole
-- difference between this declaration and the one below it.
set_option bootstrap.inductiveCheckResultingUniverse false in
/-- The basis member: `Sort (max u v)`, no floor. -/
inductive PSigma' {α : Sort u} (β : α → Sort v) : Sort (max u v) where
  | mk (fst : α) (snd : β fst) : PSigma' β

/-- The control: Lean's own `PSigma`, `Sort (max 1 u v)`, declared here rather
    than imported because a `prelude` fixture has no `Init`. Identical to the
    above at every σ this file demands. -/
inductive PSigma {α : Sort u} (β : α → Sort v) : Sort (max 1 u v) where
  | mk (fst : α) (snd : β fst) : PSigma β

def tight00 : (α : Sort 0) → (β : α → Sort 0) → Sort 0 := fun _ β => PSigma'.{0,0} β
def tight01 : (α : Sort 0) → (β : α → Sort 1) → Sort 1 := fun _ β => PSigma'.{0,1} β
def tight10 : (α : Sort 1) → (β : α → Sort 0) → Sort 1 := fun _ β => PSigma'.{1,0} β
def tight11 : (α : Sort 1) → (β : α → Sort 1) → Sort 1 := fun _ β => PSigma'.{1,1} β

def wide00 : (α : Sort 0) → (β : α → Sort 0) → Sort 1 := fun _ β => PSigma.{0,0} β
def wide01 : (α : Sort 0) → (β : α → Sort 1) → Sort 1 := fun _ β => PSigma.{0,1} β
def wide10 : (α : Sort 1) → (β : α → Sort 0) → Sort 1 := fun _ β => PSigma.{1,0} β
def wide11 : (α : Sort 1) → (β : α → Sort 1) → Sort 1 := fun _ β => PSigma.{1,1} β
