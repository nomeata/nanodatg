/-
# A recursive argument whose domain is a *parameter*

`PTree.node : (α → PTree α) → PTree α` is ordinary Lean, and until now its
carrier was not placed. The obstacle was never that the statement is false —
it is that the statement is **conditional**, and the pipeline that spends it
demanded an unconditional input.

A Lean declaration is always closed, so a parameterised one's theorem is
`⊢ ∀p⃗. (H → ind(p⃗) ∈ Uₙ)` with `H` the conjunction of the parameters' own
typings, and every use site has `H` ready. `derived/src/cumul/opt.rs`'s `Ctx`
is that discipline, and `decl.rs` already took a `hyp: Option<&Formula>` for
the **tag** side. What did not take one was the **fibre** side: the summand
`Aᵢⱼ = Σ(z::γᵢⱼ)` of a function-typed recursive argument, whose universe
membership at `γ = α` is exactly `α ∈ Uₙ ⊢ …` and nothing weaker.

`A ∈ Uₙ` genuinely cannot be discharged locally: `List α` for an `α` that is
not small has no W-type in `Uₙ` at all. The antecedent is the theorem's
content, so it is threaded rather than dropped.

# Five trees, and the fifth was found by a mutation

Each row differs from its neighbour in exactly one thing, so the row that
fails names the property that fails:

| declaration | `np` | recursive-argument domains | before | after |
|---|---|---|---|---|
| `CTree.node : (B2 → CTree) → CTree`                        | 0 | one, closed              | certifies | certifies |
| `KTree.node : (B2 → KTree α) → KTree α`                    | 1 | one, closed              | certifies | certifies |
| `PTree.node : (α → PTree α) → PTree α`                     | 1 | one, **the parameter**   | declined  | **certifies** |
| `MTree.node : (B2 → MTree α) → (α → MTree α) → MTree α`    | 1 | **two, mixed**           | declined  | **certifies** |
| `XTree.node : XTree α → (α → XTree α) → XTree α`           | 1 | one **empty**, one parameter | declined | **certifies** |

`CTree` and `KTree` are the controls: they say that neither a function-typed
recursive argument nor a parameter is on its own what the placement could not
do. `PTree` is the witness. `MTree` is the mixed constructor: its fibre value
is `Sum_2(Σ(z::⟦B2⟧), Σ(z::α))`, two *different* summands in one sum, only one
of which would be provable without `H`. A three-tree fixture would have
measured `Sum_1` four times.

**Where the two rows are made uniform is worth stating exactly, because the
obvious answer is wrong.** It is not the sum-closure fold: by the time the fold
sees them both rows already carry `H`, because the walk discharges *every*
recursive-argument domain typing through the parameter scopes whether the
domain needs it or not, and `⟦B2⟧ ∈ Uₙ` under a vacuous `H` is one
`implies_intr`. The fold's own lifting is elsewhere and every tree exercises
it: each `leaf` contributes no summand at all, so its fibre value is `Sum_0()`,
whose base `∅ ∈ Uₙ` is a fact about the universe and is lifted into `H` rather
than obtained there.

`XTree` is the fifth row and it was **added by a mutation, not by a design**.
Its first recursive slot has an *empty* `γ` — a plain recursive field — sitting
beside a function-typed one, so the constructor's fibre value is
`Sum_2(1, Σ(z::α))` and the `1` is a summand `zoneb::fibre_facts` synthesises
rather than derives. That summand has to be lifted into `H` like every other
row, and deleting the lift **killed nothing** across the whole `derived` and
`mini` suites: a declaration reaches that branch only when some *other* slot in
the same declaration has a non-empty `γ`, and at `np ≥ 1` no such declaration
existed anywhere. The four rows above all have every `γ` non-empty or every `γ`
empty, and `np = 0` makes the lift vacuous. One export closes it.

`113_reduceCtorParamRefl.mk` and `114_reduceCtorParamRefl2.mk` are the corpus
exports of the same shape — their constructor field reduces to `α → T α`
through an `id` and a `constType`. **They advanced and did not close**, which
is why this fixture exists rather than being replaced by them: their carrier is
placed now, and they stop one construction later, in `zoneb::constructor`,
because the field's Lean codomain is `constType (T α) (T α)` while the
constructor's spine is `⟦T⟧(p⃗)`. The two are definitionally equal — that is
what makes the field recursive at all — but `⟦·⟧` is a function of the term, so
the bridge is a δ/β conversion and not a placement obligation. Their reason
moved from `ind-fibre-value(…)` to `ctor(…: recursive field codomain)`, and
`mini/tests/dump.rs` is where that is pinned.

Here the shape is *stated* rather than obfuscated, so this file measures the
placement and only the placement.

# The three untranslated eliminators

`KTree.rec`, `PTree.rec` and `MTree.rec` are not translated: a parameterised
dependent recursor's minor premise does not transport. `KTree` reported that
**before** this fixture's subject changed anything, at `np = 1` with a closed
`γ`, and `CTree.rec` at `np = 0` translates — so it is an axis of its own and
not a residue of the branching domain. It is asserted in `designed.rs` rather
than left to be rediscovered.

# Why `B2` and not `Bool`

`Bool` is not available under `prelude`, and a two-constructor nullary
inductive is the smallest closed `γ` whose `Σ(z::γ)` is not the one-point
summand an empty domain gets. Instantiating the parameterised trees at `B2` is
what makes the use sites discharge `H`: `⟦B2⟧ ∈ ⟦Sort 1⟧` is exactly the
antecedent the declaration's theorem carries.
-/
prelude

universe u

unsafe axiom lcErased : Type u
unsafe axiom lcAny : Type u
unsafe axiom lcVoid : Type u

--#export ctreeTy ctreeNode ktreeTy ktreeNode ptreeTy ptreeNode mtreeTy mtreeNode
--#export xtreeTy xtreeNode

/-- A closed two-point domain. -/
inductive B2 : Type where
  | ff : B2
  | tt : B2

/-- The first control: a function-typed recursive argument at `np = 0`. -/
inductive CTree : Type where
  | leaf : CTree
  | node : (B2 → CTree) → CTree

/-- The second control: the same, with a parameter the domain does not use. -/
inductive KTree (α : Type) : Type where
  | leaf : KTree α
  | node : (B2 → KTree α) → KTree α

/-- The witness: the recursive argument's domain *is* the parameter. -/
inductive PTree (α : Type) : Type where
  | leaf : PTree α
  | node : (α → PTree α) → PTree α

/-- The mixer: one closed domain and one parameter domain in one constructor,
    so the fibre value sums a conditional summand with an unconditional one. -/
inductive MTree (α : Type) : Type where
  | leaf : MTree α
  | node : (B2 → MTree α) → (α → MTree α) → MTree α

/-- The synthesised summand: a *plain* recursive field beside a function-typed
    one, so one summand is the one-point set the walk supplies itself. -/
inductive XTree (α : Type) : Type where
  | leaf : XTree α
  | node : XTree α → (α → XTree α) → XTree α

def ctreeTy : Type := CTree
def ctreeNode (f : B2 → CTree) : CTree := CTree.node f
def ktreeTy : Type := KTree B2
def ktreeNode (f : B2 → KTree B2) : KTree B2 := KTree.node f
def ptreeTy : Type := PTree B2
def ptreeNode (f : B2 → PTree B2) : PTree B2 := PTree.node f
def mtreeTy : Type := MTree B2
def mtreeNode (g : B2 → MTree B2) (f : B2 → MTree B2) : MTree B2 := MTree.node g f
def xtreeTy : Type := XTree B2
def xtreeNode (t : XTree B2) (f : B2 → XTree B2) : XTree B2 := XTree.node t f
