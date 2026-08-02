# Indexed inductive families — design

§5.2's `good` predicate and `spec` judgment, and §5.3's subsingleton
eliminators, translated into this development's terms. Companion to
`RECURSOR-DESIGN.md` (whose rungs 1–4 landed as `derived/src/inductive/`) and
`INDUCTIVES.md`. Thesis references are to the scratchpad `thesis.txt` copy:
§5.2 at `:1752–1820`, §5.3 at `:1822–1889`, the interpretation clauses at
`:2075–2131`.

Provenance markers, per the standing rule: **[read]** = verified in this
repository's code or docs during this design; **[decoded]** = read out of an
`.ndjson` export by actually decoding the declaration (the script parses the
name/level/expr tables and pretty-prints the types — no reasoning from names);
**[believed]** = inferred, with the inference stated. Every `RBTree` claim
below is **[decoded]** from `042_rbTreeDef.ndjson` line 294; this is the
declaration that was mis-stated twice this week, so nothing about it is taken
from any prior document.

---

## 1. Verdict up front

1. **`good` does not need a DTT equality type, and never did.** The chain
   recorded in `README.md` ("indexed families need `acc`, then §5.3, then
   §5.2 — because `good`'s base case wants `Eq`'s elimination") dissolves at
   the set level. `good`'s base case `(x) = (e)` is a **kernel-level equality
   of tuple terms** inside a Separation, and "eliminating" it is
   `kernel::thm::eq_leibniz` — a primitive rule **[read**,
   `kernel/src/thm.rs:759`**]**. The thesis's own interpretation says as much:
   `⟦rec₌ e b h⟧ = ⟦e⟧` (`thesis.txt:2124`) — the eliminator is the identity
   on the minor premise, so at the interpretation level there is nothing to
   build. **§5.2-indexed does not depend on §5.3 or on `acc` at all.** The
   two branches are independent, and `RBTree` needs only §5.2. §2.3 has the
   detail.
2. **The `good` function is the existing general W-recursor at one new
   target.** `goodrec := wrec(A, B, u, 𝒫(Idx), e_G)` — the same shared
   `RecCore`, the same step-by-Replacement shape as
   `inductive/step.rs`, with the step's values Separation subsets of the
   index-tuple space `Idx`. Because every value is a Separation subset,
   `step_typed` is **unconditional** — the `good` recursion is total with no
   `HYP` at all, unlike the value recursor. §3 gives the construction.
3. **The carrier is one more Separation**:
   `ind(p⃗, x⃗) := { s ∈ W(A,B,u) : tup(x⃗) ∈ app(goodrec, s) }`. Constructor
   membership, inversion ("no junk at an index") and non-vacuity in both
   polarities all fall out of the single per-constructor `good`-ι equation.
4. **The branch criterion is Lean's eliminator trichotomy, per declaration,
   read off the export** — never the instantiated sort
   (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3's rule, kept). `RBTree` is
   **class (T)**: its resultant sort is `Sort u+1` **[decoded]**, provably
   nonzero at every instantiation, so it takes §5.2 with a genuine `good` —
   **not** §5.3, which it never touches. §2 has the criterion and the full
   census of the 91 files: exactly five indexed families exist in the
   tutorial corpus, and each is classified there.
5. **`acc^φ_r` is not a new construction.** Because `derived/src/acc/`'s
   `preds_in` carries its own `y ∈ A` guard and `R ⊆ A × A` was deliberately
   never assumed **[read**, `acc/condition.rs` header**]**, the thesis's
   `acc^φ_r x := ∃h : φ x. acc_{r′}(x,h)` collapses to
   `acc(A_φ, R)` at the Separation `A_φ := {q ∈ Idx : φ(q)}` with **the same
   unrestricted `R`**. The two corrections that landed with `acc` are exactly
   what make this one-liner sound; §6.1 spells it out.
6. **`DeclSpec` is extended by wrapping, not by churning.** A new
   `IndexedDeclSpec` carries the index-type symbols and the per-constructor
   index expressions; its *erasure* is a plain `DeclSpec` and is what the
   existing `Machine`/`Inductive`/`GenRecursor` stack consumes, unchanged.
   The non-indexed path stays a special case, not an instance — deliberately,
   because the fragment's zero-gap results must not be re-derived through a
   vacuous-subset wrapper. §7.
7. **The riskiest step is not the mathematics.** Derived-side, the one proof
   with no ancestor at its shape is the `good`-ι/constructor-membership
   composition (§8, rung D3). Overall, the riskiest step is — as it was for
   the general recursor, five recorded late surprises running — the wiring:
   the `np > 0` lambda-graph nest (today a blanket `Decline::Params`
   **[read**, `tg.rs::gen_scope`**]**) and the new `T`-policy branch for
   family-valued motives, which `077`'s `RBTree.id` needs (§5.3, §8 rung C3).

---

## 2. The branch criterion, and the corpus census

### 2.1 The criterion

Per declaration, decided once, from the export's own data (never
per-instantiation — `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3's conclusion,
which this design adopts as-is):

| class | test on the export | translation |
| --- | --- | --- |
| (T) | resultant level **provably nonzero** (`tg.rs::provably_nonzero`, existing) | §5.2: skeleton W + `good` subset (this document §3–4); `good` vacuous iff `numIndices = 0` (existing path) |
| (S) | resultant level possibly 0 **and** the recursor is large-eliminating — its motive's `Sort` is a fresh universe parameter, visible as the extra entry in the `rec`'s `levelParams` | §5.3: `acc(A_φ, R)` carrier (§6) |
| (P) | resultant level possibly 0, recursor **not** LE — motive `Sort 0`, no extra level parameter | §5.2's truncation clause: `‖·‖` of the lifted translation — **built**, `family::trunc`, §6.3; **indifferent to `numIndices`**, since seven of the thirteen witnesses have none |

The (S)/(P) split is read off the recursor rather than recomputed from Lean's
subsingleton rules: `071`'s `SortElimProp.rec` has `levelParams=['u']` (LE)
and `072`'s `SortElimProp2.rec` has `levelParams=[]` (not LE) **[decoded]** —
the same constructor shape, differing only in that `072`'s index `id Bool b1`
is not invertible. Recomputing Lean's invertibility analysis to get that
distinction right would be re-implementing the thing being checked; the
export states the outcome, and using it can only mis-classify if the export
lies, which is the standing threat model for every field this project reads.

### 2.2 The census — every indexed family in the 91 tutorial files [decoded]

| declaration | shape | class | files | what it needs |
| --- | --- | --- | --- | --- |
| `RBTree : Sort u+1 → Color → N → Sort u+1` | 1 param, **2 indices**, recursive, 3 ctors; `rec` motive `Sort u_1`, `k=false` | **(T)** | `042`, `068`, `077` | §5.2 with genuine `good` — §3–5 of this document |
| `Eq : Sort u_1 → α → α → Sort 0` | 2 params, 1 index, non-recursive, `k=true` | (S) | 28 files | **direct clause**, not the general §5.3: carrier `[ā = b̄]` exists (`prop.rs`); `⟦Eq.rec⟧` is the minor-projection nest, ι is beta (`thesis.txt:2124`). `094_ruleK` uses `Eq.rec.{0+1,0+1}` — a **Type-level motive** — so this clause, not `proof_eq`, is what closes `094` |
| `Acc : Πα, (α→α→Prop) → α → Prop` | 2 params, 1 index, recursive, reflexive (function-typed rec arg), LE | (S) | `117`, `118` | **direct clause**: `⟦Acc α r x⟧ = [x̄ ∈ acc(⟦α⟧, R̄)]` (`thesis.txt:2126`), with `R̄ = rel_graph(⟦α⟧, ⟦r⟧)` (`quot::graph`, **built**); `Acc.rec` = `rec_acc::pack` — the module built for exactly this **[read]**. The reflexive field is **not on this path**: the direct clause replaces the carrier, so the walk that would refuse it never runs — see §6.2 |
| `SortElimProp : Bool → Bool → Bool → Prop`, `mk : ∀b b1 b2. P b b2 b1` | 1 param, 2 indices, non-recursive, LE | (S) | `071` | §5.3 **degenerate**: no recursive args ⇒ `R = ∅` ⇒ `acc(A_φ, ∅) = A_φ` (`acc_empty_relation`, exists **[read]**) ⇒ carrier `[φ(x⃗)]`, a conditional singleton. §6.2 |
| `SortElimProp2` (same, index `id Bool b1`) | 1 param, 2 indices, non-recursive, **not** LE | (P) | `072` | truncation clause: carrier `[∃…]` via `Trunc`. §6.3 |

Checked by enumerating every `inductive` record in all 91 files, not by
sampling: these five are the **only** declarations with `numIndices > 0`.
That census is scoped to the tutorials *and* to indexed declarations, and both
scopes matter: `init-prelude` and `grind-ring-5` add four more indexed families,
and class (P) is not an indexed-only class at all — §6.3 has the repository-wide
class-(P) table, thirteen declarations of which seven have no indices.
Also checked: every `Eq.rec`/`Acc.rec`/`RBTree.rec`/`SortElimProp*.rec`
*instantiation* in the corpus, because the branch a file needs depends on the
motive level actually used. `077`'s `Eq.rec` sites are all `u = 0`
(Prop motive → the existing `proof_eq` short-circuit); the only Type-motive
`Eq.rec` is `094`'s and the only Type-motive `Acc.rec` is `118`'s
**[decoded]**.

### 2.3 `RBTree`, resolved concretely

From `042_rbTreeDef.ndjson` **[decoded]**:

```text
RBTree : ∀(α : Sort u+1), Color → N → Sort u+1        numParams=1, numIndices=2
leaf  : ∀α. RBTree α Color.b N.zero
red   : ∀α (n : N). RBTree α Color.b n → α → RBTree α Color.b n → RBTree α Color.r n
black : ∀α (c1 c2 : Color) (n : N). RBTree α c1 n → α → RBTree α c2 n → RBTree α Color.b (N.succ n)
RBTree.rec : k=false, numMotives=1, numMinors=3, levelParams=[u_1, u]
             motive : ∀(c : Color)(n : N). RBTree α c n → Sort u_1
```

Its own sort is `Sort u+1` — nonzero at **every** instantiation, including
`u := 0` — so the trichotomy puts it in class (T) unconditionally and §5.3
never applies to it. The thing §5.3 is *for* — a family that must stay a
subsingleton because Prop instantiation is possible — has no purchase here.
What decides the branch is the declaration's resultant level, not
`numIndices` and not the `k` flag: `Eq` is indexed *and* subsingleton;
`RBTree` is indexed and never a subsingleton.

The `good` predicate `RBTree` needs, in the thesis's own notation:

```text
good leaf              (c,m) := (c,m) = (Color.b, N.zero)
good (red n l x r)     (c,m) := (c,m) = (Color.r, n)        ∧ good l (Color.b, n) ∧ good r (Color.b, n)
good (black c₁ c₂ n l x r) (c,m) := (c,m) = (Color.b, succ n) ∧ good l (c₁, n)      ∧ good r (c₂, n)
```

### 2.4 Where the "needs Eq elimination" belief came from, and why it is void

The `spec` judgment's base case (`thesis.txt:1793`) emits `x = e` — in DTT, a
use of the equality *type*, and any later use of that fact (deriving the
recursor, inversion) transports along it with `rec₌`. Hence the recorded
chain: `Eq`'s elimination before `good`. But this development never builds
`good` as a DTT term. It builds `good` as a **set-level function into
`𝒫(Idx)`** (§3), where the base case is the kernel formula
`w = ⟨e₁,⟨e₂,•⟩⟩` inside a Separation, and every downstream use of it is
`eq_leibniz` plus Kuratowski-pair injectivity (`pairs.rs`, exists
**[read]**). The thesis's own interpretation of `rec₌` as the identity
(`thesis.txt:2124`) is the same observation made from the other side: after
interpretation, equality elimination is substitution of equals, which a
FOL kernel has as a primitive. **Checked, as the task asked: the cost is zero
new constructions.** What survives of the dependency is only that the
*checker* must interpret Lean's `Eq` type and `Eq.refl` — which
`derived/src/prop.rs` already does — and `Eq.rec` as the minor-projection
nest (§2.2's direct clause), which `094` needs regardless of indexed
families.

---

## 3. The `good` component — construction

### 3.1 The data

Fix a declaration with `np` parameters, index-type symbols `ι₀ … ι_{ni−1}`
(`ι_k` of arity `np + k`: parameters, then earlier indices), and per
constructor `i` the erased data (`args`, `order` — as today) plus:

- `e⃗ᵢ` — the **result indices**: `ni` symbols, each of arity `np + kᵢ`
  (parameters, then *all* of the constructor's non-recursive arguments, in
  plain order);
- `d⃗ᵢⱼ` — per recursive argument `j`, the **argument's indices**: `ni`
  symbols of arity `np + (#Plain slots before that Rec slot)`.

Arities follow the established `FnSym` convention (`inductive/spec.rs`
**[read]**): dependence is expressed by application, because the kernel has
`Formula::subst` but no `Term::subst`. The restriction this encodes — no
index expression may mention a recursive field — is the same one the thesis's
rules impose (the recursive-argument rule does not extend `Γ`,
`thesis.txt:1798–1801`), and a Lean declaration violating it is
**unrepresentable and must be declined** (§7, §9.2). `RBTree` satisfies it:
`red`'s rec-arg indices `(Color.b, n)` mention only the plain field `n`,
which precedes both `Rec` slots in the order mask `Plain,Rec,Plain,Rec`;
`black`'s `(c₁,n)`/`(c₂,n)` likewise **[decoded]**.

### 3.2 The index space

```text
Idx(p⃗) := Σ x₀:ι₀. … Σ x_{ni−1}:ι_{ni−1}. 1        tup(x⃗) := ⟨x₀,⟨x₁,…⟨x_{ni−1},•⟩…⟩⟩
```

— one `sigma::Telescope` at `(np, [ι₀…ι_{ni−1}])`, giving `intro`,
`proj_mem` and `eta` for free **[read**, `sigma/telescope.rs`**]**. This is
the thesis's `(z₁,…,(zₙ,()))` tuple convention exactly.

### 3.3 The per-constructor `good` value

One `define_by_membership` per constructor mints `Gᵢ(p⃗, σ, r)` — `σ` the tag
payload (the plain-argument tuple), `r` the induction-hypothesis row — with
defining axiom

```text
⊢ ∀p⃗ ∀σ ∀r ∀w.  ( w ∈ Gᵢ(p⃗,σ,r)  ↔
      ( w ∈ Idx(p⃗)
      ∧ ( w = tup(e⃗ᵢ(p⃗, comp₀σ … comp_{kᵢ−1}σ))
        ∧ ⋀ⱼ  tup(d⃗ᵢⱼ(p⃗, …)) ∈ app(app(r, Injⱼ(•)), •) ) ) )
```

i.e. `Gᵢ` is `{tup(e⃗ᵢ)}` when every recursive child is good at its required
index, and `∅` otherwise. (The `app(·, Injⱼ(•))` spelling follows
`inductive/step.rs`'s rec-slot convention **[read]**; whether the ih row
needs the extra `•` application depends on which of `wrec`'s ih encodings the
step reuses — a spelling decision for D2, not a design fork.)

This is the `spec` judgment's `G`, specialised to the set level. The three
`ctor` rules of `thesis.txt:1793–1801` correspond as: the base case is the
`w = tup(e⃗ᵢ)` conjunct; the `∀y : β` rule is absorbed into `σ` being the
telescope tuple (the thesis's `[π₁p′/y][π₂p′/p]` substitutions *are* the
`compⱼ` projections — the mechanism `sigma/telescope.rs` was built to
provide); the recursive-argument rule is the `⋀ⱼ … ∈ app(r,…)` conjunct
(`g (inl (z)) e` with `γ` empty, since plain recursive arguments are the
scope — function-typed ones are declined today and stay declined).

### 3.4 The `good` recursion, and why it is cheaper than the value recursion

```text
e_G(p⃗)      := the packed step with rows ⟨⟨Injᵢ(σ), q⟩, Gᵢ(p⃗, σ, π₂q)⟩   — one Replacement per ctor
goodrec(p⃗) := wrec(A, B, U({A,T_B}), 𝒫(Idx(p⃗)), e_G(p⃗))
```

— the same `RecCore`/`wrec` apparatus, the same step shape as
`inductive/step.rs` with `valᵢ` replaced by `Gᵢ`. The analogues of
(S1)/(S2) are the same derivations. The analogue of (S3) — `step_typed` — is
where the shape pays off:

> every value `Gᵢ(p⃗,σ,r)` is, by its defining axiom, a subset of `Idx(p⃗)`,
> hence a member of `𝒫(Idx(p⃗))`, **with no hypothesis about `σ` or `r` at
> all**.

So `goodrec`'s totality and ι are **unconditional** (given `closed`, which
`Inductive::closed` discharges at every arity **[read]**). The value
recursor's `HYP` — the pointwise minor-typing bundle that is the general
recursor's one standing hypothesis — simply has no counterpart here. The
per-constructor `good`-ι comes out as

```text
(G-ι)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗. ( Hᵢ^W →
           app(goodrec, ctorᵢ(y⃗,r⃗)) = Gᵢ(p⃗, tup(y⃗), ih-row) )
       with  app(app(ih-row, Injⱼ(•)), •) = app(goodrec, rⱼ)
```

where `Hᵢ^W` is the constructor's argument typings with recursive arguments
at the **skeleton** `W` — exactly (S4)'s `Hᵢ^ctor`, minus `HYP`.

---

## 4. The carrier, membership, inversion

### 4.1 The carrier

```text
ind(p⃗, x⃗) := { s ∈ W(A,B,u) : tup(x⃗) ∈ app(goodrec(p⃗), s) }
```

— one `define_abbrev` of arity `np + ni`, and the thesis's
`λx :: α. {s : Wp:A. B p | rec_W (λp. G p) s x}` (`thesis.txt:1784`) with the
`rec_W … s x` application read as "the index tuple is in the good-set of
`s`". `ind(p⃗,x⃗) ⊆ W` holds for every `x⃗`, including junk ones — a Separation
is a subset no matter what is asked of it — which is what makes the universe
statement (§5.4) quantifier-friendly.

### 4.2 Constructor membership

```text
(M)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗. ( Hᵢ^ind → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)) )
```

where `Hᵢ^ind` is the Lean-shaped hypothesis: plain arguments at their types,
recursive arguments at `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))`. Derivation: (1) weaken each
`rⱼ ∈ ind(…)` to `rⱼ ∈ W` (Separation), obtaining `Hᵢ^W`; (2) `Ctor::mem`
puts `ctorᵢ ∈ W` (existing **[read]**); (3) (G-ι) computes
`app(goodrec, ctorᵢ)`; (4) `tup(e⃗ᵢ) ∈ Gᵢ(…)` by the defining axiom — the
equality conjunct by reflexivity, the child conjuncts because
`tup(d⃗ᵢⱼ) ∈ app(goodrec, rⱼ)` is exactly what `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` unfolds to.
No step is new machinery.

### 4.3 Inversion, and where Leibniz earns its keep

From (G-ι) read right-to-left plus the `Gᵢ` axiom:

```text
(I)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗ ∀x⃗. ( (Hᵢ^W ∧ ctorᵢ(y⃗,r⃗) ∈ ind(p⃗,x⃗)) →
         ( tup(x⃗) = tup(e⃗ᵢ(p⃗,y⃗))  ∧  ⋀ⱼ rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗)) ) )
```

and componentwise `xₖ = eᵢₖ` by Kuratowski injectivity. Every use of these
equalities downstream — moving a motive from index `e⃗ᵢ` to index `x⃗`, the
recursor's typing at the major premise's index — is one `eq_leibniz`. This is
the entire content of "the base case wants `Eq`'s elimination".

### 4.4 Non-vacuity — both polarities, per the standing discipline

A `good` that came out constant would make every theorem above true and
worthless. Pin both directions at the `RBTree` shape (as a derived-layer
test, no Lean syntax):

```text
⊢ leaf ∈ ind(p, ⟨Color.b, ⟨zero,•⟩⟩)                       (M) fired closed
⊢ ¬( leaf ∈ ind(p, ⟨Color.r, ⟨zero,•⟩⟩) )                  (I) + tag distinctness
```

the second from inversion: membership would force
`⟨Color.b,…⟩ = ⟨Color.r,…⟩`, refuted by injectivity plus the enum
distinctness already derived for the index type's own translation. This test
is the analogue of `acc`'s two-polarity witness set and is **not optional**:
it is the only thing that distinguishes `good` from `λs.Idx` (always-true)
and from `λs.∅` (always-false).

---

## 5. The indexed recursor and ι — the §5.4 invention

§5.4 is future work in the thesis; as with `RECURSOR-DESIGN.md`, this part is
ours. The finding is that **almost nothing is new**: the indexed family's
recursor engine *is* the erased declaration's `GenRecursor`.

### 5.1 Why the erased recursor is the right engine

Lean's indexed recursor
`T.rec p⃗ (C : Πx⃗. ind p⃗ x⃗ → Sort u₁) s⃗ x⃗ (t : ind p⃗ x⃗)` reduces, at
`t = ctorᵢ …`, to the minor applied to the constructor's fields in declared
order followed by one ih per recursive field — verified against
`RBTree.red`/`black`'s `RecRule::rhs` in the export (`RECURSOR-DESIGN.md`
§10.2, re-checked here **[decoded]**: `red`'s rhs is
`red n l x r (rec … Color.b n l) (rec … Color.b n r)`). The index arguments
`x⃗` appear in the reduct **only** inside the recursive calls' index spines —
and there they are determined by the child (`d⃗ᵢⱼ`), not free. At the set
level the recursion never needs the indices at all: it runs on the skeleton
tree. So:

```text
⟦T.rec⟧(p⃗, C, s⃗, x⃗, t) := app(grec(p⃗, s⃗, T_policy), t)      — x⃗ dead
```

with `grec` the **existing** `GenRecursor` of the erased spec. The ι
equation the checker must certify beta-reduces on both sides to (S4): on the
left the nest consumes `x⃗` as inert lambda binders; on the right each
recursive call `T.rec p⃗ C s⃗ d⃗ᵢⱼ rⱼ` beta-reduces to `app(grec, rⱼ)`, which is
(S4)'s rhs slot. **The indexed ι is the non-indexed ι with `ni` dead binders
per nest** — `(S4)` plus `2×ni`-ish extra beta obligations, all of the shape
the nest discipline already discharges. No new derived theorem is needed for
ι itself; the one new derived lemma is the `Hᵢ^ind → Hᵢ^W` weakening bridge
(§4.2 step 1) packaged for the wiring.

### 5.2 What is genuinely new: the `T`-policy for index-dependent motives

The value recursor is simply typed (`RECURSOR-DESIGN.md` §5: one target set
`T`). An indexed motive `C : Πx⃗. ind p⃗ x⃗ → Sort u₁` varies with `x⃗` even
when it ignores the tree — so policy 2 ("motive at the first nullary
constructor as the nest walked it") picks `⟦C⟧` at `leaf`'s indices, which
does **not** contain `red`/`black`'s minor values. `077`'s actual Type-motive
site is `RBTree.id`, whose motive is `λ c n t. RBTree α c n` **[decoded]** —
the family itself at its own index binders. For that shape the right target
exists and is canonical:

```text
family-valued motive:  C = λx⃗ t. T′ q⃗ ⃗f(x⃗)  for some translated family T′
                       ⇒  T := S′, the skeleton of T′
```

since every `ind′(q⃗, ⃗f(x⃗)) ⊆ S′` regardless of `x⃗` (§4.1). The `HYP` bridge
is then: Lean's minor typing gives values in `ind′(…)`; weaken to `S′`
(Separation) — the same safe direction as §4.2. For `RBTree.id`, `T′ = T`
and `T := S`, the declaration's own skeleton. Recognising the shape is a
syntactic check on the motive body (the family constant applied to the
motive's own binders / to translated index expressions); anything else
declines to policy 3 (counted gap). This is the one new policy branch; it
sits beside branches 1–3, replacing none of them.

### 5.3 The Prop-motive sites

Unchanged: `Certifier::iota` tries `proof_eq` first **[read**, per
`RECURSOR-DESIGN.md` §5.1**]**, and `077`'s `id_spec` proof — motive
`λ c n t. Eq (RBTree.id … t) t`, every `Eq.rec` at `u = 0` **[decoded]** —
never reaches `grec`.

---

## 6. §5.3 — subsingleton eliminators, against what `acc` actually exports

### 6.1 `acc^φ_r` is an instantiation, not a module

The thesis (`:1831–1845`) builds `acc^φ_r` from plain `acc` over the subtype
`{x : α | φ x}` with the projected relation `r′`. At the set level both
wrappers evaporate, **because of the two corrections that landed with
`derived/src/acc/` and must not be undone**:

- `step_closed` carries the `x ∈ A` guard the thesis omits, and `preds_in`
  carries `y ∈ A` — without the former, `acc(A,R) = A` for every `R`
  (recorded, with the collapse argument, in `acc/condition.rs`'s header
  **[read]**);
- `R ⊆ A × A` is **not** assumed anywhere — edges leaving `A` are ignored by
  the guards, and the countermodel at `acc_no_two_cycle` (`A := {a}`,
  `R := {⟨a,b⟩,⟨b,a⟩}`, `b ∉ A` — `a` is accessible *relative to `A`* while
  sitting on a 2-cycle through `b`) pins that the `w ∈ A` conjunct is
  load-bearing, not proof-convenience **[read**, `acc/witness.rs:226`**]**.

Consequently, with `A_φ := {q ∈ Idx(p⃗) : φ(q)}` (one Separation),

```text
acc^φ_r  =  acc(A_φ, R)        — R passed through UNRESTRICTED
```

is *definitionally* the φ-restricted accessibility: `preds_in(A_φ,R,C,q)`
quantifies only over predecessors satisfying `φ`, which is precisely the
thesis's intent, and no projected `r′`, no subtype pairing `⟨x,h⟩` (whose
second component would be `•` anyway) and no new module are needed. The
thesis's remark that "large elimination for `acc^φ_r` is derivable because
`∃h : p. q` has projections" becomes trivial: membership in `acc(A_φ,R)` is a
formula, and its "projections" are conjunction elimination.

`φ` and `R` come from §5.3's `LE ctor` recursion (`:1848–1877`), which at the
set level is a **formula** builder, not a set builder: existentially close
each argument (`∃y ∈ β̄ᵢ(…)`), the base case contributing
`q = tup(ē)` to `B` (=φ's matrix) and each recursive argument contributing
`(S ∧ ∃z⃗. q′ = tup(ē′)) ∨ R` to the relation's matrix, exactly per the
thesis's `[S; R]` accumulator. Both land as `define_by_membership`
Separations on `Idx` and `Idx × Idx`. The carrier is
`⟦P x⃗⟧ := [tup(x⃗) ∈ acc(A_φ, R)]` — a conditional singleton, as class (S)
requires at every instantiation.

### 6.2 The degenerate and direct cases are the whole tutorial demand

- **No recursive arguments** (`071_SortElimProp`): the `LE ctor` recursion
  emits `R` with an empty disjunction, i.e. `R = ∅`, and
  `acc(A_φ, ∅) = A_φ` — **already derived**, `acc_empty_relation` **[read]**.
  Carrier `[φ(x⃗)]` outright; intro is Separation-intro at the `mk` instance;
  the recursor's reduct is the minor at the **index projections rearranged
  per the variable–variable equalities** (`mk : ∀b b1 b2. P b b2 b1` ⇒ minor
  applied at `x₂, x₁`) — the thesis's "delayed elimination" of `:1866–1870`,
  which at the set level is: read the fields off `tup(x⃗)` with `compⱼ`,
  permute per the base-case equality, ι is beta. Invention, but small and
  checkable per-file.
- **`Acc` itself** (`117`/`118`): not the general §5.3 translation but the
  interpretation clause `⟦acc_{α,r} x⟧ = [x ∈ acc(⟦α⟧,⟦r̄⟧)]`
  (`thesis.txt:2126`) with `R̄ := {⟨y,x⟩ ∈ ⟦α⟧×⟦α⟧ : • ∈ app(app(⟦r⟧,y),x)}`,
  and `Acc.rec` = `rec_acc`'s `pack`, whose curried `e(x)(•)(ih)` spelling
  was chosen to match Lean's minor **[read**, `rec_acc.rs` header**]**. `R̄` is
  no longer a Separation to be written: it is `quot::rel_graph`, built with
  the four bridge lemmas both this clause and `Quot.sound` consume.

  **What blocks `117`/`118` today is the carrier, not the recursor**
  **[measured**, `mini --block`**]**. Both report
  `obligation: the type's interpretation, ⟦ty[σ]⟧`, both have `typesOk=0`, and
  both mint `fun-typed-rec-arg(Acc)` at `zoneb.rs`'s constructor walk — because
  the *type* of each declaration mentions `Acc.{ℓ}`, and `⟦Acc⟧` does not
  exist. `⊢ ⟦val[σ]⟧ ∈ ⟦ty[σ]⟧` is *not attempted*. So the three obligations
  are strictly ordered — carrier, then `⟦Acc.rec⟧`'s typing, then the ι — and
  only the third is §9.6's bridge. Reading `fun-typed-rec-arg(Acc)` as a
  statement about the recursor inverts that order.

  The reflexive field is a fact about `Acc` and **irrelevant to this route**:
  `zoneb::build` dispatches on `direct::clause_for` *before* the index check
  and the trichotomy, exactly as it does for `Eq`, so a declaration with a
  direct clause never reaches the walk that refuses a function-typed
  recursive argument. Widening `CtorSpec::recs` would serve the *general*
  translation of `Acc`, which this document has declined to use for `Acc`
  since it was written.

  The two files are also **different problems**, and the scheduled σ decide
  which **[decoded]**: `117` is one pair at `Acc.rec.{0,0}` — a `Sort 0`
  motive, so the eliminator is a proof and no `T`-policy arises — while `118`
  is one pair at `Acc.rec.{1,1}` with motive `fun _ _ => Bool`, a genuine
  large elimination at a *constant* motive, where the target is `⟦Bool⟧` and
  the `T`-policy is trivial. `118`'s reduct has a lambda under the minor (the
  `∀y h. …` ih), the shape that sank `116` on the W side; `rec_acc::ih`/`cval`
  were built as that lambda's graph, so the derived side is ready, but the
  **wiring bridge from the reduct's lambda nest to `ih(accrec,…)` is new work
  and a named risk** (§9.6).
- **`Eq`** (28 files): direct clause, §2.2/§2.4. No `acc` involvement.
- A **recursive user-defined subsingleton** (the case needing `acc^φ_r` with
  `R ≠ ∅` and the full §5.3 recursion) has **no witness in the 91 files —
  nor in `init-prelude`** **[decoded**, 2026-08-01, every `.ndjson` in
  `vendor/arena-tests` and `checker/tests/fixtures`**]**. The full list of
  class-(S) declarations anywhere in the repository is `Eq`, `HEq`,
  `SortElimProp`, `T` (`nested-unused-param`) — all **non-recursive**, hence
  degenerate — and `Acc`, which is recursive but *reflexive* (function-typed
  recursive argument), so it is not expressible as an `IndexedDeclSpec` at all
  and takes the direct clause above. `init-prelude`'s other two indexed
  declarations, `Nat.le` and `Nat.le.below`, have **two constructors** and are
  therefore not large-eliminating: class (P), the truncation clause. This
  corrects an expectation recorded during the C0 census that the prelude's
  indexed demand would exercise the general §5.3 route; it does not.

  The carrier is built generally (it is one formula recursion), and so now is
  the **recursor** — `derived/src/inductive/family/le_rec.rs`, §5 of this
  document's §5.4-invention discipline applied to class (S). It is `rec_acc` at
  `(A_φ, R)` plus the edge-introduction rule that makes ι fire, and it covers
  `mᵢ = 0` uniformly, which is the shape the degenerate witnesses need. What
  stays deferred is the **step**: `thesis.txt:1866–1870`'s delayed elimination
  (index tuple ↦ constructor fields) is per-declaration data
  `IndexedDeclSpec` does not carry, so `le_rec` states it as the hypothesis
  `minor_eq` — the same status `step_typed` and the general recursor's
  pointwise `HYP` have — and the wiring owes its discharge.

### 6.3 Class (P) — built, `derived/src/inductive/family/trunc.rs`

`‖·‖` of the lifted §5.2 translation, per `thesis.txt:1813–1815`. The general
route (translate at `ℓ′ ≥ 1`, wrap in `Trunc`) is what landed, at both an
indexed and a non-indexed entry point; `072`'s collapse to
`[∃y⃗. tup(x⃗) = tup(ē(y⃗)) ∧ …]` is not taken as a special case, because the
truncation is one symbol application on a carrier that already exists and the
collapse would save nothing.

Three things this section got wrong, all found by decoding rather than by
reasoning, and all corrected in `trunc.rs`'s header:

1. **The demand is not `072`.** Classifying every `inductive` record in every
   export in this repository by `rec.levelParams` against the declaration's own
   gives **thirteen** class-(P) declarations **[decoded]**: `SortElimProp2`,
   `Nat.le`, `Nat.le.below`, `List.Mem`, `Int.NonNeg` and `Prod.Lex` indexed;
   `Or`, `Exists`, `Nonempty`, `ByteArray.IsValidUTF8`, `BoolProp`,
   `PropStructure` and `PredWithTypeField` not. Three of them — `Nat.le`,
   `Nat.le.below`, `List.Mem` — are **recursive**, which §6.2 said had no
   witness anywhere; that finding was about class *(S)*, and does not carry to
   class (P).
2. **`numIndices > 0` is the wrong census for this class.** Seven of the
   thirteen have no indices at all, so `trunc.rs` serves both shapes. That is
   the opposite of §7.2's policy for class (T), and for a reason: nothing is
   re-derived here.
3. **`ulift` really does cost nothing, and the corollary is bigger than
   expected.** `thesis.txt:2106–2108` gives `⟦ulift_n^n α⟧ = ⟦α⟧` and
   `⟦↑e⟧ = ⟦↓e⟧ = ⟦e⟧` **[decoded]**, so the *same* carrier serves at `ℓ` and at
   `ℓ′` — there is no second W-type at the lifted universe. The level survives
   only in the universe statement, and there class (P) is **cheaper** than class
   (T): `‖a‖ ∈ U₀` is one `cond_in_u0`, with no `C₂`, no `W ∈ U₁` and no
   antecedent, because `‖a‖ ⊆ 1` holds whatever `a` is.

Small elimination only, so there is no recursor set: ι is
`TruncCarrier::only_point` (*every* inhabitant is `•`, so both sides of an ι are
`•` and it holds by reflexivity) plus `TruncCarrier::irrel` to type it. What
does need a derivation, and is the only one in the file, is the Lean-shaped
constructor rule for a *recursive* class-(P) declaration: a recursive argument
of a `Prop` is a proof, so its hypothesis is `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖` rather than
`rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)`, and the element has to be eliminated existentially
(`Trunc::elim`, then one `hyp_ex_branch` per recursive argument).

---

## 7. The `DeclSpec` extension

### 7.1 The shape

New type in `derived/src/family/` (or `inductive/family.rs` — placement per
the one-construction-per-file rule), **wrapping** the existing spec:

```rust
pub struct IndexedDeclSpec {
    pub base: DeclSpec,              // the ERASED declaration — unchanged consumers
    pub indices: Vec<FnSym>,         // ι_k, arity np + k;  empty ⇔ non-indexed
    pub ctors: Vec<CtorIndices>,     // parallel to base.ctors
}
pub struct CtorIndices {
    pub result: Vec<FnSym>,          // e⃗_i : ni symbols, arity np + k_i
    pub rec_args: Vec<Vec<FnSym>>,   // d⃗_ij : per Rec slot, ni symbols,
                                     //         arity np + plains_before(j)
}
```

`well_formed` extends `DeclSpec::well_formed` with the arity checks above and
`rec_args.len() == base.ctors[i].recs`.

### 7.2 Wrapper, not field — the judgment call, argued

The `Slot` mask went the other way (fields added to `CtorSpec` in place), so
this deviates from precedent and should say why. Three reasons:

1. **The erased spec is the identity the shared machinery is keyed on.**
   `Machine`/`Inductive`/`GenRecursor` consume `DeclSpec` and are cached
   against it; `goodrec` (§3.4) is *also* the erased declaration's `wrec` at
   another target. Growing index fields inside `DeclSpec` would make every
   existing consumer carry fields it must ignore, and the ignoring would be
   an invariant ("the carrier does not read `indices`") instead of a type.
2. **The non-indexed path stays a special case, and must.** Routing
   `ni = 0` through the subset carrier would wrap `Bool`/`N`/`List` in a
   provably-vacuous Separation (`INDUCTIVES.md:176`'s collapse), re-deriving
   the whole zero-gap fragment through `ind(p⃗) = {s ∈ W : • ∈ …}` — real
   cost, zero benefit, and a direct violation of the "fragment stays 27/27"
   non-negotiable. The vacuity collapse is a theorem worth *testing* (one
   witness: derive `ind(p⃗) = W` at an `ni = 0` toy spec), not a code path
   worth taking.
3. The `Slot` precedent's own caveat pointed here: "whether to put the mask
   on `CtorSpec` or on a thin `RecSpec` wrapper is the … task's call — the
   carrier files must not be churned" **[read**, `RECURSOR-DESIGN.md`
   §3.1**]**. The mask was consumed by the same module family; the index
   data is consumed by a *new* module family. Wrapping is the no-churn
   answer.

So: **the non-indexed path stays a special case; the indexed construction is
a new consumer of the same machine.** What must change inside
`inductive/spec.rs` itself: nothing. (`spec.rs`'s header sentence "adding
[an index field] would not be an extension of this construction but a
different one — it needs the equality type first" is half-superseded by this
document: a different construction, yes; the equality-type prerequisite is
void per §2.4. Correct that header in place when D1 lands.)

---

## 8. Ordered implementation plan

Boundary rule throughout: `derived/` speaks `Term`/`Formula`/`FnSym` only;
everything touching `ExprPtr`/`NamePtr`/export data is `checker/` (`tg.rs`)
— and, since the mini port shares `derived/` wholesale and reimplements only
clause dispatch **[read**, `mini/src/interp.rs` header**]**, each checker
rung below lands twice (tg.rs and `mini/`), against the same derived
exports.

**Derived side** (one construction per file; every rung with its own
two-polarity witness test):

- **D1** — `family/spec.rs`: `IndexedDeclSpec`/`CtorIndices` +
  `well_formed`; the `Idx` telescope assembly (§3.2, reusing
  `sigma::Telescope`); fix `inductive/spec.rs`'s header sentence in place
  (§7.2). Small.
- **D2** — `family/goodstep.rs`: the `Gᵢ` symbols and the `good` step
  Replacements; (S1)/(S2) analogues; **unconditional** `step_typed` (§3.4).
  Mostly `inductive/step.rs` at a different value slot.
- **D3** — `family/good.rs` + `family/carrier.rs`: `goodrec`, (G-ι), the
  `ind(p⃗,x⃗)` Separation, membership (M), inversion (I), and the §4.4
  witness pair. **← riskiest derived rung**: (M)/(I) compose a `wrec` ι with
  a `define_by_membership` unfolding under an ambient hypothesis across `n`
  branches — the same risk profile (S3) had, and like (S3) it has no
  hand-written ancestor at its shape.
- **D4** — `family/universe.rs`: `⊢ [H →] ind(p⃗,x⃗) ∈ U₁` = `DeclUniverse`'s
  `wty_in_u1` + one `C₂` (`cumul/chain.rs:83` **[read]**), `∀`-closed over
  `x⃗` with no new antecedent — the list stays exactly `A ∈ U₁` (§7 of
  `cumul/decl.rs` unchanged). For class (S)/(P) carriers there is **no
  universe obligation at all**: `[φ] ∈ U₀` is `Tower::cond_in_u0`
  (`tower/levels.rs:281` **[read]**), and membership at higher levels is
  `u0_mem` + transitivity. This settles the task's question 5: the
  subset-of-W carrier costs one lemma over the existing chain; the acc
  carrier costs zero.
- **D5** — `family/le.rs` (class S): the `LE ctor` formula recursion
  producing `φ`/`R`; carrier `acc(A_φ, R)`; the degenerate-`R` corollary via
  `acc_empty_relation`; the index-projection minor for the non-recursive
  recursor (§6.2). Independent of D2–D4; can run in parallel.
- **D6** — the `Hᵢ^ind → Hᵢ^W` weakening bridge packaged for the wiring, and
  the (S4)-reuse statement of §5.1 pinned by a derived test at an
  RBTree-shaped spec (3 ctors, masks as decoded, 2 indices over an enum and
  a recursive type).

**Checker side** (tg.rs, then mini):

- **C0** — lift `Decline::Params`: the `np > 0` type-former lambda-graph
  nest and parameter spines. **Prerequisite, not indexed-specific** — it is
  already its own recorded item ("the spec is general in `np`; there would
  be nothing to attach it to" **[read**, `gen_scope`**]**), it currently
  declines 35 tutorial occurrences, and `RBTree` (`np = 1`) is unreachable
  without it. Do it first and bank its own corpus movement.
- **C1** — spec builder: walk `num_indices` binders, build
  `IndexedDeclSpec`; the branch trichotomy of §2.1 (reading the recursor's
  `levelParams` for S/P); new decline variants (`IndexRecFieldDep`,
  index-shape mismatch) replacing the blanket `Decline::Indices` — which
  today fires 106 times on the tutorials and is the single largest decline
  row **[read**, `MEASUREMENTS.md`**]**.
- **C2** — carrier + constructor wiring for class (T) indexed: type former
  as an `np + ni`-graph nest, constructor memberships from (M). Measurable:
  `042`'s declaration-checking gaps.
- **C3** — recursor nest: index binders dead in the bottom (§5.1), the
  family-valued-motive `T`-policy branch (§5.2), pointwise-`HYP` bridging
  through D6. **← riskiest step overall**, same grounds as every prior
  wiring rung — this is where derived statements meet nest-computed terms,
  and where all five recorded late surprises lived. Measurable: `068`, and
  `077`'s Type-motive site.
- **C4** — the direct clauses, each small and independently landable:
  `Eq.rec` as the minor-projection nest (`094`); `Acc`/`Acc.rec` via
  `acc` + `rec_acc` (`117`/`118` — flag the reduct-lambda bridge, §9.6);
  class-(S) degenerate (`071`); class-(P) truncation (`072`).

Acceptance gates per the non-negotiables: fragment 27/27 at 0/0, arena
152/0/2, all existing zero-gap files byte-identical, `HAS_GAPS` rows removed
one at a time as they close.

### 8.1 Status, 2026-08-01 — C0 landed; C1–C4 not started

**C0 is done and measured on its own**, per its own instruction. The whole of
the Lean-facing layer is now general in `np`: the type former is a nest of `np`
lambda graphs (`tg.rs::gen_ty_nest`, a `GenTyNest`), every constructor's nest
and `CtorRule` carries the parameter spine ahead of its fields, and the general
ι rule takes `p⃗` from `ta[..np]`. The `T`-policy and the recursor nest were
already written in `np` and needed no change. `MEASUREMENTS.md` has the
numbers; the short version is **`init-prelude` 15572 → 15492 gaps at +49% wall
clock**, and the tutorials do not move at any of the three instantiation sets.

Three things the design did not say, all of which C1–C3 will meet again:

1. **A declaration one of the hand-written recognisers owns must never fall
   through to the general path**, even when the recogniser refused a particular
   *use*, and saying so takes two guards. `ind_const_recognised` returns `None`
   for both "not my shape" and "my shape, but not for this use", and conflating
   them builds a *second* carrier for the same inductive over the other stack's
   incompatible sets — `ind_abbrev` then re-mints `⟦List⟧` and `interp` stops
   being a function on that constant, which is the recorded failure that cost 54
   ι sites. The shape-only `recognised_ind` gate in `ind_const` and
   `gen_rec_bottom` is the first guard; the second is that it must **not**
   consult `is_recursive`, because while an inductive is being checked the
   checker installs a temporary `InductiveData` with `is_recursive: false`
   (`inductive.rs:115`) and `list_shape`/`nat_shape` therefore refuse their own
   declarations for the duration. Found by reading `076_listRecReduction`'s
   ledger rows, not by a test: one
   `shared inductive symbols declined: body not canonical` where there had been
   none, and it did not move when only the first guard was in place. §8's C2/C3
   inherit both — the seam is the same, and an indexed family's own check will
   be inside exactly that window.
2. **`rec.levelParams` is `[motive, ind…]`** — the motive's level is *first*,
   so the declaration's own instantiation is the **tail** of the recursor's
   **[decoded**, `042`'s `RBTree.rec` is `[35, 5]` against `RBTree`'s `[5]`,
   and `076`'s `List.rec` is `[9, 2]` against `List`'s `[2]`**]**. This is what
   `WIRING-DESIGN.md` §6.1 left as "an export-format convention this has not
   been checked against"; it is checked now, and it is what lets a
   level-polymorphic declaration be eliminated at all.
3. **`βⱼ`'s stored body is not usable at a use site once `np > 0`.** It is
   stated over the *walk's* parameter variables, and the kernel has no
   `Term::subst`, so the body at actual parameters has to be read off `βⱼ`'s
   **instantiated defining equation** (`inst_all` substitutes into the
   formula). The same applies to the raw carrier `W`, which is why
   `fire_general` uses `recursor::carrier_at` at `p⃗` and checks it against
   `ind.ty_ax` rather than using `ind.wty`. Any C2 code that wants
   `eᵢₖ`'s or `ιₖ`'s body at a use site is in exactly this position.

**C1–C4 are not started.** Nothing in `derived::inductive::family` is reachable
from the checker yet; `RBTree` still declines, now under a sharper reason (see
below). What C2 will hit first, and what this document does not answer: (M)'s
`ni` extra antecedents `Eᵢ` are **not positional against the constructor's Lean
spine**, and `has_type_ctor_app` instantiates a `CtorRule`'s premises
positionally against it (`tg.rs:7448–7464`, `subj != ts[i]` → refuse). So `Eᵢ`
cannot simply be appended to `CtorRule::prems`: either the rule grows a second,
subject-addressed premise list, or `Eᵢ` is discharged at rule-build time. For
`RBTree.red` the second is available — `n ∈ N` *is* the field premise `β₀`'s
own atom and `Color.r ∈ Color` is closed — but that is an argument about one
constructor, not a general answer, and it should be settled before C2 is
written rather than during.

One decline row changed meaning as part of C0, and it is the census §2.2 asks
for at prelude scale: `gen_scope` now tests the **eliminator trichotomy before
`num_indices`**, so `…declined: indices` counts only class-(T) indexed
families — the ones §5.2 would serve — while every indexed `Prop` (`Eq`, `HEq`,
`Acc`, …) lands in `…declined: sort-ambiguous or Prop (class S/P)` where §5.3
and the truncation clause will find it.

---

## 9. Failure modes and open questions

Failure modes (each must surface as a counted decline or a conditional
certificate — never a wrong `Proved`):

1. **Index expression mentions a recursive field** — unrepresentable in
   `CtorIndices` (§3.1); decline (`IndexRecFieldDep`). Same status as the
   existing `RecFieldDep`: no corpus witness, not tested against a live
   kernel whether Lean even accepts it (open, inherited from
   `RECURSOR-DESIGN.md` §9.4).
2. **`good` degenerating to a constant** — caught only by the §4.4
   two-polarity witness; a missing negative witness would let an
   always-true `good` ship every (M) and no (I) content. This is the
   design's own vacuity hazard; the test is part of D3's definition of done.
3. **Family-valued-motive recogniser misfiring** (§5.2) — a motive that
   *looks* family-valued but isn't lands in policy 3: conditional `HYP`,
   undischargeable, counted. Safe direction.
4. **Mutual / nested / function-typed-rec-arg indexed families** — out, as
   before, now with the index axis multiplied in; the existing declines
   cover them because `gen_scope`'s checks run before and independently of
   the index walk.

   For the function-typed case specifically, the demand is **zero, not small**,
   and it is worth stating because the one apparent witness is not one. `le.rs`
   records that a function-typed recursive argument has no representable
   witness in the tutorials or the prelude; `Acc` looks like the exception and
   is not, because its direct clause (§6.2) replaces the carrier before the
   walk that would refuse it. So nothing in this repository needs the
   `Σ(z::γ)` fibre. That matters for sizing: widening `CtorSpec::recs` from a
   count to a telescope changes `B`, hence `W(A,B,u)`, hence the *carrier* —
   `step.rs`, `values.rs`, `typed.rs`, `iota.rs` and `rect.rs`'s `recarg_eta`
   all key on `finord(m)` — so it is a module-sized change, and it should be
   ranked as speculative until a witness exists rather than as measured work.
5. **Per-instantiation drift** — the branch is per-declaration (§2.1); the
   recursor's extra level `u_1` is per-σ as today. Nothing new, but C1 must
   route the trichotomy through the declaration's *symbolic* level, exactly
   as `provably_nonzero` already does, or the LPI §3.3 design error returns.

Could not settle:

1. **Whether `077`'s remaining 53 gaps are all RBTree-opacity cascade.**
   Predicted (the file's gap history halved when an unrelated guard change
   landed, so its composition is volatile); needs one `stepcount` run with
   C0–C3 stubbed to attribute rows. Do it before C3, not after.
2. **The ih-row spelling in `Gᵢ`** (§3.3): whether `good`'s step reuses
   `wrec`'s `⟨f,r⟩` pair or only `r`, and the exact application depth. A D2
   decision; both spellings derive, one composes with (S4) more cheaply.
3. **`goodrec`/`grec` cache coexistence**: both are `wrec` instances over
   one `Machine`; whether the per-declaration memo (which must store both,
   with certificates, per the standing memo rule) needs a key extension I
   did not verify against the current cache keying in `tg.rs`.
4. **The general recursive §5.3 recursor** (user-defined WF predicate,
   `R ≠ ∅`): **settled** — carrier §6.1, recursor
   `derived/src/inductive/family/le_rec.rs`. Still no corpus witness anywhere,
   tutorials *or* `init-prelude` (§6.2, corrected). Two lemmas fell out that
   neither `acc` nor `rec_acc` had: **A4**, `acc::acc_pred_closed` (an
   `A`-predecessor of an accessible point is accessible), and
   `rec_acc::Bounded` (`accrec`'s values are in `T`, and its own induction
   hypothesis is in `ih_bound(A,T)`). A4 is what keeps `∅ ∈ T` off the
   hypothesis list, which matters because `T` is often a skeleton `W`. What
   remains open is the *step builder*, not the recursor.
5. **`118`'s reduct-lambda bridge** (§6.2): `rec_acc`'s `ih`/`cval` were
   shaped for it, but the wiring from Lean's `λ y h. Acc.rec … (h y h′)`
   nest to `ih(accrec, …)` is unwritten and is the same *kind* of shape that
   made `116` a permanent decline on the W side. If it fails, `118` stays a
   counted gap and nothing else regresses.
6. **Whether `068`'s symbolic-level `RBTree.rec.{u,u}` sites all ground
   through the instantiation pre-pass** — expected (the pre-pass exists for
   exactly this), not checked against `068`'s schedule.
