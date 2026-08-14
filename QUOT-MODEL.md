# The `Sort 0` clause for `Quot` — model analysis

Question: what is the interpretation of `Quot α r` when `α : Prop`, given that the
equivalence-class construction `quot(A,R) ⊆ 𝒫A` cannot land in `⟦Sort 0⟧`?

Sources read for this note: thesis.txt (§2.7.1 at 812–832, §3.1.1 at 1022–1029,
§6.1 at 1905–1935, §6.2 at 2040–2140, §6.3 at 2183–2415), `derived/src/quot/*`,
`derived/src/tower/rungs.rs`, `derived/src/prop/*`, `derived/src/anchor/falsity.rs`,
`kernel/src/thm.rs` (`define` and its choice note), `checker/src/mini/kernel.rs` (`add_quot`),
`checker/src/mini/interp.rs` (`point_of_proof`, `CondSite`/`FibreSite`), `checker/src/mini/ledger.rs`,
`checker/src/instantiations.rs`, `checker/src/mini/zoneb.rs` and `checker/src/tg.rs`
(`provably_nonzero`), MINI-DESIGN.md §6.2–6.4,
LEVEL-POLYMORPHIC-INDUCTIVES.md §2–3.4, INDEXED-DESIGN.md §8.1.

## Verdict

1. The observation is **confirmed**, with one refinement: the classes clause fails at
   `Sort 0` on every *inhabited* proposition (refutably, not just unprovably), and
   accidentally passes on the empty one.
2. The right `Sort 0` clause is the **identity interpretation**:
   `⟦Quot α r⟧ = ⟦α⟧`, `mk` and every proof to `•`, `lift` (into Type) to `⟦f⟧` itself.
   New `derived/` surface: one small lemma. The *wiring* is not free — §2.4.
3. The clause is **forced, not chosen**. Formation, `mk` and `Quot.ind` pin
   `⟦Quot α r⟧ = ⟦α⟧` pointwise, out of soundness invariants the thesis states with
   **no level restriction** (§2.2). The candidate survey of §3 records what that
   rules out; it is no longer what carries the argument.
4. The split is **not a new decision point**: it is the proof-split the interpretation
   already performs at every application, lambda and Π. `provably_nonzero` is the
   **wrong instrument**; the right one is the ground level numeral plus the threaded
   `⊢ ⟦α⟧ ∈ U₀` certificate (the existing `is_prop` witness).
5. The `ℓ > 0` clause is sound as built, but has an unstated sub-case of its own
   (`lift` into `Prop` — the thesis hedges there too, `n′ ≥ 1` at thesis.txt:2359)
   and one genuinely missing seam (the `R̄`-graph conversion). Details in §6.
   *(Corrected in place at `184bde9`: the seam is **built** — `rel_graph` and
   its two bridges, `derived/src/quot/graph.rs` — and its first consumer is
   `Acc`, not `Quot`. `checker/src/mini/acc.rs` names `rel_graph(A,r)` in `Acc`'s
   formation clause, because `derived/src/acc/` reads `⟨y,x⟩ ∈ R` for exactly
   the reason `derived/src/quot/` does. So finding 3 below is a statement about
   two constructions and reads as one.)*
6. **None of this will move a corpus number.** `Declaration::Quot` is given no
   `(declaration, σ)` pairs at all (`checker/src/mini/ledger.rs:289`), so the four
   primitives can be built, stored and used without a single ledger row changing.
   A flat delta is the *expected* outcome of landing the clause, not evidence
   against it. §5 has the measurable consequences, which are downstream.

**Landed at `u = 0`, `6706616`–`89e960e`, and completed at `f2c4b5b`.**
*(`Quot.sound`'s own inhabitation — T8 — is `checker/src/mini/axiom.rs`, at the
declaration pipeline rather than at `zoneb::ensure`, because an axiom has no
constant occurrence to hang a clause off. `constEv` 195 → **197**: both of
`123`'s `u = 0` pairs, since `quotSoundType`'s value is the same constant. The
`u = 0` branch is now closed in full.)* All four primitives interpret;
`constEv` 190 → **195** and `typeEv` 197 → **203**, entirely on the consuming
declarations exactly as item 6 and §5.1 predict. Four corrections to this note,
all marked in place and all found by building: §2.1's "same term" (three of the
four primitives need a β step), T3/T5's "costs nothing" (one congruence each),
T6 (not a lemma — **`u = 0` owes `derived/` nothing at all**), and
`Quot.lift`'s nest depth (five, not six). Every one is a price, not a
mechanism: **the model analysis was right about what the clause is and
consistently one β step optimistic about what it costs.**

---

## 1. The observation is confirmed

### 1.1 `⟦Sort 0⟧` really is the subsets of `1`

Thesis.txt:2040: `U0 = {∅, {•}}` with `• = ∅`; a proposition is interpreted via
`[p] = {x ∈ {•} | p}` (thesis.txt:2057), so `A ∈ U₀ ↔ A ⊆ 1`. The code agrees
exactly: `Tower::u0_members` is `⊢ ∀p. (p ∈ U₀ ↔ (p = 0 ∨ p = 1))`
(`derived/src/tower/rungs.rs:57`), `derived/src/prop/cond.rs` builds every
proposition as `χ = {x ∈ 1 : φ}`, and MINI-DESIGN.md §6.3 fixes `⟦Sort 0⟧ = U₀`
with the `is_prop` witness `⊢ ⟦ty⟧ ∈ U₀`. The question does not dissolve.

### 1.2 The countermodel, in the code's own terms

Take `A = 1 = {•}` (any inhabited proposition), `R` arbitrary. Then, from the
interfaces in `derived/src/quot/`:

- `eqv_refl` (`eqv.rs`) is unconditional in `R`: `⟨•,•⟩ ∈ eqv(1,R)`.
- `class(1,R,•) = {y ∈ 1 : ⟨•,y⟩ ∈ eqv} = {•} = 1` (`class_self` + `class_subset`).
- `quot(1,R) = {c ∈ 𝒫1 : ∃x.(x ∈ 1 ∧ c = class(1,R,x))} = {1}` (`quot_symbol`).

And `{1} ∉ U₀` is **refutable**, not merely unprovable: by `u0_members`, membership
would force `{1} = 0` (false: `1 ∈ {1}`) or `{1} = 1 = {0}` (forces `1 = 0`,
refuted by `u0_two_valued`, `rungs.rs:63`). So a wiring that used the classes
clause at `Sort 0` would face a formation obligation `⊢ quot(A,R) ∈ U₀` whose
negation is a theorem. The failure mode is a permanent gap, not unsoundness — the
kernel cannot certify a false membership — but the clause is dead on arrival.

A second, independent way to see it cannot be rescued: the classes construction
lives inside `𝒫A`, and **rung 0 is not power-set closed** — `Tower::at`'s own
comment (`rungs.rs:303`): `𝒫{0} = {0,1} = U₀ ∉ U₀`. `pow` (`rungs.rs:84`) is a
closure of `U(x)`, i.e. of rungs ≥ 1 only. Nothing `⊆ 𝒫A`-shaped can be placed in
`U₀` by the tower's theorems, for any `A` at all.

### 1.3 The failure is not pointwise universal — it spares the empty proposition

At `A = 0`: `quot(0,R) = {c ∈ 𝒫∅ : ∃x.(x ∈ ∅ ∧ …)} = ∅ = 0 ∈ U₀`. So "the classes
clause lands outside `⟦Sort 0⟧` exactly when Lean says it should land inside" is a
fair indictment but overstates pointwise: the clause fails on every **inhabited**
`Prop` and accidentally passes on the empty one. Since `Quot.mk` and the ι-rule
only ever fire on inhabited quotients, the failure covers every case that matters
— it passes precisely where nothing can use it.

### 1.4 What the thesis actually says (it hedges, knowingly)

The thesis's interpretation clause is stated uniformly (`⟦α/R⟧ = ⟦α⟧/∼`,
thesis.txt:2132) but its **soundness case is proved only for `n ≥ 1`**:
"Suppose `Γ ⊢ α : Un` with `n ≥ 1`" (thesis.txt:2353), and `lift`'s target is
likewise assumed `n′ ≥ 1` (thesis.txt:2359). Meanwhile §3.1.1 (thesis.txt:1022–1029)
explicitly admits prop-level quotients exist in Lean — it builds its second
non-transitivity example out of exactly `p : P`, `R : p → p → P`, `lift` into
`α : U₁`. So the thesis **has no `Sort 0` quotient clause**; the `n ≥ 1` hypothesis
is a silent gap, and what follows is an extension, not a reading — though, as §2.2
shows, an extension with no latitude in it. The construction below is nonetheless
anticipated by the thesis's own remark at thesis.txt:828–830:

> "the other constants and the computational rule would all be satisfied with the
> definitions `α/R := α`, `mkR a := a`, `liftR f h := f`" — everything but `sound`.

The remark says the identity reading is *available* at `Sort 0`, because the one
thing it fails in general comes free there: `⟦mkR a⟧ = •` by Theorem 6.7 part 2
whatever the quotient is, so `sound`'s obligation is `• ∈ [• = •]` and closes by
reflexivity.

That is a necessary condition and **not** the reason to take the clause. `sound`
is free at `Sort 0` for *every* candidate in §3, A and C included, so it selects
nothing. What selects the clause is `mk`'s typing and `Quot.ind`, and between them
they leave no choice at all — §2.2.

## 2. The right `Sort 0` clause: the identity interpretation

### 2.1 The clause

Given the certificates the checker already threads — `Γ ⊢ A ∈ U₀` for `A := ⟦α⟧`
(the `is_prop` witness of `α`, MINI-DESIGN.md §6.3) — define, at ground level
`u = 0`:

```text
⟦Quot α r⟧γ        := ⟦α⟧γ                          (r is not consulted)
⟦Quot.mk r a⟧γ     := •     (it is a proof; forced by the proof-split, §4.1)
⟦Quot.lift β f h⟧γ := ⟦f⟧γ  when lvl(β) ≥ 1
                   := •     when lvl(β) = 0   (the whole lift is a proof)
⟦Quot.ind β h⟧γ    := •     (its result ∀q, β q is a Prop)
⟦Quot.sound …⟧γ    := •     (as at every level)
```

`⟦Quot α r⟧` and `⟦α⟧` are the *same term*, not merely provably equal sets.

*(**Corrected in place at `89e960e`, against the built clause.** That sentence
is true of the *clause* and false of what `infer_type` hands back. §6.2's
application clause gives `⟦Quot α r⟧` as `app(app(⟦Quot.{0}⟧,⟦α⟧),⟦r⟧)` — a
redex over the stored λ-graph, related to `⟦α⟧` by **β** and not by syntax. So
a consumer expecting `point_of_proof` or a membership comparison to apply
directly is wrong by exactly one `beta_spine` down the formation clause's own
nest, and that step appears in **three** of the four primitives:
`mk` (carrying `⟦a⟧ ∈ ⟦α⟧` onto `⟦Quot α r⟧`), `ind` (carrying `q` the other
way, so that `h` applies at it), and `lift` (below).*

*The domain-slot argument of the next paragraph is unaffected, and it is the
one that carries T3 and T5.)*

**The conflation is harmless**, and for a reason worth stating exactly: mini's
*acceptance* is nanoda's algorithm on `Expr`, decided upstream of and
independently of `⟦·⟧`, and the interpretation only ever produces evidence *for*
an already-accepted step. `Gap::NoEndpoint`'s own documentation names `is_def_eq`,
the shape zone and the `whnf` inside a K-rule check as "acceptance-only calls
whose results have no evidence consumer at all". So no conversion theorem is ever
consulted to decide a definitional equality, and the model is free to identify
types Lean keeps distinct. It already does: `⟦True⟧` and `⟦0 = 0⟧` are the same
term in shipped code.

**The conflation is also the mechanism, not just a tolerated side effect.** Mini
keys its Π machinery on the *body* shape and passes the domain as an argument —
`conds: HashMap<Term, CondSite>` builds `chi(h⃗, A)` and `fibres: HashMap<Term,
FibreSite>` builds `dprod(h⃗, A)`. **Two** mechanisms, not three: the
non-dependent arrow used to build `fs(A, B)` through a clause of its own, and
that clause was retired (`SCOPING.md` §10) — a binder-free codomain is hole 0
entire, so it is `dprod` at the *constant* fibre, one `fibres` entry
corpus-wide. The domain therefore occupies an argument slot of a **shared**
symbol rather than being baked into a freshly minted one, and now does so under
one mechanism fewer. So
`⟦α → β⟧` and `⟦Quot α r → β⟧` are not two conditional singletons that happen to
be provably equal — under this clause they are **literally the same term**, at
both `v ≥ 1` and `v = 0`. That single fact is what makes T3 and T5 below cost
nothing, and it is the load-bearing implementation property of the whole clause.

**The invariant it rests on, stated so it is not merely incidental.** The reverse
tables `cond_by_sym` / `fibre_by_sym` exist so that `whnf` and `assert_def_eq` can
recover `⟦A⟧` and `⟦B⟧` from `⟦Π x:A. B⟧`. Under this clause that recovery cannot
distinguish `α` from `Quot α r` — correctly, since they are the same term. That is
safe today because every clause dispatches on the `Expr`, never on the
interpretation's head symbol. **It becomes a defect the moment any clause keys
decomposition on the interpretation's head symbol**, and a clause that wants to do
so must be checked against this one first.

*(Checked once, at the `fs`-clause removal, and this is what the check looked
like. `Interp::as_pi` **does** key on head symbol, and after the change a
constant-fibre `dprod` and a genuine dependent one both land in its `Dep` arm —
distinguished by which fibre symbol, which is exactly what `fibre_by_sym` is
for. No new conflation. The change also removed `PiShape::Fs` rather than
leaving it unreachable, and this paragraph is the reason: `derived::fs` stays in
the library, so a stray library function space would have gone on decomposing as
an interpreted `Π` for as long as the variant existed. The invariant is easier
to state with one clause fewer, not harder.)*

### 2.2 The clause is forced, not chosen

The identity reading is not the best of the candidates in §3. It is the **only**
value `⟦Quot α r⟧` can take at `u = 0`, pinned pointwise in `(A, R)` by three
parts of Theorem 6.7 — all of which the thesis states and proves **without any
level restriction**, unlike the quotient case at thesis.txt:2353. Write
`Q := ⟦Quot α r⟧` and `A := ⟦α⟧`.

**Formation bounds it to two values.** `Quot α r : Sort 0`, so Theorem 6.7 part 1
(`Γ ⊢ α : P ⟹ ⟦α⟧ ⊆ {•}`) gives `Q ⊆ 1`, and `u0_members` sharpens that to
`Q = 0 ∨ Q = 1`. No other value is admissible for any clause whatever.

**`mk` forces `Q = 1` when `A = 1`.** `Quot.mk r a` inhabits a `Sort 0` type, so
Theorem 6.7 part 2 forces `⟦mk r a⟧ = •` *whatever set `Q` is* — this is the same
observation §4.1 makes, used here as a constraint rather than as a convenience.
Part 3 then requires `⟦mk r a⟧ ∈ Q`, i.e. `• ∈ Q`. `Quot.mk`'s own typing
obligation carries the hypothesis `a ∈ A`, which with `A ⊆ 1` gives `A = 1`. So
`Q(1,R) = 1`.

**`Quot.ind` forces `Q = 0` when `A = 0`.** At `A = 0` the minor premise
`∀a. (a ∈ A → …)` is vacuous, so a `Q = 1` would have to yield
`• ∈ app(β̄, •)` from nothing — and `β̄` is universally quantified over
`fs(Q, U₀)`, so it may be the constant-`0` function `{⟨•,0⟩}`, making the
obligation `• ∈ 0`. That is **refutable**, not merely underivable, by
`falsity::false_uninhabited`. So `Q(0,R) = 0`.

Hence `Q = A` at both admissible values, with no residual freedom and no
dependence on `r`: **`⟦Quot α r⟧ = ⟦α⟧` is the unique completion of the thesis's
interpretation that is consistent with its own soundness theorem.** Both ends meet
the "refutable, not merely unprovable" standard the rest of this note holds itself
to — the same standard §1.2 applies to the classes clause and §4.3 applies to the
identity clause at `u ≥ 1`.

Two things follow. First, §3's candidate survey is a record of what is ruled out,
not the argument; nothing downstream depends on its exhaustiveness. Second, the one
genuinely new lemma this note asks for (T6) is exactly the one that *earns* the
downward half: `Quot.ind` is both the obligation that costs the most and the
obligation that pins `Q` at the empty proposition.

### 2.3 The exact obligations, and what discharges each

Writing `B := ⟦β⟧`, `f̄ := ⟦f⟧`, `[φ]` for the conditional singleton, `fs` for the
function space, obligations per primitive at `u = 0`:

| # | obligation | discharged by |
|---|---|---|
| T1 | formation: `Γ ⊢ ⟦Quot α r⟧ ∈ U₀` | is literally the threaded witness `Γ ⊢ A ∈ U₀`; zero new theorems |
| T2 | `mk` typing: `Γ ⊢ • ∈ A` | from `Γ ⊢ ⟦a⟧ ∈ A` via `falsity::prop_subsingleton` — this is `mini::interp::point_of_proof` (interp.rs:591), unchanged |
| T3 | `lift` typing, `v ≥ 1`: `Γ ⊢ f̄ ∈ dprod₀(B, A)` | `f`'s own typing certificate **plus one congruence** — `dprod₀(B,A)` and `dprod₀(B,⟦Quot α r⟧)` are *not* the same term, because the domain argument is `⟦α⟧` on one side and the redex on the other. The domain-slot property is what makes the repair **one** `congr_arg` in the `Π` symbol's last argument rather than a rebuild, so §2.1's mechanism carries T3 exactly as claimed; what was wrong is "costs nothing". Same two steps as T2, at the `Π` symbol instead of at the membership. *(Corrected at `89e960e`, measured. Also: the arrow is `dprod` at the constant fibre since `SCOPING.md` §10, where this was spelled `fs(A,B)`.)* And it discharges the **bottom** of a nest, not the obligation entire: see below |
| T4 | ι, `v ≥ 1`: `Γ ⊢ ⟦Quot.lift α r β f h (Quot.mk α r a)⟧ = ⟦f a⟧` | descend the five-deep `beta_spine` on the stored λ-nest to reach `app(f̄, ⟦Quot.mk r a⟧)`, then two `Thm::eq_leibniz` steps along `⟦mk…⟧ = •` and `⟦a⟧ = •` (both from `point_of_proof`); app-congruence is one Leibniz instance at `φ(x) := app(f̄,⟦a⟧) = app(f̄,x)` |
| T5 | `lift` typing, `v = 0`: `Γ ⊢ • ∈ [∀x ∈ A → • ∈ B]` | `f`'s own certificate **plus the same congruence as T3** — `chi(h⃗,⟦α⟧)` and `chi(h⃗,⟦Quot α r⟧)` share the symbol and the holes and differ in the domain argument. `CondSite` taking the domain as an argument is what keeps it one step (§2.1). ι at `v = 0` is proof irrelevance, and `124_quotLiftReduction` closes on it |
| T6 | `ind` typing: `Γ ⊢ • ∈ app(ḡ, q)` at the nest's own `q` | **not a lemma, and `derived/` owes nothing.** *(Corrected at `0f17034`, built.)* At a nest bottom the quantifier is never introduced, because `q` is this nest's own binder: it inhabits `⟦Quot α r⟧`, which β-reduces to `⟦α⟧`, so **`q` is its own witness** for `h : ∀a:α, β (mk a)` and no `a` is produced; and `⟦mk a⟧` is `•` at *every* `a`, so `h`'s fibre does not mention its binder and the application lands on `app(ḡ,•)` whatever it is applied at. One Leibniz along `• = ⟦q⟧` finishes. The quantified form below is the right shape only for a consumer holding an arbitrary `q` |
| T7 | `ind` ι (`ind β h (mk r a) ≡ h a`, the rule at checker/src/mini/kernel.rs:2564) | both sides are proofs: `point_of_proof` on each side, `trans`/`symm`. **Not a `u = 0` obligation** — see below |
| T8 | `sound` typing: `Γ ⊢ • ∈ [t₁ = t₂]` where `t₁ = ⟦mk a⟧`, `t₂ = ⟦mk b⟧` | both provably `•`: `eq_refl`, Leibniz, `cond_intro`. `r a b` is never consulted — `sound` is *free* at `Sort 0`, because `A` is a subsingleton |

**T7 is uniform in `u`, not a `Sort 0` obligation.** `Quot.ind`'s motive is
hardwired `β : Quot α r → Prop` in `add_quot` (`checker/src/mini/kernel.rs`), and its
level parameter list is `[u]` alone — there is no `v`. So both sides of its
ι-rule are proofs at **every** `u`, and the derivation above is the whole of it at
every level. It is tabulated here for locality; it is not part of what the `u = 0`
branch owes.

**Total new `derived/` surface: none.** *(Corrected at `0f17034`. This read
"T6, one lemma"; the lemma is not needed at a nest bottom — see T6's row. The
statement below is still the right one for a consumer holding an arbitrary `q`,
and no consumer does.)* The statement it would have been:

```text
⊢ ∀A ∀g. ((A ∈ U₀ ∧ • ∈ app(g,•)) → ∀q. (q ∈ A → • ∈ app(g,q)))
```

or its curried per-certificate form. Note it does **not** need `g ∈ fs(A,U₀)`: the
proof is `u0_subsingleton` to get `q = •`, then one Leibniz, and neither step asks
what `g` is. Nothing from `derived/src/quot/` is used at `u = 0` at all — no `eqv`,
no `class`, no Replacement, no funspace lift, and `r`'s graph need not even be
constructed.

### 2.4 What the one lemma does not cover — the wiring

The `derived/` surface really is one lemma, and every cost claim in this note is a
claim about `derived/` only. The **wiring** is not free, and two rows of the table
above compress it, so they are spelled out here.

*The obligation is on the constant, and the constant is a nest.* `⟦Quot.lift.{u,v}⟧`
is a five-deep λ-graph nest `λA λr λB λf λh. f`, not `f` — **five and not six**,
though the declared type has six binders: the sixth is the major `q`, and the
clause's codomain is the *arrow* `Quot α r → β`. A six-deep nest is this one
η-expanded, its bottom is `app(f̄,⟦q⟧)`, and T3 has nothing to say about it. The
first build used six and declined (`89e960e`); `⟦Quot.{u}⟧` is
`λA λr. A`; `⟦Quot.mk.{u}⟧` is `λA λr λa. •`. What each certificate in the table
discharges is the nest's **bottom**. The nest itself is built by `lam_nest`, one λ
rule per level, exactly as the inductive type former is.

*The ι-rule reaches that bottom through a spine.* T4's redex is
`Quot.lift α r β f h (Quot.mk α r a)`, so the left-hand side must first descend
five levels of `Interp::beta_spine` — each step consuming the corresponding
argument's own typing certificate — before the two Leibniz steps apply. All five
certificates are in hand at a redex that typechecked, and `beta_spine` is the same
mechanism the inductive constructors already use, so this is precedented work
rather than new work. It is not, however, zero.

This is worth naming because it is a recurring failure mode in this project's
design notes, not a one-off: `042`'s indexed-family obligation was read the same
way, as a statement about a carrier when it was in fact a statement about an
`np + ni`-deep type-former nest whose bottom the carrier theorem discharges. A
cost claim about `derived/` and a cost claim about the landing are different
claims, and this note makes only the first.

### 2.5 `Quot.lift` out of a `Prop` quotient into `Type` is real, and costs nothing

Checked against the primitive types as ported verbatim in `checker/src/mini/kernel.rs`
(`add_quot`, lines 2496–2523): `Quot : ∀(α : Sort u), (α → α → Prop) → Sort u` and
`Quot.lift` carries an independent `sort_v` for `β`. Nothing ties `v` to `u`;
`u = 0, v = 1` typechecks, and thesis §3.1.1 exhibits precisely that instance —
it is Lean's second source of algorithmic non-transitivity ("lift acts like a
subsingleton eliminator in this case", thesis.txt:1024).

Under the identity clause this large elimination is free: `⟦Quot α r⟧ = A` and
`f̄ ∈ fs(A,B)` **is already** a function on the quotient, because the quotient *is*
the domain. This is worth stating as the design reason and not just a convenience:
any clause that moved `⟦Quot α r⟧` "away" from `A` (e.g. `{1}`) would need a
definable section back to representatives to build `lift`'s function — which is
where a choice operator would sneak in (§3.2). The identity clause is the unique
reading in which `lift` into `Type` requires no new function at all.

(On the non-transitivity itself: not our problem. The checker follows Lean's
algorithmic acceptance and certifies only what is accepted; the model validates
all of `≡`, so every accepted chain — including `lift f H q ≡ f h` via proof
irrelevance `q ≡ mk h` followed by ι — certifies through `point_of_proof` + T4.)

## 3. The candidate survey — a record of what is ruled out

**Commentary, not argument.** §2.2 settles the `Sort 0` value pointwise, so
nothing below is load-bearing and in particular no exhaustiveness claim has to
carry weight. The section is kept because knowing *why* each alternative fails is
what stops it being proposed again, and because §3.2's obstruction is the one the
original question asked to be specific about.

### 3.1 Candidate A: literal equivalence classes at both ends — **refuted**

§1.2. `quot(1,R) = {1} ∉ U₀`, refutably. Also blocked wholesale by rung 0's lack
of power-set closure. No repair inside `𝒫A` exists: the formation target `U₀`
contains only `0` and `1`, and `quot(A,R)` for inhabited `A` is always a nonempty
*set of subsets*, which is neither: it is not `0` because it has a member, and not
`1 = {∅}` because that member — a class, which contains its own representative —
is not `∅`.

### 3.2 Candidate B: canonical representatives via choice — mathematically uniform, **foundationally closed off**

Define `quotε(A,R) := {ε([x]∼) : x ∈ A} ⊆ A`, `mkε(x) := ε([x]∼)`,
`liftε(f) := f` restricted to `quotε`. This *is* level-uniform: `quotε ⊆ A`, so
`A ∈ U₀ → quotε ∈ U₀` (subsets of `1` are `0` or `1`) and `A ∈ Uₙ → quotε ∈ Uₙ`
(`Tower::sub`, no power set needed); `mk` is a section of the class map, so a
class is recoverable from its representative (`[ε([x])] = [x]`) and `lift` is
well defined; the ι-rule `f(ε([a])) = f(a)` holds by `compat`. It is the thesis's
own `ε` (thesis.txt:2043–2044, fixed on `Uω`) used one level deeper.

It is unavailable here, and the kernel documents why with unusual precision:
`kernel::thm::define` (kernel/src/thm.rs:1358) demands `⊢ ∀x⃗ ∃!y. φ` — a choice
function is never unique, so `ε` cannot be minted; and the long comment above
`define` (thm.rs:1326–1338) proves the sharper point that a Skolemising
`define_choice` at arity ≥ 1 would be a **genuine unsoundness** in this kernel,
because `ax_replacement` accepts arbitrary formulas and a Skolem symbol is
conservative but not eliminable — a model expanded by an arbitrary choice
function need not satisfy Replacement for formulas mentioning it. `ax_choice`
exists only in existential form (`derived/src/choice/function.rs`), and an
existentially bound `f` cannot appear in the closed terms the interpretation must
produce.

**The escape hatch the kernel offers does not reach this.** That same comment
names a *safe* replacement for Skolemisation — a **0-ary Henkin constant**: from
`⊢ ∃y. φ` with `FV(φ) ⊆ {y}`, mint a fresh constant `c` and conclude `⊢ φ(c)`,
which is conservative including the schemes because a constant is a parameter. A
reader who follows the kernel's own recommendation lands here, so the section must
say why it does not help, and there are two independent reasons.

*The side condition fails.* `⟦Quot.{u}⟧` is a λ-nest `λA λr. …` over free
variables — that is what an interpretation of a *constant* is — so the `∃`
statement a representative-picker would need is open in `A` and `R`, and
`FV(φ) ⊆ {y}` does not hold. Getting a closed `φ` means fixing `A` and `R`, i.e.
arity ≥ 1 in disguise.

*And fixing them is worse than useless.* Minting one Henkin constant per use site,
at that site's closed `A` and `R`, would make `⟦Quot α r⟧` not a function of
`(α, r)` — the interpretation would stop being a function on the constant. That is
not a hypothetical: it is the recorded failure that cost 54 ι sites when
`ind_abbrev` re-minted `⟦List⟧` over a second stack's incompatible sets
(`INDEXED-DESIGN.md` §8.1 note 1). Memoising it back into a function is precisely
re-deriving the arity-≥-1 symbol the kernel refuses to mint.

So the one mathematically uniform definition is ruled out by the foundation, on
purpose, for reasons that are correct, and the sanctioned weakening does not
recover it. This is the obstruction the question asked to be specific about.

### 3.3 Candidate C: one symbol with an internal case split — definable, **pointless**

A single Separation does exist:

```text
Q(A,R) := { c ∈ 𝒫A : (A ⊆ 1 ∧ c ∈ A) ∨ (¬(A ⊆ 1) ∧ ∃x.(x ∈ A ∧ c = class(A,R,x))) }
```

(well-bounded because `A ⊆ 1 → A ⊆ 𝒫A`: the only possible element `∅` is a subset
of everything). With LEM — the kernel is classical — one proves `A ⊆ 1 → Q = A`
and `¬(A ⊆ 1) → Q = quot(A,R)`, and every export can be stated once. But this is
a case split *moved into a formula*, not removed: every proof does the LEM
analysis, `mk` and `lift` need their own `∃!`-by-cases definitions, and — the
decisive point — **it cannot make the checker uniform**, because of §4.1 below:
the ambient proof-split already forces `⟦Quot.mk r a⟧ = •`-up-to-equality at
`u = 0` no matter what set `Q(A,R)` is. The symbol-level uniformity would be
cosmetic, purchased with strictly more theorems than the two-branch reading.

A side effect worth noting, and worth stating precisely because the loose version
of it is false: `Q` would also give `Type`-level quotients of subsingleton
carriers (`A = 1 ∈ U₁`, PUnit-shaped) the identity reading rather than `{1}`. The
discriminant `A ⊆ 1` cannot see the level, and `1 ∈ U₀ ∩ U₁` by cumulativity, so
*the same set arrives at both ends and must receive one value*. What that shows is
**not** that the two ends demand different values — nothing demands `{1}` at
`A = 1, ℓ = 1`; the identity reading there is sound and every obligation
discharges. It shows only that a uniform-in-`(A,R)` clause must give up **literal
agreement with the classes construction** on subsingleton `Type`s. Cumulativity
therefore does not refute Candidate C. What disposes of it is the paragraph above
— the split is already paid for at `⟦Quot.mk r a⟧` whatever `Q` is — and, since
§2.2, the fact that there is nothing left for a uniform clause to be uniform
*about*: the `Sort 0` value is pinned regardless.

### 3.4 Why no fourth candidate is worth looking for

A heuristic, and explicitly not a proof — exhaustiveness claims are where a gap
would hide, and §2.2 is what makes it safe not to need one. The argument surveys
the shape of the space rather than closing it.

A uniform clause would need a ZF-definable (choice-free, case-free) `Q, mk` with:
`mk` collapsing exactly `∼` (forced: `lift` must be single-valued for every
compatible `f`, and at `R = ∅` every `f` is compatible — `witness::compat_at_empty`
— so `mk` must be injective there), and `Q ⊆ 1` whenever `A ⊆ 1` (forced by
formation). On subsingletons `mk` must be the identity-up-to-`•`; on `A = 2` with
`R = ∅`, `mk` must be injective into a two-element `Q`. A definable operation
that is a retraction-free quotient on one side and the identity on the other,
with no case discrimination and no choice, would in particular pick canonical
representatives definably at every `A` where classes are non-trivial — which is
Candidate B without `ε`. First-order definability always permits the disjunction
(Candidate C), so "uniform" in any sense stronger than C means choice, and choice
is closed (§3.2). Nothing in the space surveyed here survives; and if something
did, §2.2 would still fix its value at `Sort 0`, which is the only place the
question was ever open.

## 4. The split, and what decides it

### 4.1 The split already exists; `Quot` adds no new decision point

The interpretation is globally split at `ℓ = 0` before quotients enter: the
proof-split language (thesis §6.1, thesis.txt:1985–2005) translates every
application, lambda and binder differently at `sort = 0` vs `≥ 1`, and Theorem
6.7 part 2 (thesis.txt:2186) makes "every proof interprets to `•`" a soundness
invariant. Mini implements exactly this: proof-valued applications and lambdas
go to `•`, every proof is certified `= •` via `prop_subsingleton`
(`point_of_proof`, MINI-DESIGN.md §6.4 clause 1), and Π splits into
`dprod` vs `cond` on the `is_prop` witness (§6.2). `Quot.mk r a` at `u = 0` *is a
proof*; its interpretation is forced to `•` by this invariant regardless of any
choice made for `⟦Quot α r⟧`. So the quotient clause cannot be more uniform than
the application clause, and the case split recommended here is an instance of a
split the design has already paid for.

### 4.2 `provably_nonzero` is the wrong instrument

`provably_nonzero` (`mini::zoneb`, `checker/src/tg.rs`) answers a different
question: it is half of the **per-declaration** translation branch, asked on the
declaration's own level *expression* (params included), because Lean's
eliminator trichotomy (thesis §2.6.2; LEVEL-POLYMORPHIC-INDUCTIVES.md §2) is
per-declaration — `PUnit.{u}` has one recursor and must take one branch at every
`u`. (In `mini` it is the *second* half: `zoneb::subsingleton` is asked first,
and `provably_nonzero` decides only what a non-subsingleton gets. That does not
change anything below.) Applied to `Quot.{u}`, whose own resultant level is a
bare `Param u`, it answers `false`, which would force the `Prop` reading (or a
decline) at every instantiation, including `Type` ones — exactly wrong.

And the per-declaration rule's *rationale* does not reach `Quot`: `Quot` is not
an inductive, has no recursor and no trichotomy — `Quot.lift` is large-eliminating
at **every** `u`, including `u = 0` (that is the §3.1.1 behaviour). Unlike
`PUnit`, `Quot` at `Type` levels has real structure, and at `Sort 0` its value is
pinned to `⟦α⟧` by §2.2, so no single carrier can serve all `u`; and
LEVEL-POLYMORPHIC-INDUCTIVES.md §3.1 establishes that per-ground-instantiation
interpretations are sound by themselves — nothing ever compares `⟦c.{0}⟧` with
`⟦c.{1}⟧`, levels being ground per check. The interpretation of `Sort` itself is
already per-numeral.

### 4.3 What actually decides, and the evidence

At interpretation time the store key is `(name, ground levels)` (zoneb `ensure`),
so `u` is a numeral. The branch is decided by `u = 0` vs `u = n+1` — a syntactic
fact about a ground numeral, like the `sort/sort` clause — and the house rule's
*evidence* obligation is met per branch by the certificate each branch consumes:

- `u = 0`: the threaded `Γ ⊢ ⟦α⟧ ∈ U₀` — the `is_prop` witness, which is "the
  inference's own certificate, un-discarded" (MINI-DESIGN.md §6.3). Every theorem
  in §2.3 takes it as a premise, so a branch entered wrongly cannot derive
  anything: the evidence is consumed, not re-discovered.
- `u = n+1`: the threaded `Γ ⊢ ⟦α⟧ ∈ U₍ₙ₊₁₎`, same provenance, consumed by the
  formation theorem (§6.1 below) and by `lift_in_funspace`'s premises.

No new predicate, no search. The precedent is the Π clause, which branches the
same way on the same witness. Neither branch subsumes the other, and both
mis-uses are *refutable*, which is the strongest possible justification for a
split: the classes clause at `u = 0` hits `⊢ ¬({1} ∈ U₀)` (§1.2), and the
identity clause at `u ≥ 1` hits `sound`'s obligation `• ∈ [ā = b̄]` for genuinely
distinct related elements — e.g. `A = 2`, `R = {⟨0,1⟩}`, where `[0 = 1]` is
refutable by `u0_two_valued`. One more reason the numeral, not a subsumption
argument, must decide.

`Quot.lift` and `Quot.ind` carry a **second** split on `v` (the motive/target
level): `v = 0` routes to the proof-split (`lift` is itself a proof — §2.3 T5,
§6.2 below), `v ≥ 1` to the set-level function. Same instrument: `v` is ground,
the evidence is `β`'s own sort certificate. This split exists at every `u`, and
the thesis's `n′ ≥ 1` hedge at thesis.txt:2359 is its shadow. It is a split on
`lift` alone: `Quot.ind` has no `v` (§2.3, T7).

## 5. Statement of the recommended design

- **Two clauses, decided by the ground numeral `u`, evidenced by the threaded
  rung-membership certificate of `α`.**
- `u = 0`: identity interpretation — **forced by §2.2, not selected** — obligations
  T1–T8 of §2.3; new `derived/` surface **none**, and
  `derived/src/quot/` is not touched at `u = 0`. *(This bullet said "≈ one
  composed lemma (T6), suggested home `derived/src/prop/`". §2.3's own T6 row was
  corrected in place to "not a lemma, and `derived/` owes nothing", and its total
  line to "Total new `derived/` surface: none"; this bullet was not corrected with
  it. No such lemma exists in `derived/src/prop/` and none is owed.)*
- `u ≥ 1`: the existing `derived/src/quot/` classes construction, unchanged,
  plus the missing formation theorem (§6.1).
- The feared doubling of claims does not materialise: the `u = 0` branch's
  "theorems" are almost entirely re-labelings of certificates the checker already
  holds, because `⟦Quot α r⟧ = ⟦α⟧` makes the relevant statements syntactically
  identical (§2.1). The *wiring* is a separate cost and §2.4 states it.

### 5.1 How to tell whether it landed — not by the corpus number

**Landing the clause will not move any ledger row, and a flat delta must not be
read as the clause failing.** `checker/src/mini/ledger.rs:289` gives `Declaration::Quot`
no `(declaration, σ)` pairs at all — the four primitives are counted as
declarations with no interpretable content and `continue`d, exactly as inductives
are. So `⟦Quot⟧`, `⟦Quot.mk⟧`, `⟦Quot.lift⟧` and `⟦Quot.ind⟧` can be built,
stored and used with every corpus number unchanged.

What moves is **downstream**, on the declarations that *consume* them, and it is
measurable there. Measured on `123_quotSoundType`: `pairs=4`, of which
`interpretation-scope=2` (`waiting:no-interp(Quot)`) and `model-assumption=2`
(`waiting:axiom(Quot.sound)`). Only two declarations in that file bear pairs —
`Quot.sound` and `quotSoundType` — so each carries two instantiations:
`quotSoundType` is demanded by nothing and takes `DEFAULT_LEVELS = [0,1]`
(`checker/src/instantiations.rs:117`), and `Quot.sound` inherits `{0}` and `{1}`
through the demand fixpoint from `quotSoundType`'s value. Those four pairs are the
acceptance test for this clause; the `Quot` primitives themselves stay silent.

So `123` exercises **both** branches, and cannot close on either clause alone.

## 6. Sanity check of the `ℓ > 0` clause

Sound as far as it goes; five findings, in decreasing order of substance.

1. **The formation theorem is missing (known) and rung 1 supports it (checked).**
   `quot.rs`'s "What is not here" records `quot(A,R) ∈ U(c)` as underived. The
   route exists at every rung ≥ 1 including `Sort 0`'s neighbour: `quot_ax`'s
   `c ∈ 𝒫A` conjunct gives `quot(A,R) ⊆ 𝒫A`; `Tower::pow` (`rungs.rs:84`,
   stated for `U(x)`, i.e. all rungs ≥ 1) gives `𝒫A ∈ Uₙ`; `Tower::sub`
   (`rungs.rs:73`) closes: `⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))`. Note the
   code's single power set is *tighter* than the thesis's "double powerset of ᾱ"
   (thesis.txt:2355) — classes are subsets of `A`, so one `𝒫` suffices; no issue,
   just a coarse bound in the thesis.
2. **`lift` into `Prop` (`u ≥ 1, v = 0`) must bypass the funspace lift.** The
   thesis assumes `n′ ≥ 1` in its `lift` case (thesis.txt:2359); at `v = 0` the
   whole of `lift β f h` is a proof and `f` is one too, so there is no
   `f ∈ fs(A,B)` certificate to feed `lift_in_funspace` — a wiring that tried
   would gap, not err. The needed fact is per-element rather than global: given
   `q ∈ quot(A,R̄)`, `quot_cases` (`classes.rs`) yields
   `∃x. (x ∈ A ∧ q = class(A,R̄,x))`, `f`'s conditional-singleton certificate at
   that `x` yields `• ∈ B̄`, and the existential discharges. No `compat` is needed
   (proof irrelevance covers the ι-rule). The `v`-branch is decided as in §4.3.
   That `n′ ≥ 1` is, on inspection, a hedge about the thesis's *own* construction
   — it builds a function `F : ᾱ/∼ → β̄`, and so needs a function space — rather
   than about a mathematical difficulty. It does not transfer, and this sub-case
   should not inherit doubt from it.
3. **The `R̄`-graph seam** — *built, `derived/src/quot/graph.rs`, as
   `rel_graph` with its two bridge lemmas. The Verdict block at the top of this
   file was corrected when that landed; this finding's body was not, so it read
   "genuinely unbuilt" and "exist nowhere yet" long after both. Its first
   consumer was `Acc`, not `Quot`; `checker/src/mini/quot_classes.rs` is the second. The
   finding as written is below, and it is right about everything except the
   existence.*

   Lean's `r` interprets as a
   curried function `⟦r⟧ ∈ fs(A, fs(A, U₀))`; every theorem in `derived/src/quot/`
   takes `R` as a **set of pairs** (`⟨x,y⟩ ∈ R` in `eqv_incl`, `q_sound`,
   `rcompat`). The conversion
   `rel_graph(A,r) := {p ∈ A² : ∀u∀v. (p = ⟨u,v⟩ → • ∈ app(app(r,u),v))}`
   (one Separation, the `∀`-form for the same reasons as `ker`) and its two
   bridge lemmas — membership of `⟨x,y⟩` from `• ∈ app(app(r,x),y)` and back —
   exist nowhere yet, and `Quot.sound`'s and `Quot.lift`'s wiring both consume
   them (the `h`-certificate arrives in `app(app(r,·),·)` form and must become
   `rcompat`). This is plumbing, not model error, but it is the actual untested
   edge of the `ℓ > 0` clause: every quotient theorem is currently exercised only
   against a pair-set `R` that no Lean-side term yet produces.
4. **Threading for the ι-rule closes properly.** `lift_beta`'s antecedents
   (`compat ∧ x ∈ A`) are dischargeable from certificates the checker holds at
   the redex: `x ∈ A` from the constructor argument's typing, `compat` from
   `h`'s typing certificate via `compat_closure` (through finding 3's bridge).
   Lean's kernel fires the reduction without inspecting `h`; ours needs `h`'s
   typing, which is always available since the redex typechecked. "On the nose"
   in this kernel means an unconditional equation theorem per instance, which is
   what `lift_beta` yields after its antecedents are cut — consistent with how
   every other ι-rule is stored (MINI-DESIGN.md §6.4). Subsingleton carriers at
   `Type` level (`A = 1 ∈ U₁`) are unproblematic for the classes clause:
   `quot(1,R) = {1} ∈ U₁` by finding 1's theorem, and `lift`'s graph is the
   one-pair set; no edge there.
5. **`Quot.ind`'s typing at `ℓ > 0` is an obligation of its own, and findings 1–4
   do not cover it.** `Quot.ind` is the primitive that falls between the two
   splits: its motive is hardwired `→ Prop`, so it has no `v` to branch on, while
   its major premise ranges over a genuine `quot(A,R̄)`, so it is not reached by
   the `u = 0` clause either. The obligation is
   `• ∈ [∀q. q ∈ quot(A,R̄) → • ∈ app(β̄,q)]` from
   `• ∈ [∀a. a ∈ A → • ∈ app(β̄, class(A,R̄,a))]`, and it discharges by the same
   move as finding 2: `quot_cases` to get `q = class(A,R̄,x)` for some `x ∈ A`,
   the hypothesis at that `x`, then Leibniz along the equation. The technique is
   finding 2's, but the obligation is not, and it should be listed rather than
   left to be rediscovered.

## 7. Honesty notes

- **The thesis states no clause here, and §2 is an extension — but a constrained
  one, and the distinction matters.** The thesis is silent at `ℓ = 0` for
  quotients (`n ≥ 1` at thesis.txt:2353) and at `v = 0` for `lift`
  (thesis.txt:2359). What §2.2 shows is that the silence leaves no freedom: the
  three parts of Theorem 6.7 it uses are stated and proved *without* a level
  restriction, so the value of `⟦Quot α r⟧` at `Sort 0` is determined by the
  thesis's own soundness invariants even though the thesis never writes it down.
  The proof obligation is still ours, not Carneiro's — nothing here is a reading
  of his text — but the risk is misidentifying the unique completion, not choosing
  badly among live alternatives. §6.2 (`lift` into `Prop`) is an extension in the
  weaker sense: assembled from stated clauses, with no comparable uniqueness
  argument behind it.
- Candidate B's exclusion (§3.2) rests on the kernel's documented policy that
  `define` requires `∃!` and that Skolem choice at arity ≥ 1 is unsound against
  the unrestricted Replacement scheme. That comment's argument was read and checks
  out — eliminability is what licenses extended-scheme instances — but the model
  theory behind it has **not** been re-derived here.
- **What was checked, and how.** Every source claim above is from reading the
  cited lines, and the citations were followed rather than trusted: the thesis
  quotations at 828–830, 1022–1029, 2132, 2353, 2359 and Theorem 6.7 at 2186 are
  verbatim; `u0_members`, `u0_two_valued`, `u0_subsingleton`, `Tower::pow`,
  `Tower::sub` and `Tower::at(0) = None` are as quoted in
  `derived/src/tower/rungs.rs`; `add_quot`'s four types, `Quot.lift`'s independent
  `[u,v]`, `Quot.ind`'s `[u]`-only motive and both ι rules are as quoted in
  `checker/src/mini/kernel.rs`; the `CondSite`/`FibreSite` keying of §2.1 is read off
  `checker/src/mini/interp.rs`. The countermodel computations (`quot(1,R) = {1}`,
  `quot(0,R) = 0`, `{1} ∉ U₀`) are two-line set calculations against the printed
  interfaces of `eqv.rs`/`classes.rs`. The `123_quotSoundType` figures in §5.1 are
  from an actual run of `mini --verbose`; the per-declaration split of those four
  pairs across `u ∈ {0,1}` is inferred from the pair count and the scheduling
  rule, not read directly off a per-pair dump.
- *This bullet read: "**Nothing in §2 has been implemented or tested.** No
  branch exists in the checker, T6 is unwritten, and `derived/src/quot/` has
  never been exercised against a Lean-side `r` at all (§6, finding 3. The clause
  is analysis." **All four clauses are false**, and the Verdict block at the top
  of this same file says so — "Landed at `u = 0`, `6706616`–`89e960e`, and
  completed at `f2c4b5b`". The branch is `checker/src/mini/quot.rs::build`; T6 was
  dissolved rather than written (§2.3's own correction); `derived/src/quot/` is
  exercised against a Lean-side `r` through `rel_graph`. The honesty note this
  bullet belonged to is otherwise intact — it is the record of what was analysis
  and what was measured **when the note was written**, and that reading is what
  the rest of §7 still gives.*
