# The general recursor and ι — design

Task #23, 2026-08-01. Design only; no code. Written against the tree as of this
morning — `derived/src/inductive/` (the carrier machine), `derived/src/isum/`,
`sigma/`, `fibre.rs`, `recarg.rs`, `wrec*`, `wnat_rec`, `wlist_rec`, and
`checker/src/tg.rs`'s `RecCore`/`RecNest`/`RecBottom`/`derive_iota`. Two agents
are editing `derived/` and `tg.rs` concurrently, so interface names cited here
may drift; the arguments do not depend on the names.

This is the part of the inductive story the thesis declines to do (§5.4,
`thesis.txt:1895–1901`), so unlike every other design note in this repo there
is no text to check against. Throughout, claims are marked **[read]** (checked
against code or export), **[measured]** (a number from a run recorded in the
log), or **[believed]** (argued, not derived). §9 collects everything I could
not settle.

Scope is the carrier machine's scope and no more: **non-indexed, non-mutual,
non-nested, large-eliminating declarations whose recursive arguments are
plain** (the thesis's `γ = ()` at `thesis.txt:1800`). What that excludes, and
how each exclusion must surface, is in §7 and §8.

---

## 1. Verdict up front

1. **Union-of-attempts survives, unchanged.** The construction is arity-blind:
   `wrec`, `wrec_extend`, `wrec_total` are stated `∀A ∀B ∀u ∀T ∀e` over
   arbitrary sets and never mention a constructor count, an argument count, or
   a parameter. It is already shared as `RecCore` and must stay shared. Do not
   abandon it, and do not rebuild it per declaration. What was per-inductive in
   the hand-written files — and what this design generalises — is only the
   layer *underneath* it (the packed step `e`) and the layer *above* it (the
   constructor bridge and the wiring). §2 is the audit.
2. **The general recursor is `wrec` at the carrier machine's own data, with a
   packed step built as one Replacement per constructor, unioned.** §3 gives
   the term as a function of declaration data alone.
3. **ι fires for one uniform reason**: the step is a graph whose keys are
   exactly the images of constructor arguments under the (tag, payload)
   packing; the keys of different branches are separated by `Inj`-distinctness
   and within a branch by `Inj`-injectivity, so the step is single-valued; and
   the W-recursor's ι hands the step precisely such a key. Totality needs only
   `step_typed`, which reduces — by `no_junk` on the tag sum and the fibre
   computation — to the minor premises' own typings. §4 states this as
   checkable theorem schemas with per-step lemma provenance.
4. **The real boundary is the target `T`, not the arities.** The simply-typed
   W-recursor takes one target set. That covers constant motives, opaque/local
   motives (conditionally), and — via `proof_eq` — every `Prop` motive. A
   *genuinely dependent Type-level motive* is out of reach of a single `T` and
   needs the Σ-target variant of the same union-of-attempts skeleton (§5).
   That failure is a counted gap, never a wrong `Proved`.
5. **Small elimination: the prior reading is confirmed and sharpened.** A
   `Prop` motive is the same carrier and the same recursor at another
   instantiation (`thesis.txt:1705–1709`); in *this* implementation it is even
   less than that, because a Prop-motive ι site short-circuits through
   `proof_eq` before `derive_iota` is ever consulted **[read]**. §5.3 is a
   different axis and stays out of scope. §6 has the schedule cost.
6. **One correction to the record**: `116_rtreeRecReduction` is *not* the
   corpus test for "two or more recursive arguments" that `wlist_rec.rs`'s
   closing notes and `INDUCTIVES.md` claim. `RTree.node`'s single field is
   `children : Bool → RTree` **[read**, export of `116`**]** — a
   *function-typed* recursive argument (`γ = Bool`), which is outside this
   design's scope (§7.9). The real plain-`m≥2` corpus test is **`RBTree`**
   (`042`/`068`/`077`): `red : N → RBTree α → α → RBTree α → RBTree α`, three
   constructors, two plain recursive arguments, **interleaved** with
   non-recursive ones **[read**, export of `042`**]**. Interleaving is
   therefore corpus-demanded, not hypothetical, and it forces one extension to
   `CtorSpec` (§3.1).

---

## 2. Q1 — does union-of-attempts generalise? Audit

Split the existing recursor stack into layers and ask, per layer, what depends
on the arities it was written at.

| layer | file(s) | depends on shape? | verdict |
|---|---|---|---|
| composite `comp(g,f,d)`, attempts `Att`, agreement, `wrec = ⋃Att`, sv, `rec_cond` | `wrec/` | no — `∀A∀B∀u∀T∀e`, one Replacement + one Separation + one union **[read]** | keep as is |
| one-point extension, totality, `wrec ∈ fs(W,T)`, unguarded ι | `wrec_extend`, `wrec_total` | no — same quantification; `composite_app`/`composite_single_valued` are `∀g∀f∀d` **[read]** | keep as is |
| the shared build (`RecCore`) | `tg.rs:3220,5275` | no — built once per thread, mentions no tag set **[read]** | keep; the general bottom sits on the same copy |
| the packed step `e` | `wbool_rec` (two-point graph), `wnat_rec` (Replacement, 2 branches hardcoded), `wlist_rec` (adds the head) | **yes — entirely** | superseded by §3.2's general step; keep the old files as cross-check instances |
| step_typed discharge | `wnat_rec/typed.rs`, `wlist_rec/typed.rs` | yes — `HYP` is a *curried `fs` membership*, and the case analysis is a hardcoded binary `sum_cases` | superseded: pointwise `HYP` (§3.3) + `no_junk` case analysis (§4 step 2) |
| constructor bridge | `enums`/`wnat`/`wlist` + `abbrev_defs` lookups in `fire_*` | yes — per-shape terms; also the *fibres differ* (`1` vs `finord(1)`, see §7.6) | superseded by `Inductive`/`Ctor` (already built) |
| currying nest (`RecNest`) | `tg.rs:3828,5883` | no — depth is `major_idx + 1`, prefixes carry everything **[read]**; except the `vars.len() < 4` guard at `tg.rs:5921` **[read]** | keep; relax the guard to `np + n + 2` |
| ι driver (`derive_iota`, `derive_iota_core`) | `tg.rs:9120,9177` | mostly no; except `idx > 1` rejection at `tg.rs:9210` **[read]**, the 3-armed `RecBottom`, fixed minor/target positions in `fire_*` | generalise: one new `RecBottom::General` arm replaces the per-shape `fire_*` |

**Verdict.** Union-of-attempts generalises because it was never about an
inductive at all — it is a theorem about five arbitrary sets, and the five
hand-written instantiations already share one copy of it. Everything
shape-bound sits in the packed step and the wiring, which is exactly where the
carrier machine (`derived/src/inductive/`) already replaced the shape-bound
carrier files. The general recursor is the same move one layer up.

Two things in the *existing* general layers deserve a hostile second look, and
both survive it:

- `step_typed`'s quantification `∀f ∈ fs(B(a),W) ∀r ∈ fs(B(a),T)` ranges over
  *all* functions, including ones no constructor produces. The pointwise `HYP`
  of §3.3 quantifies its recursive-argument slots over the whole carrier, so
  it covers exactly these junk instantiations too — the two match, and this is
  load-bearing in §4 step 2. **[read** against `wrec_total::step_typed`**]**
- Instantiating `∀A∀B…` at *open* terms (parameters free) is exactly what
  `wlist_rec` already does with `α` free **[read]**; nothing new is being
  asked of the kernel.

---

## 3. Q2 — the general recursor term, from declaration data

### 3.1 The input, and one required extension to `CtorSpec`

The carrier machine's input is
`DeclSpec { params: np, ctors: [CtorSpec { args: Vec<FnSym>, recs: usize }] }`
**[read**, `inductive/spec.rs`**]**. That is sufficient for the carrier — `A`
collects only the non-recursive arguments and `B` only counts the recursive
ones — but it is **not sufficient for the recursor**, because it erases the
*declared order* of a constructor's fields, and Lean's minor premise and
`RecRule` reduct both use that order. `RBTree.red`'s fields are
`N, RBTree α, α, RBTree α` **[read]**: non-rec, rec, non-rec, rec. A step
value built "fields then recs" would derive an equation about a different term
and be caught by `derive_iota`'s guard — a gap on every `RBTree` ι site.

So the recursor's spec is the carrier's plus a mask:

```text
enum Slot { Plain,          // consumes the next entry of args
            Rec }           // consumes the next recursive position
CtorSpec += order: Vec<Slot>     // len k + m; #Plain = k, #Rec = m
```

with the well-formedness check extended accordingly. The carrier ignores
`order`; only `val_i` (§3.2) and the wiring's field split read it. (Whether to
put the mask on `CtorSpec` or on a thin `RecSpec` wrapper is the concurrent
carrier-wiring task's call — the carrier files must not be churned for it.)

The convention that `βⱼ` has arity `np + j` — parameters plus the *earlier
non-recursive* arguments — already encodes the restriction that a later
argument type never depends on an earlier **recursive** argument. That matches
the thesis exactly (the `ctor` rule for a recursive argument does not extend
`Γ`, `thesis.txt:1798–1801` **[read]**), and it is forced by erasure: the tag
telescope holds only the non-recursive arguments, so nothing else is available
to substitute. A Lean declaration that violates it (a field typed by a
predicate on an earlier recursive field) must be **declined** by the spec
builder — counted gap, never a mistranslation. See §9.4.

### 3.2 The step, per constructor, uniformly

All terms below are functions of: the declaration data, the carrier machine's
outputs (`Inductive`: tags `A`, summands `A_i = Tel_i(p⃗)`, fibre `B`, bound
`u = U({A,T_B})`, carrier `W`, `RecArg`s, telescopes), the `n` minor-premise
variables `s₀ … s_{n-1}`, and one target variable `T`. Parameters `p⃗` stay
free variables throughout, as everywhere else in this development.

```text
FW_i := 𝒫(prod(finord(mᵢ), W))          FT_i := 𝒫(prod(finord(mᵢ), T))
P_i  := prod(FW_i, FT_i)                Q_i := prod(A_i, P_i)

val_i(σ, f, r) :=  s_i  applied, left to right, to
                     — per Slot::Plain j:  comp_j(σ)         (telescope projection)
                     — per Slot::Rec j:    app(f, Inj_j(•))
                   and then, for j = 0 … mᵢ−1:  app(r, Inj_j(•))

row_i(σ, p)    := ⟨ ⟨Inj_i(σ), p⟩ , val_i(σ, π₁p, π₂p) ⟩
E_i            := { row_i(π₁q, π₂q) : q ∈ Q_i }              (one Replacement)
e(p⃗, s⃗, T)     := E_0 ∪ (E_1 ∪ ( … ∪ ∅))                     (right-nested, n branches)

grec(p⃗, s⃗, T)  := wrec(A, B, u, T, e(p⃗, s⃗, T))
```

Design decisions, each with its reason:

- **No nullary special case.** The hand-written steps are
  `E ∪ {⟨k₀, z⟩}` — a Replacement plus a hand-made one-point graph for the
  nullary constructor. Uniformly, a nullary constructor is just a branch with
  `Q_i = prod(A_i, prod({∅},{∅}))` (since `prod(0,X) = ∅` and `𝒫(∅) = {∅}`
  **[read**, `wtype::empty_product`**]**), whose Replacement has exactly the
  rows `⟨⟨Inj_i(σ), ⟨∅,∅⟩⟩, s_i-applied-to-σ's-components⟩` — for `k = m = 0`
  that is the single row `⟨⟨Inj_i(•), ⟨∅,∅⟩⟩, s_i⟩`, which is the old
  `{⟨k₀,z⟩}` up to the `finord`/telescope spelling. One construction, no
  special case, matching how `recarg.rs` treats `m = 0`.
- **`pow_prod` supersets, as in `wlist_rec`**: `Q_i` must be a set before
  anything is proved, and `𝒫(prod(finord(mᵢ), X))` contains both `fs(finord(mᵢ), X)`
  and `∅` without any typing side condition **[read**,
  `wlist_rec/step.rs::pow_prod`**]**.
- **Projections, not existentials** — the settled extend-or-replace verdict of
  `wnat_rec`'s header, which was cashed once already (`wlist_rec`, "one more π",
  held in full **[measured]**). The general `row_i` is `wlist_rec::row_at` with
  the bare head `h` replaced by the telescope element `σ` — one projection at
  the Replacement, values stated at `(σ, p)` so the η rule is never needed.
  Everything from `step_cases` to `unpack` stays payload-opaque; the `k`-fold
  component reads happen only in `val_i` and in the `computes` lemma.
- **The union is `finset`-shaped**: memberships and case analysis over
  `x ∈ E_0 ∪ (…)` come from the same right-nested pattern `finset.rs` already
  proves; `n = 0` gives `e = ∅` and `Empty` needs no ι rule.

**Cost note (believed, from precedent):** `wlist_rec` is ~1000 lines for
`n = 2` with hardcoded branch shapes. The general step is the same file
shape with Rust loops over `i < n`, `j < k_i`, `j < m_i` where `wlist_rec` has
two hardcoded cases; the per-lemma proofs are the ones already written, at
symbols instead of literals. Expect 1.5–2× `wlist_rec`, not `n`×.

### 3.3 The hypothesis bundle: pointwise, not curried

`wnat_rec`/`wlist_rec` state `HYP` as a curried function-space membership
(`s ∈ fs(α, fs(lt(α), fs(T,T)))`). **That does not generalise**, for a reason
that has nothing to do with arity: a *dependent* telescope (`β₁` mentioning
`y₀`) has no iterated-`fs` type at all — the inner space varies with the outer
argument. The carrier machine explicitly supports dependent telescopes
**[read**, the eighth test shape**]**, so the general `HYP` must be the
pointwise form:

```text
minor_typed_i(p⃗, s_i, T) :=
  ∀y₀ … y_{kᵢ−1} ∀t₀ … t_{mᵢ−1} ∀v₀ … v_{mᵢ−1}.
    (( ⋀_j yⱼ ∈ βⱼ(p⃗, y₀…y_{j−1}) ∧ ⋀_j tⱼ ∈ W ∧ ⋀_j vⱼ ∈ T ))
      → s_i⟪order-mask over y⃗, t⃗⟫ v₀ … v_{mᵢ−1} ∈ T

HYP := minor_typed_0 ∧ ( … ∧ minor_typed_{n−1})
```

This is strictly weaker than the curried form (the curried form implies it by
`funspace_app_mem`, `k+2m` times), which is exactly right: weaker hypotheses
make the derived theorems stronger, and the *backend* is the place that
bridges from whatever typing `has_type` can produce — for the corpus's
non-dependent shapes, from the `fs`-membership asked at the beta-reduced
kernel term, exactly as `fire_nat` does today **[read]**. Note the
recursive-argument slots quantify over the whole carrier `W`, which is what
§4's step 2 needs (see the audit note in §2).

### 3.4 The Lean-facing term

Unchanged from what exists: `⟦T.rec.{u⃗}⟧` is a `RecNest` of
`major_idx + 1 = np + n + 2` lambda graphs, domains walked off the recursor's
own type at locals (the discipline that makes the two sides of an ι equation
share their assumptions — keep it, it is the single most load-bearing wiring
decision on record **[measured**, `073`/`075`**]**). The bottom becomes

```text
t_last(p⃗, C, s₀…s_{n−1}, b) := app(grec(p⃗, s⃗, T_policy), b)
```

with one new `RecBottom::General(Rc<GenRecursor>)` arm replacing the growth of
per-shape arms. `T_policy` is §5.2.

---

## 4. Q3 — why ι fires, in general

### 4.1 The theorem schemas

Per declaration, the general module derives, at fresh `p⃗, s⃗, T` and per
constructor `i` fresh `y⃗, t⃗` (writing `ctor_i(y⃗,t⃗)` for the carrier machine's
constructor term `⟨Inj_i(tuple y⃗), recfun(t⃗)⟩` and `H_i^ctor` for its `k+m`
Lean-shaped argument typings):

```text
(S1) computes:   ⊢ ∀… ( (σ-typings ∧ payload-typings) →
                    app(e, ⟨Inj_i σ, ⟨f,r⟩⟩) = val_i(σ, f, r) )
(S2) sv:         ⊢ ∀p⃗ ∀s⃗ ∀T. sv(e(p⃗,s⃗,T))
(S3) step_typed: ⊢ ∀p⃗ ∀s⃗ ∀T. (HYP → step_typed(A, B, u, T, e))
(S4) iota_i:     ⊢ ∀p⃗ ∀s⃗ ∀T ∀y⃗ ∀t⃗. ((HYP ∧ H_i^ctor) →
                    app(grec(p⃗,s⃗,T), ctor_i(y⃗,t⃗))
                      = s_i ⟪y⃗,t⃗ in declared order⟫
                            app(grec, t₀) … app(grec, t_{mᵢ−1}) )
```

(S4) is the deliverable: ι with every recursive call live, every field live,
at every arity, hypotheses exactly `HYP` plus what Lean's constructor states.

### 4.2 The argument, step by step, with provenance

Every step below is an instance of a lemma that exists today or a loop over
such instances; nothing needs a new proof *idea*. Markers: ✓ = exists,
G = generalisation of an existing proof (same shape, `n`/`k`/`m` looped).

**Step 0 — the carrier prerequisites.** `closed(A,B,u)` unconditional
(`Inductive::closed` ✓); the fibre equations
`a ∈ A_i → app(B, Inj_i(a)) = finord(mᵢ)` (`Fibre::fibre` ✓); tag membership
(`ISumSyms::inj_mem` ✓, `Telescope::intro` ✓); `no_junk` per tag arity
(`ISumSyms::no_junk` ✓ — this design is its first real consumer);
injectivity/disjointness (`inj_inj`/`inj_distinct` ✓).

**Step 1 — the step computes (S1) and is a function (S2).** Membership of a
row: Replacement condition at witness `q := ⟨σ, ⟨f,r⟩⟩` plus
`unpack_row`/`unpack` (G of `wlist_rec/members.rs`, `step.rs`); the payload
memberships are `fs ⊆ 𝒫(prod)` (✓ `funspace_subset_pow_prod`). Then sv:
elements of the `n`-fold union are classified by the `finset`-style case
analysis (G); keys of distinct branches clash on `Inj_i σ = Inj_j σ′`, killed
by `inj_distinct` (✓); keys within a branch give `π₁q = π₁q′`, `π₂q = π₂q′` by
`inj_inj` + `opair_inj` (✓), and the values are equal by congruence because
`row_i` is one closure applied to `q` (G of `step_single_valued` — the
`wlist_rec` lesson about never reassembling `q` applies verbatim). (S1) is
membership + sv, exactly as in both hand-written files.

**Step 2 — `HYP → step_typed` (S3).** Given `a ∈ A`, `no_junk` splits into `n`
cases `a = Inj_i(σ), σ ∈ A_i`. In case `i`: rewrite the fibre,
`B(a) = finord(mᵢ)`; the hypotheses become `f ∈ fs(finord(mᵢ), W)`,
`r ∈ fs(finord(mᵢ), T)`; compute `app(e, ⟨a,⟨f,r⟩⟩) = val_i(σ,f,r)` by (S1)
(payload memberships via `funspace_subset_pow_prod` ✓); type each component —
`comp_j(σ) ∈ βⱼ(p⃗, comp₀σ …)` by `Telescope::proj_mem` (✓ — note this lands on
*exactly* `minor_typed_i`'s hypothesis instantiated at `yⱼ := comp_j(σ)`,
which is the payoff of argument types being `FnSym`s: substitution is
application), `app(f, Inj_j •) ∈ W` and `app(r, Inj_j •) ∈ T` by
`funspace_app_mem` (✓) with `Inj_j(•) ∈ finord(mᵢ)` (`inj_mem` ✓); conclude
`val_i ∈ T` by `minor_typed_i`. This is the G of
`NatRec::step_typed`/`ListRec::step_typed` with `no_junk` replacing the binary
`sum_cases`.

**Step 3 — fire the W-recursor.** `wrec_total::iota` (✓, from `RecCore`) at
`a := Inj_i(tuple y⃗)`, `f := recfun(t⃗)`, under `closed ∧ step_typed` (steps
0, 2). Its premises: `Inj_i(tuple y⃗) ∈ A` (step 0 under `H_i^ctor`);
`recfun(t⃗) ∈ fs(B(a), W)` from `RecArg::in_funspace` at `S := W` (✓, under
`tⱼ ∈ W`) transported along the fibre equation backwards (Leibniz, as
`ctor.rs` already does for the constructor typing ✓). Conclusion:
`app(grec, ctor_i(y⃗,t⃗)) = app(e, ⟨Inj_i σ, ⟨recfun, comp(grec, recfun, B(a))⟩⟩)`.

**Step 4 — compute the step at that key.** (S1) at `σ := tuple(y⃗)`,
`f := recfun(t⃗)`, `r := comp(…)`. The one non-trivial membership is
`comp(grec, recfun, B(a)) ∈ FT_i`: rewrite `B(a) → finord(mᵢ)` inside `comp`'s
third argument (congruence), then `RecCore.comp_typed` (✓ — its `indom`
premises come from totality, already under `H`), then `fs ⊆ 𝒫(prod)`.

**Step 5 — read the components back.**
`comp_j(tuple y⃗) = yⱼ` — `j` applications of `Proj::fst`/`snd` on literal
pairs (✓, unconditional); `app(recfun, Inj_j •) = tⱼ` — `RecArg::app[j]` (✓,
unconditional); `app(comp, Inj_j •) = app(grec, app(recfun, Inj_j •)) = app(grec, tⱼ)`
— `wrec_typing::composite_app` (✓, `∀d`, at `b := Inj_j(•)` with `b ∈ d` via
the fibre equation) chained with `RecArg::app[j]`. Chain 3–5 by
transitivity/congruence under the ambient hypothesis (`hyp_eq_trans`,
`hyp_congr` ✓). That is (S4).

### 4.3 What the argument assumes — the complete list

1. `HYP` — `n` pointwise minor typings at the single target `T`. Everything
   about whether these are *dischargeable* is a wiring/`T`-policy question
   (§5); the derived schema just carries them.
2. `H_i^ctor` — the constructor's own argument typings, exactly what Lean
   states.
3. `closed(A,B,u)` — discharged unconditionally by the carrier machine.
4. Nothing else. In particular: no parameter typing (`α ∈ ⟦Sort u⟧` never
   appears, confirming the `wlist` finding at general arity), no `Sort`
   encoding facts, no choice, no new axiom — the step is `n` Replacements,
   `n−1` binary unions, and instances of existing lemmas.

### 4.4 How to check it (non-vacuity discipline)

The argument above is only as good as its witnesses. Concretely:

- **Witness per shape.** Generalise `premise_witness`: at concrete small
  instantiations (`T := 1`, `s_i :=` nested constant graphs landing on `•`,
  parameters `:= 1` so every `h ∈ α`-style hypothesis is satisfiable),
  discharge `HYP` outright and fire (S4) closed and unconditional at **the
  last constructor, not only the first** (injection-depth bugs hide at the
  end), at a shape with `n ≥ 3`, at a shape with `mᵢ ≥ 2`, and at the
  interleaved shape (`Plain,Rec,Plain,Rec` — the `RBTree.red` mask). Assert
  the two sides are distinct terms and the recursive occurrence is present —
  the `wnat_rec` test discipline.
- **Cross-check against the hand-written recursors.** The general machine's
  `N`-shape and `List`-shape instances are *not* term-identical to
  `wnat_rec`/`wlist_rec` (different fibres, §7.6), so the check is not term
  equality; it is: both fire, at corresponding instances, to equations that
  differ only by the recorded spelling differences. Cheap and worth having as
  a test while both exist.
- **Corpus acceptance**, which is the real one: `073`/`075`/`076` do not
  regress (0/4/32 today **[measured]**), `068_rbTreeRef` stays 0, and
  `077_RBTree.id_spec`'s ι gaps close. `HAS_GAPS` flips `077` from expected-gap
  to unexpected-pass, which is the signal to look for.

---

## 5. The target `T`: the one real boundary

### 5.1 What a single `T` can and cannot do — established by cases

The W-recursor here is simply typed: one target set, `wrec ∈ fs(W,T)`. Lean's
recursor is dependently typed: `C : ind p⃗ → Sort u₁`. The gap between the two
is absorbed case by case:

- **`Prop` motive (`u₁ = 0`).** The ι site's redex and reduct are both proofs;
  `Certifier::iota`'s implementation tries `proof_eq` *first* and only falls
  through to `derive_iota` **[read**, `tg.rs:12090–12098`**]**, and `proof_eq`
  discharges by the model's proof irrelevance (`u0_subsingleton`) **[read]**.
  So the Prop-motive instantiation never touches `grec` at all. (Caveat §9.6:
  `point_of_proof` can itself fail; then the site falls through and `grec`'s
  chain would carry `HYP` at a `T ⊆ {•}`-shaped target — sound, conditional.)
- **Constant motive** (`075`, `076`, and every recursor used to define a plain
  function): `T :=` the motive's value at one point; all `minor_typed_i` are
  derivable from the minors' typings asked at beta-reduced simple types —
  the mechanism `fire_nat` implements today **[measured**, `075` 54→4**]**.
- **Opaque/local motive** (`073`): assumptions stay conditional and are
  dischargeable at binders when nothing above admits **[measured**, `073` →
  0**]**. For all-nullary declarations the `Bool` trick — `T :=` the finite
  set of the minors themselves — makes `HYP` *free* and fully
  dependent-motive-capable; keep it as a policy branch so enumerations do not
  regress.
- **Genuinely dependent Type-level motive**: no single `T` makes `HYP` both
  true and Lean-derivable — with `T := ⟦C c₀⟧` the minors' values live
  elsewhere; with `T := ⋃img(C)` the `vⱼ ∈ T` hypotheses are too weak to
  invoke Lean's minor typing. **[believed**, argued §5.3**]** The certificate
  is then conditional on an undischargeable (possibly unsatisfiable) formula:
  a permanent escape, i.e. a counted gap. Sound, honest, and visible in the
  ledger.

### 5.2 `T`-policy (wiring)

The derived schemas quantify `∀T`, so policy lives entirely in the wiring, per
nest (T must be fixed at nest-build time, since the bottom's body mentions
it):

1. all constructors nullary and field-free → `T := fin(s⃗)` (the `Bool` trick;
   `HYP` free);
2. some constructor nullary → `T := doms[np+1+i₀]` for the first nullary
   constructor `i₀` — the motive at a closed constructor **as the nest walked
   it**, never rebuilt (the `075` lesson, twice recorded **[measured]**);
3. otherwise → no canonical closed point exists. Options: decline (opaque
   recursor, counted gaps — the safe default), or `T := app(⟦C⟧-var, c)` at an
   arbitrary constructor instance over fresh canonical arguments
   (undischargeable `HYP`, still sound). Recommend **decline** until a corpus
   file demands it; see §9.3. (`RBTree` has `leaf`, so `077` is policy 2.)

### 5.3 The extension path: the Σ-target recursor (design sketch, not scoped)

If dependent Type-level motives ever matter, the fix is structural and reuses
the skeleton: redefine an attempt as a subset of the *dependent sum*
`Σ(w ∈ W). C(w)` (one Separation, given the motive as a set-level graph) with
`rec_cond` demanding `r`-slots in the dependent function space
(`ext::dprod`) instead of `fs(B(a),T)`. Agreement, the one-point extension,
totality and ι are the same inductions with `prod(W,T)` and `fs(B(a),T)`
systematically replaced; `step_typed` becomes "the step lands in
`C(sup a f)`", which is Lean's dependent minor typing on the nose.
**[believed** — shape-inspection of `wrec_extend`/`wrec_total`, not a
derivation; recorded as unsettled in §9.7**]** This is the strongest reason
*not* to abandon union-of-attempts: transfinite-on-rank would need ordinals
*and* face the same target question; the attempts route localises the change
to the bound and one hypothesis.

---

## 6. Q5 — small elimination, confirmed, and the schedule cost

**The prior reading is confirmed.** `thesis.txt:1705–1709`: large-eliminating
recursors are simplified to `1 ≤ ℓ`, and "the general recursor can be
constructed from this by using `C′ := λx. ulift^{max(1,ℓ)}_ℓ (C x)`" — the
*same* carrier, the same recursor, with the motive lifted: another
instantiation, not another construction. Since `⟦ulift⟧ = id` in the thesis's
model (`thesis.txt:2106`), the set-level content of the wrapper is nil; in
this implementation the `u₁ = 0` instantiation is absorbed even earlier, by
`proof_eq` (§5.1) — the recursor machinery is not consulted at Prop motives
**[read]**.

**§5.3 is a different axis, as the prior analysis said.** `u₁ := 0` selects a
Prop *motive*, which every inductive has. §5.3's subsingleton eliminators
concern Prop-valued *inductives* with large elimination (`Eq`, `Acc`, class
(S) of `LEVEL-POLYMORPHIC-INDUCTIVES.md` — whose §6 already draws this
distinction; nothing here contradicts it, and this design adds the ι-site
detail that the two axes are handled by *disjoint certificate routes*:
`proof_eq` for the Prop motive, nothing-yet (counted `is_k`/`Acc` gaps, e.g.
`094`, `117`/`118`) for §5.3).

**Cost of the extra level in the instantiation schedule (task #18).** The
recursor's `u₁` multiplies `(u₁, ℓ⃗)` pairs, and the split of costs is:

- **once per declaration, level-free**: the whole derived development — the
  carrier (`Inductive`), the general step, (S1)–(S4). These are `∀`-statements
  over set variables; no level occurs in any of them. This is where all the
  expensive derivation lives, and it does **not** multiply.
- **once per `(name, levels)` pair**: one `RecNest` — `np+n+2` `define_abbrev`s
  + `lambda_n` + `beta_conditional_n`, plus the `⟦Sort·⟧`-dependent domain
  interpretations. Cheap, linear in the pair count, already keyed correctly
  (`rec_nests: (NamePtr, Vec<Term>)` **[read]**).
- **pairs with `u₁ = 0`**: cheaper still — the ι site short-circuits through
  `proof_eq`, so those pairs typically never even build the nest.

So the schedule's recursor bill is "one nest per pair", with the derived
machine amortised across all pairs of a declaration. No change to
`instantiations.rs` is needed for this design.

---

## 7. Q4 — failure modes

Ordered by how silently they would bite.

1. **Vacuous generality (the worst class).** (S3)/(S4) carry `HYP`; a
   mis-stated `HYP` (wrong currying, wrong order, wrong quantifier domain)
   makes every theorem vacuously true and every test that only checks
   conclusions pass. Defence: the witness discipline of §4.4 — `HYP`
   *discharged*, rules fired closed, at the last constructor, at `n ≥ 3`,
   `m ≥ 2`, and the interleaved mask. This is not optional polish; it is the
   only thing standing between "derived" and "derived about nothing".
2. **Order-mask mismatch.** `val_i` in the wrong order derives a true equation
   about the wrong term. The `derive_iota` guard catches it (gap, not
   unsoundness), but only at wiring time and only on files that exercise the
   shape — and the interleaved shape's first exercise is `077`, a 100-gap
   file where one more gap is easy to misattribute. Defence: a derived-layer
   test pinning `val_i`'s spelling against the mask at the `RBTree.red` shape,
   *before* wiring; plus verifying the fields-then-ihs convention against
   `reduce_rec`/`RecRule` rather than against this document (§9.1).
3. **Dependent Type-level motive** (§5.1): permanent escape by design. The
   risk is not the escape but *misreading* it later as a recursor bug.
   Record it in the gap taxonomy now: "iota: HYP undischargeable — dependent
   motive" should be its own reason string.
4. **Two recursor developments that do not compose.** Every `Replacement`
   mints fresh symbols; building `grec` twice for one declaration yields two
   recursors whose theorems cannot be chained — a lesson recorded three times
   already (`RecCore` sharing, `Inductives::PointFun`, `Machine` docs).
   Defence: the `GenRecursor` is cached per declaration alongside the
   `Inductive`, and the cache stores the *theorems*, per the standing memo
   rule. The general recursor must be built over the **same** `Machine` and
   `Inductive` the (concurrent) carrier wiring uses — this is the one
   coordination point between the two running tasks.
5. **The hand-written/general seam.** The general carrier's fibres are
   `finord(m)` (element `Inj_0(•) = ⟨∅,•⟩`), the hand-written ones literal `0`/`1`
   (element `•`) — different sets, different constructor terms. Mixing the
   general recursor with the hand-written carriers (or vice versa) composes
   nothing and fails everywhere. Defence: cut over carrier + constructors +
   recursor per inductive *atomically* in the wiring, and keep the old bottoms
   until the corpus numbers match (§8).
6. **`finord(1) ≠ 1`** (the recorded trap, still live): any reuse of
   `point_fun`-shaped reasoning at general `m` silently proves things about
   the wrong domain. `recarg.rs` already routes around it; the step must apply
   `f` and `r` at `Inj_j(•)`, never at `•`.
7. **Wiring index arithmetic.** The general `fire` must read minors at
   `vars[np+1 .. np+1+n]`, the target per §5.2's policy, drop exactly
   `num_params` constructor arguments (mirroring `num_extra_params_to_major`),
   and lift the `idx > 1` and `vars.len() < 4` guards (`tg.rs:9210`, `5921`)
   to `idx < n` and `depth = np + n + 2 + num_indices(=0)`. Each of these has
   a guard downstream, so mistakes surface as gaps — but as *diffuse* gaps.
   Defence: assert the depth equation against `major_idx` once, loudly.
8. **sv at colliding telescopes.** Two constructors with identical argument
   types share one telescope by cache design **[read]**, so their summands are
   the same *term*; branch separation must come from `Inj_i ≠ Inj_j` alone.
   The §4 argument uses only that — but a test at a two-identical-constructor
   declaration (`TwoBool`-shaped, with fields) should pin it.
9. **Out-of-scope shapes leaking in.** Function-typed recursive arguments
   (`RTree`, `Acc.intro`'s second field, `WellFounded`) must be *declined at
   the spec builder* — their fibre is a telescope `Σ(z::γ)`, their ihs are
   functions, and their reduct contains a lambda under the minor, so a plain
   translation would fail the guard at best. Same for indexed families
   (`Eq`), `is_k`, mutual/nested. Every one: counted gap with its own reason,
   never a forced fit. The spec builder is the choke point; it must check
   *positively* for the covered shape (plain rec args, `γ = ()`), not
   negatively for known exclusions.
10. **`ctor_rules` keyed by name only** — the recorded pre-existing hazard
    (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §4.5) becomes easier to hit once
    inductives are interpreted generally at more levels. Fix the key to
    `(name, levels)` when touching the wiring.

---

## 8. Recommended implementation order

Each rung measurable, riskiest first-exposed rung marked.

1. **Spec extension** (`Slot` mask) + spec-builder scope checks (§3.1, §7.9).
   Small; unblocks everything; coordinate with the carrier-wiring task.
2. **General step** — `derived/src/inductive/step.rs` (+ `members`/`values`/
   `computes` files per the granularity rule): (S1), (S2). Cross-checked at
   the witness shapes before anything consumes it.
3. **`step_typed` from pointwise `HYP`** — (S3), first consumer of `no_junk`.
   **← riskiest derived step**: it is the one proof with no hand-written
   ancestor at its actual shape (`no_junk` case analysis under an ambient
   hypothesis across `n` branches). If the design note is wrong anywhere in
   the derived layer, it is here.
4. **(S4) + generalised `premise_witness`** at the six witness shapes (§4.4).
5. **Wiring**: `RecBottom::General`, generalised `derive_iota_core`
   (`idx < n`, param drop, obligations), `T`-policy, pointwise-`HYP`
   bridging. **← riskiest step overall**, because it is where derived
   statements meet nest-computed terms, and every recorded late surprise
   (`doms`-as-computed, `mem_along_c`, trailing args, `derive_beta`,
   `whnf` recall) lived exactly here. Wire `RBTree` (`068`/`077`) first — it
   is the only corpus shape the hand-written bottoms cannot reach, so its ι
   gaps closing is unambiguous credit.
6. **Cut-over**: replace `Enum`/`Nat`/`List` bottoms (and the hand-written
   carriers, jointly — §7.5) with the general machine; acceptance is
   `073`/`075`/`076` byte-identical or better, fragment 27/27, arena 152/0/2.
   Only then delete, or demote to tests, the superseded files.
7. **Optional, after**: step 7 uniqueness (`define` form); the Σ-target
   variant if dependent motives are ever measured to matter.

---

## 9. What I could not settle

1. **The exact minor-premise argument convention** — fields in declared order,
   then one ih per recursive field in field order — is asserted from `List`'s
   `RecRule` and `wlist_rec`'s docs, not verified against `reduce_rec` for an
   *interleaved* constructor. Verify against `RBTree.red`'s `RecRule::rhs` in
   the export before freezing `val_i`.
2. **Whether any corpus ι site has a genuinely dependent Type-level motive.**
   `073`/`075`/`076` do not; `077` I did not decode. Worth one instrumentation
   run before deciding how much §5.3-sketch matters.
3. **`T`-policy for declarations with no nullary constructor** (§5.2 option
   3). No corpus witness either way; recommend decline-and-count until one
   appears.
4. **Whether Lean accepts a later field depending on an earlier recursive
   field** (would need declining, §3.1). Argued from the thesis's rule shape;
   not tested against a live kernel, and no corpus witness found (I did not
   scan exhaustively).
5. **The `m ≥ 2` and interleaved shapes have never been derived end-to-end**
   anywhere — `RBTree` is the first. All confidence there rests on the
   claim that `wlist_rec`'s proofs are payload-opaque, which held once
   (`N → List`) and is being extrapolated a second time.
6. **`proof_eq` coverage of Prop-motive ι sites**: the route exists and fires
   (`101` **[measured in log]**), but I did not enumerate the sites where
   `point_of_proof` fails and the fall-through would reach `derive_iota` with
   a Prop-shaped target.
7. **The Σ-target variant** (§5.3) is a shape-inspection argument, not a
   derivation. Specifically unverified: that `wrec_extend`'s `sv(G)` argument
   survives the value's type varying with the key.
8. **Cost estimates** (§3.2, 1.5–2× `wlist_rec`) are extrapolation from two
   data points by an estimator with a recorded miss (`wnat_rec` came in at
   ~1050 lines against a 700–1000 estimate — close, but the wiring half was
   estimated at 300–500 and took two extra bug-fixes to land).

---

## 10. Implementation addendum — task #23, derived layer landed (2026-08-01)

Rungs 1–4 are implemented in `derived/src/inductive/` (`spec.rs` gained
`Slot`/`order`; `step.rs`, `members.rs`, `values.rs`, `computes.rs`,
`premise.rs`, `typed.rs`, `iota.rs`, `recursor.rs`). (S1)–(S4) are exported as
`GenRecursor`, exercised by `derived/tests/genrec.rs` at the witness shapes of
§4.4 including closed, `HYP`-discharged ι firings at the last constructor of
`n = 3` declarations with masks `Plain,Rec,Plain,Rec` **and** `Rec,Plain,Rec,
Plain`. Two corrections to this document, both **[read** from the export**]**:

1. **§1.6 is wrong about `RBTree`.** `042_rbTreeDef`'s declaration is
   `RBTree : Sort u → Color → N → Sort _` with **`numIndices: 2`** — an
   *indexed family* (`red : ∀n, RBTree α b n → α → RBTree α b n → RBTree α r
   n`). It is therefore **outside this design's own scope** (§7.9), `077`'s ι
   gaps will *not* close via the general recursor, and the wiring must
   **decline** `RBTree` as indexed (counted gap), not wire it first (§8 rung
   5's suggestion is void). The *in-scope* corpus witnesses for the field-order
   mask and `m ≥ 2` are instead: `Lean.Name.str : Name → String → Name`
   (mask `Rec,Plain`, in `init-prelude` — ubiquitous), `Lean.ParserDescr.sepBy
   /sepBy1` (`Rec,Plain,Rec,Plain`), `Lean.RArray.branch` (`Plain,Rec,Rec`),
   and `Lean.Grind.CommRing.Expr.add/sub/mul` (`Rec,Rec`). Interleaving stays
   corpus-demanded; the demanding files are the preludes, not the RBTree
   tutorials.
2. **§9.1 is settled.** The minor-premise convention — fields in declared
   order, then one ih per *recursive* field in field order — is confirmed
   against an interleaved constructor's `RecRule::rhs` in the export
   (`RBTree.red`: `red3 n5 x6 x7 x8 (rec … x6) (rec … x8)`; `RBTree.black`,
   six fields, likewise). `val_i`, the pointwise `HYP` and the ι right-hand
   sides all share one spelling of it (`inductive::applied_minor`), so the
   three cannot drift.

Still open from §9: 2 (corpus dependent-motive census), 3 (`T`-policy without
a nullary constructor), 4 (later field on earlier recursive field — now also
*unrepresentable* in `CtorSpec`, so the checker-side spec builder must decline
it), 6 (`proof_eq` fall-through census), 7 (Σ-target variant). §9.5 is closed
at the derived layer; corpus end-to-end awaits rung 5. §9.8's estimate held:
~1 880 lines of module code against `wlist_rec`'s 2 080 for all arities at
once, plus 630 of tests.
