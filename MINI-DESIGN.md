# The mini kernel, in Rust, proof-producing — design

*2026-08-01. Task #31(a). Design for a Rust port of
[`lean-mini-kernel`](https://github.com/nomeata/lean-mini-kernel) (read in full
from the clone at the scratchpad; `MiniKernel/Kernel.lean` is 773 lines and is
quoted here by function name), evidence-threaded from the first line, reusing
`kernel/`, `derived/`, and `checker/`'s parser and level pre-pass.*

**Method note.** Everything marked **[read]** was verified in this tree or in
the mini-kernel clone during this survey. `checker/src/tg.rs` is cited by
function name only — it is under live edit. Where a sentence is inference
rather than verification, it says so. Corpus numbers are quoted from
`README.md` §Coverage (68 of 91 tutorial exports at zero gaps; the task brief
says 70 — the number drifts upward and the README row is the anchor).

---

## 0. What mini is for, and the two axes it is measured on

Mini is where the evidence-threading design is built without nanoda's
confounders. The mini kernel **[read, all of `Kernel.lean`]** has: a
`ReaderT LEnv (Except String)` monad and nothing else — no state, no caches,
no hash-consing; plain owned de Bruijn expressions with explicit
`shift`/`substs`; a local context that is literally a telescope
`lenv : List Expr`; whnf as a stack machine with full eager delta; recursors
*generated* from inductive declarations rather than parsed; and a defeq that
is "whnf both sides, then structural, then eta". Every function that nanoda's
`THREADING-CENSUS.md` lists as a workaround — `has_type_*`, `syn_type`,
`local_premises`, `domain_obligation`, the `CondEq`/`u_*`/`reassume`
formula-level hypothesis apparatus, `discharge_families`, the `Dropped`
ledger, the `Admit`-with-retry funnel — exists to compensate for evidence that
was discarded or never threaded. **None of them may exist in mini.** The
design rule, stated once and applied everywhere below:

> Every operation takes evidence of its precondition and returns evidence of
> its postcondition. No function discards a certificate that has a consumer.
> No function searches for a fact. The only two ways to obtain a `Thm` about a
> Lean judgement are (i) composition of the evidence handed in, and (ii)
> running the checker's own inference/conversion *forward* on a subterm.
> (ii) is inference, not search: it is deterministic, total on well-typed
> input, and produces its evidence as it goes. What is banned is the
> goal-directed clause-matching of `TgBackend::has_type_a` and the
> context-guessing of `local_premises`.

### 0.1 The first measurement: what the backend/checker split costs nanoda

*Added 2026-08-01, from building §6.2's classifiers **[implemented and tested,
`mini/src/kernel.rs`]**. This is a finding about **nanoda**, not a note about
mini, and it is the clearest measurement so far of what task #29 should aim
at.*

The list above says those workarounds "may not exist in mini", as a rule.
For one whole family the situation turned out to be stronger: they are **not
expressible** once the split is gone, so no discipline is needed to keep them
out.

Deciding which §6.2 clause a `Π` or a `λ` takes needs the body's *sort*.
nanoda's `TgBackend::body_clause` cannot ask for it — its own doc says why:
*"the decision needs the body's sort, `infer` lives on `TypeChecker`, which
owns this backend and is in the middle of a call into it, and the backend may
not call back."* So it approximates, with a hundred-line syntactic walk over
heads and arities, plus a redex arm, a `let` arm, a projection arm, a
3-valued `Clause` with an `Undet::Unknown` case, a memo to pin functionality,
and the `syn_type`/`syn_type_proj` shadow walk beside it — whose *only*
purpose is to feed this classifier without re-entering the checker.

In mini the classifier is:

```
body_clause(b) = is_prop(b)                    -- lvl(b) = 0
term_clause(e) = body_clause(infer_type(e))    -- sort(e) = lvl(type of e)
```

Six lines, and **exact**. What that costs nanoda, itemised:

| nanoda carries | in mini | why |
| --- | --- | --- |
| ~100-line syntactic walk | 6 lines | the decision can call inference |
| redex arm, `let` arm | — | `is_prop` whnfs; `infer_type` substitutes |
| `syn_type` / `syn_type_proj` | replaced, not deleted | see below — they break a real loop |
| `Undet::Unknown` | unrepresentable | inference is total on well-typed input |
| the memo (to *pin* functionality) | optional | `is_prop` is a function over no state |
| `081_PSigma.snd`'s 8 lost derivations | 0 | they were a `Prop`/`Undet` disagreement between two paths of the approximation |

None of that is a threading debt in the census's sense — no evidence is
dropped anywhere in it. It is the cost of the *architecture*: a proof backend
that may not call the checker must re-derive, approximately, facts the checker
computed exactly a moment earlier. §0's rule already permits the fix ("running
the checker's own inference/conversion *forward* on a subterm" is inference,
not search).

**But `syn_type` is not pointless work, and an earlier revision of this
section implied it was.** It said the shadow walk "exists only to feed this
classifier", which is true and reads as wasteful — and that reading is wrong.
Feeding the classifier without re-entering the checker is a *real problem*,
not a self-inflicted one: the classifier needs the term's type, and the
obvious way to get it — ask inference — is **circular**, because the
interpretation the inference is producing is itself what needs the clause.
Mini hit that circle head-on and overflowed its stack (§13, risk 3).
`syn_type` is nanoda's way of breaking exactly that loop, by a cheaper and
approximate route.

So the correct claim is narrower and more useful: **nanoda is solving a real
problem by a worse means.** The better means is not "call inference" — that
is the loop — but *build the interpretation compositionally as inference
proceeds*, so the clause is read off a type the caller already holds and no
second traversal happens at all. That is what mini must do and what #29
should port. A finding that makes an existing design look purely wasteful
deserves more suspicion than this section first gave it.

### 0.2 The second measurement: `local_premises` has nothing to reconstruct

*Added 2026-08-01, from threading the reduction certificates
**[implemented and tested, `mini/src/conv.rs`]**. Also a finding about
nanoda.*

To contract `(λ x:A. b) a` the certificate needs `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧`.
`TgBackend::local_premises` **guesses** it: it scans the argument expression
for `Local` nodes, even under open binders, and reconstructs a hypothesis set
from what it finds. It is a heuristic reconstruction of information the
checker held exactly, one call earlier, and discarded.

Mini's scope stack *is* that information, so there is nothing to reconstruct.
For a `bvar`-headed argument the premise is `scopes.get(i).assumption()` —
one vector index, no derivation. That is the case the census counts as 5 186
of nanoda's `has_type` misses ("a local at the top level"). For a compound
argument it is a recursive `infer_type`, which §0's rule permits.

The general shape, and the thing to port: **`beta_leg` takes the membership
as a parameter.** A function that needs a fact takes it. Every one of
`local_premises`, `domain_obligation` and `has_type_local` exists because
some function needed a fact and was not given it; none has a counterpart
here, and none needs one.

Two smaller items fell out of the same pass and are worth recording because
they are *costs of the interpretation choice*, not of threading:

* **Zeta and `natLit` unfolding are reflexivity.** §7 defines
  `⟦let x := v in b⟧` as `⟦b[v]⟧` and `⟦natLit n⟧` as its constructor spine,
  so both reductions have the same `Term` on each side. A step that costs
  nanoda a derivation costs mini nothing.
* **`try_eta_expansion_aux`'s dropped recursive half is unrepresentable.**
  The only way to obtain a `Conv` is to compose one, so a congruence cannot
  silently discard a side; it can only produce a named `Gap`.

### 0.3 The cache-key question, from the other side

*The census names "kernel-hypothesis evidence versus `ExprPtr`-keyed caches"
as the single genuine design decision, unsettled. Mini began with no caches,
so it could not answer directly — but it does have to answer "when are these
the same thing?", and the answer is informative.*

*(**Mini now has three caches, and the premise above is the Lean kernel mini
was ported from, not mini.** `wt_memo` keeps `whnf_typing`'s certificate;
`Checker::frames` keeps whole `Typing`s per telescope slot; the `Interp`
symbol tables were always there. The measured reason is in
`CERTIFYING-OVERHEAD.md` §4: on `nested_model`'s `iotaNode`, twelve million
consecutive `infer_type` entries produced **zero** new α-canonical judgements,
and across the tutorial corpus the two caches together removed **90.6%** of
all conversions with `gapped` at 0 and `constEv` at 218/218 throughout. The
no-cache premise bought a clean measurement of the re-derivation and then the
measurement said to spend it.*

*What the census actually asks is still answered the same way, and the frame
cache is the sharpest instance of the answer: an `ExprPtr`-keyed cache is
sound exactly when its key determines the judgement **including its context**.
`Checker::frames` gets that by construction rather than by canonicalisation —
it is keyed on the expression alone and **discarded when the telescope
changes**, so at a hit the opening is the same opening and the evidence's
kernel variables are the ones still open. That is why it can cache `ev` and
not merely `ty`. A key that crossed openings would need the α-canonical
closure and `Sealed` re-instantiation `CERTIFYING-OVERHEAD.md` §2 describes;
this one never crosses, and it is the cheaper half of the same insight.)*

Mini keys its three symbol tables (`LamSite`, `FibreSite`, `CondSite`) on the
**skeleton `Term`**, not on the expression. That is forced, not chosen: two
syntactically different Lean expressions with the same interpreted body shape
must share one graph symbol, and two occurrences of one Lean node in
different contexts have different holes but the same skeleton. An
expression-keyed table gets both wrong.

Extrapolating to conversions, which is the question #29 has to settle: the
natural key for "this is the same conversion" is the pair of **interpreted
terms** `(⟦a⟧, ⟦b⟧)`, not the pair of `ExprPtr`s. And the reason the two are
described as hostile is then visible: neither key records `Γ`. An
`ExprPtr`-keyed entry proved under `{w ∈ A}` is not a fact about `⟦a⟧ = ⟦b⟧`,
and nothing in the key says so. So the decision is not "hypotheses *or*
caches" — it is:

> **A conversion cache must either key on `Γ` as well as the endpoints, or
> store `Sealed` entries only.** The second is what mini's `Sealed` funnel
> (§4.3) already enforces at its one store, and it is the cheaper of the two:
> hypothesis-free conversions are exactly the ones worth sharing across
> declarations, and a `Γ`-carrying one is local to the binder that introduced
> it and is re-derived at zero cost from the scope anyway.

**Settled by measurement, 2026-08-01** (`mini/tests/tutorial.rs`,
`tutorial_conversion_split`), once `whnf` and `assert_def_eq` returned
conversions. Over every conversion the two were *asked for* on the 91 exports —
a decision-only call hands in no endpoints and states nothing, so those are not
counted:

| | conversions | hypothesis-free |
| --- | ---: | ---: |
| all | 1 039 457 | 1 039 427 |
| endpoints actually differ | 548 | 523 (95.4%) |

The second row is the one a cache exists for; a reflexivity is free to
re-derive. **25 of the 548 carry `Γ`, and every one is a beta step** — beta is
the only rule that consumes a membership, and everything else is reflexivity, a
stored defining axiom, or a congruence over those. The reason the ratio is so
lopsided is worth stating because it is not obvious: *reflexivity under a
binder carries no hypothesis*, even when its term mentions the binder's
variable, so a conversion being derived "under `Γ`" does not make it
`Γ`-dependent.

So the disjunction above stands and its second horn is the cheap one **by
measurement rather than by argument**: a `Sealed`-only store captures 95% of
the shareable conversions, and the 5% it refuses are exactly the ones local to
the binder that introduced them, which the scope re-derives at one vector
index. What remains inference rather than measurement is the extrapolation to
*nanoda*, whose reduction mix is not mini's.

(What is separately measured, and was measured before this: the *symbol* tables
must be interpretation-keyed, which mini's tests pin.)

### 0.4 A rule for whoever builds a gap ledger

*Added 2026-08-01, from getting it wrong first. This is written for task #29's
nanoda ledger, not only as a note about mini.*

> **A gap's reason must propagate from the sub-result that caused it, never be
> the failing clause's own label.**

Mini's first threaded ledger attributed **104 of 223 pairs** to
`Gap::PiTypingUnthreaded` — "the `Π` typing rule is not wired yet". That was
false for every one of them. The real cause was an uninterpreted inductive
constant several levels below, and the `Π` clause had simply stamped its own
eager label on a failure it did not cause. Fixing it moved those 104 into the
`no-interp(...)` rows and left the residue at 169 inductive constants and 13
projections, with nothing unattributed.

**The error is not cosmetic: it changes the category.** An uninterpreted
inductive is *interpretation scope* — work the design has not reached.
"Π typing unwired" is *threading debt* — work the design has reached and left
undone. A ledger that confuses the two reports the project as further behind on
threading than it is, and further ahead on scope, which is precisely the
distinction §0's two axes exist to keep apart.

Why nanoda is more exposed to this, not less:

* It has **three** attribution channels — `Admit`, `Dropped` and the escape
  ledger — each filled at its own site, so the same underlying cause can be
  labelled three ways depending on which one notices first.
* Its `Dropped` enum was already found to *understate*, because two drop sites
  were not in it at all. An enum that is not exhaustive cannot propagate: the
  missing sites have no label to pass upwards.
* Its clause structure is deeper, so the distance between the site that fails
  and the site that reports is larger.

The mechanical form of the rule, as mini implements it: a result that carries
no interpretation carries the **first** sub-result's gap
(`Checker::sub_gap`), and only a result that *did* interpret may report its own
clause's reason. That is the same "left gap wins" discipline `Ev::zip` already
uses for evidence, applied to interpretation as well — and the two should not
have different rules, which is how mini came to have the bug.

**A second round of the same mistake, and the sharper one.** When the
declaration pipeline started storing typings, `Gap::Axiom(name)` was the
fallback for "no typing", and **57 theorems were filed as model assumptions**.
That is worse than the `Π` case: "not derivable in principle" and "not derived
yet" are not merely different categories of work, they are on opposite sides of
the question of whether the work exists. The fix is the same rule — the reason
comes from whatever stopped the value, or failing that its type — and the
lesson is that a *fallback* is where §0.4 gets violated, because a fallback is
by construction the label of the site that noticed rather than of the cause.

### 0.5 The evidence ledger, by cause

**Read a zero row twice before believing it.** A row at zero means *either*
that the work is done *or* that nothing has reached it yet, and the ledger
does not distinguish the two — it counts what the traversal ran into, and a
declaration blocked at its first inductive constant runs into nothing further.
Five times now the second reading has been the right one: the library row was
zero before zone B's boundary existed; `threading-incompleteness` was zero
until `⟦Eq.rec⟧` reached the ι rule; `gapped` was zero until `PUnit` and `Eq`
had interpretations; `proj(Prod)` went 7 → 12 the moment `Prod`'s carrier
existed at `u := 1, v := 1`; and the `prop-inductive` row read as six pairs of
class-(P) work when five of them had a further gap they could not report until
the truncation carrier existed. The inference "this row is zero, so this is
not on the critical path" has been wrong every time it has been made.

*Added 2026-08-01, on completing the threading (`whnf → (E, Conv)`,
`assert_def_eq → Conv`, and the typing rules that consume them). This is the
deliverable §0's second axis was defined for, and the one nanoda cannot produce
today because its three attribution channels mix threading debt with library
debt.*

223 `(declaration, σ)` pairs over the 91 exports. Each asks for one thing,
`⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`. **Measured twice**: before zone B's boundary existed,
and after it landed (`mini/src/zoneb.rs`, the carrier and constructor half).

| outcome | before | after | axis |
| --- | ---: | ---: | --- |
| derived | 93 | **96** | — |
| uninterpreted inductive, recursor or projection | 123 | 84 | interpretation scope |
| a named `derived/` construction | 0 | **36** | library gap |
| an axiom's inhabitation | 7 | 7 | model assumption |
| **threading incompleteness** | **0** | **0** | — |
| mini bug | 0 | 0 | — |
| `Sealed::new` refusals at the store funnel | 0 | 0 | — |

**The library row is the finding, not the three pairs.** The "before" column
read: *nothing is waiting on a `derived/` construction, so the library backlog
is behind zone B on the critical path, not beside it.* The zero was real and
the inference from it was wrong. Nothing reached the backlog because nothing
reached anything — every declaration was blocked at its first inductive
constant, so the backlog was **invisible**, not behind. Build the boundary and
two named `derived/` items become the *first* thing a translated declaration
hits:

* **`cumul::sigma_n`'s per-field summand obligations** (27 pairs). `DeclUniverse` needs `⊢ [H →] Aᵢ ∈ U₁` per constructor;
  the closed route (`nullary_summands_in_u1`) covers a constructor with no
  *non-recursive* field, which is `Bool`, `Color`, `Empty`, `N`, `Nat` and
  nothing else in this corpus. `Prod`, `PProd`, `PSigma`, `List`, `TwoBool`,
  `TypeWithTypeField(Poly)` all have one, and their obligations are stated as
  `∀y⃗. (Dⱼ → βⱼ(p⃗,y⃗) ∈ U₁)` over the *declaration's own* parameter variables
  with `Dⱼ` a left-nested conjunction — while `Closed::discharge` produces the
  interleaved `∀y.(H → …)` shape. Bridging the two is `uncurry` plus one
  `gen_all`/`inst_all`, and it belongs in `scope.rs` beside `discharge`,
  because `implies_intr` is confined there by I1.
* **`cumul::Chain`'s `U₁` is hard-wired.** `Chain::over` and `IndChain::new`
  both set `u1` from `tower.at(1)`, and `DeclUniverse`, `tags_in_u1`,
  `summand_in_u1` and `IndexedUniverse` all read that one field.
  `Chain::assemble` does take a `Level`, and it is `pub(super)`. So there is no
  `⟦T⟧ ∈ ⟦Type n⟧` for `n ≥ 1` by any caller-side route — 9 pairs, and it is
  checked *before* the constructors are walked, so the reason reported is the
  one true of the declaration rather than whichever obligation was tried first.
  §7's guess about
  which cumul generalisation would bite was the wrong one: not the `B(a) ∈ ω`
  demand, which `DeclUniverse` has since discharged, but the level the chain is
  pinned at.

The 84 that remain scope are genuinely scope, and now say which:
`prop-inductive` 23 (class (S)/(P) — §5.3 or the truncation clause),
`indexed-family` 41 (`Eq` 29, `RBTree` 6, `Acc` 3, `SortElimProp` 2,
`SortElimProp2` 1), `recursor` 7, `fun-typed-rec-arg` 4 (`RTree`), and 9 for
`quot` and `natLit`.

The zero in the threading row is the claim this exercise existed to establish,
and it is a *ratchet* (`tutorial_evidence_ledger`), so a later change that
re-introduces threading debt fails a test rather than quietly widening a row.

**The ratchet has since moved off zero, once, and the mechanism is the same one
this section is about.** `mini/src/recursor.rs` put `⟦Eq.rec⟧` in the store;
`094_ruleK`, which had been blocked at `recursor(Eq)`, then got one step
further and stopped at the ι rule — `Gap::Iota`, correctly threading, because
every piece of that step exists and `whnf`'s recursor arm hands it no
certificate. It is pinned at **1**, and pinned *by name* (`iota(Eq.rec)`)
rather than by a relaxed bound, so a second threading pair still fails the
test. A row that reads zero because nothing reaches it is not a row that reads
zero because nothing is owed — the same inference this section corrects for the
library column, one column over.

Mini is measured on two independent axes, and conflating them is the mistake
to avoid:

* **Acceptance fidelity.** Mini-rust must accept/reject each of the 91
  tutorial exports exactly as mini-lean does (mini-lean accepts all 91; it and
  the suite were co-developed — owner's statement), **or decline it by name
  with a reason**. Two are declined: `031_letTypeDep` and `032_letRed` declare
  axioms of their own **and refer to them**, and no work anywhere can derive
  their inhabitation (`mini::convert::is_standard_axiom`, narrowed to the
  referred-to ones by `mini::unused_axiom`). This axis is about the *port* being
  correct and is reachable early.
* **Evidence completeness.** Every accepted step carries a real kernel
  derivation — zero gaps on the 89 mini still checks. This axis was described as "gated on the
  `derived/` library backlog (§10), not on threading: mini has no threading
  debt *by construction*". **The first half of that is now measured and the
  second half was optimistic.** Mini did have threading debt — three named
  gaps, and several unnamed ones the ledger surfaced — and it took building
  the threading to remove it; "by construction" was a statement about the
  design, not about the code. What is true, and is now measured (§0.5), is
  that the residue *once the threading is done* is a pure scope-and-library
  worklist with nothing unattributed. That is the deliverable nanoda cannot
  produce today, because nanoda's ledger mixes threading debt with library
  debt.

"89 of 89 at zero gaps" is the joint endpoint of this port **plus** the named
library items in §10 — 89 rather than 91 because the two exports that declare
their own axioms are out of scope, by the argument in §0.6. The port alone
gets: the 27-file inductive-free fragment at zero gaps (all lemmas for it
exist — nanoda already holds that fragment at zero **[read, README
§Coverage]**), acceptance fidelity on all 91, and a gap ledger that is a to-do
list rather than a diagnosis.

### 0.6 Blocking, and what is out of scope

*Added 2026-08-02.*

§0.5's table sizes the work. It does not **order** it, and a run that files a
gap and carries on files eighty-two more behind it, each of which may exist
only because the first one does. So mini has a second mode, and it is the one
to reach for when the question is "what now":

```text
mini --block <export.ndjson>          # exit 3, and the report on stdout
cargo test -p mini --test tutorial first_blocker -- --nocapture
```

Armed, the interpretation pass stops at the **first** `(declaration, σ)` whose
obligation it cannot discharge. The vocabulary does not change: the reason is
the same `Gap` the ledger would have counted, spelled with the same
`Ledger::key` string, so a blocker and a `waiting:` row name the same thing.
What is added is the *provenance* — the source location that gave up, with the
line, obtained from `#[track_caller]` on `Ev::missing` — and the *statement*:
the obligation written out at the Lean level, where `⟦·⟧`'s argument is exact,
beside what was in hand at the kernel level.

**Four obligations, in dependency order**, and the first one missing stops the
run: inference itself, then `⟦ty[σ]⟧`, then `⟦val[σ]⟧`, then
`⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`. The type's *own* typing `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` is
deliberately not among them — it is reported, not blocked on — because
stopping on a sub-obligation nothing downstream consumed would stop on
something that is in no one's way. That this never *hides* a hole is measured
rather than argued: `Ledger::type_ev_only_gap` counts the pairs whose constant
typing derives while the type's typing does not, and it is **0** on the corpus.

That zero is a fact *about the corpus*, not a structural one, and
`mini/tests/fixtures/beyond_the_tower.lean` is a file where it is **1**: a
declaration at `Type 30 → Type 30` gets its constant typing and not its type's
own, because the arrow's sort is above `CUMUL_HEIGHT`. `--block` therefore runs
that file to the end and reports no blocker while a real obligation is owed —
which is a statement about what the blocking *mode* is for, and the reason §0.7
exists. Blocking answers "what do I fix next"; it was never the instrument for
"is this run certified".

**A user-declared axiom is out of scope, and is declined.** An axiom's
inhabitation is a model assumption: nothing in `derived/` can ever discharge
`⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` for a symbol the model says nothing about, so a run that
stops at the first missing derivation would stop there for ever. Lean's own
three — `Quot.sound`, `propext`, `Classical.choice` — are a different case:
the set-theoretic model *validates* them, so each is a `derived/` obligation
and stays in scope. `mini::convert::is_standard_axiom` is the line.

**One narrowing, `#121`.** The argument above is about a symbol something in the
file *depends on*. An axiom **nothing in the file refers to** opens no pair, so
there is no `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` to be stuck at and nothing to be evidence for;
it is ignored — dropped **before** the per-declaration loop, so it is never
added and never interpreted, and named on the verdict line so the skip is
visible. `mini::unused_axiom` states what "refers to" covers and why one pass
rather than a fixed point.

The drop used to sit *after* a whole-file kernel pass, which checked such an
axiom's **type** on the way past; `mini::decl_pass` has no whole-file kernel
pass to sit after, and the owner waived the lost rejection ("it will not
complain about the type of a dropped axiom; that's not a concern").
`mini/tests/designed.rs`'s `an_unused_axiom_may_now_be_illtyped` is the waiver
as a fixture, so the difference is measured rather than described. The
**used**-axiom decline keeps its ordering — it must lose to any rejection — by
being issued after the loop rather than before it.

**`Cause::Assumption` is therefore retired**, and the retirement is what the
decline buys. Once the boundary is enforced at the frontend, the only axioms
left are ones the model validates, so `Gap::Axiom` names a *construction*
(`Cause::Library`) rather than a postulate, and a `Cause::Assumption` could
only be reached through a hole in the decline. A cause reachable only by a bug
is better spelled as its absence than as a row pinned at zero.

`Gap::Axiom` is also reached **only once the axiom's type has interpreted**.
It used to fire unconditionally on any axiom, ahead of the check on the type,
which is §0.4's mistake one step in: being an axiom says nothing about *why* a
typing is missing when the statement itself did not interpret.
`123_quotSoundType` decided it inside one file — `quotSoundType`'s value is
literally `Quot.sound.{u}`, and the two copies of one obligation were filed on
two different axes.

The decline happens **after** the kernel has accepted the file, not in the
parser, and the position is load-bearing: four `bad/tutorial` fixtures declare
a helper axiom ahead of the ill-typed declaration they exist to catch, and
declining at the parser turns four rejections into declines — a weaker claim,
made silently, on the axis that is supposed to be exact.

### 0.7 The certification axis is in the default verdict

*Added 2026-08-04.*

§0's two axes were not equally visible. A bare `mini export.ndjson` printed
`accept N declarations` and exited `0` whether or not every obligation had been
discharged; the certification axis lived in the `evidence` and `convs` rows and
printed **only** under `--verbose`. For a project whose claim is *every
definitional-equality conclusion carries a certificate*, a silent `accept` on a
partially-certified run is the wrong default, so both axes are now in the
verdict.

| code | meaning | axis |
|------|---------|------|
| `0` | accepted, everything translated, every obligation certified | both |
| `1` | rejected — the file is ill-typed | acceptance |
| `2` | **arena decline** — a feature mini does not support; also a usage error | acceptance |
| `3` | blocked — `--block` only (§0.6) | neither |
| `4` | accepted, and something is uncertified **or untranslated** | certification |

`4` is not a verdict about the file — the file was accepted — which is why it
does not reuse `1` or `2`. A clean run's verdict line is unchanged; a run with
debt grows one or two columns, `untranslated: 1 declaration` and/or
`uncertified: 1 type typing, 3 conversions`. `--acceptance-only` restores
`Main.lean`'s three codes, for a run that genuinely compares type checkers and
nothing else; `scripts/mini-vs-nanoda.sh` is the call site that needs it.

**`2`'s population is the arena's contract and does not grow.** It is the
kernel arena's code for an *unsupported feature* at file level: two corpus
exports declaring a non-standard axiom their own declarations refer to (`031`,
`032`) and mutual inductives at the parser. A declaration mini could not translate inside a file it accepted is
**not** one of these — it is a `4`. The word "decline" was doing both jobs and a
brief written from the wrong sense nearly routed the second to exit `2`;
`mini/src/zoneb.rs`'s header now separates the three senses, and the internal
notion is spelled **untranslated** everywhere it is reported.

**A run to completion, not a stop at the first gap.** `--block` is unchanged
and keeps exit `3`: it is the development affordance — fix one thing,
re-measure — and its counters are partial by design. The default runs to the
end and reports the whole picture, which is what a user asking "is this
certified" wants in one run.

**What makes a run uncertified**, and this is the definition of the claim, so
it is asserted in `ledger.rs`'s `uncertified_is_exactly_these_four_counters`
rather than only written here:

* `pairs − constEv` — the headline obligation `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`. Every
  `waiting:` row and every interpretation gap arrives here, so `Ledger::missing`
  sums to it and is an attribution rather than a separate debt.
* `pairs − typeEv` — `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧`. **Not** implied by the line above,
  and `beyond_the_tower` is the witness: `constEv = 2`, `typeEv = 1`. A
  definition watching only constant typings would call that run clean.
* `ConvStats::gapped` — a conversion that reached its reduct with no
  certificate: the claim's own sentence, negated. Independent of both lines
  above.
* `Ledger::unsealed` — zero on a correctly threaded run by I2, so a nonzero
  count is a bug; reported on its own line rather than folded into the first,
  which it also moves.

Deliberately **out**: `sealed < proved` and `movedSealed < moved`, which are
nonzero on a legitimately clean run — 9 443 of the corpus's 11 578 061
conversions carry kernel hypotheses, which is what §0.3 measured the ratio
*for*, and certification is "a certificate exists", not "a certificate is
shareable". Also out: `type_ev_only_gap` and `type_ev_masked`, strict subsets
of `pairs − typeEv` that would double-count, and the `blocked`/`missing`/
`gapped_by` maps, which attribute counts already in the set.

**The hole this list had, and the second set that closes it.** *Corrected
2026-08-05; the paragraph here read "One hole, stated rather than papered
over", and it was right about the hole and wrong that it was only vacuity.*
`Ledger::run` opens no pair for a `Declaration::Inductive` or
`Declaration::Quot`, so every counter above is a **shortfall against `pairs`**
that such a declaration cannot move. That is not merely a file certifying
vacuously: `113_reduceCtorParamRefl` printed `accept 3 declarations`,
`pairs=2 constEv=2 typeEv=2 gapped=0 unsealed=0`, exit `0`, while carrying an
inductive mini had **recorded** that it could not translate.

So the certification axis has a second set, `ledger.rs`'s `Untranslated`, and
the invariant is written where the set is defined:

> No run reports clean while the tool knowingly did not translate something.
> `Uncertified` covers everything the ledger *asked* for; `Untranslated` covers
> everything mini *recorded a refusal for*. A run exits `0` only when both are
> clean.

It counts the three tables `zoneb` records a reason in — a whole declaration
(`IndApparatus::untranslated`), one indexed family's constructor
(`ctor_untranslated`), an eliminator waiting on a `derived/` construction
(`rec_untranslated`) — and prints `untranslated: N declarations, …`.

**Two sets and not five counters**, and the reason is the property above:
`Uncertified` is closed under new gap kinds *because* it enumerates obligations,
and a fifth counter for something that is not an obligation would buy the number
at the cost of the rule. The two may overlap — a use of an untranslated
declaration also owes a constant typing — and they are never summed, so it is
not double counting. `Untranslated` has a closure guard of its own:
`Untranslated::of` is the single reader of the three tables, and
`a_recorded_refusal_reaches_the_verdict` populates each alone and asserts the
verdict moves.

The measured population is three, over all 91 exports: `113`/`114` refuse
*correctly* and permanently (`bnd(Σ(z::α))` is refutable at `α := ⟦Nat⟧`, so a
function-typed recursive argument over an unbounded parameter has no bounded
fibre), and `052_reduceCtorParam`'s eliminator is **pending work**. That third
one is the answer to "is the silence wider than the case that found it": it is,
and the entry nobody had noticed was the one that is not permanent.

---

## 1. Crate layout

> **Historical, and this section in particular is read as a map when it is not
> one.** `lib.rs` lists 42 modules against the ten below.
> **`mini/src/inductive.rs` never existed** — zone A lives in `mini/src/kernel.rs`
> (`add_block`), so the bullet naming it is the one most likely to send a reader
> looking for a file. **`MiniEnv` never existed** either: `env.rs` holds
> `Environment`/`Declaration`/`ConstantInfo`, and the interpretation store is
> `interp::Interp`. `interp.rs` has no submodules; it is one file. The
> dependency key is `nanoda_lib = { path = "../checker" }`, not `checker`, and
> `serde_json` is missing from the list. Everything else below exists with the
> name given.

New workspace member `mini/`, untrusted, beside `checker/`:

```toml
# Cargo.toml (workspace): members = ["kernel", "derived", "checker", "mini"]

# mini/Cargo.toml
[dependencies]
kernel  = { path = "../kernel" }
derived = { path = "../derived" }
checker = { path = "../checker" }   # parser + instantiations only; see §2
```

* `mini/src/expr.rs` — `Name`, `Level`, `Expr` (owned, de Bruijn), `shift`,
  `substs`, `subst_level`, ground-level evaluation. Ports of
  `MiniKernel/Types.lean` + `ExprUtils.lean` + the `Expr` helpers at the top
  of `Kernel.lean`.
* `mini/src/convert.rs` — `ExprPtr → mini::Expr` conversion and the
  declaration schedule (§2, §3).
* `mini/src/scope.rs` — binder open/close; the **only** module that calls
  `Thm::assume`/`Thm::implies_intr` (§4).
* `mini/src/interp.rs` (+ submodules) — `⟦·⟧` against `mini::Expr`: the §6.2
  clause dispatch, skeleton handling, sort tower, per-`(name, levels)`
  constant interpretations (§7).
* `mini/src/kernel.rs` — the port of `Kernel.lean`'s mutual block, with the
  signatures of §6. One file, like the original.
* `mini/src/env.rs` — `MiniEnv`: syntactic `ConstantInfo` store (port of
  `Types.lean`) plus the per-instantiation interpretation store, all
  certificates `Sealed` (§4.3, §8).
* `mini/src/inductive.rs` — the declaration-shape zone: mini-lean's inductive
  checks and recursor generation, ported verbatim (§9).
* `mini/src/blocker.rs` — the **abort at the first missing derivation** (§0.6):
  the gap mint trail, the report, and the term rendering it needs.
* `mini/src/main.rs` — reads one `.ndjson` export, prints the verdict and the
  gap ledger in the same row format the corpus harness scrapes; `--block`
  prints the first blocker instead and exits 3.
* `mini/tests/tutorial.rs` — the 91-export harness (§11).

Depending on `checker` is deliberate and safe: `checker` is a library crate
whose `lib.rs` already exports `parser`, `util`, `instantiations`, `level`,
`env`, `expr` as `pub mod` **[read, `checker/src/lib.rs`]** — no refactor is
needed, which keeps the hard constraint of §2. Mini does not enable or touch
the `tg`/`stepcount` features and never calls into `tc.rs` or `tg.rs`.

Trust story: unchanged. `mini` constructs `Thm`s only through `kernel`'s
rules; a mini bug is a wrong verdict or a rejected derivation, never a false
theorem. `ci/check-boundary.sh` continues to guard `kernel/` exactly as
before; §4.4 states the hypothesis-discipline rule that replaces rule 6.

---

## 2. Parser reuse: `ExprPtr → mini::Expr`

**Superseded — mini and `checker` now share the representation.** What
follows described the owned-tree `Expr` mini converted *into*; PIVOT.md §1.1's
migration removed the conversion, and `mini/src/arena.rs` is the seam. Mini's
`Name`, `Level` and `E` are `checker`'s `NamePtr`, `LevelPtr` and `ExprPtr` —
hash-consed, `Copy`, and read through `view()`. The variant names below are
still the ones `view()` hands back, and every note under the listing still
holds; only the `Rc`s are gone. Two other things changed with it: `checker/`
*is* now edited, minimally and with citations (PIVOT.md §6 inverts the old
rule), and the converter no longer runs inside `ExportFile::with_ctx` — it
installs the export file as the one arena, because two contexts would make
two incomparable pointers for one name.

The public path is still `Config::to_export_file()` → `ExportFile`, walked
with `read_expr` / `read_level` / `read_name` / `read_levels` /
`read_bignum` / `read_string` **[read, all `pub` on `TcCtx`]**:

```rust
pub enum Expr {
    BVar(u32),
    Sort(Level),
    Const(Name, Rc<[Level]>),
    App(Rc<Expr>, Rc<Expr>),
    Lam  { ty: Rc<Expr>, body: Rc<Expr> },
    Pi   { ty: Rc<Expr>, body: Rc<Expr> },
    Let  { ty: Rc<Expr>, val: Rc<Expr>, body: Rc<Expr> },
    Proj { ind: Name, idx: u32, s: Rc<Expr> },
    NatLit(u64),          // > 10 rejected at conversion, as mini-lean's parser does
    StrLit(Rc<str>),      // kept inert, as in mini-lean; no reduction rule
}
```

Notes, each matching a mini-lean decision **[read, `Types.lean`,
`Parser.lean`, `Kernel.lean`]**:

* No `Local` variant and no binder names/styles: mini is pure de Bruijn;
  **and this is now enforced rather than incidental** — `checker` hash-conses
  binder names and styles into the node, so `mini/src/arena.rs` pins them to
  one value on everything mini builds and `convert::Cv::expr` normalises every
  parsed expression to match. Without that, `==` on expressions would start
  distinguishing spellings. See that module's header;
  export files contain no locals (nanoda mints them only during checking), so
  the converter never sees one. Binder names are dropped (mini-lean keeps a
  `Name` for printing; carry it only if the error messages want it —
  irrelevant to checking).
* `NatLit > 10` → the whole export is declined, mirroring mini-lean's parser
  guard and the `whnf` re-check. `NatLit ≤ 10` is kept as a constructor and
  unfolded lazily in `whnf` exactly as mini-lean does (`natLit` clause of
  `whnf.go`), *not* eagerly expanded at conversion — smaller behavioural
  distance to the original, and the unfolding step's certificate is free
  (§6.4).
* Declarations: convert `axiom`, `def`/`theorem`/`opaque`, `quot`,
  `inductive` to mini's `Declaration` (port of `Types.lean`). **Recursor and
  constructor declarations in the export are converted for the schedule
  (§3) but not fed to `Environment.add`** — mini-lean's parser discards
  recursor info (`parseRecInfo` is a stub **[read, `Parser.lean:375`]**) and
  generates its own recursors; constructors arrive inside the `inductive`
  declaration. The converter must *check* (not assume) that the export's
  recursor for `T` is named `T.rec` and that its level parameters are the
  motive parameter followed by `T`'s own, which is the order mini-lean
  generates (`v :: lparams` **[read, `Kernel.lean`, recursor generation]**);
  a mismatch is a decline with its own counted reason.
* Mutual/nested inductives, unsafe declarations: decline at conversion, as
  mini-lean's parser does **[read, `Parser.lean:339–341`]**. These do not
  occur in the tutorial corpus (owner's scope statement).

Cost estimate: ~200 lines, no unsafe, no checker changes. The one alternative
considered — extracting the parser into a shared crate — is rejected exactly
as the task states: `README.md` advertises that the instrumentation diff is
`git diff nanoda-upstream/master -- checker/` **[read, README §Layout]**, and
an extraction would put upstream parser code outside `checker/` and make that
command lie. The constraint is right, not merely respected: the diff claim is
the fork's audit story.

---

## 3. The level pre-pass

Reused, not reimplemented. `checker::instantiations::Instantiations::compute
(&ExportFile)` is `pub`, as are `for_name` and `Inst = Vec<u32>`
**[read, `instantiations.rs`]**. The constructor-type edge case for
`Declar::Inductive` — the gap `WIRING-DESIGN.md` §7.3 found — is already
landed in pass A **[read, the commented `Declar::Inductive` arm in
`compute_in`]**, so the schedule mini gets is the one nanoda audits at zero
misses.

Mechanics:

1. Parse the export once with `checker`'s parser. Run
   `Instantiations::compute` on the `ExportFile`. While still inside
   `with_ctx`, for each declaration read its schedule via `for_name` and emit
   `(mini::Declaration, Vec<Inst>)`. After this, the arena is dropped; mini
   holds only owned data. `DEFAULT_LEVELS = [0, 1]` and the
   literal-expansion seeds come along for free — same code, same schedule,
   which is itself an agreement point with nanoda (§11).
2. Ground substitution is mini-side and trivial: `Expr::subst_level_ground
   (uparams, σ)` replaces each parameter with `succ^{σᵢ}(zero)`; the ground
   evaluator `Level::eval → u32` mirrors `instantiations::eval` (numerals:
   `max` is max, `imax(_, 0) = 0`, else max). ~30 lines, pinned by a test
   against `checker::instantiations`' documented semantics.
3. The checking loop is: declarations in file order; for each, every σ in its
   schedule (checked and stored per (name, σ)). A constant occurrence inside
   a σ-ground declaration has ground level arguments; its interpretation is
   looked up at `(name, evaluated levels)`. **A lookup miss is mini's
   unpredicted-instantiation audit row** — counted, reported, and pinned at
   zero by a test, mirroring nanoda's row (README §Coverage).

Why per-σ is not optional: `⟦·⟧` is not defined at a declaration's own
parameters — `imax u v` at a parameter is neither §6.2 clause
**[read, `instantiations.rs` module doc; README §Coverage, "third case"]**.
Mini inherits the strategy wholesale. Two places symbolic levels survive, and
both are handled the same way nanoda handles them:

* The **inductive declaration-shape zone** (§9): mini-lean checks inductive
  declarations at their own `lparams` (positivity, ctor universe bounds
  `assertLevelLe u indLevel`, `defEqParams`). These checks stay at symbolic
  levels for acceptance fidelity and are the one sanctioned evidence-free
  zone (the analogue of nanoda's `inductive.rs`, which the census §1.7 rules
  "correctly unthreaded" — their judgements have no backend consumer; the
  evidence for constructor/recursor typings comes from `derived::inductive`
  per ground instantiation instead).
* The **generated recursor's** motive parameter. Mini-lean sanity-checks
  `recType` at symbolic levels (`checkType recType`); mini-rust drops that
  symbolic sanity check and instead checks the recursor at every σ its
  schedule demands, which is the same rigor at ground levels. (The recursor
  appears in the export file, so the pre-pass schedules it; §2's name/order
  check is what entitles mini to use that schedule for its *generated*
  recursor.)

`Level.le` (the balance algorithm with `byCases` on `imax`-at-parameter) is
ported verbatim from `Kernel.lean`. `LevelProofs.lean` proves it **correct
but incomplete** **[read]**: the pinned counterexample is
`succ (param p) ≤ max (succ zero) (imax (succ (param p)) (param p))` — valid
in every valuation, `le` says false. Can it bite? Incompleteness only ever
*rejects*, never accepts wrongly, so soundness is untouched. On mini-rust's
hot path it is dead: every `assertLevelEq`/`assertLevelLe` in the per-σ
checker runs on ground levels, where `le` is exact. The only symbolic uses
are in the shape zone (above), where mini-lean lives with the same procedure
and passes all 91 — so verdict fidelity is preserved by porting it unchanged.
(This also retires, for mini, nanoda's "level algebra" admit family: at
ground σ, level equality is *decided* by `le` and the certificate is
reflexivity of an identical interpretation.)

**A ground level is not syntactically a numeral, and an earlier revision of
this section said it was** — "where `simplify` yields `succ^n zero` on both
sides", and "level equality is syntactic equality of numerals". Both are
false, and code written to them would be wrong: `Level.mkIMax(a, succ b)` is
`Max(a, succ b)`, and `simplify` never collapses a `Max` of numerals. So
`imax u v` at `σ = [1, 2]` simplifies to `max(succ zero, succ (succ zero))`,
not to `succ (succ zero)`. What is true, and is all that is needed, is that
`Level.le` *decides* ground levels exactly, so `assertLevelEq` between a
ground level and its numeral always succeeds. **Consequence for §7: the
interpretation must evaluate a level with the numeric evaluator (mini's
`ground::eval`, mirroring `instantiations::eval`) and must never pattern-match
a simplified level for `succ^n zero`.** Pinned by
`mini/src/ground.rs`'s `grounding_decides_exactly`.

---

## 4. The hypothesis discipline — binder open/close

This is the design's heart, and it is stated as the positive discipline of a
clean-slate consumer of a sequent kernel — not as a carve-out from
`ci/check-boundary.sh` rule 6. (Per the project owner: rule 6 is not a
soundness rule; it shields two engineering weaknesses — `Thm::gen`'s
infallible signature and `concl()`-without-`hyps()` reads — which task #30
fixes, after which the rule is deleted. `Thm::assume` and
`Thm::implies_intr` are ordinary kernel rules **[read, `thm.rs`: `assume` is
`{φ} ⊢ φ`, valid by inspection; `implies_intr` is the deduction theorem as a
rule]** and mini uses them as such.)

### 4.1 Open

Mini-lean's `openType type k` pushes a type on the telescope. Mini-rust's
counterpart also acquires the typing hypothesis, once, at the open:

```rust
// mini/src/scope.rs — the only module that names Thm::assume / Thm::implies_intr.
pub struct Scope {
    ty: Expr,        // the domain, indexed in the enclosing context
    dom: Term,       // ⟦ty⟧, interpreted once at the open
    w: FreeVar,      // the kernel variable interpreting bvar 0 under this scope
    hyp: Formula,    // mem(Term::var(w), dom)
    assumed: Thm,    // Thm::assume(hyp)  —  {w ∈ ⟦A⟧} ⊢ w ∈ ⟦A⟧
}

impl Checker<'_> {
    /// `openType`: push. Interprets `ty` in the *current* context first.
    fn open_binder(&mut self, ty: &Expr) -> Result<ScopeToken>;
    /// Pop; the token forces pairing. Returns the closer, which owns the
    /// discharge.
    fn close_binder(&mut self, tok: ScopeToken) -> Closed;
}

impl Closed {
    /// From Γ ∪ {w ∈ ⟦A⟧} ⊢ φ  produce  Γ ⊢ ∀w. (w ∈ ⟦A⟧ → φ).
    /// implies_intr(hyp) then gen_checked(w). `gen_checked → None` is an
    /// internal error (see invariant I2), not a user-visible rejection.
    pub fn discharge(&self, thm: &Thm) -> Result<Thm>;
    /// The hypothesis, for rules that consume it directly (e.g. the typing
    /// of `bvar 0` is exactly `self.assumed`).
    pub fn assumption(&self) -> &Thm;
}
```

`⟦bvar i⟧ = Term::var(scopes[i].w)`, and the typing of `bvar i` is the stored
`assumed` theorem — **zero cost, no acquisition per consumer, no
`local_premises` guessing**. This is precisely the constant-cost context the
sequent judgement was introduced to provide (`thm.rs` module doc: the
`13u² + 73u − 134` measurement against formula-level antecedents **[read]**),
and it is what replaces the whole `CondEq`/`guard_and_generalise_at` layer:
`Closed::discharge` *is* `guard_and_generalise_at`, performed by two kernel
rules instead of a formula-surgery module.

### 4.2 The shape `discharge` produces is the shape the library consumes

Not a coincidence, a design fact: the λ-typing lemmas (`lam_in_funspace_n`,
`lam_in_dprod_n`), the congruence lemmas (`lam_ext_n`, `dprod_ext_n`,
`cond_ext_n`) and `prop::cond_intro` all take their under-the-binder premise
as `∀w. (w ∈ A → …)` — verified for the derived originals
(`derived::ext::lam_in_funspace` et al.) and asserted by the tg.rs module doc
for the n-ary ports **[read, tg.rs module doc, "Lambdas" and beta sections]**.
So the pipeline under every binder is: open → work with hypotheses riding in
`Γ` at zero per-step cost → `discharge` at the close → feed the
`∀`-`→`-shaped family to the lemma. Nothing is re-proved against a merged
hypothesis set, ever.

### 4.3 Persisting: `Sealed`

```rust
/// A theorem with no hypotheses. The only constructor checks it.
pub struct Sealed(Thm);
impl Sealed {
    pub fn new(t: Thm) -> Result<Sealed, Thm> { /* t.hyps().is_empty() */ }
    pub fn thm(&self) -> &Thm;
}
```

`MiniEnv`'s interpretation store (§8), the per-`(name, σ)` constant typings,
defining equations, iota rules, and the final per-declaration verdict funnel
hold `Sealed` only. This is the type-level form of `thm.rs`'s "hyps()
obligation": *a `Thm` establishes its conclusion only when `hyps()` is
empty*. The `Sealed` funnel enforces it at mini's one store.

*(This read "Mini has no expression-level caches at all (its one store is the
environment), so the cache-imports-Γ hazard that motivated nanoda's
`is_unconditional`/`hypothesis_free` guards is structurally absent — but the
`Sealed` funnel enforces it anyway, because 'no caches' is a fact about
today's mini, not a property of the repo." The last clause was right and the
day came. `Checker::frames` caches `Typing`s whose evidence **does** carry
`Γ` — 87% of what it removes is Γ-carrying, against 10% for `wt_memo` — so
the hazard is no longer structurally absent and the funnel is no longer
belt-and-braces. What keeps it safe is not hypothesis-freedom but scope
identity: a frame is dropped when its telescope changes, so a cached
hypothesis is one the current scope still has open. The `Sealed` gate remains
where it was, at the store that outlives a scope; the frame never does.)*

### 4.4 The invariant, stated as an enforceable rule

This is offered as rule 6's successor, for mini now and for nanoda when
stage 1 of the census lands:

> **R6′ (hypothesis discipline).**
> **I1 — single introduction point.** `Thm::assume` and `Thm::implies_intr`
> are called only in the scope module (`mini/src/scope.rs`; in nanoda, the
> stage-1 equivalent). *Grep-enforceable exactly as rule 6 is today, with a
> path allowlist instead of a ban.*
> **I2 — hypotheses are scoped.** At every point of execution,
> `thm.hyps() ⊆ { hyp of each currently open Scope }` for every live `Thm`,
> and scopes are opened/closed LIFO. Consequences: the innermost scope's `w`
> is free in no *other* scope's hypothesis, so `discharge`'s
> `gen_checked` cannot fail; enforced by `debug_assert` at `close_binder`
> and by `ScopeToken` being non-`Clone` and consumed by `close_binder`.
> **I3 — no panicking generalisation.** `Thm::gen` (the panicking wrapper)
> is never called outside `kernel/`; `gen_checked` is the only entry.
> *Grep-enforceable: forbid `Thm::gen(`.*
> **I4 — persistence requires emptiness.** Anything stored beyond the
> current declaration check, compared as a final conclusion, or reported as
> a verdict passes through `Sealed::new`. *Enforceable by the store/report
> modules' signatures mentioning `Sealed` and never `Thm`, checkable by
> grep; and by I2, since at top level no scopes are open, `Sealed::new`
> cannot fail on a correctly-threaded run — a failure is a threading bug
> surfaced at the funnel, which is where you want it.*

What this buys over rule 6: the two hazards rule 6 shielded are addressed at
their sites (I3 for the panic, I4 for the `concl()` reads) instead of by
banning the feature that makes constant-cost contexts possible.

---

## 5. Evidence types and the gap policy

```rust
/// Evidence, or a named absence. No third state, no retry, no search.
pub enum Ev { Proved(Thm), Gap(Gap) }

/// Every way evidence can be missing, as an enum — a new hole cannot be
/// introduced without naming it (same policy as checker's Admit/TyGap).
pub enum Gap { NoInterpretation(Name, Inst), IndexedFamily, FunTypedRecArg,
               StructProj, StructEta, UnitLike, FunEta, Iota, StrLit,
               Axiom(Name), SymbolicLevel, SortTowerHeight,
               // threading: absent by construction once a rule is wired
               NoEndpoint, NotDecomposable, BinderCongruence,
               NoDefiningEquation(Name),
               // mini bugs, which are neither axis
               Skeleton, Classifier, EndpointDrift, ConvCompose(&'static str) }

/// Which of §0's axes a gap belongs to, so the ledger cannot conflate them.
pub enum Cause { Scope, Library, Threading, Assumption, Bug }

pub struct Typing { pub ty: Expr, pub tm: Option<Term>, pub ev: Ev }
    // ev: Γ ⊢ mem(tm, ⟦ty⟧)   where tm = ⟦subject⟧, Γ per I2
    // and ⟦ty⟧ is read off ev.concl() — a Typing carries it inside its
    // evidence, not as a field (§6.4)
pub struct Conv   { pub to: Expr, pub ev: Ev }
    // ev: Γ ⊢ ⟦from⟧ = ⟦to⟧   (endpoints carried by the caller)
```

Policy, and how it differs from nanoda's:

* **Gaps propagate monotonically** — composing with a `Gap` yields that
  `Gap`. There is no `Dropped` ledger because nothing is discarded (a
  consumer either exists and takes the evidence, or the evidence is an
  acceptance gate with no downstream consumer, which is fine — see the
  `let` rule, §6.3). There is no `Admit` funnel with a retry search because
  there is no search.
* **`Err` vs `Gap` is the acceptance/evidence split of §0.** `Err` = the
  declaration is rejected (type error) — must match mini-lean. `Gap` = the
  declaration is accepted but a derivation is missing — must reach zero.
  A rejection needs no evidence (the licensing-branch principle, confirmed
  by the census for every negative branch).
* At 89/89-zero-gaps, `Gap` is dead code on the corpus, and the enum is the
  proof of *what* was needed to get there. *(The corpus is there —
  `constEv = typeEv = 218`, `gapped = 0`, `unsealed = 0` — and `Gap` is **not**
  dead: three exports still carry `Untranslated` rows, and
  `Gap::Recursor`/`Gap::IndexedCtor` are minted with a carried `Cause`. The
  variant listing above has drifted hard — roughly eleven variants renamed or
  gone and eleven new ones — and `Cause::Assumption` is retired, which §0.6
  records and this section does not. `mini/src/ev.rs` is the enum.)*

---

## 6. The signatures — `Kernel.lean`'s mutual block, threaded

The core deliverable. Layout mirrors `Kernel.lean` one-to-one so the port can
be reviewed against the original function by function. `Checker` bundles
`&mut MiniEnv`, the scope stack, and the interpreter; all functions are
methods on it. `Result` is rejection (§5).

### 6.1 Context primitives

| mini-lean | mini-rust | evidence |
| --- | --- | --- |
| `getLocalType idx` | `fn local_typing(&self, idx: u32) -> Result<Typing>` | `ty` = `lenv[idx]` shifted (as in the original); `ev` = the scope's stored `assumed` — `Γ ⊢ ⟦bvar idx⟧ ∈ ⟦ty⟧`, zero derivation cost |
| `openType` / close | `open_binder` / `close_binder` / `Closed::discharge` | §4.1 |
| `openTypes` (non-dep telescope) | `fn open_binders(&mut self, tys: &[Expr]) -> Result<Vec<ScopeToken>>` | n opens; used by recursor generation (shape zone) |
| `readLocalTypes n` | shape-zone helper, no evidence | consumed only by recursor generation |
| `sort e` / `assertIsSort` | `fn as_sort(e: &Expr) -> Result<Level>` | pure shape; licenses nothing by itself (the licensing facts about sorts are the tower memberships, produced where consumed) |

### 6.2 `inferType`

```rust
fn infer_type(&mut self, e: &Expr) -> Result<Typing>
```

Postcondition: `Γ ⊢ ⟦e⟧ ∈ ⟦T⟧` with `Γ` per I2. Clause by clause (each names
its mini-lean original and the derivation that composes the evidence — the
derivations are the same rules `tg.rs` already implements as its `ty_*`
consumers, with the search half absent by construction):

* `.bvar` → `local_typing`. (nanoda: `ty_local`, minus the "acquire the
  antecedent per consumer" fallback — the scope already holds it.)
* `.const name levels` → levels are ground (§3); look up
  `(name, eval(levels))` in the interpretation store; `ev` is the stored
  `Sealed` typing (weakening a hypothesis-free theorem into Γ is free — it
  is the same `Thm`). A store miss is `Gap` with the constant's own reason
  (e.g. `Gap::Axiom(name)`), never a delta-walk search. (nanoda:
  `ty_const`'s store path; the `has_type_const` delta-graph fallback does
  not exist here.)
* `.sort u` → ground `u`; type `Sort (u+1)`; `ev`: `u = 0` →
  `Prelude::u0_in_u1`; `u = n+1` → `mem_u` instantiated at the tower level
  (`⊢ ∀x. x ∈ U(x)`) **[read, tg.rs `Prelude` fields and docs]**.
* `.app f a` →
  1. `tf = infer_type(f)`;
  2. `(pi, conv, tf') = whnf_typing(tf)` — §6.4's transport form; `tf'` is
     `Γ ⊢ ⟦f⟧ ∈ ⟦Π x:A. B⟧`. **This is the composition nanoda's
     `ensure_pi` drops** (census §1.2, the silent leg `ty_bridge`
     compensates for); in mini it is one Leibniz step and it is not
     optional — there is nothing else to fall back on.
  3. `ta = infer_type(a)`;
  4. `ceq = assert_def_eq(A, ta.ty, /* typings: */ infer of both if needed — see §6.5 note on type-level typings)`;
  5. `ta' = retarget(ta, ceq)` — Leibniz on the membership's right side:
     `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧`. (nanoda: `ty_conv`.)
  6. result type `B.subst(a)`; `ev` composed by the application-membership
     lemma: `fs_app_mem` when `B` is binder-free, the dependent product's
     `∀x ∈ A. app(f,x) ∈ B(x)` conjunct otherwise (nanoda: `ty_app` /
     `app_in_codomain` / `app_in_fibre`); **proof clause**: when
     `term_clause(e)` says *proof* (§7), the application interprets to `•`
     and the typing comes from the `Prop` clauses instead
     (`point_of_proof`'s composition — here fed by `is_prop`'s witness,
     never by search).
* `.forall ty body` (mini-lean's `.forall` clause) →
  `s1 = infer_type(ty)`, whnf+`as_sort` (transport, §6.4);
  `tok = open_binder(ty)`; `s2 = infer_type(body)`, whnf+`as_sort`;
  `closed = close_binder(tok)`; `fam = closed.discharge(s2-membership)`.
  Result type `Sort (imax l1 l2)` — **ground, so exactly one §6.2 clause
  applies** and `PiUndet` does not exist in mini. **It does not follow that
  the clause classifiers can be dropped, and an earlier revision of this
  section implied they could.** `⟦·⟧` must be a *function*: two occurrences of
  one expression have to interpret to the same `Term`, or their definitional
  equality needs a theorem where reflexivity should do (§7's identity
  argument). Deciding which clause a `Π` or a `λ` takes is a judgement about
  the *expression*, not about the level alone. So mini has both classifiers.

  **But they are three lines each, not nanoda's hundred, and they are exact
  rather than approximate** **[implemented and tested, `mini/src/kernel.rs`]**.
  nanoda's `body_clause` is a syntactic walk over heads and arities with a
  redex arm, a `let` arm, a projection arm and the `syn_type` shadow walk
  beside it, and its own doc says why: *"the decision needs the body's sort,
  `infer` lives on `TypeChecker`, which owns this backend and is in the middle
  of a call into it, and the backend may not call back."* The approximation
  exists to route around the backend/checker split. Mini has no such split:

  ```
  body_clause(b) = is_prop(b)                    -- lvl(b) = 0
  term_clause(e) = body_clause(infer_type(e))    -- sort(e) = lvl(type of e)
  ```

  This is §0's rule applied, not a shortcut: running inference forward on a
  subterm is inference, not search. Three consequences, each a row nanoda
  carries and mini does not. The redex and `let` arms vanish — `is_prop`
  whnfs, and `infer_type` substitutes a `let`, both pinned by tests. The
  `syn_type`/`syn_type_proj` shadow walk has no counterpart, because it exists
  *only* to feed this classifier without re-entering the checker. And
  `Undet::Unknown` becomes unrepresentable, which retires `081_PSigma.snd`'s
  eight lost derivations by construction rather than by a special case.

  **And no memo is needed** — which this section also claimed one revision
  ago, and which is also wrong. nanoda memoises to *pin* functionality. Mini's
  answer is `is_prop` of the expression, `is_prop` is deterministic, and mini
  holds no state that could make a second call answer differently, so the
  classifier is a function by construction. A memo would be an optimisation,
  sound for the same reason.

  With that settled: `l2 = 0` → the `∀` clause,
  `ev` by the `Prop`-Π rule (`cond`-membership in `U₀`, nanoda's `PiProp`
  path, 446/449 discharged on ip **[read, census §1.2]**); else the `Π`
  clause, `ev` by the n-ary `dprod_in_universe` at the prefix — backlog
  entry 2, **LANDED** **[read, `LIBRARY-BACKLOG.md` §2]**, which was
  nanoda's largest single `ty_pi` gap row.
* `.lam ty body` → domain sort as above (its witness has a consumer: the
  lambda's own typing lemma and, on the `Prop` branch, `cond_intro` — this
  is the evidence nanoda drops 33 587 times as `Dropped::BinderSort`);
  open; `tb = infer_type(body)`; close+discharge;
  result `Π ty. tb.ty`; `ev` = `lam_in_funspace_n` / `lam_in_dprod_n` /
  `prop::cond_intro` per the body's clause. (nanoda: `ty_lam`.)
* `.let ty val body` → `s = infer_type(ty)` sort check;
  `tv = infer_type(val)`; `assert_def_eq(ty, tv.ty, …)` as an **acceptance
  gate** — its `Conv` has no downstream consumer *after substitution*
  (verified argument in the census at `infer_let`: post-substitution there
  is nothing to compose it with), and that is not a "drop": no later step
  re-derives it. Result: `infer_type(body.subst(val))` — the substituted
  body's own inference *is* the evidence. (mini-lean substitutes rather
  than opening a let-scope **[read, `inferType`, `.let` clause]**; mini-rust
  keeps that, which conveniently means no let-scope machinery at all.)
* `.proj` → §6.6.
* `.natLit n` → type `Nat`; `ev`: the literal's interpretation is *defined*
  as the interpretation of its constructor spine (§7), so its typing is the
  spine typing composed from `Nat`'s constructor memberships at σ = `[]` —
  from the store; `Gap` while `Nat`'s interpretation is absent.
* `.strLit` → type `String`; `ev = Gap::StrLit` (mini-lean has no string
  reduction and mini keeps the constructor inert; if the corpus never
  exercises it, this gap never fires — checked empirically at step 1 of
  §12).

### 6.3 `isProp` — the witness signature

```rust
/// (is_prop, the inferred sort expr, witness on the licensing branch only)
fn is_prop(&mut self, ty: &Expr) -> Result<(bool, Expr, Option<Ev>)>
```

Exactly the prompt's shape. On `true`, the witness is `Γ ⊢ ⟦ty⟧ ∈ U₀`, and
it is *not a new derivation*: `infer_type(ty)` returned
`Γ ⊢ ⟦ty⟧ ∈ ⟦s⟧`, the whnf leg is transported (§6.4), and `⟦Sort 0⟧ = U₀`
by the interpretation — the witness is the inference's own certificate,
un-discarded (census §1.6: "no new derivation needed, only non-discarding").
`false` licenses nothing and carries nothing. `isPropOrUnit` (used by defeq's
proof-irrelevance gate) is the same plus the unit-like probe; its unit branch
witness is the structure's subsingleton lemma from the inductive
interpretation (`Gap::UnitLike` until interpreted structures exist).

### 6.4 `whnf`

```rust
/// Primitive: the equality, with no typing input.
fn whnf(&mut self, e: &Expr) -> Result<(Expr, Conv)>          // Γ ⊢ ⟦e⟧ = ⟦e'⟧

/// Transport form: whnf the *type* inside a typing and convert the subject's
/// membership along it (one Leibniz). (t: Γ ⊢ ⟦x⟧ ∈ ⟦T⟧) ↦ (Γ ⊢ ⟦x⟧ ∈ ⟦T'⟧).
fn whnf_typing(&mut self, t: Typing) -> Result<(Expr, Conv, Typing)>
```

**This deviates from the target signature in the task brief**
(`whnf(e, ⊢⟦e⟧∈⟦T⟧) → (e', ⊢⟦e⟧=⟦e'⟧)`), deliberately, and the deviation is
one of the things building mini is *for* — establishing the minimal true
dataflow before nanoda commits to a signature. The typing input was to serve
two purposes (census, stage 2), and in mini each is served by something
sharper:

1. *Transporting the typing to the reduct* (subject reduction): that is a
   composition **at the caller**, packaged as `whnf_typing`. Enumerating
   every `whnf` site in `Kernel.lean` **[read]**: `inferType .app` (the
   `ensure_pi` analogue), `inferType .forall`/`.lam` (sort exposure),
   `isProp`, `isPropOrUnit`, `inferProj`, `tryStructureEta` use the
   transport form; `assertIsDefEq`'s two legs and the `whnf major` inside
   recursor reduction use the primitive (their product is an equality to be
   composed by `trans`, not a typing); `openForall*`/`instantiateForalls`
   compose legs per §6.7; `checkCtorParam` and recursor generation are
   shape-zone. **Zero sites consume a typing input for the equality
   itself.**

   **That statement is true and it is not sufficient, which the compositional
   rebuild made visible** (2026-08-01, before `whnf` was threaded). The
   equality does not need a typing; the *certificate for* the equality needs
   the **interpretations of the endpoints**, and `whnf` has neither. A delta
   step gives `⊢ ⟦c⟧ = ⟦val⟧` from the store, but lifting it to
   `⟦c s⃗⟧ = ⟦val s⃗⟧` is `app_cong` over `⟦sᵢ⟧` for every argument on the
   stack; beta needs `⟦A⟧` and `⟦a⟧`. If `whnf` computes those itself it walks
   the term a second time — exactly the defect §13 risk 3 records, reappearing
   one level down. So the uniform principle applies to `whnf` too: **every
   interpretation must come from a `Typing` already in hand**, and `whnf` must
   be handed them rather than deriving them.

   There is a wrinkle, and it has a clean resolution. What the caller holds is
   `Typing { ty, tm, ev }` where `tm` is `⟦subject⟧` — but `whnf` is applied to
   the *type*, so what it needs is `⟦ty⟧`, which `Typing` does not carry as a
   field. It does carry it *inside* `ev`: the evidence concludes
   `mem(tm, ⟦ty⟧)`, so on the `Proved` branch `⟦ty⟧` is read straight off
   `ev.concl()` at no cost. On a `Gap` branch it is unavailable — and that is
   correct rather than awkward, because a step whose endpoints have no
   interpretation has no certificate to build either.

   **Consequence for the signature.** The primitive stays untyped in the sense
   this section argued for — no typing is consumed *to decide the reduction* —
   but it takes `⟦e⟧` alongside `e`. Whether that is best spelled as a second
   parameter or by passing the whole `Typing` is an implementation choice; what
   is settled is that deriving the endpoint interpretations inside `whnf` is
   the wrong shape, for the same reason it was wrong in `push`.

   **Built 2026-08-01 as `whnf_conv(e, tm, why) -> (E, Conv)`**, with `tm` an
   `Option` and `why` the caller's own gap. Three things the plan above did not
   anticipate, each found by the ledger rather than by argument:

   * **Handing in `⟦e⟧` is not enough; the interpretation has to be
     *decomposable*.** Lifting a delta step over the stack needs `⟦sᵢ⟧` for each
     argument, and those come from taking `⟦f a⟧ = app(⟦f⟧,⟦a⟧)` apart — which
     works only because `Interp::mk` records applicative structure on the way
     in. The same is true of `⟦Π x:A. B⟧` at every consumer. So the uniform
     principle has a second half: *every interpretation comes from a `Typing`
     already in hand, and is recovered from it by decomposition rather than by
     re-interpretation.*
   * **Instantiation happens inside the kernel and is therefore unrecorded.** A
     beta step's contractum, and an application's result type, arrive as terms
     nothing can take apart, so the *next* decomposition fails — silently, and
     several steps away from the cause. `Interp::rebuild` walks the recorded
     skeleton to produce the same term through `mk` instead. Without it every
     curried application gapped.
   * **A beta leg does not end at the contractum.** `beta_conditional_n`
     concludes `app(lam(h⃗,⟦A⟧), ⟦a⟧) = t(h⃗,⟦a⟧)`, where `t` is the body
     *symbol*; the caller's `⟦b[a]⟧` is the skeleton instance. The second leg is
     `t`'s own defining equation at `⟦a⟧`, and it is where the skeleton's
     substitution-stability property is actually cashed in.

   The `Option` is load-bearing beyond tidiness: an acceptance-only caller
   (`is_def_eq`, the K-rule probe, `tryStructureEta`'s field comparison) hands
   in nothing, and the whole certificate apparatus then short-circuits on
   `Ev`'s gap. That is not a drop — those results have no downstream consumer —
   and it is what keeps the corpus at 8.5s instead of paying for a certificate
   at every decision.
2. *Feeding beta's domain obligation*: a membership `Thm` about the whole
   application cannot be inverted into `⟦a⟧ ∈ ⟦A⟧` — a `Thm` is not a
   derivation tree, and no kernel rule decomposes a conclusion. What the
   census actually established is that the *checker-level* inference knew
   the argument's typing; in mini the checker-level carrier of that
   knowledge is `infer_type` itself, so the beta step runs it (§0's
   inference-not-search rule):

```rust
/// One head beta step: e = (λ ty. body) applied to arg (from the spine).
/// Γ ⊢ ⟦(λA.b) a⟧ = ⟦b[a]⟧
fn beta_step(&mut self, lam_ty: &Expr, body: &Expr, arg: &Expr) -> Result<Conv> {
    let ta   = self.infer_type(arg)?;                    // Γ ⊢ ⟦a⟧ ∈ ⟦A'⟧
    let ceq  = self.assert_def_eq(lam_ty, &ta.ty, …)?;   // Γ ⊢ ⟦A⟧ = ⟦A'⟧
    let mem  = retarget(ta, ceq);                        // Γ ⊢ ⟦a⟧ ∈ ⟦A⟧
    // beta_conditional at the λ's skeleton, MP with mem  (proof clause: refl at •)
}
```

For a bvar-headed argument this bottoms out instantly in the scope's stored
hypothesis — the case that is 5 186 of nanoda's `has_type` misses ("a local
at the top level") costs mini one vector index. For compound arguments it is
a recursive inference, affordable because mini has no performance goals; the
mini-lean precedent for whnf↔infer mutual recursion is already in the
original (`whnf` calls `inferType` for the K-rule check **[read]**). The
added `assert_def_eq(A, A')` is a strictness delta over mini-lean (which
never looks at the λ's domain when contracting): on a well-typed input it
must hold by subject reduction; if it ever rejects a file mini-lean accepts,
the §11 fidelity gate catches it and the fix is to weaken to `Gap`, not to
delete the check. This is flagged as a named risk (§13).

The remaining `whnf` step kinds, each one certificate leg composed by `trans`
along the reduction (mini-lean's `go` stack machine is kept; the certificate
composition wraps its steps exactly as `certify_reduct`/`trace_cert` do in
nanoda, minus the memo and the endpoint-drift guard, which exists to protect
a cache mini does not have):

* **delta** (`cinfo.value?` unfold): the constant's defining equation from
  the store (`Sealed`), spine congruence (`app_cong` folds). Mini-lean's
  whnf is *eagerly* delta-unfolding with no lazy-delta heuristic — so
  nanoda's `lazy_delta_step`/`recall_eq` machinery has no counterpart, and
  the delta certificate is the defining axiom, one per unfold.
* **beta**: above.
* **let**: `⟦let⟧` — zeta is substitution; certificate is the `let`
  interpretation's defining equation (mini interprets `let` by interpreting
  the substituted body — see §7 — making zeta *reflexivity*).
* **iota** (recursor rules, including the K-rule and `Quot.lift/ind`): the
  stored per-`(rec, levels)` iota rule (S4 of `GenRecursor` **[read,
  `derived/src/inductive/recursor.rs`: `pub iota: Vec<Thm>`]**), its
  premises fed by: the major's own reduction leg (`whnf major` — primitive
  form), the constructor-spine typings (from inference of the major's
  arguments — same rule as beta), and for the K-rule the `inferType major`
  + `isDefEq` evidence the mini-lean code already computes **[read,
  `whnf.go`, recursor arm]**. `Gap` per §10 until the wiring lands.
* **proj-of-ctor**: the structure's projection computation fact from the
  inductive interpretation (`Gap::StructProj` until then).
* **natLit unfold**: reflexivity — `⟦natLit n⟧` is *defined* as
  `⟦Nat.succ (natLit (n−1))⟧`'s interpretation (§7), so the two sides are
  the same `Term`.

### 6.5 `assertIsDefEq`

```rust
fn assert_def_eq(&mut self, a: &Expr, b: &Expr,
                 ta: &Typing, tb: &Typing) -> Result<Conv>    // Γ ⊢ ⟦a⟧ = ⟦b⟧
```

The prompt's signature, adopted as written: both typings in. Where the
recursion needs typings of *types* (e.g. comparing the domains of two `Π`s),
they are obtained by `infer_type` on the types — a regress that terminates at
sorts and is the price of no memoization, accepted per §0. Clause order
follows `assertIsDefEqImpl` **[read]** exactly (acceptance fidelity):

1. **Proof irrelevance first** (`isPropOrUnit (inferType e1)`): with `ta` in
   hand the gate is `is_prop`-with-witness on `ta.ty`; on `true` the
   certificate is the `U₀`-subsingleton composition (nanoda's `proof_eq`
   minus its two `has_type_a` searches — the exact double-work loop the
   census names at `proof_irrel_eq`).

   **The premises are per-side, and an earlier revision of this section said
   they were shared.** It asked for `⟦T₁⟧ ∈ U₀`, `⟦e₁⟧ ∈ ⟦T₁⟧` and
   `⟦e₂⟧ ∈ ⟦T₁⟧` — the last obtained by retargeting `tb` along
   `assert_def_eq(ta.ty, tb.ty, …)`, and called "an *addition* over
   mini-lean's control flow, which never compares the types here". **That
   addition is not needed and the design is better without it.**
   `derived::anchor::falsity::prop_subsingleton` is stated for every
   proposition at once — `⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)` — so each
   side reaches `•` from *its own* type, and the equation is `trans` of one
   with `symm` of the other. The two types are never compared, the recursive
   `assert_def_eq` at every proof comparison disappears, and one of §13 risk
   2's two strictness deltas is gone rather than merely watched.
   **[implemented and tested, `mini/src/interp.rs`, `point_of_proof`]**

   A consequence worth recording, because it bit twice: `⟦f⟧` need not be `•`
   even when `f` is a proof. §6.2 sends a proof-valued *application* or
   *lambda* to `•`, but a proof that is a `bvar` is its scope variable, which
   is an element of the conditional singleton and hence *equal* to `•` but not
   that term. So `cond_app` and the `λ`-`Prop` rule move onto `•` by this same
   rule first; when the term already is `•` the step is `• = •` and costs
   nothing. Unit-like branch: `Gap::UnitLike` until interpreted structures.
2. whnf both sides (primitive form), legs composed into the result by
   `trans`/`symm` — the composition nanoda once skipped and now guards
   (README, "claim-matching bugs": the refl-for-a-reduction bug).
3. Structural cases:
   * `sort/sort`: ground numerals; equal → the two interpretations are the
     same `Term`, certificate `Thm::eq_refl`; unequal → `Err`.
   * `forall/forall`, `lam/lam`: domain `Conv`; open; body `Conv` (typings
     for the recursive call by inference under the scope); close;
     `discharge`; compose `dprod_ext_n`/`cond_ext_n` resp. `lam_ext_n` with
     the domain `Conv` and the discharged family. (nanoda: `pi_cong` /
     `lam_cong`, already real rules.)
   * `bvar/bvar`: same index → `eq_refl` of the same variable (nanoda's
     `Admit::Local` becomes reflexivity, as the census says it should);
     different → `Err`.
   * `app/app`: two recursive `Conv`s (typings by inference), `app_cong`.
   * `const/const`: same name, ground level lists evaluate equal → same
     interpreted `Term`, `eq_refl`; else `Err` (both sides are
     post-eager-delta opaque, so there is no "unfold one side" case —
     `lazy_delta` has no analogue).
   * `proj/proj`: same `(ind, idx)` + structure `Conv` → `proj`-congruence
     (congruence over an uninterpreted symbol needs no axioms about it —
     the census's "pure low-hanging fruit" row, `def_eq_proj`).
4. `tryStructureEta` both ways (§6.6), `tryFunEta` both ways:
   * `tryFunEta(e1 = λA.b, e2)`: open `A`; `Conv` for
     `b ≡ (shift e2) (bvar 0)`; close+discharge. The final step needs
     `Γ ⊢ ⟦e2⟧ = ⟦λA. e2·x⟧` — graph extensionality for a term *known to be
     a set-function*, whose premise `⟦e2⟧ ∈ fs/dprod(…)` is exactly why
     this function takes `tb`. That lemma does not exist yet
     (`TgBackend::eta` admits, "needs a function-extensionality lemma"
     **[read, census §1.4]**); `Gap::FunEta`, named in §10. Note the
     recursive `Conv` is composed, not discarded — the half nanoda drops
     with no ledger entry (`try_eta_expansion_aux`) is structurally
     impossible here because the only way to a `Conv` is composition.

Rejection (`Err`) needs no evidence on any branch — confirmed as the correct
polarity by the census across all of nanoda's defeq rules.

### 6.6 `inferProj`

```rust
fn infer_proj(&mut self, ind: &Name, idx: u32, e: &Expr) -> Result<Typing>
```

Port of mini-lean's `inferProj` **[read]**: `whnf_typing(infer_type(e))` to
expose the inductive head; the single-constructor telescope walk with
`instantiateForalls` (whnf legs composed per §6.7); the `isProp` gates use
§6.3 and their witnesses ride into the result. The final field typing
`Γ ⊢ ⟦e.idx⟧ ∈ ⟦D⟧` needs the structure's projection-membership fact from
the inductive interpretation — `Gap::StructProj` until that exists (nanoda:
260 `ty_proj` declines + a delta-only `syn_type_proj` shadow walk; the
shadow walk is not ported — mini's answer to "the backend must not re-enter
the checker" is that there is no backend/checker split to re-enter: the walk
already happened, threaded).

### 6.7 Telescope helpers

`openForall n type k`, `openForallEager`, `instantiateForalls`, `mkForall n`,
`mkLambda n` — ported with their mini-lean semantics **[read]**, plus: each
internal `whnf` produces a `Conv` leg, and the helpers return their legs
(`Vec<Conv>`) beside the result so a consumer that needs the equality chain
has it and a shape-zone consumer ignores it *by type* (`Vec<Conv>` unread is
visible in review; a `Thm` silently dropped inside is not). `mkForall`/
`mkLambda` read the scope stack's `ty`s exactly as mini-lean reads `lenv`.

---

## 7. The interpretation: reimplement the dispatch, reuse everything below it

The question the task poses: does mini reimplement `⟦·⟧` or share `tg.rs`'s?
**Split the question by layer, because the layers have different answers:**

1. **`kernel/` and `derived/` are reused wholesale, unchanged.** Everything
   mini composes with is `Term`/`Thm`-level and `Expr`-agnostic — verified
   for the pieces that matter: `derived::inductive`'s `DeclSpec` /
   `Inductive::build(env, mach, spec)` / `GenRecursor::build(env, mach, ind,
   rc, iota, funspace)` take no checker types **[read,
   `spec.rs`/`carrier.rs`/`recursor.rs`]**; the tower/funspace/prop/cumul
   stack likewise (their consumers in `tg.rs`'s `Prelude` call them on
   `kernel::Env` alone **[read, `prelude()`]**).
2. **The §6.2 clause dispatch is reimplemented against `mini::Expr`.** This
   is the right call, not a concession:
   * The dispatch is small — the clause structure (sort tower, proof split
     via `term_clause`, `App`/`Lam`/`Pi` doubled clauses, level
     interpretation) is a few hundred lines by inspection of the function
     inventory (`interp_sort`, `interp_level(s)`, `interp_app`,
     `interp_lambda`, `interp_pi`, `interp_pi_prop`, `term_clause`,
     `body_clause`) against a 15k-line file whose bulk is the search family,
     the CondEq apparatus, counters, and per-inductive recognisers.
   * Sharing it would mean either (a) mini adopting `ExprPtr`/`TcCtx` —
     re-importing the arena, the lifetimes, and the per-declaration
     re-interning that are precisely the confounders mini exists to escape
     — or (b) abstracting `tg.rs` over an expression trait mid-flight,
     inside a file another agent is editing. Both are worse than a few
     hundred lines written once against a stable original.
   * Independent reimplementation has diagnostic value: where mini and
     nanoda disagree about a certificate, one of the two dispatches is
     wrong, and they fail independently.
3. **The awkward middle layer: `tg.rs`'s `Term`-level machinery.** The
   skeleton decomposition (`skeleton(&mut self, t: &Term, v: FreeVar, …)` —
   verified `Term`-level by signature), the per-skeleton symbol caches, the
   n-ary prefix-threaded lemma family (`lam_ext_n`, `lam_in_funspace_n`,
   `lam_in_dprod_n`, `cond_ext_n`, `dprod_ext_n`, `dprod_const_fibre_n`,
   `image_ext_n`/`image_symbol_n`/`dprod_symbol_n`, `lam_pair_val_n`,
   `lam_single_valued_n`), and the `Prelude` assembly. Mini needs all of it:
   skeleton decomposition is not a nanoda workaround but a property of the
   interpretation itself (a defined symbol may not contain free variables
   that are not among its parameters — conservativity; and the
   maximal-`v`-free-subterm abstraction is what makes `⟦b[a]⟧` line up with
   `⟦b⟧` filled in, which beta needs **[read, tg.rs module doc,
   "Lambdas"]**). Mini has the same problem in de Bruijn dress: a nested
   lambda body mentions enclosing binders' `w`s.

   **Recommendation: extract this layer from `tg.rs` into `derived/`** (one
   construction per file, per the standing library rule), with `tg.rs`
   re-importing. It is library, not instrumentation; moving it *shrinks* the
   `checker/` diff, which strengthens rather than pollutes the README's
   diff story (the constraint forbids extracting *upstream* code — the
   parser; `tg.rs` is wholly new, so nothing upstream moves). Because
   `tg.rs` is under live edit, this is a coordinated, mechanical move for
   the `tg.rs` agent to land at a quiet point — functions move with their
   tests, conclusions pinned before/after. **Fallback if coordination
   stalls:** mini clones the family (flagged as debt with a tracking item);
   do *not* have mini call `checker::tg` internals — that couples mini's
   build to the file being rewritten under it.

Interpretation state mini does keep, and why it is not "a cache" in the
banned sense: the per-skeleton graph/fibre symbol tables and the
per-`(name, ground levels)` constant interpretations are **identity**, not
memoized recomputation — two occurrences of one lambda body shape must be
the *same* symbol or their defeq needs a theorem instead of reflexivity.
Everything stored is `Sealed` (I4) plus the certificate that produced it
(the standing memoization rule: a memo stores the certificate with the
result).

**Those tables are where canonicality lives, and it has to live in a
caller.** `derived::define_abbrev` is `kernel::thm::define` is `Env::declare`:
a fresh `FnSym` on every call, **keyed on nothing**. It cannot be keyed on
`(arity, body)` either, because the body is stated at caller-minted
`FreeVar`s that differ between calls; the alpha-canonical key exists — `define`
computes `close_all(xs, exists_unique(env, y, φ))` at `thm.rs:1409` and checks
the witness against it — but the only sound home for a memo on it is `Env`
itself, since a `FnSym` carries a brand and a memo outside the `Env` would
hand back a symbol from a different one. That is a cache in the TCB, which has
24 lines of headroom under the 700-line cap. So: *the right response to "the
call graph is the key" is to add the missing caller-side table, not to
memoise a function that cannot see a canonical key without being handed one.*
`mini/src/zoneb.rs`'s `a_second_translation_mints_no_second_symbol` is what
holds the current call graph to that.

What mini does not have: whnf/infer/defeq result memos keyed on
expressions — nanoda's caches, with their hypothesis-import guards, are
engineering for a later stage (task #29's "engineering around caches"), and
mini's role is to show the design correct without them.

`let` and `natLit` interpretation, fixing two clause choices left open
above: `⟦let ty := v in b⟧ := ⟦b[v]⟧` (zeta-transparent, making whnf's zeta
step reflexivity — legitimate because mini-lean also checks `let` by
substitution); `⟦natLit n⟧ := ⟦Nat.succ (… Nat.zero)⟧` (literal-transparent,
same effect for the natLit step).

**No per-type recognisers.** nanoda carries hand-written `Bool`/`N`/`List`
interpretations (`bool_recursor`, `nat_recursor`, `list_recursor`,
`enum_*`/`nat_*`/`list_shape`) beside the general machine; they are
scaffolding from before `derived::inductive` existed. Mini uses **only** the
general path (`DeclSpec → Inductive::build → GenRecursor`), and deliberately
trades early parity on those files for forcing the general path to completion.

This paragraph predicted the consequence and named the wrong blocker. It said
mini would gap on `⟦T⟧ ∈ ⟦Type 0⟧` until `derived::cumul` was generalised past
its `B(a) ∈ ω`-on-the-nose demand (`WIRING-DESIGN.md` verdict 5's `finord`
blocker). **`⟦T⟧ ∈ ⟦Type 0⟧` works** — `cumul::decl::DeclUniverse` discharges
exactly that, and `mini/src/zoneb.rs` derives it for `Bool`, `Color`, `Empty`,
`N` and `Nat` today. What does gap is one level up and one field along:
`⟦T⟧ ∈ ⟦Type n⟧` for `n ≥ 1`, because the cumulative chain's `u1` is a fixed
field, and `⊢ Aᵢ ∈ U₁` for a constructor with a non-recursive field, because
that route is `cumul::sigma_n` and it is not wired. §0.5 has the counts.

---

## 8. The environment and the declaration pipeline

```rust
pub struct MiniEnv {
    /// Syntactic, generic-level — the port of mini-lean's Environment.
    consts: HashMap<Name, ConstantInfo>,
    /// The interpretation store, keyed per ground instantiation.
    interp: HashMap<(Name, Inst), ConstInterp>,
    /// Kernel signature + prelude (tower, fs, ap, …), built once.
    kenv: kernel::Env,
    prelude: Prelude,
    machine: derived::inductive::Machine,   // one, process-wide (MachineId guard)
    gaps: GapLedger,
}

pub struct ConstInterp {
    pub term: Term,                    // ⟦c.{σ}⟧
    pub typing: Result<Sealed, Gap>,   // ⊢ ⟦c⟧ ∈ ⟦ty[σ]⟧
    pub defeq: Option<Sealed>,         // defs: ⊢ ⟦c⟧ = ⟦val[σ]⟧ (the defining axiom)
    pub iota: Vec<IotaRule>,           // recursors: per-ctor computation certs
}
```

`Environment.add`, per declaration kind (the mini-lean checks run verbatim;
the evidence column is what is added):

* **axiom** `name lparams ty`: per σ — `infer_type(ty[σ])` must be a sort
  (evidence produced and consumed by the store row below); mint an opaque
  constant symbol for `⟦c.{σ}⟧` (pure signature extension, conservative);
  `typing = Gap::Axiom(name)` — an axiom's inhabitation is a genuine model
  assumption, not derivable. Whether the three real axioms (`propext`,
  `Classical.choice`, `Quot.sound`) get a separate "assumption ledger"
  distinct from the gap ledger is an owner call (§13); they head zero typing
  obligations on init-prelude **[read, census §3.4]**, so on the tutorial
  corpus this is likely moot — measured at step 1.
* **def / theorem** (the model case — nanoda's `check_declar_at`, the one
  row the census marks "done" end-to-end): per σ —
  1. `ts = infer_type(ty[σ])`, whnf+sort; for `theorem`, the sort must be
     ground `0` and the `is_prop` witness `⊢ ⟦ty⟧ ∈ U₀` is stored beside the
     typing (the "this constant is a proof" fact the census wants from
     `check_declar_info`);
  2. `tv = infer_type(val[σ])`;
  3. `ceq = assert_def_eq(ty[σ], tv.ty, ts, …)`;
  4. define `⟦c.{σ}⟧ := ⟦val[σ]⟧` (`kernel::define` via the abbreviation
     discipline — nanoda's `const_abbrev`); `typing` = `tv.ev` transported
     along the defining equation and `ceq` — `⊢ ⟦c⟧ ∈ ⟦ty⟧`;
  5. `Sealed::new` — at top level no scopes are open, so per I2 this cannot
     fail on a correct run; store.
  `opaque` stores the typing but no defining equation.
* **quot**: `Environment.addQuot`'s four constants ported verbatim
  (syntactic side **[read, `Kernel.lean`]**); interpretation and typings
  from `derived::quot` over the shared prelude, computation rules for
  `Quot.lift`/`Quot.ind` stored as iota rules (backlog entry 6,
  LANDED/MID-BUILD **[read]**; wiring is mini-side work, §10).
* **inductive**: §9.

Checking order is file order (mini-lean's), σ-inner (§3). The `insertNew`
duplicate check is ported as-is.

---

## 9. Inductives and recursors

Two zones with different evidence rules, and the boundary between them is
the design:

**Zone A — the declaration-shape zone (evidence-free, sanctioned).** The
verbatim port of mini-lean's inductive checking **[read, `Environment.add`,
`.inductive` arm]**: `checkType indType`, `numIndices`/`indLevel` via
`openForall`/`openForallEager`, the `isUnit` probe, per-ctor `checkType` +
`defEqParams` + `checkCtorType`/`checkCtorParam` (positivity,
`assertLevelLe u indLevel`, `isValidIndApp`), the `elimToSort` decision, the
K-`kType` computation, and the whole recursor-type/rules **generation**
(§1–6 of the `recType` builder, `Expr.bvars`, the rules with their
`ih` construction).

*This zone takes a `mutual … end` block.* `kernel::add_block` is the port,
generalised: one `IndCtx` over every member of the block, `isValidIndApp`
answering **which** member an occurrence ends at, one motive per member and
one minor per constructor of the whole block in the shared recursor
telescope, one recursor per member, and each recursive field's induction
hypothesis stated at — and computed by — the recursor of *the field's own*
member. A block of one is the original and nothing branches on the size.
Three rules acquire a block-size condition: the members must share a
resultant universe, a block of more than one type never eliminates large
(this closes mini-lean's own `TODO` on the empty-constructor branch), and the
K-rule needs a block of one. `ConstantInfo::Recursor` grows `num_motives`,
which was an unwritten `1` at every telescope position including whnf's major
argument. **Zone B does not follow**: `ledger::fill_declaration` records
`ind-spec(T: mutual)` for every member, constructor and eliminator of a
block, so a use site reports that reason and nothing reaches `zoneb::ensure`,
where a member is indistinguishable from a single inductive and would be
translated as if its siblings did not exist. The frontend still declines a
mutual export by default (`convert::LoadOptions`); `mini --mutual` opens the
gate and `mini/tests/mutual.rs` is what uses it.

*And zone B does not have to.* `mini/src/mutual_aux.rs` **encodes the block
away** at the block's own position in the per-declaration loop.
`mini::decl_pass::Pass::step` drives `mutual_aux::Expander`, which replaces each
block it can express by a tag
inductive `Tag (p⃗) : Sort W` with one constructor `Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗` per
member carrying *that* member's index telescope, one indexed inductive
`Aux (p⃗) : Tag p⃗ → Sort u` carrying every constructor of every member, and
ordinary declarations over them —
`Tᵢ := fun p⃗ ix⃗ᵢ => Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ)`,
`Tᵢ.ctorⱼ := fun p⃗ f⃗ => Aux.cᵢⱼ p⃗ f⃗`, a packed motive
`Mot := fun p⃗ m⃗ => Tag.rec p⃗ (fun t => Aux p⃗ t → Sort v) m⃗`,
`Tᵢ.rec := fun p⃗ m⃗ k⃗ ix⃗ᵢ t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ (Tag.tᵢ p⃗ ix⃗ᵢ) t` at
*zone A's own declared type*, and one `theorem … := Eq.refl _` per recursor
rule at *zone A's own rule*. Those go through `kernel::add` and then through the
ordinary evidence walk, **under the block's own names** — which is why there is
no install step: `⟦Tᵢ.{σ}⟧`, `⟦Tᵢ.ctorⱼ.{σ}⟧`, `⟦Tᵢ.rec.{σ}⟧` and the rule
theorems land in the store at exactly the keys every later use site reads.

The rule theorems are the one part that is **not** emitted at the block: their
statements mention an `Eq` the block does not, and the exporter routinely
declares it after the block, so they are appended at the end of the file. Since
the loop was fused they are also *stated* there — `mutual_aux::rule_theorems`,
called from `Expander::append_rules` — because the environment at the block's
own position has no `Eq` either.

Three things make the rules reflexivity rather than transports, and each is
load-bearing: `Tag` is an *index* of `Aux` and not a parameter; the minors
are passed to `Aux.rec` untouched, because `Mot … (Tag.tᵢ p⃗ idx⃗)` ι-reduces to
`mᵢ idx⃗` and `Tᵢ.ctorⱼ` δ-reduces to `Aux.cᵢⱼ`; and every `Tᵢ.rec` hands
`Aux.rec` the *same* motive and minors, so a rule's induction hypothesis
`Aux.rec … (Tag.t_k p⃗ idx⃗) …` is literally what `T_k.rec …` unfolds to — which
holds across telescopes, so `MA.mk : MB → MA N.z` builds at arity 1 and its ih
is at `MB`'s arity 0. `mini/tests/fixtures/mutual_aux_encoding.lean` is the
unindexed encoding written by hand, and it certifies all 23 of its pairs.

**Indices go through the same encoding because they are inside the tag.**
`Aux` has exactly one index at every block, and a member with no indices is
the case where its tag constructor is nullary — so a block whose members carry
*different* telescopes is not a special case and there is no branch on whether
they agree. Exactly one number in the whole encoding is not readable off the
declaration: `W`, the sort `Tag` is declared at, which is
`max(1, s₁ … s_k)` over **every member's** index types, `sⱼ` being the sort of
the `j`-th index *type* — and an index of type `N` is at `Sort 1` only because
`N`'s declaration says so. The encoder asks the checker, through
`kernel::sort_under`, whose entire output is a `Level`. An
over-approximation is safe: the kernel checks `sⱼ ≤ W` and nothing bounds an
index type's sort from above. `Tag.rec` then runs at the purely syntactic
`max(u, v+1)`, the `imax` a `Π` carries collapsing because `v+1` is never
zero.

**The encoder never names a `Term`, a `Thm`, an `Ev` or an `Interp`**, which
is `ci/check-mutual-blackbox.sh` — a scan of one file, with its own self-test
that plants both kinds of violation, and the reason the encoder is a file of
its own. Asking mini's checker a question is not the banned thing; reading its
certificates is, so the script carries an **allowlist by name** —
`kernel::{add, sort_under}` — and a third entry point cannot appear without
someone editing the rule.

**Nesting is a different dance, and zone A now does it.** Lean's nested
compiler reduces `inductive Tree | node : List Tree → Tree` to the mutual block
`{Tree, ListTree}`, which zone A already takes. `mini/src/nested.rs` is that
reduction, run **inside the acceptance pass**: it specialises the declaration
into a block with a *mimic* copy of every container the type is nested into,
hands the block straight back to `kernel::add`, and **restores** what comes out
— the copy to `List Tree`, the copy's constructors to `List.nil Tree` /
`List.cons Tree`, and the copy's recursor `Tree._nested.1.rec` to `Tree.rec_1`.
The mimics live in a scratch environment and are never installed.

*This section used to say nesting was not reachable this way. It was written
about the **aux encoding** — `mutual_aux`'s `Tag`/`Aux` substitution — and that
part is still true and still measured (below). Specialising and restoring is a
different route with a different, weaker claim.*

**The restored recursors are the ones Lean exports, by the oracle.** A nested
`Tree` is one `Declar::Inductive` with `all = [Tree]` and `numNested = 1`, plus
**two** recursors — `Tree.rec` with rules for `Tree`'s constructors and
`Tree.rec_1` with rules for **`List`'s**, both at two motives and four minors.
`the_generated_recursors_are_the_ones_lean_exports` compares mini's *generated*
recursor against the export's own for every fixture, and both nested fixtures
are now in its sweep: type, motive/minor/index counts, rule count, rule order
and every rule's right-hand side agree, at `numNested = 1` over a recursive and
over a non-recursive container, at `numNested = 2` over one container twice
(`DTree.node : List (List DTree) → DTree`) and over **two different**
containers (`BTree.node : Box BTree → BTree`, `Box` a structure over `List` —
which is `Lean.Syntax`'s shape). `nested_iota.lean` states all ten ι rules as
`rfl` theorems, so Lean's kernel checked them at export time and mini's kernel
has to reduce the same redexes; it does.

One reduction rule had to change for that: mini's ι step took the fields off a
constructor application by dropping the **recursor's** parameter count, which is
the constructor's own for every recursor whose rules are its own type's
constructors and is wrong for a nested one — `Tree.rec_1` has `numParams = 0`
and reduces on `List.cons`, whose first argument is `List`'s parameter. It now
reads the owner's count, which is Lean's `RecursorRule.nfields` by another
route.

**What the acceptance axis does not check, and it is the whole obligation.**
The block that is checked is the specialised one; the declarations installed are
the restored ones, and the restoration is a **rewrite, not a derivation**.
`List Tree` and the mimic are isomorphic and *not equal* — bridging them needs
`fromAux (toAux l) ≡ l` at a **variable**, which is propositional.
`mini/tests/fixtures/nested_roundtrip.lean` is the encoding built out to that
point and `mini/tests/nested.rs` asserts mini's kernel rejects the equation,
with two closed instances accepted as the controls. `thesis.txt:902` says the
same in one line about Coq: mutual inductives, nested inductive types and
coinductive types "can all be encoded using regular inductives, although some
definitional equalities may fail to hold in the encodings".

So `Tree.rec_1`'s ι rule on `List.cons` enters the environment as an assumption
*transported along an isomorphism nothing on the acceptance axis checks*. The
oracle says mini's rule is the rule Lean declares; it does not say either is
sound. Discharging it is the evidence axis's job — a certificate that the two
interpretations agree — and until that lands `--nested` is a gate the corpus
never sets, exactly as `--mutual` was and for a sharper reason. Zone B declines
every such declaration with `ind-spec(T: nested occurrence)`.

**The second of the two routes is built, checked, and measured; what is left is
its wiring.** *Corrected 2026-08-06; this paragraph read "two routes stay open"
and costed both, which was right about the routes and stale about their state.*
`mini/tests/fixtures/nested_model.lean` is the specialised block's own model
written out as an export: the block as an ordinary `mutual`, `Tree`, `treeLeaf`
and `treeNode` as `def`s over it, `pack`/`unpack` and **both** propositional
round trips, `treeRec` and `treeRec1` at the types the export declares for
`Tree.rec` and `Tree.rec_1`, and all four ι rules as theorems with proofs. Lean
checks it at export time and `mini/tests/nested.rs` checks every declaration of
it through `kernel::add`.

Its price is two lemmas and no more. `Tree.rec` on `leaf` and `Tree.rec_1` on
`List.nil` are **definitional** under pack/unpack — the second because
`unpackPack List.nil` ι-reduces to `Eq.refl` and the transport in `treeRec1`
disappears — and `Tree.node` and `List.cons` are not, each needing one
transport-commutation lemma proved by `Eq.rec` on the round trip landing at
`Eq.refl`. The triangle identity between the two round trips is never proved:
`packUnpack (pack a)` and `congrPack (unpackPack a)` are two proofs of the same
`Prop`, so **proof irrelevance** identifies them. Lean 3 rewrote that stuck
`eq.rec` with a simp set (`LEAN3-INDUCTIVE-COMPILER.md` §4); mini does not have
to. `two_of_the_four_model_iota_rules_are_definitional_and_two_are_not` is that
table as a check rather than a claim.

On the *evidence* axis the model reads `pairs=41 typeEv=37 constEv=28`, and all
thirteen missing constant typings and all 3 214 gapped conversions are
`Gap::StuckRecursor` — a variant that had minted `0` over all 91 corpus exports
and whose doc comment said so. `unpack (pack l)` at an open `l` is a recursor
whose major premise is another stuck recursor, so the major reduces underneath
without the outer redex firing and the certificate owes a congruence over that
reduction, which `whnf` performs acceptance-only and does not thread. That is
the *one* named thing between the model and a certified nested declaration, and
it is a wiring question about the traversal — not a clause of §6.2 and not a
`derived/` construction. The other half of the wiring is keying: `zoneb::ensure`
must answer for `Tree`, its constructors and its two recursors out of the
model's own store entries instead of `ind-spec(T: nested occurrence)`.

*This paragraph used to end "— this is a rename in the store, not a
derivation". **Half of that is right.** For occurrence typing it is exactly a
rename: `Checker::const_evidence` is name-agnostic and `miss_reason` stops
looking once `get_const` hits. For ι *reduction* it is not: `iota_dep` demands
the `dep_elims` nest the eliminator was built over, and `decls`/`deprecs`
document themselves as identity rather than memoisation, so the model's recursor
cannot be pointed at the existing machinery. What is owed there is a **fourth
dispatch arm** beside `quot_iota` and `rec_acc_iota`, cashing the generated ι
theorem rather than using `DepRecursor::iota`. `MEASUREMENTS.md`'s "The keying
is a rename for typing and a new route for reduction" is the trace.*

*That arm is `mini/src/iota_model.rs` and it fires. **What it could not do is
the obvious thing**: apply the model's ι theorem to the redex's own arguments
and hand the application to `eq_cash::cash`. That application is a Lean **type
error** — the theorem binds `M₀ : T._model.self → Sort v` and the redex's motive
is at the export's `T`, and the two are not convertible precisely because the
model is a parallel development rather than a substitution. The instantiation is
therefore done at the *interpretation*, one `Interp::cond_app` per argument,
where `⟦T⟧` and `⟦T._model.self⟧` are one term by the keying; `eq_cash::cash_stmt`
— `cash` without its step 1 — then reads the equation off, handed the same
statement spelled in the **export's** constants. See that module's header. The
rules whose model proof *transports* still decline, by name, on #90(b).*

The first route — a `derived/` carrier over the *real* `⟦List⟧`, the initial
algebra of `X ↦ 1 + List X`, with both recursors and their ι theorems — remains
open and is still costed by `LEAN3-INDUCTIVE-COMPILER.md` §8.
`derived::inductive::DeclSpec` cannot express it as it stands: its `recs` is a
`usize`, and the spec's own header says a nested recursive argument contributes
a fibre summand that a count cannot describe.

### The generator — and the two things that are not obvious

*The generator is **`modelgen/`**, a separate Lean package that filters the
`.ndjson` export and splices the model in before each nested inductive;
`MODELGEN.md` §1 is its contract. `mini/src/nested_ev.rs` — 2117 lines of Rust
that built the same tower and handed each declaration to `kernel::add` — is
deleted, and `ci/check-mutual-blackbox.sh` no longer scans it. What is left on
mini's side is `mini/src/nested_splice.rs`, which **recognises** the tower,
checks each statement against the export's own and keys `⟦T⟧`, `⟦T.ctorᵢ⟧` and
`⟦T.rec_k⟧` onto it. The two facts below were learned by building the
hand-written model and are still exactly why the tower has the shape it has;
they are the reason `MODELGEN.md` §1 can be a short section.*

`nested_model.lean` is written by hand at `Tree`; `Lean.Syntax` will not be. So
the tower is generated, and its shape is fixed by the hand-written model —
**two facts about it were only learned by building that model**. Both are cheap
to state and expensive to rediscover.

**1. The model may not reuse the export's `T`, and this is not a naming
preference.** `T` is installed by `nested::add` as a *primitive*
`ConstantInfo::Inductive`; the block member `B₀` is a different constant, and
they are not convertible. A generator that splices `def`s mentioning the
export's own `T` does not typecheck — `pack : List T → B₁` cannot be built,
because `List`'s `cons` field arrives at `T` and the block's `cons` wants `B₀`.
So the model declares its **own** carrier

```text
def T._model.self : ∀p⃗, Sort u := fun p⃗ => B₀ p⃗
```

and every occurrence `occᵢ` is rewritten `T ↦ T._model.self` before it is used.
`T._model.self p⃗` β-δ-reduces to `B₀ p⃗`, which is exactly what lets `cons`'s
head field — typed `B₀ p⃗` in the block — be handed to the *real* `List.cons`,
which wants an element of `List (T._model.self p⃗)`'s parameter. Everything
downstream (`pack`'s domain, `unpack`'s codomain, every ι statement) is about
`T._model.self`, and **the keying is what identifies it with `T`**: `⟦T⟧` is set
to `⟦T._model.self⟧`, so `⟦List T⟧` and `⟦List T._model.self⟧` are the same
term and the cashed equations are about the right sets. The parallel
development is the design, not a workaround.

**2. The motive vector for `unpack` is forced, and only the root transports.**
A block recursor carries one motive per member at **one** motive universe, so
the members `unpack` does not eliminate into still need a motive at that sort.
The choice that works for every block whatever its constructors are is the
*identity* motive at the root and the occurrence at each mimic:

```text
motive₀ := fun _ : B₀ p⃗ => B₀ p⃗          minor for c : fun f⃗ ih⃗ => c p⃗ f⃗
motiveⱼ := fun _ : Bⱼ p⃗ => occⱼ^S        minor for c' : fun f⃗ ih⃗ => c_real q⃗ g⃗
```

where `gₖ` is `ihₖ` for a field at another mimic, the field itself for a field
at `B₀` (by fact 1) or a plain field. `fun _ => Bⱼ p⃗` at a mimic would not do —
`unpack₁` for `Box BTree` needs `unpack₂`'s result as its `mk` field, and that
arrives as the induction hypothesis at `motive₂`. **The mimic minors need no
transport at all**; only a *root* constructor with a packed field does, which is
why the price is one lemma per such constructor and not one per rule.

The emitted list, in dependency order, is: the renamed block as one
`Declaration::Mutual`; `T._model.self`; one `packᵢ`/`unpackᵢ` pair per mimic, in
an order where `packᵢ` follows every `packⱼ` its container's fields mention;
`unpackPackᵢ` and `packUnpackᵢ`; the constructors; `congr` and one transport
lemma per packed position; each `T._model.rec_k`; and one ι theorem per rule of
each, **stated from zone A's own `ConstantInfo::Recursor` rules** with the
export's names swapped for the model's, exactly as `mutual_aux` reads its rule
statements rather than recomputing them.

What it must decline, by name rather than by forcing a fit: a container with
**indices**; an occurrence whose mimic graph has a cycle; and a constructor with
**two or more packed positions**, where the transport lemma has to be folded
over the positions rather than applied once — `nested_shapes`' `DTree`, whose
`cons` is `M₂ → M₁ → M₁`, is the witness for the last and is the reason it is
listed rather than assumed absent.

Nesting an *indexed* container used to wait on the index scope
line below; that line is gone, so it does not any more. An unindexed container's
specialised copy is unindexed, so `nested_shapes.lean`'s four shapes never
touched it either way.

**A block's members need not share an index telescope.** They share their
parameters and their resultant sort, which the kernel checks; their indices
are their own. `Tag` carries them: `Tag (p⃗) : Sort W` with
`Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗`, one constructor per member holding *that* member's
telescope as fields, and `Aux (p⃗) : Tag p⃗ → Sort u` therefore has exactly one
index. A block whose members are unindexed is the case where every tag
constructor is nullary — one path, nothing branching on whether the telescopes
agree, and the eight fixtures that predate the generalisation are its
regression suite: every one of them is unchanged to the counter.

`mini/tests/fixtures/mutual_index_sorts.lean`'s `HA : N → Type` / `HB : Type`
block is the **arity** axis and used to be `Reason::IndicesDiffer`, exit 4 with
three pairs uncertified; the same export is exit 0 with all 56 certifying.
`mutual_index_telescopes.lean` is the two axes that leaves open — three members
with the odd one in the middle, and two members at equal arity whose index
*types* differ.

The one number in the encoding that is not syntax moved rather than going
away. It is now `W`, the sort `Tag` is declared at: `max(1, s⃗)` over every
member's index types, `kernel::sort_under`'s question because an index of type
`N` is at `Sort 1` only because `N` says so, and an over-approximation is safe
because nothing bounds an index type's sort from above. `Tag.rec` then runs at
the purely syntactic `max(u, v+1)`. The cheap guess `W = 1` is right on every
fixture but `mutual_index_sorts`, whose `Prop`-valued `SA` is indexed by
`Type 1` — the same escape shape that separated the *old* level formula, at a
new address.

*This was recorded for a long time as needing an `Ix : Tag → Type` by recursion
on the tag. That was a guess that was never measured; the shape wanted the
indices in the tag.*

The recursor generation now has an oracle that is not mini:
`mini/tests/mutual.rs`'s `the_generated_recursors_are_the_ones_lean_exports`
compares the generated recursor's type, rule order and every rule's
right-hand side against the export's own, over every designed fixture and the
whole tutorial corpus. It found one standing divergence, which is mini-lean's
and is left alone: `PUnit.rec` is K-like to mini and not to Lean, because
mini-lean asks `indLevel.isNotZero` where Lean asks `is_zero`, and a bare
level parameter answers "no" to both.

This zone runs at the declaration's own `lparams`
(symbolic — required for acceptance fidelity, §3), so its internal
`inferType`/`whnf`/`isDefEq` calls run with their `Ev` outputs ignored *by
type* and `interp` returning `Gap::SymbolicLevel` where a symbolic sort
blocks a clause. This mirrors what the census verdicts for nanoda's
`inductive.rs` ("correctly unthreaded — these judgements have no backend
consumer") — with the sharper mini justification: the zone's *outputs* are
(i) accept/reject, which needs no evidence, and (ii) a syntactic `DeclSpec`
+ recursor declaration, whose evidence is produced in zone B. The
`elimToSort` branch is decided here, from declaration data, by
`indLevel.isNotZero` — mini-lean's own predicate, which is exactly the
`provably_nonzero`-on-the-declaration's-own-level rule `WIRING-DESIGN.md`
§4 mandates (never the σ-numeral) **[read, both]**.

**Zone B — the interpretation (evidence-carrying, per ground levels, at the
declaration).** For each `(T, ℓ⃗)`, `(T.ctorᵢ, ℓ⃗)` and `(T.rec, ℓ⃗')` the
pre-pass scheduled, driven by `mini/src/ledger.rs`'s `fill_declaration` when
the declaration walk reaches `T`:

*(This paragraph said "on demand", and cited `WIRING-DESIGN.md` §7.1 —
inductives excluded from σ scheduling, interpreted at use sites under the
using declaration's σ. That is **nanoda's** decision and mini never inherited
the premise: `checker::instantiations::compute` handles `Declar::Inductive`,
`Declar::Constructor` and `Declar::Recursor` explicitly and propagates demand
through recursor rules and through an inductive's constructors' types, and
`mini/src/convert.rs` writes a schedule entry for every declaration where
`insts.for_name` is `Some` — inductives included — before it matches on the
declaration kind. Mini had the schedule and read it for `def`s only. Two
things were measured when it started reading it for inductives too: the
schedule's `(name, σ)` set covers **every** lookup, with the miss path made to
`panic!` and the corpus run; and three declarations that nothing in the corpus
uses at a ground level turn out to decline, which no run had ever asked. See
`mini/tests/dump.rs`.)*

1. Build the `DeclSpec` from `T`'s stored declaration at ground `ℓ⃗`: `np`
   from the declaration, per-ctor `CtorSpec` with field masks (`Rec`/`Plain`
   order) and each plain field type interpreted as the `βᵢ` body over the
   `np + i` prefix. **Positive scope check**: decline (with a counted
   reason) anything `DeclSpec` cannot express — **nested**, per the spec's own
   doc **[read, `spec.rs`, `well_formed` doc]**. A decline populates the store
   with `Gap`, not with a forced fit.

   *(This list read "indices, function-typed recursive arguments, mutual,
   nested". **Three of the four are translated now**: indices through
   `mini/src/ctor_ix.rs` and `zoneb::build_indexed`; function-typed recursive
   arguments through `CtorSpec::rec_doms` — `Gap::FunTypedRecArg` documents in
   `ev.rs` that it has no mint site left; mutual through
   `mini/src/mutual_aux.rs`. Nested is the only survivor.)*
2. `Inductive::build(kenv, machine, spec)` → carrier, `ty_ax`, ctor terms
   and memberships; `wrec_total::iota`/`wrec_funspace` →
   `GenRecursor::build` → S1–S4 **[read, the struct: `computes`, `sv`,
   `step_typed`, `iota: Vec<Thm>`]**.

   *(**`GenRecursor` is never called from `mini/src`** — the one occurrence is
   a doc comment in `ev.rs` explaining why it was not enough, being simply typed
   and landing in one target set. The eliminator that was built is a stack:
   `recursor.rs` dispatching to `rec_dep.rs`, `rec_prop.rs`, `rec_trunc.rs`,
   `rec_trunc_ix.rs`, `rec_ix_dep.rs`, `rec_ix_prop.rs`, `rec_s_ix.rs` and five
   `rec_acc*.rs`, with `iota_dep.rs`/`iota_ix_dep.rs`/`quot_iota.rs` for the ι
   rules. Nor does zone B's four-step recipe mention `direct.rs`, `class_s.rs`,
   `class_p_ix.rs`, `ctor_ix.rs`, `minor_ix.rs`, `proj_data.rs`, `proj_prop.rs`,
   `quot_classes.rs`, `acc.rs` or `unit_like.rs`. **Zone A above is accurate and
   was revised late; zone B is the plan, not the code** — the seven zone-B
   citations of "§9" in `mini/src` point at this recipe.)*
3. Wire to Lean shapes: the abbreviation `⊢ ⟦T.{ℓ⃗}⟧(p⃗) = W(…)`, constructor
   typings retargeted to the Lean-side telescopes (order-mask permutation
   per `WIRING-DESIGN.md` §5), the recursor typing, and per-ctor
   `IotaRule`s whose premises line up positionally with the Lean spine.
   All stored `Sealed` with their certificates (the memoization rule).
4. The eliminator branch and K-behaviour come from zone A's declaration
   data, not recomputed.

This zone is mini's port of `WIRING-DESIGN.md` §§3–6 against `mini::Expr`
instead of `ExprPtr`, and it is the **riskiest part of the whole port**
(§12) — the same verdict WIRING gives its own `fire_general` ("where derived
∀-schemas meet nest-computed terms, which is where every recorded late
surprise lived"). Mini's mitigations are inherited: pinned-conclusion tests
per wired shape, non-vacuity checks on every `HYP`-shaped premise
(RECURSOR-DESIGN §7's vacuous-`HYP` failure mode), and the `MachineId` guard
against cross-apparatus mixing **[read, `carrier.rs`]**.

---

## 10. What gates 91-of-91-at-zero-gaps (the library worklist)

> **Nothing on this list gates anything today.** Every row is done or
> superseded, including the two later-added blockers: `rec_acc` landed
> 2026-08-01, §5.3/§5.2's carriers are `derived/src/inductive/family/` with
> `mini/src/class_s*.rs` above them, the `finord` blocker is
> `derived/src/cumul/finord.rs`, and the dependent eliminator is
> `derived::inductive::DepRecursor` wired by `mini/src/rec_dep.rs`. The
> function-eta row already carries its own correction in the closing paragraph
> below. The criterion the section was named for is met —
> `constEv = typeEv = 218`, `gapped = 0` — so read the rows as the record of
> what was owed, never as what is owed. The one thing genuinely unbuilt in the
> tree is **nested inductives**, which this list never had.

Named so the success criterion is honest. Verified against
`LIBRARY-BACKLOG.md` (headings and status **[read]**) and the design docs:

| item | status | mini files it gates (inference from nanoda's ledger shape) |
| --- | --- | --- |
| n-ary `dprod_in_universe` (Π typing at a prefix) | LANDED (entry 2) | the former largest `ty_pi` row — available to mini day one |
| `acc` carrier | DONE (entry 1) | — |
| `rec_acc` (accessibility recursor) | **in flight now** (`derived/src/rec_acc/`, live agent) | prerequisite of §5.3 |
| §5.3 subsingleton elimination + §5.2 `good`/indexed carriers | BLOCKED on `rec_acc` (entry 8) | indexed families: `042/068/077` (`RBTree`), `Eq.rec` users |
| function-typed recursive args (`Σ(z::γ)` fibre) | **non-indexed: landed** (`mini/tests/infinitary.rs`, `constEv = 6`, no `waiting` key). **Indexed: the carrier landed 2026-08-06** (`derived/tests/family_infinitary.rs`); what is left is `ctor_ix`'s two bridges — see `indexed_infinitary_ctor.lean`'s header | `116_rtreeRecReduction` |
| cumul generalisation past `B(a) ∈ ω` (`finord` blocker) | named in WIRING verdict 5, not started | `⟦T⟧ ∈ ⟦Type 0⟧` for general-path inductives — hits mini harder than nanoda (§7, no recognisers) |
| function eta lemma (graph extensionality at a typed term) | not in backlog yet — **this design adds it** | every `tryFunEta` site; nanoda admits it today |
| interpreted structures: projection membership, structure eta, unit-like subsingleton | follows from zone B + per-structure lemmas; not separately in backlog | `inferProj` results, `tryStructureEta`, `def_eq_unit` analogues; `081_PSigma.snd`'s known escape |
| quot wiring (constructions LANDED, entry 6) | mini-side wiring | quot files |
| general iota wiring (`GenRecursor` → whnf steps) | derived layer landed (RECURSOR §10); wiring is §9 zone B | every `*RecReduction`/`*RecEqns` file on the general path |
| **a dependent eliminator** — `⊢ ∀t ∈ ⟦T p⃗⟧. rec(t) ∈ app(C,t)` at a *variable* motive | not started; `GenRecursor` is simply typed and RECURSOR-DESIGN §5.3's Σ-target variant is a sketch | `⟦T.rec⟧`'s own typing for every class-(T) declaration — **22 pairs**, the largest single library row |

Everything else mini needs exists and is in use by nanoda today (tower,
funspace, prop split, beta_conditional, the congruence family).

**This section said the backlog was *behind* zone B on the critical path, and
that was wrong — it was invisible, which is not the same thing.** The reading
came from an evidence ledger in which every row was an uninterpreted
inductive, so `FunEta`, `StructProj`, `UnitLike` and the cumul item all read
zero. Building zone B's boundary (`mini/src/zoneb.rs`) turned 36 of the 223
pairs into library rows immediately, and neither of the two items they name is
in the table above:

| item | status | what it gates |
| --- | --- | --- |
| `cumul::sigma_n` wired to a checker's field typings | constructions exist; the **mini-side bridge does not** | every constructor with a non-recursive field — `Prod`, `PProd`, `PSigma`, `List`, `TwoBool`: **27 pairs** |
| `cumul::Chain` parameterised over a tower `Level` | `u1` is a field set from `tower.at(1)`; `Chain::assemble` takes a `Level` but is `pub(super)` | `⟦T⟧ ∈ ⟦Type n⟧` for every `n ≥ 1`: `Prod` at σ = (1,1), `TypeWithTypeField(Poly)` — **9 pairs** |

So the backlog is **beside** zone B, and the two entries above are ahead of
the four this table already had — those four are still unreached, for the
original reason. The function-eta lemma is the one item that needs nothing:
it landed as `derived::ext::funspace_ext` and mini's `conv::fun_eta_leg`
composes against it already.

---

## 11. Where mini and nanoda must agree, and how it is checked

1. **The schedule.** Same `Instantiations` code, same `DEFAULT_LEVELS`, same
   seeds — agreement by construction, plus mini's own
   unpredicted-instantiation row pinned at zero (§3).
2. **Acceptance vs mini-lean** (port fidelity): a committed fixture table of
   mini-lean's per-file verdicts on the 91 exports (generated once with
   `lake build` outside this repo's CI — mini-lean is not a workspace
   member), compared by `mini/tests/tutorial.rs`. Any divergence is a
   red test naming the file. The two deliberate strictness deltas (§6.4
   beta-domain check, §6.5 proof-irrel type check) are watched by exactly
   this gate.
3. **Acceptance vs nanoda**: `scripts/mini-vs-nanoda.sh` produces a
   two-column verdict table over the 91 `good/` exports and the 42 `bad/`
   ones — negative agreement matters too: both must *reject* the bad files,
   evidence or no evidence. Divergences are not necessarily bugs, since
   mini is allowed to be more permissive than the official kernel (the
   guarantee is the certificate, not acceptance fidelity), so the gate's job
   is that every divergence is a **named** one rather than that there are
   none. The expected set is not empty and is not classified four ways: two
   rules name it — `out-of-scope` (mini declines a file declaring its own
   axiom, §0.6) and `reason-only` (nanoda's exit status cannot separate a
   decline from a reject) — and anything else, including a crash on either
   side, fails. Measured 2026-08-08: **130 agree, 2 out-of-scope, 1
   reason-only** of 133. `ci/check-mini-vs-nanoda.sh` is the CI harness
   around it; that file argues why there is no committed waiver list here
   when `scripts/arena.sh` has one.
4. **Gap ledgers**: mini's `Gap` enum rows vs nanoda's `Admit`/`TyGap` rows
   per file. These will *not* match numerically (different architectures
   count different events); what must match is the **explanation**: a file
   at zero in mini and nonzero in nanoda is a threading-debt finding for
   task #29 (the point of the exercise), and the reverse is a mini port bug
   or a §7 no-recogniser consequence, which the table must say.
5. **Ratchets**, copied from nanoda's harness style: `FULLY_DERIVED` list
   (files pinned at zero gaps — starts with the 27 inductive-free), per-file
   gap budgets that fail on regression *and* on unrecorded improvement, the
   audit-row-zero test, and an escapes-analogue: mini has no escape ledger
   because escaped assumptions cannot exist (an assumption is introduced
   only by `Scope` and discharged at its close; `Sealed` refuses anything
   that leaks) — a test asserts the *mechanism*: `Sealed::new` failures at
   the store funnel are zero across the corpus.
6. **The first blocker** (§0.6), which is a ratchet of a different kind:
   `tutorial_first_blocker` runs the corpus armed, finds the first export that
   stops, and pins *which* `(declaration, σ)` and *which* `Gap`. Green means
   the recorded blocker is still the one in the way; red means it moved, and
   the failure carries the whole report for the new one. Unlike the budgets in
   item 5 it pins an **ordering**, which is the thing a per-cause total cannot
   express and the reason a table of residual pairs kept hiding what to do
   next.

What is *not* checkable and should not be pretended: term-level agreement of
the two interpretations. The two runs mint independent symbol numberings in
independent `kernel::Env`s (brands make them incomparable by design
**[read, `thm.rs` brand machinery]**). Agreement lives at the
verdict-and-ledger level only.

---

## 12. Ordered implementation plan

1. **Crate + data types + converter + schedule** (§1–3). Exit: all 91
   exports parse, convert, and schedule; the corpus facts this design
   flagged as empirical get measured (does any tutorial export contain a
   `strLit` or a `natLit > 10`? does every export recursor match the
   generated name/level order?).
2. **Scope + Sealed + Ev + prelude bootstrap** (§4, §5, the `Prelude`
   assembly against `derived/`). Exit: the scope module's unit tests pin I2
   (a hypothesis discharged out of order is caught), `discharge` produces
   the `∀`-`→` shape, `Sealed` refuses a hypothetical theorem.
3. **The Term-level library decision** (§7.3): either the extraction lands
   in `derived/` (coordinated with the `tg.rs` agent) or mini vendors the
   clone. This gates step 4's lambda/Π clauses; do not let it float.
4. **`kernel.rs` for the inductive-free fragment**: `infer_type`, `whnf`,
   `assert_def_eq`, declaration pipeline for `axiom`/`def`/`theorem`; the
   interpretation dispatch. Exit: **the 27 inductive-free exports at zero
   gaps** and acceptance fidelity on all 91 (inductive files accepted with
   gaps). **LANDED 2026-08-01**, and the exit criterion is now a ratchet
   (`tutorial_evidence_ledger`): 93 of 223 pairs derived, with the whole
   residue attributed to zone B and to declared axioms, and the threading and
   library rows at zero. §0.5 has the table.
5. **Zone A + zone B inductives** (§9): shape zone port, spec builder with
   positive declines, `Inductive`/`GenRecursor` wiring, iota into whnf.
   **This is the riskiest step** — named per §9; it is also the step with
   the highest information yield, because mini lands the general-path
   wiring that `WIRING-DESIGN.md` designed for nanoda, in the codebase
   without the confounders, first. **Zone A was already in the port; zone B's
   boundary — the declaration walk, the carrier, `DeclUniverse`, and the
   Lean-facing λ-nests for the type former and the constructors — landed
   2026-08-01** (`mini/src/zoneb.rs`), with the eliminator trichotomy deciding
   the branch per declaration. Outstanding, in the order the ledger puts them:
   the two `derived/` items of §10, the recursor nest with its ι rules, the
   `Prop` classes, and indexed families.
6. **Quot wiring; structures** (projection membership, structure eta,
   unit-like); the **eta lemma** as a new `derived/` construction (backlog
   addition, one file, `# Interface` header).
7. **Harness + agreement tables + ratchets** (§11) — built incrementally
   from step 4, complete here.

Steps 1–2 are independent of the live agents' files entirely; step 3 is the
single coordination point.

---

## 13. Adversarial review — risks, and what this design could not settle

**Where this design is most likely wrong, in order:**

1. **The whnf-signature deviation (§6.4).** The owner's target signature
   threads the typing *into* whnf; this design keeps the primitive untyped
   and puts inference at the redex. If the owner's intent was that the
   checker-level derivation (not the kernel `Thm`) flows down the
   reduction — a `Typed`-carrying cursor — that is a real alternative:
   it avoids re-inference at compound arguments at the cost of a
   derivation-tree type mini otherwise doesn't need. The census's stage-2
   text supports either reading. Mini is the cheap place to measure both;
   the design commits to the simpler one and marks it as the first thing to
   revisit if step 4's corpus run shows pathological re-inference depth.
2. **Strictness deltas vs mini-lean** — **one of the two is gone and the
   other is narrower than this section said.** §6.5's proof-irrelevance type
   comparison turned out to be unnecessary altogether (see §6.5): each side
   reaches `•` from its own type. §6.4's beta-domain check survives, but only
   on the branch where the argument's inferred type and the `λ`'s domain have
   *different interpretations*; when they agree on the nose — which subject
   reduction makes the normal case — no conversion is asked for at all. What
   remains is argued acceptance-neutral by subject reduction and not proved;
   the fidelity gate is the detector (91/91 accepted, 42/42 rejected as of
   2026-08-01), and the documented fallback (weaken to `Gap`) keeps the axis
   separation.

   A third delta was introduced deliberately and is recorded here rather than
   discovered later: `inferType`'s `.forall` clause whnfs the codomain's sort
   **inside** the binder's scope, where mini-lean does it outside. The reduct
   is the same — `tb.ty` reduces to a `Sort`, and a sort mentions no local —
   but the *certificate* for the transport belongs in the `Γ` the binder
   opened, and computing it outside would either lose it or violate I2. The
   fidelity gate watches this one too.
3. **Performance without memos — and the proposed remedy is the wrong one.**
   Re-inference inside whnf inside defeq is exponential in the worst case.
   Mini-lean survives the corpus with the same recursion shape, but it does
   strictly less work per step (no interpretation, no kernel calls).

   This section used to say the contained fix is "a per-declaration memo
   storing only `Sealed`-able (hypothesis-free) facts — the same guard
   nanoda's caches use". **That is wrong, and it was established by hitting
   the blow-up rather than by argument** (2026-08-01, first threaded run of
   `infer_type`). The cost is not repeated *proving*, which a memo would fix.
   It is repeated **traversal**:

   * `interp` needs the proof/non-proof clause, which is `sort(e)`, which is
     `lvl(type of e)`, which is `infer_type`.
   * A threaded `infer_type` wants `⟦e⟧` for its `Typing`, so it called
     `interp` on the *same* node. Two exact functions, each needing the other
     at the same argument: the first run **overflowed the stack**.
   * Breaking the cycle by passing the known type downwards terminates, but
     leaves the classifier calling `infer_type` once per node while
     `infer_type` builds evidence — quadratic in kernel calls.
     `077_RBTree.id_spec` went from about a second to **8m20s**; suppressing
     evidence construction inside the classifier took it to 3m20s, still two
     orders of magnitude too slow, so a third cost remains unaccounted for
     and must be profiled rather than guessed at.

   A `Sealed` memo addresses none of that: nothing is being re-proved. **The
   fix is structural — `infer_type` must build `⟦f a⟧` compositionally, from
   its sub-`Typing`s' own `tm`s, and never traverse a second time.** That
   removes the cycle and the redundancy together, and it is the shape to port
   to nanoda.

   **The third cost, located by reading the path rather than measured.**
   `Checker::push` interprets the binder's domain (`let dom = self.interp(&ty)`).
   So the recursion is not one cycle but two interleaved ones:

   ```
   interp(e) → term_clause(e) → infer_type(e) → push(A) → interp(A)
             → term_clause(A) → infer_type(A) → push(A′) → interp(A′) → …
   ```

   Each step is on a strict subterm, so it terminates — but the branching is
   exponential in **binder depth**, and it is invisible while `infer_type` is
   cheap. That is why the same structure costs 0.3s at the interpretation-only
   commit and minutes once `infer_type` builds evidence: the threading did not
   introduce the blow-up, it made an existing one affordable to notice.

   This is the same principle again, so the fix is uniform: **every
   interpretation must come from a `Typing` already in hand.** `push` takes
   `⟦A⟧` as a parameter — `infer_type(ty).tm`, which the caller has just
   computed — rather than recomputing it, and `infer_type` builds `⟦f a⟧` from
   its sub-`Typing`s. There is then no separate interpretation traversal at
   all: `⟦e⟧` *is* `infer_type(e).tm`.

   **Measured after the rebuild (2026-08-01):** `077_RBTree.id_spec` goes
   8m20s (naive) → 3m20s (evidence suppressed in the classifier) → **1.9s**
   (compositional), against 0.3s at the interpretation-only commit, which
   built no kernel terms at all. The exponential is gone and nothing is left
   unexplained, so the `perf` run this section previously called for is not
   needed.

   **What this does *not* establish.** It is tempting to say the rebuild also
   removed a latent defect that would have bitten eventually. The numbers do
   not support that. The exponential existed at the interpretation-only commit
   but was **unreachable**: nothing there called `infer_type` from `interp` at
   a depth where it could bite, because `infer_type` built nothing worth
   paying for. It was a defect waiting for a caller, and threading was that
   caller. The fix is right on its own terms and does not need the stronger
   claim.
4. **The general-path-only decision (§7)** costs mini early parity with
   nanoda on `Bool`/`N`/`List` files (cumul `finord` blocker). If the owner
   wants those files at zero in mini before the cumul generalisation lands,
   the alternative is porting nanoda's recognisers — recommended against,
   since it duplicates exactly the scaffolding mini exists to obsolete.
5. **Zone A's evidence-free status** rests on the census §1.7 argument
   (shape judgements have no consumer). If §5.2's `spec` judgment work later
   gives constructor-parameter defeqs a consumer, zone A's `defEqParams`
   legs get one too; the `Vec<Conv>`-returned-and-ignored convention (§6.7)
   is what makes that future threading a local change.

**Could not settle here (each is a named, bounded follow-up):**

* The exact function list for the §7.3 extraction — needs a pass over
  `tg.rs` by whoever executes it (by name here, but signatures and
  private-helper closures need the file open, and the file is being
  edited).
* Whether the tutorial corpus exercises `strLit`, `natLit > 10`, or a
  recursor whose exported name/levels deviate from mini-lean's generation
  order — all empirical, all measured at step 1.
* The axiom-inhabitation policy (`Gap::Axiom` vs a separate assumption
  ledger) — owner call; zero-cost on init-prelude by measurement, expected
  zero-cost here, but "expected" is not "measured".
* Whether mini should also run the arena `bad/` suite (mini-lean handles
  the tutorial only; negative agreement with nanoda on the subset both
  parse is cheap and valuable — proposed in §11.3, not committed).
* mini-lean verdict fixture provenance: generated outside this repo's CI
  (Lean toolchain dependency) and committed — acceptable, but it is a
  fixture someone must regenerate if the mini-kernel upstream moves.

**Is the port worth it at all?** Yes, and the evidence is in this tree
rather than in enthusiasm: the census shows nanoda's remaining threading
work is dominated by decisions (binder representation, whnf dataflow,
cache/hypothesis interaction) that are *entangled with caches and arenas
there* and *free-standing here*; the wiring design names its riskiest step
as one mini must build anyway and can build first; and the one measurement
that most strongly justifies evidence-threading — `discharge_families`
firing zero times in 1 378 offers (retry-at-the-boundary cannot replace
threading) **[read, census §1.9]** — is an argument that the design must be
built *clean somewhere* to be ported *confidently anywhere*. Mini is that
somewhere, and its gap ledger at completion is the first honest statement of
what the library, as opposed to the threading, still owes.
