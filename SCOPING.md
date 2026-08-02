# How to scope a blocker here

Written at a handoff. Not design — the derivations in this repository are
worth nothing once the theorem is proved, and the design notes already carry
them. This is the part that has survived: how to find out what a blocker
actually is, which claims about it are reliable, and which are not.

Read it before the first `--block` run, not after.

---

## 1. Calibration — which kinds of claim held and which did not

Stated by *kind*, because the successes and failures sort cleanly and the sort
is the useful part.

**Reliable: static structure.** What an export says, what a theorem states,
what the thesis contains. Seven declarations decoded from `.ndjson` over this
run — `RBTree` and its recursor, `Quot.sound`, `PredWithTypeField`, `And`,
`Acc`, `BoolProp` — and every reading held under later measurement. Three
thesis checks, all three finding something the surrounding prose had wrong (§4
below). Reading the export is the cheapest thing available and it has never
once been the thing that was wrong.

**Unreliable: dynamic behaviour.** What order code runs in, what a route will
do downstream, what a fixture that does not exist yet will reach. Every error
below is this kind:

* **`042` ordering.** I claimed the summand ceiling would fire before the
  indexed guard at `u := 1`, having **quoted the guard that makes that
  impossible in the same report**. The mechanism was right and Milo confirmed
  it independently; the ordering was wrong because I never traced control flow
  to the site. *Rule that came out of it: never assert an ordering without
  following the function to the return.*
* **`084`/`086` → `StructProj`.** I predicted they would move to a projection
  row when class (P) closed. They closed outright, `fullyInterpreted=1`,
  because a projection out of a `Prop` is a proof-valued application and
  `⟦proj x⟧ = •`. I was predicting a route's downstream behaviour without
  tracing the route.
* **The `mᵢ > 0` decline.** Right about the exports — no corpus witness — and
  wrong about what is reachable, because Quinn's fixtures reach it directly.
  *Reasoning from the corpus as though it were closed.* The corpus is a lower
  bound on demand, never an upper one, and it stopped being one the day
  fixtures started being generated.
* **A near-miss worth recording.** In the class-(S) scope I nearly filed
  `rec_typed`'s `fs(1,T)` as a gap, on the grounds that `dprod(∅,·) = {∅}`. It
  dissolves because mini's recursor nests open `∀t` (`rec_dep.rs`,
  `depth = np + 1 + n + 1`). I checked before asserting, but only just, and the
  shape is identical to the three errors above.

**Efficiency degrades before accuracy does.** In the last round I cycled
through three wrong hypotheses on why `070` survives and `069` does not —
per-σ classification, a mis-located proof short-circuit, a stale audit — before
running the one command that settled it (`--block` on `070`, reading the
printed `⟦ty[σ]⟧` for a `•` in the argument list). The answer was right; the
route to it was not. If you are on your third hypothesis, stop and find the
decisive one-line measurement.

**The general rule.** Anything you can read, read. Anything you would have to
predict, measure instead — `--block` is cheap, single-file, and answers most of
these in one run.

---

## 2. The standing questions, with their instances

These are the questions that have paid. Ask all of them before sizing
anything.

### "One problem or several?" — five for five

Never once has a gap label covered exactly one problem in the way its name
suggests.

| label | what it actually covered |
|---|---|
| `fun-typed-rec-arg(Acc)` | the **carrier**, not the recursor; the reflexive field was true and irrelevant |
| `prop-inductive(·)` | four tiers — former only, former+recursor, former+projection, indexed — of which one was truncation |
| `recursor(·: class (S))` | genuinely one construction, three declarations, `k = 0` its degenerate case |
| `indexed-family(·)` | four problems with four different owners: class-(T) Prop motive, class-(T) value motive, class-(S) carrier, class-(P) carrier |
| `no-interp(BoolProp.a)` | one pair, not a class — every *applied* occurrence short-circuits |

Answering it costs one census and it has changed the size estimate every time,
in both directions.

### "Is the label naming where the walk stopped, or what is missing?"

Almost always the former. `fun-typed-rec-arg(Acc)` is minted by the
constructor walk while building the *carrier*. `indexed-family(SortElimProp)`
is minted while building a carrier, not an eliminator. `no-interp(BoolProp.a)`
is minted on the *type*, through a constructor. The label is a location; the
obligation is what `--block` prints on the `obligation:` line.

### "Is the obligation the type or the value?"

`--block`'s `obligation:` line distinguishes them and it has flipped the answer
three times. `Acc` (`117`/`118`) owes its **type** — which is why the recursor
was never the blocker. `069` owes its **type**. `068` owes its **value**. A
declaration whose type mentions the constant being built fails upstream of
everything the design note is about.

### "How many σ, and are they the same problem?"

Usually not the same problem. `And.rec` at `u := 0` is a proof; at `u := 1` it
is a large elimination. `117` is `Acc.rec.{0,0}`, a `Sort 0` motive with no
`T`-policy; `118` is `Acc.rec.{1,1}` at a constant motive. `068` and `077` are
both `RBTree.rec` and share no construction. **Check the recursor's own level
arguments at each scheduled σ before assuming one construction serves them.**

### "Does the thesis have a clause here, or is this a §5.4-shaped silence?"

Three instances, three *different* answers — which is why it must be checked
rather than inferred:

* **Hidden gap.** `Quot` at `Sort 0`: the interpretation clause is stated
  uniformly (`thesis.txt:2132`) but soundness is proved only for `n ≥ 1`
  (`:2353`), and `lift`'s target likewise (`:2359`). Nothing announces this.
* **Clause present.** Class (P): the small-eliminator rule is right there at
  `:1813–1815`, `ulift_ℓ ‖·‖`, with its justification at `:1816–1818`. The
  surrounding prose implied it was missing; it was not.
* **Declared silence.** The recursor and ι: `:1893–1901` says outright that
  "the introduction rules and the recursor … will be left as future work".

Read the lines. All three took under five minutes and each changed a scope.

---

## 3. Corpus facts that are not written down anywhere else

* **`DEFAULT_LEVELS = [0, 1]`** (`checker/src/instantiations.rs:117`). A
  declaration demanded by nothing is checked at two instantiations, and those
  two routinely exercise **different branches**. This is the single most
  load-bearing scoping fact on the project and it is easy to miss: it is why
  `062` is two problems and why `042` needed the rung-general universe.
* **Demanded declarations inherit σ through the fixpoint** from whatever uses
  them — `Quot.sound` gets `{0}` and `{1}` from `quotSoundType`'s value, not
  from the defaults.
* **The multi-parameter schedule is not the product and I never worked out the
  rule.** `punitRec` (2 level params) got 2 pairs; `accRecType` (2 params) got
  1. Unknown, and worth knowing before anyone predicts a pair count.
* **`Declaration::Quot` and `Declaration::Inductive` bear no pairs at all**
  (`mini/src/ledger.rs:289`). Building their interpretations moves **no ledger
  number**. A flat delta after landing a carrier is expected, not a failure —
  the movement shows up on the declarations that consume it.
* **`bad/` contains declarations with no recursor at all**
  (`large-elim-param.ndjson`: `False`, `True`, `MyBool.{u}`). Any
  `|rec.lparams|` comparison classifies them as small-eliminating on that
  basis. Only reachable in `bad/`, which acceptance rejects, but it is why
  `large_eliminating` computes rather than reads.
* **`RBTree` is the only §5.2-indexed class-(T) declaration in the entire
  corpus**, tutorials and prelude alike. Thirteen distinct class-(P)
  declarations in `good/`, verified by two independent sweeps.
* **Two throwaway scripts did most of the work and they are in scratchpad, so
  they are gone.** Rebuild them first; they take ten minutes and they are the
  reason the export reading held. (1) A decoder: fold the `in`/`il`/`ie` lines
  into name, level and expr tables, then pretty-print each `inductive`/`def`
  record's type and value. Watch the two encodings that bite — a name node is
  `{"str":…}` *or* `{"num":{"i":…}}`, and `rec.levelParams` is
  `[motive, decl…]` with the motive **first**. (2) A census: walk every
  `inductive` record in every export, peel `np + ni` binders, read the
  resultant sort, and classify (T)/(S)/(P) by `provably_nonzero` then by
  recursor level count. Run it over `good/` and `bad/` **separately** — mixing
  them is what produced the phantom class-(P) rows above.

---

## 4. Where the prose is still wrong

Corrected in place by me, with the reason in each commit message — `592f4f6`
(`QUOT-MODEL`), `21a93bf` (`LEVEL-POLYMORPHIC-INDUCTIVES` §3.5), `15c40bc`,
`820bd07`, `b89d621` (`INDEXED-DESIGN` §2.2, §5.3, §6.2, §6.4, §9, D7).

**Known still stale:**

* **`derived/src/inductive/motive.rs`** documents `cod_at_funspace` as "*the*
  way to discharge `COD`". It returns `None` at every input — a
  mis-association at `motive.rs:197`, `k = h ∧ (mx ∧ my)` while `gen_under`
  gets `and(h, mx)`. It is dead, it has **no live caller anywhere**, and
  `rec_dep.rs:1037` pins the `None`. The module header still presents it as
  live. Fixing it needs a consumer invented to justify inverting the pin;
  there is none.
* **`mini/src/recursor.rs`**'s header routes the class-(S) obligation through
  `rec_typed`'s `fs(1,T)` and worries about retargeting to `fs(A_φ,T)`. That is
  not the path: the nest opens `∀t`, so there is no function to build and the
  scope atom supplies what the retarget was for. I reported it; I do not know
  whether it was corrected.
* **`INDEXED-DESIGN` §5.1** still reads as *the* indexed recursor
  (`⟦T.rec⟧ := app(grec(…), t)`). It covers the value motive only. §5.3 now
  says so, but §5.1 does not say it about itself.

**Never audited by me** — assume nothing about their currency:
`MEASUREMENTS.md`, `THREADING-CENSUS.md`, `LIBRARY-BACKLOG.md`, `LOCALS.md`,
`PERF-REVIEW.md`, `DERIVED-AUDIT*.md`.

---

## 5. A pointer at binder congruence — explicitly not a scope

937 of 988 gapped conversions, one reason, `Cause::Threading`. I did not scope
it and this is not one. Three things a scoper should know before starting:

1. **The construction exists.** `Gap::BinderCongruence`'s own doc:
   `dprod_ext_n` / `cond_ext_n` / `lam_ext_n` "take a discharged family over a
   scope opened on `⟦A⟧`, and the recursive body conversion is not threaded
   through that scope yet." So this is threading, and the derived side is
   probably owed nothing — which has been the answer three times running.
2. **Ask "one problem or several" first, and note that it is not currently
   measurable.** `Gap::BinderCongruence` is a **payload-free enum variant**, so
   all 937 are one indistinguishable bucket covering *three* different `ext_n`
   rules. `ConvStats` attributes by reason, and the reason cannot tell you
   which rule is wanted. Giving the variant a discriminant is a small change
   and it is the same defect Otto just fixed, one level further down — the
   counter is now attributable to a reason but the reason is not attributable
   to a rule.
3. **`--dump-theorems` (`f98c5e1`)** prints stored conclusions with declines in
   place. I never used it. It is very likely a better census instrument than
   anything in §3 and should be tried before writing another script.

---

## 6. The one habit worth keeping

Every good finding on this run came from the same move: **the design note said
X, the measurement said Y, and Y was right.** `Acc`'s blocker was the carrier,
not the recursor. `069` was a constructor, not a projection. Class (P) was four
tiers, not one. The thesis had no `Sort 0` quotient clause. `084`/`086` closed
outright.

The notes in this repository are unusually good and are still, reliably, one
round behind the code. Trust them for *intent* and measure for *state*.
