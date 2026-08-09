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

### A thirteenth: a supplier's *typing* fits and its *application* need not

*(Added when `sigma::push` was consumed. It is the tenth category one field
further along again: there a decline's statement travelled and its direction did
not; here an entire interface travelled — statement, direction, guards, both
keyed theorems, non-vacuity — and what did not travel is that the theorem the
**consumer's own obligation** is stated at applies the transported object to
something.)*

`derived::sigma::push` was scoped from `mini/src/rec_dep.rs`'s `PUSH` decline,
built to that scope, and fitted unadapted — the fifth `derived` interface in a
row to do so. It closes the `u₁ = 0` clause outright. It cannot close `u₁ ≥ 1`,
and the reason was invisible from either side's scope:

```text
push_in_funspace :  t ∈ fs(Aⱼ,W) → push(t,β₀(p⃗)) ∈ fs(β₀(p⃗),W)     ← the typing
dep_minor        :  … → app(app(Sᵢ, t), v) ∈ app(C, ctorᵢ(t))       ← the obligation
```

The first says the crossing exists. The second **applies `Sᵢ` to `t`**, and
`⟦Sᵢ⟧` is a function on the *other* side of that crossing. Both statements are
right; the transport has no place to act, because the obligation never mentions
the transported term. `DEPᵢ` at `su := ⟦Sᵢ⟧` is therefore not unproved but
*false*, at a general motive, and it is false for a reason no shape check
catches: `fs(Σ(z::γ),W)` and `dprod(b,⟦γ⟧)` are both well-formed sets and the
formula relating them is well-formed too.

Two things make this its own category rather than an instance of the tenth.

* **Both crates' scopes were complete and neither could see it.**
  `sigma/push.rs`'s "What mini must bring" is accurate line by line — the fibre
  stack, the ih atom at `⟨z,•⟩`, the one Leibniz over `Push::app` — and it is a
  list of what the *consumer* must supply. It has no line for what the
  consumer's own obligation says, because that obligation lives in a third file
  (`inductive/motive.rs`) that neither scope had reason to re-read.
  `rec_dep.rs`'s `PUSH` decline stated both theorems exactly and never stated
  the conclusion it was going to have to reach with them.
* **The repair is not on the consumer's side, and that is checkable.** The
  tempting move — have `mini` pass an *adapted* minor `S'ᵢ` with
  `app(S'ᵢ,t) = app(Sᵢ, push(t,β₀))` — fails at the induction hypothesis and
  fails for a stated reason: `dep_minor`'s `vⱼ` carries **no set typing**, only
  the pointwise family, and the `vⱼ` satisfying that family are not contained in
  any set (add a pair at a point outside `Aⱼ` and the family still holds), so no
  graph is defined at all of them.

> **When a supplier's interface fits and the row does not move, ask what the
> obligation *applies* the supplied object to, not whether its type is right.**
> One `grep` for the consumer's premise builder — here `dep_minor` and `iota`,
> both one file over from the interface that was read — settles it, and it is
> the same one-file-over the seventh and tenth categories both turned on.

The cheap instrument, and it is a *construction* rather than a read: peel the
obligation's `∀`s through `Thm::ax_inst` at labelled fresh variables, then build
the term you believe the subject is and compare with `==`. That is three lines,
it needs no printer, and it answers "is the minor applied to the binder itself"
with a `bool` — which a rendered formula would not have, because every term in
it prints as `⟨·⟩` (the interpretation's label registry knows only terms built
through `Interp::mk`, and `derived` builds these).

---

### A twelfth: the census is cheap enough to run per *axis*, and the axes disagree

*(Added the round after the eleventh, by running the eleventh's own instrument
across the axes it had not been pointed at. It is not a new principle; it is
what the instrument says when you aim it somewhere else, and the useful part is
that **one axis being clean does not travel to the next**.)*

The eleventh's census reported one number per declaration and read off three
axes (constructor count 5, plain fields 4, indices 3) as clamp-safe, with the
recursive slot as the thin one. Re-run with the *shape* printed rather than the
maxima — `(np, n, per-ctor k/m/γ-lengths/mask)` — the same one call site gives
38 distinct shapes, and three further axes come out of the same run:

* **Mixed constructors** — a constructor with slots of two kinds. **Two shapes,
  both at `m = 2`.** No shape anywhere has a mixed constructor at three slots,
  and none has *two* function-typed slots in one constructor at any width. This
  is the gap `122ac11` declined to close with a weak fixture, now measured
  rather than argued, and closed at `3330a39`.
* **γ-depth** — depth 1 at **five** distinct shapes, 22 builds. `|γ| ≥ 2` at
  none, which matches the standing decline. *No witness is not no gap* was the
  worry and here it does not apply: depth 1 is not a single fixture's accident.
* **Index arity × constructor count** in `family/` — `ni` reaches 3, `n`
  reaches 3, and **never together**: `ni = 3` occurs only at `n = 1`, `ni = 2`
  reaches `n = 3`. More sharply, and this is the one that matters: **`ni ≥ 2`
  and `m ≥ 3` never co-occur, and `ni = 3` never occurs with any recursive
  argument at all.**

The third of those needed a **second instrument at a different site**, because
a declaration-level shape does not say which *code path* saw it. The cheap one
is not another `eprintln!` in another builder — it is `#[track_caller]` on the
per-slot accessor (`IndexedDeclSpec::rec_index_vec`) printing
`Location::caller()` with `j`, `ni`, `m`. One run, and every call site in the
crate is listed with the widths it actually reaches:

> Of the library's ten `rec_index_vec` call sites, six reach `j = 2` (all at
> `ni = 1`) and **four never exceed `j = 1`**: `dep_rec::induction_step`,
> `dep_rec::indexed_iota`, `prop_rec::minor_atoms_at` and
> `prop_rec::induction_step`. Two more (`le::build`, `le_rec::build`) never
> exceed `j = 0`, where not even a permutation is pinned.

> **`#[track_caller]` on the accessor is the census the eleventh's instrument
> cannot give you.** The builder's instrument answers *"what shapes exist"*;
> this one answers *"which loop saw them"*, and the two differ whenever a shape
> reaches part of a module and not the rest — `prop_rec` is reached at `m = 3`
> at its inversion helper and at `m ≤ 2` at its two statement builders, in the
> same suite, in the same file.

And the honest part, which is the eleventh's own lesson one turn further along.
The eleventh says a fixture width is *cheap to measure*. It is cheaper still to
measure **per axis in one run** — the marginal cost of a fourth axis is a
`sort | uniq -c`, not a fourth round — and the reason four axes had gone
unmeasured is that the instrument had been aimed once and its output read for
the question that prompted it. **An instrument is aimed, and what it is aimed
at is a choice nobody records.** Print the shape, not the maximum: the maxima
answer the question you had, and the shape answers the ones you did not.

### An eleventh: a fixture width is a measurable quantity, and nobody had measured it

*(Added at `derived/`'s hygiene round. The clamp *principle* is already written
twice — §6 above, and `MINI-HANDOFF.md` §34. This entry is not the principle. It
is what happened to the principle after it was written down.)*

§6 closed a clamp in `family/`'s class-(S) index maps and stated the general
form correctly. It closed it **at that module**. One layer down, in the
non-indexed general and dependent recursors, six per-slot index maps were still
pinned by nothing at all, and the reason is arithmetic rather than reasoning:
no fixture in `derived/` reached a third recursive slot on those paths.

The way that was found is worth more than the six fixes. **Instrument the
declaration builder, not the loops.** One `eprintln!` in `Inductive::build`
reporting `(args, recs, γ-depths)` per constructor, one `cargo test -- --nocapture`,
one `sort | uniq -c`, and the whole suite's fixture census is 36 lines:

> Of 36 distinct declaration shapes built by `derived/`'s 875 tests, **two**
> have a constructor with three recursive slots — and both are the two tests
> §6's round added. Every other shape tops out at `m ≤ 2`. Constructor count
> reaches 5, plain-field count reaches 4, index count reaches 3; the recursive
> slot is the thin axis and nothing else is.

Six clamp mutations followed, and all six passed the full suite. That is not a
second finding; it is the same one counted. Then two fixtures at
`Rec, Plain, Rec, Rec` caught all six.

> **A test suite's fixture widths are a property of the suite, cheap to
> measure, and not implied by any amount of care about the code.** When a
> mis-index class is found and closed at one module, do not re-derive whether
> it can recur elsewhere — census the widths and read off where it already has.
> The instrument goes at the *source* of the arity, where there is one call
> site, not at the loops, where there are four hundred.

And the honest part: this seat read §6's clamp paragraph, understood it, and
would still not have looked here without being told to census. **Recognising an
inherited pattern is not the same act as checking whether you are repeating
it**, and only the second one is measurable.

### A tenth: a decline's *statement* survives the consumer and its *direction* does not

*(Added when `sigma::push` was built. It is the eighth category one field
further along — there the `cause` of a row was carried across a move; here it is
the **direction** of a theorem, and the theorem itself travelled perfectly.)*

The eighth category ends with the instruction that pays here: *"a crate that
declines an artefact for want of a consumer has written half of a future
blocker's scope; re-read those sections the round a row arrives at the file that
owns them."* It was re-read, the scope it had written was right, and **two of
the three things it said about the artefact were still wrong**, in the way a
decline is *structurally* prone to be:

> **A decline is written from the declining file's own side. Its statement of
> the missing theorem survives the move to the consumer; its statement of which
> *direction* of that theorem is wanted does not, because the declining file has
> no consumer to take the direction from — that is what "declined" means.**

`sigma/reindex.rs` declined `push` four times and sized the round trip as
`push(pull(g)) = g`, *"one `funspace_ext` over the two computation rules"*. The
consumer — a minor premise, which binds the *other* side — needs
`pull(push(t)) = t`, and that direction is not the same derivation read
backwards: it reduces at an arbitrary `q ∈ T(p⃗)` instead of at a tuple, so it
needs `Telescope::proj_mem[0]` to discharge the conditional computation rule and
`Telescope::eta` to come back, three chained equations where the declined
direction really would have been one existing lemma pointwise. The `funspace_ext`
the note named is the *last* of the three steps, which is exactly why the note
reads as complete.

**The cost axis fired at its documented size and the double is where §1 says it
is:** two extra equations for one pullback, one for each direction the seam is
crossed in. A round trip is a pullback with a name.

*(**And then the declined direction arrived, with a second consumer, and the
estimate it was given was exact.** The ι rule at a *use site* starts from Lean's
own function and returns to it, which is the shape `sigma/push.rs`'s decline
said a consumer would have to have; `push(pull(g,T(p⃗)),β₀(p⃗)) = g` cost one
`funspace_ext` over `reindex_at_tuple` pointwise and nothing more. So the
category above stands and gains a bound: **a decline's statement of the
*theorem* survives, its statement of the *direction* does not, and its size
estimate is accurate for whichever direction it was written about.** The note
was wrong about which direction the first consumer would want and right about
what that one would cost — and both halves were readable off the same paragraph
the day the second consumer arrived.)*

**The size axis fired the other way for the first time, and the reason is worth
the paragraph.** The note sized `push` at *"the same 15 lines"* as the file it
was declined in. Measured, non-comment: `Reindex::new` + `reindex_in_funspace`
is **91** lines and `Push::new` + `push_in_funspace` is **94**. So the *analogy*
was accurate to three lines in ninety-one, and the *number attached to it* was
low by six times.

> **A size given as an analogy is two claims, and only one of them is about the
> work.** "The same N lines as X" — check the analogy by measuring X, and drop
> the N. A note's author can see the shape of the neighbouring file and reliably
> cannot see its length; every instance of the size axis so far is a number
> quoted from memory beside a comparison that held.

The instrument was the eighth category's own one-line `grep`, run in the other
direction: `grep -rn 'push' derived/src mini/src` found the consumer's decline
(`mini/src/rec_dep.rs`) stating the two theorems it wanted **in full**, and the
two statements did not match the ones the library's decline had written down.
**When two files decline the same artefact from opposite sides, diff their
statements of it before building either** — the difference is the direction, and
it is the whole scope.

### An eighth category: a cause that travelled with its pairs

*(Added at `MINI-HANDOFF.md` §34. It is the seventh's mirror — there a static
claim was made without the search; here a *dynamic* classification was carried
forward without the measurement that would have refuted it.)*

> **When a row moves to a new site, its count moves, its key moves, and its
> **cause** silently does not. A cause is a claim about which crate owes the
> next step, and it is a property of the *site*, not of the pairs.**

`RTree`'s four pairs have now crossed four sites in five increments —
`fun-typed-rec-arg` → `ind-fibre-value` → `ctor` → `recursor` — and at the
fourth the axis was written `threading-incompleteness` because the *third* had
been one. It was wrong: `derived::sigma::reindex` carries a function into the
fibre summand (`pull`), which is what a **constructor** needs, and a minor
premise quantifies the other side and needs `push`, which exists nowhere. The
row was on `library-gap` and had been filed as mini's own wiring debt.

Two things make this worth its own category rather than a footnote to §1's
"census behind a blocker".

* **Nothing was inferred from a symptom.** The site was reached, the label was
  right, the pair count was right, and the derivation the note described was
  the derivation the code attempts. Only the *ownership* was carried, and
  ownership is the one field of a `waiting:` row that nothing downstream
  recomputes.
* **The check is one question and it has a name already.** `MINI-HANDOFF.md`
  §32 states it for a `Gap`'s imputed cause — *"a `Gap`'s imputed cause can be
  right at every site that has ever reached it and wrong at the first new
  one"* — and this is the same failure for a cause that is *carried* rather
  than imputed, one field along. **When you unblock something, re-ask what each
  downstream classification was validated on**, and re-ask it of the axis as
  well as of the label.

The instrument that answers it is the one the seventh category names:
`grep -rn '<the artefact>' derived/src mini/src`, without `head`. Here it
returned `push` as **prose only**, in the very file that would own it, in a
section headed *"what is declined, by name"* which states the theorem, sizes it
at fifteen lines, and declines it **for want of a consumer**. That section was
one round old and nobody had read it against the row it was about.

> **A crate that declines an artefact "for want of a consumer" has written half
> of a future blocker's scope. Re-read those sections the round a row arrives
> at the file that owns them** — it is the same check as §10's *"a scope that
> predicts a consumer should be re-read the round the consumer is claimed
> missing"*, from the other end, and it costs the same one `grep`.

### A ninth, smaller: a mutation that fails nothing, at a predicate whose two readings are provably one

Same round, and it is the *good* outcome of the rule rather than a failure.
`rec_dep::general_slot_declines` is written over `Inductive::ctor_slot_domains`
and the obvious mutation — swap it for `rec_slot_domains`, the other of the two
grains — **fails nothing at six cells**. The two grains differ per *slot*; the
predicate is per *constructor*; and at that grain they are the same predicate,
because `RecArg::general` is chosen exactly when some `γⱼ` is non-empty. The
second mutation, `any` → `all`, fails four of the six, and for a reason no
design would have predicted: `.all()` over a **fieldless** constructor's empty
slot vector is vacuously true, so `L.nil` declines and takes every plain
declaration with it.

> **Run both mutations even when one is obviously the interesting one.** The
> quantifier turned out to be load-bearing and the grain turned out not to be,
> which is the opposite of what the two names suggest — and the surviving
> mutation is a *fact about the interface* worth writing down, not a hole in
> the test.

### A seventh category: a claim whose evidence is a search, asserted from a read

*(Added at `MINI-HANDOFF.md` §33, and it is the cheapest of the seven to
avoid.)*

> **"Nothing reads this theorem" and "no function here does that" are `grep`s.
> They look like static reads — a statement's shape, which theorem exists — and
> this file has calibrated static reads as the reliable kind. They are not one:
> a static read is about the thing in front of you, and these are about
> *everything else*.**

Two instances, one round, both about the same theorem. `ext::dprod_const_fibre_n`
was called "stored and unread" by four consecutive `MINI-HANDOFF.md` sections
while `mini/src/quot_classes.rs` had been calling it for two days; and
"`retarget_set` takes no hole, so that is where the build fails" was a correct
reading of `retarget_set` and a wrong claim about the crate, which has
`congr_arg` and already used it eight lines from the call site above.

Neither cost correctness — the gaps were carried honestly and nothing
downstream was wrong. What they cost is **sizing**: four rounds deferred an
increment as an unbuilt construction, and the round that built it started by
reading the call site the notes said did not exist.

The check is one command and it is not "read the callee":

```sh
grep -rn '<theorem>' mini/src derived/src      # who already reads it
git log -1 -- <path>                           # and how stale is what I just read
```

§13's habit already says to date a static read of another crate. This extends it
in the direction that is easy to miss: **date a claim about your own crate too,
when the claim is that nobody in it does something.**

### A sixth category: a design note's two independent biases

*(Added after `QUOT-MODEL.md`'s `Sort 0` clause was built; split into two axes
after `Acc.intro`. Not any of the five below, and unlike them not a mistake —
these are **biases**, which makes them predictable and cheap to correct for.)*

> **cost** — a design is right about what a clause *is* and consistently **one
> β step optimistic** about what it *costs*.
>
> **size** — a note that sizes work by its **hardest named step** overshoots
> whenever that step is already built.

**They are two rules and not one signed rule, and the proof is that one
paragraph showed both.** `MINI-HANDOFF` §16 sized `Acc.intro` as *"a
construction the size of `iota_dep.rs`"* — 548 lines against a measured **57**
— while the `beta_spine` its cost half predicts was needed exactly where
predicted. A single bias with a sign cannot be optimistic and pessimistic in the
same paragraph; two axes can, and were.

**What distinguishes them is the object.** The cost axis is about the thing
being *transferred* — the **glue**: a design reasons about denotations, where
`⟦Quot α r⟧` and `⟦α⟧` are one thing, and the code holds terms, where one is a
redex over a stored λ-graph. Glue is invisible from a design, so it is
under-counted, and the gap is one reduction every time. The size axis is about
the code *around* it — the **body**: a note names the hardest step and sizes the
whole by it. Bodies are visible from a design; their *reuse* is not. `Acc.intro`'s
"hypothesis management, and that is the bulk" was `Scopes::open` plus
`Closed::discharge` — two calls — over `rec_dep::minor_at`'s existing walk.

**So the correction is per named step, not per note:**

| the note says | which axis | what to do |
|---|---|---|
| "the certificate transfers unchanged" | glue | **add a β step** |
| "and that is the bulk" | body | **check whether it is built** |

Bram's form of the second is the one to keep: *before accepting a size, ask
whether the named hard step is built — if it is, the estimate is measuring the
wrong thing.*

**The prediction had its third instance and held — and this is the first size
this project has got right in advance.** Both earlier downward errors came from
notes that *also* showed the upward one (`QUOT-MODEL`'s T6 beside its three
missing `beta_spine`s; §16's `Acc` size beside its correctly-predicted one).
`Quot.ind` was then sized by applying **both** corrections to the same
paragraph, and came out **40 non-comment lines with two β steps the note named
neither of**. Three of three. So the instruction stands as the operative one:

> **Apply both corrections to the same note rather than deciding which bias it
> has.** A note that names a hard body step is exactly the note that glosses the
> glue around it — check whether the body is built, and add a β step per
> transfer, in the same pass.

**The fourth instance is the first where both corrections landed on one step and
nearly cancelled, and the cost side won.** `bnd` under the binary sum was scoped
at **150–250** lines and measured **334** (`derived/src/cumul/sum_bnd.rs`,
non-comment, at `a3f0688`). The size correction fired as advertised — the note's
hardest named step was the stage *merge*, and the merge was already built as
`finite::bnd_bin_union`, worth about 165 lines that were never written. The cost
correction then ate all of it and more, because the β step the note glossed
appears **twice per instance**, not once: a pullback along a term-former is
reduced at the bound variable of the hypothesis *and* at the witness the
inversion hands back — two directions, two `beta_at` calls — and the inversion
itself costs an `∃`-elimination the note named nowhere.

Two things follow, and the second is the one worth carrying.

* **Cancellation is not a reason to skip either correction.** Applied
  separately, each would have produced a number closer to the note's than the
  truth: size alone says 85–150, cost alone says 250-plus. Only both together
  say *why* 334, and the why is what the next estimate needs.
* **Count the β steps by counting the directions the equation is used in, not
  the equations.** "Add a β step per transfer" is the rule as stated and it
  under-counts whenever the transfer is a *pullback*, because a pullback is
  reduced once going in and once coming out. `carrier_bnd` and `telescope_bnd`
  are the same shape and paid the same double. `9314954` factored all three into
  one `bnd_via_pullback`, which is where the doubling is now written down once
  instead of three times — and which is also the measurement that the three were
  one derivation and not three similar ones.

The quotient clause is the clean instance because all four corrections have the
same shape and none touches a mechanism:

| the note says | measured |
|---|---|
| `⟦Quot α r⟧` and `⟦α⟧` are "the same term" | β-related; **three** primitives need a `beta_spine` |
| T3/T5 are `f`'s certificate, "costs nothing" | plus one `congr_arg` in the `Π` symbol's domain slot |
| T6 is "the one genuinely new composed lemma" | not a lemma at a nest bottom; `derived/` owes **nothing** |
| `Quot.lift`'s nest is five deep | five is right; the *declared type* has six binders and the first build used six |

Every row is the same error and it points the same way: a design reasons about
*denotations*, where `⟦Quot α r⟧` and `⟦α⟧` genuinely are one thing, and the
code holds *terms*, where one is a redex over a stored λ-graph and the other is
not. The gap between them is exactly one reduction, every time.

**What follows for a reader sizing work from a design note.** Take the
mechanism as stated — it has been right every time — and add one β step
wherever the note says a certificate transfers unchanged. `MINI-HANDOFF.md`
§11.1's finding 1 is the same bias at a different layer: `derived` hands back a
term that is correct and not yet in the `Parts` table, so it cannot go under a
binder. The mechanism was right there too.

The one row that went the *other* way is T6, and it is the **first** instance of
the size axis above: scoped as a new lemma, it turned out to be nothing at all,
since a nest bottom holds its own binder and never introduces the quantifier the
lemma exists to discharge. `Acc.intro` is the second. Both were briefed to a
builder as larger than they were, and in `Acc`'s case that is part of why the
row sat — which is the cost of the size axis and the reason it is worth stating
separately rather than as a footnote to the cost one.

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
* **A negative fixture that pinned nothing, and passed for three commits.**
  `bnd_carrier`'s test asserted that a *recursive* declaration is refused, with
  a comment naming the fibre value as the reason — and handed the function a
  **different** declaration's `bnd(A)`, so it was refused two checks earlier by
  the conclusion comparison and never read a fibre value at all. The assertion
  was true, the comment was false, and the test would have gone on passing with
  the recursion story entirely wrong. This is the same family as the `042`
  ordering error and it is worse to catch, because a `.is_none()` assertion
  looks like it has been measured. *Rule: a negative fixture must be shown to
  reach the check it is named after — probe the `return None`s, do not read the
  function.*

**A fifth instance, and the cheapest instrument yet.** `BinderShapes::apply` has
five outcomes and the ledger counts only the failures, so four of its five rows
read `0` and nothing said whether that meant *solved* or *unreached*. Five
`eprintln!`s in a **detached worktree** — built, run over the corpus, thrown
away, never committed — answered it in one build: all four fire and all four
succeed. The same throwaway carried a prototype of the missing arm and turned
"`derived/` owes nothing" from a reading of an export into 1305 discharged
sites. **Instrumenting a throwaway build is measurement, not editing**, and it
is available even under a read-only remit; it should be reached for whenever the
question is "does this code path ever run".

**And the instrument itself can be wrong, which is the failure mode that
instrumenting invites.** A census of "which per-constructor loops in `family/`
are only ever entered at one constructor" was run by machine-inserting one
`eprintln!` above each such loop. Twenty of twenty-one sites reported 2 or 3;
`gval.rs` reported **1, twice**, against 41 entries at its two immediate
neighbours in the same call chain — a number that is the right shape, from the
right run, and false. A second marker at that function's *first statement*
reported 41 entries at up to 3. The wrong reading was not read wrongly and no
`wc -l` would have caught it: the generated marker was the thing at fault.
**A surprising instrumented count is checked by a second instrument at a
different site, never by re-reading the first** — and a site whose count
disagrees with its own callers is surprising by definition, so the neighbours
are the check that comes for free.

**A third kind of error, which the static/dynamic split does not cover: a
correct measurement transcribed wrongly.** I wrote "60 waiting pairs over **15**
distinct keys" into §6. The run was right, the cause split (26/28/6) was right
and reproduced exactly by an independent re-measurement, and the pair total was
right. There are **22** keys. Fifteen is the number of keys with *more than one*
pair — my aggregation printed `sort -rn`, and I read down the descending list
and stopped where the counts hit `1`, taking the head of a sort for its length.

Two things make this worth a paragraph rather than a fix. The plausible
reconstructions were both wrong — it was not a stale pre-class-(P) run, and it
was not a count of reason families (there are **7** of those, and 15 is neither
22 nor 7) — so *"what narrower thing could this number be measuring"* found
nothing, and only re-running the aggregation settled it. And a wrong count of
this shape is invisible: it is the right order of magnitude, from the right
command, on the right corpus. **The rule that comes out of it: never quote a
count you did not pipe into `wc -l` or `awk 'END{print NR}'`. Eyeballing a
sorted list is not measuring it**, and it is precisely the step where "read what
you can" stops protecting you, because the thing being read is your own output
rather than the code.

**A second instance, and the rule above does not cover it.** I recorded
`pair_in_graph` as having *no occurrence* in `mini/src` beyond an unused import.
It has seven, in `acc.rs` alone: built at `:164`, stored at `:145`, pinned at
`:351`. My grep ended in `| head -20`, and the `derived/` hits filled lines 1–19
with `mini/src/acc.rs:103` at line 20 — **I concluded absence from a truncated
listing.** Same family as the count above and a different fix, because this was
not a count: `wc -l` would not have helped.

> **`head` is safe for sampling and unsafe for concluding, and the two look
> identical at the terminal.** An absence claim needs the listing *without*
> `head`, or a `grep -c`. Any sentence of the form "its only occurrence is…" or
> "nothing calls this" is an absence claim.

The cost is not symmetric with a count being wrong, either: a wrong count
mis-sizes, a wrong absence claim **points at the wrong action** — delete the
import versus find the theorem a consumer.

**A fourth category, and it cost two rounds: "this cannot be measured yet" is
itself a claim.** On `072` I flagged the δ-redex conversion as unmeasurable
until the carrier landed; Wren measured it in one corner walk with opaque `B`
and `C`, because it is a conversion between two Lean `Expr`s and needs no
carrier. Wren then flagged the carrier branch as the unsized risk; it turned out
to be the smallest piece, because the §5.2 chain reads no level anywhere and
what was missing was a caller. Neither was a measurement error. Both were
**judgements about what could not yet be measured**, and one build refuted each.
The rule is the general one with the deferral removed: *if you are about to
write "not measurable until X lands", spend the build first* — the thing you
think is downstream of X usually is not, and the cost of finding out is the same
build you were postponing.

**A fifth, and it is the one that looks most like careful work: classifying by a
downstream observable instead of by the datum that decides.** Scoping `proj` I
grouped `And`, `PProd.{0,0}` and `PSigma.{0,0}` as class (S) because all three
project to `•`. Two of them are class (T). The trichotomy has exactly two
inputs — `zoneb::subsingleton` (Carneiro's SS condition, computed from the
declaration) and `provably_nonzero` (the declaration's own resultant sort) — and
I had the first from `elim_audit` and **inferred** the second from the
*parameter* sorts printed on the blocker's `⟦ty[σ]⟧` line. One decode would have shown
`Sort max(max(0+1,u),v)`, with a literal `1` in it, nonzero at every σ.

What makes it worth a paragraph rather than a fix: I had described the mechanism
**correctly** one paragraph earlier — that the `•` arrives from the λ clause's
proof branch, not from the `Expr::Proj` arm, which returns `tm: None` with no
`is_prop` test. That description is exactly right, and it is precisely what
should have stopped me: a `•` keyed on the *projection's type* being a `Prop`
says nothing about the *structure's* class, because a `Prop` field sits happily
in a `Type`-resultant structure. **A correctly-identified mechanism whose scope
is wider than the classification drawn from it looks like evidence and is not.**

`derived/…/family/le.rs` had already learned this on the *other* half of the
trichotomy — "the constructor count is not the test; `rec.levelParams` is, and it
is read, never recomputed". The rule generalises and should have been applied to
both halves: **read both inputs of the trichotomy off the declaration; never
infer either from a symptom, however well you understand the symptom.**

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
| `binder-congruence(dprod vs fs)` | one mechanism, but **six pairs split 3/3**: three definitions the fix certifies outright, three theorems that move to `iota(·.rec)`; and the row masked its own mirror |
| `indexed-family(SortElimProp: class (S) carrier at an index)` | **three** pieces with two owners — the carrier (`derived`), the constructor (three lines over theorems that exist), and the recursor, whose `minor_eq` is §5.3's delayed elimination and is `mini`'s |
| `indexed-family(SortElimProp2: class (P) truncation over an indexed base)` | **four** — carrier (ready), constructor (does *not* extend from the non-indexed one), recursor (`derived` owes it), and a δ-redex conversion in the alias's declared minor that is in no design note |
| `iota(·.rec)` | **four** constructions over six keys — a missing §6.2 *clause* (`Eq.rec`), a theorem built and stored and unread (`Bool`/`Prod`/`N`/`List`), one genuinely unbuilt (`RBTree`), and a third mint site that is **not ι at all** and has never fired |
| `ind-fibre-value(RTree)` | one *at `np = 0`*, and a **second, unnamed** blocker at `np ≥ 1`: `Inductive::build` refuses every non-empty `γ` whose fibre value mentions a parameter variable, one construction before the placement. `RTree` is `np = 0`, so the corpus witness cannot see it (`MINI-HANDOFF.md` §31). The `np = 0` half then closed and the row moved to `ctor(RTree: …)` — **and the arm it landed on had the wrong cause**, `Cause::Bug` by imputation, correct at every site that had ever reached it (§32) |
| `proj(·)` | **four** over five keys, split by the **carrier's** class — 12 of the 24 pairs owe an **interpretation** and 12 owe only a **typing**. I said one, corrected to three, and three was still wrong: two declarations I had grouped by what they *project to* belong with a third by what their *carrier* is (§1's fifth variant) |

Answering it costs one census and it has changed the size estimate every time,
in both directions.

**And the discarded-evidence pattern now splits, which is more useful than
another instance of it.** Five rows have turned out to hinge on a value computed
and dropped, and I had been recording them as one shape. Fen's `dep_bottom` pair
shows they are two, wanting **opposite** treatments: `ax` is hypothesis-free, so
it had to be **stored** on the declaration's translation; `PRE` is a *derivation
to share*, because its `Γ` is the caller's and generalising over the nest's
binders reaches no other minor — storing it would have been wrong. His
discriminator is the one to apply first: **does the consumer want it at the same
terms?** If yes, store it; if no, the thing to keep is the derivation and the
scope it was made in. This is the first test that tells apart *within* the
pattern rather than adding to it.

**A companion question that has now been wrong three times: "is this the last
X row?"** `binder-congruence` was called the last of its kind and was masking
four successors; `071` was called "the last non-ι row" and was one of fifteen
keys; `072` was called "the last `Scope` row" and is one of eight. Every time
the error is the same shape — a true statement about one *cause* or one *label*
generalised to the whole ledger — and every time there was a *better* true
sentence available at the same measurement: `iota(·.rec)` really is the only
remaining `Threading` shape, and `072` really is the last `indexed-family(·)`
row. **Name the quantifier: last row of what.** The narrow claim is usually the
interesting one anyway, because it is the one that closes a design note.

**And a corollary that cost Otto a retraction he did not owe.** A census taken
*behind* a blocking gap under-counts the **population**, not merely the demand.
`Mismatch(fs,dprod)` measured 0 occurrences and `iota(RBTree.rec)` measured "no
row at all"; both appear the moment the row in front of them is discharged. So
"zero in the corpus, therefore not a case" is only sound for a gap nothing else
blocks — and §1's `mᵢ > 0` lesson has this second edge. Otto filed his
`iota(RBTree.rec)` hypothesis against himself as *wrong*; it was right, and the
measurement that refuted it was taken through the mask.

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

**One exception, and it is a *class* of exception worth recognising: class
(S).** `sortElimPropRec.{u}` at `u := 0` and `u := 1` is one problem, and so
were `And`, `PUnit` and `ProjDataIndex` before it. The reason is structural and
readable rather than incidental — every class-(S) field is a proposition and the
major premise is a proof, so the minor is applied at `•⃗` whatever the motive's
sort is, and `Sort u₁` is never itself `Prop`, so the motive's own `Π` clause is
`fs` at every `u₁` (`rec_prop.rs`'s own comment, and the derivation there does
not branch on `u₁` except where the *stored term* differs). Where the σ do part
company is a **large elimination that computes** — class (T) — and that is what
the four instances above have in common.

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
* **A fourth kind: mini has a clause the thesis does not.** §6.2's `Π`
  interpretation is `⟦Πx:α.β⟧γ = ∏_{x∈⟦α⟧γ} ⟦β⟧(γ,x)` (`thesis.txt:2077`),
  **unconditionally**; the only split is proof-vs-value, at `:2075`/`:2077`,
  matching the proof-split translation's own split on `lvl(Γ ⊢ β) = 0` at
  `:1993–1995`. There is **no function-space clause anywhere** — the soundness
  argument at `:2231–2235` uses `∏` alone. mini's `fs` is its own third clause,
  an optimisation, and `dprod_const_fibre_n` is precisely the theorem that
  licenses it. Checking the thesis here does not find a gap; it finds that the
  *checker* added a clause and never wired its warrant.
* **A fifth: the thesis writes the missing object in symbols while the code
  carries it in prose.** The class-(S) carrier is stated at `:1886`
  (`⟦µt : ∀x::α. U_ℓ. (c:β)⟧ = λx::α. ulift_ℓ (acc^ϕ_r (x))`), `[p]` is defined
  at `:2057`, and `:2162` writes `[x ∈ acc(A,R)]` outright inside `rec_acc`'s own
  definition. Five headers in this repository describe that set in prose and
  nothing builds it (§6). Grepping the thesis for the *notation* found in one
  step what grepping the code for the construction could not.

Read the lines. All five took under five minutes and each changed a scope.

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
* **`Quot.ind`'s ι rule is uniform in `u`, confirmed at the level where it could
  have failed.** `QUOT-MODEL` §2.3's T7 — both sides proofs at every level, so
  no separate ι step — was asserted from a `u = 0` ratchet, which is the weakest
  place to assert a level-uniformity claim. `125_quotIndReduction` at `u ≥ 1`
  needed no ι step at all. A ratchet at the degenerate level is evidence about
  the mechanism and not about the uniformity; this one has now been checked
  where the two could have come apart.
* **A `Prop`-valued `Π` hides a missing dependency from its own type's typing;
  a dependent one does not.** Verified in the signatures:
  `cond_typing(&self, site, dom)` takes **no** domain membership, while
  `dprod_typing(&self, site, dom, dom_mem: &Thm, fibres, n)` takes one. So the
  `Prop` clause's `⊢ ⟦Π⟧ ∈ ⟦Sort 0⟧` is `cond_in_u0` and is unconditional
  whatever the domain does. Two consequences (Bram): a declaration scheduled at
  both a `Prop` and a non-`Prop` σ has **the non-`Prop` σ reporting the truth**,
  and one scheduled *only* at a `Prop` σ can pass with an absent dependency and
  **no row anywhere**. That is `typeEvMasked`'s shape without a counter to catch
  it. Before trusting a green `Prop`-σ pair, check whether the same declaration
  has a non-`Prop` σ; if it does not, the green means less than it looks.
* **A projection splits across σ exactly when the projected field's sort is a
  bare level parameter.** `Sort u` can be zero at one σ and nonzero at another;
  `Sort 0` and `Sort (u+1)` cannot. So `PProd.fst`/`PSigma.fst` are a proof at
  `u,v := 0,0` and data at `1,1` — *the same declaration owes a certificate at
  one σ and a term at the other* — while `And.left` and `Prod.fst` are one thing
  at every σ. This is the first row where σ splits the **obligation** rather
  than the construction, and it is why `SCOPING` and `MINI-HANDOFF` disagreed
  about a count while both were right (§2's fifth axis). The test is one look at
  the constructor's field types and it should be run before sizing any row whose
  declaration has level parameters.
* **The declaration that η-expands its eliminator is the one that reaches ι.**
  `069`–`072` each closed and produced **no successor ι row**, because
  `def f := T.rec` is a bare `Expr::Const`: nothing is ever *applied*, so no use
  site asks for a computation rule. The ι **row** moves only when a declaration
  applies its recursor to a constructor — `073`–`077` and `094`. So a run of
  alias-shaped exports keeps closing rows at a flat ι count, and that is the
  expected reading rather than a stall. `recursor.rs` §5.1 records the same
  observation from the other end.
* **A mint site is not a demand, and I published a count that conflated them.**
  I instrumented the ι mints and reported **114** at **nine** recursors over
  **nine** exports against the ledger's six, concluding the row understated the
  population. Fen then measured the half I had not: of 72 mint sites only **5**
  carried an interpretation, all `RBTree.rec`; he downgraded the untracked ones
  and checked that neither census moved, which is what proves the rest were
  noise. **`whnf` runs on the acceptance path too**, and an acceptance-only walk
  mints gaps that no certificate was ever going to consume. The discriminator is
  `tm_asked` — the same flag `note_conv` is gated on. So: instrument the mint if
  you want to know where code runs, but **count only the mints that carry a
  term** if you want to know what is owed, and say which you did.
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
  resultant sort, and classify (T)/(S)/(P) by the subsingleton condition then
  by `provably_nonzero`. Run it over `good/` and `bad/` **separately** — mixing
  them is what produced the phantom class-(P) rows above.

---

## 4. Where the prose is still wrong

Corrected in place by me, with the reason in each commit message — `592f4f6`
(`QUOT-MODEL`), `21a93bf` (`LEVEL-POLYMORPHIC-INDUCTIVES` §3.5), `15c40bc`,
`820bd07`, `b89d621` (`INDEXED-DESIGN` §2.2, §5.3, §6.2, §6.4, §9, D7).

**Closed — and one of them was stale in a second way nobody had named:**

* **`derived/src/inductive/motive.rs`'s `cod_at_funspace` — fixed, and the
  diagnosis recorded here was half of it.** It returned `None` at every input,
  and this entry (and `mini/src/rec_dep.rs`'s header, and that file's
  `cod_at_funspace_is_dead_…` test) all say the cause is *one* re-association:
  `k = h ∧ (mx ∧ my)` where the two `gen_under`s want `(h ∧ mx) ∧ my`. True,
  and not sufficient — the union injection was also lifted under `k` with
  `a1i` before being handed to `syl`, which wants it bare. **Either defect
  alone makes the `?` fire**, so anyone who applied the recorded fix would have
  measured it still dead and had no reason to look further; that is the cost of
  a diagnosis stated as complete when only the first `?` was traced. Both are
  repaired, the consumer that arrived first was **not** §11's level sharing but
  `deprec.rs`'s non-vacuity witness, and `derived/tests/deprec.rs` now has the
  test the module never had.

  **The mini side is corrected, and correcting it found the omission underneath
  the omission.** All four records read "dead" and "not used" as one sentence,
  so none of them said why [`cod_at_rung`] would still exist the day it was
  repaired — and it does, for reasons in the *statement*
  `⊢ ∀C ∀V. (C ∈ fs(W,V) → COD(C, ⋃V ∪ {∅}))` rather than in its health. Its
  hypothesis is a **function-space** membership and the motive is
  `⟦C⟧ ∈ dprod(⟦Sort u₁⟧, W)` at a constant fibre — §10 took the `fs` clause
  out of `⟦Π⟧`, so reaching it costs `ext::dprod_const_fibre_n` — *(which this
  bullet, and four sections of `MINI-HANDOFF.md`, called "stored and unread".
  It never was: `mini/src/quot_classes.rs`'s `lift_at` has called it since
  `9edf304`. It is now `Interp::dprod_is_fs`, one method with three consumers,
  so the crossing is a **method call** and this bullet's remaining force is its
  second half alone. `MINI-HANDOFF.md` §33 item 3 is the finding: a "nothing
  reads this" claim is a `grep`, not a static read, and it inherits none of a
  static read's record.)* — and its
  target is `⋃V ∪ {∅}` where this route instantiates `DepRecursor::target` at
  `⟦Sort u₁⟧`. `rec_dep.rs`'s test now asserts those two statements (and that
  it is `Some`) instead of `is_none()`: a tombstone goes stale silently in one
  direction and loudly in the other, and in neither direction does it carry the
  reason. `mini/src/rec_dep.rs`'s and `mini/src/recursor.rs`'s headers and
  `MINI-HANDOFF.md` §4's shaky-list entry are corrected in place with it.
* **`mini/src/recursor.rs`**'s header used to route the class-(S) obligation
  through `rec_typed`'s `fs(1,T)` and worry about retargeting to `fs(A_φ,T)`.
  That is not the path: the nest opens `∀t`, so there is no function to build
  and the scope atom supplies what the retarget was for. **Checked rather than
  left open: it was corrected.** The header now states the class-(S) carrier as
  `A_φ(p⃗) ⊆ 1` with no funspace anywhere in it, and the one surviving mention
  of `rec_typed` is `empty_rec`'s, which names that shape only to say it is
  *not* built — "`• ∈ app(⟦C⟧,t)` avoids inventing an `f` and a funspace
  membership to carry it", which is this bullet's own conclusion arrived at
  independently.

**Known still stale:**
* **`INDEXED-DESIGN` §5.1** still reads as *the* indexed recursor
  (`⟦T.rec⟧ := app(grec(…), t)`). It covers the value motive only. §5.3 now
  says so, but §5.1 does not say it about itself.
* **`derived/src/inductive/family/dep_rec.rs` §"What is not here"** ends with
  "`077` was predicted to reach it and does not: it stops one step earlier, at
  binder-congruence in the λ clause's own typing (measured)." **That was true
  when written and is now false** — the binder-congruence bridge, the carrier
  and the recursor typing have all landed since, and `077` reports
  `iota(RBTree.rec)` with 14 gapped conversions and 18 ι mints (measured,
  `b82368d`). The paragraph's *substance* — that the indexed ι at a value motive
  is neither built nor tested — is unaffected and is §8's construction 3. Only
  the last sentence needs correcting, and it is a `derived/` header, so it is
  Isla's. It is also a clean instance of §2's corollary: the measurement that
  produced it was taken behind three blockers that have since gone.

* **`derived/src/quot/graph.rs`'s `graph_pair` and `pair_in_graph` are
  attributed backwards in their own field docs** — they read "the direction the
  eliminator needs" and "the direction the constructor needs" (Bram). The rule
  they got wrong is worth more than the swap: **a bridge is chosen by which side
  of the implication the consumer stands on, not by which of the two directions
  it is.** `Acc.intro` wants `graph_pair` because the pair membership is an
  *antecedent* there; `step_closed` stands in the same position, so the
  *eliminator* wants `graph_pair` too. **`pair_in_graph` has no consumer of the
  *theorem*** — it is built at `acc.rs:164`, stored as a field at `:145` and
  pinned unconditional at `:351`, so the **import is live** and only the theorem
  is unspent. (I recorded it here as an "unused `use` line"; that was wrong, and
  the two readings imply opposite actions — an unused import gets deleted, a
  stored-but-unspent theorem gets a consumer. `mini/src/quot_classes.rs:82` had
  it right all along: *"the bridge with no consumer yet"*.) `Quot.sound` at
  `u ≥ 1` is predicted to be its first real consumer, and that prediction is a
  reading of `q_sound`'s statement, **not a build**.

**Never audited by me** — assume nothing about their currency:
`MEASUREMENTS.md`, `THREADING-CENSUS.md`, `LIBRARY-BACKLOG.md`, `LOCALS.md`,
`PERF-REVIEW.md`, `DERIVED-AUDIT*.md`.

---

## 5. Binder congruence — scoped (Vera)

937 of 988 gapped conversions at `e88bd6f`, all in one row,
`binder-congruence(clauses differ: dprod vs fs)`, `Cause::Threading`. Scoped and
measured. **`derived/` owes nothing; the theorem exists and has no consumer in
`mini/`.**

### What it is

`⟦Π x:A. B⟧` takes mini's `fs` clause when `B` does not mention the binder and
its `dprod` clause when it does — `dep = has_bvar(body, 0)`, `kernel.rs:1079`
for `Π` and `:1485` for `λ`. That predicate is **syntactic and β-unstable**:
`(fun _ => T) x` mentions the binder and `T` does not, and the two are
definitionally equal. So a conversion between two spellings of one type reaches
`BinderShapes::apply` with `Dep` on one side and `Fs` on the other, and the
`_ => None` arm has no rule for the pair.

Every occurrence in the corpus is the same source: a **recursor at a constant
motive whose body is a non-dependent `Π`**. `N.rec.{1} (fun _:N => ∀_:N, N) …`
gives the value the inferred type `∀ t:N, motive t` — dependent — while the
declared type `∀_:N, ∀_:N, N` is not. Three definitions (`N.add`,
`myListApped`, `RBTree.id`) and the three `_spec` theorems about them.

**Both classifications are right.** Neither side is wrong about its own
spelling, and they cannot be made to agree without whnf-ing the codomain before
classifying — which would make `⟦·⟧` a function of a normal form rather than of
a term. The two are genuinely two spellings of one set.

### What settles it, and where it already exists

`derived::ext::dprod_const_fibre_n` (`derived/src/ext/const_fibre_n.rs:87`,
exported at `ext.rs:78`):

```text
⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A → b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))
```

Its hypothesis is *exactly* `binder_cong`'s discharged `family`, because the
`fs` side's `sym_at` is `eq_refl(cod)` and the pointwise chain therefore
concludes `b(q⃗,x) = ⟦B⟧`. Its conclusion is exactly what the arm must return,
modulo one `fs_cong` against the domain conversion. Everything it needs —
`FibreSite::dp`'s `b/img/img_ax/dprod/dprod_def`, and the prelude's
`fs_app_mem`/`fs_retarget` — is already in `Interp`.

`checker/src/tg.rs::derive_pi_bridge` (`:13142`) is the same repair, done. Read
it before writing mini's; it handles both orientations with a `flip`.

**`mini/src/interp.rs:994` is the doc that hid this.** `Interp::fs`'s header
says `dprod_const_fibre_n` "is not needed to say so — the interpretation simply
*is* `fs`". True of *building* an interpretation, false of *relating* two, and
that is the whole row. It should be corrected when the arm lands.

### Measured, not predicted

**Landed** (Wren), `mini/src/interp.rs::dprod_fs_bridge` + `BinderShapes::apply`'s
two mismatch arms. Every number below reproduced exactly, and
`mini/tests/tutorial.rs` now pins them. Two things this scoping got wrong, both
small: the mirror is handled *inside* `apply` rather than before the scope opens
(normalising earlier would reorder the acceptance recursion, which must not
depend on the certificate), and discharging the row exposes one further
conversion row, `no-endpoint`, at 1.

A throwaway prototype of the arm in a detached worktree (never committed),
over `good/tutorial`:

| | at `e88bd6f` | with the bridge |
|---|---:|---:|
| gapped conversions | 988 | **81** |
| `binder-congruence` rows | 937 convs / 6 pairs | **0 / 0** |
| certified pairs (`constEv`) | 152 | **155** |
| `unsealed` | 0 | 0 |

`BinderShapes::apply` outcomes, which is the honest denominator — the 937 counts
conversions *tainted*, not sites that failed:

| arm | at `e88bd6f` | with the bridge |
|---|---:|---:|
| `fs_cong` | 507 ✓ | 879 ✓ |
| `dprod_ext_n` | 66 ✓ | 799 ✓ |
| `cond_ext_n` | 75 ✓ | 75 ✓ |
| `lam_ext_n` | 6 ✓ | 6 ✓ |
| `Mismatch(dprod,fs)` | **306 ✗** | 1299 ✓ |
| `Mismatch(fs,dprod)` | 0 | 6 ✓ |

The mirror needs no new library theorem either: `derived::eq_symm_imp` + `syl` +
`Thm::gen` turn the family round under its own `∀`, and `derived::congr` on the
`dprod` symbol moves the domain. It is only awkward because `apply` receives the
family already discharged and does not receive the `Closed`; normalising the
orientation before the scope is opened, as `tg.rs` does, is the tidier route.

### The three zero rows were "solved", not "unreached"

Read twice, as §2 says. `dprod_ext_n`, `cond_ext_n`, `lam_ext_n` and `fs_cong`
all fire and all succeed — 654 times between them at `e88bd6f`. The row was
never "the extensionality lemmas are unthreaded"; they are threaded and they
work.

### What it was masking

The successor rows do not exist until the bridge lands, and three of them are
new:

* `iota(N.rec)` — 8 convs, `nRecReduction`
* `iota(List.rec)` — 7 convs, `listRecReduction`
* `iota(RBTree.rec)` — 14 convs, `RBTree.id_spec`
* `Mismatch(fs,dprod)` — the row's own mirror, 6 sites

So the six pairs are **three definitions that the bridge certifies outright**
and **three theorems that move to ι**. `iota(·.rec)` is the next row, and it is
now six declarations (`Bool`, `Prod`, `Eq`, `N`, `List`, `RBTree`) rather than
three.

---

## 6. Class (S) at an index — scoped (Vera)

`071_sortElimPropRec` / `indexed-family(SortElimProp: class (S) carrier at an
index)`, `Cause::Scope`, **2 pairs** (`u := 0`, `u := 1`). The **first blocker in
file order** at `1498aff`, once class (P) closed `069`/`070`.

**It is not "the last non-ι row".** Measured over all 91 exports of
`good/tutorial` at `08c91ea`: 60 waiting pairs over **22 distinct keys** in
**7 reason families** — 26 `Scope`, 28 `Library`, 6 `Threading`, `constEv` 158
of 218. What is true is the narrower statement: `iota(·.rec)` is the only
remaining `Cause::Threading` shape, at six declarations. This row is `Scope`,
and `proj(·)` alone is **24 `Library` pairs over five declarations** (`And`,
`Prod`, `PProd`, `PSigma`, `PropStructure`) **and eight exports** (`078`–`081`,
`084`, `086`, `093`, `105`). Two true sentences, and conflating them oversized
one row and hid another.

Keys and families are both worth carrying, because they differ by 3× and the
work does not track either alone: `proj` is one family, five keys and one
construction; `iota` is one family, six keys and six ι rules; `no-interp(Quot*)`
is four keys of one clause. **Count keys for the ledger and families for the
worklist, and say which you mean.**

**A fifth axis, which `proj` forced and which is the first to cut *inside* a
declaration:** *pairs owing a **term*** versus *pairs owing a **certificate***.
`SCOPING` §9 and `MINI-HANDOFF` §11 disagreed about row 1b at 8 against 4, and
both were right — 8 pairs on those two keys, of which 4 owe a certificate and 4
owe a term, split by σ within one declaration. Every earlier axis (keys,
families, exports, pairs) partitions declarations or files; this one does not,
so a row can be two sizes at once without either being wrong. The full rule:

> **keys for the ledger, families for the worklist, exports for the schedule,
> constructions for the estimate, and term-versus-certificate for who builds
> it — and name which.**

### The obligation, and the declaration

`--block` says **`⟦ty[σ]⟧`** — the type's interpretation. Not the value, not the
constant's typing. `sortElimPropRec`'s type mentions `SortElimProp b b1 b2`, the
store hands back the declaration's decline, and the recursor is never reached.

```text
SortElimProp        : ∀ (b : Bool), Bool → Bool → Prop      np = 1, ni = 2
SortElimProp.mk     : ∀ (b b1 b2 : Bool), SortElimProp b b2 b1
SortElimProp.rec.{u}                          one extra lparam ⟹ class (S)
sortElimPropRec.{u} := SortElimProp.rec.{u}   bare constant, no η-expansion
```

Two facts to read off it. The constructor's fields appear in the result index
**swapped**, which is `thesis.txt:1856–1858`'s delayed elimination in its
non-trivial form — it bites the recursor and not the carrier. And `recs = 0`, so
`R = ∅`, `LeCarrier::degenerate` applies and `acc(A_φ,R) = A_φ`.

The gap is `IndexedFamily` and **not** `IndSpec`, and `zoneb` walks before it
declines (`zoneb.rs:470–504`) — so the spec is *measurably* well formed.
`SortElimProp` is representable as an `IndexedDeclSpec`; nothing about this row
is a representability question.

### Three pieces, two owners

1. **The carrier** — missing. Below.
2. **The constructor** — `⊢ ∀p⃗∀y⃗ᵢ. ((Hᵢ ∧ Eᵢ) → • ∈ χ(p⃗, e⃗ᵢ))`, which is
   `LeCarrier::intro[i]` composed with `degenerate` and `cond_intro`. Three
   lines over theorems that all exist.
3. **The recursor** — `rec_prop.rs:165` declines `ni ≠ 0`.
   `derived::…::le_rec` is the right module (its own `family.rs:70–75` says
   `le_prop_rec` is the `ni = 0` one and does not generalise) and it exists, but
   its `minor_eq` is a **hypothesis** and discharging it *is* the delayed
   elimination. That is `mini`'s by the boundary rule, and the raw material is
   already in hand — but it is the *second* of two index families and only one
   of them carries the permutation:

   ```text
   IndexAx::indices        ⊢ ∀p⃗ ∀x⃗<ₖ. (ιₖ(p⃗,x⃗<ₖ) = ⟦Iₖ⟧)        the index TYPE
   CtorIndexAx::result     ⊢ ∀p⃗ ∀y⃗ᵢ.  (eᵢₖ(p⃗,y⃗ᵢ) = ⟦e⃗ᵢₖ⟧)  the result EXPRESSION
   ```

   On `SortElimProp` the first says `⟨·⟩ = ⟦Bool⟧` at both slots and records
   nothing about the constructor; the second says `⟨·⟩ = x2` and `⟨·⟩ = x1`,
   which *is* the field↔index-slot correspondence. `zoneb.rs`'s own code
   comment marks the split — the index types are read by `interpret_and_open` on
   the declaration's binders, the result expressions by `ind_spine` on the
   constructor's codomain "over the parameters and **all** the plain fields".
   `IndexedDeclSpec` records a symbol per slot and not which field's expression
   it abbreviates, so this exists in no other form anywhere.

   And `mini` computed it **on the very line that discarded it**. The old
   `let (_, base, ix) = spec_of(…)?` dropped the whole `IndexAx` *and* the
   entire `Shape` behind the `_` — every `CtorEvidence`, including
   `field_sort`, whose own header names the class-(S) recursor as the consumer
   that would otherwise recompute it at a second set of variables. So the
   recursor's `Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1` was being thrown away on the same line as
   its `minor_eq` material. Otto's MINI-HANDOFF §2 pattern, at a **decline**
   rather than at a return — which is the new part, because a decline reads as
   a place where nothing was produced. Retained as
   `IndApparatus::indexed_walks` (`08c91ea`), corpus byte-identical across all
   91 exports.

### Nils's finding: verified, with one correction that changes route (a)

Holds, checked independently:

* `LeCarrier` stops at `acc_set: Term` (`le.rs:303`, `ac.of(a_phi, r)`). No
  conditional singleton, no `FnSym`, no `∈ U₀`.
* `[tup(x⃗) ∈ acc(A_φ,R)]` exists **only as prose** — `mini/src/zoneb.rs:107` and
  `:498`, `mini/src/direct.rs:23`, `mini/src/class_s.rs:25`,
  `derived/…/le_rec.rs:468`, `INDEXED-DESIGN.md:575`.
* `LeProp::build` refuses `ni ≠ 0` (`le_prop.rs:150–151`).

**The correction: there is no guard to lift.** `LeProp` mints *nothing*. Its
whole content is that at `ni = 0` the *already-existing* `A_φ` **is** a
conditional singleton, because `Idx(p⃗) = 1` — its own header says so
(`le_prop.rs:61`, "The symbol `A_φ` is **not** re-introduced"). Every step after
`le_prop.rs:185` spends `IndexSpace::point()`, which returns `None` at `ni ≥ 1`
**by construction** (`index.rs:145–147`, `telescope.betas.is_empty().then_some`),
so deleting the explicit guard would leave `LeProp::build` returning `None`
anyway — and any version that did not would be *false*, because at `ni ≥ 1`
`A_φ` is a subset of a genuine Σ-nest and is not the carrier. Route (a) is **a
new module beside `le_prop`**, not a relaxed guard, and it must mint a symbol of
arity `np + ni`.

### The routing verdict: (a), `derived/`

**The canonicality argument does not discriminate and should not be used.**
`class_s::build` has exactly **one** call site (`zoneb.rs:511`), reached only
through `zoneb::ensure`'s per-`(name,σ)` guard (`stored_term(…).is_none()` plus
`app.declined`), and its result is cached in `app.props`, which `class_s::of`
reads. A symbol minted there is minted once per `(declaration, σ)` — the same
discipline `LeCarrier`'s own `A_φ` already has. `gen_ctor_nest`'s hazard is about
a **use site**; this is not one, and route (b) would not fire it. Three other
things decide it:

1. **The boundary rule, applied literally.** The construction is a function of
   `(spec, ix, lc, params)` and touches no `Expr`, no `Name`, no binder order. It
   is `thesis.txt:1886`'s carrier verbatim. It models type theory.
2. **The sibling is already there, with the signature to copy.**
   `TruncCarrier::over_family` is the class-(P) carrier — a conditional singleton
   over an indexed base — and it lives in `derived`, takes a `&Tower`, and
   exports `xvs`, `carrier`, `ty_ax`, `subset_unit`, `only_point`, `irrel`,
   `elim` and `in_u0 : ⊢ ∀p⃗∀x⃗. ‖a‖ ∈ U₀`, the last built with `tow.cond_in_u0`
   and `gen_all` at `trunc.rs:426–430`. Route (b) would have `mini` do for class
   (S) precisely what `derived` already does for class (P), in the same
   directory, for the same kind of object. One level down the same split holds:
   `derived::prop::apparatus` mints `eq_set` and `and_set` — both conditional
   singletons of positive arity — and `mini/src/direct.rs:275` only calls
   `cond_in_u0` at them. **`derived` mints the symbol and exports the
   characteristic theorem; `mini` calls `cond_in_u0` where it needs the typing**
   is the established seam, and it is not the seam either route as posed puts it
   at.
3. **Testability, and this one is not aesthetic.** `derived/tests/family_le.rs`
   already exercises `LeCarrier` at `ni = 2` on a `071`-shaped fixture
   (`spec_071`, `indices = vec![i0, i1]`) in **both** polarities —
   `the_non_recursive_subsingleton_collapses_to_its_domain` and
   `a_recursive_subsingleton_gets_no_collapse` — and both pass. A module beside
   it inherits that fixture and can be pinned at a *recursive* spec. The corpus
   cannot: `le.rs`'s census finds **no recursive class-(S) declaration anywhere
   in this repository**, tutorials or prelude, so anything minted in `mini/` is
   testable at one degenerate witness and nothing else. §2's corollary again —
   the corpus bounds demand *and* population from below.

### What `derived/` owed — and this is the first time it was not "nothing"

**Landed at `90d9bf3` as `derived/src/inductive/family/le_index.rs`**
(`LeIndexCarrier`, `LeIndexCtor`), consumed by `mini/src/class_s_ix.rs` and
`rec_s_ix.rs`, pinned by `derived/tests/family_le_index.rs`. The specification
below is what it was built against and is left standing because it is still the
interface; everything in it is exported under the name in brackets, plus `at`,
`chi_at` and `cond_at` for reaching a consumer's own index terms. **It was
missing from `INDEXED-DESIGN.md` §8's D5 line for two rounds afterwards and a
later seat was scoped onto it as unbuilt** — the same failure D6 records, and
the reason both entries now name their files.

It is a module beside `le_prop`, guarded at `ni ≥ 1` as `le_prop` is at
`ni = 0`, with `LeProp::build`'s signature plus a `&Tower`. Write `p⃗` for the
parameter variables, `x⃗` for `ni` fresh index variables, `X := tup(x⃗)`, and
`acc := acc(A_φ(p⃗), R(p⃗))`:

```text
⊢ ∀p⃗ ∀x⃗ ∀z. (z ∈ χ(p⃗,x⃗) ↔ (z ∈ 1 ∧ X ∈ acc))                        [chi]
⊢ ∀p⃗ ∀x⃗. χ(p⃗,x⃗) ∈ U₀                                               [in_u0]
⊢ ∀p⃗ ∀x⃗. (X ∈ acc → • ∈ χ(p⃗,x⃗))                                    [intro]
⊢ ∀p⃗ ∀x⃗. (• ∈ χ(p⃗,x⃗) → X ∈ acc)                                     [elim]
⊢ ∀p⃗ ∀x⃗ ∀z. (z ∈ χ(p⃗,x⃗) → z = •)                              [only_point]
⊢ ∀p⃗ ∀x⃗ ∀u ∀v. ((u ∈ χ(p⃗,x⃗) ∧ v ∈ χ(p⃗,x⃗)) → u = v)                [irrel]
⊢ ∀p⃗ ∀y⃗ᵢ. ((Hᵢ ∧ Eᵢ) → • ∈ χ(p⃗, e⃗ᵢ(p⃗,y⃗ᵢ)))            [ctor_intro], per i
```

`chi` is one `prop::conditional_singleton(env, sums, p⃗ ++ x⃗, φ)` at
`φ := X ∈ acc`; `in_u0` is `Tower::cond_in_u0` then `gen_all`, and it is
**unconditional** — `χ ⊆ 1` whatever `acc` is, so no `H`, no size argument, no
parameter typings, exactly as `LeProp`'s and `TruncCarrier`'s are. `intro`,
`elim`, `irrel` are `cond_intro` / `cond_elim` / `cond_subsingleton` at that
`chi`. `ctor_intro` is `LeCarrier::intro[i]` composed with
`LeCarrier::degenerate` and `intro`.

Two things the module must say rather than quietly assume, and both are in its
header:

* **`ctor_intro` is stated at the degenerate case only.** With a recursive
  constructor `degenerate` is `None` and the premise `Acc::acc_intro` (A1) wants
  is `∀y. (y ∈ A_φ → (⟨y,X⟩ ∈ R → y ∈ acc))` — a *universally quantified*
  accessibility, where a Lean constructor supplies `mᵢ` specific accessible
  children and an inversion of `rel_ax` to say they are the only predecessors.
  That is `le_rec`-shaped work with no witness anywhere; decline it with the
  census, as `le.rs` already does.
* **The `acc^ϕ_r` collapse is `le.rs`'s argument, not the thesis's.** Carneiro
  builds `acc^ϕ_r x := ∃h : ϕ x. acc_{r'}(x,h)` over a subtype (`:1832–1845`);
  `derived` builds `acc(A_φ, R)` with `R` unrestricted, justified by
  `le.rs`'s header on the two `crate::acc` corrections. The new module rests on
  that argument too and must not re-derive it.

**One thing the specification did not think to say, found by mutation.**
`ctor_rule` reads the constructor position `i` in three places — the field
count, `LeCarrier::intro[i]` and the result vector — and every fixture the
module landed with had exactly **one** constructor, as does the tutorials'
only class-(S)-at-an-index declaration. Replacing `i` by `0` throughout passed
all six tests. `derived` is general in the constructor count (φ is a
disjunction over constructors, and `family_le_prop.rs` already carried a
three-constructor fixture at `ni = 0`), so this was a coverage gap and not a
library one; `spec_three_ctors` closes it at `ni ≥ 1` with three constructors
at 0, 1 and 2 fields and three distinct result vectors. **Three and not two,
and here the reason is not the usual one:** `i ↦ 0` and `i ↦ n−1−i` are both
caught at two, because every non-identity permutation of two moves both — what
two cannot see is a **clamp**, `i ↦ min(i,1)` being the identity on `{0,1}`.
The general form is worth carrying: *the third element is needed whenever a
mis-index can fix some positions and move others, which a permutation of two
never does.*

### Where the thesis speaks

* **`:1886`** — `⟦µt : ∀x::α. U_ℓ. (c:β)⟧ = λx::α. ulift_ℓ (acc^ϕ_r (x))`. The
  carrier is **stated**. This is not a §5.4 silence.
* **`:1859`**, **`:1832–1845`** — `P x ≃ acc^ϕ_r (x)`, and `acc^ϕ_r`'s definition
  with the note that large elimination for it is derivable.
* **`:2057`** and **`:2162`** — `[p] = {x ∈ {•} | p}`, and `[x ∈ acc(A,R)]`
  written outright inside `rec_acc`'s own definition. The set five headers here
  describe in prose is in the thesis in symbols.
* **`:2106`, `:2284`** — `ulift` evaporates at the set level and its soundness
  clause is `ᾱ ∈ Uₙ ⊆ Uₙ′`, i.e. the cumulativity raise `class_s::former`
  already performs (`raise_in_gamma(0, level, …)`). `ulift_ℓ` in `:1886` needs
  nothing new and the correspondence carries to `ni ≥ 1` unchanged.
* **`:1893–1901`** — §5.4 leaves the introduction rules, the recursor and ι as
  future work. Piece 3 above sits there, and `le_rec`'s header already says
  everything in it is invention.

---

## 7. Class (P) at an index — scoped (Vera)

`072_sortElimProp2Rec` / `indexed-family(SortElimProp2: class (P) truncation
over an indexed base)`, `Cause::Scope`, **1 pair**, σ = `—`. Obligation
`⟦ty[σ]⟧`; the type mentions `SortElimProp2 b b1 b2`, the store hands back the
decline, the recursor is never reached. Neither the declaration nor its alias
has a level parameter, so for the first time in this series the σ axis is
trivial rather than argued.

**It is not the last `Scope` row.** Measured at `fd42fb9` over all 91 exports:
58 waiting pairs over 21 keys in 7 families — 24 `Scope`, 28 `Library`, 6
`Threading`, `constEv` 160 of 218. `072` is **1 of 8 `Scope` keys and 1 of 24
`Scope` pairs**; the rest are `no-interp(Quot*)` (4 keys, 14 pairs),
`fun-typed-rec-arg(RTree)` (4), `fun-typed-rec-arg(Acc)` (3), `no-interp(Nat)`
(2). The better sentence, and it is a real milestone: **`072` is the last
`indexed-family(·)` row** — the fourth and last of the four problems §2's table
says that one label covered, after the class-(T) `Prop` motive, the class-(T)
value motive and the class-(S) carrier.

### The declaration, and the thing nobody has recorded about it

```text
SortElimProp2      : ∀ (b : Bool), Bool → Bool → Prop      np = 1, ni = 2
SortElimProp2.mk   : ∀ (b b1 b2 : Bool), SortElimProp2 b b2 (id.{1} Bool b1)
SortElimProp2.rec                     no extra lparam ⟹ class (P)
sortElimProp2Rec  := SortElimProp2.rec    bare constant, no η-expansion
```

`elim_audit` agrees the trichotomy is right: `computed=false oracle=false`.
`recs = 0`, one constructor, `kᵢ = 2`, and the result indices are the fields
**permuted**, as in `071`.

**The second result index is a δ-redex, and that is the point of the fixture.**
`id.{1} Bool b1` is what makes the index non-invertible and hence the eliminator
small. It also puts an obligation on this pair that `069`–`071` did not have:
`sortElimProp2Rec`'s *declared* minor is `motive b2 b1 (mk b b1 b2)` while
`SortElimProp2.rec`'s own minor is `motive b2 (id.{1} Bool b1) (mk b b1 b2)`.
The two types are definitionally equal only through δ+β on `id`, and the pair's
last obligation is a conversion between them. Nobody has written that down; it
is not the carrier, and it will not appear until the carrier lands.

### Four pieces

1. **The carrier** — `TruncCarrier::over_family`, and it is ready (below).
2. **The constructor** — does **not** fall out of `07bee9e`'s non-indexed path.
3. **The recursor** — `derived/` owes it, and this is the second time running.
4. **The `id`-redex conversion** above.

### The three inherited claims, checked

**(a) Tara's carrier claim holds — and this time the fixture is real.** Applying
§1's new rule to `derived/tests/family_trunc.rs`: `sort_elim_prop2` builds
`DeclSpec::new(1, [CtorSpec::new([b0,b1], 0)])` with `indices = [i0, i1]` of
arities 1 and 2 and `CtorIndices::nonrecursive([e0, e1])` at arity 3, where
`e0 = a[2]` and `e1 = a[1]` — **`np = 1`, `ni = 2`, `kᵢ = 2`, result indices
permuted**. That is `072`'s shape including the corner, not `spec_071`'s
`np = 0, kᵢ = 0`. `over_family` has three positive call sites and three negative
ones against it. The claim survives a refactor and the caution.

One difference between the fixture and what `mini` will hand over, and it is
benign: the fixture models `⟦id Bool b1⟧` as the bare `y₀`, while `spec_of`'s
`index_syms` does `infer_type` with **no whnf**, so `mini`'s `e1` abbreviates
`app(app(⟦id.{1}⟧,⟦Bool⟧), y₀)`. The carrier cannot see the difference —
`IndexedDeclSpec` holds `FnSym`s and every construction over it treats them
opaquely — which is exactly why the difference lands on piece 4 instead.

**(b) Petra's flag holds verbatim, and `072` witnesses half of it.**
`trunc_rec.rs`'s "Scope: non-indexed only" states the owed `φ` word for word,
including the `IndexedCtor::inv` forcing. But its second clause — "the recursive
minors stop being trivial" — is **not** witnessed by `072`, which has `recs = 0`.
`072` witnesses the non-constant `φ` and the index forcing; `Nat.le`,
`Nat.le.below` and `List.Mem` (prelude and `grind-ring-5`, not the tutorials)
are what would witness the recursive half. Size the guard as half-covered.

**(c) Task #41's constructor path does not extend.** `trunc_ctor_bottom` splits
the nest's binders at `np` and applies the type former to the parameters alone
(`beta_spine(&former, &ps, param_mems)`, and `inst_all(&site.ax, &ps)`). At
`ni ≥ 1` the codomain is `T p⃗ e⃗ᵢ` and the spine is `np + ni` deep, with the
index arguments being *expressions in the fields* rather than binders of the
nest. That is precisely what `crate::ctor_ix` does for class (T) and it is a
module, not a parameter. Read from the code, not predicted.

### What `derived/` owes

The indexed class-(P) recursor. Writing `‖a‖` for
[`TruncCarrier::over_family`]'s carrier and `app(m, x⃗, •)` for `prop_rec`'s
curried `motive_app`:

```text
MINORᵢ(m) := ∀y⃗. ( ⋀ⱼ yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)                    the kᵢ plain fields
                   ∧ (• ∈ ‖ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))‖) × mᵢ      the recursive arguments
                   ∧ (• ∈ app(m, d⃗ᵢⱼ(p⃗,y⃗), •)) × mᵢ     the induction hypotheses
                 → • ∈ app(m, e⃗ᵢ(p⃗,y⃗), •) )

⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) → ∀x⃗ ∀t. ( t ∈ ‖ind(p⃗,x⃗)‖ → • ∈ app(m, x⃗, t) ) )
```

**It sits strictly between the two files that already exist, and takes one half
from each.** The three `φ`s, side by side:

| module | `φ(z)` | `z` in `goodrec` | `z` in the motive |
|---|---|---|---|
| `trunc_rec` — class (P), `ni = 0` | `• ∈ app(m,•)` | — | no |
| **owed** — class (P), `ni ≥ 1` | `∀x⃗. (tup(x⃗) ∈ app(goodrec(p⃗),z) → • ∈ app(m,x⃗,•))` | **yes** | **no** |
| `prop_rec` — class (T) at a `Prop` motive, `ni ≥ 1` | `∀x⃗. (tup(x⃗) ∈ app(goodrec(p⃗),z) → • ∈ app(m,x⃗,z))` | yes | yes |

So it needs **`prop_rec`'s inversion machinery** — `IndexedCtor::inv`,
`Apply::pair_inj` componentwise, `IndexedCarrier::good_of` firing the induction
hypothesis at the child's own indices, one `eq_leibniz` per index moving the
conclusion from `e⃗ᵢ` to `x⃗` — because of the `goodrec` antecedent; and it keeps
**`trunc_rec`'s truncated minors and its two ends**, `TruncCarrier::only_point`
and `TruncCarrier::elim`, because the motive never sees `z`. Neither file's
simplification applies whole: `trunc_rec`'s "recursive minors provable by one
projection" fails (the IH at `x⃗ := d⃗ᵢⱼ` carries content), and `prop_rec`'s
`z`-transport through the motive is not needed. `prop_rec.rs`'s own header
states the contrast in the other direction and is the thing to read first.

The consumer-side boundary move is already built and should not be rebuilt:
`mini`'s `ctor_ix::index_congr` at the `mem`-shaped positions, and
`prop_rec`'s exported `motive_congr` / `motive_congr_of` down the `app` spine.

**Nothing else is owed.** `TruncCarrier::over_family` exists and is tested at
this shape; `Inductive::build`, `IndexedInductive::build` and the `wrec`
apparatus are the same objects `build_indexed` already runs for `RBTree`; and
`TruncCarrier::in_u0` needs no size argument, so class (P) skips
`decl_universe`, `IndexedUniverse` and the cumulativity chain entirely. The
`Legs::Skip` walk `zoneb` already performs before declining is the walk the
build wants, and it is retained in `IndApparatus::indexed_walks`, so the
`mini` side starts from a stored `IndexedWalk` exactly as `class_s_ix` does.

### Where the thesis speaks

* **`:1811–1819`** — the class-(P) clause, **stated for the indexed case
  directly**: `⟦µt : ∀x::α. U_ℓ. K⟧ = λx::α. ulift_ℓ ‖⟦µt : ∀x::α. U_{ℓ'}. K⟧ x‖`,
  with the `λx::α` prefix and the `x` applied to the underlying carrier. Not a
  non-indexed clause being stretched.
* **`ℓ' = max(1, all the constructor arguments)`** — Carneiro *lifts the target
  universe above 1* before truncating. At the set level `ulift` evaporates
  (`:2106`, and `:2284`'s soundness clause is the cumulativity raise), so
  `derived` builds one W-type and not a second at `ℓ'`. Worth saying why that
  matters here rather than only that it is free: **the lift is exactly the step
  class (P) does not have to pay for**, because nothing ever places the base in
  a universe — only `‖a‖ ∈ U₀`, which needs no size argument. That is the
  content of `trunc.rs`'s "cheaper rather than more expensive".
* **`:1893–1901`** — §5.4 again leaves the introduction rules, the recursor and
  ι as future work, so the owed theorem above is invention on the same footing
  as `trunc_rec`'s and `prop_rec`'s. Both of those headers say so of themselves.

---

## 8. The ι row — scoped (Vera)

`073_boolRecEqns` / `iota(Bool.rec)`, `Cause::Threading`, **1 pair**, σ = `u := 1`,
obligation **the constant's typing**. `⟦val⟧ = •` (an `And.intro` of two
`Eq.refl`s), and the two ι steps it needs are minted at `kernel.rs:725`, twice —
once per `Bool` constructor.

### Name the quantifier

Measured at `b82368d` over all 91 exports — 57 waiting pairs, 20 keys, 6
families, 23 `Scope` / 28 `Library` / 6 `Threading`, `constEv` 161, `typeEv` 195.
The ι row is:

| unit | count |
|---|---:|
| families | **1** (`iota`) |
| keys = recursors = exports = pairs | **6** |
| gapped conversions | **58** |
| ι gaps minted, corpus-wide | **114** at **9** recursors over **9** exports — but see §3: **a mint is not a demand**, most of these are acceptance-only walks carrying no interpretation, and the ledger's six was the honest number |
| **constructions** | **4** |

Two of those rows say different things and both matter. **The ι row is not the
ι population**: `116` (`RTree.rec`, and `Bool.rec` again), `118` (`Acc.rec`) and
`124` (`Quot.lift`) all mint ι and all report an earlier gap
(`fun-typed-rec-arg`, `no-interp`), so their demand is masked. And **six keys is
four constructions**, which is the census below.

### The three mint sites, instrumented

`Gap::Iota` is minted at exactly three places, all in `whnf`'s recursor arm:

| site | outcome | mints | where |
|---|---|---:|---|
| `kernel.rs:704` | **K-rule** — the major has the right *type*, no constructor matched | **2** | `Eq.rec`, `094` only |
| `kernel.rs:725` | **constructor match** — the rule fires | **112** | everything else |
| `kernel.rs:740` | **stuck, but the major moved underneath** | **0** | never |

**Site 3 is not an ι rule.** Its own comment says so: the recursor is *stuck*
and what is owed is a **congruence over the major's change**, not a computation
rule. It wears the ι label and has never fired. Read the zero twice, as §2 says:
it cannot be "solved" — the branch mints unconditionally when its guard holds —
so it is **unreached**. A row of 58 conversions is not evidence about it either
way.

### Four constructions

**1. `Eq.rec` (`094`) is not a missing theorem — it is a missing §6.2 clause.**
Carneiro gives the equality recursor an *interpretation*, `⟦rec=_a e b h⟧γ =
⟦e⟧γ` (`thesis.txt:2124`), with the definitional reduction at `:796`. Under that
clause `⟦Eq.rec α a C x b h⟧` **is** `⟦x⟧` and whnf's ι step is
`Thm::eq_refl`. `direct.rs`'s `Clause` enum has exactly one variant and
`clause_for` matches only the type former `"Eq"`; the recursor has no clause.
The typing that makes the clause sound is `Props::eq_sound`
(`⊢ ∀a∀b. (• ∈ eq_set(a,b) → a = b)`) plus one Leibniz, both already stored.
This is also the only member where the K-rule fires, and the clause covers K for
free — it has no side condition, while Lean's ι computes only on `Eq.refl`.
**`derived/` owes nothing.**

**2. `Bool`, `Prod`, `N`, `List` — built, stored, and unread.**
`DepRecursor::iota[i]` is

```text
⊢ PRE → ∀y⃗ ∀t⃗. ( Hᵢ → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ app(drec,t⃗) )
```

held in `IndApparatus::deprecs` per `(declaration, σ)`. `--dump-only=Bool` on
`073` prints it: `ι 0`, `ι 1`, `gen ι 0`, `gen ι 1` at `Bool.rec σ = [1]`.
`mini/src/rec_dep.rs`, `recursor.rs` and `rec_ix_dep.rs` contain **no occurrence
of the string `iota`**. One theorem covers all four — `mᵢ = 0` at `Bool`/`Prod`
and the recursive half exercised by `N`/`List` — so this is one construction and
four declarations. **`derived/` owes nothing**; it is threading, and it is the
fourth instance of MINI-HANDOFF §2's discarded-evidence pattern, this time at a
`pub` field of a struct the store already holds.

The shape of the missing wiring, so it is not rediscovered: whnf's ι step sets
`cur_tm = None` — it **drops the interpretation** rather than transporting it.
What has to arrive there is `⟦rhs⟧` and the equation above, with `PRE` (which
`rec_dep` already discharges for the typing) and `Hᵢ` (the field typings, which
`whnf` obtains when it whnfs the major but does not keep).

**3. `RBTree` (`077`) is genuinely unbuilt, and `derived/` owes it.**
`IndexedDepRecursor` has **no `iota` field**, and `dep_rec.rs` §"What is not
here" says the indexed ι at a value motive "is neither built nor tested" and
that `GenRecursor::iota` plus `IndexedGuardedMinors::fires` "is *expected* to be
all of it — but that is a separate theorem with its own antecedent … the
expectation has not been checked against anything." The dump prints the absence
in place (`value-motive ι — not stored`).

**4. Site 3's congruence**, above — owed to nobody yet, because nothing reaches
it.

### What `derived/` owes

One theorem, per constructor, in `IndexedDepRecursor`'s own vocabulary
(`irec = grec(p⃗, gmin⃗, T)`, `PRE = ICOD(m,T) ∧ IDEP(m,S⃗)`):

```text
⊢ ∀p⃗ ∀m ∀S⃗ ∀T. ( PRE → ∀y⃗ ∀t⃗. ( Hᵢ → app(irec, ctorᵢ(y⃗,t⃗))
                                        = Sᵢ⟪y⃗,t⃗⟫ app(irec,t⃗) ) )
```

with `Hᵢ` the field typings — `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` at a `Slot::Plain`,
`tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` at a `Slot::Rec` — and `Sᵢ⟪y⃗,t⃗⟫` the minor applied in
**declared field order**, then the `mᵢ` recursive results. The index vector does
not appear: ι fires at a constructor, whose result index `e⃗ᵢ(p⃗,y⃗)` is
determined, which is `INDEXED-DESIGN` §5.1's "the erased ι with `ni` dead
binders" — state it as the theorem, and if the proof is one instantiation of
`GenRecursor::iota` then the *check* is the deliverable.

### The mask claim does not survive, and this row is where it bites

The interleaved-mask hole was sized as reachable only from a synthetic
`Plain, Rec, Plain, Rec` declaration. Decoding `077`:

```text
RBTree.red   : ∀ α, ∀ n:N, ∀ _:RBTree α b n, ∀ _:α, ∀ _:RBTree α b n, RBTree α r n
                        Plain      Rec           Plain     Rec
RBTree.black : ∀ α, ∀ c1 c2 : Color, ∀ n:N, ∀ _:RBTree.., ∀ _:α, ∀ _:RBTree.., …
                        Plain Plain      Plain      Rec       Plain    Rec
```

**Both are interleaved, and both are in `good/tutorial/077`.** The corpus's
interleaved witness is not synthetic; it exists, it is `RBTree`, and it is the
hardest member of this very row — construction 3 above states `Sᵢ⟪y⃗,t⃗⟫` in
declared field order and `RBTree.red` is exactly the shape that tells the two
orders apart. What was true is that nothing had *reached* the path: `077` stopped
at binder-congruence, then the carrier, then the recursor typing. It reaches ι
now. Do not size the ι wiring's mask handling as untested-because-unwitnessed.

### Where the thesis speaks

* **`:2124`** — `⟦rec=_a e b h⟧γ = ⟦e⟧γ`, and **`:796`** the reduction
  `rec=_a C x a h ≡ x`. Construction 1 is a clause Carneiro states and mini has
  not implemented, not a gap.
* **`:1893–1901`** — §5.4 leaves ι as future work for the *inductive*
  declarations, so constructions 2 and 3 are invention. That is the third row
  running to land on the same declared silence, and by now it should be read as
  the standing answer for anything recursor-shaped rather than re-checked.
* Nothing in §6.2 speaks to site 3: a congruence over a stuck head is a property
  of the *checker's* traversal, not of the interpretation.

---

## 9. `proj` — scoped (Vera)

`078_And.right` / `And.left` / `proj(And)`, `Cause::Library`, **2 pairs**,
σ = `—`, obligation **the constant's typing**, `⟦val[σ]⟧ = •` already in hand.

At `1e63e56`, when this was scoped, `proj` was **24 of the 52 remaining waiting
pairs** — measured, and it really was roughly half of everything left. The rest:
`Quot*` 14, `RTree` 4, `Acc` 3, `Nat` 2, `unit-like(PUnit)` 2, `fun-eta` 2,
`iota(RBTree.rec)` 1.

Rows 1 and 2 have since landed, and at `d81dc6d` the remaining `proj` population
is **20 pairs over 3 keys and 5 exports** — `proj(PProd)=4`, `proj(PSigma)=4`,
`proj(Prod)=12` (`079` 4, `093` 2, `105` 6). `078`, `084` and `086` have no
waiting row at all.

### Name the quantifier

| unit | at `1e63e56` | remaining at `d81dc6d` |
|---|---:|---:|
| families | 1 | 1 |
| keys = declarations | 5 | **3** |
| exports | 8 | **5** |
| pairs | 24 | **20** |
| — of those, owing a **certificate** | 8 | **4** |
| — owing a **term** | 16 | **16** |
| **constructions** | **4** | 2 left |

"One construction" was my estimate and it **does not survive contact** — and
neither did my first correction of it, which said three. The row splits by the
**carrier's** class, and the obligation splits with it — §2's third standing
question paying twice on one row:

| # | **carrier** class | declarations | σ | pairs | `⟦proj x⟧` | obligation | status |
|---|---|---|---|---:|---|---|---|
| 1 | **(S)** | `And` | — | 2 | `•` | a **certificate** | **done** |
| 1b | **(T)**, field a `Prop` *at this σ* | `PProd`, `PSigma` | `0,0` | **4** | `•` | a **certificate** | Isla |
| 2 | **(P)** | `PropStructure` | — | 2 | `•` | a **certificate** | **done** |
| 3 | **(T)**, field is data | `Prod`; **and `PProd`, `PSigma`** | `1,1` | **16** | **absent** | a **term** | route (b) |

Half the row owes a *term* and half owes only a *certificate*, and no design
note distinguished them.

**Row 1b was corrected twice and the two corrections are on different axes; both
are right.** `SCOPING` said 8 pairs and `MINI-HANDOFF` said 4. **8 is the count
by key** — `proj(PProd)=4` and `proj(PSigma)=4` are what the ledger shows. **4
is the count by obligation**, and it is the one that says who builds it:

```text
PProd.fst σ = 0,0   defeq  ⊢ ⟦PProd.fst.{0,0}⟧ = •          owes a certificate
PProd.fst σ = 1,1   defeq  (…was expected and is missing)    owes a TERM
```

— measured on all four, `PProd` and `PSigma` alike. At `u = v = 0` the projected
field is a `Prop` and the projection is a proof; at `1,1` it is data. So four of
row 1b's eight pairs belong with `Prod` in row 3, which is **16**, and row 1b is
**4**. Say it as *"8 by key and 4 by obligation"*; picking either number alone is
what the disagreement was made of.

**And the first correction — my own grouping — is worth keeping too.** I put
`PProd.{0,0}` and `PSigma.{0,0}` with `And` as class (S) at 10 pairs, on the
ground that all three project to `•`. They are class **(T)**: decoded, both are

```text
PProd.{u,v}  : ∀ α:Sort u, ∀ β:Sort v,        Sort max(max(0+1,u),v)
PSigma.{u,v} : ∀ α:Sort u, ∀ β:(α → Sort v),  Sort max(max(0+1,u),v)
```

— the resultant sort contains a literal `1`, so it is `provably_nonzero` at
**every** σ, and `PProd.{0,0}` is `Prop → Prop → Type 0`. The store says the
same thing from the other side:
`⊢ ⟦PProd.{0,0}⟧ ∈ fs(⟦Sort 0⟧, fs(⟦Sort 0⟧, ⟦Sort 1⟧))` — two `Prop`
parameters, a `Type 0` result. They live in
`IndApparatus::decls` and have no `A_φ` at all. So the split is by the
**carrier's** class, and 1b's premise is not `LeProp::elim` but the carrier's
own — which is Isla's `TruncFields`-shaped argument again, one layer over.

The `•` is **not evidence of the structure's class.** It fires because the
projection's *type* is a `Prop`, which is equally true of a `Prop` field in a
`Type`-resultant structure. I had `elim_audit`'s half of the trichotomy
(`And`/`Prod`/`PProd`/`PSigma` `computed=true`, `PropStructure` `computed=false`)
and substituted an inference for the other half, reading the *parameter* sorts
off the blocker's `⟦ty[σ]⟧` line — `f63(⟦PProd.{0,0}⟧, ⟦Sort 0⟧, ⟦Sort 0⟧)` — as
if they were the resultant one. See §1's fifth variant.

Where the `•` comes from is worth stating, because it is not the `Proj` clause:
`infer_type`'s `Expr::Proj` arm returns `tm: None` **unconditionally**, with no
`is_prop` test. `⟦And.left⟧ = •` arrives from the *λ* clause, whose proof branch
needs neither the domain nor the body. So Tara's `084`/`086` finding was right
about the interpretation and the pairs still wait on the typing — which is the
"type or value?" question answering *differently for the two halves of one row*.

### Construction 1 — `And`: `derived/` owes nothing, and the mini ingredient is wired

`LePropFields` (`derived/…/family/le_prop_fields.rs`) is exactly the fact:

```text
⊢ ∀p⃗. ( • ∈ A_φ(p⃗) → ((P₀ ∧ … ∧ P_{k-1}) → (H₀ ∧ … ∧ H_{k-1})) )
       Pⱼ := βⱼ(p⃗,•⃗<ⱼ) ⊆ 1        Hⱼ := • ∈ βⱼ(p⃗,•⃗<ⱼ)
```

`Hⱼ` **is** `⊢ ⟦projⱼ x⟧ ∈ ⟦βⱼ⟧` at `⟦projⱼ x⟧ = •`. It is built, tested
(`derived/tests/family_le_prop_fields.rs`), and already *consumed* — `rec_prop`
reaches it through `app.prop_fields(…)` for the class-(S) eliminator. What was
missing is a second call site, not a theorem and not a store. **Landed.**

### Construction 1b — `PProd`, `PSigma`: a row that did not exist until measured

Same obligation as 1 and 2 — `⟦projⱼ x⟧ = •`, owe `⊢ • ∈ ⟦βⱼ⟧` — but over a
class-(T) carrier, so neither `LeProp::elim` nor `TruncCarrier::elim` is the
premise; the §5.2 carrier's own is. **8 pairs, the second largest piece of the
row, and it was invisible while three declarations sat in the wrong group.** Fen
has it as the blocker with a synthetic witness, so it now exists independently of
the corpus — which is the right response to a row that only appeared when a
misgrouping was undone.

### Construction 2 — the truncated analogue, and `derived/` owes it

`PropStructure` is class (P), so `A_φ` and `LeProp::elim` do not exist for it.
The premise is `TruncCarrier::elim` (`⊢ • ∈ ‖a‖ → ∃w. w ∈ a`) and the collapse
then runs as `LePropFields`' does. Owed, and now **landed** as
`derived/…/family/trunc_fields.rs`, beside `le_prop_fields` as it should be:

```text
⊢ ∀p⃗. ( • ∈ ‖ind(p⃗)‖ → ((P₀ ∧ … ∧ P_{k-1}) → (H₀ ∧ … ∧ H_{k-1})) )
```

**One correction to how I described the route, from Isla, and it is a naming
error with a real cost attached.** I wrote that the witness is "recovered through
the carrier's own inversion". *There is no inversion theorem for a non-indexed
carrier* — `inv` is `IndexedCarrier`'s, and the non-indexed `Ctor` has `mem` and
`inj` only. Structural induction at a `φ` **constant in the induction variable**
*is* the inversion: `TruncFields::elim_psi` is `decl_rect` at
`ψ := ∃y⃗. ⋀ⱼ yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)`, one existential introduction per field in the
step. It costs one `w_rect` Separation — the only one in the file, and the only
thing `le_prop_fields` does not pay. Naming it "inversion" hides that price and
points a builder at a theorem that is not there.

**And the scope condition is enforced by acceptance, which is the strongest form
it could take.** A class-(P) structure may have non-`Prop` fields —
`PropStructure` has two, `someData` and `someMoreData`, both `PUnit.{1}` — and
the truncation has thrown the inhabitant away, so those projections are *not*
interpretable. `infer_proj` rejects them outright:
`"projection … would project data out of a proposition"` (`kernel.rs:1985`),
plus the dependency guard at `:1973`. The corpus was built around exactly that
line: **`085_projProp2`, `087_projProp4`, `088_projProp5` and `089_projProp6` are
all in `bad/tutorial/`**, projecting indices 1, 3, 4 and 5 — the two data fields,
the proof whose *type* mentions one, and a `Prop` field reachable only by
stepping over one. `084` (index 0) and `086` (index 2) are the two that are
legal, and they are the two in `good/`. Read the numbering gap: it is the scope
boundary, written down four times.

**And it has a consequence I did not draw, which Isla did without building a
witness.** `086` is legal and projects index **2**, so the ladder needs
`P₀ ∧ P₁ ∧ P₂` — and `P₁` is the **data** field `someData : PUnit.{1}`'s. It
discharges, because `PUnit.{1}` interprets to a singleton. So `βⱼ ⊆ 1` is
**strictly weaker** than "`βⱼ` is a `Prop`", and a `derived/`-side
field-is-a-Prop guard would have refused a declaration the checker accepts. That
is the whole argument for the ladder quantifying `Pⱼ` rather than deciding it.

**A second layer under it, visible only once the first was fixed:** `086` cannot
ask `infer_proj` for field 1's type at all, because projecting field 1 is
illegal — yet the ladder quantifies `P₁`. *The type is wanted exactly where the
projection is refused.* Fen's rule from it, and it belongs beside §2's masking
corollary: **two blockers in series look exactly like one blocker plus a bad
guess about what is behind it.**

### Construction 3 — half the row, and the only one needing a term

`Prod.fst := fun α β self => proj[Prod,0] self` projects at a **variable**, so
`whnf`'s proj-of-ctor step (`kernel.rs:920`) never fires and a genuine
term-former is required. Two routes, and the choice should be made before
anything is built:

* **(a) the eliminator.** Lean's `proj i s` is definitionally
  `T.rec (λ_. βᵢ) (λ y⃗. yᵢ) s`, and `DepRecursor` plus the ι Fen has just wired
  is that machinery. **Measured obstacle:** `--dump-only=Prod` on `079` reports
  `recursor (not built — this declaration's eliminator was never asked for)`.
  Nothing in the export names `Prod.rec`, so the projection clause would have to
  *pull* an eliminator — a new kind of demand, since every other one so far
  arrives as a `Const` occurrence.
* **(b) the carrier's own structure.** A W-element is a Kuratowski pair and the
  plain fields sit packed in its tag component (`ctor 0 inj` is injective in
  both), so `derived::proj::Proj` — `π₁`, `π₂`, `fst`, `snd`, all unconditional —
  composed with the summand injection and `sigma::Telescope`'s `proj_mem` reads
  a field out directly. `proj.rs`'s header says it was written for precisely
  this: the injectivity theorems "let a proof compare two pairs but never let a
  **term** mention a component".

**η favours (b), and η is the successor row.** `105_structEta` wants
`Prod.mk (fst x) (snd x) = x` at a variable `x`; `Proj::eta` is
`⊢ ∀a∀b. ⟨π₁⟨a,b⟩, π₂⟨a,b⟩⟩ = ⟨a,b⟩`, and a recursor has no η. `Gap::StructEta`
already exists as a separate variant, so `105` is expected to move there rather
than close — **flagged as a prediction, not a measurement**: it cannot be
checked until construction 3 lands, and §1's fourth category says to say so.

`Prod` is scheduled at `u,v := 0,0` and `1,1` and its field is data at both, so
for `Prod` this is one construction at two instantiations. **I generalised that
to "a projection is level-generic in a way an eliminator is not" and it is
false** — `PProd` and `PSigma` split across exactly this σ pair, which is row 1b
above. Two over-generalisations from one correct local observation, in one
section; see §1's fifth variant, which is the same shape both times.

The rule that does hold, and it is one decode rather than a slogan: **a
projection's obligation splits across σ exactly when the projected field's sort
is a bare level *parameter*.**

```text
And.left      a : Sort 0        numeral zero      proof at every σ    no split
Prod.fst      α : Sort (u+1)    successor         data at every σ     no split
PProd.fst     α : Sort u        bare parameter    either              SPLITS
PSigma.fst    α : Sort u        bare parameter    either              SPLITS
```

Only a bare parameter can be zero at one σ and nonzero at another. Fen's
statement — *a projection is level-generic in its term and not in its class* —
is true and is the reason; the table is what tells you *which* declarations it
bites, and it costs one look at the constructor's field types. This is §1's
fifth variant one axis over: read the declaration's own level **expression**,
and note its shape, not just its value at the σ in front of you.

**What this means for the theorem being built now.** Isla's `decl_rect` at
`φ(z) := (⋀P → ⋀H)` constant in `z` is correct as stated and needs no change —
`Pⱼ := βⱼ ⊆ 1` is a *hypothesis*, so the theorem is true at every σ. But at
`σ = 1,1` the consumer cannot discharge `Pⱼ`: `⟦α⟧ ∈ U₁` does not give
`⟦α⟧ ⊆ 1`. So it closes **4 pairs, not 8**, and the other four are row 3's
term-former. The ladder's quantify-don't-decide design — which Isla argued for
from `086` — is exactly what lets one σ-generic statement be usable at only some
σ, so the same property that made it right there makes the count smaller here.

### Where the thesis speaks

* **`:2080–2082`** — `⟦π₁ e⟧γ = π₁(⟦e⟧γ)`, `⟦π₂ e⟧γ = π₂(⟦e⟧γ)`, with the ι
  rules `π₁(a,b) ≡ a` and the η rule at `:1614`'s menagerie. But those are for
  the **menagerie `Σ`**, and Lean's `Prod` reaches the model through §5.1's
  W-type, not as a `Σ`. So the thesis gives the term-formers and **not** the
  clause that connects them to a general structure's projection.
* Carneiro's source language **has no `Expr::Proj`**. Lean's projection is a
  derived notion — definitionally the recursor — and §5.4 leaves the recursor as
  future work. So construction 3 is invention either way, and route (b) is the
  one the thesis actually supplies parts for.
* Nothing speaks to constructions 1, 1b or 2: "a proof projects to `•`" is
  §6.2's left column applied twice, and the inhabitation is a fact about the
  specific carrier — §5.3/§5.2 territory, and `derived`'s. That the three of
  them differ only in *which* carrier supplies the major premise is why they
  read as one problem for as long as they did.

---

## 10. Removing the `fs` clause — scoped ahead of the change (Vera)

The decision: `⟦Π⟧` always emits `dprod`; `derived::fs` and everything on it
stay. This section is the scope, **prototyped and measured** rather than
reasoned — the change is exactly the shape §1's fourth category warns about, so
the deferral was not taken.

Baseline is `a63008b`, measured: `constEv` **186** of 218, 32 waiting pairs,
23 `Scope` / 8 `Library` / 1 `Threading`, corpus runtime **67 s**. (The
coordinator's 174/20 was `proj` row 4 ago — stamp the commit.)

### 1. The fibre needs no new helper

`derived/src/skeleton.rs:94–98`: a term that does not mention the binder becomes
**hole 0 entire** and the skeleton is the bare `Term::var(h₀)`. So a constant
fibre's key in `Interp::fibres` is the same term for *every* non-dependent
arrow — **one table entry corpus-wide**, minting `b(h₀,x) = h₀`, a projection,
once. `dprod_term` then gives

```text
fs(⟦A⟧, ⟦B⟧)      becomes      dprod(⟦B⟧, ⟦A⟧)
```

— the same arity, the arguments swapped. The guessed `const_fibre(A,B)` is the
right *shape* and the wrong *cost*: `fibres` already keys on body shape with the
domain as an argument, and a constant fibre is the degenerate shape, so nothing
new is keyed and nothing new is written. Measured on `036_andType` alone: **1
table miss, 8 hits, all at the constant skeleton.**

`dprod_const_fibre_n` stays and gets *simpler*: at the shared symbol its
hypothesis is `∀x ∈ A. ⟦B⟧ = ⟦B⟧`, discharged by reflexivity. It stops being a
bridge between two clauses and becomes an unconditional fact about one.

### 2. Blast radius, measured — and Π and λ are one decision

`BinderShapes::apply` goes from five outcomes to **three**: `(Dep,Dep)`,
`(Prop,Prop)`, `_ => None`. `fs_cong`'s uses all become `dprod_ext_n` at the
shared fibre. `cond_ext_n` is **untouched** — `n2 == 0` routes to `cond` before
the `!dep` test ever runs, so §6.2's genuine other clause is not in the change.
(The 507/66/75 figures were `e88bd6f`; the populations have moved, so take the
shape and re-measure the numbers.)

**The `Mismatch` arm becomes unreachable, not gone**, and the difference is a
choice to make deliberately. `as_pi` recognises `fs` by *head symbol*, and `fs`
stays in the library, so a stray `fs` term would still decompose as `Fs`. Delete
`PiShape::Fs` and it is gone — and a stray `fs` then yields `NotDecomposable`
instead. This repository has one of each already: `stuck-major-moved` (§8) is a
branch that cannot fire and still mints, `Clause::Undet` was made
unrepresentable.

**Prototyped.** Deleting `pi_evidence`'s `!dep` branch alone:

| | baseline | Π only | Π **and** λ |
|---|---:|---:|---:|
| `constEv` | 186 | **96** | **158** |
| `endpoint-drift` (`Cause::Bug`) | 0 | **64** | **0** |
| corpus runtime | 67 s | 67 s | 83 s |

`Gap::EndpointDrift` is *"the endpoint the caller handed in and the one inference
computes for the same expression are different terms — `⟦·⟧` failed to be a
function at this node"*. **Moving the Π clause without the λ clause re-creates
the two-spellings mismatch one layer down — the exact thing the change exists to
remove** — because `lam_typing_fs` asserts `⟦λ⟧ ∈ fs(dom,cod)` about a type that
is now a `dprod`. Move both and it is zero. They are one decision.

**The whole residual is one sentence, repeated.** After both clauses move, the
only new family is

```text
recursor(T: … the motive's type is not T p⃗ → Sort u₁)     19 pairs
```

over **10 declarations and 4 routes** — `Prod`, `N`, `Bool`, `List`, `TwoBool`,
`PProd` (dependent); `PUnit`, `ProjDataIndex`, `And` (class (S)); `Exists`,
`BoolProp` (class (P), `→ Prop`). It is `motive_set != s.fs.of(spine, v_set)`
written once each in `rec_dep`, `rec_prop`, `rec_trunc` and the indexed
variants: a motive `T p⃗ → Sort u₁` is non-dependent, so its type is `fs` today
and `dprod` after. Mechanical, enumerable, and it is the entire remainder.

### 3. `QUOT-MODEL` §2.1 survives, and its own warning passes

The load-bearing property is that **the domain occupies an argument slot of a
shared symbol** rather than being baked into a minted one. After the change
`⟦α → β⟧` is `dprod(⟦β⟧, ⟦α⟧)` and `⟦Quot α r → β⟧` is `dprod(⟦β⟧, ⟦Quot α r⟧)`
— same symbol, domain in an argument slot. Preserved exactly; T3 and T5 still
cost nothing. Two textual corrections owed there: §2.1 lists **three** keying
mechanisms and there will be two, and T3's sentence names `fs(A,B)`.

§2.1's own warning is the thing to check: *"it becomes a defect the moment any
clause keys decomposition on the interpretation's head symbol."* `as_pi` does.
After the change a constant-fibre `dprod` and a genuine dependent `dprod` both
land in the `Dep` arm, distinguished by **which fibre symbol** — which is what
`fibre_by_sym` exists for. No new conflation, and the invariant is if anything
easier to state with one fewer clause.

### 4. `derived/` owes nothing — measured, not expected

`library-gap` is **8 in the baseline and 8 in the prototype**: the change moves
no library row in either direction. `dprod`, `dprod_ext_n`,
`dprod_in_universe_pair_n`, `lam_typing_dprod` and `dprod_app` all exist and are
exercised today; `dprod_const_fibre_n` stays and simplifies; `fs` and everything
built on it is untouched, as the decision says. Seven of the last ten rows.

### 5. Cost

**One symbol. Same term arity. Runtime +24 %** — 67 s to 83 s corpus-wide, at
9,749,082 → 9,762,181 proved conversions (**+0.13 %**). So the cost is not more
conversions; it is the per-`Π` construction — `dprod` carries Replacement,
`img` and the universe machinery where `fs` had a direct funspace closure. `fs`
was an optimisation and this is its price, measured, in the one place it is paid.

### The soundness question — looked for, not found, and one real loss

I looked for a case where `dprod` at a constant fibre is not interchangeable
with `fs`, because that finding would outweigh the refactor. I did not find one:

* the equation is **unconditional** at the shared symbol — `∀x∈A. ⟦B⟧ = ⟦B⟧` is
  reflexivity — and `dprod_const_fibre_n`'s header already establishes it *at
  `A = ∅`*, warning that the obvious `⋃img(A) = B` route is false there. That
  care is taken.
* **`Sort 0` codomains never reached `fs`**: `n2 == 0` routes to `cond` first, so
  the `imax`-zero case is outside the change entirely.
* a proof-valued domain is `n1 = 0`, one cumulativity raise on either route.

**The one real loss is a detector, not a proof.** `pi_evidence`'s `!dep` branch
carries a guard that turns *"the codomain's typing depends on the binder's
hypothesis"* into `Gap::Skeleton` — the interpretation leaked a variable. Under
`dprod` the fibre premise is discharged **under** the binder, so such a typing is
simply accepted: strictly more permissive, still a real proof, and the only part
of the change that cannot be recovered by re-targeting a statement. If it is
worth keeping it has to be re-stated as an explicit check, because the clause
that enforced it for free is the clause being removed.

### Landed — and the first consequence is the design working, not a defect

`derived::quot`'s `lift_in_funspace` is stated over **`fs`**, and after the
retirement **no interpreted `Π` in mini is an `fs` any more**: `⟦α → β⟧` is
`dprod(h⃗, A)`. So the two do not meet directly, and what joins them is
`dprod_const_fibre_n` — built, exported, **no consumer today**, and wanted
**twice** in `Quot.lift`: once at `A` going in, once at `quot(A, R̄)` coming back
out.

That is not a regression, it is the seam moving to one place. **Every future
library theorem stated over `fs` meets the same bridge**, and the bridge is the
theorem §5 found had been built and never wired — so its first consumers arrive
by the retirement rather than by anyone going to look for it. Worth carrying in
any clause inventory: *`fs` survives in `derived/` as a statement vocabulary and
nowhere in `mini`'s interpretation, and `dprod_const_fibre_n` is the whole of
the join.*

> **This paragraph held exactly, and it is the one nobody re-read.** The two
> `Quot.lift` consumers landed at `9edf304`; the third is the constructor's
> function-typed recursive field, and a fourth (`cod_at_funspace`'s hypothesis)
> is named in §4 above. Four sections of `MINI-HANDOFF.md` written *after*
> `9edf304` nevertheless say the theorem is "stored and unread", and each sized
> the crossing as an unbuilt construction on that basis. The prediction here was
> right and the notes downstream did not check it — `MINI-HANDOFF.md` §33 item 3.
> **A scope that predicts a consumer should be re-read the round the consumer is
> claimed missing**, which costs one `grep` and is the cheapest check in this
> file.

### And the thesis is why this is a removal, not an addition

§6.2 gives the dependent product **unconditionally** (`thesis.txt:2077`) and has
no function-space clause anywhere; the only split is proof-versus-value at
`:2075`/`:2077`. §5's finding was that `fs` is mini's own third clause whose
warrant (`dprod_const_fibre_n`) was never wired. This change retires the clause
instead of wiring it, which closes the same divergence from the other side.

---

## 11. Is the class-(T) recursor universe-agnostic? — scoped (Vera)

A design question, answered by reading the proofs. **Short answer: the theorem
is already general; the *practice* is not, for one locatable reason; and the
optimisation it suggests is gated on the carrier rather than on the target.**

### The construction and its ι spend no rung fact at all

Counted, not inferred — occurrences of `Rung`, `tower`, `Tower`, `pow`,
`transitive` across the whole non-indexed class-(T) recursor stack:

```text
derived/src/inductive/dep.rs        0     DepRecursor, COD/DEP, iota
derived/src/inductive/recursor.rs   0     GenRecursor, step_typed, (S4)
derived/src/inductive/guard.rs      0     the guarded minors
derived/src/inductive/iota.rs       0
derived/src/inductive/rect.rs       0
derived/src/inductive/motive.rs     0
derived/src/recarg.rs               0     recarg_eta
derived/src/inductive/step.rs       1     `s.pow` — the powerset TERM-FORMER
                                          building 𝒫(D × X), not a rung
```

and `family/dep_rec.rs`'s only two hits are **comments** (`:112`, `:115`)
describing what the *consumer* does with `ICOV`. So `T` is an arbitrary set and
nothing in the derivation cares. All three of the recalled facts hold; this is
the **third** independent confirmation that §5.2's target policy is unnecessary,
and `RECURSOR-DESIGN.md` §5.2 should be marked settled rather than re-litigated.

### But the only live discharge of `COD` pins `T` to a rung

This is the part the statement does not show, and it is why the question was
worth asking rather than answering from the shape of the quantifier.

```text
COD(C,T) := (∀x. (x ∈ W → ∀y. (y ∈ app(C,x) → y ∈ T))) ∧ ∅ ∈ T
```

`mini/src/rec_dep.rs`'s `cod_at_rung` takes `T := ⟦Sort u₁⟧` and spends **two
rung facts** — `Rung::transitive` and `Rung::empty_mem` — because a rung is
transitive and contains `∅`. That is the only route in the tree. So the recursor
is built per level today **not because the theorem needs a universe but because
the discharge picks one**.

**And the rung-free discharge exists, is designed, and works.**
`motive::cod_at_funspace` is `⊢ ∀C ∀V. (C ∈ fs(W,V) → COD(C, ⋃V ∪ {∅}))` — a
target satisfying `COD` for *any* `V` the motive lands in, no rung anywhere.

*(**Four claims stood here and all four have been false since `derived`
`c2bd75f`**, which is where the theorem was repaired. They read: it "is dead";
it "returns `None` at every input"; the defect is one re-association, its `k`
being `h ∧ (mx ∧ my)` where the `gen_under` wants `h ∧ mx`; it "is the one
theorem in that module with no test, and `rec_dep`'s tests pin the `None`".
Corrected in place, item by item, because each implies a different wrong
action.*

* *It is **live**, at three sites: `derived/tests/deprec.rs:1451` fires it
  inside a real `COD` discharge, `:1989` is its direct test, and*
  *`mini/src/rec_dep.rs`'s*
  *`cod_at_funspace_is_stated_at_a_function_space_and_at_another_target`*
  *asserts that it returns `Some` — so it has both a test and consumers, and
  neither the "no test" nor the "`rec_dep` pins the `None`" sentence survives.
  The `rec_dep` test is the exact inversion of the one described: it was a
  tombstone and is now a pin on the statement.*
* *The re-association was **real and not sufficient**. A second defect — the
  union injection `left` lifted under `k` with `a1i` before being handed to
  `syl`, which wants it bare — makes the `?` fire on its own, so a reader who
  applied the recorded fix would have found it still dead. `MINI-HANDOFF.md`
  §30 §1 is where that was measured.*
* *What `mini` does **not** take is the route, and that is a live design fact
  rather than a defect: `cod_at_funspace`'s hypothesis is a **function-space**
  membership, and §12 retired the `fs` clause from `⟦Π⟧`, so `⟦T p⃗ → Sort u₁⟧`
  is a `dprod` at a constant fibre and reaching `fs` costs*
  *`ext::dprod_const_fibre_n`. It also discharges at `⋃V ∪ {∅}` and this route
  wants `⟦Sort u₁⟧` itself, which `DepElim::target` stores. `cod_at_rung` needs
  neither bridge. So the answer to this section's question is unchanged and its
  reason is now the true one.*
* ***§4 was corrected at that commit and this section was not*** *— and this is
  the section that declared itself the consumer. A correction applied where a
  claim is *repeated* and not where it is *owned* leaves the owning copy
  authoritative and stale, which is the shape `MINI-HANDOFF.md` §33 item 3
  records four times over for a different sentence.)*

### Where the per-level work actually is — and the target is not the bottleneck

The carrier *construction* is level-free: `Inductive`'s `seed = {A, T}` and
`bound = U({A,T})`, the least universe containing the tag sum and the fibre
codomain, computed **from the sets themselves**. `LEVEL-POLYMORPHIC-INDUCTIVES`
§3.2 says exactly this — but its evidence is `derived/src/wlist.rs`,
`wlist_fun.rs` and `checker/src/tg.rs::list_const`, the **old checker's bespoke
`List` clause**, which `mini` does not use (`wlist` has no occurrence in
`mini/src` outside a comment). The conclusion transfers by a different route
(`bound::least_universe_closed`); the evidence does not. A doc reading as
covering more than it does — the hazard named this round, at a second site.

What repeats per σ, **by unit**, since the units cost very differently:

| unit | what | shared? |
|---|---|---|
| symbols minted | `spec_of`'s `define_abbrev` per field type per σ, hence a distinct `ind` | **no** |
| Separations carved | the W-type's, inside `Inductive::build` | **no** |
| theorems re-derived | `GenRecursor::build` + `DepRecursor::build`, each a `w_rect` Separation plus the guarded minors — **the expensive one** | **no** |
| genuinely σ-dependent content | `⊢ ind(p⃗) ∈ Uₙ`, and the λ-nest's domains `⟦Sort ℓ⟧` | — |

**So the target being general is necessary and not sufficient.** `GenRecursor` is
built over `ind`, and `ind` is keyed on the per-σ field symbols, so the recursor
cannot be shared across levels until the carrier is. `cod_at_funspace` — which
this section wrote as unfixed and which was repaired at `derived` `c2bd75f` —
removes the rung *dependency* from the statement; it does not remove the per-σ
*rebuild*, and mini does not take that route anyway, for the two reasons above.

Whether the carrier could be shared is per-declaration and readable: a field type
mentioning a `Sort` at a level **parameter** makes the spec σ-dependent
(`PropStructure.mk`'s `someData : PUnit.{v}`); a field type that is a parameter
or a closed inductive does not (`List.cons`'s `α`, `RBTree.red`'s `n : N`). Same
test as §1's fifth variant — read the declaration's own level expression — one
axis over again.

### Backlog shape

Two independent halves, and the small one is not the useful one on its own:

1. ~~**`cod_at_funspace`'s association bug**, one line, with this as its
   consumer. Makes the recursor's target rung-free in practice as well as in
   statement.~~ **Repaired at `derived` `c2bd75f`, in two places and not the one
   this item names** — see the corrected paragraph above. It was never one line
   and it is no longer work. What it does *not* buy is the rung-free target for
   `mini`, and the reason is in the statement rather than in its health:
   `cod_at_funspace` is stated over `fs` and discharges at `⋃V ∪ {∅}`, and this
   route holds a `dprod` at a constant fibre and wants `⟦Sort u₁⟧`. So (1) is
   closed and its consumer is somebody else's.
2. **Sharing the carrier across σ**, which is where the Separations and the
   `w_rect` derivations actually are, and which is gated on `spec_of` minting
   field abbrevs per σ. **That precondition is now met**, so this is the whole
   of the item and it is `mini/`'s — recorded here rather than left to be
   re-derived, and not queued behind anything in `derived/`.

Nothing is wrong today. (2) is the real optimisation, and the sentence that
stood here — *"(1) is a precondition for it"* — was true of neither half: (1) is
closed, and what actually gated (2) was `spec_of`.

---

## 12. Function-typed recursive fields (#37) — LANDED; superseded on the tower question by §14

**The name was wrong and that changed the scope.** This was not "infinitary
fibres". `RTree.node : (Bool → RTree) → RTree` — the fibre is `⟦Bool⟧`, a
**two-element set**. The restriction was not finite-versus-infinite branching; it
was *"the fibre must be `finord(m)` for a literal `m` the spec counts"* against
*"the fibre is an arbitrary set the declaration names"*. `RTree` is finitely
branching and was still inexpressible. **Genuinely infinitary branching has no
witness anywhere in `vendor/arena-tests`, `good/` or `bad/`.**

That last sentence is still true and it is the *interesting* one, because #37 is
done and the restriction it did not lift is the one nothing in the corpus can
see. The witness this section says the corpus cannot supply was then written:
`mini/tests/fixtures/infinitary_branching.lean` and
`derived/tests/cumul_infinite_fibre.rs`.

**What this paragraph said next is superseded — read §14 instead.** It read:
`derived::cumul::bnd` is an `ω`-tower predicate, so `NTree.node : (Nat → NTree)
→ NTree` "is refutable rather than underived, and the successor is the thesis
§6.2.1 `κ`-tower". The premise about `bnd` is still true and the conclusion is
not: the route taken was **not** a taller tower. `derived/src/wpath/` bounds
`W(A,B,u)` by its labelled path codes at an arbitrary fibre family, `bnd` is
never stated on that path, `cumul::FibreFacts` lost its `bnd` field, and `NTree`
certifies end to end at `constEv = 6`. §14 is the record of how that choice was
made; RECURSOR-DESIGN.md §5.4 carries the same correction; in DECISIONS.md the
2026-08-05 entry to read is *"Infinitary branching is wired"*, which supersedes
the *"The tower is `ω`-high"* entry above it.

### 1. The blocker and the population

**Closed.** This read *"`115_rTreeRec` / `fun-typed-rec-arg(RTree)`,
`Cause::Scope`, σ = `u_1 := 0`, obligation `⟦ty[σ]⟧` — the type's
interpretation, so the recursor is never reached"*. All four pairs now certify:
`115` and `117` at `pairs=2 typeEv=2 constEv=2`, `116` at `3/3/3`, `118` at
`1/1/1`, `gapped=0` throughout **[measured**, 2026-08-05**]**. The choke point
for a function-typed recursive field is no longer the scope walk but
`cumul::FibreFacts`, which asks `⊢ bnd(Σ(z::γ))` and `⊢ Σ(z::γ) ∈ Uₙ` per
recursive slot and declines as `Gap::IndFibreValue` when `γ`'s `bnd` is
unavailable. The population census below stands as written.

Census over **all** of `vendor/arena-tests` — every constructor with a recursive
field under a `∀`:

| constructor | telescope depth | where |
|---|---:|---|
| `RTree.node` | 1 | `good/115`, `good/116` |
| `Acc.intro` | 2 | `good/117`, `good/118`, `bad/096`, `bad/119` |
| `indNeg.mk`, `indNegReducible.mk`, `reflOccInIndex.mk` | 1 | **`bad/` only** — acceptance rejects |

**Two declarations in `good/`, and one of them already has a direct clause.** So
#37's whole reachable population is `RTree`, 4 pairs.

### 2. What changes — the size axis, and it pays at the estimate's hardest item

The estimate names `step.rs`, `values.rs`, `typed.rs`, `iota.rs`, `rect.rs`. The
`finord` surface is in fact **wider**: `carrier.rs` 6, `ctor.rs` 5, `iota.rs` 12,
`rect.rs` 11, `spec.rs` 1, `step.rs` 13, `typed.rs` 9, plus
`family/{good,goodstep,gval}.rs`, `recarg.rs`, `cumul/*` and `isum/*`.

**But counting `finord` is the wrong measurement, because it plays two unrelated
roles.** As the **tag sum** it is one tag per constructor — `n` = the number of
constructors, genuinely finite, and untouched by this change. As the **fibre**,
`B(tagᵢ) = finord(mᵢ)`, it *is* the restriction. Sorted by whether the use is
opaque or enumerating:

* **Opaque — changes by swapping one accessor.** `step.rs`'s
  `FWᵢ = 𝒫(prod(finord(mᵢ), W))`, `typed.rs`'s `g ∈ fs(finord(mᵢ), cod)`,
  `ctor.rs`'s `app(B, inj_i⟨y⃗⟩) = finord(mᵢ)`, `iota.rs`'s
  `recfun ∈ fs(finord(mᵢ), W)`. All reach the fibre through **one** helper,
  `Cx::finord(i)` at `step.rs:189`, and then treat it as a set. Already
  parameterised in substance — the estimate overshoots here exactly as the axis
  predicts.
* **Enumerating — the real work.** `rect.rs`'s `recarg_eta`,
  `⊢ ∀S ∀f. (f ∈ fs(finord(m),S) → f = recfun(app(f,I₀•) … app(f,I_{m-1}•)))`,
  which reconstructs a function **from `m` values**; and the ι rule's per-child
  applications at `Injⱼ(•)` (`step.rs:43`, `iota.rs:329`).

**And the axis pays at the sharpest point.** `recarg`/`recarg_eta` exist *only*
to bridge "`m` separate arguments" ↔ "one function" — `recarg.rs`'s own header:
`f(r₀ … r_{m-1}) ∈ fs(finord(m), carrier)` with `f(r⃗)(Inj_j •) = r_j`. **A
function-typed recursive field needs no bridge, because Lean hands you the
function**: `RTree.node children` has `⟦children⟧` already a set function. So
the estimate's hardest named step is not widened on the new path — it is
**skipped**. Third for three.

### 3. What `derived/` owes

One thing, and it is the currying seam. The field's interpretation is a
**dprod nest** (curried, one level per `∀z::γ`); `sup` wants a **function out of
the Σ-telescope** (uncurried, domain `Σ(z::γ)`).

* At **`RTree`** — depth 1, constant fibre — that is exactly
  `dprod_const_fibre_n`, **already built**, and it is another consumer of the
  bridge §10's retirement created. So `RTree` may cost `derived/` *nothing*.
* At **`Acc.intro`** — depth 2, dependent — it is genuine currying.
  `derived/src/sigma/telescope.rs` exports `ty`, `intro`, `proj_mem`,
  `tail_mem`, `eta`, `tuple_of` and **no `curry`/`uncurry`**; nor is there one
  elsewhere in `sigma/` or `funcs`.

Shape of the statements, for a telescope `γ` with `Σγ := Telescope::ty`:

```text
⊢ ∀p⃗ ∀S ∀f. ( f ∈ dprod-nest(γ, S) → uncurry(f) ∈ fs(Σγ, S) )
⊢ ∀p⃗ ∀S ∀f ∀z⃗. ( (f ∈ dprod-nest(γ,S) ∧ z⃗ ∈ γ)
                   → app(uncurry(f), tup(z⃗)) = app…(f, z⃗) )
⊢ ∀p⃗ ∀S ∀g. ( g ∈ fs(Σγ, S) → curry(g) ∈ dprod-nest(γ, S) )   [if ι goes back]
```

**Stated as a proposal from the shapes, not read off a design note** — the exact
spelling depends on how `fibre.rs` chooses to present the sum, and at depth 1
with a constant fibre the first two degenerate to `dprod_const_fibre_n` and
reflexivity. Isla should treat the degenerate case as the specification and the
general case as the thing to design.

### 4. The thesis does not restrict — the restriction is ours alone

`derived/src/fibre.rs`'s header quotes `thesis.txt:1800`:

```text
Γ; t : F ⊢ (∀z :: γ. t e) → τ ctor ⇒ A; p. Σ(z :: γ) + B; …
```

and then says in as many words: *"For a plain recursive argument the telescope
`γ` is empty, so `Σ(z::γ)` is `1` and the clause is `1 + B`. A constructor with
`m` recursive arguments therefore gets `1 + (1 + (… + 0))` with `m` copies — the
finite ordinal `m`."* **`finord(m)` is the thesis's own general rule specialised
to `γ = ∅`.** The general clause is one line of the thesis that `derived`'s own
header already quotes, and `finord` is `ISumSyms`'s iterated binary sum with
every summand `1` — so the generalisation is *replace the summand `1` with
`Σ(z::γⱼ)`* in machinery that is already general in its summands.

**Provenance caveat, and it is mine to flag.** `thesis.txt` is not in this
session's scratchpad — the previous session's is gone — so this is read
**through `fibre.rs`'s and `recarg.rs`'s quotations**, which agree on `:1800`,
rather than from the file. Second-hand. Anyone with the file should confirm
`:1800` before it is relied on.

### 5. `Acc`'s direct clause — job 1 required, job 2 dissolves

* **Job 1, matching the thesis, is not merely legitimate — it is required.**
  `acc` is one of the thesis's **eight** menagerie types
  (`⊥, Σ, +, ulift, ‖·‖, W, =, acc`), so `Acc` is not a W-type *in the thesis
  either*. Closing #37 does not touch this and the clause stays whatever else
  happens.
* **Job 2, dodging this gap, disappears.** With a general fibre, `Acc.intro`'s
  depth-2 field becomes expressible and the W-route exists, so the clause
  becomes an optimisation over an available route rather than the only route.
* **And the census makes that sharper than expected: `Acc` is the *harder* of
  the two witnesses and it is the one already covered.** Closing #37 for `RTree`
  exercises only depth 1 at a constant fibre; the depth-2 dependent case stays
  untested even after, because `Acc` takes the direct clause.

### What would have to be built, because the corpus cannot test this

Three synthetic declarations, and the corpus supplies **none** of them:

1. **depth 1, non-constant** — a field `∀ z : γ, T` where `γ` depends on an
   earlier field. No witness.
2. **depth ≥ 2, dependent, reaching the W-route** — `Acc.intro` is the shape but
   takes the direct clause, so a synthetic twin is needed.
3. **genuinely infinitary** — `α → T α` at a parameter. No witness anywhere, and
   it is the case the task is *named* after.

`RTree` alone would leave the general path exercised at a constant two-element
fibre and nothing else. This is §1's "passes on the corpus and is wrong at the
fourth shape" with the corpus supplying only the first shape.

### Collision surface

Of Bram's four, **`Acc.rec` is directly on it** — `rec_acc::pack` is the
direct clause's eliminator, i.e. job 2's territory — and `iota(RBTree.rec)`
touches `iota.rs`, which holds 12 of the `finord` uses.

---

## 13. The one habit worth keeping

Every good finding on this run came from the same move: **the design note said
X, the measurement said Y, and Y was right.** `Acc`'s blocker was the carrier,
not the recursor. `069` was a constructor, not a projection. Class (P) was four
tiers, not one. The thesis had no `Sort 0` quotient clause. `084`/`086` closed
outright.

The notes in this repository are unusually good and are still, reliably, one
round behind the code. Trust them for *intent* and measure for *state*.

---

## 14. Infinitary branching — **landed**, by path codes rather than a `κ`-tower

Successor to §12. **Done**: `constEv` on
`mini/tests/fixtures/infinitary_branching.ndjson` is **6**, every pair, and
`inductive NTree | leaf | node : (Nat → NTree) → NTree` certifies end to end.
The route is B, §3 below — bound `W` by its labelled path codes — and Route A,
the `κ`-tower this section was originally written to scope, was never started
and should not be.

This section is kept as the record of how the choice was made and of what each
estimate got wrong, because three of them were wrong and two in the cheap
direction. §6 is the status; §7 is the owner's question, answered against
measurements rather than against the code.

### 1. What is actually required, and why `ω` cannot be repaired

`derived::cumul::bnd(k)` holds exactly when `|k| < cf(ω)`, i.e. when `k` is
finite, and it is the hypothesis `tower_closed_bnd` spends to close
`T = ⋃ₙ Vₙ` under `sup`. The instinct that a *stronger step operator* fixes it
is wrong, and the reason is a fact about ranks rather than about the
construction: with `Nat`-branching there is a tree whose `n`-th child has rank
`n` (rank `ω`), then one whose `n`-th child has rank `ω+n`, and the ranks so
reachable are **cofinal in `ω₁`**. Any tower closed under `sup` at a countable
fibre must therefore have length at least `ω₁`. That is the content of
`cf(κ) > sup_{a∈A}|B(a)|` and no choice of `G` avoids it.

### 1a. Route C — "put the carrier in an existing universe" — asked, answered, no-op

Asked once as its own round, because the kernel is TG and `derived/src/tower/`,
`U(c)`, `Uₙ`, `isum_in_universe` and `dprod_in_universe` are all built and
heavily used, so "a universe was never tried" is a natural reading of §1. **It
is wrong, and the complete pattern is
`rg 'least_universe_closed|universe_closed\b'`: `derived/src/bound.rs` exports**

```text
⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a ∈ A. B(a) ∈ u)) → closed(A,B,u))
⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a ∈ A. B(a) ∈ U(c))            → closed(A,B,U(c)))
```

**with no fibre condition at all** — no `bnd`, no `B(a) ∈ ω` — and its header's
first line is *"a universe is closed under `sup`"*. It is consumed by `wnat`,
`wlist`, `enums`, `wrec`, `wrec_unit` and `inductive/carrier.rs`. A universe is
already the W-type's **bound**, at every W-type in the library, and it is
already sup-closed at a `Nat`-indexed fibre.

The confusion is bound versus catcher, and it is worth naming once:

| set | job | infinite fibre |
|---|---|---|
| bound `U(c)` | `W` is Separated out of it; `W ⊆ U(c)` is free | **fine today** |
| catcher `T` | `W ⊆ T` **and `T ∈ U₁`**, so `C₂` gives `⟦T⟧ ∈ U₁` | this is what `bnd` buys |

A universe cannot be a catcher. `u ∉ u` by Regularity, and the only `U ∈ U`
fact anywhere is `universe::tower_step`, `⊢ ∀x. U(x) ∈ U(U(x))` — one rung too
high, so a universe catcher puts a `Type 0` inductive in `U₂`. `U(c) ∈ U₁` is
not reachable either. **This paragraph used to blame that on CSB, and that is
no longer true and was never the reason:** `is_universe(U(x))` is a theorem
since 2026-08-05 (`universe::least_universe_is_universe`, `derived/src/csb`),
and it changes nothing here, because it says `U(c)` *is* a universe and not that
it is a **member** of `U₁`. `C₄` at a rung is still only reached by transfer
through the intersection, the one `⊆`-to-`∈` tool that transfer exposes is
`cantor::image_in_universe`, and that wants a **member** of `u` surjecting onto
the target. Constructing that member *is* the work; the universe supplies none
of it.

And the universe's set-indexed-union closure — the thing the question is really
about — **is already spent**: `Inside::tower_mem` derives `T ∈ U(c)` from the
`ω`-indexed family `iter(S)` by exactly that closure. The index is `ω`, so the
catcher is `ω` tall. A taller catcher in the *same* rung needs a taller index
(Route A) or a power set (Route B). Nothing about Routes A/B below changes;
nothing was landed but this note and one in `cumul/bounded.rs`, and `constEv`
on the fixture stays **2**.

### 2. Route A — the thesis tower at a regular `κ`

**Settled: §6.2.1.** `thesis.txt:2144-2149`, "Definition of W-types in ZFC",
carries the formula as `cf(λ) > sup_{x∈A}|B(x)|` and the rank argument that goes
with it; §6.3 is "Soundness" and contains no cofinality statement.
`derived/src/tower.rs` cited §6.3 and has been corrected in place;
`derived/src/cumul/bounded.rs` was right.

The thesis's own sentence is worth quoting, because it names the fibre condition
the `ω`-tower cannot state: *"If `cf(λ) > sup_{x∈A}|B(x)|`, then `V_λ` is an
upper bound for `W`, since `rank ∘ f` is a sequence of ordinals of length
`B(a) < cf(λ)`. Thus, `U_{n+1}` is closed under W-types if the `κ` sequence is
`(n+1)`-correct."* The fibre condition there is **`|B(a)| < κ`**, i.e.
`B(a) ∈ Uₙ` — *not* finiteness. `bnd` is the `ω`-tower's shadow of it, and the
thesis never asks for anything stronger than membership.

Faithful, and the cost is a development that does not exist:

| prerequisite | in `derived/` today |
|---|---|
| von Neumann ordinals | **none** — no `ordinal`, `rank`, `transfinite`, `wellorder` anywhere |
| recursion over a well-ordering | **none**; `recursion/` is Peano-only |
| a regular `κ` above the fibres (Hartogs / successor cardinal) | **none** |
| `T ∈ Uₙ` by Replacement over the index | `tower::Family::at` — **have it** |

`derived/src/recursion/` is **4 911 lines for `ω`-recursion alone**
(`peano`, `approximation`, `agree`, `unique`, `existence`, `iterate`). The
transfinite analogue is a second development of that order, *before* one line
of `cumul/` changes — and then `stages.rs`, `bounded.rs`, `closed.rs` and
`chain.rs` (1 499 lines together) are re-derived at the new index, with
`Stages::directed` becoming a genuine cofinality argument rather than the
`succ`-of-the-hypothesis trick it is today.

### 3. Route B — bound `W` by its path codes — **BUILT**, in `derived/src/wpath/`

**Not the thesis's, and it was flagged as invented rather than read.** The
standing rule is to check Carneiro before inventing; §6.2.1 is now in the tree
and says nothing like this. The rule's recorded exception applies:
`derived/src/wrec.rs`'s header, *"Carneiro defines the recursor by transfinite
recursion on rank, which would mean developing ordinals. The union-of-attempts
construction lands in the same place and needs only W2"*. This is the same move
at the carrier, and it landed.

The theorem is `wpath::w_in_universe_paths`:

```text
⊢ ∀A ∀B ∀u ∀Q ∀d. ( ((closed(A,B,u) ∧ amb(A,B,Q))
                     ∧ ((W ⊆ U(d) ∧ Q ∈ U(d)) ∧ A ∈ U(d)))
                       → W(A,B,u) ∈ U(d) )
```

**No condition on the fibres appears in it.** `bnd` is not weakened; it is never
stated. `derived/tests/wpath.rs` derives it, hypothesis-free, and pins every
conclusion.

**Three things this estimate got wrong, and each made the construction cheaper:**

1. **`Seq` is never built, and neither is `D`.** The estimate had
   `D := ⋃_{a∈A} B(a)` by Replacement and `Seq := ⋃ₙ Dⁿ` by `ω`-recursion. Both
   are unnecessary: the paths only need *some* ambient set closed under the
   Kuratowski pair and containing `∅` and the fibres, and the `ω`-tower `T` is
   already one — `cumul::tower_amb`. So `recursion/iterate.rs`, `Family::at` and
   the Replacement instance are **not used at all**.
2. **`code` is not defined by recursion.** The estimate assumed a recursively
   defined function `code(w)`. What is defined is the *relation*
   `paths(A,B,u,Q) ⊆ prod(W, prod(Q,A))` — "`s` is a finite path in `w` with
   label `x`" — as the **least set closed under two rules**, which is one
   Separation, the pattern `wtype` and `acc` already use. `code(w)` is then
   `{ q ∈ prod(Q,A) : ⟨w,q⟩ ∈ paths }`, a second Separation per call. **No
   `wrec`, no ordinals, no recursion theorem.**
3. **`T` does not disappear.** The estimate said "there is no sup-closed
   bounding set any more, so `Stages`, `bounded`, `closed`, `tower_closed_bnd`,
   `w_sub_tower{,_bnd}` and `Fin⁺` are replaced rather than repaired." Wrong on
   the first four: `Stages` (`directed`, `zero_least`), `closed.rs`'s
   `pair_in_stage` / `sub_in_stage` / `mem_tower`, and `Inside::tower_mem` are
   all *used*, and the tower keeps its `Uₙ`-membership job. What the tower stops
   being is the **catcher**; it becomes the set the **paths** live in, where its
   height was never in question. Only `bounded` (`bnd` itself),
   `tower_closed_bnd`, `w_sub_tower_bnd`, `w_in_universe_bnd` and the `bnd` half
   of `Fin⁺` become dead.

The whole of the size demand is **binary** pairing on `Q`. `tower_closed_bnd`
needed a whole `B(a)`-indexed function to land in one stage, because it placed
the node `⟨a,f⟩`; the path route pairs one fibre element at a time, so nothing
grows with the fibre. That sentence is the construction.

Shape of what landed, 3 300 lines in six files plus one bridge:

| file | theorem |
|---|---|
| `wpath/condition.rs` | the two rules, the symbol, `paths ⊆ prod(W, prod(Q,A))` |
| `wpath/induction.rs` | **P2** — `paths` is the least closed set |
| `wpath/intro.rs` | **P1** — `amb`, and the rules hold of `paths` |
| `wpath/inversion.rs` | **P3** — no junk |
| `wpath/decompose.rs` | `root_label`, `step_premise` — P3 at a node |
| `wpath/injective.rs` | **P4** — one `w_rect`; the hypothesis is one *inclusion*, not an equivalence, which halves the proof |
| `wpath/member.rs` | the theorem, by `cantor::image_in_universe` |
| `cumul/wpaths.rs` | `tower_amb` — the tower satisfies `amb`, from `∀a ∈ A. B(a) ⊆ S` alone |

### 3a. The blast radius, measured

**`bnd` is three different names.** A naive `rg` reports 94 files and 1 018
lines; after separating `derived::bound::Bound` (the W-type's *universe* bound,
held in locals called `bnd` all over `checker/src/tg.rs` and the hand-written
carriers) and `Approx::bounded`/`rec_acc::Bounded` (the recursion theorem's
axiom A1), the real surface is **36 files**. Anyone scoping from a grep will
overstate this by a factor of three.

| crate | files | src | tests |
|---|---:|---:|---:|
| kernel | **0** | 0 | 0 |
| derived | 28 | 22 | 6 |
| checker | 1 | 1 (doc only) | 0 |
| mini | 7 | 3 | 4 |

By role: **7 producer** files (`bounded`, `pullback`, `finite`, `finord`,
`sum_bnd`, `carrier_bnd`, `telescope_bnd`), 7 consumer, 7 statement/shape-pin,
15 doc-only.

**`bnd` is *spent* in exactly one mathematical place**: `cumul/closed.rs:221`
and `:258`, inside `tower_closed_bnd`. Everything else produces it or carries
it. That is the good news, and it is not where the difficulty is.

**The difficulty is `Stages::directed`.** `cumul/stages.rs:26-49` proves
directedness by *successor-chasing* — `n = succ n′ ⟹ p := succ p′` — and its own
header advertises that as the reason no order on `ω` is needed. **That proof has
no limit case at all.** A `κ`-tower must re-prove directedness with an order and
a cofinality argument, and that, not `bnd`, is the thing with no foundation
under it.

What *is* already in place for a `κ`-tower: `Rung::funspace`
(`⊢ (a ∈ Uₙ ∧ b ∈ Uₙ) → fs(a,b) ∈ Uₙ`) at every rung `n ≥ 1`, and Replacement
via `Tower::family(b)` — but Replacement is **per family symbol**, not
`∀`-quantifiable inside one theorem, so every distinct family costs a
`Tower::family` call that mints symbols. A `κ`-indexed stage family is one such
symbol, which is the shape one would want anyway.

### 4. The interface answer

`FibreFacts` has two components per recursive slot. **Measured at `NTree`
(`derived/tests/cumul_infinite_fibre.rs`): the universe half `⊢ Σ z:⟦N⟧. 1 ∈ U₁`
derives today and only `bnd` does not.** So the obstruction is exactly one
component, and on both routes that component stops carrying information:

* Route A picks `κ := (sup over the fibres of |Aᵢⱼ|)⁺`, which is computed from
  the `mem` component; every fibre is then below `κ` by construction and
  `bnd(Aᵢⱼ)` is free. Whether the *field* then goes is a design choice, not a
  forced one.
* Route B has no `bnd` to state, so the field goes.

So `FibreFacts` loses its first field, and with it **fourteen** `Thm`-producing
entry points lose their only consumer — `bounded`, `bnd_empty`, `bnd_singleton`,
`bnd_bin_union`, `bnd_finord`, `bnd_finords`, `bnd_tagged_copy`, `bnd_sum`,
`bnd_isum`, `bnd_isums`, `bnd_unit`, `bnd_carrier`, `bnd_nullary_tags`,
`bnd_telescope1`, plus `pullback::bnd_via_pullback` behind three of them and the
formula builders `bnd`/`bounded_at` in front of all of them.

**How far `mini/` moves depends on which of the three the change is, and the
spread is large.** Measured per site:

**Routes A and B are *which construction*; (i)–(iii) below are *what is done
with `bnd` afterwards*, and they are independent choices.**

| fate of `bnd` | what it means | `mini/` cost |
|---|---|---|
| **(i)** survives, new proof | name and formula unchanged, `FibreFacts` keeps both fields | **zero code changes.** One integer in `mini/tests/infinitary.rs` (`constEv` 2→4), and six comments asserting "`bnd` is refutable at an infinite set" that stop being true |
| **(ii)** derivable from `k ∈ Uₙ` | formula stays, every proof of it is free | ~6 sites: `zoneb.rs:2435, 2484, 2496-2510`, the `carrier_bnd` memo in `interp.rs:527-528/845-846/1192-1223`, `ev.rs`. `constEv` 2→6; the "both facts unconditional" guard at `zoneb.rs:2456` relaxes, which is what closes `FieldTree` |
| **(iii)** disappears | no formula; `FibreFacts` loses a field | all of (ii), plus hard compile breaks at `zoneb.rs:2435,2501,2522` and `interp.rs:1213-1214`; `fibre_facts` (147 lines) deleted wholesale; `Gap::IndFibreValue` probably retired |

**(i) is not a viable landing, and this is the trap to avoid.** A `κ`-tower
makes `bnd(⟦N⟧)` *true*; it does not make anything **derive** it. The only route
to `bnd(⟦γ⟧)` in the library runs `carrier_bnd → bnd_nullary_tags → bnd_carrier`,
and both of those refuse a `γ` with a recursive constructor — `bnd_carrier`
*structurally*, because its proof is a pullback along `mk(x) = ⟨x,∅⟩` that needs
every fibre empty. So a `κ`-tower landed as (i) leaves `constEv` at **2**: it
closes nothing on the fixture and nothing on the corpus, and it is precisely the
shape this project has paid for four times — a generalisation landed ahead of its
consumers. The producer that would close (i) is *"`bnd` from `k ∈ Uₙ`"*, which is
(ii).

So the real choice is **(ii) on Route A** or **(iii) on Route B**. Route B forces
(iii): there is no tower left to state `bnd` over.

**(iii) is what landed, and the row's `mini/` cost was over-stated.** Measured
across the three commits: `mini/src/zoneb.rs`, `mini/src/interp.rs` and
`mini/tests/infinitary.rs` — **three** files, not seven, and no hard compile
break anywhere except the one `FibreFacts { bnd, mem }` literal. The predicted
break sites `zoneb.rs:2435,2501,2522` and `interp.rs:1213-1214` were all inside
code that was deleted wholesale rather than adapted. `Gap::IndFibreValue` was
**not** retired: it still keys the three refusals `fibre_facts` has left (a `γ`
that is not a bare constant, one whose typing carries the parameters' scope, one
resident below the declaration's rung).

That is the architecture answer, and it is **not one answer**: under (ii)
`mini/` moves at six sites and keeps its shape; under (iii) it loses a function.
**The interface contains the change exactly to the extent that `bnd` keeps its
name** — and the cheapest landing that actually closes `NTree` already breaks
that containment, because it must reach past `bnd`'s producers and delete them.

**Coordination note.** Of the files another seat owns, only `mini/tests/dump.rs`
(3 lines) and `mini/tests/tutorial.rs` (4 comment blocks) appear anywhere in
this radius, and both are **doc-only under all three scenarios**. `main.rs`,
`run.rs`, `ledger.rs`, `dump.rs` and `designed.rs` are entirely clean of `bnd`.

### 5. The standing declines, and what happens to each

* **`bnd` at telescope depth ≥ 2** — needed a Replacement-indexed union over
  `β₀`-many indices, which `Stages::directed` (a two-way merge) cannot give.
  On Route B **the obligation is deleted, not discharged**: there is no `bnd`
  at any depth, and `bnd_telescope1`'s depth guard is off the path. What is
  left is the `mem` half, `Σ y⃗:β⃗. 1 ∈ Uₙ`.

  **This bullet used to end "the remaining work is one `k`-ary call site, not a
  theorem", and that is wrong — measured, and it is the cheap direction again.**
  `sigma_n::summand_at` is `k`-ary, but only over an `Inductive`'s *argument*
  telescope: its `levels()` reads `ind.telescopes[ci]`, checks
  `ind.spec.ctors[ci].args.len()` and pins the result against
  `ind.summands[ci]`, none of which a **fibre** telescope has. The only entry
  point taking a `Telescope` directly is `unary_telescope_at`, and
  `unary_sum_of` requires `tel.ys.len() == 1`. So the remaining work is a
  `telescope_at` — the `k`-ary analogue of `unary_telescope_at`, i.e. exactly
  the split that already exists between `unary_summand_at` (over an
  `Inductive`) and `unary_telescope_at` (over a `Telescope`), made at depth `k`.
  That is a **refactor of `summand_at`'s core**, not a call site and not new
  mathematics. Pinned at the terms in
  `derived/tests/cumul_decl_fibres.rs::a_fibre_telescope_of_depth_two_declines_at_the_unary_entry_point`.
* **`bnd` of a carrier with recursive arguments** (`bnd_carrier`'s `recs`
  guard) — deleted with the rest. It existed only because the pullback along
  `mk(x) = ⟨x,∅⟩` needs empty fibres, and the pullback existed only to prove
  `bnd`. Note the guard was *right*: `bnd(⟦N⟧)` is **false**, and no route makes
  it true. What the path route does is stop asking.
* **A `γ` that mentions a *parameter*** — **closed, and the two corpus exports
  moved rather than followed.** This bullet twice named a refusal and twice the
  reason expired. First: `cumul::sum_bnd` requires `bnd(Aᵢⱼ)` unconditional and
  `bnd` at a parameter is refutable, so the two per-summand obligations stood or
  fell together — gone with `bnd`. Then: `isum::isum_in_universe` rejects an
  input carrying a sequent hypothesis *or* an antecedent, structurally, where
  the fact is spent — true, and a statement about a library that had not been
  asked to carry one.

  **What it took.** `isum::isum_in_universe_under` is the same fold under
  `ctx::Ctx`, and `DeclUniverse::over_at_general` spends it: `T ∈ Uₙ` and
  `⋃T ∈ Uₙ` move from the unconditional group to the conditional one, `fin` and
  `S ∈ U({A,T})` stay. Nothing is weakened — every input is still a `⊢` with
  nothing on the left, and `H` lives in the conclusion where `Thm::gen` over the
  parameters can pass it.

  **The mini-side half was not where this bullet said it was, and that is the
  finding.** The row's *hypothesis set* was only half the obstacle: it was also
  stated at the **walk's own scope variable** while the term it had to match was
  stated at `Inductive::params`, so both disjuncts of `zoneb`'s guard fired.
  One discharge through the parameter scopes — the same step every summand leg
  already took, added to `spec_of`'s step 3 — fixed both at once, because
  `Closed::discharge` generalises the scope variable and instantiating at `p⃗`
  puts the theorem on the carrier's. And it is what gives a declaration with **no
  plain field** an `H` at all: `T (α) | node : (α → T α) → T α` has no leg, so
  before the `γ` typings were read there was nothing in the declaration to read
  `H` off.

  **Measured.** `constEv` on `mini/tests/fixtures/parameter_domain_branching.ndjson`
  is **8** — four trees, two `def`s each, `waiting` empty,
  `untranslated declarations=0`. The `?`-census over `zoneb::fibre_facts`,
  `cumul::decl::over_at_general`, `cumul::sigma::unary_telescope_at` and
  `isum::isum_in_universe`: before, `zoneb.rs`'s `hyps().is_empty()` guard twice
  and **nothing else**; after, silent.

  **`113`/`114` advanced one construction and stopped again**, and their
  untranslated reason moved from `ind-fibre-value(…)` to
  `ctor(…: recursive field codomain)`. Their carrier is placed; what refuses
  them is in `zoneb::constructor`, and it is not a placement obligation at all:
  the recursive field's Lean codomain is `constType (T α) (T α)`, whose
  interpretation is an application term, while the constructor's spine is
  `⟦T⟧(p⃗)`. The two are definitionally equal — `rec_field` classifies the field
  by its reduct, which is why the declaration is accepted — but `⟦·⟧` is a
  function of the term, so the membership arrives about one and is owed about
  the other. **One δ/β step, §4's calibration entry exactly**, and the next
  piece of work on this row. The corpus ratchet is unchanged: `accept=89
  decline=2 reject=0`, `constEv=218 typeEv=218`, `untranslated: 1 declaration`
  at both files. `mini/tests/dump.rs`, `decl.rs`'s header, `zoneb.rs`'s
  `rec_dom_sort` and `fibre_facts` headers and the two `zoneb` tests have all
  been corrected in place.

### 5a. And it went through — the conditional route, landed

Step 3 of §14.6 left `FibreFacts` requiring an unconditional summand membership.
It does not any more, and the whole of it is above in §5's third bullet. In
one line: **a Lean declaration is always closed, so a parameterised one's
theorems are conditional on its parameters' typings and every use site has that
assumption ready** — the antecedent is the theorem's *content* at a summand
`Σ(z::α)`, not a shortfall, since a `Tree α` over a non-small `α` has no W-type
in `Uₙ` at all.

Two commits, each green on its own:

1. **`derived/`** — `isum::isum_in_universe_under`, and `over_at_general`'s
   `T ∈ Uₙ` chain under `Ctx`. At `hyp = None` the derivation is term-identical
   and the corpus does not notice, which is what made it landable alone.
2. **`mini/`** — `spec_of` discharges `CtorEvidence::rec_dom_sort` through the
   parameter scopes beside every leg; `decl_universe` reads `H` off **both**
   families, which is the only reason a declaration with no plain field has one;
   `fibre_facts` states every row at `ctx.under(…)` and passes `hyp` on.

**The `mini` side was a discharge, not a placement change**, and the estimate
did not say so. This section, `zoneb.rs`'s two headers and
`the_fibre_summand_frontier_at_np_one_is_closed` all located the obstacle in the
*hypothesis set* and in the library's refusal to accept one. Both were real;
neither was the whole of it. The row was also stated at the walk's scope
variable rather than the carrier's parameters, so the conclusion comparison in
`zoneb` would have failed even with the hypothesis check deleted — and the one
discharge that fixes the hypothesis fixes the variable too, because `gen` then
`inst_all` is exactly that move. *Rule that comes out of it: when a guard is a
disjunction, instrument **which disjunct**; the census that found this printed
one line and the shape print beside it printed two facts.*

### 6. Status — wired, and what each step actually needed

**Route B's mathematics is landed, it is wired, and Route A is not needed.**
`derived/` proves that a Grothendieck universe is closed under W-types at an
arbitrary fibre family, with no ordinals; `DeclUniverse::over_at_general` spends
that theorem; `FibreFacts` has no `bnd` field. **`constEv` on
`mini/tests/fixtures/infinitary_branching.ndjson` is `6`**, up from `2`, with
`waiting` empty and `untranslated declarations=0`. Route A — the `κ`-tower and
the ~5 000-line transfinite-recursion development §2 prices — buys nothing this
does not, and should not be started.

The corpus is unchanged at every step: `accept=89 decline=2 reject=0`,
`constEv=218 typeEv=218`, `unsealed=0 gapped=0`, declines byte-identical.

Steps 1–3 were the wiring and are done. **This list used to say what was owed;
it now says what each step needed, and two of the three needed something the
estimate did not name.**

1. **`Chain` carries the `wpath` symbols** — `cumul::Paths`, built inside
   `Chain::assemble`. Additive, as predicted, and it needed **three** things the
   estimate did not list: `Closures` gains `product_all` (`w_in_universe_paths`
   wants the tower's `∀c` product closure for `I = 𝒫(Q × A)`, and `Chain` kept
   only the five the stages need); `least_universe_is_universe` wants a `Csb`,
   built over the chain's own `Apply` rather than `Csb::new`, which would mint a
   second pairing; and `tower_amb` took a `&Chain` while now running *before*
   one exists, so it is split into `tower_amb_over`.
2. **`DeclUniverse::over_at` swaps its step (f).** The five clauses were named
   correctly and `bound::least_universe_subset` really was the only new line of
   set theory. Two details: `amb`'s hypothesis is a **second** `fin_elim` at a
   `⊆`-only goal rather than a projection out of `Fin⁺` (so it does not depend
   on the conjunct that is leaving), and `W ⊆ Uₙ` is a `∀z` derived under the
   declaration's `H`, which needed two new `Ctx` combinators (`syl`, `gen`).
   Landed on its own, with `FibreFacts` untouched, so that the corpus could
   measure the one thing worth measuring: **the path route is at least as strong
   as the `bnd` route everywhere the corpus goes.**
3. **`FibreFacts` loses its `bnd` field.** `constEv` **2 → 6**, exactly as
   predicted and for the predicted reason. The `?`-census that settled it, over
   `zoneb::fibre_facts`, `interp::carrier_bnd` and `derived::cumul::carrier_bnd`:
   before, `zoneb.rs:2484` twice (`app.carrier_bnd`) and `interp.rs:1213` twice
   (`bnd_nullary_tags`) and **nothing else** — so both declining rows had already
   passed every other `?`, including the `mem` half at `⟦N⟧`; after, silent.

4. **The fourteen `bnd` producers are deleted** — **not done, and the reason is
   that the premise is wrong.** This item used to list `bounded`,
   `tower_closed_bnd` and `fin_bnd` among the casualties. They cannot go:
   `closed::tower_closed`, the `B(a) ∈ ω` form, is *derived from*
   `tower_closed_bnd` and `bounded`, and `tower_closed` is what
   `WMem::w_in_universe` carries, which is what `wnat`, `wlist`, `cumul::enums`
   and `NatUniverse` spend. §3a's "`bnd` is spent in exactly one mathematical
   place, `cumul/closed.rs:221`/`:258`" is exactly right and is exactly why:
   that one spend is on the path to a live theorem. **`bnd`, `bounded`,
   `bounded_at`, `tower_closed_bnd` and `fin_bnd` are all standing, as the proof
   of a statement that never mentions them.**

   What the wiring did orphan, and what was deleted, is `mini`'s
   `IndApparatus::carrier_bnd` memo and its `w_inversion` slot. What it orphaned
   and was **kept**: `bnd_carrier`, `bnd_nullary_tags`, `bnd_telescope1`,
   `bnd_isums`, `bnd_finord`, `bnd_finords` and `WMem::{w_sub_tower_bnd,
   w_in_universe_bnd}`. They are correct, they are tested at the terms
   (`derived/tests/cumul.rs`, `cumul_decl_fibres.rs`, `cumul_infinite_fibre.rs`
   — ~180 lines of `cumul.rs` exercise the `WMem` pair alone), and *unused* and
   *wrong* are different. `cumul/bounded.rs`'s header carries this list and the
   reason; its "dead-in-waiting" line has been corrected there rather than
   here.

### 7. Does it really solve it, or kick the can — answered, and now measured

The owner asked for this in those words. Four answers, and one of them is a
can-kick named as such. **All four were written from the code before the wiring
existed; each is now marked with what the measurement said.**

**1. Does it generalise beyond `⟦Nat⟧`?** **Yes, and `Nat` was never special —
it does not appear anywhere in the construction.** `w_in_universe_paths` and
`tower_amb` are both `∀A ∀B`, the fibre family is a parameter, and no lemma in
`wpath/` inspects it. There is no cardinal, no `ω`, no stage index and no
finiteness anywhere in the eight files. The one place the *shape* of anything is
used is `shared::pair_not_empty` — "a Kuratowski pair is not `∅`" — which
separates the root path from a step path and says nothing about size.

At the translation layer the question becomes *which `γ` can `fibre_facts`
supply `⟦γ⟧ ∈ Uₙ` for*, and the answer is: any declaration `mini` has
translated whose placement is unconditional. Branching over `Bool`, over another
inductive, or over another tree type is the same call. Branching over a
**parameter** is not — see §5's third bullet. **A second end-to-end witness was
not built, because the consumer wiring (§6, steps 1–3) is not landed**; the
generality claim above is about the derived theorems, which are checked.

**Measured.** The fixture has three `γ` — `B2` (two nullary constructors), `P1`
(one constructor with a field) and `N` (`zero`/`succ`, recursive and infinite) —
and all three now supply the fibre fact through the *same* call, with no branch
on `γ`. The second end-to-end witness that was owed is that fixture itself:
`FieldTree` and `NTree` were built to differ from `FinTree` in one coordinate
each, and both closed.

**2. What happens to `P1` / `FieldTree`?** **It closes too, and `constEv` goes
2 → 6 rather than 2 → 4. Confirmed by measurement.** This contradicted the
expectation that Route B closes `N` and leaves `P1`. The reason is that
`FieldTree`'s *only* blocker was the `bnd` half of `FibreFacts`:
`bnd_nullary_tags` refuses `P1` because its tag summand is a one-binder
telescope rather than `1`, and the universe half `Σ z:⟦P1⟧. 1 ∈ U₁` has no such
guard. Deleting the `bnd` half took both rows at once, at one commit, and
`waiting` went from two keys to none.

That the two go **together** is the measurement that identifies the route, and
it is worth keeping: `FieldTree`'s `bnd` is true-but-unbuilt and `NTree`'s is
false, so a taller tower would have closed the second and left the first, and a
lemma for `bnd_nullary_tags` the converse. They went together because the path
route *deletes* the obligation rather than discharging it.

**3. Telescope depth ≥ 2.** The `bnd` reason for that decline — a
Replacement-indexed union over `β₀`-many indices, which `Stages::directed`
cannot give — is **removed rather than discharged**, because there is no `bnd`.
That half holds. **The second half was wrong, and verified wrong by
construction**: `summand_at` is `k`-ary only over an `Inductive`'s *argument*
telescope (`levels()` reads `ind.telescopes[ci]` and pins against
`ind.summands[ci]`), and the only entry point taking a `Telescope` directly is
`unary_telescope_at`, which is unary. What survives is therefore not "a unary
call site" but a missing `telescope_at` — the `k`-ary analogue, a refactor of
`summand_at`'s core rather than a theorem. See §5's first bullet, and
`derived/tests/cumul_decl_fibres.rs::a_fibre_telescope_of_depth_two_declines_at_the_unary_entry_point`,
which pins it.

**4. What shape does Lean support that is still untranslatable?** *This answer
read "precisely two" and named the parameter domain first; that one is closed
and two more have been exposed underneath, so it reads four. Each entry that
closed revealed the next, which is the standing lesson of this section: a
decline's stated reason describes the layer that is refusing, not the
obstacle.* All are `mem`-side rather than `bnd`-side:

* ~~**a recursive argument whose domain mentions a parameter**~~ — **closed**
  (§5a). `inductive Tree (α) | node : (α → Tree α) → Tree α` certifies;
  `constEv` on `mini/tests/fixtures/parameter_domain_branching.ndjson` is `8`.
  *This bullet twice gave a reason the declaration could not be placed and both
  expired — first "`bnd` at a parameter is refutable under any `H`", then
  "`isum::isum_in_universe` refuses a conditional input where it is spent".* The
  corpus's `113`/`114` are **not** witnesses of this shape any more: their
  carrier is placed and they stop at `ctor(…: recursive field codomain)`, a δ/β
  step on the `constType` obfuscation, which is the third entry below.
* **an indexed family whose constructor takes a function-typed recursive
  argument** — `IxT (α) : N → Type | node : {n} → (B2 → IxT α n) → IxT α (N.s n)`.
  Two mini-side layers lifted on 2026-08-05 (`ctor_spec`'s blanket `ni != 0`,
  then `ctor_ix::ctor_abbrevs`' abstraction) and it now reaches `derived/`:
  `IndexedInductive::build` refuses because `gval::matrix_atoms` gives each
  recursive slot the atom `tup(d⃗ᵢⱼ) ∈ r(Inj_j(•))`, a membership at a single
  point, and a `Σ(z::γⱼ)` summand needs `∀z ∈ γⱼ. … ∈ r(Inj_j(⟨z,•⟩))`.
  Located by census at `family/good.rs:247`; `constEv` on
  `mini/tests/fixtures/indexed_infinitary_ctor.ndjson` is **0**, target 4.
* **a recursive argument with a telescope of depth ≥ 2** —
  `node : (α → β → Tree) → Tree`. Declines at `unary_telescope_at`, which wants
  exactly one binder. Needs a `telescope_at`, not a call site — see answer 3.
* **a recursive field whose codomain is a *reducible application* of the
  declaration** — `node : (α → constType (T α) (T α)) → T α`. Accepted by the
  walk, which classifies the field by its reduct; refused by
  `zoneb::constructor`, because `⟦constType (T α) (T α)⟧` and `⟦T⟧(p⃗)` are two
  terms and `⟦·⟧` is a function of the term. Needs one δ/β conversion carried
  onto the membership — §4's calibration class, "add one reduction step wherever
  a note says a certificate transfers unchanged". `113`/`114` are the corpus
  witnesses, and they arrived here by the parameter-domain bullet above
  closing.

Everything outside the fibre-facts chain — indexed families, nested and mutual
inductives, level-polymorphic placement — is untouched by this round and its
status is unchanged.
