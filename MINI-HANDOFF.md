# `mini/` — handoff

Started by Otto (2026-08-02), continued by Wren (2026-08-03). Findings, not
derivations. The derivations are in the module headers and in the commits; what
is here is the part that is expensive to rediscover.

Read `SCOPING.md` (Tara, Vera) first — it is the corpus facts. This is the code.
Sections marked **[Otto]** are his and still hold; the rest is mine, or is his
corrected in place.

---

## 0. The method that paid best: the corner walk

Two variables, four cells, one build.

Twice this week a question of the form *"why does this decline?"* had two
plausible causes and I produced three hypotheses before measuring. Both times
the settling move was the same and cost one build: **enumerate the corners of
the two variables and run all of them at once.**

`class (S) at an index` declined and the candidates were the parameter count and
the field count. The walk:

| `np` | `kᵢ` | `ni` | carrier |
| ---: | ---: | ---: | --- |
| 0 | 0 | 1 | built |
| 1 | 0 | 1 | built |
| 0 | 1 | 1 | declined |
| 1 | 1 | 1 | declined |

Four synthetic declarations, one `cargo test`, and the answer is *the field, not
the parameter, and they do not interact* — which no amount of reading
`LeCarrier::build` had produced. It also localised the failing `?` well enough
for `derived`'s author to find a variable capture from the description alone.

Why it beats reading:

* **It answers the interaction question too.** "Is it A or B" has a third
  answer, "both together", and a corner walk is the only cheap thing that sees
  it.
* **The passing cells are the deliverable.** Two of the four rows built carrier,
  former *and* constructor end to end, so what remained was one named guard
  rather than a hole of unknown size — and the test stayed as a frontier test
  that flipped, loudly, the day the guard lifted.
* **It costs one build whatever the answer is.** Three hypotheses cost three.

The precondition is that you can *synthesise* the corners. On this project you
can: `crate::kernel::add` takes a `Declaration::Inductive` and generates the
recursor, so a four-cell family of declarations is forty lines. That is the
whole trick, and it generalises past `(np, kᵢ)` — the same shape settled the
δ-redex question in §7.

**If you catch yourself on a third hypothesis, stop and walk the corners.** Both
of us have now failed this rule and then applied it; it is the cheapest
instrument anyone has used on this project.

---

## 1. Calibration — which kinds of claim held

**[Otto]** Every wrong prediction I made was about **dynamic behaviour**: what a
run would do, what a row was waiting on, what would be reachable. Everything I
got right by *reading* was static: a statement's shape, an atom's order, which
theorem exists. Tara reached the same split independently and her rule is the
right one:

> **read what you can, measure what you would otherwise predict.**

| claim | kind | outcome |
| --- | --- | --- |
| `IDEPᵢ`'s antecedent is `minor_atoms_at` at `vⱼ`, so the transport reuses | static | **held**, exactly |
| `DepRecursor` cannot state Lean's indexed minor | static | **held** |
| `derived/` owes `077` a construction | static | **held** |
| `iota(RBTree.rec)` sits behind `077` | dynamic | **right, and wrongly retracted** — the census was taken behind a blocker |
| `mᵢ > 0` class-(P) constructors are unreachable | dynamic | **wrong** — Quinn's fixture reaches them |
| `ICOV` needs excluded middle | dynamic | **wrong** — `Rung::app` is unconditional |
| `dprod_const_fibre_n` is the binder row's whole content (Vera) | static | **held** |
| the mirror wants normalising before the scope opens (Vera) | design | **overruled, correctly** — §5 |
| `TruncRecursor` has no consumer (coordinator) | static | **held**, and the reason was §2 |
| `LeCarrier` at `kᵢ ≥ 1, ni ≥ 1` is a limitation (mine) | dynamic | **wrong** — a variable capture |
| the δ-redex cannot be measured until `072`'s carrier lands (Vera) | dynamic | **wrong** — §7 |
| "the last non-ι row" / "the last `Scope` row" (coordinator) | census | **wrong twice** — §6 |
| `072`'s carrier is the unsized risk (Wren, coordinator) | dynamic | **wrong** — §7.1; it was a caller, not a derivation |
| the constructor does not extend from `trunc_ctor_bottom` (Vera) | static | **held**, exactly |
| the δ-redex is unconditional in both directions (Wren) | static | **held** |
| the δ-redex surfaces in the eliminator's minor (mine) | dynamic | **wrong** — §7.3; it is at the alias pair |
| `derived`'s pre-empted interfaces fit unadapted (Isla) | static | **held**, third running |
| `cur_tm = None` is "the shape of the ι gap" (coordinator, relaying Vera) | diagnosis | **wrong** — §8; it is the symptom and `PRE` is the reason |
| `PRE` at the use site's own minors is what is missing (Kai) | static | **held**, exactly; `rec_dep`'s builders needed no variant |
| construction 2 ends in one `step!` per level (Kai) | static | **wrong** — §8.1; `beta_spine` composes and lifts, so it is one leg |
| `cur_tm = None` at the ι site is not a demand (mine, from the K-rule branch) | dynamic | **held** — 67 of 72 mints, measured |

A **fourth** category, and it cost a relay rather than a measurement. Vera
observed a mechanism at the failure point — `whnf`'s ι step sets
`cur_tm = None` — and reported it as that. It was promoted in relay to *the
shape of the gap*, i.e. to a diagnosis, and as a diagnosis it is wrong: setting
`cur_tm` is the last thing that happens, and what stops the step is that `PRE`
is not available at the use site's own minors. The coordinator named the error
as his rather than hers, which is the right attribution and is why it is worth
writing down:

> **a mechanism observed at the failure point is not the reason it fails.**

This is §6's "a census taken behind a blocker" one layer down. Both are the same
move — reading what is visible *at* the stopping point and treating it as what
is *behind* it — and both are cheap to avoid by asking which of the two you
have.

The pattern is stable across six personas: **static reads hold, dynamic
predictions do not, and a census is a dynamic prediction.** A row's count, its
cause, and what is behind it are three separate measurements and none of them
follows from the label. A third category appeared this week and the split does
not cover it — Vera's: *a correct measurement transcribed wrongly*. Right
command, right corpus, right order of magnitude, and "read what you can" does
not protect you when the thing being read is your own output.

---

## 2. Evidence produced and then discarded — six instances, one pattern

**[Otto]** Three times in one month, and three more since:

| site | what was computed | what was dropped |
| --- | --- | --- |
| `zoneb::CtorEvidence::field_sort` | the field type's sort typing | kept, in a form no consumer could instantiate |
| `ctor_ix::one` | `cᵢ`, the constructor abbreviation | its **defining axiom**, with the `Site` |
| `zoneb::build_trunc` | `tc.ctors`, a rule per class-(P) constructor | all of them, by ending at `former_at` |
| `zoneb::build_trunc` again | **the whole class-(P) translation** | `ind`, `tc`, both abbreviation families |
| `zoneb::ensure`'s indexed decline | the whole boundary walk | `IndexAx` *and* `Shape`, on the decline path |
| `rec_dep::dep_bottom` | `PRE` discharged, and `ax` for `app(drec,⟦t⟧)` | both, at the bottom of a λ-nest — **closed**, §8 |

**The pattern: a value computed at the bottom of a call whose site outlives
nothing.** The call has everything in hand at that moment — the scopes are open,
the symbols are fresh, the axioms are live — and then returns one thing and
drops the rest. The next consumer is at a different nest, cannot re-derive
(re-minting gives a *second* symbol no equation relates to the first), and reads
as blocked on a library gap that does not exist.

Two rules **[Otto]**, two the fourth and fifth instances added, and a fifth
the sixth did:

1. **If a call mints a symbol, its defining axiom belongs on the declaration's
   translation, not on the call's local `Site`.**
2. **When a builder returns a struct, check every `pub` field has a consumer.**
3. **A decline is the worst place to drop evidence.** Instances 1–3 were on
   success paths; the fifth was on a decline, which is strictly worse — the
   decline is precisely the moment someone will later want to know what the
   walk found. `zoneb::ensure` now stores the walk *before* it branches, so the
   retention is the same whether the route goes on to build or not, and the
   test that pins it needed a one-line change when the route started building.
4. **"`derived/` owes X" is worth one check against "X exists and its input was
   discarded" before it is sized.** `TruncRecursor` was built and tested for a
   month and could not be *called*, because its `tc` argument no longer existed
   anywhere by the time the eliminator was asked for. That row was filed as a
   library gap and was wiring.

**The sixth instance is at a new position and it is the one currently costing
most.** The five above are values dropped by a *call*; this one is dropped by a
**λ-nest bottom**, which is worse in a specific way. `rec_dep::dep_bottom`
derives `pre` — `⊢ COD(⟦C⟧,T) ∧ DEP(⟦C⟧,⟦S⃗⟧)` at the nest's own binders,
Γ-carrying — spends it on the typing, and returns. It also mints the
abbreviation `ax : ∀x⃗. sym(x⃗) = app(drec,⟦t⟧)` and drops that too. Both are
exactly what a *use site* needs in order to fire `DepRecursor::iota`, and
neither survives, so `whnf` reads as blocked on an ι theorem that has been in
the store the whole time. §8 is the route out.

A nest bottom is the sharpest form of the pattern because the value's `Γ` is the
nest's own scope assumptions: it cannot simply be stored, it has to be
discharged *through the closes* (`Closed::discharge`, innermost first — the move
`minor_ix::domain_swap` makes for the same reason). So **rule 5**: when a nest
bottom derives a fact about its own binders that a later consumer will want at
*other* terms, the thing to keep is the discharged, generalised form
`⊢ ∀x⃗. (mems → φ)`, and the place to decide that is while the scopes are open.

**The sixth instance is closed, and rule 5 turned out to be half right.** Two
values were dropped and they wanted *opposite* treatments, which is worth
knowing before the seventh:

* **`ax`, the abbreviation, is a theorem and had to be stored.** It is
  `⊢ ∀p⃗ C S⃗ t. sym(…) = app(drec, t)` — already generalised over the nest's own
  binders, hypothesis-free, and re-minting gives a *second* symbol no equation
  relates to the first. It is now `interp::DepElim`, keyed by the **recursor**
  (`u₁` is the recursor's, not the declaration's), with a dump section.
* **`PRE` is not a theorem to store, it is a *derivation* to share.** Its `Γ` is
  whoever's binders are open, and at a use site those are not the nest's at all
  — the minors are arbitrary terms. What it needed was to be a function
  (`rec_dep::pre_at`) taking terms and memberships. Rule 5 would have had me
  discharge and generalise it through the closes; that would have been real work
  and would have produced a theorem about the wrong things.

The test for which one you have: **does the consumer want it at the same terms?**
`ax`'s consumer wants `sym` at other arguments, which `inst_all` gives. `PRE`'s
consumer wants a different `C` and `S⃗` entirely, and no amount of generalising
over the nest's binders reaches those, because the nest's binders were never the
quantifier — `DepRecursor` states `PRE` at *its own* free variables and the nest
had already instantiated them.

`zoneb::IndexAx` and `class_s_ix::of` are the counter-examples that prove the
rule works: both were stored *ahead* of their consumers with an
`#[allow(dead_code)]` and a comment saying so, and both consumers needed them in
the next commit.

---

## 3. The worktree hazard **[Otto]**

`cargo` builds from the **working tree**. If anyone else has uncommitted work in
the crate, every number you measure is measured through it, and
`git commit --only <path>` will happily commit their file if you name it.

```sh
git worktree add --detach $W HEAD
git diff <only my files> > $W/mine.patch     # run from the main tree
git -C $W apply $W/mine.patch
cd $W && cargo build -p mini --release
for f in /path/to/repo/vendor/arena-tests/good/tutorial/*.ndjson; do
  $W/target/release/mini --verbose "$f"
done
```

Two traps inside that recipe. `cd $W` persists across a compound command, so a
later `git diff` runs in the *worktree* and produces an empty patch. And before
committing, diff each file you intend to name and confirm the lines are yours.

Addendum: when `git status` shows only your own files, measuring from the main
tree is sound and saves a build. Check, do not assume.

---

## 4. State of the code

### Built and consumed

* `minor_ix` — the indexed minor-premise transport, both clauses live. **[Otto]**
* `rec_ix_prop` / `rec_ix_dep` — `RBTree`'s indexed eliminators. **[Otto]**
* `zoneb::trunc_constructors` — class-(P) constructors, general in `np`/`kᵢ`/`mᵢ`.
* `interp::dprod_fs_bridge` — the `dprod`/`fs` bridge (§5).
* `rec_trunc` — the class-(P) eliminator, general in `mᵢ`.
* `class_s_ix` + `rec_s_ix` — class (S) at an index: carrier, former, constructor,
  eliminator. `071` derives at both σ.
* `zoneb::IndexedWalk` — the boundary walk kept across the branch, and the only
  record of the field↔index-slot correspondence.
* `class_p_ix` + `rec_trunc_ix` — class (P) at an index: carrier, former,
  constructors, eliminator. `072` derives, and `indexed-family(·)` is empty.
* `Checker::nest_iota` — `Eq.rec`'s ι, β down the interpreted nest. The one
  recursor mini does not *derive*, so the one whose reduction needs no theorem.
* `Gap::StuckRecursor` — split out of `Gap::Iota`; measured at zero and
  unreached, so `Gap::Iota` now means one shape and it always has a premise.
* `minor_ix::Fam` — the walk is shared by **three** routes now. `Clause::trunc`
  is the whole of class (P)'s difference and its three rows are one fact: a
  recursive argument of a `Prop`-valued family is a proof, so it is `•`.
* `iota_dep` — the class-(T) ι rule at a use site, over `DepRecursor::iota`.
  Four declarations, one construction, `073`–`076`. It is the first consumer of
  `rec_dep::pre_at`, `rec_dep::cx_of` and `Checker::nest_arg_mems`, all three of
  which exist so that the *nest* and the *use site* share one derivation.
* `interp::DepElim` — the eliminator nest bottom's abbreviation, kept. Keyed by
  the **recursor**, because `u₁` is the recursor's.

### Shaky, in ways a header reader would not see

* **`rec_ix_dep`'s target `T` is the rung the motive's own type inhabits**, not
  `⟦Sort u₁⟧`. If D8's `ICOV` interface ever takes the bounded form, re-read
  this. **[Otto]**
* **`minor_ix::domain_swap` must run at each binder's close**, not after the
  walk. **[Otto]**
* **`trunc_ctor_bottom` splits fields by the `Slot` mask**, and the only thing
  testing that split is `mini/tests/fixtures/prop_recursive_interleaved.ndjson`.
  Do not weaken it. **[Otto]**
* `derived::inductive::motive::cod_at_funspace` still returns `None` at every
  input and `rec_dep.rs`'s test pins it. Leave the pin. **[Otto]**
* **`rec_s_ix` reads §5.3's field↔slot map syntactically**, off the
  constructor's declared codomain, and requires each slot to be a *bare* field.
  `072`'s `id.{1} Bool b1` is the first index that is not, and that route
  declines it by name. Do not relax the check without a witness: a compound
  `eᵢₖ` is not invertible, and the whole cancellation argument rests on it.
  **`class_p_ix`/`rec_trunc_ix` need no such check and that is not an
  inconsistency**: a small eliminator never inverts an index, which is what
  makes `072` class (P) in the first place. The two routes differ on exactly the
  property the trichotomy splits on.
* **`minor_ix::Clause::binds` is the level-binding policy and it is not a
  count.** It was one (`l < nvars`) and that was wrong at an interleaved mask;
  see §7.4. If a fourth route arrives, state its policy there rather than
  reintroducing an arithmetic that is right at three shapes out of four.

---

## 5. The binder-congruence row, and the one design call worth re-reading

937 of 988 gapped conversions were one shape: `⟦Π x:A. B⟧` classified as a
dependent product on one side and a function space on the other. **Both
classifications were right.** `dep = has_bvar(body, 0)` is syntactic and
β-unstable, and the repair is a bridge (`derived::ext::dprod_const_fibre_n`),
not a reclassification.

Vera scoped it and recommended normalising the orientation *before* the scope
opens, as `checker/src/tg.rs` does. **I overruled that and it was right**, for a
reason worth keeping: swapping the sides earlier reorders `assert_def_eq`'s
recursion and opens the scope on the other domain, and `binder_cong`'s own first
comment is that acceptance runs "first, and unconditionally: the certificate
must never be able to change a verdict." **Reordering acceptance to make a
certificate easier is exactly what that forbids.** The mirror is handled inside
`apply` instead; the family is re-openable at a fresh variable with `ax_inst`,
and `gen_checked`'s side condition holds *because* the variable is fresh.

The general form: when a scoping note proposes moving work across the acceptance
boundary, the boundary wins.

---

## 6. Where the corpus stands, and how to count it

*(Rewritten four times. `fd42fb9` read 160/218 with an `indexed-family` row,
which `072` closed; `c425ac5` read 161/218 with an `iota(Eq.rec)` row, which the
equality clause closed; `014af6f` read **162/218**, 56 waiting over 19 keys, 75
gapped conversions and 29 exports stopping, with the ι row at 5 pairs / 5 keys /
**2 constructions**. Construction 2 landed and closed four of the five keys at
once.)*

At `7d30266+`, `good/tutorial`: **166 of 218 pairs certified**, 52 waiting, **37**
gapped conversions, **25** of 89 exports stopping under `--block`.

The 52 waiting pairs, and **say which unit you mean** — this went wrong three
times, twice in one week. Counted off `tutorial_evidence_ledger`'s own printed
rows, which are the keys:

| family | pairs | keys | exports | constructions |
| --- | ---: | ---: | ---: | ---: |
| `proj` | 24 | 5 | 8 | **1** |
| `no-interp(Quot*)`, `Nat` | 16 | 5 | 8 | 2 |
| `fun-typed-rec-arg` | 7 | 2 | 4 | 1 |
| `iota(·.rec)` | **1** | **1** | 1 | **1** |
| `unit-like(PUnit)` | 2 | 1 | 2 | 1 |
| `fun-eta` | 2 | 1 | 2 | 1 |

52 pairs over **15 keys** in **6 families**. The `proj`, `no-interp` and
`fun-typed-rec-arg` columns were **not** re-measured and are carried forward.

**The ι row is one pair, one key, one export and one construction, and every
one of those numbers moved by a different amount.** It was 5/5/5/2. One
construction (`mini/src/iota_dep.rs`) closed four pairs, four keys and four
exports; what is left is construction 3, `RBTree`. This is the clearest instance
yet of why the unit has to be named: "the ι row halved" is true of the
constructions and false of everything else, and "the ι row is nearly gone" is
true of the pairs and says nothing about the work.

**`derived/` still owes the ι row nothing.** `IndexedDepRecursor::iota` landed
at `211c46e` and is stored and unread, exactly as `DepRecursor::iota` was.

**Count keys for the ledger, families for the worklist, exports for the
schedule, and constructions for the estimate** — and name which. `proj` is one
family, five keys, eight exports and *one* construction; `iota` was one family,
six keys, six exports and *two* constructions, and closing one of the two took
four of the six keys with it. A sentence that does not say which number it means
has been wrong every time it has been used to size anything.

Three claims of the form "the last X row" have been made and all three were
false. The habits that produce them: reading a `sort -rn` and taking the head
for the length, and rolling `Scope`/`Library`/`Threading` into one sentence. The
narrow true statements at this measurement are: `iota(RBTree.rec)` is the only
remaining **threading** row of any shape, and `072` is the last
**`indexed-family(·)`** row — the fourth and last of the four distinct problems
that one label covered.

### A corpus fact worth relying on

**The declaration that η-expands its eliminator is the one that reaches ι.**
`069`, `070` and `071` each closed with *no successor row* — their exports are
`def f := T.rec` at a bare constant, so no use site ever asks for a reduction.
`072` is the same shape and did the same. The ι count moves only for
`073`–`077` and `094`, which is exactly the six.

### The ι census over-stated the demand by thirteen, and now does not

Instrumented over all 91 exports with `iota_dep` wired — the same three-site
split Vera made, re-measured:

| site | mints | of which `cur_tm = Some` |
|---|---:|---:|
| K-rule (`kernel.rs:704`) | 1 | **0** |
| constructor match (`kernel.rs:778`) | 71 | **5** |
| stuck (`kernel.rs:826`) | 0 | 0 |

**67 of the 72 carry no interpretation at all**, which means the `whnf` that
reached them is acceptance-only and is not asking for a computation rule. The
K-rule branch had made that argument and downgraded to `Gap::NoEndpoint`; the
constructor-match branch three lines below had not, and so labelled 67
non-demands `iota(·.rec)`. It does now. `Gap::Iota` is minted **5 times
corpus-wide**, all `RBTree.rec` in `077`, which is construction 3's whole
population and the number to size it against.

Nothing in the ledger or the conversion census moved when that changed, which is
the check: those 67 were never anyone's blocking reason and never had both
endpoints, so they were pure census inflation. *Read a zero row twice — and read
a large row twice as well.*

---

## 7. `072_sortElimProp2Rec` — closed, and the four things it taught

*(Rewritten at `c425ac5`. The prior revision, at `9bb19c9`, scoped the four
pieces and ordered them by risk: the carrier "unsized, not obviously small",
the constructor "a module, not a parameter", the recursor `derived`'s, and the
δ-redex measured clean. Three of the four readings held; the risk ordering did
not.)*

`mini/src/class_p_ix.rs` is the carrier, the type former and the constructors;
`mini/src/rec_trunc_ix.rs` the eliminator over Isla's `IndexedTruncRecursor`
(`c0519af`). The pair derives, `constEv` 160 → 161, and the label is empty.

**1. The carrier was the *smallest* piece, not the largest.** The §5.2 indexed
chain — `Inductive::build` → `IndexedInductive::build` — reads no level
anywhere; the level enters only at `IndexedUniverse`, which class (P) skips
because `TruncCarrier::in_u0` is unconditional. So what was missing at a
`Prop`-resultant declaration was a *caller*, not a derivation. The general form
is worth keeping: **"no route reaches this shape" and "this shape needs new
work" are different claims**, and reading which constructions consult the level
told them apart in one pass. That is a static read, and §1's rule predicts it
would hold.

**2. The boundary walk retained across the old decline was the whole input.**
`08c91ea` kept it *on the decline path* specifically so that a later build would
not have to re-mint; §2's fifth instance paid for itself here exactly as
predicted, and no symbol was minted twice.

**3. The δ-redex is real, was correctly measured, and is at a different pair
from where every reading put it.** Wren measured the conversion clean and
unconditional. The natural next step — that the two motive spellings meet inside
the minor walk — is wrong: the eliminator reads its minor off
`SortElimProp2.rec`'s **own** exported type, which is the `id.{1} Bool b1`
spelling, the same one `spec_of` abbreviated. The two spellings meet at the
*alias* pair, `sortElimProp2Rec := SortElimProp2.rec`, where `assert_def_eq`
discharges them. Nothing was wired for it. **A conversion's placement is a
dynamic fact even when its certificate is a static one**, and this is a third
instance of §1's split rather than an exception to it.

**4. The one real defect was invisible to the corpus, and the corner walk found
it in one command.** `minor_ix` generalised a transported minor's `∀y⃗` prefix
over `wvs[..nvars]` — **a prefix of the levels**. That is right at both
class-(T) routes and at every mask that is plains-then-recs, and at an
interleaved mask (`Plain, Rec, Plain, Rec`) it binds the *recursive* binder and
leaves the second plain field free. `072` has `recs = 0`; `Nat.le`'s mask is
`Plain, Rec`, which is both orders at once. `class_p_ix::tests::cells`' `Pe` is
the only declaration in the repository that can see it, and Isla found the same
hole one layer down on the same day — she added an interleaved fixture to
`derived` because her `minor_atoms` ordering claim had no witness either.

**The rule that generalises: when two orderings coincide at every witness you
have, the claim that you read the right one is untested, and the shortest
counter-shape is cheap to synthesise.** Two fields cannot distinguish an
interleave; four can. It is `MEMORY`'s "two atoms cannot distinguish" at a
different arity, and it has now been paid for at two layers of one seam.

### What class (P) at an index still declines

* **a resultant sort above `Prop`** — `class_p_ix::ABOVE_PROP`, the same refusal
  `build_trunc` makes at `ni = 0` and with the same replacement scheduled
  (`TruncCarrier::in_un`). No `good/` file can exercise it.
* nothing else. Recursive constructors and recursive minors are **built**, not
  declined: `TruncCtor::trunc_mem` and `Clause::trunc` are general in `mᵢ`, and
  the four `(kᵢ, mᵢ)` corners plus `Pe` cover them synthetically. That is the
  other half of `trunc_rec.rs`'s "Scope: non-indexed only" flag, which the
  corpus cannot witness — `Nat.le`, `Nat.le.below` and `List.Mem` are prelude
  and `grind-ring-5`, not tutorials — so **a passing corpus run is not evidence
  for it** and the tests say so.

## 8. `073_boolRecEqns` — the ι row, and where construction 2 stops

`SCOPING.md` §8 is Vera's scope: six keys, four constructions. Two are landed
(`014af6f`), one is `derived`'s and has landed there (`211c46e`), and **one is
open and is the whole content of the blocker**. What follows is the route, in
the detail it takes to start.

### What is done, and the one thing worth carrying from it

* **`Eq.rec` was a §6.2 clause and it is smaller than the scope.**
  `thesis.txt:2124` *interprets* the equality recursor, and
  `recursor::eq_bottom` already returns **the minor term itself** as the nest's
  bottom. So the ι certificate is neither `eq_refl` nor `Props::eq_sound`: it is
  **β down the stored nest**, which the interpretation already supports
  (`Checker::nest_iota`). `eq_sound` is spent once, where `⟦Eq.rec⟧` is built,
  which is exactly why the clause has no side condition and **covers the K-rule
  for free**.
* **Site 3 was never an ι rule** — `Gap::StuckRecursor`, measured at zero mints
  over all 91 exports, and *unreached* rather than solved because the branch
  mints unconditionally when its guard holds.
* **The mint-site split**, instrumented: K-rule **0** ι (one visit, an
  acceptance-only `whnf` with no interpretation tracked, now `NoEndpoint`);
  constructor match **112**; stuck **0**. Vera's "2 at the K-rule" was one real
  demand and one census artefact. *(Re-measured with `iota_dep` wired: 72 total,
  **5** of them real, all `RBTree.rec`. §6 has the table and what changed.)*

### The trap that will catch the next person — and construction 2 did not meet it

*(Kai's, and it is right about `step!`. Its last sentence is rewritten; the prior
revision is at `7d30266`, where it read "Construction 2 ends in the same kind of
chain and will meet it again.")*

**`whnf`'s `step!` lifts each leg over the arguments still on the stack.** A leg
is about the head applied to **one more argument**, not about the whole spine,
so a sequence of β steps down a stored nest emitted *as legs* must be **one
`step!` per level, with `stack_tms.remove(0)` before each** — exactly what the
ordinary `Expr::Lam` case does. Composing them into a single equation first and
`step!`-ing that once fails with `ConvCompose`, because leg *j*'s left-hand side
is `app(headⱼ, aⱼ)` and the accumulator's right-hand side is `headⱼ`.

**The way out is not to produce per-argument legs at all.**
`Interp::beta_spine` walks the same nest and does the `congr` lifting
*internally*, returning one equation about the whole applied spine. So
construction 2 removes `major_pos + 1` entries from `stack_tms` **first** and
emits exactly **one** `step!` carrying the entire four-step composite. The trap
is real and it is `Checker::nest_iota`'s, whose contract is per-argument legs
because the K-rule branch wanted them; `iota_dep` never holds one.

The general form, because this is the second time a hazard has been inherited
along with the shape that causes it: *a trap in a helper is a fact about that
helper, not about the problem.* Before routing around one, check whether a
sibling exists that cannot produce the bad shape.

### Construction 2 — `Bool`, `Prod`, `N`, `List`: one theorem, four declarations

`DepRecursor::iota[i]` is **stored and unread**, in `IndApparatus::deprecs`
under the very key the gap names (`--dump-only=Bool` prints `ι 0`, `ι 1`,
`gen ι 0`, `gen ι 1`), and `rec_dep.rs`/`recursor.rs`/`rec_ix_dep.rs` contain no
occurrence of the string `iota`.

```text
⊢ PRE → ∀y⃗ ∀t⃗. ( Hᵢ → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ app(drec,t⃗) )
```

**`cur_tm = None` is the symptom; `PRE` is the reason.** `PRE = COD(C,T) ∧
DEP(C,S⃗)` is a fact about *the use site's own minors*, which are arbitrary
terms, and `rec_dep::dep_bottom` derives it at the **eliminator nest's** binders
and drops it (§2's sixth instance). So what a reduction lacks is not the
theorem. It is `PRE` at other terms.

**The good news, and it is most of a first day.** `rec_dep`'s two premise
builders are already parameterised over exactly what a use site can produce:

```text
cod_at_rung(ip, site, cx)          -> ⊢ COD(⟦C⟧, ⟦Sort u₁⟧)
minor_at(ip, site, cx, at, i, ...) -> ⊢ DEPᵢ(⟦C⟧, ⟦Sᵢ⟧)
```

and **`Cx` is terms and memberships, not nest positions**: `ps`, `c_tm`,
`s_tms`/`s_mems`, `t_tm`/`t_in_w`, `v_set`, `w_term`, `c_in_fs`, `psub`, `ind`.
Every one of those is obtainable at a use site by `infer_type` on the Lean
arguments `whnf` already holds in `stack` — which is precisely what
`beta_premise` does for **one** argument, and it is the function to read first.
`minor_at` opens its own private `Scopes` rather than the checker's telescope,
so it does not care where it is called from. Neither builder needs a λ-nest.

The four-step composite at the fire point, all of whose pieces exist:

| step | from | to | how |
|---|---|---|---|
| 1 | `app(…app(⟦T.rec⟧,⟦p⃗⟧)…,⟦major⟧)` | `app(drec, ⟦major⟧)` | `beta_spine`, then `ax` — **and `ax` is the other thing `dep_bottom` drops** |
| 2 | `⟦major⟧` | `ctorᵢ(⟦y⃗⟧,⟦t⃗⟧)` | β down `⟦T.ctorᵢ⟧`'s nest, then `Translated::ctor_abbrev` |
| 3 | `app(drec, ctorᵢ(…))` | `Sᵢ⟪⟦y⃗⟧,⟦t⃗⟧⟫ app(drec,⟦t⃗⟧)` | `dr.iota[i]`, `gen_all_checked` over `params ++ motive ++ minors ++ target` then `inst_all`, `mp` with `PRE`, `mp` with `Hᵢ` |
| 4 | that | `⟦rhs_lean⟧` | the Lean rhs is `Sᵢ y⃗ t⃗ (T.rec p⃗ C S⃗ t₀) …`, so its interpretation is an `app` spine; the recursive calls are step 1 again at `tⱼ` |

`gen_all_checked` at step 3 is the same move `dep_bottom` makes on `dr.typing`
(`rec_dep.rs`, "the typing obligation, instantiated and discharged") — copy that
five-line block; `iota[i]` is stated at the same free variables as `typing`.

**Size it against `rec_trunc_ix`, not against a new derivation.** It is a
use-site `Cx` plus that composite, and nothing in it is a theorem `derived/`
does not have. `whnf` is not a λ-nest, so the one thing genuinely new is
acquiring the argument memberships — and `beta_premise` is that, per argument,
already written.

**Two things to check early, because both are cheap and both could resize it.**
Whether step 2's major needs a *conversion* first: `whnf` reduces the major with
the acceptance-only `self.whnf(&major)?`, which threads no certificate, so a
major that is not already a constructor application needs one and `073`'s
(`Bool.false`, `Bool.true`) do not. And whether `minor_at`'s `prop` flag and the
`Slot` mask behave at `N`/`List` — those are the recursive members and
`Bool`/`Prod` cannot see them.

### Construction 2 — **landed**, and where the route above did not survive

`mini/src/iota_dep.rs`. `constEv` 162 → **166**, four pairs and four keys, the
four exports `073`–`076`. Everything above held except where marked. Three
corrections, in descending order of what they would have cost:

1. **The composite is one leg, not four `step!`s** — see the rewritten trap
   section above. `beta_spine` is the instrument; `nest_iota` is not.
2. **`Cx` did not move, and neither did `minor_at` or `cod_at_rung`.** The route
   said they were parameterised over terms and memberships and they are,
   exactly. What was needed was twelve lines producing `⊢ ⟦aᵢ⟧ ∈ domᵢ` for a
   Lean argument — `Checker::nest_arg_mems`, which is `beta_premise` in a loop,
   because a nest binder's *scope assumption* and that membership are the same
   statement. `rec_dep`'s only structural change is `build` split into `cx_of`
   and `pre_at`.
3. **Both early checks came out "no work", and both were worth making.** The
   major needs no conversion at any of the four; the guard is
   `major2 == major`, and a major that had to reduce declines by name.
   `minor_at`'s `prop` flag and the `Slot` mask behave at `N`/`List` unchanged —
   the whole `mᵢ > 0` cost is **step 4**, which the route did predict: `⟦rhs⟧`
   spells each recursive result `T.rec p⃗ C S⃗ tⱼ`, so it is step 1 again at
   `tⱼ`, reversed, under `mᵢ` congruences over `app`. Fifteen lines.

One thing the route did not mention, and it will matter one table along:
**`ctorᵢ(y⃗,t⃗)` does not depend on the parameters.** `Inductive::ctor_term`
takes only the fields, so `Translated::ctor_abbrev[i]` is quantified over fields
alone — the parameters live in the constructor's *types*, not in its term. A use
site whose major carries parameters that are not the eliminator's own is a
conversion nobody holds, so it declines by name rather than transporting across
a different carrier. No corpus member exercises that decline.

### Construction 3 — `RBTree`, and it is now wiring too

`IndexedDepRecursor::iota` landed in `derived` at `211c46e`. Measured, its
arrival does **not** disturb `rec_ix_dep`: `077` still reports
`iota(RBTree.rec)` rather than a recursor gap, so `over_family` still returns
`Some` at that declaration. It is the same shape as construction 2 one
table along, and `RBTree.red`/`.black` are **interleaved masks in the corpus**,
so `Sᵢ⟪y⃗,t⃗⟫`'s declared field order is exercised for real — see §7.4 for what
an interleave caught one layer down.

**It is now the whole of the ledger's threading axis**: 1 pair, 1 key, 1 export,
**5** ι mints corpus-wide and 14 gapped conversions, all in `077`. Read
`mini/src/iota_dep.rs` beside `mini/src/rec_ix_dep.rs` — the second is the
indexed analogue of `rec_dep`, and what construction 3 needs is the indexed
analogue of the first: the same four steps over `IndexedDepRecursor`'s
vocabulary (`irec = grec(p⃗, gmin⃗, T)`, `PRE = ICOD ∧ IDEP`), with the index
vector dead at a constructor (`INDEXED-DESIGN` §5.1). **Whether `rec_ix_dep`
splits into `cx_of`/`pre_at` as cleanly as `rec_dep` did is the first thing to
check, and it is a read rather than a measurement** — which §1 says is the kind
that holds.

---

## 9. Instruments

* **`mini --dump-theorems`** (`mini/src/dump.rs`). Prints every stored theorem's
  real conclusion with declines in place. `--dump-only` is a
  **Lean-name-component prefix**, so `--dump-only=List` shows `List`, `List.rec`
  and `List.cons`; it was exact, which made it useless for the question people
  actually ask. It now has sections for the class-(P) translation and for the
  retained indexed walk, both of which were invisible for as long as their
  stores had no reader — *the instrument built to find storeless evidence could
  not see the stores whose readers were missing.* Keep that property: a new
  store gets a dump section in the same commit.
* **`--block`** stops at the first `(declaration, σ)` it cannot discharge and
  prints the obligation, what is in hand, and the mint sites.
  `blocker::show_term` still elides a nested argument as `…` —
  `f116(…, …, ⟦N.{}⟧)` — and the elided position is sometimes exactly the one
  under test. Raise the depth if you are in that file.
* **A frontier test that flips.** Write the decline down *with the reason you
  believe* and say in the header what would make it flip. Two did this week and
  both flipped within a day, each telling its author something the count could
  not. When one flips, rewrite the rationale **in place with a marker to the
  prior revision** rather than appending — Quinn's convention, and it is what
  keeps a reversal findable instead of buried under its own correction.
* **`SCOPING.md`** (Tara, Vera) — corpus facts written nowhere else, including
  that `Quot` and `Inductive` declarations bear **no pairs**. Read it before
  sizing anything by its row count.

---

## 10. Why Kai handed off here — and what is true now

*(Kai's, at `7d30266`, kept because the protocol it describes is the point.
Construction 2 has since landed; the unit test he names as abandoned is
`iota_dep::tests`, written, and the corpus ratchet he left is still there beside
it because the two assert different things.)*

`073` is the blocker and construction 2 is its whole content — one construction,
four declarations, nothing owed by `derived/`. It is a clean thing to start on
and §8 is the route.

The reason it is not mine is the one this project has a protocol for. I closed
`072` and two of the ι row's four constructions, and I finished the last commit
by **abandoning a unit test mid-write** because I could not afford the de Bruijn
arithmetic — the pin is a corpus ratchet by name instead, which is adequate but
is not what I would have written with room. Construction 2's first day is the
`Cx` above, and I would be starting it with less context than that day needs.

Accuracy held throughout: the wrong calls I made were caught by the run in the
same commit (the δ-redex reading in `rec_trunc_ix`'s header, the composed β
chain), and none reached a measurement. What slipped was room to work, not
judgement — which is the signal §0 of this file was written about, and the
cheapest moment to act on it is before the next construction rather than inside
it.

What a successor starts with: this file — §8 first, then §0 and §2 — plus
`SCOPING.md` §8 and `MINI-DESIGN.md` §0.5. `class_p_ix.rs`, `rec_trunc_ix.rs`
and `minor_ix.rs` are the three most recent modules and the closest models;
`rec_dep.rs`'s `dep_bottom` is the twenty lines to read before anything.

**Addendum, after construction 2.** That reading list was right and the twenty
lines were the right twenty. The one thing to add: read `iota_dep.rs`'s header
*table* before its code, and `rec_dep.rs`'s `pre_at` before either — the whole
construction is "which of these two functions is the nest's and which is
shared", and every line of the answer is in the split between `cx_of`/`pre_at`
and `dep_bottom`. The next construction is the same question at
`rec_ix_dep.rs`.
