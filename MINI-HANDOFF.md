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

### Its boundary, which cost a wrong paragraph to find

**A corner walk says which cell differs. It does not say the cell holds one
thing.**

`086_projProp3` against `084_projProp1` is a two-cell walk and it localised
perfectly: everything `086` used beyond `P₁` and `P₂` was already exercised by
`084`, and `P₂` is a `Prop` field exactly like `P₀`, so the difference was
*provably* `P₁`. Then I explained `P₁` — and the explanation was wrong, and
underneath it was a **second, unrelated** blocker (the field's type could not be
read at all, because projecting that field is illegal) which was invisible until
the first was fixed.

> **Two blockers in series look exactly like one blocker plus a bad guess about
> what is behind it.**

The failing cell is a *conjunction* of everything that cell adds, and a walk
narrows the conjunction without splitting it. So when the localisation is sharp
and the explanation still needs a guess, **the guess is the part to go and
measure** — it is not protected by the walk's rigour, and it inherits none of
it. `--dump-only=PUnit` settled mine in one command after a paragraph of
plausible reasoning about W-encodings had already been committed.

This does not weaken §0; it says where §0 stops. The walk is still the cheapest
way to find *which* cell, and it remains the only cheap thing that sees the
interaction answer. What it cannot do is tell you when to stop looking.

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
| `⟦proj x⟧ = •` comes from the λ clause, not the `Proj` arm (Vera) | static | **held**, exactly |
| …so `And`/`PProd`/`PSigma` are one class (Vera) | static | **wrong** — §1's fifth category; the mechanism is wider than the conclusion |
| `⟦PUnit.{1}⟧ ⊆ 1` is false because a W-unit's inhabitant is a pair (mine) | static | **wrong** — it never reaches the W-carrier; the store said so |
| `whnf`'s `Expr::Proj` arm must keep `cur` a subterm of its input (mine) | static | **held** — and it is what decides `proj`'s route |

A **fifth** category, and it is the one that looks most like careful work.
Vera's `proj` scope identified a mechanism *exactly right* —
`⟦And.left⟧ = •` comes from the **λ clause's proof branch**, not from
`infer_type`'s `Expr::Proj` arm, which returns `tm: None` unconditionally with
no `is_prop` test — and then, one paragraph later, used it as a
**classification**: `And`, `PProd.{0,0}` and `PSigma.{0,0}` all project to `•`,
so all three are class (S). They all do project to `•`, and two of the three are
class (T): the branch fires because the projection's *type* is a `Prop`, which
is equally true of a `Prop` field in a `Type`-resultant structure.

> **A correctly-identified mechanism can have wider scope than the conclusion
> drawn from it.**

That is not a census behind a blocker (§6) and not a mechanism mistaken for a
diagnosis (below) — the mechanism *was* the diagnosis and it was right. What was
wrong was the quantifier over it. It is the hardest of the five to catch,
because every step is sound and the reasoning is visibly better than average;
the check is to ask **what else satisfies this mechanism**, which for a `•` is
"every proof, and a proof is decided by its type, not by its structure's class".

My own instance, same round: I explained a decline by guessing which
*translation* `PUnit.{1}` takes — reasoning about W-encoded units when it
reaches `class_s` and `⊢ ⟦PUnit.{1}⟧ ∈ ⟦Sort 0⟧` was in the store. Same shape as
the rule §9 already states: the instrument was available and reasoning was
cheaper to reach for.

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
* **`PRE` was better shared as a *derivation* than stored as a theorem.** Its
  `Γ` is the memberships of the binders it was derived at, so storing it means
  discharging those first — and `Closed::discharge` belongs to `lam_nest`, not
  to the bottom closure that derives `PRE`. What it needed instead was to be a
  function (`rec_dep::pre_at`) taking terms and memberships, which is what it
  already almost was.

  **Rule 5 was not wrong here, it was more expensive.** *(Rewritten: at
  `1e63e56` this paragraph said discharging and generalising "would have
  produced a theorem about the wrong things", which is a claim I did not
  measure and do not believe on re-reading.)* `⊢ ∀p⃗ C S⃗. (mems → PRE)` is a
  perfectly good theorem and instantiates at a use site's own minors — the
  quantifier reaches them, because the nest's binders are exactly the variables
  `PRE` mentions. What it costs is plumbing a value out through `lam_nest`'s
  closes, which no route does today.

The discriminator, then, is not *what the consumer wants* — it is **whether the
value's `Γ` can be discharged where the value is derived.** `ax` is
hypothesis-free the moment `define_abbrev` returns, so it stores. `PRE` is not,
and the closes that would discharge it are somebody else's. That is the same
sentence §2's opening makes about nest bottoms, one level more precise, and it
predicts which of the two treatments the *seventh* instance will want.

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
* ~~`interp::dprod_fs_bridge` — the `dprod`/`fs` bridge (§5).~~ **Deleted at
  `3bf5b24`**: the `fs` clause is retired, so the bridge has no input. See §5.
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

## 5. The binder-congruence row — repaired, then removed at its source

*(The row is **gone** as of `3bf5b24`: `⟦Π⟧` has one value clause, so there are
no two spellings to bridge. The design call below stands and is why this section
is kept rather than deleted — it was right about *how* to repair a mismatch you
have, and the thing it repaired should not have existed. `SCOPING.md` §10 is the
removal, prototyped before it was made.)*

937 of 988 gapped conversions were one shape: `⟦Π x:A. B⟧` classified as a
dependent product on one side and a function space on the other. **Both
classifications were right.** `dep = has_bvar(body, 0)` is syntactic and
β-unstable, and the repair is a bridge (`derived::ext::dprod_const_fibre_n`),
not a reclassification.

> **A repair that is right and load-bearing at 937 sites is evidence about the
> clause, not only about the repair.** Two rounds later `has_bvar` turned out to
> be *blind to `Expr::Proj`* as well (§11.1), which is the same clause
> classifying one type two ways with one side simply wrong — and that is the
> instance that decided the removal. One β-instability is a bridge; two is a
> clause that should not exist.

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

At `3b8f5f8`, `good/tutorial`: **190 of 218 pairs certified**, 28 waiting, **37**
gapped conversions, **17** of 89 exports stopping under `--block`.

*(Rewritten again. At `7d30266+` this read 166/218 with 52 waiting and a `proj`
row of 24 pairs / 5 keys / 1 construction. Rows 1, 3 and 2 of `proj` closed —
`9e60a27`, `b36f6ab`/`d561d51`, `ce2bb57` — and the construction count went
1 → 4 → 1 without the family count moving, which is §6's whole point about
naming the unit.)*

The 28 waiting pairs, and **say which unit you mean** — this went wrong three
times, twice in one week. Counted off `tutorial_evidence_ledger`'s own printed
rows, which are the keys:

| family | pairs | keys | exports | constructions |
| --- | ---: | ---: | ---: | ---: |
| `no-interp(Quot*)`, `Nat` | 16 | 5 | 8 | 2 |
| `fun-typed-rec-arg` | 7 | 2 | 4 | 1 |
| `iota(·.rec)` | **1** | **1** | 1 | **1** |
| `unit-like(PUnit)` | 2 | 1 | 2 | 1 |
| `fun-eta` | 2 | 1 | 2 | 1 |

28 pairs over **10 keys** in **5 families**. The `no-interp` and
`fun-typed-rec-arg` columns were **not** re-measured and are carried forward.

**`proj` is off this table entirely** — 24 pairs, four rows, four carriers, four
constructions, and it was scoped as *one*. Two things about the count are worth
keeping. The `PProd`/`PSigma` keys **halved before they closed**, which no key
had done before: at `ce2bb57` they read 2 each, because one σ owed a certificate
and the other owed a term. And the conversion census went **37 → 53 → 37**: the
sixteen pairs that stopped at the term reached three conversion rows nobody had
run, and all three then closed. *A conversion census counts what the walk got
to, so a rising count after a typing lands is the expected reading and not a
regression* — the pin says so beside the total.

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
**5** ι mints corpus-wide and 14 gapped conversions, all in `077`. The 5 are at
`RBTree.rec.{1,0}`, the *value* recursor reached through `RBTree.id`'s δ; the
`{0,0}` spine in the same file interprets to `•`, so `split_app` answers `None`
and no ι question is asked there.

#### The first thing to check, checked: `rec_ix_dep` does **not** split like `rec_dep`

The route above ends "whether `rec_ix_dep` splits into `cx_of`/`pre_at` as
cleanly as `rec_dep` did is the first thing to check, and it is a read". It is,
and **the answer is no.** The obstacle is not in `rec_ix_dep` at all — it is one
level down, in `minor_ix::transport`, and it is exactly two lines:

```text
minor_ix.rs:362   let idx = site.depth - 1 - (site.np + 1 + i);
minor_ix.rs:363   let mty = c.local_type(idx)?;          // the minor's Lean type
minor_ix.rs:509   let d = site.depth + l - np;           // where the parameters are pinned
minor_ix.rs:511   zoneb::ind_spine(&site.ind, &dom_e, np, ni, d)?
```

`rec_dep::minor_at` opens a **private `Scopes`** and never looks at a Lean type,
so it is use-site-ready by construction. `minor_ix::transport` opens **checker**
binders and reads the minor's type off the telescope — and its own header says
why it must: at `ni > 0` the recursive field's atom is
`rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))`, the index expressions live inside the minor's Lean
type, and `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` exists nowhere else. **That reason is right and the
nest-shaped implementation of it is incidental**, which is the same distinction
the `step!` trap turned on one section above.

Both lines generalise, and neither needs a new theorem:

* **the minor's type** becomes a parameter. At a use site it is the recursor's
  declared minor binder with the actual arguments substituted, which is a
  four-line `Expr::Forall` peel over `rec_ty` (there is no such helper yet;
  `Checker::nest_arg_mems` walks the same binders for the memberships).
* **`d`** is only ever used by `zoneb::ind_spine` to check that the recursive
  field's type applies the declaration to *the parameters* — `args[..np]` are
  required to be `BVar(d + np - 1 - i)`. At a use site the parameters are
  arbitrary expressions, so the honest generalisation is `ind_spine_at(ind, e,
  params: &[E], ni)` taking the expressions to match, with today's `ind_spine`
  a wrapper that builds `bvars(np, d)`. Ten callers, none of which change.
  Inside the walk the caller's expressions need `crate::expr::shift(·, l, 0)`,
  because level `l` sits under `l` open binders — that is the de Bruijn step
  and it is the one part of this nobody has written.

So construction 3 is **construction 2's four steps plus one generalisation of a
module three routes share**, and the second half is the risk: `minor_ix` is the
file §4 lists twice under "shaky in ways a header reader would not see"
(`domain_swap` at each close, `Clause::binds` a policy and not a count). Size it
at more than construction 2, not less, and do the generalisation as its own
commit with the three existing callers unchanged and measured.

Three further differences from construction 2, all in the statement:

* **`Hᵢ` is in *declared* field order** and the `∀y⃗∀t⃗` prefix is
  plains-then-recs. `IndexedDepRecursor::iota_atoms` and `::iota_vars` are both
  exported *precisely because the two differ* — read the association, do not
  reconstruct it. `RBTree.red` is `Plain, Rec, Plain, Rec` and `.black` is
  `Plain, Plain, Plain, Rec, Plain, Rec`, both `mᵢ = 2`, and `black`'s two
  children sit at **different index vectors** (`RBTree α c₁ n` and
  `RBTree α c₂ n`), so a mispairing is visible rather than masked.
* **the recursive atom is `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` and not `tⱼ ∈ W`** — one carrier
  equation per child, at the child's own indices, where construction 2 had one
  `w_eq` for all of them.
* **step 4's reverse chain carries index arguments.** `⟦rhs⟧` spells each
  recursive result `T.rec p⃗ C S⃗ d⃗ᵢⱼ tⱼ`, so the β chain back down the nest is
  over `np + 1 + n + ni + 1` arguments with the `ni` slots differing per child.

`IndexedDepRecursor::iota` is stored and unread, and **the dump said the
opposite until this commit** — see §9.

---

## 11. `proj` — closed, four rows, and it was scoped as one construction

*(At `3b8f5f8`: `constEv` **190** of 218, `library-gap` **4**, 17 exports
stopping, and every `waiting:proj(·)` row gone. Stamp the commit beside any
figure quoted here.)*

| # | carrier | declarations | pairs | closed by |
|---|---|---|---:|---|
| 1 | (S) | `And` | 2 | `LePropFields`, `9e60a27` |
| 2 | (T), `Prop` fields | `PProd.{0,0}`, `PSigma.{0,0}` | 4 | `DeclFields`, `ce2bb57` |
| 3 | (P) | `PropStructure` | 2 | `TruncFields`, `b36f6ab`/`d561d51` |
| 4 | (T), data fields | `Prod` ×2σ, `PProd.{1,1}`, `PSigma.{1,1}` | **16** | `DeclProj`, `a63008b`–`3b8f5f8` |

**Four rows, four carriers, four `derived/` theorems, and one estimate that said
"one construction".** The estimate moved four times and every move was the same
error at a different arity: a *symptom* read as a classification. `SCOPING.md`
§9's own §10 is the rule — trust the notes for intent and measure for state — and
this row is the largest instance of it on the project.

Row 4's three findings, none of which any scope named, are §11.1.

`mini/src/proj_prop.rs`, both `Prop`-side halves. `constEv` 166 → **170**,
`library-gap` 28 → **24**, exports stopping 25 → **22**, `waiting:proj(And)`
and `waiting:proj(PropStructure)` both gone. It is a **second call site** and nothing else:
`derived::…::LePropFields` was built, tested and already consumed by
`rec_prop`, whose `inhabit` climbs exactly the ladder a projection needs. The
only new work is acquiring the ladder's major premise `• ∈ A_φ(⟦p⃗⟧)` from a
*term* rather than a nest binder — `infer_type`, the carrier equation, and
proof irrelevance when the subject is not already `•`.

### The estimate was 10 pairs over three declarations; it is 2 over one

`SCOPING.md` §9 puts `And`, `PProd.{0,0}` and `PSigma.{0,0}` in one
construction because all three project to `•`. **They do, and the `•` is not
evidence of the structure's class.** Vera identified the mechanism correctly one
paragraph earlier — the `•` comes from the **λ clause's proof branch**, not from
the `Expr::Proj` arm — and then read it as a classification. It fires because
the projection's *type* is a `Prop`, which is equally true of a `Prop` field
sitting in a `Type`-resultant structure.

Measured: this corpus's `PProd` and `PSigma` are `Prop → Prop → Type 0`. They
are in `IndApparatus::decls`, not `props`; there is no `A_φ` for `LePropFields`
to be about; and `--dump-only=PProd` shows the carrier at `⟦Sort 1⟧`. So the row
splits by **carrier class** into four:

| # | carrier | declarations | pairs | owes |
|---|---|---|---:|---|
| 1 | (S) | `And` | 2 | **done** |
| 2 | (T), `Prop` fields | `PProd.{0,0}`, `PSigma.{0,0}` | **4** | **done** — over `DeclFields`, `57b5dcd`/`ce2bb57` |
| 3 | (P) | `PropStructure` | 2 | **done** — over `TruncFields`, `386ca07` |
| 4 | (T), data fields | `Prod` ×2σ, `PProd.{1,1}`, `PSigma.{1,1}` | **16** | a term — **and a theorem**, §11.1 |

*(Row 2 was written as 8 pairs when it was first split out and it is **4**. The
σ splits it: `--dump-only=PProd` shows `⟦PProd.fst.{0,0}⟧ = •` and, at
`{1,1}`, "this declaration has a value, so `⊢ ⟦c⟧ = ⟦val⟧` was expected and is
missing" — no interpretation at all, because at `u = v = 1` the field is data
and the projection is not a proof. The same for `PSigma`. So four pairs move
from row 2 to row 4, and **the σ question answers "different" on a `proj` row**,
which is the opposite of what it answers for the eliminator: a projection is
level-generic in its *term* and not in its *class*.)*

Row 2 is new and is the one worth sizing now: `⟦projⱼ x⟧` is still `•` and the
obligation is still `⊢ • ∈ ⟦βⱼ⟧`, so it is construction 1's *statement* over a
different premise. The sketch, unbuilt and unchecked: `decl_rect` at
`φ(z) := • ∈ βⱼ(p⃗,•⃗<ⱼ)`, constant in `z`, whose single induction step is
`∀y⃗. (y⃗ ∈ β⃗ → • ∈ βⱼ)` — discharged by `yⱼ ∈ βⱼ` plus `βⱼ ⊆ 1`, the same
`subset_of_unit` the class-(S) ladder already uses. Both pieces are in mini
(`rec_dep::prop_bottom` calls `decl_rect`; `rec_prop::subset_of_unit` is the
other), so it may owe `derived/` nothing either. **That is a prediction, not a
measurement** — §1's fourth category — and the cheapest way to settle it is to
try `decl_rect` at a constant `φ` and see whether `rect_parts` gives that step.

`mini/src/proj_prop.rs`'s
`a_class_t_structure_with_prop_fields_is_declined_not_spoken_for` is row 2's
synthetic witness, so it exists in the repository independently of the corpus
and will flip when the row lands.

### Row 3 closes, and the corner walk found **two** layers, not one

`TruncFields` (Isla, `386ca07`) is row 1's ladder with the major premise
swapped, and `proj_prop`'s second branch spends it. `084` went through at once;
`086` — index 2, so `P₀ ∧ P₁ ∧ P₂` over a **data** field at index 1 — took two
further findings, and they were **stacked**:

1. **`Pⱼ = βⱼ ⊆ 1` is strictly weaker than "βⱼ is a `Prop`."** The first
   revision checked only the Lean sort, and `PUnit.{1}`'s is `Type 0`. But a
   unit-like declaration never reaches the W-carrier — it reaches `class_s` —
   and `⊢ ⟦PUnit.{1}⟧ ∈ ⟦Sort 0⟧` was in the store the whole time.
   `proj_prop::field_in_u0` is the second route: the inferred sort when it is
   `⟦Prop⟧`, otherwise the field type's **own declaration's** carrier
   membership.
2. **`086` cannot ask `infer_proj` for field 1's type at all**, because
   projecting field 1 is illegal — `085_projProp2` is in `bad/` for exactly
   that. The ladder still quantifies `P₁`, so the *type* is wanted where the
   *projection* is refused. `Checker::infer_proj_ty` reads it with the two
   guards off, and the guards stay where they are: legality is `Expr::Proj`'s
   business and this route must not widen it.

**The order is the lesson.** The corner walk localised layer 1 exactly and
*only* layer 1 — everything `086` used beyond `P₁`/`P₂` was already exercised by
`084`, so the difference was provably `P₁`. Layer 2 was invisible until layer 1
was fixed. I wrote a note at that point saying `⟦PUnit.{1}⟧ ⊆ 1` "looks false,
because `1` is `{•}` and a W-encoded unit's inhabitant is a pair"; it was
**wrong about which translation the declaration takes**, and one
`--dump-only=PUnit` settled it. So:

> **Two blockers in series look exactly like one blocker plus a bad guess about
> what is behind it.** A corner walk tells you which cell differs; it does not
> tell you the cell contains one thing. When the localisation is sharp and the
> explanation still needs a guess, the guess is the part to go and measure —
> and the instrument is usually one command, not one argument.

That is §1's "a mechanism observed at the failure point is not the reason it
fails" with the roles reversed: here the mechanism *was* a reason, and there was
a second one under it.

### Row 2 — closed, and the theorem was the simplest of the family

*(Rewritten at `ce2bb57`; the prior revision, at `d81dc6d`, is the sketch below
with "owes `derived/` one theorem" in the heading and the sketch flagged as "a
prediction, not a measurement". The prediction held on the nose: `decl_rect` at
a constant φ gives exactly that step, Isla built it as
`derived::inductive::DeclFields` at `57b5dcd`, and mini's side is a third branch
in `proj_prop` routing on `decls`. Four pairs, `constEv` 170 → 174. The one
check flagged unmade below **was made** and came out as read: `PSigma.snd.{0,0}`
derives, so `field_in_u0`'s first route — the inferred sort at `⟦Prop⟧` —
suffices at `β fst`, and the second route is not needed. The family is four
members, not three; the fourth is §11.1.)*

`LePropFields` (class S) and `TruncFields` (class P) are the same ladder over
two different major premises. Row 2 is the third member and it is **smaller
than both**, because `decl_rect` already quantifies the carrier element and no
existential fold is needed:

```text
⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → ((P₀ ∧ … ∧ Pⱼ) → (H₀ ∧ … ∧ Hⱼ)) )     [steps[j]]
        Pⱼ := βⱼ(p⃗,•⃗<ⱼ) ⊆ 1        Hⱼ := • ∈ βⱼ(p⃗,•⃗<ⱼ)
```

It is `decl_rect` at `φ(z) := (⋀P → ⋀H)` — **constant in `z`**, which is legal
(`rect_step` substitutes `ctorᵢ(y⃗)` for `zv` and a φ that ignores it is
unchanged) and is what removes the fold. The single induction step is
`∀y⃗. (⋀ⱼ yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ) → (⋀P → ⋀H))`, discharged exactly as `le_prop_fields`
discharges its own: `P₀` collapses `y₀` to `•` by `unit_eta`, one Leibniz moves
`β₁(y₀)` to `β₁(•)`, and so on up — `k(k−1)/2` Leibniz steps, which that file's
header already names as the whole cost.

Same three refusals as both siblings, and for the same reasons its headers give:
**indices, a constructor count other than one, and a recursive field.** At two
constructors the statement is false — membership pins nothing about constructor
0's fields.

Why `derived/` and not mini: it is the third member of a family whose second
member Isla's own header says "should be built beside `le_prop_fields`, not
inside it", and the ladder is ~150 lines of Hilbert plumbing that exists twice.
Mini's side is then a third branch in `proj_prop`, ~40 lines mirroring
`trunc_typing`, and the routing already keys on which store holds the
declaration — `decls` here, where rows 1 and 3 key on `props` and `truncs`.

**One check that could still resize it — made, and it came out as read:**
whether `⋀P` is dischargeable at `PSigma.{0,0}`'s second field. `β₁` is
`app(⟦β⟧, •)` after the collapse and `proj_prop::field_in_u0` needs
`⟦β⟧ • ∈ ⟦Prop⟧`; the field's Lean type is `β fst` with `β : α → Prop`, so the
inferred sort is `⟦Prop⟧` directly and the second route is not needed.
`081_PSigma.snd` at `σ = 0,0` derives, which is the measurement — the export is
`snd`, so the ladder really is climbed through `P₀` and `H₀` on the corpus and
not only in the synthetic witness.

### 11.1 Row 4 — closed, and the three things no scope named

*(Rewritten at `3b8f5f8`. The prior revision, at `8bb3915`, is the scope: it
recorded that `SCOPING.md` §9 and this section's own table both said row 4 owed
"a **term** — the only one that does", that the term was built and tested, and
that the row *also* owed `derived/` a theorem — `decl_rect` at
`φ(z) := πⱼ(z) ∈ βⱼ(p⃗, π⃗<ⱼ z)`, the fourth member of the field family, φ not
constant in `z`. **That scope held exactly.** Isla built it as
`derived::inductive::DeclProj` at `fb382db`, with η folded into the same `φ` for
one Separation, and it wanted nothing the scope did not name.)*

`mini/src/proj_data.rs`. The term is what route (b) said — every layer of a
class-(T) carrier element is a Kuratowski pair, so

```text
ctor₀(y⃗) = ⟨ ⟨∅, ⟨y₀, ⟨y₁, … ⟨y_{k-1}, •⟩…⟩⟩⟩ , ∅ ⟩
πⱼ(z)   := compⱼ(π₂(π₁ z)) = π₁(π₂ʲ(π₂(π₁ z)))
```

and `computes` — `⊢ πⱼ(ctor₀(y⃗)) = yⱼ` — is `j + 3` instantiations of
`Proj::fst`/`Proj::snd`, unconditional. `π₂(π₁ z)` and **not** `π₁(π₁ z)`: the
tag is `Inj₀(tuple)`, so there is one unwrapping between the outer pair's first
component and the telescope, and no declaration with fewer than three fields
distinguishes the two.

Three things the route did not mention, in descending order of what they cost.

**1. The term has to be built through `Interp::mk`.** `⟦projⱼ x⟧` is the
interpretation of a λ *body*, and `lam_site` splits that body around the binder:
every subterm on the path down to the bound variable must be in the `Parts` hint
table, because the kernel does not expose `Term`'s constructors for reading.
`derived`'s term-formers build with `Term::apply`, as they should, and here
*every* layer mentions the binder. `proj_data::term_recorded` mirrors `proj_of`
layer for layer and compares the result against it.

> **A term `derived` hands back is not yet a term the checker can put under a
> binder.** Nothing in the three preceding rows could see this, because all
> three return `•`, which has no structure to record. It is the first time an
> interpretation clause has produced a *composite* term at a use site, and it is
> the thing to expect again at `Quot`.

**2. `expr::has_bvar` does not descend into `Expr::Proj`, and that made one type
two.** The declared codomain `β (PSigma.fst α β self)` and `infer_proj`'s
`β (self.PSigma.0)` are the same type; `has_bvar` calls the first dependent and
the second not, so `⟦ty⟧` was a `dprod` and the λ's typing was assembled at `fs`
against it. **That is §5's row at the λ/Π boundary rather than at a conversion —
and unlike §5's, the two classifications are not both right: one is blind.**
`expr::has_bvar_in_proj` is the descending version and the port is untouched,
because `has_bvar`'s other caller is `infer_proj`'s dependency guard, which is
acceptance with four `bad/tutorial/` fixtures built around its behaviour.
Over-approximating dependency is the safe direction: `dprod_const_fibre_n`
bridges `dprod` back to `fs` and nothing bridges the other way.

**3. η fires and then hits a second blocker, and the first was real.**
`SCOPING.md` §9 predicted `105_structEta` would *move* to `Gap::StructEta`
rather than close, and flagged it as a prediction. Measured: it moved, exactly.
Spending `DeclProj::eta` then moved it again — to `proj(Prod)` — because
`structEta`'s theorem is `rfl` at `x = Prod.mk (fst x) (snd x)`, so each field
conversion δ-unfolds to a `Proj`-against-`Proj`, an arm that discharged its
subjects with `assert_is_def_eq` and threw the conversion away. Two blockers in
series, §0's boundary, and this time the first was *necessary* rather than a bad
guess — which is the distinction that section could not make from one instance.

**The probe decides and the certificate only certifies.**
`Checker::try_structure_eta` is unchanged and still uses `is_def_eq`;
`proj_data::structure_eta` runs second and its failure is a gap, never a
rejection. §5's boundary, at the one place in this row where it could have been
crossed.

**What `derived/` owed and what it did not.** Four theorems, one per carrier,
none re-derived and none of them wiring: this row is the counter-example to §2's
"`derived/` owes X is worth one check against X exists and its input was
discarded". Four times the check was made and four times the answer was that the
theorem genuinely did not exist. The one *near* miss is η, and Isla's note on it
is worth keeping: `rect.rs` assembles the same equation as a local and drops it,
but it is **not** §2's pattern — it is stated at existential witnesses under a
case analysis's own context, so surfacing it means re-running the analysis, and
the cheap place to state it is at a `φ` that mentions `z`. *Evidence that cannot
be stated where a consumer could use it is a different failure from evidence
discarded*, and the discriminator is Fen's: does the consumer want it at the same
terms?

### The general form, because this is the *fourth* `proj` estimate to move

**A `•` in the ledger names the interpretation, never the carrier.** §6.2's left
column is about the term's *type* being a `Prop`, and a declaration's class is
about its *resultant sort*. Those coincide at every class-(S) witness and come
apart at the first `Type`-resultant structure with a `Prop` field — which is
`two atoms cannot distinguish` at yet another arity, and the shortest
counter-shape is again cheap to synthesise.

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

  **And the sharper failure, found at `211c46e + 2`: a dump that *denies* a
  store is worse than one that cannot see it.** `value-motive ι` printed
  *"not stored — `IndexedDepRecursor` has no `iota` field"* with a `derived/`
  file path beside it, for as long as it took `derived` to build the field and
  nobody to update the instrument. Read literally it says the library owes the
  row; the library does not, and had not since `211c46e`. An absence with a
  reason is the design's whole point and it is also its whole exposure — the
  reason is prose and prose does not recompile. `mini/tests/dump.rs`'s
  `a_store_that_gained_a_theorem_is_no_longer_printed_as_absent` is the ratchet;
  it asserts the **presence of a theorem line**, not the absence of a string, so
  renaming the reason cannot satisfy it.
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

---

## 12. Removing the `fs` clause — what the prototype did not name

`3bf5b24`, over `SCOPING.md` §10, which prototyped and measured the change
before it was made. **Everything §10 predicted held**: Π and λ are one decision,
the fibre needs no helper, the residual is one sentence in four routes, and
`derived/` owed nothing. The ledger came out **byte-identical** — `constEv` 190,
`typeEv` 197, 17 exports stopping, every `waiting:` row unchanged.

Three things it did not name.

**1. The conversion census did not move at all.** §10 predicted +0.13 % proved
conversions; measured, `proved` is 9,738,106 before and after, and `gapped`,
`moved` and `movedSealed` are identical to the unit. So the +38 % runtime
(52 s → 72 s here; §10 measured +24 %) is **entirely** per-`Π` construction and
not conversion volume — which is what §10 said the cost *was*, arrived at by a
different measurement than the one it used. Worth knowing before the next
performance question: the two are separable and this change separates them
cleanly.

**2. Two routes *apply* the motive, not only name it.** §10's residual is
`motive_set != s.fs.of(spine, v_set)`, and that is right as far as it goes;
`rec_trunc` and `rec_prop` also spend `fs_app` on the motive, so the *fibre
site* has to be threaded and not only the term. That is why
`Interp::const_fibre_site` exists beside `const_dprod`, and why `rec_dep::Cx`
gained a field. A scope that enumerates *statements* will miss the rules that
consume them.

**3. The leak detector §10 mourns is not the one that fired — and it never
fired.** §10 names `pi_evidence`'s `!dep` guard, which turned "the codomain's
typing depends on the binder's hypothesis" into `Gap::Skeleton`, as the change's
one irrecoverable loss, and credits it with catching `proj_data`'s missing
`Interp::mk` records (§11.1's finding 1). **It did not.** That bug was caught by
`Interp::skeleton` answering `None` — a *term*-level check, strictly stronger,
which survives the change and now runs on **every** `Π` instead of only the
dependent ones. The `!dep` guard was measured at zero in every corpus run it
existed for, and under `dprod` its condition is not a defect at all: a codomain
whose term is binder-free and whose typing is not is simply *provable*, because
the fibre premise lives under the binder.

> **A guard that refuses an input its own rule cannot state is not a bug
> detector.** It looks like one, because both spell their refusal the same way.
> The check is whether the input is wrong or merely out of the rule's reach —
> and the cheap way to tell is that a bug detector has *caught* something.

So there is nothing to re-state, and re-stating it would have refused a
declaration mini can now certify. What is done instead is the honest half: the
surviving detector's test says what it guards and that its coverage grew, and
`pi_evidence`'s header records the retraction rather than the loss.

---

## 13. `Quot` — reconnaissance only, and the code was discarded

A `Sort 0` clause was started and **thrown away half-built** at a reboot. None
of it is in the tree. What follows is only what was *measured* before it went,
and the one question the coordinator asked is answered honestly rather than
plausibly.

**1. The row is half `Sort 0` and half classes — measured, and `QUOT-MODEL.md`
does not say it.** Every `Quot`-bearing declaration in the corpus is scheduled
at **both** `u = 0` and `u = 1`, at all six exports:

```text
120 quotMkType  u:=0, u:=1      123 Quot.sound / quotSoundType  u:=0, u:=1 each
121 quotIndType u:=0, u:=1      124 quotLiftReduction           u,v:=0,0 / 1,1
122 quotLiftType u,v:=0,0 / 1,1 125 quotIndReduction            u:=0, u:=1
```

§5.1 says `123` "exercises both branches"; it is *every* export, so the 14
pairs are roughly 7 and 7. **Neither clause alone closes a single export**, and
the ledger key must carry `u` or a row that is half closed reads as untouched.

**2. `zoneb::ensure` has no route to `Quot` at all**, and that is the hook
point. The four primitives are `add_quot`'s `ConstantInfo::Opaque` with no
`owner`, so every branch of `ensure` answers `no-interp` on the name before
reaching anything. They are §6.2 clauses, not translations — `crate::direct`'s
`Eq` is the shape to copy, one `prim_for` table and one `lam_nest` per
primitive.

**3. The formation clause works and is free**, as §2.3's T1 says. `⟦Quot.{0}⟧`
is `λA λr. A` and its bottom is the `α` binder's **own scope assumption**
returned unaltered — nothing derived, nothing minted. Measured: `typeEv` moved
from 0 to 1 on five of the six exports the moment it stored.

**4. Finding 1 did *not* recur where it could be seen, and where the build
stopped I do not know why.** The prediction was that `⟦·⟧` would return a term
the checker cannot put under a binder. `Quot`'s bottom is a *scope variable*,
which is recorded by construction, so the two nests that built could not have
tripped it. `Quot.mk`, `Quot.ind` and `Quot.lift` all failed — but at **my own**
bottom-certificate check, not at `Interp::skeleton`, and I did not measure which
of `point_of_proof`'s premises, the `as_pi` shape or the codomain comparison was
the refuser.

> **So the honest answer is "not observed", not "did not happen".** The
> distinction is this file's oldest rule and it is the one I would otherwise be
> breaking here: a decline at a check I wrote tells me nothing about a detector
> I did not reach. Whoever picks this up should instrument which check fires
> first — `MINI-HANDOFF.md` §11.1's finding 1 and §12's third note are both
> about exactly this confusion, in opposite directions.

**5. One thing worth checking early, because it is cheap and it could resize
`Quot.ind`.** §2.3 calls T6 — `(A ∈ U₀ ∧ • ∈ app(g,•)) → ∀q ∈ A. • ∈ app(g,q)`
— "the one genuinely new composed lemma" and the whole of what `derived/` owes
at `u = 0`. At a *nest bottom* it may not be needed at all: `q` is a scope
variable whose membership is in hand, so `point_of_proof` collapses it to `•`
in one step and the quantifier is never introduced. The lemma is the right
shape for a consumer holding an arbitrary `q`; a nest bottom holds its own
binder. **That is a read, not a measurement** — the branch that would have
settled it is the one that failed above.

### 13.1 A second run, also discarded — and three things settled

Resumed and stopped again at a reboot that had not happened. The clause is
**not** in the tree; one thing from the run is, and it is unrelated to `Quot`.

**The ledger key carrying `u` is trivial and it has a trap.** `Gap::Quotient(u)`
plus one `Ledger::key` arm, one `Gap::cause` arm and one `blocker::variant_name`
arm — four lines. The trap: the key was first spelled `quot-classes(u = 1)`, and
the `evidence` row is tab-separated `key=value` **split on the first `=`**, so
`tutorial_evidence_ledger` panicked inside its own parser and named a line of
the harness rather than the key. Nothing enforced the format; every existing key
*happened* to be safe. `ledger::tests::a_reason_key_is_wire_safe` is committed
and is the only surviving code from this run. Spell it `u:1`.

**The formation clause lands and the hook is one `if`.** `crate::quot::prim_for`
at the top of `zoneb::ensure`, before `env.get`, because the primitives are
opaque with no `owner`. `⟦Quot.{0}⟧ = λA λr. A`, bottom is the `α` binder's own
scope typing checked against the codomain's interpretation. Measured:
`typeEv` **197 → 203**, `no-interp(Quot)` 6 → **0**. `constEv` does not move,
which §5.1 predicts.

**Why the *types* interpret without `⟦Quot.mk⟧`, which no note says.** At
`u = 0` the expression `Quot.mk α r a` has type `Quot α r`, a `Prop`, so §6.2's
left column gives it `•` through the **application clause** — the constant
`⟦Quot.mk.{0}⟧` is never consulted. `⟦Quot.sound⟧`'s type comes out as
`f60(⟦Eq.{0}⟧, ⟦Quot.{0}⟧, •, •, …)` with `Quot.mk` already collapsed. So the
`mk` clause is needed **only** where the bare constant is the value — which is
`120_quotMkType` and nothing else. That reorders the work: `mk` is one export,
not a prerequisite.

**Two pins move and one of them is a judgement.** `interpretation-scope` 23 → 21
and `library-gap` 4 → 6, because `123_quotSoundType`'s `u = 0` pairs move from
`no-interp(Quot)` to **`axiom(Quot.sound)`**. `tutorial_evidence_ledger` asserts
that **no** `waiting:axiom(` key is emitted at all, and that pin was written
about this exact declaration: `Gap::Axiom` used to answer ahead of the check on
whether the type had interpreted, putting one obligation on two axes. `ty_blocked`
is that check and is untouched — the row is back because the type *now
interprets*, so the axis is right this time. **The absence pin cannot tell those
two apart** and has to become a count plus the property that made the old one a
misattribution. Do that deliberately; it is the one place in this row where a
green test would otherwise be bought by weakening the thing it was protecting.

**T6 is still unsettled**, and the branch that would settle it is `Quot.ind`,
which was not reached in either run. The read in §13 stands as a read.

### 13.2 `Quot` — three landings, and where `Quot.ind` stops

`6593b20`, `6706616`, `e8e58d7`. **`constEv` 190 → 191, `typeEv` 197 → 203**,
`no-interp(Quot)` and `no-interp(Quot.mk)` both closed. The increments were
committed separately and each is green on its own, which is the third attempt at
this row and the first to survive.

| landing | what | measured |
|---|---|---|
| `6593b20` | `Gap::Quotient(u)` + three arms | nothing mints it; corpus unchanged |
| `6706616` | formation, `⟦Quot.{0}⟧ = λA λr. A` | `typeEv` +6, `no-interp(Quot)` 6 → 0 |
| `e8e58d7` | `⟦Quot.mk.{0}⟧ = •` | `constEv` +1, `no-interp(Quot.mk)` 2 → 0 |

**`QUOT-MODEL.md` §2.1's "same term" is about the clause, not about
`infer_type`.** The note says `⟦Quot α r⟧` and `⟦α⟧` are "the same term, not
merely provably equal sets". As a statement of the clause that is right; as a
statement about what the checker hands back it is not — §6.2's application
clause gives `app(app(⟦Quot.{0}⟧,⟦α⟧),⟦r⟧)`, a redex over the stored λ-graph,
related to `⟦α⟧` by β. So `Quot.mk`'s bottom needs one `beta_spine` and one
`retarget_set` before `point_of_proof` applies. Nothing downstream weakens:
§2.1's load-bearing use is that the **domain** sits in an argument slot of a
shared `Π` symbol, which is about the domain slot and not about `Quot`'s spine,
so T3 and T5 still cost what the note says.

**Where `Quot.ind` stops, stated as far as it was measured.** A branch was
written and **reverted**; the tree has only the two clauses above. What is
known:

* `⟦Quot.ind.{0}⟧` **never reaches the store** — `--dump-only=Quot` lists
  `Quot` and `Quot.mk` and not it;
* the ledger says `no-interp(Quot.ind)`, minted at **`kernel.rs:1024`**, which
  is `const_defeq`. That path looks the constant up and does **not** call
  `zoneb::ensure`, so it cannot report the store's own decline — **the real
  reason is masked**. That is why the failure is opaque, and it is a fact about
  the reporting path rather than about `Quot`: any clause whose *store* fails
  while a declaration's **value** is the bare constant will read as plain
  `no-interp` with the reason discarded. Worth fixing on its own, and it is
  §2's discarded-evidence pattern at a seventh position.

So the next step is **instrument which check in the `Ind` bottom refuses** —
not guess. §13 already says this about this exact branch and it is still the
answer.

**T6 remains a read.** The branch that settles it is the one that failed. The
route looked right on paper — `q` inhabits `⟦Quot α r⟧`, which β-reduces to
`⟦α⟧`, so `q` is its own witness for `h : ∀a:α, β (mk a)`, and `⟦mk a⟧` is `•`
for every `a`, so the application lands on `app(⟦β⟧,•)` and one Leibniz along
`• = ⟦q⟧` finishes it — but a route that looked right and did not run is
exactly what this file's §1 calls a dynamic prediction. **Do not record `u = 0`
as owing `derived/` nothing until `Quot.ind` runs.**

### 13.3 The `Sort 0` clause is complete — and two things to carry

`6706616`–`89e960e`, over `2dfcaa0`. **`constEv` 190 → 195, `typeEv` 197 → 203**,
all four `add_quot` primitives interpreted, both ι rules closed, `derived/`
untouched. `QUOT-MODEL.md` is corrected in place at `bd46a71`.

**1. `ConstantInfo` is not uniform across the four, and that is why the hook
goes at the top of `ensure`.** `Quot` and `Quot.mk` are
`ConstantInfo::Opaque`; **`Quot.lift` and `Quot.ind` are
`ConstantInfo::Recursor`**. A clause matching `Opaque` alone silently declines
half the family — which is what happened, and what `Checker::fill_store` turned
from a bare `no-interp` into a one-look fix. It is also why the hook cannot sit
after `env.get`: the ordinary path routes a `Recursor` to `crate::recursor`,
which is about an inductive declaration's eliminator and has nothing to say
about these two. **Any future clause over primitives will meet the same
non-uniformity.**

**2. `Quot.sound` is not reachable from `zoneb::ensure`, and the clause for it
is written in the wrong place.** It was built and **reverted**. The derivation
is right and small — the codomain is `Eq (Quot α r) (mk a) (mk b)`, both sides
are `•` at `u = 0`, so the set is `eq_set(•,•)` and the inhabitant is one
instance of `Direct::eq_refl` composed with `beta_spine` down `⟦Eq.{0}⟧`'s
stored nest, which is `direct::ctor_bottom`'s own `Eq.refl` derivation at a
codomain that is not a constructor's. `QUOT-MODEL.md` §2.3's T8, and it needs
`derived/` nothing.

What is wrong is the insertion point. `ensure` runs on a **constant occurrence**
that misses the store; `Quot.sound` in `123` is the *declaration being
checked*, so nothing ever asks. Its gap is minted at `ledger.rs:434` —
`ty_blocked.unwrap_or_else(|| Gap::Axiom(name))` — the ledger's own fallback for
a `Declaration::Axiom` whose type interpreted and whose typing did not arrive.

> **So the hook belongs where `Declaration::Axiom` is handled in the
> declaration pipeline, not in `ensure`** — a *third* insertion point, after
> `zoneb::ensure` for inductives and `crate::direct` for §6.2 clauses. Worth
> stating as its own shape: an axiom's inhabitation is the one obligation with
> no constant occurrence to hang off.

**What remains: 7 pairs** *(was 9; `axiom(Quot.sound)` closed at `f2c4b5b`)*.
`quot-classes(u:1)` 7 — the equivalence-class half, against `rel_graph` and
`quot::universe`, both built at `57f5482`; `rel_graph` is no longer unconsumed
and its **first consumer is `Acc`**, not `Quot` — §16.

`axiom(Quot.sound)` closed as this section said it would, at insertion point 3,
and both its pairs are at `u = 0`: `quotSoundType`'s value is literally
`Quot.sound.{u}`, so its `defeq` was already in hand and its typing arrived by
`retarget_subject` in the same run. The derivation is `direct::ctor_bottom`
unchanged, exposed as `direct::eq_refl_bottom` — that function never consulted
which declaration it was the bottom of, so it was already the rule for any nest
whose codomain is an equation between two terms the interpretation identifies.

---

## 14. The interpretation's three insertion points

Nobody had written this down, and I only have it because `Quot` hit all three.
It is the thing to read before adding any clause, because **which point a
clause belongs to is decided by what asks for it, not by what it is**.

| # | point | what triggers it | what it may build |
|---|---|---|---|
| 1 | `zoneb::ensure` | a **constant occurrence** that misses the store, through `Checker::fill_store` | anything named by a `Const` node |
| 2 | `direct::build`, from `zoneb::build` | point 1, on a declaration `direct::clause_for` names | §6.2's own clauses (`Eq`, `Acc`) |
| 3 | the **declaration pipeline**, `ledger.rs` | a declaration reaching its own typing obligation | `mini/src/axiom.rs` — an axiom's inhabitation (`Quot.sound`) |

**Point 1 is reached from two callers and only recently from both.**
`Checker::const_evidence` — `⟦c.{σ}⟧` and its typing, i.e. every `Const` node in
a type or a value — and `Checker::delta_evidence`, `whnf`'s δ leg. The second
had no `ensure` call until `2dfcaa0`, so a clause whose *store* declined was
reported as a bare `no-interp` whenever the constant was reached through δ.
That matters most for a declaration whose **value is a bare constant**, since δ
is then the first thing that asks.

**Point 3 now has one clause, and `Quot.sound` is it** *(built at `f2c4b5b`;
this paragraph read "has no clause in it, and `Quot.sound` is why it should")*.
An axiom has no value, so its typing obligation `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` was
decided by `ty_blocked.unwrap_or_else(|| Gap::Axiom(name))` alone, and there
is **no constant occurrence anywhere to hang a clause off**. Points 1 and 2
cannot see it. That is not a `Quot` fact:

> **An axiom's inhabitation is the one obligation with no constant occurrence
> to hang off**, and it will be true of every axiom this project ever
> certifies.

Building it added one thing the paragraph above did not have, and it is the
reason the hook cannot simply be moved: **hooking `ensure` for an axiom is not
late, it is silently wrong.** `Ledger::run`'s store-hit branch `continue`s
*before* `note_missing` and before `const_ev_ok`, so an axiom pre-filled from
`ensure` leaves a pair that emits no `waiting:` row and no `constEv` at all —
an absence with no reason, which is the defect the ledger exists to prevent,
arriving through the fix rather than through the bug.

**That is §2's pattern at a seventh position**, and it is worth counting as
one. The six there are values *computed and dropped*; this is a value
**never computed**, because a `continue` walked past the site that would have
computed it. Same symptom, and the symptom is what §2 is a register of: a row
that reads as blocked on nothing, or on the wrong thing. The discriminator §2
ends on — whether the value's `Γ` can be discharged where it is derived —
does not apply, so the register needs a second one: **a control-flow shortcut
past a recording site is indistinguishable from a value that was recorded and
lost.** `typeEvMasked` (§16 item 5) is the same shape a third time, at the
ledger's own reporting layer rather than at a store.

### The non-uniformity that catches a clause at point 1

`zoneb::ensure` branches on `ConstantInfo`, and a *family* of primitives need
not share one:

```text
Quot, Quot.mk        ConstantInfo::Opaque
Quot.lift, Quot.ind  ConstantInfo::Recursor      ← add_quot's own choice
Quot.sound           ConstantInfo::Opaque, declared by the export, not add_quot
```

A clause matching `Opaque` alone silently declines half the family. It is also
why `crate::quot`'s hook sits at the **top** of `ensure`, before `env.get`: the
ordinary path routes a `Recursor` to `crate::recursor`, which is about an
inductive declaration's eliminator and has nothing to say about these two.
`crate::direct` gets away with a later hook only because `Eq` is an
`Inductive`.

---

## 15. Handing off — the signal, named

**Signal 1: accuracy holding while efficiency slips.** It is firing and I would
rather say so than have it inferred.

Accuracy held throughout. Nothing wrong reached a commit; every wrong thing was
caught by the run in the same round; three half-built branches were reverted
rather than left, and the tree was clean at every stop. What slipped is the
*mode*. Early in this run I read the source, predicted, and was right —
`π₂(π₁ z)` against `π₁(π₁ z)` before writing a line, `has_bvar`'s blindness to
`Expr::Proj` diagnosed from one instrumented run. In the last three increments
the first attempt was wrong three times running, each on a mechanical detail I
could have read off the source first: the `ConstantInfo` variant, `Quot.lift`'s
nest depth, `Quot.sound`'s insertion point. Write-fail-diagnose-fix, where it
used to be read-then-write.

**Signal 2 has one instance, and it is the sharper one.** §13 says, about this
exact family, *"instrument which check refuses — not guess."* Two commits later
I guessed `Quot.sound`'s insertion point and only read `ledger.rs:434` after the
build failed. Recognising an inherited pattern while repeating it — mine, in the
section I wrote to prevent it.

Signal 3 has not fired: nothing was committed worse than I would want, which is
what the three reverts were for.

**Why stop here rather than after the classes row.** `quot-classes(u:1)` is 7
pairs over the `R̄` seam — Lean's curried `⟦r⟧ ∈ fs(A, fs(A, U₀))` against
`derived/src/quot/`'s pair-set `R` — which two notes call the untested edge, and
which `SCOPING.md` §1's sixth category predicts will cost one β step more than
either says. That is precisely the work that wants read-then-write, and it is
the largest single piece left.

### What a successor starts with

Better than any predecessor had, and the reading order matters:

1. **§14 first** — the three insertion points. It is short and it decides where
   a clause goes, which is the question that cost me two reverts;
2. `SCOPING.md` §1's **sixth category**, then §10. The sixth is the only one of
   the six that is a bias rather than a mistake, so it is the only one you can
   correct for in advance: take the mechanism as stated and add one β step
   wherever a note says a certificate transfers unchanged;
3. `QUOT-MODEL.md`, **corrected in place at `bd46a71`** — its `u = 0` half is
   now measurement rather than design, and its `ℓ > 0` half is still design;
4. `mini/src/quot.rs` for the shape a primitive clause takes, and
   `mini/src/proj_data.rs` for the shape a term-former takes.

### The board

*(Corrected in place at `f2c4b5b`, `8d883fa`, `2828662` and `bd174b8`. It read
`constEv` **195**, `typeEv` 203, library-gap 6, threading 1, 23 pairs waiting;
then `typeEv` 204 with one masked row under it; then 197 / 205 / 21 with
`quot-classes(u:1)` as one seven-pair row; then 198 / 211 / 20.)*

`constEv` **200** of 218, `typeEv` **211**, `fullyInterpreted` **138**,
library-gap 4, threading 4, interpretation-scope 10, **18 pairs waiting**,
`typeEvMasked` **0**, **14** exports block.

| row | pairs | owes |
|---|---:|---|
| `fun-typed-rec-arg(RTree)` | 4 | the *general* construction widened — not a clause |
| `recursor(Acc: …rec_acc::pack is not wired)` | 3 | **two** constructions — §17 |
| `no-interp(Nat)` | 2 | — |
| `unit-like(PUnit)` | 2 | — |
| `fun-eta` | 2 | — |
| `quot-classes(Quot.lift, u:1)` | 2 | a construction, and the `fs`/`dprod` seam — §18 |
| `ind-spec(Eq: type former spine)` | 2 | `Quot.sound` at `u ≥ 1`, over `q_sound` — §18, and it is **two blockers in series** |
| `iota(RBTree.rec)` | 1 | wiring, over `IndexedDepRecursor::iota` |

Plus two design items owed and not started: `Term::as_apply` into the kernel,
and the three `skeleton()` sites branching on the Lean `Expr` rather than on
`Parts` — which would collapse `Expr::has_bvar` and `Term::occurs_free` into one
"mentions the binder" test, and §12 records why two that can disagree is what we
keep paying for.

---

## 16. `Acc` — the formation clause landed, and the row's cost is not what §15 said

`184bde9` (formation) and `f2c4b5b` (`Quot.sound`, §14's point 3). Both green
on their own; `constEv` 195 → **197**, `typeEv` 203 → **204**.

**1. The note's cost ordering did not survive contact, and the correction is
a split rather than a number.** §15's board called `Acc` "pure wiring,
`derived/` complete" and the cheapest thing on the board, against
`quot-classes(u:1)` as the largest. Measured, `Acc` is **two** things with
very different prices — and item 5 below makes it **three**:

* the **formation clause** — `⟦Acc α r x⟧ = [x̄ ∈ acc(⟦α⟧,R̄)]`, one row of
  `direct::Clause`, one arity-3 conditional singleton, one afternoon. Landed;
* the **eliminator** — `recursor(Acc: …)`, 3 pairs, and it is **two
  constructions**, not one. `Acc.rec.{u₁,u}` splits on `u₁` exactly as
  `rec_dep` does: at `u₁ = 0` the eliminator is a proof and the rule is
  `derived::acc::acc_rect` at `φ(z) := • ∈ app(app(C̄,z),•)`, which needs no
  `rec_acc` at all; at `u₁ ≥ 1` it is `rec_acc::pack` and `pack_iota`'s
  `step_typed` hypothesis has to be discharged. Measured per pair: `117` is
  scheduled at `(0,0)` and `(1,1)`, and `118`'s single pair is at
  `Acc.rec.{1,1}` with motive `Bool`. So it is **one pair on `acc_rect` and
  two on `pack`**, and neither construction closes an export alone.

That is `SCOPING.md` §1's sixth category at the level of a *row* rather than
of a certificate: the note was right about what the clause **is** and
optimistic about what it **costs**, and the optimism was concentrated
entirely in the eliminator.

**2. `pack_iota` is not unconditional, and the brief said the family was.**
`derived/src/rec_acc.rs`'s own header: `step_typed(A,R,T,e)` is "the **only**
hypothesis anywhere in this module", and it guards `totality`, `rec_funspace`,
`iota` and `pack_iota`. `pack_app` is unconditional; `pack_iota` is not. The
`u₁ ≥ 1` half therefore owes a discharge of `step_typed` at Lean's own minor
premise, which is the piece to size before starting it.

**3. The `R̄` seam's first consumer is `Acc`, not `Quot`.** §15 and
`QUOT-MODEL.md` §6 finding 3 both frame `derived::quot::graph`'s
`rel_graph(A,r)` as the untested edge of the `ℓ > 0` *quotient* clause. It is
the untested edge of `acc` too, and for exactly the same reason one layer
along: every theorem in `derived/src/acc/` reads `⟨y,x⟩ ∈ R` while Lean's `r`
interprets curried. `mini/src/acc.rs` consumes `rel_graph`, `graph_pair` and
`pair_in_graph`, so the seam is now exercised — by the formation clause's
symbol, which mentions the graph but does not yet *reason* about it. The
bridges are consumed for real by `Acc.intro` and `Acc.rec`, both open.

**4. The formation clause alone carried the types, exactly as `Quot`'s did —
and that generalises.** §13.1 found it for `Quot.mk`: a constructor applied at
a `Prop` gets `•` from §6.2's **application** clause, so the constant's own
interpretation is never consulted by a *type*. `Acc.intro α r x h` is the same
shape, and `117`'s `typesOk` went 0 → 2 with `⟦Acc.intro⟧` still declining.
The rule worth carrying: **for a `Prop`-valued declaration, the type former is
the whole of what its consumers' types need**, and the constructor and
eliminator clauses are each one export.

**5. The masked reason, measured — and the row underneath is not the one the
label named.** *(Rewritten in place. This item read "one measurement I could
not attribute, left as a measurement"; the run was spent at `e1608c3` and the
answer changes the row's shape, so the item is the answer rather than the
deferral.)*

`117` has `typesOk = 2` and `typeEv = 1`. Five lines in a detached worktree —
print `Ledger::key(ty_ev.gap())` whenever `ty_tm.is_some()` and the typing is
not proved — and it is:

```text
TYEV  accRecType  sigma=[1,1]
      reason=ind-spec(Acc: acc: Acc.intro's step hypothesis is not transported to preds_in)
```

**It is the constructor, under a row labelled for the eliminator.** So the
`Acc` row is **three** pieces, not the two item 1 says:

| piece | pairs it gates | rule | state |
|---|---|---|---|
| `Acc.intro`'s typing | `117` σ `[1,1]`'s *type* typing (`typeEv` +1) | `acc_intro`, over the transport | **landed**, `8d883fa` — §17 |
| `Acc.rec` at `u₁ = 0` | `117` σ `(0,0)` | `acc_rect` | open |
| `Acc.rec` at `u₁ ≥ 1` | `117` σ `(1,1)`, `118` | `rec_acc::pack` + `step_typed` | open |

and the **first** of the three is the one to take, for two reasons beyond its
size: it is a prerequisite for one of the other two, and it is where the
`cond_elim` / `graph_pair` / `beta_spine` transport gets written **once** —
`acc_intro`'s second premise and `acc_rect`'s `ind_step` want the same three
moves at different arities. *(Both reasons held; the third move is
`graph_pair`, not `pair_in_graph`, and §17 item 3 is why that distinction is
not cosmetic.)*

Why `(0,0)` does not need it and `(1,1)` does was **not** measured, and is left
as a question rather than a guess. *(Answered at `8d883fa`; §17 item 2. It is
not a fact about the constructor at all — `⟦Acc.intro⟧`'s typing was absent at
**both** σ.)*

The instrument is now permanent: `typeEvMasked` on the evidence row, pinned at
1 with its occupant named, and the five-line throwaway that reads the reason
back is in the field's own doc-comment. Corpus-wide the count is 1 — this is
the only masked row there is. `MINI-DESIGN.md` §0.5's "read a zero row twice"
has a sibling: **a row whose reason is about a different obligation reads
exactly like a row whose reason is its own**, and nothing distinguished them
until there was a counter.

**6. Two `acc` symbols now exist and the reason it is safe is written down
rather than assumed.** `IndApparatus::acc` is §5.3's general class-(S)
carrier's; `Interp::acc` is this clause's. They never compare notes — `Acc`
takes the direct clause before the trichotomy, so it never acquires a
`ClassS` — and what they *must* share is the pairing, which
`mini/src/acc.rs`'s `the_two_acc_apparatus_share_one_pairing` asserts rather
than argues. Reaching for `IndApparatus::acc` instead would make an export
that mentions `Acc` and nothing else build a `Wtype`, a `Bound`, an `IndChain`
and a `Machine`; `117_accRecType` is exactly such an export.

### What a successor starts on

*(This section is **spent**: `Acc.intro`'s typing landed at `8d883fa`. It is
kept unedited below because §17 is a report against it and the comparison is
the useful part — three of its four predictions held exactly, one did not, and
the one that did not is the cost. Read §17 for what a successor starts on
now.)*

**`Acc.intro`'s typing** — item 5's finding, and it displaced `Acc.rec` as the
answer to this question after one instrumented run. It is the smallest of the
three pieces, it is a prerequisite for `117` σ `[1,1]`, and it is where the
transport gets written *once*: `acc_intro`'s second premise and `acc_rect`'s
`ind_step` want the same three moves at different arities, and
`direct::ACC_INTRO` names them —

* the minor's scope typing is `• ∈ chi(h⃗,A)`, and `CondSite::chi_ax` plus
  `derived::prop::cond_elim` turn that into `CondSite::phi`, which is
  `∀x. (x ∈ A → • ∈ b(h⃗,x))`. `Interp::cond_lam_typing` is the same step in
  reverse and is what closes each level on the way back up;
* Lean's `r y x` arrives as `• ∈ app(app(r̄,y),x̄)` and `acc_rect` wants
  `⟨y,x̄⟩ ∈ R̄`: `AccClause::graph_pair` one way, `pair_in_graph` the other;
* `⟦Acc α r y⟧` in a hypothesis is a **redex** over the nest being built, so
  it is one `beta_spine` from `acc_set(A,r̄,ȳ)` before the conditional
  singleton can be eliminated. That is the sixth category's one β step, in the
  place it was predicted.

`mini/src/quot.rs`'s `Prim::Ind` bottom is the closest worked example of all
three moves in one bottom, and `mini/src/axiom.rs` is the shortest example of
a whole clause. `Interp::cond_app` is the one helper worth reading before
either: it already does "apply a `Prop`-`Π` hypothesis at an argument",
including the `point_of_proof` step that moves the membership off a scope
variable and onto `•`, which is the part a first attempt would leave out.

**The one thing that is genuinely new work** is the quantifier: `cond_app`
delivers the conclusion *at a term*, and `acc_intro` wants
`∀y. (y ∈ A → …)`. That is derive-at-a-fresh-variable-then-discharge, which is
§2's rule 5 and `rec_dep::pre_at`'s shape, and it is the piece to size first
rather than the three moves above.

### Why this is a handoff and not a pause

The three moves are read off the source and written down; what is not written
is the hypothesis management around them, and that is the bulk. It is a
construction the size of `iota_dep.rs`, and §10 is explicit that the cheapest
moment to hand off is *before* the next construction rather than inside it —
Kai's reason, and it is mine. Nothing here is half-built: the tree is clean,
every increment is green on its own, and the scope this section leaves is
sharper than the one it inherited by exactly one instrumented run.

---

## 17. `Acc.intro`'s typing — landed, and the estimate erred the rare way **[Bram]**

`8d883fa` (the transport) and `deb8368` (a correction the transport forced).
Green on their own; `typeEv` 204 → **205**, `typeEvMasked` 1 → **0**.

**1. The ledger delta is one line, and that is the finding as much as the
theorem is.** Measured over the whole tutorial corpus, before and after, by
summing every `evidence` and `ledger` row:

| counter | before | after |
|---|---:|---:|
| `typeEv` | 204 | **205** |
| `typeEvMasked` | 1 | **0** |
| everything else | — | *bit-identical* |

`pairs` 218, `constEv` 197, `typesOk` 205, `fullyInterpreted` 133,
`threading-incompleteness` 4, every `waiting:` row, the cause split: unchanged.
So the row §16 item 5 identified was exactly the row that closed, and it closed
alone. Per-declaration: `117_accRecType` σ `[1,1]`'s *type* typing is the one
obligation that moved; `117` σ `(0,0)` and `118` are untouched and still wait
on `recursor(Acc: …rec_acc::pack is not wired)`. `⟦Acc.intro.{u}⟧`'s own typing
is now stored at both σ `[0]` and σ `[1]` — read out of `--dump-only=Acc.intro`,
where it previously printed *"(no typing — waiting on ind-spec(Acc: …))"*.

**The instrument was run first.** `typeEvMasked`'s five-line reader, in a
detached worktree, reproduced §16's reading verbatim before a line was written:

```text
TYEV  accRecType  sigma=[1, 1]
      reason=ind-spec(Acc: acc: Acc.intro's step hypothesis is not transported to preds_in)
```

**2. §16's open question, answered — and the question was pointing at the wrong
object.** *"Why `(0,0)` does not need it and `(1,1)` does was not measured."*
It is not a fact about the constructor: `⟦Acc.intro⟧`'s typing was absent at
**both** σ `[0]` and σ `[1]`, measured off the store dump before the change. The
asymmetry is entirely the *consumer's*, and the discriminator is a signature,
not a control flow:

```text
Interp::cond_typing (site, dom)                 — no domain membership
Interp::dprod_typing(site, dom, dom_mem, …)     — takes one
```

`cond_in_u0` is closed at any `φ` whatever, so a `Prop`-valued `Π` types
**without its domain's typing**. At `σ = (0,0)` `accRecType`'s motive is
`Sort 0`, its type is `Sort 0`-valued throughout — the blocker prints
`⊢ ⟦ty[σ]⟧ ∈ ⟦Sort 0⟧` — so every `Π` in it takes the `Prop` clause and none of
them ever asks for `⟦Acc.intro α r x h⟧ ∈ ⟦Acc α r x⟧`. At `(1,1)` the motive is
`Sort 1`, the chain is `dprod`, and the domain's membership is demanded.

That generalises past `Acc`, and it is the dual of §16 item 4: **a `Prop`-valued
`Π` hides a missing constructor typing from its own type's typing, and a
dependent one does not.** Anywhere a declaration is scheduled at both a `Prop`
and a non-`Prop` σ, the non-`Prop` one is the σ that reports the truth.

**3. `graph_pair` and `pair_in_graph` were attributed the wrong way round, and
it is not cosmetic.** `mini/src/acc.rs`'s field docs read "the direction the
**eliminator** needs" and "the direction the **constructor** needs"
respectively. Measured: `Acc.intro` needs **`graph_pair`**. `acc_intro`'s second
premise is `∀y. (y ∈ A → (⟨y,x̄⟩ ∈ R̄ → y ∈ acc(A,R̄)))`, so the pair membership
is an *antecedent* — held, never owed — and what is owed is Lean's curried
`r y x`. `step_closed` has it in the same position, so the eliminator wants
`graph_pair` too.

**A bridge is chosen by which side of the implication the consumer stands on,
not by which of constructor and eliminator it is.** Corrected in place at
`deb8368`. §16 item 3's sentence *"The bridges are consumed for real by
`Acc.intro` and `Acc.rec`, both open"* is half right: `Acc.intro` consumes
**one** bridge, and `pair_in_graph` still has **no consumer in `mini/` at all**.
It is kept rather than deleted — what wants that direction is a caller that must
*put* a related pair into `R̄`, which is `derived::quot`'s `q_sound`/`rcompat`
and the `ℓ > 0` quotient clause — but it is now an *unused* item and the
standing rule applies to it: measure which check fires first, once that clause
exists.

**4. The size estimate was wrong, and in the direction this project almost never
goes.** §16: *"It is a construction the size of `iota_dep.rs`"* — 548 lines —
*"and §10 is explicit that the cheapest moment to hand off is before the next
construction."* Measured: **57 non-comment lines** in `intro_mem`, plus a
`match` arm and two tests. `mini/src/acc.rs` went 269 → 419 lines and most of
that is header.

The mechanism was right and the *cost* was wrong, which is `SCOPING.md` §1's
sixth category — except pointing the other way, and this is only its second
recorded instance (the first is T6, which was scoped as a lemma and turned out
to be nothing). Both have the same cause and it is worth stating as a rule:

> **A note that sizes a piece of work by its *hardest named step* overshoots
> whenever that step is already built.** §16 sized `Acc.intro` by "the
> hypothesis management, and that is the bulk". The hypothesis management is
> `Scopes::open` and `Closed::discharge` — two calls — and the walk shape is
> `rec_dep::minor_at`'s, already written. What was genuinely new was three
> lines of composition.

The sixth category's *upward* bias is about denotations versus terms, and it
held again here (the `beta_spine` was needed, exactly where predicted). This
downward one is about **constructions versus their ingredients**, and the two
are independent: a note can be one β step optimistic about a certificate and a
whole construction pessimistic about the surrounding code in the same
paragraph. §16 was both.

**5. Three of §16's four predictions held exactly.** Worth recording because
the section was written from the source rather than from a scope, and it shows:

| §16 said | measured |
|---|---|
| `cond_app` delivers at a term, `acc_intro` wants a `∀` — derive-at-a-fresh-variable-then-discharge | held; `Closed::discharge`'s shape is A1's premise on the nose, no formula surgery |
| `⟦Acc α r y⟧` in a hypothesis is a redex, one `beta_spine` from `acc_set` | held, and it is the only β step in the derivation |
| `cond_elim` turns `CondSite::chi_ax` into the `∀`-form | held for `cond_elim`; **`cond_lam_typing` was not used at all** — `lam_nest` closes the levels above, so nothing goes back up by hand |
| the transport is where three moves get written once | held for two of three; `pair_in_graph` is the third and it is not one of them (item 3) |

**6. The one test that is not free.** A declaration named `Acc` whose step
hypothesis is `r x y` rather than `r y x` is the accessibility predicate of the
*converse* relation. Its codomain is unchanged, so neither `Clause::arity`'s
shape check nor `ctor_bottom`'s final comparison can see it; the only thing that
can is `syl`, where `graph_pair`'s conclusion has to meet the inner conditional
singleton's domain. `a_declaration_named_acc_with_the_relation_reversed_is_declined`
pins the gap **by name**, and the positive test on the same synthetic
declaration is what makes that a corner walk rather than an assertion: one
build, two cells, and the differing input is the relation's argument order.

### What a successor starts on

The board's largest single piece is unchanged and so is the argument for it:
**`quot-classes(u:1)`, 7 pairs.** It is now better supported than when §15
scoped it — `rel_graph` has two consumers rather than one, the `R̄` seam has
been exercised for real by a derivation and not only by a symbol, and item 3
above says which of its two bridges a *given* consumer wants and why. Note that
`pair_in_graph` — the bridge with no consumer today — is the one the quotient
clause is expected to want, so that row is also the measurement that decides
whether it stays.

`Acc.rec` is the other candidate and it is two constructions, per §16 item 1
and its table above. `u₁ = 0` is `acc_rect` and needs no `rec_acc`; `u₁ ≥ 1` is
`rec_acc::pack` and owes a discharge of `step_typed`, which §16 item 2 is
explicit is **not** unconditional and is the piece to size before starting.
Nothing in this section changes that ordering; what it changes is the estimate
you should apply to either, which is item 4.

---

## 18. `quot-classes(u:1)` — three of four clauses landed **[Bram]**

`44d4b33` (formation), `2828662` (`mk`), `bd174b8` (`ind`). Green on their own;
`constEv` 197 → **200**, `typeEv` 205 → **211**, `fullyInterpreted` 133 → **138**,
blocked exports 17 → **14**, the seven-pair row down to **two** pairs on `lift`
plus two that left the family.

*(This section read "two of four" and gave the board at `mk`; `ind` landed in
the same run and the numbers above are the current ones.)*

**1. All seven pairs blocked on the *type's interpretation*.** Measured per
export before a line was written, and it is why formation was the right first
increment rather than a guess about which primitive to take: `⟦ty[σ]⟧` is the
cheapest obligation there is, so every one of the seven was stopped at the first
mention of `Quot` in a type, and nothing downstream had ever been reached.

**2. Formation moved `typeEv` by two and moved the `waiting:` row by nothing —
which is why the key now carries the primitive.** `quot-classes(u:1)` stayed
bit-identical at 7 across an increment that closed two of its type typings. That
is exactly the *half-closed row reads as untouched* defect the **level** was put
into the key to prevent, one level down, on the first increment. Split:

| primitive | at the split | after `mk` | after `ind` |
|---|---:|---:|---:|
| `Quot.mk` | 4 | **0** | 0 |
| `Quot.lift` | 2 | 2 | 2 |
| `Quot.ind` | 1 | 2 | **0** |
| *(left the family)* | — | 2, as `ind-spec(Eq: …)` | 2 |

The general rule, now measured twice at two depths: **a reason key must name
every axis the row is split along, and the axes are found by landing one clause
and watching the row not move.** There is no way to know in advance; there is a
cheap way to find out, and it is one increment.

**3. `125_quotIndReduction` was labelled `Quot.mk` and is an `ind` pair.**
`Quot.ind`'s declared type is `∀β. (∀a. β (Quot.mk α r a)) → ∀q. β q`, so a
declaration *about* `ind` meets `mk` first. Reading the row as "one `ind` pair,
one `lift` pair, four `mk`" would have sized `Quot.ind` at a third of its true
share. **A blocker names the first constant a walk ran into, not the clause the
declaration is about**, and for a family whose members mention each other those
differ systematically.

**4. `Quot.sound` at `u ≥ 1` is not reflexivity, and its two pairs left the
quotient family.** At `u = 0` its codomain `Eq (Quot α r) (mk a) (mk b)` has
both sides `•` (§13.1), so `crate::axiom` routes it to
`direct::eq_refl_bottom` and `⊢ • ∈ eq_set(a,a)` is the whole of it. At
`u ≥ 1` the sides are `class(A,R̄,ā)` and `class(A,R̄,b̄)` — genuinely different
terms — and the rule is `derived::quot::q_sound`.

**Measured, and this is the part that is not obvious: it declines at
`direct.rs`'s `beta_spine`, *before* reflexivity is tried at all.** So the row
is **two blockers in series**, which `SCOPING.md` §0 names as the one thing a
corner walk cannot tell from one blocker plus a bad guess. Repairing the spine
would land you at the refl comparison still needing `q_sound`. It is pinned by
its real key (`ind-spec(Eq: type former spine)`, 2) rather than renamed, so a
successor sees the count move when *either* is fixed — and knows from this
paragraph that one moving is not the row closing.

**5. `pair_in_graph` has its predicted consumer, and it is `Quot.sound`.** §17
item 3 found the bridge unused in `mini/` and predicted the `ℓ > 0` quotient
clause would want it, on the rule that a bridge is chosen by which side of the
implication the consumer stands on. `q_sound` wants `⟨ā,b̄⟩ ∈ R̄` while Lean's `h`
arrives as `• ∈ app(app(r̄,ā),b̄)` — *owing* the pair, not holding it. The rule
survives contact; the theorem is not yet consumed, so the confirmation is a
reading of `q_sound`'s statement and not a build. Say so.

**6. Two design notes that held, and one shape that did not transfer.**

* `QUOT-MODEL.md` §6 finding 1's formation theorem instantiates at the rung with
  no friction: `⟦Sort u⟧` is `U(seed)` and `quot_in_universe` is stated at
  `U(c)`, so they meet exactly where there is a rung, which is `u ≥ 1`. The
  `u = 0` case is not merely unavailable but refutably wrong, and
  `formation_declines_at_sort_zero` pins that the clause does not answer there.
* The sixth category's **upward** half held again, twice: `mk` needed one
  `beta_spine`, in the same place the `u = 0` clause needs one and in the
  opposite direction.
* **What did not transfer is `crate::quot`'s own header claim** that
  *"`⟦Quot.{0}⟧` alone moves `typeEv` on five of the six exports, because at
  `u = 0` the types need nothing else."* At `u ≥ 1` `Quot α r` is not a `Prop`,
  so §6.2's application clause no longer collapses `⟦Quot.mk α r a⟧` to `•` and
  the constant's own interpretation **is** consulted by types. Formation alone
  moved two of six, not five. That is §17 item 2's finding from the other side:
  a `Prop`-valued σ hides a constructor's interpretation from its consumers'
  types, and the non-`Prop` σ is where the truth is.

**7. `Quot.ind` cost two β steps at two nests, and the note names neither.**
`QUOT-MODEL.md` §6 finding 5 states the route exactly right — `quot_cases`, the
hypothesis at the witness, Leibniz along the equation — and that route held
verbatim. What it does not say is that `⟦Quot α r⟧` is a redex over
`⟦Quot.{u}⟧`'s stored nest **and** the `⟦Quot.mk α r x⟧` inside `h`'s own fibre
is a redex over `⟦Quot.mk.{u}⟧`'s, the second sitting under `β̄`'s application
and so costing a `congr_arg` in `app`'s second slot as well. Two applications of
the sixth category's upward half in one derivation, and the note's downward half
applied too: `quot_cases`, `exists_elim`, `curry` and `inst_self` are all built,
so the whole thing is 40 non-comment lines. **Both corrections, same
paragraph** — which is the pattern Vera recorded, at a third instance.

**8. `125_quotIndReduction`'s ι rule needed no step at all.** Both sides of
`ind β h (mk a) ≡ h a` are proofs at every `u`, so §2.3's T7 is uniform in `u`
— asserted by the `u = 0` ratchet, and this is the second instance, at the
level where it could have failed.

### What a successor starts on

One clause left in the family and one row that has left it. **Both are
constructions**, which is why this is a handoff and not a pause — §10's rule
that the cheapest moment to stop is *before* the next construction, and the
`Quot` row's own history of two attempts discarded because a clause was coherent
only as a six-file set.

* **`Quot.lift` at `u ≥ 1`** — 2 pairs (`122`, `124`), and it is the biggest of
  the four. `lift_in_funspace` and `lift_beta` are built and unconsumed. Three
  distinct pieces, and the middle one is not in any note:

  1. **`rcompat` out of Lean's `h`.** `h : ∀ a b, r a b → f a = f b` is a
     three-level `cond_app` walk; `r a b` becomes `⟨ā,b̄⟩ ∈ R̄` by `graph_pair`
     (the *holding* direction, §17 item 3), and `⟦Eq β (f a) (f b)⟧` is
     `eq_set(app(f̄,ā), app(f̄,b̄))` whose `cond_elim` gives the equation.
     `compat_closure` then turns `rcompat` into the `compat` both `lift_beta`
     and `lift_in_funspace` carry.
  2. **The `fs`/`dprod` seam, and this is the piece to size first.**
     `lift_in_funspace` is stated over **`fs`**, and *no interpreted `Π` in mini
     is ever an `fs`*: the `Fs` variant of `PiShape` was removed at §12, and
     `Interp::fs`/`fs_app`/`fs_typing` have no callers outside `interp.rs`
     (read, not inferred). So `⟦α → β⟧` is `dprod(h⃗,A)` and
     `⟦Quot α r → β⟧` is the *same* symbol at a different last argument (§2.1's
     domain-slot property, which `crate::quot`'s `u = 0` `Prim::Lift` arm
     already relies on). The bridge is
     [`derived::ext::dprod_const_fibre_n`] — `⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A →
     b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))`, built, exported, **no consumer
     today** — and it is wanted **twice**, once at `A` to get `f̄ ∈ fs(A,B)` in
     and once at `quot(A,R̄)` to get `lift(A,R̄,f̄) ∈ dprod(h⃗,quot(A,R̄))` back
     out. Its premise is a pointwise constant-fibre family, which is
     `Closed::discharge`'s shape.
  3. **`124`'s ι rule.** `lift_beta` is the equation and its two antecedents —
     `compat` and `x ∈ A` — are dischargeable at the redex
     (`QUOT-MODEL.md` §6 finding 4). Piece 1 supplies the first.

  Budget one `beta_spine` at the codomain as `mk` needed, and discount pieces 1
  and 3 by §17 item 4 — every theorem they name is built. Piece 2 is the one
  with nothing built on the mini side.

* **`Quot.sound` at `u ≥ 1`** — 2 pairs, item 4, and **size it as two**:
  `direct.rs`'s `beta_spine` refuses before reflexivity is reached, and behind
  it is a different rule entirely (`q_sound`). This is also where
  `pair_in_graph` gets its first consumer if §17 item 3's bridge rule holds —
  `q_sound` wants `⟨ā,b̄⟩ ∈ R̄` while Lean's `h` arrives curried, which is
  *owing* the pair. Two cautions: `pair_in_graph` is **built and stored** by
  `AccClause::build` today, so "unused" means no consumer of the *theorem*, not
  a dead import; and there are two unrelated `graph_pair`s in the workspace,
  `quot::graph`'s and `cumul::inside`'s.
