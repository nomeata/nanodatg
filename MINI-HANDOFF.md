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

### The rule the first trap actually needs **[Bram]**

> **A compound `cd $W && …` may contain builds and measurements but never a
> `git` write.** Writes belong in a separate invocation, at the repository root.

"Use one invocation" is the rule everyone reads off the recipe, and it does not
protect against putting a `git commit` in that invocation. When one lands there
the commit goes onto the **worktree's detached HEAD** instead of onto `master`
— and *every check you would run to notice agrees with you*, because the
`git status`, the `git add` and the `git log` in the same compound command are
all the worktree's and all look exactly right. It is silent at the point it
happens; the only thing that catches it is `git log` at the root afterwards.

This fired once with the recipe's own warning already on the page, which is why
the rule is restated as a ban on a *kind of command* rather than as a caution
about a directory.

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
* `derived::inductive::motive::cod_at_funspace` **works** — repaired at
  `derived` `c2bd75f`, in two places and not the one re-association four
  records named. The pin is kept and is no longer a tombstone: `rec_dep.rs`'s
  `cod_at_funspace_is_stated_at_a_function_space_and_at_another_target` asserts
  the *statement* — hypothesis `C ∈ fs(W,V)` against a motive that is a `dprod`
  at a constant fibre, and target `⋃V ∪ {∅}` against `DepElim::target`'s
  `⟦Sort u₁⟧`, read off a real run. **[Otto, corrected §30]**
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

`constEv` **210** of 218, `typeEv` **213**, `fullyInterpreted` **146**,
library-gap **0**, threading 4, interpretation-scope 4, **8 pairs waiting**,
`typeEvMasked` **0**, **5** exports block. **`Quot` is done** (all six exports,
both σ) **and so are the nat literals.** Node interpretability is **99.83%**,
and all 13 remaining nodes are `proj`.

| row | pairs | owes |
|---|---:|---|
| `fun-typed-rec-arg(RTree)` | 4 | the *general* construction widened — **not a clause**, and not mini's |
| `recursor(Acc: …rec_acc::pack is not wired)` | 3 | **two** constructions — §17 |
| `iota(RBTree.rec)` | 1 | a route at `whnf`'s ι site, over `IndexedDepRecursor::iota` |

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
**one** bridge.

*(This paragraph's second half read: "`pair_in_graph` still has **no consumer in
`mini/` at all** … what wants that direction is `derived::quot`'s
`q_sound`/`rcompat` and the `ℓ > 0` quotient clause". **Both halves are wrong,
measured at §25.** `Acc.rec` at `u₁ = 0` consumes `pair_in_graph`, twice, and
`graph_pair` not at all — so the bridge with no consumer is neither unused nor
the quotient clause's. The sentence above it, "`step_closed` has it in the same
position, so the eliminator wants `graph_pair` too", is the actual error, and it
is the rule this item states misapplied by the person who stated it:*

> **The rule is about an occurrence, not about a theorem.** `preds_in` occurs
> once in `acc_intro` and once in `ind_step` and it is the *same formula*; in
> the first it is **proved**, so the pair membership is an antecedent held, and
> in the second it is an antecedent **used**, so the pair is owed. Reasoning
> "same position in the statement, therefore same bridge" skips the polarity,
> which is the only thing that decides.

*This is a third instance of `SCOPING.md` §1's fifth category — a mechanism
identified exactly right and then quantified over too widely — and it is the
first where the over-wide quantifier was in a correction rather than in the
thing corrected.*

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

## 18. `Quot` at `u ≥ 1` — closed, all six exports **[Bram]**

`44d4b33` (formation), `2828662` (`mk`), `bd174b8` (`ind`), `9edf304` (`lift`),
`07259cc` (`Quot.sound`), `52ad758` (the computation rule). Green on their own;
`constEv` 197 → **204**, `typeEv` 205 → **212**, `fullyInterpreted` 133 →
**140**, blocked exports 17 → **11**. The seven-pair row is at zero and so is
everything it moved to.

**`QUOT-MODEL.md` §5.1 said no single clause could close one export, and none
did**: it took four clauses, an axiom and a computation rule, in six increments,
each green on its own. The design was written before the work and every
mechanism it states held; what it was wrong about was cost, in the direction
`SCOPING.md` §1 now predicts on both axes.

*(This section read "two of four", then "three of four", then "all four", then
"five of six"; the numbers above are the current ones.)*

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

| primitive | at the split | after `mk` | after `ind` | after `lift` | after `sound` |
|---|---:|---:|---:|---:|---:|
| `Quot.mk` | 4 | **0** | 0 | 0 | 0 |
| `Quot.lift` | 2 | 2 | 2 | **0** | 0 |
| `Quot.ind` | 1 | 2 | **0** | 0 | 0 |
| *(left the family)* | — | 2, as `ind-spec(Eq: …)` | 2 | 3 | **1**, as `iota(Quot.lift)` |

**The family reaching zero is not the row closing**, and the table is the reason
the two are distinguishable: every pair that left did so by *moving*, and the
key it moved to says onto which axis.

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

**9. The `fs`/`dprod` seam is the `fs` retirement's first real cost, and it is
the design working.** This is the worked instance every future library theorem
stated over `fs` will meet, so it is written out rather than left in a commit.

`derived::quot::lift_in_funspace` is stated over **`fs`**. *No interpreted `Π`
in mini is ever an `fs`*: the `Fs` variant of `PiShape` was removed when the
clause retired, and `Interp::fs`/`fs_app`/`fs_typing` have no callers outside
`interp.rs` — read off, not inferred. `fs` was nevertheless **kept in
`derived/`**, deliberately, and the consequence is exactly that such a theorem
reaches an interpreted `Π` through a bridge rather than by coincidence.

The bridge is [`derived::ext::dprod_const_fibre_n`], and it is wanted **twice**
— at `⟦α⟧` to put `f̄` into `fs(A,B)`, and at `quot(A,R̄)` to bring `lift` back
out into a `dprod`. **Two uses is the honest price of one spelling.**

It was an interface with **no consumer**, which on this project is where the
mismatch lives, so it was checked at both positions before anything was built on
it. **It fitted at both, unchanged.** And its hypothesis really had become free:
the fibre of `⟦α → β⟧` is constant — `β` is a binder, so the body mentions no
`x` — so the fibre symbol's own defining axiom *is* the family, via
`symbol_at` + `a1i` + one `gen`, with no scope and no pointwise derivation. A
simplification nobody had exercised, exercised.

**10. All three of `Acc.intro`'s transports reappeared in `rcompat`, at a
different arity, and one β step appeared at a *third* nest.** Two scopes and two
discharges for the quantifiers, with `inst_self` + `curry` at each level because
`Closed::discharge` produces the curried shape and `rcompat` wants the conjoined
one; `graph_pair` composed with `syl`, because `⟨x,y⟩ ∈ R̄` is an antecedent
here too; and `⟦Eq β (f a) (f b)⟧` is a redex over `⟦Eq.{v}⟧`'s stored nest, so
`cond_elim` only reaches the equation after it reduces to `eq_set(f̄x,f̄y)`.
Counting the whole family: the sixth category's upward half fired at **five**
distinct nests across four clauses (`Quot`, `Quot.mk`, `Eq`, and twice in
`ind`), and never once did a note mention it.

**11. `ci/check-mini-scope.sh` caught a real I3 violation, and the grep has a
blind spot worth knowing.** A `Thm::gen` where `gen_all_checked` belongs — the
check found it. Two *sibling* calls in the same module went through
`derived::gen_all`, which the textual grep cannot see, and they were equally
wrong for the same reason: `derived`'s theorems are unconditional by
construction and mini's `Γ` is live, so the side condition is real here and
vacuous there. All three are checked now. **A path-based ban catches the
spelling, not the route**, and `derived::gen_all` is a live route into
`Thm::gen` from any crate.

**12. `Quot.sound`'s two blockers in series, and the first was not what its
label said.** `ind-spec(Eq: type former spine)` was `direct::eq_refl_bottom`
hardcoding `inst: vec![0]`: at `u = 1` it fetched `⟦Eq.{0}⟧`'s nest, so the
`beta_spine` met a `⟦Sort 1⟧` argument against a `⟦Sort 0⟧` domain. **A
hardcoded level, not a spine defect** — and a latent bug for any `Eq` above
`Sort 0`, not only for this axiom. Behind it, the second blocker was exactly as
sized: the two sides are two different classes, reflexivity is the wrong rule,
`q_sound` is the right one. `direct::eq_bottom` now takes the level and an
optional equation, `Direct::eq_intro` is `eq_refl`'s rule with the equation left
to be supplied, and the equation is checked against the arguments `ctor_bottom`
**inferred**.

Worth naming as a shape: **a blocker whose label names a mechanism can be a
mis-parameterised call to that mechanism rather than a defect in it.** Nothing
about `beta_spine` was wrong; it was handed the wrong nest.

**13. The bridge rule passed its real test.** §17 item 3 — *a bridge is chosen
by which side of the implication the consumer stands on, not by which of
constructor and eliminator it is.* Three consumers (`Acc.intro`, and both walks
in `Quot.lift`'s `rcompat`) all **held** the pair and all wanted `graph_pair`;
all three stand on the same side, so none of them could distinguish the rule
from a coincidence. `q_sound` wants `⟨ā,b̄⟩ ∈ R̄` as a **premise** — the first
consumer anywhere that *owes* it — and `pair_in_graph` is what fits. The theorem
had been built and stored since `Acc`'s apparatus landed with no consumer of any
kind, and this is it.

**14. The computation rule, and `§6` finding 4 names neither β step.** The note
says `lift_beta`'s antecedents — `compat(A,R̄,f̄)` and `ā ∈ A` — are dischargeable
at the redex, and they are; what it does not say is that **the redex is not in
`lift_beta`'s shape until both nests have been walked**. Down
`⟦Quot.lift.{u,v}⟧`'s to `lift(A,R̄,f̄)` and down `⟦Quot.mk.{u}⟧`'s to
`class(A,R̄,ā)`. The sixth category's upward half, twice more.

Two mechanical facts about `whnf`'s ι site, both read off `iota_dep` before
writing and both load-bearing:

* **`step!` lifts a leg over the arguments still on the stack**, so the route
  must return **one** equation about the whole spine. A per-level leg would have
  to be composed afterwards, and composing afterwards is `Gap::ConvCompose`.
* **The nest is five deep and the spine is six long.** `⟦Quot.lift α r β f h⟧`
  is the clause; the major is applied *to* it. So `beta_spine` runs on five and
  the major is lifted over by one `congr` — which is also what makes the result
  one equation.

**15. The `compat` memo question, answered by building the consumer.** §2's
register has a shape — a value computed at a site that outlives nothing — and
`lift_at` deriving `compat` and spending it matches it exactly. It is **not** an
instance, and Fen's discriminator is what tells them apart: *does the consumer
want it at the same terms?* It does not. `lift_at` derives `compat` at the
eliminator nest's own binder variables, under that nest's open scopes, so its
`Γ` cannot be discharged there; `quot_iota` needs it at the redex's own
arguments. **Storing the theorem would store one about the wrong terms.**
`compat_at` is `pub(crate)` and the derivation is shared instead.

That is worth keeping as the register's counter-example: **a value computed and
spent is only §2 if a later site wants it at the same terms.** Everything else
is a shared derivation, and the two look identical until the discriminator is
applied.

### What a successor starts on

`Quot` is closed. The board's remaining rows, in the order the blocker meets
them:

* **`Acc.rec`** — 3 pairs, and §17 item 1's table says it is **two**
  constructions: `u₁ = 0` is `derived::acc::acc_rect` and needs no `rec_acc` at
  all; `u₁ ≥ 1` is `rec_acc::pack` and owes a discharge of `step_typed`, which
  §16 item 2 is explicit is **not** unconditional and is the piece to size
  first. `Acc.intro`'s transports (§17) are the ones `acc_rect`'s `ind_step`
  wants, at a different arity — and after `Quot`, the shape of that reuse is
  known rather than predicted.
* **`iota(RBTree.rec)`** — 1 pair, wiring over `IndexedDepRecursor::iota`, and
  `mini/src/quot_iota.rs` is now a second precedent beside `iota_dep.rs` for
  what a route at that site looks like.
* **`unit-like(PUnit)` 2**, **`fun-eta` 2** — instrumented, and both are
  **conversion certificates rather than clauses**. §20.
* **`RTree` 4** — needs **the general construction widened, not a clause**. A
  clause here would be `direct.rs`'s fourth row, which that module's header
  refuses by standing rule, and which the project goal forbids in as many
  words: *constructions and translations are not special-cased to the tutorial
  tests*. The distinction that keeps `Eq` and `Acc` legitimate is that their
  clauses are **Carneiro's own** (`thesis.txt:2124`, `:2126`) rather than
  accommodations for a corpus file.

### 19. `Nat` — the literal, and the label named the type **[Bram]**

`8e1710c`. `constEv` 204 → **206**, `typeEv` 212 → **213**,
`fullyInterpreted` 140 → **142**, blocked exports 11 → **9**.

**1. `no-interp(Nat)` was about `Expr::NatLit`, not about `Nat`.**
`097_aNatLit`'s blocker prints `⊢ ⟦Nat.{}⟧ ∈ ⟦Sort 1⟧` in the *same report* as
the gap: the inductive had translated for some time through the general route.
What was absent was `infer_type`'s `Expr::NatLit` arm, and the reason named
`Nat` because the literal's declared *type* is `Nat`. That is §18 item 12's
shape again — a label naming the right thing about the wrong object — and it is
now four rounds in a row that instrumenting first paid.

**2. The clause is the expansion and nothing else.**

```text
⟦natLit n⟧ = ⟦Nat.succ^n Nat.zero⟧
```

The literal is expanded and the *expansion* is inferred, so the term and the
certificate come from `Nat`'s carrier and `Nat.zero`/`Nat.succ`'s constructor
typings. Nothing in the clause knows what a numeral is, which is the point: an
accelerated representation would be a second arithmetic to keep in step with the
first, and the owner's brief is explicit that none is wanted yet.

**3. `whnf`'s unfolding is now reflexivity at the term level, and that was
already the intent.** Its comment read *"the unfolding is reflexivity by §7's
choice of `⟦natLit n⟧`; what is missing is `Nat`'s interpretation"* — half
stale, half prophetic. With this clause the two sides are **one term**, which is
what lets that branch emit no `step!` at all. The two unfoldings are now one
`Checker::nat_unfold`: the reduction owing no certificate is *exactly* the
property that they agree, so two spellings that could drift would be the §12
defect at a place where it would be silent.

**4. Two fixtures went stale and both announced it by failing.** `natLit`'s
census row said "**remaining** — needs `Nat`'s interpretation" (the same
misattribution as the ledger label) and moves to `interpreted`, taking node
interpretability to 99.83%. And three `ledger.rs` tests used `Expr::NatLit(3)`
as their *uninterpretable* stand-in; it interprets now, so all three stopped
exercising what they are about. Moved to `Expr::StrLit`, a better fixture
because `Gap::StrLit` has no construction behind it at all where the nat
literal's absence was always one clause away.

> **A fixture chosen for being unsupported has a shelf life**, and the only
> thing that keeps it honest is that it fails loudly when the support arrives.
> These three did, which is the argument for choosing such fixtures by
> *construction absent* rather than by *convenient today*.

---

## 20. `unit-like(PUnit)` and `fun-eta` — instrumented, not built **[Bram]**

Measured, not scoped from the labels, and the measurement changes both rows.
Nothing was built; the tree is clean and this section is the whole of the round.

**1. Neither row is an interpretation clause. Both are conversion
certificates.** All four exports (`102`, `103`, `106`, `107`) have their type
*and* their value interpreted — `⟦val[σ]⟧ = •`, `⟦ty[σ]⟧ = f5x(…)`, and the
type's own typing derived. What is absent in every one is
`⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`, blocked on the certificate for a `def_eq` step. So "2
pairs each, unexamined" is **not** two more clauses; it is two conversion legs,
and the work lives in `is_def_eq`'s threading rather than in §6.2.

**2. Both are filed `Cause::Library` and `fun-eta` is not library debt.**
`ev.rs:396` sends `StructProj | StructEta | UnitLike | FunEta` to
`Cause::Library` as a block. For `fun-eta` that is wrong on the measurement:
`conv::fun_eta_leg` is **in `mini/`**, built and tested, and its only caller is
inside `#[cfg(test)]` (`conv.rs:347`, under the `#[cfg(test)]` at `:223`). The
theorems it stands on — `derived::ext::funspace_ext`, `derived::ext::Eta` — are
built too. **`derived/` is owed nothing here; it is wiring.** A row filed on the
wrong axis is the same defect §17 and §18 keep finding, one column over, and it
would put a successor's estimate on the wrong side of the library boundary.

**3. The `fun-eta` note sizes it by a step that may be unnecessary, and this is
the fourth same-paragraph instance.** `kernel.rs:2703` reads *"The pointwise
family is discharged from a scope the recursion above opens with no endpoints;
wiring `conv::fun_eta_leg` needs that recursion threaded first."* That is the
hardest named step — `try_fun_eta` calls the **`bool`** `is_def_eq` and throws
the conversions away, so threading it is a real piece of work. But
`derived::ext::Eta::eta` is

```text
⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))
```

— **η itself, with no pointwise family anywhere in it.** What is then needed is
to relate mini's own `lam(h⃗,A)` to `Eta`'s `graph(f,A)`: two `lambda_n` graphs
over body symbols that are pointwise equal by the site's own `t_ax`, which is
`lam_ext_n` and is built. So for the case η is actually *about* — the body **is**
`f x`, which is what both corpus exports have — the recursion need not be
threaded at all, and the genuinely recursive case (a body merely *def-eq* to
`f x`) can gap by its own name. Size it that way and check the shortcut before
threading anything.

**4. The `fs`/`dprod` seam is here too, and the two pairs need *different*
bridges.** `fun_eta_leg` and `Eta::eta` are both stated over `fs`; mini's `Π` is
always a `dprod` (§18 item 9). `106_funEta`'s fibre is **constant** — its type is
`∀ (α β : Sort 1) (f : α → β), …` — so `dprod_const_fibre_n` applies, as it did
for `Quot.lift`. **`107_funEtaDep`'s is not**: `∀ (α : Sort 1) (β : α → Sort 1)
(f : ∀ x, β x), …`. That one wants `DProdN::dprod_sub`,
`⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))` — a built field — at
`B := ⋃img(h⃗,A)`. A successor reusing §18 item 9 and expecting it to cover both
will find it covers one.

**5. `unit-like(PUnit)` is the one that may genuinely owe `derived/`, and this
is a flag rather than a finding.** The site (`kernel.rs:2253`) is explicit:
*"the unit-like branch's witness is the structure's subsingleton lemma from the
inductive interpretation, which §9 zone B has not reached."* What it wants is

```text
⊢ ∀x ∀y. (x ∈ ⟦PUnit.{u}⟧ → (y ∈ ⟦PUnit.{u}⟧ → x = y))
```

for a class-(T) carrier with one constructor and no fields. A targeted search of
`derived/` did not find one — `prop::cond_subsingleton` is `Prop`-only
(`[φ] ⊆ 1`) and does not reach a `Sort u` carrier. **I did not exhaust
`derived/`, so the honest statement is that the search found nothing rather than
that nothing exists**, and confirming it is the first thing to do: if it is
absent the row is a `derived/` construction and not mini's, which is the
opposite conclusion from `fun-eta` despite the two sharing a `Cause`.

Note also that `102_unitEta1` is stated at `Unit` and `103_unitEta2` at
`PUnit.{1}`; both reach the same branch, so this is one construction and not
two.

### What a successor starts on

* **`fun-eta`** — 2 pairs, **wiring in `mini/`**, and item 3's shortcut is the
  thing to check before item 3's threading. Item 4 says the two pairs need
  different bridges.
* **`unit-like(PUnit)`** — 2 pairs, and **settle item 5's search first**: it
  decides whether the row is mini's or `derived/`'s.
* **`Acc.rec`** — 3 pairs, §17, and §16 item 2 first: `step_typed` guards
  `pack_iota` and is the only hypothesis in `rec_acc`.
* **`iota(RBTree.rec)`** — 1 pair, a route at `whnf`'s ι site, with
  `iota_dep.rs` and `quot_iota.rs` as precedents.
* **`RTree`** — 4 pairs, `derived/`'s (task #37), not a clause.

---

## 21. `fun-eta` closed, and §20 item 5 was wrong **[Bram]**

`2beff14`. `constEv` 206 → **208**, `library-gap` 4 → **2**, blocked exports
9 → **7**, conversion gaps 37 → **27**.

**1. The shortcut held and the threading was not needed.** `kernel.rs`'s note
sized function η by *"the recursion threaded first"* — and `try_fun_eta` really
does call the `bool` `is_def_eq` and discard its conversions, so that is real
work. It is work for a **general** body. η's own theorem needs none of it:
`derived::ext::Eta::eta` is `⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))`, and
`graph(f,A)` is a `lambda_n` graph exactly as `⟦λx:A. f x⟧` is, so `lam_ext_n`
relates them given a pointwise family — which is the site's **own `t_ax`**,
`t(h⃗,x) = app(f̄,x)`, with no derivation at all.

The generality that buys is named rather than hidden: a body merely **def-eq**
to `f x` declines by name, and that is precisely what the threading would buy.
Both corpus exports have the body literally `f x`, which is what η is about.

**2. One bridge, not two — my own §20 item 4 was one too many.** It predicted
`dprod_const_fibre_n` for `106` and something else for the dependent `107`.
Neither: `DProdN::dprod_sub` — `⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))`,
unconditional, no constant-fibre hypothesis — serves whatever the fibre is, and
`107_funEtaDep` takes the same route as `106_funEta`.

This is **not** a counter-example to §18 item 9, and the discriminator is the
useful part: `Quot.lift` needed the function space at a **named** codomain
because `lift_in_funspace` mentions `B`; η does not care what the codomain is.
**A `dprod`→`fs` bridge is chosen by whether the consumer names the codomain** —
`dprod_const_fibre_n` when it does, `dprod_sub` when it does not.

**3. It was never library debt.** `ev.rs` files
`StructProj | StructEta | UnitLike | FunEta` as `Cause::Library` in one block.
Everything `fun-eta` needed was built, with `conv::fun_eta_leg`'s only caller
inside `#[cfg(test)]`. `library-gap` 4 → 2 is two pairs leaving an axis they
were never on.

**4. §20 item 5 was wrong, and it is the shape of error I flagged it as.** I
wrote that a targeted search of `derived/` for a class-(T) subsingleton lemma
*"found nothing"*, and said explicitly that I had not exhausted it. Exhausting
it — `grep -rn … | grep -v /prop`, whole listing, 44 hits read — finds

```text
⊢ ∀x ∀y. ((x ∈ A_φ(p⃗) ∧ y ∈ A_φ(p⃗)) → x = y)      [LeProp::subsingleton]
```

`derived/src/inductive/family/le_prop.rs:51`. It is exactly the theorem, and
`mini/src/class_s.rs` **already builds a `LeProp` for every class-(S)
declaration** (`ClassS::lp`). `PUnit` is class (S) at every `u` — its resultant
sort is `Sort (Param u)`, so `provably_nonzero` is false and the trichotomy
sends it there whatever `u` is, which is `SCOPING.md` §1's fifth item read the
right way round for once.

**So the row is `mini/`'s, not `derived/`'s** — the opposite of what §20
concluded, and the same axis error as item 3 one row over. Two rows filed
`Cause::Library` in the same block; **neither is library debt.**

The rule the coordinator wrote after a live import was nearly deleted on a
truncated grep is exactly the one that would have caught this: **`head` is safe
for sampling and unsafe for concluding, and the two look identical at the
terminal.** I used the safe phrasing and still reached for the unsafe tool. The
asymmetry is what matters — a wrong count mis-sizes, **a wrong absence claim
points at the wrong crate** — and this one would have sent a `derived/`
construction to Isla that already exists.

### What a successor starts on

* **`unit-like(PUnit)`** — 2 pairs, **wiring in `mini/`**, and the site is
  `Checker::proof_irrel_ev`'s `!prop2` branch (`kernel.rs`), whose comment
  ("§9 zone B has not reached [it]") is stale. The gate above it already names
  the declaration, inside `Gap::UnitLike(name)`. What to fetch is the stored
  `ClassS`'s `lp.subsingleton`, instantiate at the declaration's parameters
  (`PUnit` has none) and then at the two interpretations, and discharge with the
  two memberships `proof_irrel_ev` already holds — `t1.ev` and `t2.ev`. Check
  whether `⟦PUnit.{u}⟧` is `LeProp::set` directly or a redex over a 0-deep nest
  before assuming; at no parameters it should be direct.
* **`Acc.rec`** — 3 pairs, §17, and §16 item 2 first: `step_typed` guards
  `pack_iota` and is the only hypothesis in `rec_acc`.
* **`iota(RBTree.rec)`** — 1 pair, a route at `whnf`'s ι site, with
  `iota_dep.rs` and `quot_iota.rs` as precedents. **Tell the coordinator before
  starting it** — Isla needs `iota.rs`, `step.rs` and `rect.rs` at her step 4.
* **`RTree`** — 4 pairs, `derived/`'s, not a clause.

---

## 22. `unit-like` closed — and the `Cause::Library` block was wrong twice **[Bram]**

`cbab786`. `constEv` 208 → **210**, `library-gap` 2 → **0**, blocked exports
7 → **5**, conversion gaps 27 → **15**.

**1. The theorem was `LeProp::subsingleton` and mini already held it.**
§21's correction stands: `mini::class_s` builds a `LeProp` for every class-(S)
declaration, and `PUnit.{u}` is class (S) at every `u` — its resultant sort is
`Sort (Param u)`, so `provably_nonzero` reads **false**, and the trichotomy runs
on the declaration's own level *expression* rather than on the ground σ.

**2. The one thing that was not obvious, and it is a general fix rather than a
case.** `103_unitEta2` landed immediately; `102_unitEta1` did not, and the
difference is that `102` is stated at **`Unit`** where `103` is stated at
`PUnit.{1}`. **A corpus with only the `PUnit` spelling would have shipped this
silently** — the two exports differing is a coincidence doing the work a fixture
should, and it is worth assuming the next such transport has no `102` to catch
it. `Unit` is a definitional abbreviation, so `⟦Unit.{}⟧` is a *fresh
symbol* with δ's equation beside it — and the two memberships state membership
in the **abbreviation** while `subsingleton` is about `A_φ(p⃗)`.
`Checker::whnf_typing` carries both along that equation. **Any structure reached
through an abbreviation needs this**, so the fix is the general one and the
corpus happened to contain both spellings, which is the only reason it surfaced.

**3. `library-gap` is zero and the *axis* is the finding, not the row.**
`ev.rs` files `StructProj | StructEta | UnitLike | FunEta` as `Cause::Library`
in one block. Both of the two that were reachable turned out to be **wiring**:
`fun-eta` wanted `derived::ext::Eta`, built and unwired; `unit-like` wanted
`LeProp::subsingleton`, built and already in mini's hands. **Neither owed
`derived/` anything**, and a successor sizing either from its `Cause` would have
gone to the wrong crate — which is the same axis error as §18 item 3 and §21
item 3, now at two rows out of two.

The remaining two members of that block, `StructProj` and `StructEta`, are at
zero and **unexamined**. Do not read their `Cause` as evidence either.

Pinned at zero and read as `MINI-DESIGN.md` §0.5 insists: *nothing is owed on
this axis, measured* — not *nothing has reached it*. Both rows that could reach
it did, and both left.

**4. §3's `cd $W` trap fired, and it cost one command.** The recipe's own
warning — *"`cd $W` persists across a compound command"* — caught me: a
compound command that began `cd $W && cargo build` ended with `git add` and
`git commit`, and both ran in the **worktree**, putting the commit on its
detached HEAD instead of on `master`. Nothing was lost (the worktree's `git log`
showed it immediately, and re-committing from the main tree is one command), but
it is worth recording that the trap survives having been written down, because
the failure is silent at the point it happens: `git status` inside the compound
command reports the *worktree's* status and looks exactly right.

**5. There is uncommitted `derived/` work in the shared tree.**
`derived/src/lib.rs` (modified) and `derived/src/ran.rs` (new) are Isla's and
are **not** mine; my commit named four `mini/` paths and left them untouched.
Because §3 says every number measured through someone else's uncommitted work is
measured through it, the figures above were taken in a detached worktree at
`8138fcb` and the whole suite was then re-verified in a second worktree at
`cbab786` — 111 + 8 + 8 + 11 green, both `ci/` checks, workspace clean — with
her working-tree files excluded by construction.

### What a successor starts on

* **`Acc.rec`** — 3 pairs, §17, and §16 item 2 first: `rec_acc::pack_iota` is
  **not** unconditional, `step_typed(A,R,T,e)` is the only hypothesis in that
  module and guards it. Two constructions, `acc_rect` at `u₁ = 0` and
  `rec_acc::pack` at `u₁ ≥ 1`; size the `step_typed` discharge before choosing.
* **`iota(RBTree.rec)`** — 1 pair, and **held**: it consumes `RecArg::app`'s
  contract, which Isla's fibre widening is changing (`app` cannot stay
  unconditional in the general form, which reaches `ctor.rs` and `iota.rs`).
  Ask the coordinator before starting; `iota_dep.rs` and `quot_iota.rs` are the
  two precedents when it unblocks.
* **`RTree`** — 4 pairs, `derived/`'s, not a clause.

---

## 23. `Acc.rec` — the `step_typed` discharge, sized **[Bram]**

Sized, not built. §16 item 2 says `rec_acc::pack_iota` is **not** unconditional
and that `step_typed` is the piece to size before starting; this is that sizing,
read off `derived/src/rec_acc.rs` and the corpus's own two exports.

**1. What the hypothesis actually demands.**

```text
step_typed(A,R,T,e) := ∀x. (x ∈ acc(A,R) →
                         ∀i. (i ∈ ih_bound(A,T) → step(e,x,i) ∈ T))
step(e,x,i)         := app(app(app(e,x),•),i)
ih_bound(A,T)       := 𝒫(prod(A, 𝒫(prod(1,T))))
```

The module header calls `ih_bound` being a power set rather than a function space
a *weakening* — "so no attempt ever has to be proved total to be usable", and it
makes the theorems stronger. **At a Lean minor premise it is the whole cost.**
`ih_bound(A,T)` contains `∅` and every non-single-valued junk relation, while
`⟦∀y (hr : r y x), C y (h y hr)⟧` — the `ih` binder's own interpretation, which
is what `⟦e⟧`'s typing constrains — is a `dprod`, i.e. only total sections. So
the quantifier ranges strictly wider than the certificate in hand, and **no
transport closes the gap**: the discharge has to say something about `e` applied
outside its domain.

**2. What makes it dischargeable at all, and it is not in any note.** `app` off
the domain is `∅` — `derived::funcs::app_off_domain`,
`⊢ ∀f ∀a. ((¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅)`. So the obligation at a junk `i` is
`∅ ∈ T`, and **`T` is a universe rung**: `Acc.rec.{u₁,u}`'s target is `Sort u₁`
and `rec_acc` is non-dependent in `T`, so the recursor is typed into `⟦Sort u₁⟧`
first and refined afterwards, exactly as `rec_dep`'s `COD` premise does.
`Rung::empty_mem` is `⊢ ∅ ∈ Uₙ`, a field.

*(This item's first sentence read "`⟦e⟧` is a **λ-nest**, so `app` off the
domain is `∅`", and item 3 derived `app_off_domain`'s antecedent from "a member
of `lam(h⃗,D)` is `⟨d, t(d)⟩` for `d ∈ D`". **The conclusion holds and that route
does not exist at either remaining σ.** At `117` σ `(1,1)` the minor `e` is a
**binder of the recursor's own nest**, so `⟦e⟧` is a scope variable and there is
no `lam` term to take apart — only its typing is in hand. What delivers the
antecedent instead is `dprod`'s own defining condition, one conjunct along:
`f ∈ dprod(A) ↔ (f ∈ fs(A,⋃img(A)) ∧ ∀x. (x ∈ A → app(f,x) ∈ b(x)))`
(`derived::ext::dprod`), and `fs(a,b) ⊆ 𝒫(prod(a,b))`
(`derived::funspace::space`). So `⟨i,y⟩ ∈ app(app(ē,x),•)` forces `i ∈ D`
whatever `ē` is, and the contraposition is off the **type**, never off the term.
That is strictly better than the route named — it is what makes the discharge
work at a variable minor — but anyone following item 3 as written would look for
a λ-nest that is not there.)*

Checked rather than assumed on the export that could have refuted it:
`118_accRecReduction`'s motive is `fun x h => Bool`, and I expected `T = ⟦Bool⟧`
— which would have made `∅ ∈ T` **false** and `step_typed` undischargeable.
It is not: `Bool` is the motive's *value* and `T` is the recursor's *target
sort*, `⟦Sort 1⟧`. The distinction is the whole of why this works.

> **`step_typed` is dischargeable only because the recursor is typed into a
> universe.** At any `T` that is a genuine carrier rather than a rung, the junk
> branch demands `∅ ∈ T` and there is nothing to prove it with. Anyone reusing
> `rec_acc` at a non-rung target should expect it to stop here.

**And this is the second independent instance of one property of the design.**
The same question was answered from the other side of the codebase for the
class-(T) recursor: `derived::inductive`'s theorems are general in `T` — it is a
bound variable and nothing in the construction or its ι spends a rung, counted
across the whole stack — **but the only live discharge of `COD` pins `T` to a
rung**, because `crate::rec_dep::cod_at_rung` spends `Rung::transitive` and
`Rung::empty_mem`. This one spends `Rung::empty_mem` for the same reason at a
different construction, reached without knowing of the other.

> **The theorems are universe-agnostic; the discharges are not.**

Two constructions, two independent derivations of the same constraint, the same
two rung facts. It is a property of the design and not of either module, and it
is what task #43's optimisation rests on — so it is written here rather than
left to be found a third time.

**3. The shape, and every ingredient is built.**

```text
∀x ∈ acc(A,R̄). ∀i ∈ ih_bound(A,T).
  i ∈ ⟦ih's type⟧   →  step(ē,x,i) ∈ T      three application rules off ē's typing
  i ∉ ⟦ih's type⟧   →  step(ē,x,i) = ∅ ∈ T  app_off_domain, then Rung::empty_mem
```

A **case split on domain membership** — classical, and no note mentions it — plus
the off-domain lemma, plus the three-level walk (`cond_app` at the `h` binder,
`dprod_app` at `ih`). `app_off_domain`'s antecedent `¬∃y. ⟨i,y⟩ ∈ app(app(ē,x),•)`
comes from the **dprod's** own defining condition, per item 2's correction.

Apply §17 item 4's discount: the hardest step named by §16 item 2 is the
discharge itself, and everything it stands on — `app_off_domain`, `empty_mem`,
both application rules — exists. What is genuinely new is the
case split and the plumbing around it.

*(Two corrections, opposite in sign, and both are `SCOPING.md` §1's two axes on
this paragraph. **Down**: the case split costs about two lines. `Formula::or(φ,ψ)`
unfolds to `¬φ → ψ`, so excluded middle at `φ` is `imp_refl(¬φ)` — free — and
`derived::hyp_or_elim` takes it from there. **Up**: "the three-level walk" is
four steps, not three; the third `dprod_app` lands `step(ē,x,i)` in
`app(app(C̄,x),•)`, and getting from there to `T = ⟦Sort u₁⟧` is one
`Rung::transitive`, the same step `rec_dep::cod_at_rung` takes. Applying the
`h` binder also needs `• ∈ ⟦∀y, r y x → Acc α r y⟧` at an arbitrary accessible
`x`, which is **A4**, `derived::acc::acc_pred_closed` — a theorem the item names
nowhere.)*

**4. The split is still two constructions and neither closes an export.**
`117` σ `(0,0)` is `acc_rect` and needs no `rec_acc`; `117` σ `(1,1)` and `118`
are `pack` + this discharge. `118`'s single pair is `Acc.rec.{1,1}`.

*(**σ `(0,0)` landed at §25; and this item is the sizing's real error.** "`pack`
+ this discharge" is not what the `u₁ ≥ 1` half is made of — §25 item 3 has the
measured list, and `step_typed` is one of four pieces, not the piece. The one
this item could not have seen is that `derived::rec_acc` is **non-dependent**:
it recurses into a fixed `T` and has no analogue of
`derived::inductive::DepRecursor::typing`, so "refined afterwards" in item 2 is
not a step, it is a **second `acc_rect` induction** with its own new content.)*

### What a successor starts on

* **`Acc.rec` at `u₁ ≥ 1`** — item 3's shape, and item 2 is the thing to confirm
  first at whatever σ is being built: if `T` is not a rung, stop and say so.
* **`Acc.rec` at `u₁ = 0`** — `acc_rect`, `117` σ `(0,0)`, and §17's transports
  are the ones its `ind_step` wants.
* **`iota(RBTree.rec)`** — held; the `RecArg` contract is in motion.
* **`RTree`** — `derived/`'s.

---

## 24. Two bridge-choice rules, and the handoff **[Bram]**

### The rules belong together

Both came out of wiring `derived/` theorems to interpreted terms, three rounds
apart and at unrelated constructions, and they have the same shape: **look at
what the consumer's statement mentions, not at what the bridge is called.**

| the pair | what decides | measured at |
|---|---|---|
| `graph_pair` / `pair_in_graph` | **which side of the implication the consumer stands on** — holding the pair or owing it | §17 item 3, §18 item 13 |
| `dprod_const_fibre_n` / `dprod_sub` | **whether the consumer names the codomain** | §18 item 9, §21 item 2 |

Both were got wrong first by their names. `graph_pair`'s doc said "the direction
the **eliminator** needs" and `pair_in_graph`'s "the direction the
**constructor** needs"; measured, `Acc.intro`, `Acc.rec` and `Quot.lift`'s
`rcompat` all *hold* the pair and all want `graph_pair`, and `q_sound` is the
first consumer anywhere that *owes* it. And §20 predicted two different `fs`
bridges for function η's two exports; `dprod_sub` serves both, because η does
not name a codomain where `lift_in_funspace` mentions `B`.

**The generalisation worth carrying to the next such pair**: a two-directional
lemma pair in `derived/` is documented by its *author's* consumer, and the
author had one. Read the consumer's own statement instead — which side of the
implication it stands on, and which of the bridge's variables it mentions.

### Runway, named

I am handing off, and calling it **before** the next construction rather than
inside it — Sol's reason at §16, and the fourth time this run that stopping at a
clean commit has cost nothing. `Acc.rec` is a fresh case-split derivation with
genuinely new content (§23 item 3), and starting it now would be signal 3:
committing an artifact worse than the one I would want.

Accuracy held throughout. Every derivation this run compiled and produced its
intended ledger delta on the first attempt; the only failures were stale
ratchets, stale fixtures, two missing `use` lines and one I3 violation, each
named by a tool rather than diagnosed from a wrong run. Two process slips are
recorded rather than left to be inferred: a scripted `replace(…, 1)` that hit
the wrong occurrence (ruled a tooling hazard, did not recur), and §3's `cd $W`
trap, now restated there as a ban on a kind of command.

### What this run moved

`constEv` 197 → **210** of 218, `typeEv` 205 → **213**, `fullyInterpreted`
133 → **146**, blocked exports 17 → **5**, waiting 21 → **8**,
`typeEvMasked` 1 → **0**, `library-gap` 4 → **0**.

Closed: `Acc.intro`'s typing; all four `u ≥ 1` quotient clauses, `Quot.sound`
and `Quot.lift`'s computation rule (**`Quot` entire — six exports, both σ**);
nat literals; function η; unit-like η.

### What a successor starts on

1. **`Acc.rec`**, 3 pairs, two constructions. §23 is the whole sizing and it is
   the only thing between a successor and the build. Confirm §23 item 2 at
   whatever σ is being built *before* anything else: **if `T` is not a rung,
   stop and say so.** *(Half spent: `u₁ = 0` landed at §25, which also records
   that "§23 is the whole sizing" was wrong by three pieces, and that the
   precondition holds at both remaining σ.)*
2. **`iota(RBTree.rec)`**, 1 pair — held while the `RecArg` contract moves. Two
   precedents when it unblocks: `iota_dep.rs` and `quot_iota.rs`.
3. **`RTree`**, 4 pairs — `derived/`'s fibre widening, **not a clause**. The
   project goal forbids the shortcut in as many words; what keeps `Eq` and `Acc`
   legitimate is that theirs are Carneiro's own clauses (`thesis.txt:2124`,
   `:2126`) rather than accommodations for a corpus file.

### The four rules this run paid for

* **Instrument before scoping** — seven for seven, and four rounds running the
  label named something other than what was missing: a *type* where the clause
  was absent (§19), a **mis-parameterised call** to a mechanism that was fine
  (§18 item 12), a constructor under an eliminator's row (§17), and a
  `Cause::Library` block wrong at two rows out of two (§22 item 3, whose
  remaining members are at zero and **unexamined** — their `Cause` is not
  evidence either).
* **Apply both corrections to the same paragraph.** `SCOPING.md` §1's two axes
  are independent, and a note is routinely optimistic about a certificate's cost
  and pessimistic about a construction's size *in the same sentence*. Applying
  them together is what got `Quot.ind` and `Quot.lift` sized right in advance.
* **`head` is safe for sampling and unsafe for concluding.** §21 item 4 is my
  own instance: I used the safe phrasing and the unsafe tool, and the absence
  claim would have sent `derived/` a construction that already existed.
* **A value computed and spent is only §2 if a later site wants it at the same
  terms** — §18 item 15, the register's counter-example, and what makes the
  discriminator worth more than the list.

## 25. `Acc.rec` at `u₁ = 0` — landed, and §23's route is not the one that exists **[Juno]**

`5658439`. Green on its own; measured over the whole tutorial corpus, before and
after, by summing every `ledger` and `evidence` row:

| counter | before | after |
|---|---:|---:|
| `constEv` | 210 | **211** |
| `valuesOk` | 211 | **212** |
| `threading-incompleteness` | 4 | **3** |
| `waiting:recursor(Acc: …)` | 3 | **2** |
| everything else | — | *bit-identical* |

`pairs` 218, `typeEv` 213, `typesOk` 213, `typeEvMasked` 0, `library-gap` 0,
`interpretation-scope` 4, `fullyInterpreted` 142: unchanged. Per-declaration,
`117_accRecType` σ `(0,0)`'s **value** is the one obligation that moved; σ
`(1,1)` and `118` are untouched and now wait on a reason that says which of the
two rules they want. `fullyInterpreted` not moving is §23 item 4 holding
exactly: neither `Acc` construction closes an export alone.

**Two corpus numbers in the briefing do not reproduce, and they are worth
correcting before the next scope is written on them.** Measured at `ffba4b1`,
*before* this run's change: `fullyInterpreted` is **142**, not 146, and the
blocked exports are **4**, not 5 — `115`, `116` (both `fun-typed-rec-arg(RTree)`)
and `117`, `118`. `waiting:iota(RBTree.rec)` is one *pair*, and it is in a file
that is not blocked, which is how a five-file count and a four-file count can
both come from looking at the same run. The measurement is a `--verbose` sweep
of the 91 exports summing `ledger`/`evidence`; a baseline worktree at `ffba4b1`
is what makes it a delta rather than a reading.

**1. The bridge finding, and it is a rule about occurrences.** §17 item 3 is
corrected in place and so is `mini/src/acc.rs`. `Acc.rec` wants
**`pair_in_graph`**, twice, and `graph_pair` not at all — the opposite of what
§17 predicted, and the prediction failed inside a paragraph whose whole subject
is how to choose between the two. `preds_in` is one formula occurring in
`acc_intro` (where it is *proved*, so the pair is held) and in `ind_step` (where
it is an *antecedent*, so the pair is owed); §17 read "same position in the
statement" and stopped there.

> **Same formula, opposite polarity, opposite bridge.** The discriminator is the
> occurrence, not the theorem the occurrence is in.

That also retires the standing question §17 left open — *which check fires first
for `pair_in_graph`, once a consumer exists* — with the answer that its first
consumer was never going to be the quotient clause.

**2. A hypothesis that is not a binder's typing.** `crate::scope` gained
`Scopes::assume`, the second and last call to `Thm::assume`. `ind_step`'s
induction hypothesis is `∀y. (y ∈ A → (⟨y,x⟩ ∈ R̄ → (y ∈ acc(A,R̄) ∧ φ(y))))` —
a formula, not a membership — so `Scopes::open` cannot take it, and every
mini-side step it feeds (`cond_app`, `cond_intro`, `beta_spine`,
`point_of_proof`, `to_cond_fibre`) takes and returns a plain `Γ ⊢ t ∈ S`. The
alternative was a `K → …` variant of each of them, which is the whole reason the
sequent judgement exists. It opens no variable, discharges to `φ → ψ` with no
`∀`, and lives on a stack of its own so that `get`, `len` and every `bvar` index
keep counting binders only.

**Two things about it that a reader would not guess.** The stacks have to
interleave, and `close` now asserts it: an assumption made *under* a binder must
be discharged before it, or `gen_checked` is asked to bind a variable free in a
live hypothesis. And the derivation must thread the caller's **one** `Scopes`
rather than opening a fresh one per helper — a second stack loses the LIFO order
between the four live hypotheses, and the `debug_assert` that catches it is
`close_checked`'s, which is why nest bottoms in this codebase call plain `close`:
their theorems legitimately carry the *checker's* binder hypotheses, which no
local `Scopes` knows about. That convention was already there in `rec_dep` and
`acc.rs` and is written down nowhere; it is now the reason `close_checked` says
"in the checker".

**3. What the `u₁ ≥ 1` half is actually made of.** §23 sized `step_typed` and
called it the whole of what stands between a successor and the build. Measured
against `derived::rec_acc`'s interface, it is one of four pieces:

| # | piece | state |
|---|---|---|
| 1 | `step_typed(A,R̄,⟦Sort u₁⟧,ē)` | §23 item 3, with item 2 and item 3's corrections above |
| 2 | the **dependent refinement** — `app(accrec,z) ∈ app(app(C̄,z),•)` | **not sized anywhere**; a second `acc_rect` |
| 3 | the term: `pack`, `pack_app`, the nest, the store | small, `rec_dep::dep_bottom`'s shape |
| 4 | the **ι rule** at a use site, for `118`'s value | `iota_dep.rs`'s shape; `118` is a reduction test |

**Piece 2 is the one that is genuinely new, and the reason is a property of the
library.** `derived::rec_acc` recurses into a **fixed set** `T`: its exports are
`accrec ∈ fs(acc(A,R),T)`, `app(accrec,y) ∈ T`, and the ι rule — and there is no
analogue of `derived::inductive::DepRecursor::typing`, which is what carries a
class-(T) eliminator into `app(C,t)`. Lean's obligation is
`⟦Acc.rec α r C m a t⟧ ∈ app(app(C̄,ā),•)`, a fibre. So the typing has to be
*refined* from `T` down to the motive, and the only tool for that is another
`acc_rect`, at

```text
φ(z) := app(accrec(A,R̄,T,ē), z) ∈ app(app(C̄,z),•)
```

whose `ind_step` rewrites `app(accrec,x)` by ι and then applies `ē` at `x`, `•`
and `ih(accrec,A,R̄,x)`. That last application is the cost: it needs

* `ih(accrec,A,R̄,x) ∈ ⟦∀ y (hy : r y x), C y (h y hy)⟧` — `derived`'s `ih` is a
  set of rows `⟨y, cval(ep(R̄,y,x), app(accrec,y))⟩` and Lean's is a `dprod` of
  `dprod`s, so this is *three* separate facts: the rows are sections
  (`cval(c,v) ∈ dprod(const V, c)`), the whole is a section over `A`, and
* **`ep(R̄,y,x) = ⟦r y x⟧`** — a conditional singleton against Lean's own
  relation value. They are equal only by Extensionality over **both** graph
  bridges plus "`⟦r y x⟧` is a truth value", and this is the one place
  `graph_pair` and `pair_in_graph` are wanted *together*. Nothing states it
  today.
* and the induction hypothesis feeds exactly the fibre condition, `φ(y)`, which
  is why it has to be an induction and not a direct typing.

**4. §23's precondition, re-confirmed at the σ that will be built.** `T` is
`⟦Sort u₁⟧` at both remaining pairs and `u₁ = 1` at both — `117`'s recursor type
prints `Sort (0+1)` at the motive binder, and `118`'s occurrence is
`Acc.rec.{1,1}`, whose `motive_level` is `rec_inst[0]`. `⟦Sort 1⟧` is `U₁`, a
rung, so `Rung::empty_mem` is available and the junk branch closes. Bram's
`Bool`-is-the-motive's-value distinction holds. **The precondition survives; the
justification printed beside it does not** — see item 2's correction, which is
what would have stopped a successor who went looking for `⟦e⟧`'s λ-nest.

### Why this is a handoff and not a pause

Signal 3, called before it fires, and the reason is item 3's table. `u₁ = 0` is
landed, committed and measured; `u₁ ≥ 1` is four pieces of which the largest is
one nobody has sized, and starting it here would land the first of four and leave
the other three described by a person who had stopped reading. §10's rule is that
the cheapest moment is *before* the next construction, and this is a boundary
between two constructions rather than a point inside one.

Accuracy held: every derivation compiled and produced its intended ledger delta,
and the two failures were both the same one — a `debug_assert` in
`Scopes::close_checked`, which named the invariant precisely enough that the fix
was mechanical both times (thread one stack; use plain `close` in a nest bottom).
Neither reached a measurement. One process note: the shared tree moved under me —
`46cfebd` was HEAD at the start and `ffba4b1` by the time I measured — so the
baseline worktree is against `ffba4b1` and the delta above excludes Mira's two
`derived/` commits by construction rather than by assumption.

### What a successor starts on

1. **`Acc.rec` at `u₁ ≥ 1`**, 2 pairs — item 3's four pieces, in that order.
   Piece 2 is the one to size first, and the question to answer before writing
   anything is whether `ep(R̄,y,x) = ⟦r y x⟧` belongs in `mini/` or is a
   `derived/` lemma about `rel_graph`; it is stated in `derived`'s vocabulary on
   one side and mini's on the other, which is the seam §16 item 3 named.
2. **`iota(RBTree.rec)`**, 1 pair — still held on `RecArg`'s contract; `d4480c3`
   and `ffba4b1` are Mira's two landings on it. *(**Closed at §26.** The hold
   was already released and the row is gone; `mini/src/iota_ix_dep.rs`.)*
3. **`RTree`**, 4 pairs, 2 blocked exports — `derived/`'s. *(**And more of it
   is `derived/`'s than this line says** — §26 item 2 measured it: all four
   pairs reach `⟦RTree.rec⟧`, which `GenRecursor::build` refuses.)*

## 26. `iota(RBTree.rec)` closed, and `RTree` is not a `mini/` row **[Perrin]**

Two commits. Measured over the 91 tutorial exports by summing every `ledger`
and `evidence` row, against a sweep taken at `4ba0904` before either landed:

| counter | before | after |
|---|---:|---:|
| `constEv` | 211 | **212** |
| `threading-incompleteness` | 3 | **2** |
| `waiting:iota(RBTree.rec)` | 1 | **0** |
| conversions `gapped` | 15 | **0** |
| exports that stop | 5 | **4** |
| everything else | — | *bit-identical* |

`pairs` 218, `typeEv` 213, `typesOk` 213, `fullyInterpreted` 142,
`interpretation-scope` 4, `waiting:fun-typed-rec-arg(RTree)` 4: unchanged.
Per declaration, `077_RBTree.id_spec`'s **constant typing** is the one
obligation that moved — the `--block` report named it, not the type's — and
`077` now reports `typeEv=3 constEv=3 fullyInterpreted=3`, no waiting row.

**`gapped` reaching zero is the number worth quoting.** Every conversion the
tutorial corpus asks for now carries a certificate. Read the zero twice, as
§0.5 says: it is *nothing left uncertified*, not *nothing reached* — `proved`
is 11,071,428 and `moved` went 8857 → **9888**, and a fired ι moves endpoints
where a gapped one does not. The rise is what distinguishes the two readings.

**1. The row was three quarters built, and the note that sized it named the
part that had landed.** `SCOPING.md` §1's *size* axis, fourth instance, and
this is the first time it fired on a note whose hard step had been built by
somebody else in the meantime. §8's construction 3 says the obstacle is
`minor_ix::transport`, one level below `rec_ix_dep`, and it is right — but
`minor_ix::transport_at` and `Source` already exist, `ind_spine_at` already
takes parameter *expressions*, and the de Bruijn shift §8 called "the one part
nobody has written" is written, at `minor_ix.rs`'s `Slot::Rec` level. Both
halves of the generalisation had landed with **no external caller**, which is
why a reader of the ledger could not see it and a reader of the note could not
either.

> **Before accepting a size, `grep` for the hard step's *name*, not only for
> its consumers.** A generalisation landed ahead of its consumer looks exactly
> like a generalisation not landed, from every instrument except the source.

What was left was one factoring and one module. `rec_ix_dep::premise_at`
(`a9c49d8`, committed alone and measured bit-identical) is `rec_dep::pre_at`
one table along: `PRE = ICOD ∧ IDEP` from an `At` rather than from a nest
position, with `sources: None` the eliminator's own frame and `Some` the use
site's. Then `mini/src/iota_ix_dep.rs`, which is `iota_dep.rs`'s four steps
with §8's three differences, all in the statement and all read rather than
reconstructed:

* `Hᵢ` in **declared** field order against a `∀y⃗∀t⃗` prefix in plains-then-recs
  — `iota_atoms` and `iota_vars` are exported precisely because they differ;
* a recursive atom at `ind(p⃗, d⃗ᵢⱼ)` and not at `W`, which is `ctor_ix`'s own
  two moves (β down the former's nest, then `index_congr` reversed) once per
  child rather than one `w_eq` for all of them;
* step 4's reverse chain carrying the child's index vector, whose memberships
  are the *inferred* `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` and exist nowhere but at the
  constructor's own Lean binder type.

It compiled and produced its ledger delta on the first attempt, and so did the
two unit tests over `rec_ix_prop::tests::indexed_env` — `(k,m)` at `(0,0)`,
`(1,1)` and `(2,2)`, the last with its two children at *different* index
vectors and its minor returning the **second** hypothesis.

**2. `RTree` is `derived/`'s row entire, and the briefing's two claims about it
are both wrong.** Instrumented before scoping — nine for nine — and the finding
is the one that was asked for before any work-around:

```text
115  rTreeRec       val = RTree.rec.{0}                       (bare constant)
115  rTreeRec       val = RTree.rec.{1}
116  RTree.left     val = fun _ => RTree.rec.{(0+1)} … #0
116  rtreeRecReduction                                        (a reduction test)
```

**All four pairs reach `⟦RTree.rec⟧`.** "The recursor is never reached" is
false at every one of them: `115`'s value *is* the recursor, so `⟦val[σ]⟧` is
`⟦RTree.rec.{u₁}⟧` and nothing else, and `116`'s two are spines over it. So
lifting `zoneb`'s `Gap::FunTypedRecArg` on the strength of a carrier carry
closes nothing.

**Where they stop is one function earlier than this paragraph said, and the
correction is the fifth refuted `RTree` claim.** *(This read: "`crate::recursor`
routes them to `Interp::dep_recursor`, which is `GenRecursor::build` then
`DepRecursor::build`, and both refuse on
`Inductive::has_function_typed_recs`.")* They never reach either builder.
**`zoneb.rs:1544` refuses the constructor spec** — `is_function_typed_rec` at
the field, inside the walk that builds `DeclSpec` — and `Inductive::build` is
at `zoneb.rs:619`, *after* it. So mini never constructs a `derived::Inductive`
for `RTree` at all, and the guard in `derived`'s two recursor builders is never
consulted for it. Measured the way the label could not be: the `derived/` side
lifted that guard and a full 91-export sweep left
`waiting:fun-typed-rec-arg(RTree)` at **4**, unchanged.

That is `SCOPING.md` §1's fourth category once more — *a mechanism read at the
right place and attributed to the wrong rule*. Both guards exist, both are
about the same property, and only one of them is reached; naming the wrong one
sends the next round to the wrong crate. `RTree`'s mini-side row is
`zoneb.rs:1544` plus `sigma::reindex` at the constructor and at the minor
premise, and it is a `mini/` row, not a `derived/` one.

And the carrier half is not free either. `Ctor::mem` for `RTree.node` is
`⊢ ∀g. (g ∈ fs(Σz:Bool. 1, ind) → node(g) ∈ ind)`, where `Σ(z::γ)` is
`Telescope::ty_of` — a set of **pairs** `⟨b,•⟩`. Lean's field type interprets
to `⟦Bool → RTree⟧ = fs(⟦Bool⟧, ind)`, over `⟦Bool⟧` itself. The two function
spaces have different domains, so the constructor's nest bottom needs a
*reindexing* of `g` along the telescope's tuple/`comp` bijection before
`Ctor::mem` applies — and the recursor's ι would have to agree about which of
the two `g` the pack holds. That is a `derived/` construction and nothing in
`mini/` states it.

> **`derived/`'s widening made the *carrier* expressible; it did not make the
> declaration translatable.** `fibre_values` and `CtorSpec::rec_doms` are real
> and `RTree.node`'s constructor really is derived — over `Σ(z::γ)`, which is
> not the domain Lean's arrow interprets to.

*(One stale line found while measuring, in a file I may not edit:
`derived/src/inductive/carrier.rs`'s `fibre_values` doc says a declaration with
a non-empty `γ` "cannot yet" build a carrier "since `Ctor::mem` still wants
`crate::recarg`'s function at `finord(m)`". `ffba4b1` built exactly that and
the sentence survived it. It is §9's *dump that denies a store* at a doc
comment, and the same exposure: the reason is prose and prose does not
recompile.)* **Both doc defects are fixed — `2f7b22c` and `da2f7df` — and the
second now names the domain mismatch and points at the carry.**

**The carry itself landed at `e81372b`, hours after this paragraph was
written**, and it closes the *second* count and not the first:

```text
⊢ ∀p ∀S ∀g. (g ∈ fs(β₀(p), S) → pull(g, T(p)) ∈ fs(T(p), S))   sigma::reindex_in_funspace
⊢ ∀p ∀g ∀b. (b ∈ β₀(p) → app(pull(g,T(p)), ⟨b,•⟩) = app(g,b))  sigma::reindex_at_tuple
```

`derived/src/sigma/reindex.rs` — `isum::restrict` at `comp₀ = π₁` instead of
`Injⱼ`, restricted to `k = 1` for a stated and measured reason (at `k ≥ 2` the
map is an uncurrying, not a reindexing). `RTree.node`'s `γ₀ = [Bool]` is `k = 1`,
so the theorem covers it, and `reindex_at_tuple` carries **no** typing
hypothesis on `g` — which is what an ι rule would need to decide which of the
two functions the pack holds.

**What that changes for `mini/`, and it is less than it looks.** ~~The
constructor's nest bottom can now be written: `ctor_bottom` would carry the
scope's `g ∈ fs(⟦Bool⟧, ind)` along `reindex_in_funspace` and hand `Ctor::mem`
the pulled function.~~ **The scope does not hold `g ∈ fs(⟦Bool⟧, ind)`** — §29
item 3. `Checker::pi_evidence` has one clause and `⟦Bool → RTree⟧` is
`dprod(b, ⟦Bool⟧)` at a constant fibre, so `ext::dprod_const_fibre_n` stands in
front of `reindex_in_funspace`; it is stored, unread, and was the reader §12
deleted. The bottom is six steps, not four. Wiring the carry alone closes **no pair** — all four
`RTree` pairs need `⟦RTree.rec⟧` and none of them gets a declaration to build it
over. *(This sentence used to explain that by
`derived/src/inductive/recursor.rs:169` and `dep.rs:127` still guarding on
`Inductive::has_function_typed_recs`. Those guards are real and are **not** what
holds `RTree`; see the correction in item 2. The `derived/` side has since
lifted them, and the row did not move.)*

**3. Three ratchets moved and one of them was already red.** Two are mine —
`tutorial_conversion_split`'s reason table, now compared against an **empty**
map, which is the strongest form that assertion has ever taken; and
`tutorial_first_blocker`, which moves from `077` on the `Threading` axis to
`115` on the `Scope` one. The third is not:
`mini/tests/dump.rs`'s `an_unreached_pair_is_named_as_unreached_not_omitted`
**was failing at `4ba0904`**, and it went red at `5658439` — §25's own commit.
`117` σ `(0,0)` stopped blocking, so σ `(1,1)` became *reached* and the file it
asserted about had no "not reached" left in it. `dump.rs` was last touched at
`184bde9`, which is what makes the attribution a read rather than a guess.

> **"Green on its own" has to name which targets ran.** §25's measurement was a
> corpus sweep and its unit tests; `cargo test -p mini` has four targets and the
> integration ones take 70–90 seconds, which is exactly the interval a run
> under time pressure skips. Nothing about the derivation was wrong — the
> ratchet's *witness* had moved and its *property* had not, which is why the
> repair is eleven lines and a marker.

Repaired in place with a marker, per Quinn's convention: the witness is now
`115_rTreeRec`, whose first pair blocks and whose second is never attempted.
It will flip the day `RTree` builds, and the header says so and says to move it
again rather than weaken it.

### What a successor starts on

1. **`Acc.rec` at `u₁ ≥ 1`**, 2 pairs, 2 blocked exports — §25 item 3's four
   pieces, unchanged and unstarted. ~~Piece 2 is still the one nobody has
   sized, and the question in front of it is still whether `ep(R̄,y,x) = ⟦r y x⟧`
   is a `derived/` lemma.~~ **Both halves of that sentence are now answered, at
   `4fa1e50`.** `derived/src/rec_acc/edge_value.rs` states

   ```text
   ⊢ ∀A ∀r ∀y ∀x. ((y ∈ A ∧ (x ∈ A ∧ app(app(r,y),x) ∈ ⟦Prop⟧))
                     → ep(rel_graph(A,r), y, x) = app(app(r,y),x))
   ```

   and the boundary question is settled the way §25 did **not** guess: *both*
   sides are `derived`'s vocabulary — `R̄` is `quot::graph`'s `rel_graph(A,r)`
   and `⟦r y x⟧` is `app(app(r,y),x)`, which that file already calls `holds` —
   so the whole equation quantifies set variables, mentions no interpreted term,
   and **mini's only job is to instantiate it**. The one interpretation-flavoured
   input is a *hypothesis*, `app(app(r,y),x) ∈ ⟦Prop⟧`, which a caller holding
   `r : α → α → Prop` already has. So piece 2's gate is open and what remains is
   the second `acc_rect` itself, the `pack` term, and the ι clause for `118`.
   **This is the row to start on**, and it is now entirely `mini/`-side.
2. **`RTree`**, 4 pairs, 2 blocked exports. The *constructor* count closed at
   `e81372b` (item 2's correction); the *recursor* count did not, and it is the
   one that owns all four pairs. ~~Do not lift `zoneb::ctor_spec`'s decline on
   the strength of the carry: it would move the label without moving a pair, and
   `has_function_typed_recs` still guards both recursor builders.~~ **The second
   half of that is wrong and the first half is still right, for a different
   reason** — item 2's correction. `zoneb.rs:1544` is not *a* guard in front of
   `derived`'s, it is **the** one that fires, and `derived`'s is never consulted
   for this declaration. Lifting `zoneb`'s is now the row's first step rather
   than a label change, and it is a `mini/` row.
3. The ledger is `constEv` **212** of 218 and the residue is two declarations,
   not four exports.

*(Items 1 and 2 were written when both blockers were `derived/`'s and were
corrected in place within the hour, against `da2f7df`. The four commits between
this section's first draft and its correction are `2f7b22c`, `4fa1e50`,
`e81372b`, `da2f7df` — three of the four are answers to item 2 and to §25 item
3, so **the seam this file kept describing as a hand-off cost was closed by
naming it precisely once.** That is the argument for writing a blocker down in
the other crate's vocabulary rather than as "derived/ owes us something".)*

### 26.1 `Acc.rec` at `u₁ ≥ 1` — the precondition confirmed, and a piece nobody named **[Perrin]**

Taken, scoped, **not built**. I am stopping at the boundary rather than inside
the first of four pieces; the reason is at the end. What follows is the part
that is expensive to rediscover, and two items of it are not in §23 or §25.

**1. The precondition holds, and the check is structural rather than a
measurement of one export.** §23 and §25 both say to confirm it first and to
stop if `T` is not a rung.

```text
Tower::at(n)  = Some(Rung) iff n ≥ 1,  with  Rung::set == Tower::u(n)
Interp::sort(n)                        == Tower::u(n)
```

So `T = ⟦Sort u₁⟧` **is** `Rung::set` by construction whenever `u₁ ≥ 1` — the
two are the same term, not two terms that happen to be equal — and
`Rung::empty_mem` is a field on it. Measured at both pairs: `117_accRecType` σ
`(1,1)` and `118`'s occurrence `Acc.rec.{(0+1) (0+1)}`, so `u₁ = 1` at both.

**And `Tower::at(0) = None` is the reason the two clauses had to split at all.**
§16 derived the split from §6.2's `Prop`/value column; it is over-determined,
and the second reason is that the `u₁ ≥ 1` discharge's central fact does not
*exist* at `u₁ = 0`. `U₀` is not a universe — `𝒫{0} = U₀ ∉ U₀` — so there is no
rung to be transitive or to contain `∅`.

Bram's distinction re-checked at the export that could have refuted it, and it
holds: `118`'s motive is `λ a h. Bool`, so a reader looking at the *value* sees
`⟦Bool⟧`, at which `∅ ∈ T` is false. `T` is the recursor's **target sort**,
`⟦Sort 1⟧`. The distinction is the whole of why the discharge works.

**2. `mini` does not reach `derived::rec_acc` at any site — there is no
apparatus accessor, and that is piece 0.** `grep`ped over the crate: the only
occurrences of `rec_acc` outside the module itself are `recursor.rs:164`'s call
to `crate::rec_acc::ensure` and a doc mention in `direct.rs`. `Interp` has
memoised accessors for the `AccClause`, the `WRec` and the dependent recursors;
it has none for `RecAcc`, so every theorem in the interface above is currently
unreachable from the checker. §23 and §25 both size the *derivation* and neither
names the wiring it stands on.

**3. And the accessor has a trap in it, which is the item I most want written
down.** `RecAcc::new(env)` builds its **own** `Sums` and its **own**
`crate::acc::Acc`:

```rust
pub fn new(env: &mut Env) -> Option<RecAcc> {
    let s = Sums::new(env)?;
    let ac = Acc::with_apply(env, &s.ap)?;      // ← a *fresh* carrier
    let base = Base::over(env, s, ac)?;
    RecAcc::over(env, base)
}
```

`Acc::with_apply` mints symbols through `define_abbrev`, so calling it twice
yields **two unrelated `acc` carriers with no equation between them**. The
`u₁ = 0` clause reasons about `AccClause::sets`, and Lean's major premise
delivers `⟦a⟧ ∈ acc(A,R̄)` at *that* one. An accessor built on `RecAcc::new`
would compile, derive, and be about somebody else's set. The correct shape is

```text
Base::over(env, ⟨the prelude's Sums⟩, acc_clause.sets.clone())  then  RecAcc::over
```

`Base::over` does check `ac.sets.up == s.ap.sets.up` and refuses a mismatched
*pairing* — so a wrong `Sums` is caught — but it cannot see that a same-shaped
`Acc` is a different `acc`. **That check is the near miss that makes the trap
worth naming**: it is exactly close enough to be mistaken for a guard against
this.

**4. Piece 1's helper inventory, all present.** `funcs::app_off_domain`,
`acc::acc_pred_closed` (A4, which §23 item 3 names nowhere), `hyp_or_elim` and
`imp_refl` for the case split, `ext::DProd`'s `dprod_sub` and `dprod_members`,
`funspace::funspace_subset_pow_prod`, and `Interp`'s `dprod_app` / `cond_app`.
The step's three levels are `dprod_app` at `x`, **`cond_app` at `h`** — a proof
binder, which is where A4 is spent — and `dprod_app` at `ih`, landing in
`app(app(C̄,x),•)`; one `Rung::transitive` finishes into `T`. §23's corrected
count of four steps is right.

**5. `118`'s obligation is the *type's* interpretation, not the value's**, and
that is worth knowing before sizing piece 4. Its value is `Eq.refl`, already
`⟦val⟧ = •`; what is absent is `⟦ty[σ]⟧`, because the type is
`Eq Bool (Acc.rec … (Acc.intro …)) x` and mentions `Acc.rec.{1,1}` inside. So
`118` wants the **term** (piece 3) to interpret its type at all, and then the ι
rule for `⊢ ⟦val⟧ ∈ ⟦ty⟧`. A successor who reads "`118` is a reduction test"
and starts at piece 4 will find the type will not interpret yet.

### Why this is a handoff and not a pause

**Signal 3, called before it fires.** Piece 0 is unbuilt and unnamed, piece 1 is
a case-split derivation of a couple of hundred lines, and pieces 2–4 follow it;
what I have left is enough to write the first of five badly. §10's rule is that
the cheapest moment is *before* the next construction, and this is a boundary
between reconnaissance and one.

The specific thing I declined to do is land piece 0 alone. It is about forty
lines and would compile — and it would be **a generalisation landed ahead of its
consumer**, which is the exact failure §26 item 1 records from the other side:
`minor_ix::transport_at` sat built and callerless, invisible to the ledger and
to the note, and cost this round a re-derivation of its size. Adding a second
one to that pile to show progress is not worth it. It is specified in item 3
precisely enough to write in one sitting.

Accuracy held for the round: both derivations compiled and produced their
intended ledger delta on the first attempt, both new unit tests passed first
run, and the one red test I found was inherited and is repaired.

### What a successor starts on

1. **`Acc.rec` at `u₁ ≥ 1`**, 2 pairs, 2 blocked exports — piece 0 (item 3, and
   read the trap before writing the accessor), then §25 item 3's four. The
   precondition is **confirmed** and does not need re-measuring at these two σ.
2. **`RTree`**, 4 pairs — `derived/`'s, routed there by the coordinator.
3. The ledger is `constEv` **212** of 218, conversions `gapped` **0**, four
   exports stopping over two declarations.

## 27. `Acc.rec` at `u₁ ≥ 1` — four of five pieces landed **[Ilse]**

Pieces 0–3 of §26.1. Measured over the 91 tutorial exports by summing every
`ledger`, `evidence` and `convs` row, in a **detached worktree at `62e6cbc`**
— see the process note at the end for why that was not optional.

| counter | before | after |
|---|---:|---:|
| `constEv` | 212 | **213** |
| `typeEv` | 213 | **214** |
| `threading-incompleteness` | 2 | **1** |
| `waiting:recursor(Acc: … at u:1)` | 2 | **0** |
| `waiting:iota(Acc.rec)` | 0 | **1** |
| exports that stop | 4 | **3** |
| conversions `gapped` | 0 | **12** |
| conversions `moved` | 9888 | **10145** |
| everything else | — | *bit-identical* |

`pairs` 218, `interpretation-scope` 4, `typeEvMasked` 0, `typeEvOnlyGap` 0,
`unsealed` 0, `movedSealed` 1496, `waiting:fun-typed-rec-arg(RTree)` 4:
unchanged. Per declaration, **two** obligations moved and they are different
obligations:

* `117_accRecType` σ `(1,1)`'s **value**. The export closes —
  `typeEv=2 constEv=2 fullyInterpreted=1`, no waiting row — and it is the first
  `Acc` export to close at all, because §23 item 4 is right that neither
  construction closes one alone and σ `(0,0)` landed at §25.
* `118_accRecReduction`'s **type**. §26.1 item 5 called this exactly: its value
  was already `•`, and what was absent was `⟦ty[σ]⟧`, because the type is
  `Eq Bool (Acc.rec … ) x` and mentions `Acc.rec.{1,1}` inside. So the type now
  interprets, `typeEv` goes 0 → 1, and the pair waits on the **ι rule**.

**`gapped` 0 → 12 is §0.5's zero read the second way, in the direction that
reads as a regression and is not one.** Nothing stopped being certified. All
twelve are one site — `convGap:iota(Acc.rec)`, all of them in `118` — and they
did not exist before because `118`'s type did not interpret, so `whnf` never
reached the ι site to have an opinion about it. `moved` rising by 257 in the
same increment is what distinguishes "the walk got further" from "the walk got
worse"; a total on `gapped` alone cannot.

> **A row can go from zero to nonzero because a blocker in front of it was
> removed.** §26 recorded the zero as *nothing left uncertified*; that reading
> was true and is still true of the eleven million conversions that were being
> counted. What changed is the population.

### 1. The trap was real, and it is now a test rather than a paragraph

§26.1 item 3's `RecAcc::new` hazard is avoided the way it says —
`Base::over(env, ⟨the prelude's Sums⟩, acc_clause.sets.clone())`, then
`RecAcc::over` — in `mini/src/rec_acc_ap.rs`, and
`the_apparatus_is_over_the_clause_s_own_acc` asserts the two symbols and the
pairing. Nothing to correct; it is recorded because *the note is what stopped
it*, and the cost of the note was one paragraph against a class of failure §2
prices at 61% of a round's wall clock.

The apparatus carries four things beside `RecAcc`, and three of them were named
in §26.1 item 4: `Bounded`, **A4**, `edge_value`. The fourth is
`funcs::app_off_domain`, which §23 item 2 names as *what makes `step_typed`
dischargeable at all* and which no note put anywhere; it is derived, not looked
up, and this is its only consumer.

### 2. §26.1 item 4's inventory is right and one of its *rules* is not

> "The step's three levels are `dprod_app` at `x`, **`cond_app` at `h`** — a
> proof binder, which is where A4 is spent — and `dprod_app` at `ih`."

**All three levels are `dprod_app`.** At `u₁ ≥ 1` Lean's minor premise is
`∀ x h, (∀ y hy, C y (h y hy)) → C x (Acc.intro α r x h)`, whose body is
`Sort u₁`-valued and *not* a `Prop`, so `Interp::as_pi` answers `Dep` at every
one of them — §6.2 splits on the **body's** sort and the `h` binder's own domain
being a `Prop` does not enter. A4 is spent exactly where the item says it is,
but not through the rule it names: it is spent producing the *argument* of the
second `dprod_app`, `• ∈ ⟦∀ y, r y x → Acc α r y⟧`, and *that* walk is two
`cond_app` levels deep because those two `Π`s really are `Prop`-valued.

That is `SCOPING.md` §1's fourth category one layer in — a mechanism read at the
right place and attributed to the wrong rule — and it is cheap to avoid: the
clause a `Π` takes is decided by `body_clause`, never by what the binder is.

### 3. `acc_rect`'s `params` differ between the two clauses, and it is not a
difference in the scheme

This cost the one build that a corner walk would have cost anyway, and it is the
sort of thing that reads as a library limitation from a decline.

```text
u₁ = 0   φ(z) = • ∈ app(app(C̄,z),•)                  params = [av, rv, C]
u₁ ≥ 1   φ(z) = app(accrec(A,R̄,T,ē),z) ∈ app(app(C̄,z),•)
                                             params = [av, rv, α, r, C, m]
```

`acc_rect` carves `{z ∈ acc(A,R) : φ(z)}` by one Separation over `params` and
requires **every** free variable of `φ` to be listed. The `u₁ = 0` clause's `φ`
mentions the motive and nothing else, so its list is short and reads as if the
short list were the scheme's shape. The refinement's `φ` mentions `accrec`, and
`accrec` is `accrec(A, rel_graph(A,⟦r⟧), ⟦Sort u₁⟧, ⟦m⟧)` — so all four of the
nest's earlier binders occur in it. `av`/`rv` stay in the list because
`Params { a, r }` is what `acc_rect` builds `acc(A,R)` from and they are still
generalised and instantiated at `[A, R̄]` afterwards.

### 4. `preds` generalises by its *source*, and only half of it carries over

`crate::rec_acc::preds` gained `Src`, which is where `y ∈ acc(A,R̄)` comes from
at a predecessor: `Src::Ih` (the induction hypothesis) or `Src::Pred` (**A4** at
an `x` already known accessible). The `u₁ = 0` clause is the first; every use in
the `u₁ ≥ 1` clause is the second, including inside the *refinement's* own
induction, where the hypothesis is available and A4 is simply shorter.

`Want::Motive` does **not** carry over, and the reason is §6.2 again: at
`u₁ = 0` Lean's second predecessor hypothesis `∀ y hy, C y (h y hy)` is a
conditional singleton and `preds` can show it inhabited; at `u₁ ≥ 1` it is a
`dprod` and what is owed is not inhabitation but a **member** — which is
`mini/src/rec_acc_ih.rs`, the largest single piece of this round. Half of a
two-way helper carrying over is the honest outcome and the enum says which half.

### 5. Piece 2, sized by §25 item 3 as three facts, is three facts — and the
inner half is much cheaper than the outer

§25 item 3's list (`the rows are sections`, `the whole is a section over A`,
`ep(R̄,y,x) = ⟦r y x⟧`) is exactly the file's three sections. The correction is
to the *cost*, and it goes down:

> **`⟦∀ (hy : r y x), C y (h y hy)⟧` is a `dprod` at a constant fibre.**
> `h y hy : Acc α r y` is a `Prop`, so it denotes `•` and the body is
> `app(app(C̄,y),•)` at every argument. `derived::ext::dprod_const_fibre_n`
> turns the inner product into `fs(⟦r y x⟧, app(app(C̄,y),•))`, and the whole
> inner half is then `cval_bound` + `cval_single_valued` + one totality witness,
> with **no `⋃img` in it at all**.

`⋃img(h⃗,A)` is named exactly once in the file, in the outer half, whose fibre
genuinely does depend on `y` (through `r y x` *and* through `C y`). The outer
half is the long one: subset, totality and single-valuedness against
`fs_ax`, then `dprod_def`.

The other thing worth carrying is where the induction hypothesis is spent. It is
spent **once**, on `app(accrec,y) ∈ app(app(C̄,y),•)` — which is `φ(y)` — and
only *under* `h ∈ ep(R̄,y,x)`, because `derived::rec_acc::cval`'s two lemmas are
guarded by the condition's **inhabitation** rather than by the proposition. At a
`y` that is not a predecessor the row is `cval(∅,v) = ∅` and the fibre is
`dprod(∅,·)`, and no case analysis on the proposition happens anywhere — the
property that module's header advertises, consumed for the first time.

### 6. Two smaller things

**`define_abbrev` through `&mut ip.env`, not `Interp::ind_parts`.**
`rec_dep::dep_bottom` reaches its `Env` through the inductive apparatus because
it is holding one already. Copying that would make `117_accRecType` — an export
that mentions no inductive but `Acc` — build a `Wtype`, a `Bound` and an
`IndChain` for one abbreviation, which is precisely the expense `crate::acc`'s
laziness exists to avoid. `Interp::env` is `pub` and is the same `Env`.

**`step_typed`'s junk branch is two lines of case split**, as §23's correction
predicted: `Formula::or(φ,ψ)` is `¬φ → ψ`, so excluded middle at `φ` is
`imp_refl(¬φ)`, and `Scopes::assume` supplies both branches' hypotheses. What
the correction did not name is that `hyp_or_elim` wants its three premises in
`H → …` form while a scoped derivation has them in `Γ`; taking `H := φ ∨ ¬φ`
itself and discharging it against the same `imp_refl` closes that gap in one
line. §23 item 2's correction about the antecedent coming off the **type** and
never off the term is right and is what the code does.

### Why this is a handoff and not a pause

**Signal 3, called before it fires**, and the boundary is the same kind §25 and
§26.1 both stopped at: four pieces are landed, measured and committed, and the
fifth is one construction of its own that nobody has sized. Writing the first
third of it here would leave it described by someone who had stopped reading.

Accuracy held: every derivation compiled on the first attempt and the three
failures were all shape mismatches that named themselves —
an over-lifted `imp_mono_r` where a `Thm::mp` was wanted, and `acc_rect`'s
`params` (item 3). None reached a measurement. The one thing that did not hold
is efficiency: the corpus measurement took four attempts because the shared tree
stopped compiling under me (below).

### Piece 4 — `iota(Acc.rec)`, sized

The route already exists and what is missing is one equation. `whnf` reaches
`Acc.rec.{1,1} α r C m a (Acc.intro α r a h)`; `Acc` takes `direct::clause_for`,
so `Checker::nest_iota` β-chains down the stored nest, lands on
`sym(⟦α⟧,…,⟦a⟧,•) = app(app(pack,ā),•)`, compares against `⟦rhs⟧` and declines.
Then

```text
LHS  pack_iota (guarded by ST, which this clause now discharges)
       app(app(pack,ā),•) = app(app(app(ē,ā),•), ih(accrec,A,R̄,ā))
RHS  ⟦m a h (fun y hy => Acc.rec α r C m y (h y hy))⟧
       = app(app(app(ē,ā),•), L)          — ⟦h⟧ = • , both proofs
```

so **the whole of piece 4 is `ih(accrec,A,R̄,ā) = L`**: an extensionality
between `derived`'s row set and mini's λ-graph. `L`'s outer `lam` is over `A`
with body the inner `lam` over `⟦r y ā⟧` with body `app(app(pack,y),•)`, and
`pack_app` turns that into `app(accrec,y)` given `y ∈ acc(A,R̄)` — which is
**A4** at `ā ∈ acc` and the pair, and the pair comes from `w ∈ ⟦r y ā⟧` through
`pair_in_graph`. `ep(R̄,y,ā) = ⟦r y ā⟧` is `edge_value`, already on the
apparatus. Off the relation both sides are `∅`-domained and agree, which is the
`cval`-guarded-by-inhabitation discipline paying a second time.

Two things a sizing should not miss:

1. **The nest bottom does not store its abbreviation, and the ι rule has no
   other way back to `pack`.** `rec_dep::dep_bottom` keeps `(sym, ax)` on
   `IndApparatus::dep_elims` for exactly this — §2's sixth instance — and the
   `u₁ ≥ 1` bottom deliberately does **not**, because a store with no reader is
   §26 item 1's failure from the other side. Adding it is part of piece 4, not a
   prerequisite of it: `Site` had `rec`/`rec_inst` fields for one hour and they
   were removed rather than left dead.
2. Every input is already on `RecAccApparatus` and in `rec_acc_value::Cx`. What
   is new is the two extensionality steps, and by size they are
   `rec_acc_ih.rs` again — one construction, not four.

### What a successor starts on

1. **`iota(Acc.rec)`**, 1 pair, 1 blocked export — the sizing above. It is the
   last `Acc` row and the only one left on the threading axis.
2. **`RTree`**, 4 pairs, 2 blocked exports — ~~`derived/`'s recursor, unchanged
   from §26 item 2. Do not lift `zoneb::ctor_spec`'s decline.~~ **Corrected in
   §26 item 2: it is a `mini/` row.** `zoneb.rs:1544` refuses the constructor
   spec before `Inductive::build` at `zoneb.rs:619`, so `derived`'s recursor
   guards are never reached — measured by lifting them and watching
   `waiting:fun-typed-rec-arg(RTree)` stay at 4.
3. The ledger is `constEv` **213** of 218, `gapped` **12** at one site, three
   exports stopping over two declarations.

### A process note, and it is not a small one

**The shared tree stopped compiling mid-round, in `derived/`, uncommitted.**
`derived/src/inductive/iota.rs` calls `ctor_atoms_at` and `rec_sets`, neither of
which exists in `derived/src/inductive/carrier.rs` as of this writing; both files
are modified and unstaged. That is a third owner's `RTree` work in flight and it
is expected, but it means **no build of `mini` in the shared tree succeeds while
it lasts**, so this round's measurement is from a detached worktree at `62e6cbc`
with only `mini/`'s files copied in. That is the same instrument §25 reached for
and for the same reason: it makes the delta a delta *by construction* rather than
by assumption about what else moved.

Reported rather than worked around, per the standing rule. Nothing of theirs
reaches this row: `Acc` takes `direct::clause_for` before the eliminator
trichotomy, so it never touches `crate::inductive`.

**And a detached worktree is green for a reason that is not the one you want.**
`vendor/arena-tests` is **gitignored**, so `git worktree add` does not bring it,
and every corpus test in `mini/tests/` opens `good_dir()`, gets `Err`, prints
`SKIP:` and passes. The first full run in the worktree reported
`11 passed … finished in 0.00s` — eleven greens over nothing, and the `0.00s`
against the 90 seconds the same target takes in the shared tree is the only
thing that says so.

> **`ln -s` the corpus into the worktree before believing an integration
> target there**, and read the *duration* as well as the count. This is §26
> item 3's rule (*"green on its own" has to name which targets ran*) at one more
> position: the target ran, and it ran on an empty file list.

## 28. `iota(Acc.rec)` closed — `Acc` is done, and the threading axis is empty **[Tove]**

`f4cac3f`. Piece 4 of §26.1. Measured over the 91 tutorial exports by summing
every `ledger`, `evidence` and `convs` row, against a detached worktree at
**`b2b66b9`** — the shared tree's own HEAD, not Ilse's `62e6cbc`, because
`derived/` compiled again for the middle of this round.

| counter | before | after |
|---|---:|---:|
| `constEv` | 213 | **214** |
| `threading-incompleteness` | 1 | **0** |
| `waiting:iota(Acc.rec)` | 1 | **0** |
| conversions `gapped` | 12 | **0** |
| `convGap:iota(Acc.rec)` | 12 | **0** |
| conversions `moved` | 10145 | **10224** |
| conversions `proved` | 11 407 939 | **11 562 196** |
| `movedSealed` | 1496 | **1497** |
| exports that stop | 3 | **2** |
| everything else | — | *bit-identical* |

`pairs` 218, `typeEv` 214, `typesOk` 214, `fullyInterpreted` 144,
`interpretation-scope` 4, `typeEvMasked` 0, `typeEvOnlyGap` 0, `unsealed` 0,
`waiting:fun-typed-rec-arg(RTree)` 4: unchanged. Per declaration,
**`118_accRecReduction`'s constant typing** is the one obligation that moved —
`typeEv=1 constEv=1`, no waiting row — and `117_accRecType` is untouched at
`typeEv=2 constEv=2`. The two exports that still stop are `115` and `116`, both
`RTree`, so the residue is **one declaration**.

**`gapped` 12 → 0 is §27's zero read forwards.** §27 recorded the rise as *the
walk got further*; the fall is that same walk now getting past the site — which
is why `proved` rose by 154 257 and `moved` by 79 in the same increment rather
than staying put. A route that fired at the outer graph and declined at the
inner one would have left a residue, and the reason table is compared against an
**empty** map, so it could not have hidden in a total.

### 1. §27's route is right about the derivation and wrong about the arm

The sizing says `Checker::nest_iota` β-chains down the stored nest, compares
against `⟦rhs⟧` and declines. **`Acc` never reaches `nest_iota`.** That function
has one caller, `whnf`'s **K-rule** branch, and `crate::kernel::add` sets
`k_type` only when the declaration is an inductive proposition with one
constructor **and that constructor has no fields**; `Acc.intro` has two. So the
major premise is reduced, matched against the rule, and `118`'s twelve declines
came from the *constructor-match* branch, where `num_indices = 1` routed them to
`iota_ix_dep` — a module about `IndexedDepRecursor`, which no `direct::Clause`
declaration has.

The instrument that settled it is one line of the `--block` report: **`gave up
at mini/src/kernel.rs:874`**, which is the constructor-match arm's `None`, not
the K-rule arm's at `:746`. Reading the two sites the report already prints was
cheaper than reading `whnf`, and it is the eighth-for-eighth instance of
*instrument the masked reason before scoping on top of it* — here the label
(`iota(Acc.rec)`) was right, the mechanism (β down the nest) was right, and the
**arm** was wrong, which is `SCOPING.md` §1's fourth category at a control-flow
join rather than at a theorem.

> **A gap's construction site is printed and its *reaching* site is not.** The
> blocker report gives both — `gave up at` and `Gap::… is constructed at` — and
> when a gap has two construction sites they are the two arms of the same
> `match`. Read which one fired before believing a note about which route
> declined.

So the hook goes beside `crate::quot_iota`'s, gated on `direct::clause_for`,
*before* the `num_indices != 0` arm. Nothing about the derivation changed.

### 2. Two things are one β step short of what the sizing spells, and both are the cost axis

§27: *"`L`'s outer `lam` is over `A` with body the inner `lam` over `⟦r y ā⟧`
with body `app(app(pack,y),•)`"*.

The body is **not** `app(app(pack,y),•)`. `Interp::app` builds
`⟦f a⟧ = app(⟦f⟧,⟦a⟧)` and never reduces, so `⟦Acc.rec α r C m y (h y hy)⟧` is
the six-fold applicative spine over `⟦Acc.rec.{1,1}⟧` — a redex over the stored
λ-graph. Step 1 therefore runs a **second** time, at `y` and `•`, and only then
does `pack_app` apply. That is `SCOPING.md` §1's cost axis exactly: *a design
reasons about denotations, the code holds terms, and the gap is one reduction.*

The second is smaller and cost the same build. **`⟦h⟧` is not `•`.** §6.2 sends
a *proof* to `•` at an **application** — which is why `⟦Acc.intro α r a h⟧` is
`•` and the `tt == point` check passes — but `h` is a **binder of the
declaration under check**, so its interpretation is that binder's own scope
variable and `⟦rhs⟧` is `app(app(app(ē,ā),⟦h⟧),L)`. `pack_iota` is stated at
`•`, so one proof-irrelevance step and one more `app` congruence bridge them,
exactly as the value clause bridges `⟦t⟧`.

> **`•` is a fact about an occurrence's *clause*, not about its type.** Same
> proof, same type, two spellings: an application collapses at the interpreter,
> a `bvar` does not and is collapsed by a theorem.

### 3. `inst_all` produces the term and not the structure, and that is the third landmine

`ip.as_lam` reads the graph symbol off the **recorded** applicative structure.
`derived::inst_all(&site.t_ax, …)` instantiates *inside the kernel*, so the
right-hand side it hands back is the right `Term` and has **no `parts` entry** —
and the very next decomposition returns `None`. [`Interp::body_unfold`] is the
same equation with `Interp::rebuild` in front of it, and it is what a caller
that intends to take the result apart must use.

`Interp::rebuild`'s own doc states this and calls it "how a whole class of
curried applications was silently gapping". It is stated at `rebuild` and the
trap is at `inst_all`, which is why it was met twice in one file.

### 4. What piece 4 actually is: one lemma, used at both levels

`derived`'s `ih(accrec,A,R̄,ā)` is `{ ⟨y, cval(ep(R̄,y,ā), app(accrec,y))⟩ : y ∈ A }`
and Lean's λ is `lam(p⃗,A) = { ⟨y, t(p⃗,y)⟩ : y ∈ A }`. **Both are Replacement
images over the same domain**, so what closes the level is: the rows agree
pointwise, hence the sets are equal. The same is true one level down, where
`cval(c,v) = prod(c,{v})` and the inner λ is a graph over `⟦r y ā⟧`.

So `mini/src/rec_acc_iota.rs` has **one** extensionality lemma, `same_rows`,
run twice. It is `derived::ext::image_ext_n` with the domain equation dropped
and the two membership conditions taken as *theorems* rather than as symbols —
and that last part is forced, not a preference:

> **`ih(g,A,R,x)` carries its domain in the middle of its argument list and
> every `_n` extensionality in `derived/` wants it last.** A symbol's arity and
> argument order are fixed, so no threading of prefixes instantiates the library
> lemma at this pair. The lemma is re-derived over `Thm`s instead, and pinned
> against `Base::cval_ext` at the instance where both sides *are* `cval` —
> which is a comparison against a theorem derived from `prod_inhabited` rather
> than from Extensionality over rows.

The one thing `derived` genuinely owed and does not state is
`p ∈ cval(c,v) ↔ ∃w. (w ∈ c ∧ p = ⟨w,v⟩)` — the reduction `rec_acc::cval`'s own
header spells in prose and derives no theorem for, because nothing in that
module needs the members one at a time. It is 45 lines here (`cval_members`).

**`refine` and `crate::rec_acc_ih` are not wanted at a use site**, and that is
the size correction that goes *down*. The ι certificate is an **equation**, not
a typing, so the fibre refinement — the second `acc_rect`, the largest piece of
§27 — has no part in it. Only `step_typed_at` and `major` are reused from the
value clause. §27's "by size they are `rec_acc_ih.rs` again" is right at ~500
lines and right about which file to compare against, and it is right for a
different reason than it gives.

### 5. Two smaller things

**The store, and where it lives.** `IndApparatus::dep_elims` is the model, and
the field cannot go there: `Acc` takes `direct::clause_for` and building an
`IndApparatus` for one `define_abbrev` is precisely the expense §27 item 6
declines. `Interp::rec_acc_elims` is keyed the same way — by the **recursor's**
constant — and `Site` regains the `rec`/`rec_inst` fields it carried for an hour
at §27, now that they have a reader. That is the *store with no reader* rule
paid off in the intended direction rather than a second time.

**A4 is spent at the predecessor and the pair comes from the proof binder.**
`app(accrec,y) = ⟦Acc.rec … y (h y hy)⟧` needs `y ∈ acc(A,R̄)`, which is
`acc_pred_closed` at `ā ∈ acc(A,R̄)` and `⟨y,ā⟩ ∈ R̄` — and that pair is
`pair_in_graph` at `• ∈ ⟦r y ā⟧`, available because the *inner* scope's proof
binder `w` inhabits it. Off the relation there is no obligation at all: both
sides are `∅`-domained, no case analysis happens anywhere, and that is
`cval`-guarded-by-inhabitation paying the second time §27 predicted.

### 6. Three ratchets moved, all forwards, and one now asserts an absence

`tutorial_first_blocker` 3 → **2**; `tutorial_evidence_ledger`'s `constEv`
213 → **214** and `threading-incompleteness` 1 → **0**;
`tutorial_conversion_split`'s `gapped` 12 → **0**, `moved` 10145 → **10224**,
`movedSealed` 1496 → **1497**, and its reason table back to the **empty map** —
the strongest form that assertion takes, and the second time it has held it.
`waiting:iota(Acc.rec)` is pinned at **0 by name** rather than deleted, beside
the six ι rows that preceded it.

Two unit tests in `rec_acc_iota.rs`, both about the lemmas rather than the
wiring: the cross-check against `Base::cval_ext` above, and `cval`'s membership
condition compared against the formula whole (a derivation that left the inner
existential in place would be sound and would decline four functions deeper).
The wiring itself is pinned by the three corpus ratchets, which is the right
division: a synthetic `Acc.rec … (Acc.intro …)` needs an inhabited
`∀ y, r y a → Acc α r y` and there is nothing closed to build one from.

### Why this is a handoff and not a pause

`Acc` is closed entire and the **threading axis is empty** — every remaining
stop on the corpus is `interpretation-scope`, and all four are `RTree`'s, which
is one declaration and explicitly not this seat's row. There is no next piece of
this construction to be half-way into.

Accuracy held: the derivation compiled on the first attempt and every one of the
four failures named itself and was a *shape* mismatch that a `--block` run or a
split reason constant localised in one build — `nest_iota` (item 1), `⟦h⟧`
(item 2), and `inst_all` twice (item 3). None reached a measurement, and none
needed a third hypothesis. Efficiency held too, with one caveat: the shared tree
stopped compiling under me a second time, mid-test-run, and the recovery was to
copy `mini/` into the worktree rather than to wait.

### What a successor starts on

1. **`RTree`**, 4 pairs, 2 blocked exports — and §26 item 2 is corrected in
   place: it is a **`mini/` row**. `zoneb.rs:1544` refuses the constructor spec
   before `Inductive::build` at `zoneb.rs:619`, so `derived`'s recursor guards
   are never consulted for this declaration; lifting them left
   `waiting:fun-typed-rec-arg(RTree)` at 4. ~~The work is `zoneb.rs:1544` plus
   `derived::sigma::reindex` at the constructor's nest bottom **and** at the
   minor premise.~~ **The first half held and the second is incomplete** —
   §29. `zoneb.rs:1544` is lifted at `9b5ea75` and the carrier now builds; the
   row is **`derived/`'s again**, at `cumul::DeclUniverse::over_at`, whose two
   fibre-value readers are stated at `finord(mᵢ)`. And `sigma::reindex` is not
   reachable from what mini holds without a `dprod`→`fs` bridge first, because
   §12 removed the `fs` clause and `⟦Bool → RTree⟧` is a dependent product.
2. The ledger is `constEv` **214** of 218, `typeEv` **214**, `gapped` **0**,
   `threading-incompleteness` **0**, two exports stopping over one declaration.
   *(And, since §29, `interpretation-scope` **0** and `library-gap` **4**: the
   residue moved axis without moving a pair.)*
3. `mini/src/rec_acc_iota.rs`'s `same_rows` is the extensionality
   `derived::ext::image_ext_n` cannot be instantiated to. If a second consumer
   appears — any pair of Replacement images over one domain whose symbols do not
   put the domain last — it belongs in `derived/ext`, and not before.

### A process note, and it is the same one twice

**The shared tree stopped compiling under me again**, in `derived/`, uncommitted
and *mid-round*: `derived/src/inductive/dep.rs` calls `induction_step`,
`dep_iota` and `composite_in_funspace` at arities and names its siblings do not
have. It compiled at the start of this round and did not an hour later, which
is the shape §27's note did not have: not a tree that was broken when I arrived,
but one that broke between two `cargo test` invocations of mine.

Reported, not worked around, and the recovery is cheap and worth writing down:
**`git worktree add --detach <dir> <sha>`, `mkdir -p vendor` and symlink both
`vendor/` entries, then `cp -a mini/src/. <dir>/mini/src/`.** That gives a tree
whose `derived/` is a commit and whose `mini/` is the working copy, which is
what the delta needs to be a delta by construction — and it is also what makes
`cargo test -p mini` meaningful while somebody else's crate is mid-edit. Ilse's
`ln -s` rule is the other half of it: **read the durations**, 70 s and 91 s for
the two integration targets, or the corpus was not there.

## 29. `RTree`'s constructor spec landed — and the blocker is one function on **[Yara]**

`9b5ea75`. Measured over the 91 tutorial exports by summing every `ledger`,
`evidence` and `convs` row, against a detached worktree at **`13603c6`** —
`derived/` was mid-edit in the shared tree when the round opened and was
committed under me at `37b4fe9`, so the baseline is a commit and `mini/` is the
working copy, per §28's recipe.

| counter | before | after |
|---|---:|---:|
| `interpretation-scope` | 4 | **0** |
| `library-gap` | 0 | **4** |
| `waiting:fun-typed-rec-arg(RTree)` | 4 | **0** |
| `waiting:ind-fibre-value(RTree)` | 0 | **4** |
| everything else | — | *bit-identical* |

`pairs` 218, `constEv` **214**, `typeEv` 214, `typesOk` 214,
`fullyInterpreted` 144, `gapped` **0**, `moved` 10224, `proved` 11 562 196,
`movedSealed` 1497, `threading-incompleteness` 0, `unsealed` 0. **No pair
moved.** What moved is the axis, and that is the whole deliverable of this
increment: `interpretation-scope` is now **zero**, so nothing on
`good/tutorial` stops because mini cannot express a shape.

### 1. §26 item 2's correction verified, and then the finding underneath it

The briefing asked for `zoneb.rs:1544` to be checked rather than believed, and
it holds exactly: the `--block` report on `115_rTreeRec` prints **one**
construction site for `Gap::FunTypedRecArg`, `mini/src/zoneb.rs:1544`, and
`Inductive::build` at `zoneb.rs:619` is after it. So `derived`'s recursor guards
were never consulted for this declaration.

Lifting it is ~60 lines. `ctor_spec`'s middle arm now peels the field's
telescope, abbreviates each `γⱼᵢ` **over the parameters alone** — `Telescope`
fixes the arity at `np + i`, so a binder type reaching an earlier plain field is
refused by `define_abbrev` rather than by a hand-written scan — and pushes
`Slot::Rec` with the row into `CtorSpec::rec_doms`. Everything below it is
already general and needed nothing: the spec is `well_formed`, and
`derived::Inductive::build` produces the carrier, the constructor term and
`Ctor::mem` for `RTree` on the first attempt.

**And then it stops one function later, in `decl_universe`.**
`cumul::DeclUniverse::over_at` reads each constructor's fibre value twice —
`cumul::bnd_finords` for `vᵢ ⊆ S ∧ bnd(vᵢ)` (`decl.rs:314`, compared at `:344`)
and `isum::finords_in_universe` for `vᵢ ∈ U₁` (`decl.rs:389`, compared at
`:393`) — and **both are stated at `finord(mᵢ)`**, comparing their conclusion
against `Inductive::fibre`'s own `values[i]`.

Instrumented rather than inferred, at the one comparison that decides it:

```text
INSTRUMENT Bool  ctor 0: recs=0  value==finord(m)?  true
INSTRUMENT Bool  ctor 1: recs=0  value==finord(m)?  true
INSTRUMENT RTree ctor 0: recs=0  value==finord(m)?  true
INSTRUMENT RTree ctor 1: recs=1  value==finord(m)?  false
```

`RTree.node`'s fibre value is `Sum_1(Σ(z::[Bool]))`. Neither comparison can hold
at a non-empty `γ`, **at any level**, so the placement declines whatever the
tower does.

> **`derived/`'s widening made the carrier *expressible* and the declaration
> *buildable*; it did not make the declaration **placeable**.** `fibre_values`,
> `CtorSpec::rec_doms`, `RecArg::general` and `Ctor::mem` are all general and
> all reached. The one thing that is not is the universe placement that stands
> between the carrier and its type former.

### 2. The label would have sent the next round to the tower

`over_at` returning `None` mints `Gap::IndUniverseHeight(RTree, 1)`, which the
ledger spells **`ind-universe(RTree>U1)`**. `RTree : Type 0` and its height is
not the problem; a reader of that key goes and looks at `Tower::at`. So the
decline gets its own variant, `Gap::IndFibreValue` → `ind-fibre-value(RTree)`,
minted from a **necessary** condition on `over_at`'s inputs and checked before
it is called — two checks, one input each, so `IndUniverseHeight` still owns
every other way the placement can refuse. That is the *over-determined net*
side of the mutation rule rather than the *redundant layer* side, and it is
stated here because the two are only distinguishable by which fires first.

The instrument that settled *which* arm declined was one line: `decl_universe`
has two `IndUniverseHeight` sites, `over_at`'s `ok_or_else` and the
`rests_on_nothing`/`universe != want` check after it, and the `--block` report
prints **all seven** sites of the variant crate-wide rather than the one that
fired. §28's rule holds — *read which arm fired before believing a note about
which route declined* — but its instrument does not, when a variant has seven
sites and none of them is in the printed control-flow join. Renaming the second
site for one build is what answered it, and it took ninety seconds.

> **`gave up at` localises the *reaching* site; `is constructed at` is a
> crate-wide grep and localises nothing when the variant has more than two
> sites.** For those, spend one build on a temporary distinct reason. It is
> cheaper than any amount of reading `derived/`.

### 3. The sixth `RTree` claim, refuted before it was built on

`derived/src/sigma/reindex.rs`'s own header — and the briefing paraphrasing it —
says *"a field `children : Bool → RTree` interprets to `fs(⟦Bool⟧, ind)`, over
`⟦Bool⟧` itself"*, and `reindex_in_funspace` is stated at `fs(β₀(p⃗), S)`
accordingly.

**It does not.** `Checker::pi_evidence` has `let _ = dep;` and one clause:

```rust
// **There is no binder-free clause.** `⟦Π x:A. B⟧` is `dprod` whether or
// not `B` mentions `x`; see this function's own header for why the
// clause that used to sit here was retired rather than repaired.
```

§12 removed the `fs` clause — 937 of 988 gapped conversions were one type
classified two ways — so `⟦Bool → RTree⟧` is `dprod(b, ⟦Bool⟧)` at a **constant
fibre**, and the constructor's nest bottom holds a membership in a dependent
product, not in a function space. `sigma::reindex` does not apply to what mini
has. This is not a defect in either crate; it is the two headers describing the
same field in two vocabularies, and the bridge between them is real work that no
note has counted.

The bridge exists and is **unread**: `derived::ext::dprod_const_fibre_n`,

```text
⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A → b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))
```

`Interp::dprod_fs_bridge` used to call it and was **deleted** at the `fs`-clause
removal, with a comment saying so — the theorem "is now unread, and that is a
real consequence to record rather than a side-effect". This is the consequence,
arriving two sections later. Its hypothesis is reflexivity at a constant fibre,
which is precisely what `Interp::const_dprod` already relies on without naming.

So the constructor's bottom is **six** steps and not four, and this is the cost
axis at its usual size:

```text
1.  g ∈ dprod(b, ⟦Bool⟧)                     the nest's own scope
2.  dprod(b, ⟦Bool⟧) = fs(⟦Bool⟧, ⟦RTree⟧)   ext::dprod_const_fibre_n   ← not in any note
3.  ⟦Bool⟧ ↦ β₀(p⃗)                          CtorEvidence::rec_dom_abbrev
4.  store spine ↦ ind(p⃗)                     the existing spine_eq
5.  pull(g,T(p⃗)) ∈ fs(T(p⃗), ind(p⃗))         sigma::reindex_in_funspace
6.  Ctor::mem at r₀ := pull(g, T(p⃗))
```

Steps 3 and 4 are two Leibniz rewrites *inside* an `fs`, and `retarget_set`
rewrites the set whole — so each needs its own hole, which `retarget_set` does
not take. That is where a successor's first build will fail.

**None of this was written, and none of it can be measured today**, because
`over_at` declines before `constructor` is reached. `CtorEvidence::rec_dom_abbrev`
is kept — the symbol is minted inside the walk and is unrecoverable once that
frame goes, which is §26 item 1's lesson in the direction that costs nothing —
but the bottom itself is deliberately **not built**: it would be a
generalisation landed ahead of a consumer that cannot run, which is the failure
this file records four instances of.

### 4. What `derived/` owes, in `derived/`'s vocabulary

§26's closing note says the seam is cheapest to close by writing the blocker in
the other crate's words, so:

> `cumul::DeclUniverse::over_at` needs its two fibre-value readers generalised
> from `finord(mᵢ)` to `Sum_m(A⃗)` at arbitrary summands: `bnd(Sum_m(A⃗))` given
> `bnd(Aⱼ)` per summand, and `Sum_m(A⃗) ∈ Uₙ` given `Aⱼ ∈ Uₙ`. At
> `Aⱼ = Σ(z::γⱼ)` that reduces to the **telescope's** own placement, and
> `Telescope` is `k` nested `DSum`s over the `βᵢ`, so the input it will want
> from a caller is `⊢ ⟦γᵢ⟧ ∈ ⟦Sort ℓ⟧` per binder — which `ctor_spec` has in
> hand at exactly the point it abbreviates `γᵢ` and does not currently keep.
> Say so and I will keep it; it is two lines beside `CtorEvidence::field_sort`,
> and keeping it *before* there is a consumer is the mistake this file names
> four times.

`RTree.node` is `m = 1`, `γ₀ = [Bool]`, `⟦Bool⟧` a two-element enum — so the
corpus instance is the smallest one the general statement has.

### 5. Three ratchets moved and one gained an assertion it never had

`tutorial_first_blocker`'s `FIRST_BLOCKER` is `115_rTreeRec` /
`ind-fibre-value(RTree)` — same export, same declaration, new key and new axis.
Its doc block carried two sentences that §26 item 2 had already refuted and this
round refutes again from the other side; both are corrected in place.

`tutorial_evidence_ledger` gains `waiting:ind-fibre-value(RTree)` at **4** and
pins `waiting:fun-typed-rec-arg(RTree)` at **0** by name beside the closed rows,
and — the one worth quoting — `interpretation-scope` is now asserted at
**zero**. That assertion has never been zero before. `library-gap` rises from 0
to 4 and is the first time *that* axis has risen at all; both are asserted
separately, because a row that moved axis and a row that closed look identical
in either number alone.

`mini/tests/dump.rs`'s decline row expects the new key. It was pinned on
`fun-typed-rec-arg(RTree)` and its paragraph already recorded that `RTree` is
the only declaration that declines; that is still true and is now true for a
different reason, rewritten in place with the marker.

One unit test, and its shape is the briefing's warning taken literally:
`a_function_typed_recursive_argument_records_its_telescope_at_its_own_slot`
runs `T.c : T → (A → T) → (B → T) → T` — the **mixed** constructor, because
`RecArg::general` takes a constructor as a whole and a single function-typed
argument would validate a spec that recorded `γ` per *constructor*. Three
recursive slots and two distinct closed domains, because the claim is about
position and two atoms cannot distinguish a rotation; the domains are compared
by their defining axioms rather than by arity. Mutated once —
`rec_doms.push` → `rec_doms.insert(0, …)` — and it fails at the slot-to-domain
assertion, not merely at a length.

### 6. `Gap::FunTypedRecArg` has no mint site

The two shapes still declined are a `γ` of depth `≥ 2` — `sigma::reindex` is
`k = 1` for a stated reason, and at `k ≥ 2` the map is an uncurrying — and one
at an indexed family, whose index expressions may mention `z⃗`. Both are
`Gap::IndSpec` with the step that refused them, which is what that variant is
for and which a rolled-up label would hide (§26 item 2's own lesson).

**Reported rather than deleted.** The variant stays, with a doc note saying it
has no site; its reason string is pinned in three ratchets and `Acc`'s two prose
references to it were stale in two independent ways, both corrected in place.
Deleting a `Gap` whose vocabulary the ledger asserts on is not one seat's call.

### Why this is a handoff and not a pause

**Signal 3, called before it fires** — the third time in a row, and the
condition is sharp rather than felt: the next piece of `RTree` is the
constructor's nest bottom, it cannot be reached until `derived/` widens the
placement, and writing it now produces exactly the callerless artifact this file
has four instances of. There is nothing half-built: the spec walk is complete,
green, committed and measured, and item 3 above is the successor's spec written
at the level of detail that made §26's seam close in one round.

Accuracy held: the walk compiled and produced its ledger delta on the first
attempt, the one red test was a real property (a detail literal must pin one
line) and named itself, and every claim above was measured rather than read
except the two static ones, both in code I may not edit. Efficiency held; the
round cost six release builds and three corpus sweeps.

### What a successor starts on

1. **`RTree`, 4 pairs, 2 blocked exports — and the first step is `derived/`'s**,
   item 4. Nothing in `mini/` moves until the placement takes a general fibre
   value. If it lands, the mini row is item 3's six steps at `ctor_bottom`, then
   the recursor: `Rx::fibre_apps` is already wide, and `Interp::dep_recursor`
   wants Marit's `dep.rs` widening, which landed at `79a65c6`/`37b4fe9`.
2. The ledger is `constEv` **214** of 218, `typeEv` 214, `gapped` **0**,
   `threading-incompleteness` **0**, **`interpretation-scope` 0**, `library-gap`
   **4** — one declaration, one obligation, and it is in the other crate.
3. `derived::ext::dprod_const_fibre_n` is stored and unread and is step 2 of
   the constructor's bottom. It is the same theorem §12 deleted the reader of;
   if a second consumer appears, the `dprod`→`fs` move belongs in `Interp`
   beside `const_dprod` and not copied into two call sites.
