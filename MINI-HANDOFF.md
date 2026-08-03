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

The pattern is stable across six personas: **static reads hold, dynamic
predictions do not, and a census is a dynamic prediction.** A row's count, its
cause, and what is behind it are three separate measurements and none of them
follows from the label. A third category appeared this week and the split does
not cover it — Vera's: *a correct measurement transcribed wrongly*. Right
command, right corpus, right order of magnitude, and "read what you can" does
not protect you when the thing being read is your own output.

---

## 2. Evidence produced and then discarded — five instances, one pattern

**[Otto]** Three times in one month, and twice more since:

| site | what was computed | what was dropped |
| --- | --- | --- |
| `zoneb::CtorEvidence::field_sort` | the field type's sort typing | kept, in a form no consumer could instantiate |
| `ctor_ix::one` | `cᵢ`, the constructor abbreviation | its **defining axiom**, with the `Site` |
| `zoneb::build_trunc` | `tc.ctors`, a rule per class-(P) constructor | all of them, by ending at `former_at` |
| `zoneb::build_trunc` again | **the whole class-(P) translation** | `ind`, `tc`, both abbreviation families |
| `zoneb::ensure`'s indexed decline | the whole boundary walk | `IndexAx` *and* `Shape`, on the decline path |

**The pattern: a value computed at the bottom of a call whose site outlives
nothing.** The call has everything in hand at that moment — the scopes are open,
the symbols are fresh, the axioms are live — and then returns one thing and
drops the rest. The next consumer is at a different nest, cannot re-derive
(re-minting gives a *second* symbol no equation relates to the first), and reads
as blocked on a library gap that does not exist.

Two rules **[Otto]**, and two the last two instances added:

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
* `minor_ix::Fam` — the walk is shared by **three** routes now. `Clause::trunc`
  is the whole of class (P)'s difference and its three rows are one fact: a
  recursive argument of a `Prop`-valued family is a proof, so it is `•`.

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

At `c425ac5`, `good/tutorial`: **161 of 218 pairs certified**, 57 waiting, 81
gapped conversions, **30** of 89 exports stopping under `--block`. *(Rewritten
from the `fd42fb9` measurement — 160/218, 58 waiting, 31 stopping, with an
`indexed-family` row of 1 — which `072` closed.)*

The 57 waiting pairs, and **say which unit you mean** — this went wrong three
times, twice in one week. Counted off `tutorial_evidence_ledger`'s own printed
rows, which are the keys:

| family | pairs | keys | exports | constructions |
| --- | ---: | ---: | ---: | ---: |
| `proj` | 24 | 5 | 8 | **1** |
| `no-interp(Quot*)`, `Nat` | 16 | 5 | 8 | 2 |
| `fun-typed-rec-arg` | 7 | 2 | 4 | 1 |
| `iota(·.rec)` | 6 | 6 | 6 | **6** |
| `unit-like(PUnit)` | 2 | 1 | 2 | 1 |
| `fun-eta` | 2 | 1 | 2 | 1 |

**`indexed-family(·)` is empty**, and it is the row this table lost rather than
the row it gained: 57 pairs over **20 keys** in **6 families**. The exports and
constructions columns are unchanged and were not re-measured — `072` was one
pair, one key, one export, and the family had no second occupant.

**Count keys for the ledger, families for the worklist, exports for the
schedule, and constructions for the estimate** — and name which. `proj` is one
family, five keys, eight exports and *one* construction; `iota` is one family,
six keys, six exports and *six* ι rules. A sentence that does not say which
number it means has been wrong every time it has been used to size anything.

Three claims of the form "the last X row" have been made and all three were
false. The habits that produce them: reading a `sort -rn` and taking the head
for the length, and rolling `Scope`/`Library`/`Threading` into one sentence. The
narrow true statements at this measurement are: `iota(·.rec)` is the only
remaining **threading** shape, and `072` is the last **`indexed-family(·)`**
row — the fourth and last of the four distinct problems that one label covered.

### A corpus fact worth relying on

**The declaration that η-expands its eliminator is the one that reaches ι.**
`069`, `070` and `071` each closed with *no successor row* — their exports are
`def f := T.rec` at a bare constant, so no use site ever asks for a reduction.
`072` is the same shape and will do the same. The ι count moves only for
`073`–`077` and `094`, which is exactly the six.

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

## 8. Instruments

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

## 9. Why I am handing off here

`072` cannot close until `derived`'s recursor lands, so nothing is stalled by
the timing. Of the two pieces that are mine, the carrier needs a branch that
does not exist yet and the constructor is a module; either is comparable to the
two rows I have just landed.

The other half of the reason is the one worth writing down. I named the same
efficiency slip on myself twice — three hypotheses before the corner walk on
`(np, kᵢ)`, and again before localising `LeCarrier`'s capture — and recognising
an inherited pattern while repeating it is the signal, not the fix. §0 is the
fix, and it is better handed to someone who reads it before their first
hypothesis than applied by someone who keeps rediscovering it after their third.

What you start with: this file, `SCOPING.md` §7, `MINI-DESIGN.md` §0.5, the
`LeIndexCarrier`/`TruncCarrier` interfaces, and the δ-redex already measured.
`class_s_ix.rs` and `rec_s_ix.rs` are the two most recent modules and are the
closest models for both remaining pieces.
