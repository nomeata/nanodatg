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

Answering it costs one census and it has changed the size estimate every time,
in both directions.

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
**swapped**, which is `thesis.txt:1866–1870`'s delayed elimination in its
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

### What `derived/` owes — and this is the first time it is not "nothing"

A module beside `le_prop`, guarded at `ni ≥ 1` as `le_prop` is at `ni = 0`, with
`LeProp::build`'s signature plus a `&Tower`. Write `p⃗` for the parameter
variables, `x⃗` for `ni` fresh index variables, `X := tup(x⃗)`, and
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

Two things the module must say rather than quietly assume:

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

## 7. The one habit worth keeping

Every good finding on this run came from the same move: **the design note said
X, the measurement said Y, and Y was right.** `Acc`'s blocker was the carrier,
not the recursor. `069` was a constructor, not a projection. Class (P) was four
tiers, not one. The thesis had no `Sort 0` quotient clause. `084`/`086` closed
outright.

The notes in this repository are unusually good and are still, reliably, one
round behind the code. Trust them for *intent* and measure for *state*.
