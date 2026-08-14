# Documentation audit — 2026-08-01

Read-only audit of the project's prose against the code and the corpus,
prompted by the `116_rtreeRecReduction` finding. Everything below was verified
against the source of truth named in each entry — the `.ndjson` exports under
`vendor/arena-tests/`, the extracted thesis text, or the code — never against
other prose. Nothing was built or run; where a claim needs a run to check, it
is listed in the final section rather than guessed at.

Five agents were editing the tree while this audit ran. Where a discrepancy is
a concurrent task having landed faster than its documentation, it is marked
**RACE** rather than reported as a defect.

Severity legend: **FALSE** = contradicted by the code or corpus as it stands;
**STALE** = was true when written, superseded since; **RACE** = mid-edit skew.

> **Status, 2026-08-06 — closed.** All five headline findings are fixed, and so
> is essentially all of §1, §3, §4 and §5; the sites carry the corrections, most
> of them naming what they used to say. §2 (README's stale numbers) was the one
> unactioned section for five days and is now actioned — but note that §2's own
> *replacement* figures had themselves gone stale in the meantime (it reported
> 662 kernel lines, now 676; ~34,100 `derived/` lines and 558 tests, now
> ~101,600 and 873), which is this audit's own thesis happening to this audit.
> What is worth keeping is **§6, "Checked and found correct"** — a
> do-not-re-verify list of corpus counts, thesis line numbers and `ax_tarski`'s
> clauses — and the record that the sweep was run at all. *(Two corrections,
> 2026-08-14: this file **is** cited — `QUESTIONS.md:10` cites "`DOC-AUDIT.md`
> §3.1". And `mini/` is no longer a directory; the code it named is
> `checker/src/mini/`. See §8 for the re-verification of §6's "checked clean"
> lines, three of which no longer hold.)*

**The five findings to act on first:**

1. **RBTree is an indexed family** (`numIndices: 2`), so RECURSOR-DESIGN's
   §1.6 correction — "the real plain-`m≥2` corpus test is RBTree
   (042/068/077)" — is itself false, its "wire RBTree first" plan is void,
   and the wrong `RBTree.red` signature has already propagated into
   `derived/src/inductive/spec.rs` and `premise.rs`. The tutorial corpus has
   **no** plain `m ≥ 2` test at all; the real witnesses are
   `Lean.ParserDescr.{binary,sepBy,sepBy1}` in init-prelude. (§10, appended
   concurrently, now records this in-file; the body does not.) — §1.1–1.2
2. **`kernel/README.md` still contains a section titled "Why beta is not yet
   derivable"** describing work finished on 2026-07-30/31 as "the substance
   of the remaining milestone-3 work" — a false current-state claim in the
   trusted crate's own README. — §1.4
3. **`derived/src/recursion.rs`'s rationale would cause work INDUCTIVES
   explicitly warns against restarting**: it claims the universe closure
   properties are unproved and the ω-tower is the critical path; both are
   settled the other way. — §5.2
4. **Four comments in `checker/src/tg.rs` still say "`gen` needs no side
   condition, since a `Thm` carries no hypotheses"** — the retired
   pre-sequent soundness argument, standing beside code where `gen` now
   panics on exactly that condition. — §5.1
5. **The `116_rtreeRecReduction` claim** (the audit's trigger) is confirmed
   at four sites, one more than known: README, INDUCTIVES, `wlist_rec.rs`,
   *and* LIBRARY-BACKLOG's "Checked and rejected" list, which wrongly assures
   readers `116` is covered by the in-flight general design (function-typed
   recursive arguments are declined by it). — §1.3

---

## 1. FALSE — highest priority

### 1.1 `RECURSOR-DESIGN.md`'s replacement for the `116` claim is itself wrong: RBTree is an *indexed family*

`RECURSOR-DESIGN.md` §1.6 (lines 57–67) correctly retracts the claim that
`116_rtreeRecReduction` is the `m ≥ 2` test, but the correction it installs is
false:

> "The real plain-`m≥2` corpus test is **RBTree** (`042`/`068`/`077`):
> `red : N → RBTree α → α → RBTree α → RBTree α` **[read**, export of `042`**]**"

Decoding the actual export (`vendor/arena-tests/good/tutorial/042_rbTreeDef.ndjson`,
identically in `068` and `077`):

```text
RBTree : Sort u → Color → N → Sort u          numParams: 1, numIndices: 2
RBTree.red : ∀ (α : Sort u) (n : N),
    RBTree α Color.b n → α → RBTree α Color.b n → RBTree α Color.r n
```

`RBTree` is an **indexed family** — two indices, `Color` and `N` — and indexed
families are outside the design's own declared scope (§7.9 requires the spec
builder to *decline* them; the scope statement at the top of the file says
"non-indexed"). So RBTree is not a corpus test for this design at all, and the
quoted signature (indices dropped) does not appear in any export. The `[read]`
marker is wrong: whatever was read, it was not the constructor's type.

**Checked exhaustively:** no non-indexed constructor with two or more plain
recursive arguments exists *anywhere in the tutorial corpus* (a scan of every
`inductive` block in all 91 files finds `m ≥ 2` only on `RBTree.red`/`black`,
both indexed). In `init-prelude.ndjson` there are exactly three:
`Lean.ParserDescr.binary` (mask `Plain,Rec,Rec`), `Lean.ParserDescr.sepBy` and
`sepBy1` (mask `Rec,Plain,Rec,Plain` — **interleaved**), all non-indexed with
zero parameters. So "the corpus demands interleaving" survives, but its
witness is `ParserDescr.sepBy` on `init-prelude`, not RBTree, and there is
**no tutorial-corpus test at all** for the plain `m ≥ 2` shape.

**Update while this audit ran (RACE, converging):** the implementing agent
appended **§10** to `RECURSOR-DESIGN.md` (now 655 lines) recording the same
correction independently — `numIndices: 2`, decline RBTree, §8 rung 5 void —
with a compatible witness list (`Lean.Name.str` for the mask,
`ParserDescr.sepBy/sepBy1`, plus `Lean.RArray.branch` and
`Lean.Grind.CommRing.Expr.add/sub/mul`, the latter two in
`good/perf/grind-ring-5.ndjson`, not init-prelude). Two independent reads of
the export agree, so the *finding* is settled. The residual defect is that
**§1.6, §4.4, §5.2, §7.2 and §8.5 stand uncorrected in place** — a reader
hitting §1.6 first, with its `[read]` marker and "wire RBTree first"
instruction, gets the wrong plan and only learns otherwise if they reach the
addendum — the same correct-only-in-the-appendix pattern as INDUCTIVES.md's
"Wiring" section (finding 3.4).

Everything downstream of the RBTree premise in `RECURSOR-DESIGN.md` is
therefore wrong or moot:

| site | claim | status |
| --- | --- | --- |
| §1.6 | "Interleaving is therefore corpus-demanded" via RBTree | true conclusion, wrong witness (`sepBy`, init-prelude) |
| §3.1 | `Slot` mask motivated by `RBTree.red`'s fields | motivation survives via `sepBy`; the RBTree spelling is wrong |
| §4.4 | acceptance: "`077_RBTree.id_spec`'s ι gaps close" | unreachable — §7.9 declines indexed families, so `077`'s ι sites stay counted gaps under this design |
| §4.4 | "`HAS_GAPS` flips `077` from expected-gap to unexpected-pass" | `077` is not in `HAS_GAPS` (`checker/tests/tg_tutorial.rs:116` — it is `["075_nRecReduction", "076_listRecReduction"]`), so no such signal exists |
| §5.2 | "(`RBTree` has `leaf`, so `077` is policy 2)" | moot |
| §7.2 | "the interleaved shape's first exercise is `077`" | false — `077` will be declined; first exercise is `init-prelude` |
| §8.5 | "Wire `RBTree` (`068`/`077`) first — the only corpus shape the hand-written bottoms cannot reach, so its ι gaps closing is unambiguous credit" | wrong wiring target; would produce zero credit and misattributed gaps |
| §9.1 | "verify `val_i` against `RBTree.red`'s `RecRule::rhs`" | the right instinct, wrong declaration — use `ParserDescr.sepBy`'s |

**Corrected statement:** the general (non-indexed) recursor's corpus witnesses
for `m ≥ 2` and interleaving are `Lean.ParserDescr.{binary, sepBy, sepBy1}` in
`init-prelude`; the tutorial corpus exercises the shape only through the
indexed `RBTree`, which the spec builder must decline and count. `077`'s ι gaps
are unreachable until indexed families (§5.2 `good`/`spec`) land.

### 1.2 The wrong `RBTree.red` signature has already propagated into code headers

Same failure mode as the `116` claim propagating into three files:

* `derived/src/inductive/spec.rs:77–78` — "the corpus demands interleaving
  (`RBTree.red : N → RBTree α → α → RBTree α → RBTree α` is
  `Plain, Rec, Plain, Rec`)". The mask matches the fields, but the signature is
  misquoted (both indices dropped) and the declaration cited is out of the
  module's own scope. Corrected witness: `Lean.ParserDescr.sepBy`
  (`Rec, Plain, Rec, Plain`, non-indexed, init-prelude).
* `derived/src/inductive/premise.rs:142` — "Used by tests to pin the
  `RBTree.red` spelling before anything is wired." Same correction.

### 1.3 The known `116` claim — all four sites, one more than the brief listed

Confirmed against the export: `RTree.node`'s single field is
`children : (∀ _ : Bool, RTree) → RTree` — a *function-typed* recursive
argument (`γ = Bool`), not two-or-more plain recursive arguments
(`116_rtreeRecReduction.ndjson`; same declaration in `115_rTreeRec`).

* `README.md:210–212` (Remaining work, item 1) — "the cheap next step is a
  constructor with two or more recursive arguments (`116_rtreeRecReduction`),
  which changes only the fibre".
* `INDUCTIVES.md:1455–1460` (end of the `List.rec` log entry) — "…`f` and `r`
  are still single sets, over a two-point domain instead of `1` … and
  `116_rtreeRecReduction` (10 gaps) is the corpus test for it."
* `derived/src/wlist_rec.rs:212–216` — same claim, closing notes.
* `LIBRARY-BACKLOG.md:349–351` ("Checked and rejected") — "**A
  two-recursive-argument recursor by hand (`116_rtreeRecReduction`)** — in the
  in-flight general recursor/ι design's scope; building it now duplicates."
  **Doubly false**: `116` is not the two-recursive-argument shape, and
  function-typed recursive arguments are *not* in the general design's scope —
  §7.9 declines them. Nothing in flight covers `116`; its ι gaps are
  unreachable until the `Σ(z::γ)` fibre translation exists.

Note when fixing: `RTree` *is* the natural W-type with fibre `Bool`, so "changes
only the fibre" is truer of the W-type picture than of the current machinery —
but the current machinery (`recarg.rs` `finord(m)` fibres, packed steps with
one `app(f, Inj_j •)` per rec-arg) does not cover it, and the reduct contains a
lambda under the minor, which is the real reason §7.9 excludes it.

### 1.4 `kernel/README.md` — "Why beta is not yet derivable" (trusted-crate README)

`kernel/README.md:449–491`. The section is titled **"Why beta is not yet
derivable"** and closes with:

> "So closing beta means extending the `Certifier` boundary beyond equality to
> carry typing judgements, and threading those through the checker's `infer`
> alongside the existing equality certificates. That is the substance of the
> remaining milestone-3 work…"

Every part of this has been done, most of it since 2026-07-30:

* beta is derived — `derived/src/funcs/beta.rs` (`beta_conditional`,
  `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))`), wired through
  `Certifier::beta`, and the beta-exercising tutorials (`006`, `007`, `028`,
  `029`) have long been at zero gaps and zero escapes;
* typing judgements exist and are threaded — `TgBackend::has_type` family
  (`checker/src/tg.rs:6763` ff.), and `infer` returns typing evidence
  (`Inferred { ty, cert }`, MEASUREMENTS "Inference carries its evidence").

This is a false current-state claim in the trusted crate's own README — the
exact failure mode this audit exists for. The section also cites
"`tests/define.rs`" as if in `kernel/tests/`; that file does not exist there —
the demonstration lives at `derived/tests/define.rs`. The section's *content*
(beta is conditional; the antecedent is a typing fact; why the interpretation
is type-directed) is correct and worth keeping as rationale — the fix is a
retitle and a rewrite of its frame from "remaining work" to "why beta is
conditional, and what discharging it took", with the test path corrected.

### 1.5 `LEVEL-POLYMORPHIC-INDUCTIVES.md` — `DEFAULT_LEVEL = 0`

Line 54: PUnit's `Prop` instantiation is reachable "…through
`DEFAULT_LEVEL = 0` for undemanded declarations."

False when written *and* stale now. The recorded choice at the time was
`DEFAULT_LEVEL = 1` (MEASUREMENTS, "The default instantiation is a choice…":
"Since 27/27 on the fragment is the acceptance criterion for this design, the
default is 1"). Today the constant is
`instantiations.rs:117 — pub const DEFAULT_LEVELS: &[u32] = &[0, 1]`. The
section's conclusion ("the `Prop` instantiation of `PUnit` is not a corner case
the schedule avoids") happens to be rescued by the later `[0, 1]` change, but
its stated mechanism was wrong on the day it was written.

### 1.6 `INDUCTIVES.md` — `HAS_GAPS` "is currently empty"

Line 380–382: "`HAS_GAPS` in `checker/tests/tg_tutorial.rs` is currently empty
and asserts `gaps > 0`…". It is not empty:
`tg_tutorial.rs:116 — const HAS_GAPS: &[&str] = &["075_nRecReduction", "076_listRecReduction"]`.
The mechanism described (a closed gap surfaces as an unexpected pass) is real;
the population is stale. See also 1.1's `077` row.

---

## 2. STALE numbers

### 2.1 `README.md:69` — "kernel/ is **625 non-comment lines**"

Counted with the CI method (`grep -vE '^\s*(//|$)'` over `kernel/src/*.rs`):
**662**. `kernel/README.md` has it right ("662 today"); 625 is the
pre-hypotheses figure (625 → 662 is recorded in both kernel/README and
DECISIONS). The 700 budget claim is correct.

### 2.2 `README.md:132` — "derived/ (19,900 lines, untrusted, 384 tests)"

Today: **~34,100 non-comment lines** in `derived/src` (48,600 including
`derived/tests`; 57,700 raw source lines), and **558 `#[test]` functions**
across `derived/{src,tests}` (static count; the last recorded `cargo test`
figure was 548, and `acc`/`quot`/`trunc`/`genrec` have landed since — RACE on
the exact number, but 384 is several landings old either way).

### 2.3 `README.md:143–151` — coverage headline "68 of 91 … and 79 have zero escapes"

The last recorded values at the *current* default (`DEFAULT_LEVELS = [0, 1]`)
are **69 files at zero gaps / 79 at zero escapes** (222 gaps / 77 escapes),
and the combined tree of 2026-08-01 recorded 70/79 at the `[1]` default
(MEASUREMENTS, final sections). The tree is mid-edit; pin with a run. The
27/27 zero-gap zero-escape fragment claim is consistent with every recorded
measurement and was held at every default set.

### 2.4 `README.md:236–244` — the sample stepcount block

The illustrative provenance block still shows `admit whnf 2681`,
`admit lazy_delta 1126`, `admit eq_cache 687`, `TOTAL admitted 4520`. Those are
the 2026-07-30 numbers: `whnf` went 2681 → 145 → 0 and `lazy_delta` 1126 → 0
the same day (`whnf` emits evidence), and `eq_cache` is 272 since the
proof-carrying union-find. As a sample of the *format* it works; as numbers it
no longer resembles any current run and understates the project's own progress.

### 2.5 `INDUCTIVES.md:529–531` — "`MAX_TYPE_DEPTH = 16` kept as a termination bound"

Removed since: `tg.rs:6684` ("There used to be a constant here,
`MAX_TYPE_DEPTH = 16`…"), replaced by per-edge visited sets (MEASUREMENTS,
"`MAX_TYPE_DEPTH` is gone, replaced by visited sets"). The State-section note
predates the removal.

---

## 3. STALE — overtaken by changes that landed (mostly acknowledged elsewhere)

### 3.1 `QUESTIONS.md` §1 — the definitional-equality cache — is resolved, not open

The checker-side fix it exists to track has landed:
`checker/src/certify.rs:591` — `is_unconditional` is
`c.thm().is_some_and(|t| t.hyps().is_empty())` — gating the equality cache at
`tc.rs:1864`; the reduct memo is gated by the weaker `hypothesis_free` at
`tc.rs:1292`; `kernel/README.md` records "The checker has taken option 1" and
retracts its own "the state today by default" warning. §1 should move to
"Answered, kept for the record". (Its title also cites `thm.rs`'s section as
"THE CACHE OBLIGATION"; the section is now titled "THE `hyps()` OBLIGATION",
`thm.rs:143`.)

### 3.2 `LOCALS.md` §6 and §7 — the three-line fix and the other stores

§6 states as current: "`certify::is_unconditional` is currently:
`c.is_proved()`". Landed (see 3.1). §7's table rows are equally stale:
`reduct::Trace::cert` is no longer "a third hypothesis-carrying store … with no
guard at all" (guarded by `hypothesis_free`), and the `infer_cache_*` premise
is no longer "asserted, not enforced" (it is `debug_assert`ed at the single
insertion point, with the transitive-into-binder-types reading —
DECISIONS 2026-07-31, "Three stores, not one"). The file's status header dates
it, but a reader of §6–§7 alone would re-do finished work. §5's stamp design
and §9's open questions are unaffected.

### 3.3 `LEVEL-POLYMORPHIC-INDUCTIVES.md` §4.5 / §7.2 — `ctor_rules` keyed by name only

Already fixed (RACE): `tg.rs:3781` —
`ctor_rules: HashMap<(NamePtr<'t>, Vec<Term>), CtorRule>`, populated and read
at `(name, levels)` (6226, 6348–6349, 7483). The "bug-shaped finding" was
real when written; a concurrent agent has since keyed it correctly.
`RECURSOR-DESIGN.md` §7.10 ("fix the key … when touching the wiring") is
likewise already done.

### 3.4 `INDUCTIVES.md` "Wiring" section — "The `Certifier` trait has no `iota` method"

Lines 384–399 state as current: the trait "carries `refl, symm, trans,
app_cong, lam_cong, pi_cong, beta, zeta, delta, eta, sort, const_eq, admit`"
and ι's certificate "is `admit(_, _, "iota")`". Superseded on 2026-07-31:
`iota` is a trait method with a default delegating to `admit`
(`certify.rs:174`), route 1 was taken, and the trait also carries the
`has_type`/`declar_checked` family now. The file's own log corrects this ~500
lines later, but the section itself reads as current fact and steers a
top-down reader at the exact decision (route 1 vs 2) it gets wrong.

### 3.5 `INDUCTIVES.md` State table / `RECURSOR-DESIGN.md` header — RACE

State rows "wiring the general translation into the checker — not started" and
"the general recursor and ι — not started", and RECURSOR-DESIGN's "Design only;
no code": `derived/src/inductive/{recursor,step,iota,premise,typed,computes,…}.rs`
and `derived/tests/genrec.rs` (9 tests) exist. The tasks are literally in
flight; update the table when they land.

### 3.6 `LIBRARY-BACKLOG.md` — every READY entry has already landed or is mid-build — RACE

All five: entry 2 (`derived/src/ext/dprod_universe_n.rs` and
`derived/src/universe/replacement_n.rs` exist — the exact files the entry
names), entry 3 (`derived/src/sums/in_universe.rs`), entry 4
(`derived/src/tower/cumulative.rs`), entry 5 (`derived/src/prop/trunc.rs`,
which calls itself "the third conditional singleton" — so the entry's
"Verified missing: … no third exists" is no longer true), entry 6
(`derived/src/quot/{eqv,classes,lift,compat,witness,…}.rs`). Entry 1 (`acc`,
"DONE") was verified **correct**: the seven submodules and
`derived/tests/acc.rs` with exactly 12 tests are as stated. The backlog was
compiled yesterday evening against 543 tests and has been almost fully
consumed in a day; its status column is now historical.

---

## 4. Minor

* `README.md:72` — "the rules (modus ponens, generalisation, reflexivity,
  Leibniz)" omits the two structural rules `assume`/`implies_intr` that came
  with the sequent change (and instantiation/distribution, if "five logic
  axioms" is not meant to cover them). `kernel/README.md`'s itemisation is the
  accurate one.
* `kernel/README.md` — "Demonstrated end to end in `tests/define.rs`": the file
  is `derived/tests/define.rs` (inside the 1.4 section, fix together).
* `LOCALS.md:8` — cites `kernel/src/thm.rs` "*THE CACHE OBLIGATION*"; the
  section is now "THE `hyps()` OBLIGATION".

---

## 5. Module-header sweep

### 5.1 `checker/src` (all spot-verified against the code)

**FALSE — "`gen` needs no side condition, since a `Thm` carries no
hypotheses", four sites in `checker/src/tg.rs`:** lines 10008–10009,
10088–10089, 11133–11134, 12012–12013. Since `Thm` became a sequent, `gen`
*has* the classic side condition `x ∉ FV(Γ)`: `gen_checked`
(`kernel/src/thm.rs:650`) returns `None` on violation and `Thm::gen`
(`thm.rs:610`) is the wrapper that **panics**. The attached safety argument
("a slip could only make the `mp` below fail, never produce a false claim")
is also wrong in direction — a hypothetical premise reaching these sites
panics rather than failing closed. These four comments carry the pre-sequent
absolute-validity premise verbatim, without the "no rule here builds a
hypothetical `Thm` *today*, and CI pins that" caveat that
`certify.rs:577–581` states correctly. This is prose in untrusted code, but
it is the same retired soundness argument the kernel README explicitly
retracted ("a retired soundness argument standing beside the code it no
longer justifies is how the next reader deletes the check").

**FALSE — `checker/src/tc.rs:1504–1505`:** the doc comment on
`def_eq_binder_aux` says "The `lam_cong`/`pi_cong` rules in the backend are
the ones that will discharge the generalisation; **today the whole chain is
admitted as `BINDER`**." Contradicted by the body of the very function it
heads: `tc.rs:1573–1601` folds `pi_cong`/`lam_cong` and calls
`bump_certified()`, the inline comment at 1564–1566 says the opposite
("this whole path is certified rather than admitted"), and `Admit::Binder`
is raised nowhere in the crate. Stale since 2026-07-30 ("Real congruence
certificates", binder 4,978 → 0).

**STALE — `checker/src/tc.rs:1568–1572`:** "…what keeps the resulting
certificate valid absolutely rather than relative to a local context — and
hence what keeps the equality cache globally sound." Generalisation is no
longer sufficient for cacheability: the write is gated on
`certify::is_unconditional` (`tc.rs:1864`), because a context-free
`Γ ⊢ a = b` is exactly what is *not* globally cacheable. This is the
sentence `certify.rs:563–581` was written to correct; it survives here
unamended.

**STALE — `checker/src/certify.rs:634–642`:** `Admit::Binder` ("Structural/
alpha comparison of two binder chains") and `Admit::App` ("Congruence over a
spine of applications") are documented as live holes — "the deeper structural
comparisons … still admit" — but neither variant is constructed anywhere
(only `name()` and `ALL` mention them). `Admit::Iota` got a
"no longer raised" annotation when it closed; these two never did, so the
admit ledger's documentation lists two holes that do not exist. The enum doc
("Every variant is a hole that milestone 3 must close") is wrong for both.

**RACE — `checker/src/instantiations.rs:117`:** during the audit the constant
briefly read `DEFAULT_LEVELS: &[u32] = &[1]` (file mtime minutes before the
read) while its own header and `tg_tutorial.rs` say `[0, 1]`; on re-read it
was `&[0, 1]` again. A concurrent agent A/B-ing the constant — not a prose
defect, recorded so the window is known.

**Checked clean in `checker/src`:** `certify.rs`'s cache-obligation prose
(names the sequent change, the `is_proved()` → `hyps().is_empty()` fix, all
four `Thm` stores — current and correct); `instantiations.rs`'s header and
default-set discussion (describes a list); every surviving
`MAX_TYPE_DEPTH`/`MAX_HOLES`/`MAX_HYPS` reference is past-tense; `ctor_rules`
docs match the `(name, levels)` key; `Certifier` docs match the trait
(`iota` at 174, `has_type` family, `NullCertifier` under
`cfg(not(feature = "tg"))`); `infer`-returns-evidence framing is past-tense
where it recalls the old shape; the eviction note reads as withdrawn and no
other comment recommends eviction; `tg.rs:423–430`'s constructor-head list
makes no indexedness claim; no `ax_empty` or 1000-budget references;
`reduct.rs`, `union_find.rs`, `stepcount.rs` headers consistent with their
code.

### 5.2 `derived/src` (headline findings spot-verified against the code)

The recurring shape here is a header written *before* the 2026-07-31
transitivity clause and the `⋃`-closure derivations, still presenting closure
properties as open/needing-CSB when they are now theorems exported from
`derived/src/universe.rs` ("Settled" list, lines 188–246: `⋃a ∈ u`,
`a ∪ b ∈ u`, `prod`, `fs`, `img`, `app`, pairing — all proved).

**FALSE — `derived/src/recursion.rs:36–41` (module rationale):** "the closure
properties are open rather than refuted; **none of them is proved, so the plan
below is unchanged** … bound finitely-branching W-types by an ω-indexed tower
… recursion is **the critical path either way**." Three ways wrong: the
closure properties *are* proved (`universe_union_closed`,
`universe_bin_union`, `product_in_universe`, `funspace_in_universe_pair`,
`dprod_in_universe_pair`, all re-exported); the ω-tower is *not* how W-types
are bounded (`inductive/carrier.rs` bounds every declaration at `U({A,T})` by
the transitivity clause, and INDUCTIVES records "the transitivity clause
removed the need for the ω-tower — do not restart it"); and the cited
`crate::empty` "open middle" no longer exists (`empty.rs:62–66` records that
`C₁` removed the obstruction). A reader of this header would restart exactly
the work INDUCTIVES warns against restarting.

**FALSE — `derived/src/recursion.rs:55–66` and `recursion/succ.rs:26–29`:**
"what is still missing is `⋃n ∈ u`, which needs `C₄`'s equinumerosity
disjunct refuted" and "pairing … needs the *inaccessibility* clause, i.e. …
cardinal arithmetic". Both are theorems today: `universe_union_closed` and
`universe_pairing` (the latter via three power-tower members and pigeonhole —
no cardinal arithmetic, `universe/pairing.rs:19–39`).

**FALSE — `derived/src/recursion/theorem.rs:181–200` (closing note):**
"`W(A,B,u) ∈ u` is still open, and it is the whole reason this file exists."
It is **refutable**, not open (`cumul.rs:101–125` proves the point;
`cumul/wmem.rs` repeats it), `cumul.rs:127–147` records that two of the
note's three next-step bullets are "the wrong shape", and everything the note
lists as next was done in `crate::cumul`.

**FALSE — `derived/src/isum.rs:32–36`:** section "# Nothing here is a new
symbol": "this module adds no definitional extension and no axiom".
Contradicted by the same header's own table six lines up (`symbols.rs`:
"`Sum_n` and `Inj_i` as **real symbols**") and by `isum/symbols.rs`, which
calls `define_abbrev` per arity/depth. The section predates the 2026-08-01
symbols change (known movement: isum is now real defined symbols) and was not
updated with the table.

**FALSE — `derived/src/universe/pairing.rs:43–45`:** "No binary union is
involved — see `crate::universe` for why that closure property is **the one
that is still missing**." The pointer's target says the opposite: binary
union is under "**Settled**" and `universe_bin_union`/`least_universe_bin_union`
are exported.

**FALSE — `derived/src/bound/funspace_universe.rs:22–24`:** "`(a ∪ b) ∈ U(c)`
… is open, not refutable". Proved (`least_universe_bin_union`,
`product_in_universe`); `funspace.rs:81–89` says "The two-argument case is now
complete", and the `bound.rs` hub already carries the corrected statement —
only this leaf drifted.

**FALSE — `derived/src/tower.rs:118–120`:** "…no recursion theorem is needed —
which matters, because `crate::recursion` **does not have one**."
`recursion::recursion` is the recursion theorem, complete and re-exported
(`recursion/theorem.rs`, "The recursion theorem, and the symbol it
licenses"). The first half of the sentence stands; the causal clause is false.

**STALE — clause-ordinal drift after `C₁`:** `is_universe` has four clauses
and inaccessibility is now the *fourth*, but three sites still call it "the
third clause": `universe/inaccessibility.rs:54` and `:183`,
`universe/pairing.rs:574`. (`universe/closure.rs:41` and
`funspace/closure.rs:15` correctly say "fourth".)

**STALE — `derived/src/cumul.rs`, two internal disagreements:** line 24 calls
`⟦N⟧ ∈ ⟦Type 0⟧` "the largest remaining wall in the checker" while lines
266–270 of the same file record that `tg.rs` now consumes it (`IndTy`
clause); line 293 says "`Peano` is not `Clone`" while lines 277–279 record
that `Peano` (and five others) became `Clone` — `recursion/peano.rs` derives
`Clone`. The later (2026-08-01) sections are right in both cases.

**STALE — `derived/src/cantor/image.rs:26–28`:** "would need the very product
closure **that is not available**" — `product_in_universe` is available; if a
layering cycle still prevents its use there, the sentence should say that
instead.

**Low — `derived/src/fibre.rs:27,43` and `recarg.rs:8,75`:** doc links for
`finord`/`inj_distinct` still resolve to the `tags::` nest formers, while the
code and the exported statements use `ISumSyms`/`Sum_m`; `fibre.rs:43` spells
the value as the nest term. `derived/src/acc.rs:39` says "1291" lines for the
module; it is 1298 (the other two figures in that sentence are exact).

**Confirmed, no further occurrences:** the `116` claim exists in exactly one
`derived/src` file (`wlist_rec.rs:213–216`), and the wrong `RBTree.red`
signature in exactly one (`inductive/spec.rs:77`; plus the test pointer in
`inductive/premise.rs:142`). *(Both closed since: `derived/src/inductive/
spec.rs:118` now opens "This comment used to cite `RBTree.red` as…", and
`RBTree.red` appears in four further `derived/src` files as a legitimate
indexed-family example — `inductive/family/{prop_rec.rs:63, carrier.rs:82,
carrier.rs:123, index.rs:32}`. The "exactly one" count is a record of the sweep,
not a live invariant.)*

**Checked clean in `derived/src`:** every CSB/`is_universe(U(x))` mention in
`funspace*`, `ext*`, `universe*`, `tower.rs`, `cantor*` now correctly says it
is not needed (modulo the ordinal drift above); `hyp.rs` and all four
submodules open with SUPERSEDED; `wlist.rs`/`enums.rs`/`wlist_rec.rs` headers
accurate *(the entry also covered `wnat.rs` and `wnat_rec.rs`, including
`wnat.rs`'s ω-tower-not-needed note; **both files were deleted on 2026-08-11**
and that half of the line is void — see §8)*; no stale
`ax_empty`/`MAX_*` references; the "eight axioms" figure matches `thm.rs`
*(the phrase no longer occurs in `derived/src`, so the site this checked is
gone — §8)*;
~~all checked cross-references into `checker/src/tg.rs` resolve~~ — **false
today, §8**; every
`tests/<name>.rs` named in a header exists; `inductive/carrier.rs`'s "eight
declarations" matches `derived/tests/inductive.rs`.

---

## 6. Checked and found correct

Worth recording so the next reader does not re-verify:

* **Corpus counts**: 102 `good` / 55 `bad` arena files, 91 tutorial files, two
  declined arena files — as stated in README and DECISIONS.
* **kernel/README.md's numbers and mechanisms**: 662 non-comment lines against
  the 700 budget (recounted with the CI script's own method) — *the count is
  **697** on 2026-08-14, recounted the same way; the 700 budget still holds,
  with three lines of slack, but this figure is now the number to watch and not
  a do-not-re-verify one;* `lib.rs` "six
  lines" is right under the non-comment convention (6 code lines);
  `ci/check-boundary.sh` really enforces the `Thm::assume`/`implies_intr`
  grep, the budget, and the dependency table; `kernel/tests/{tarski,
  replacement, choice, rules, hypotheses, substitution}.rs` all exist;
  `rules.rs` really asserts `ax_empty` stays gone; `ax_empty` is really deleted
  from `thm.rs`; `derived::empty::empty_existence` exists.
* **`ax_tarski`'s doc comment** now states all five clauses, says explicitly
  that Tarski's Axiom A alone does not entail transitivity, and cites the
  countermodels — the "Grothendieck" framing that caused the CSB detour is
  repaired, consistent with INDUCTIVES' "Resolved" note.
* **README's instantiation-pre-pass paragraph**: 2652 pairs / 2059
  declarations / 13 rounds, 2366 → 12 and 336 → 36, 446-of-449 and 136-of-137,
  5718/660 Π sites at 41%/51%, 1.14×/1.16× cost, audit row zero with a test —
  all match MEASUREMENTS' recorded tables exactly.
* **`TgBackend::iota` tries `proof_eq` first** — RECURSOR-DESIGN §5.1's
  `[read]` cite is accurate in substance. **The line number given here,
  `tg.rs:12096`, was wrong on the day it was written**: at this audit's own
  commit `cb2d188`, `tg.rs:12096` is a doc comment about `derive_pi_cong` and
  `fn iota` was at `:12123`. The body is right — `proof_eq` is the first thing
  tried — but a citation that was never read is exactly what this file exists
  to catch. Today it is `checker/src/tg.rs:19894–19896`, still `proof_eq`
  first, and `Certifier::iota` is `checker/src/certify.rs:174`.
* **LIBRARY-BACKLOG's citations**: the `MEASUREMENTS.md:` line numbers
  (343–345, 366, 809, 1013, 1175, 1224, 1524–1529, 1536–1540) all say what
  they are cited for; the thesis line numbers used across LIBRARY-BACKLOG,
  RECURSOR-DESIGN and LEVEL-POLYMORPHIC-INDUCTIVES (1705–1709, 1788, 1800,
  1826–1830, 1885–1901, 2106, 2109, 2124, 2126, 2146–2153, 2160–2166, 2184,
  2284) were checked against the extracted `thesis.txt` and match.
* **The eviction note** in `tg.rs` (~3096) really is corrected in place and
  reads as withdrawn, as MEASUREMENTS claims; `MAX_HOLES`/`MAX_HYPS` sites
  are marked "there used to be".
* **The cache guards** match kernel/README's account: option 1 taken,
  `is_unconditional` at the eq-cache write (`tc.rs:1864`), `hypothesis_free`
  at the reduct memo's write (`tc.rs:1292`).
* **`042`/`068`/`077` agree with each other** on the RBTree declaration
  (so the 1.1 finding is not a per-file quirk), and `077` additionally
  declares the indexed `Eq` exactly as INDUCTIVES describes for `076`.
* **`Lean.ParserDescr.binary/sepBy/sepBy1`** are the only plain `m ≥ 2`
  constructors in `init-prelude` (exhaustive scan), giving the design a real
  in-scope witness including an interleaved mask.

## 7. Not checkable without building or running

* Every *current* gap/escape/derivation count: tutorial totals, files at
  zero, `init-prelude` figures, fragment 27/27, arena 152/0/2. Five agents are
  editing; any number recorded this morning may already be wrong. The last
  recorded values are in MEASUREMENTS' final sections (at
  `DEFAULT_LEVELS = [0,1]`: tutorial 222 gaps / 77 escapes / 69 at zero gaps /
  79 at zero escapes; `init-prelude` 16422 / 2288; pairs 3861; fragment 27/27
  under all three default sets). A `--features tg` run pins them.
* The exact `cargo test -p derived` count (static `#[test]` count is 558).
* `LEVEL-POLYMORPHIC-INDUCTIVES.md`'s "129 inductives checked" sweep of
  `init-prelude` and the PUnit occurrence-level list (the file itself flags
  the schedule membership of `(PUnit, [0])` as unmeasured).
* Whether `077`'s remaining gap composition still matches MEASUREMENTS' last
  probe (53/31) — needs a run.

---

## 8. Second sweep — 2026-08-14, against the unified checker

*Audit of the root-level `*.md` against the tree at `b91433b`, on the owner's
instruction, after the mini/checker merge landed. Same method as §1–§7: every
correction below was established by reading code, and each names the
`file:line` it rests on. Where a claim could not be settled cheaply it is
marked unverified here rather than deleted or blessed. Corrections were made
**in place** in the documents; this section is the index, not the correction.*

### 8.0 The ground truth these corrections are measured against

Established first, by reading, and cited throughout:

* The workspace is `members = ["kernel", "derived", "checker"]` (`Cargo.toml:3`).
  There is no `mini` crate and no mini binary. The surviving mini
  implementation is modules under `checker/src/mini/` (`checker/src/mini.rs:63–122`),
  its tests are `checker/tests/mini_*.rs`, and the workspace's two binaries are
  `checker` (`checker/src/bin/checker.rs`) and upstream nanoda's `nanoda_bin`
  (`checker/src/main.rs`).
* One checker: one parse, one `Instantiations::compute` (`checker/src/mini/convert.rs:336`,
  whose published `Arc` is the schedule `RoutedChecker::new` receives at
  `route.rs:311`), one loop over declaration groups, one dispatch on kind.
  `Mode` has the single variant `Split` (`route.rs:70–74`) and it is the default
  (`bin/checker.rs:125`): inductives, mutual blocks and quotients → the mini
  implementation; definitions, theorems, opaques **and axioms** → nanoda
  (`route.rs:114–124`). Nanoda emits TG evidence in the same call as
  acceptance, so the driver's evidence step for a checker-routed group is empty
  by design (`route.rs:334–350`).
* **No fallback, no repair sweep, no second validation pass.** `route.rs:38` is
  the header saying so; a nanoda rejection or missing export group returns
  `Err` (`route.rs:374–414`); unclaimed anchors are observed and never checked
  (`route.rs:416–431`, `routed.rs:215–217`). The route counters are
  `toMini`/`toChecker`/`unclaimed` only.
* A nanoda-accepted ordinary declaration is mirrored **unchecked** into mini's
  syntactic environment: `install_checked_noninductive`, `checker/src/mini/kernel.rs:4867–4898`.
* `--naive` selects `Driver::Plain`, the historical whole-file mini checker, and
  is the only way to run that policy. `--route=…` **has been removed** and exits
  2 (`bin/checker.rs:115–118`).
* TG gaps are certification debt: exit 4, alongside `uncertified` and
  `untranslated` (`bin/checker.rs:250–254`); `--acceptance-only` suppresses the
  exit code only, not the columns.
* `⟦Nat⟧` is von Neumann `ω`, not a W-type (`checker/src/tg.rs:1638–1642`,
  `derived/src/inductive.rs:8`). `derived/src/wnat.rs`, `derived/src/wnat_rec.rs`
  and `derived/src/cumul/witness.rs` — with `NatUniverse`, `NatMem` and the
  `nat_shape` recogniser — are deleted; no definition of any of them survives.
  The general W-type machinery is untouched, and the `N` of the tutorial corpus
  (`041_natDef`) is a fixture's own inductive, not Lean's `Nat` — checked before
  any "W-type" sentence was edited.

### 8.1 Corrections, worst blast radius first

| # | document | what it said | what is true | how established |
|---|---|---|---|---|
| 1 | ENV-UNIFY.md, track D | a `--route` flag on a separate `mini` binary, three modes (`Split`/`ForceMini`/`ForceChecker`), axioms routed to mini, a counted fallback in **both** directions (`fellBack:name=reason`), and a post-loop sweep that **checks** unclaimed groups (`strays`) | all six are gone; §8.0 has the replacements one by one | read `route.rs`, `routed.rs`, `bin/checker.rs` |
| 2 | CHURCH-BASIS.md :42, :68 | "`em` and `Classical.choice` are **not** carried — `clause_for` has one arm" | `clause_for` has three arms including `Classical.choice`; `Clause::Choice` is built over `derived::choice::Epsilon` + `checker/src/mini/choice_clause.rs`, with tests | `checker/src/mini/axiom.rs:295–307`, `:220–223`, `:1100–1228` |
| 3 | LIBRARY-BACKLOG.md :501 | "`Classical.choice` is not [built], and it is not a library item — `ε` cannot be a term of the kernel's language" | built; the header now records the gain (`constEv` 3→7, library-gap 4→0, waiting rows 4→0) | `checker/src/mini/axiom.rs:220–223` |
| 4 | MINI-DESIGN.md §1 | a workspace member `mini/` with its own `Cargo.toml` and `mini/src/main.rs`; and "mini does not enable or touch the `tg`/`stepcount` features and never calls into `tc.rs` or `tg.rs`" | no such crate; and mini **does** reach both — `route.rs` drives `routed.rs` into `ExportFile::check_declar_scheduled`, `run.rs` calls `tg::global_gap_count`, and a non-`--naive` run *requires* `--features tg` | `Cargo.toml:3`, `bin/checker.rs:119–124` |
| 5 | MINI-HANDOFF.md :1128 | "the bare run is now an instrument … `mini <export>` runs to the end and exits 4" | a bare `checker <export>` is the **split** checker, not the whole-file mini one; that is `--naive` | `checker/tests/unified_cli.rs:54–68` |
| 6 | MINI-HANDOFF.md :295 | a worktree recipe building `-p mini` and running `target/release/mini` | neither exists; `-p nanoda_lib --bin checker`, then `checker --naive` | `checker/Cargo.toml:49–57` |
| 7 | NAT-REPRESENTATION.md :49 | links 1–2 were built over ω "while the checker uses the first" (the W-type), "which is why link 4 cannot be written" | the checker uses ω; there is one carrier | `checker/src/tg.rs:1638–1642`, `:1721`, `:1746`, `checker/src/mini/nat_clause.rs:57–81` |
| 8 | NAT-REPRESENTATION.md §6.1, §7.2 | "must `⟦Nat⟧` be `ω`? No, and it isn't"; "the general route's `⟦Nat⟧` is a W-type carrier that no binary numeral can be a term of" | the project answered yes and built it; §7.3 of the same file says "Built." eleven lines later | as above |
| 9 | INDUCTIVES.md :518 | "primitive `Nat`/`String` literals, already shelved *(still shelved.)*" | the `Nat` half is not shelved — a `NatLit` converts to a real literal, the `> 10` decline is gone; the `String` half is still true | `checker/src/mini/convert.rs:715–732`, `census.rs:280–289`, `ledger.rs:1755` |
| 10 | MATCHER-WALL.md §1, §2.6 | mimalloc as `#[global_allocator]` is worth −28 % and is "sitting unclaimed in the sibling binary" (the mini binary) | that binary is gone and the two lines did not move: `#[global_allocator]` occurs once in the workspace, `checker/src/main.rs:37–38`, which builds `nanoda_bin`. `checker/src/bin/checker.rs` — the binary every routed run and test spawns — has none, so the production checker runs on glibc and the win is still unclaimed | grep over the workspace |
| 11 | DECISIONS.md :3581 | the "one checker pipeline" decision, written as a forward plan and the log's last entry | landed in full at `4e86d46` and `8815abb` | `Cargo.toml:3`, `checker/src/mini.rs:63–122` |
| 12 | PIVOT.md §5 | "Today, in parallel": lift mini's indexed-family coverage **into** `tg.rs` | the opposite of the rule now in force — mini-owned inductive objects are authoritative and TG consumes them | owner's standing instruction; §6's crate-edge argument is also moot |
| 13 | ENV-UNIFY.md §3.8 | "mini today generates but never compares (`parseRecInfo` stub)" | half wrong: no full mint-and-compare, but a load-time **shape** comparison exists and is reported | `checker/src/mini/convert.rs:67`, `:621`, `bin/checker.rs:198–203` |
| 14 | ENV-UNIFY.md B6–B8 | gap totals quoted as standing controls — "remains 172", "`proj_reduced_carrier` stays 139" | true at their 2026-08-11 landings; four have since moved. Current committed ratchet: `nat_char_equations` **152**, `proj_reduced_subject` **2**, `proj_stuck_subject` **6**, `proj_reduced_carrier` **16**, `field_in_u0_by_carrier` **0** | `checker/tests/unified_cli.rs`; corroborated by MEASUREMENTS' 2026-08-14 census |
| 15 | ENV-UNIFY.md track A1 | the read adapter "`mini/src/genv.rs`" | never built; no such file | `ls` |
| 16 | ENV-UNIFY.md, "comprehensive merge, in progress" | in progress, wholesale | the structural half landed; outstanding are the cond mint (no `cond_store.rs`; `prop_infos`/`cond_by_sym` both live) and the entry collapse (`adopt_shared`, `divergent`, `alias` all still present) | grep over `checker/src` |
| 17 | README.md :192 | "`Bool`, `N` and `List` are interpreted as W-types" — next to this project's Nat work, reads as a claim about Lean's `Nat` | true of the corpus's own `N` (`041_natDef`); Lean's `Nat` is `ω` | `derived/src/inductive.rs:8` |
| 18 | SCOPING.md :2358, :2752; DECISIONS.md :2452; W-FROM-LFP.md :453; INDUCTIVES.md :41, :594; RECURSOR-DESIGN.md; WIRING-DESIGN.md :642; DERIVED-AUDIT.md F2 | `wnat` / `NatUniverse` / `NatMem` / `cumul/witness.rs` named as live | all deleted 2026-08-11. In each case the surrounding **finding** survives on its other consumers and was kept, not cut | `derived/src/cumul.rs:51–52`, absence of the files |

**Stale paths, repaired in bulk**: ~200 `mini/src/x.rs` → `checker/src/mini/x.rs`
and `mini/tests/y.rs` → `checker/tests/mini_y.rs` across 28 documents. Every
target was checked to exist before rewriting. Three do **not** resolve —
`mini/src/main.rs`, `mini/src/probe.rs`, `mini/src/termstats.rs` — because those
files were deleted rather than moved; they were left alone, since a rewritten
path would be a worse lie than a stale one. Two rewritten citations are known to
carry **drifted line numbers** as well (e.g. old `mini/src/kernel.rs:1836` is
`checker/src/mini/kernel.rs:2695`); the paths are fixed, the line numbers are not
re-derived and should not be trusted.

### 8.2 Re-verification of §6's "checked clean" lines

Prompted by the standing rule that a wrong "checked clean" is worse than no
audit. **One was false on the day it was written**: §6's
`TgBackend::iota` entry cited `tg.rs:12096`, but at this audit's own commit
`cb2d188` that line is a doc comment about `derive_pi_cong` and `fn iota` was at
`:12123`. The substance was right — `proof_eq` is tried first, then and now
(`checker/src/tg.rs:19894–19896`) — but the line was evidently not read.
Corrected in place at §6.

False **today** (each corrected in place above): the `wnat.rs`/`wnat_rec.rs`
header entry at §5 (two of its four files are deleted); "all checked
cross-references into `checker/src/tg.rs` resolve" (the one surviving explicit
cite, `derived/src/ext/dprod_universe_n.rs:31` → `tg.rs:6642`, now lands on an
inductive-shape guard, not the `Pi` clause decline it claims); the "eight axioms"
entry (the phrase no longer occurs in `derived/src`, so the site it checked is
gone); "662 non-comment lines" (**697** today, recounted with the CI script's
method — the 700 budget still holds, with three lines of slack); the "exactly
one `RBTree.red`" count (closed in place at `inductive/spec.rs:118`, and the
name now appears in four further files as a legitimate indexed-family example);
and the status header's "Nothing … cites this file" (`QUESTIONS.md:10` does).

Verified **true today**, and worth keeping as do-not-re-verify: `Certifier::iota`
is still exactly `checker/src/certify.rs:174`; `DEFAULT_LEVELS = &[0, 1]` is
still `checker/src/instantiations.rs:117`; the `MAX_TYPE_DEPTH`/`MAX_HOLES`/
`MAX_HYPS` references are all past-tense; `ctor_rules`' `(name, levels)` key
matches its docs (`tg.rs:3275`); `hyp.rs` and all four submodules open with
SUPERSEDED; every `tests/<name>.rs` named in a `derived/src` header exists; the
eviction note reads as withdrawn (`tg.rs:1563`); the cache guards are as
described (`tc.rs:2610` `is_unconditional`, `tc.rs:1721` `hypothesis_free`);
`HAS_GAPS = ["075_nRecReduction", "076_listRecReduction"]` (`tg_tutorial.rs:178`).
Several of these carry drifted line numbers, noted where they matter.

**Marked unverified rather than blessed or cut**, with the reason: everything
resting on the `.ndjson` corpus (the 102/55 arena counts, the 91 tutorial files,
the `042`/`068`/`077` RBTree agreement, and the exhaustive `Lean.ParserDescr`
scan — `vendor/` is absent from this worktree, so §1.1's headline finding is not
re-checkable here); `ax_tarski`'s "all five clauses and the countermodels";
README's instantiation-pre-pass numbers against MEASUREMENTS' tables;
LIBRARY-BACKLOG's ~30 `MEASUREMENTS.md:` line cites, all presumptively drifted
since MEASUREMENTS has grown; the CSB/`is_universe(U(x))` sweep across ~20
`derived/` files; and `inductive/carrier.rs`'s "eight declarations".

**One structural warning about §6 itself.** Its heading "Checked clean in
`checker/src`" was written on 2026-08-01, when `checker/src` was about fifteen
files. `checker/src` now also contains `checker/src/mini/` — sixty files that
were a separate crate then and were **never in that sweep's scope**. The heading
now reads as covering them and does not.

### 8.3 Reported, not fixed — for the seats that own them

* **`derived/src/cumul.rs` refers to `crate::wnat` in the present tense** at
  `:158`, `:164`, `:172`, `:231`, `:253`, `:395`, `:429` — a reader greps for the
  module and finds nothing. The surrounding mathematics (a W-type over `1+1` as
  the worked example of the general bound) is sound and is not about Lean's
  `Nat`; only the module references are dead. Left to the `derived/` owner: this
  was a documentation pass and the file is a shared boundary.
* **`NAT-BRIDGE-FEASIBILITY.md` was deliberately not edited.** The seat on
  `joachim/natchar-census` had already touched it at `e3544dc`. Its defects, for
  that seat: `:575` and `:731–733` state `⟦Nat⟧` is `derived::wnat`'s W-type and
  cite `derived::wnat::Nat::ty` and `wnat.rs`; `:752` says ι fires "on the W-nat
  the interpretation actually uses"; `:698` says "`checker/src/tg.rs` does not
  reach `derived::nat` at all", which is false (19 references, live calls at
  `tg.rs:1721` and `:1746`) and is contradicted by the file's own `:777`; and
  `:241`, `:264`, `:669` invoke `./target/debug/mini` and `cargo test -p mini`.
  The file already carries a correct correction at `:775–778` — the defects are
  the un-marked paragraphs above it.
* **`LEVEL-POLYMORPHIC-INDUCTIVES.md`, `MODELGEN.md`, `modelgen/` and everything
  under `kernel/` were out of scope** and are untouched.
* **`MEASUREMENTS.md` was deliberately not rewritten** — it is an append-only
  log whose dated entries are correct records. It was checked for standing
  architecture claims (`grep` for the two-crate, fallback, force-mode and
  stray-sweep vocabulary): **zero hits**, so nothing needed correcting. Its
  newest section (2026-08-14, the corpus-wide gap census) independently
  corroborates finding 14 above.
