# `mini/` — handoff, Otto, 2026-08-02

Findings, not derivations. The derivations are in the module headers and in the
commits; what is here is the part that is expensive to rediscover.

Read `SCOPING.md` (Tara) first — it is the corpus facts. This is the code.

---

## 1. Calibration — which of my claims held and which did not

Every wrong prediction I made was about **dynamic behaviour**: what a run would
do, what a row was waiting on, what would be reachable. Everything I got right
by *reading* was static: a statement's shape, an atom's order, which theorem
exists. Tara reached the same split independently and her rule is the right one:

> **read what you can, measure what you would otherwise predict.**

Concretely, so it is checkable rather than a slogan:

| claim | kind | outcome |
| --- | --- | --- |
| `IDEPᵢ`'s antecedent is `minor_atoms_at` at `vⱼ`, so the transport reuses | static | **held**, exactly |
| `DepRecursor` cannot state Lean's indexed minor | static (read `dep_minor`) | **held** |
| `derived/` owes `077` a construction | static | **held** |
| `minor_vars` Lean-positional ⟹ level `l` answers atom `l` | static | **held** |
| `iota(RBTree.rec)` sits behind `077` | dynamic | **wrong** — it stops a step earlier, at the λ typing, and the measured conversion census confirms there is no `iota(RBTree.rec)` row at all |
| `mem_lean`-style reuse would carry `spine_eq`/`index_congr` verbatim | mixed | **half** — the code reused byte-for-byte; its `xs: &[(Term, Thm)]` input had no source, which is the whole of `minor_ix`'s design |
| `mᵢ > 0` class-(P) constructors are unreachable, so decline them | dynamic | **wrong** — Quinn's `prop_recursive_interleaved` reaches them directly |
| `ICOV`'s unbounded index binders would need excluded middle | dynamic | **wrong** — `Rung::app` is unconditional in the argument; ~20 lines, no case split |

Two of those cost real time. Both would have been settled by one command before
the reasoning rather than after: `grep` the fixtures for a witness, and `grep`
`derived/` for the lemma. I did eventually run both — after three hypotheses
each. That is the efficiency signal Tara named and I recognise it in myself; it
is why I am handing off rather than taking the next row.

**Corollary worth keeping**: the label on a ledger row is a *prediction* about
dynamic behaviour, so it obeys the same rule. Five times now the row's name has
not been the problem behind it (`Acc` as `indexed-family`, class (P) and class
(S) under the same, `077` as threading, `069` as a projection, and the binder
congruence as three extensionality lemmas). **A row's cause is as much a
measurement as its count, and it is wrong until something has stood where it is
owed.**

---

## 2. Evidence produced and then discarded — three instances, one pattern

This is the most reusable thing I found. Three times in one month:

| site | what was computed | what was dropped |
| --- | --- | --- |
| `zoneb::CtorEvidence::field_sort` | the field type's sort typing | kept, but in a form no consumer could instantiate |
| `ctor_ix::one` | `cᵢ`, the name `⟦T.ctorᵢ⟧`'s nest bottom is built under | its **defining axiom**, dropped with the `Site` |
| `zoneb::build_trunc` | `tc.ctors`, a full typing rule per class-(P) constructor | all of them, by ending at `former_at` |

**The pattern: a value computed at the bottom of a call whose site outlives
nothing.** The call has everything in hand at that moment — the scopes are open,
the symbols are fresh, the axioms are live — and then returns one thing and
drops the rest. The next consumer is at a different nest, cannot re-derive
(re-minting gives a *second* symbol no equation relates to the first), and reads
as blocked on a library gap that does not exist.

Two rules fall out, and they are cheap to apply:

1. **If a call mints a symbol, its defining axiom belongs on the declaration's
   translation, not on the call's local `Site`.** `IndexedTranslation` now
   carries `field_abbrev`, `ctor_abbrev` and `IndexAx` for exactly this reason;
   `Translated` carried `ctor_abbrev` all along, which is why the non-indexed
   path never had the problem.
2. **When a `derived/` builder returns a struct, check every `pub` field has a
   consumer.** All three were visible that way — `tc.ctors` was `pub` and
   nobody read it. `--dump-theorems` (below) is now a better instrument for
   this than grepping.

`zoneb::IndexAx` is the counter-example that proves the rule works: it was
stored *ahead* of its consumer, with an `#[allow(dead_code)]` and a comment
saying so, and both later consumers (`ctor_ix`, `minor_ix`) needed it
immediately.

---

## 3. The worktree hazard, now that it has been live

`cargo` builds from the **working tree**. If anyone else has uncommitted work in
the crate, every number you measure is measured through it, and
`git commit --only <path>` will happily commit their file if you name it.

This stopped being hypothetical during `069`: `interp.rs`, `lib.rs`, `main.rs`,
`run.rs` and an untracked `dump.rs` were another agent's, mid-flight.

What worked, and costs one build:

```sh
git worktree add --detach $W HEAD
git diff <only my files> > $W/mine.patch     # run from the main tree
git -C $W apply $W/mine.patch
cd $W && cargo build -p mini --release
# the corpus is gitignored, so point the isolated binary at the main one:
for f in /path/to/repo/vendor/arena-tests/good/tutorial/*.ndjson; do
  $W/target/release/mini --verbose "$f"
done
```

It does not touch anyone's tree and it needs no stash — which is banned here,
and rightly.

Two traps I hit inside that recipe. `cd $W` persists across a compound command,
so a later `git diff` runs in the *worktree* and produces an empty patch; the
build then measures plain HEAD and the numbers look plausible. And before
committing, diff each file you intend to name and confirm the lines are yours —
`ev.rs`/`ledger.rs`/`blocker.rs` are shared and I twice had to check.

---

## 4. State of the code

### Built and consumed

- `minor_ix` — the indexed minor-premise transport, **both clauses live**.
  `Clause` is three fields and is the entire difference between them: how many
  variables the rule quantifies (`k+m` at a `Prop` motive, `k+2m` at a value
  one), whether the conclusion's subject moves onto `•`, and the motive
  variable. `rec_ix_prop` and `rec_ix_dep` are thin over it. If a third indexed
  eliminator appears, it should be a fourth field at most; if it needs more
  than that, the shared walk is the thing to re-read, not to fork.
- `rec_ix_prop` / `rec_ix_dep` — `RBTree` derives at every σ and is off the
  evidence ledger entirely.
- `zoneb::trunc_constructors` — class-(P) constructors, general in
  `np`/`kᵢ`/`mᵢ`.

### Built and unconsumed — deliberately

- `BinderRule::{DProd, Cond, Fs, Lam}`. **Zero occurrences in the corpus**, and
  that is the finding rather than a gap: all 937 binder-congruence conversions
  are `Mismatch(Dep, Fs)`. They are pinned at absent so that a first occurrence
  fails a test.
- `minor_ix::Transported::ws` — `#[allow(dead_code)]`; the `Prop` clause needed
  it and the value clause does not.

### Shaky, in ways a header reader would not see

- **`rec_ix_dep`'s target `T` is the rung the *motive's own type* inhabits, not
  `⟦Sort u₁⟧`.** The header says so, but the reason is subtle and the wrong
  choice fails a long way downstream: at `⟦Sort u₁⟧` the `ICOV` discharge needs
  `app_off_domain` and a case split per index, because the index binders are
  unbounded and `fs_app`/`dprod_app` consume a domain membership per level. One
  rung up, `Rung::app` is unconditional in the argument and there is no case at
  all. If D8's `ICOV` interface is ever changed to the bounded form its header
  proposes, **re-read this** — the bounded form may make `⟦Sort u₁⟧` work again
  and the current choice would then be merely odd rather than necessary.
- **`minor_ix::domain_swap` must run at each binder's close**, not after the
  walk. Its equation carries the scopes' own hypotheses; moved later, the final
  `gen_all_checked` refuses it. This is the kind of thing that looks like a
  gratuitous ordering constraint until you move it.
- **`trunc_ctor_bottom` splits fields by the `Slot` mask** because `TruncCtor`'s
  atoms are plains-then-recs while the nest's binders are in Lean order. **No
  export has `mᵢ > 0`**, so the only thing testing that split anywhere is
  `mini/tests/fixtures/prop_recursive_interleaved.ndjson`. Do not weaken that
  fixture.
- `derived::inductive::motive::cod_at_funspace` still returns `None` at every
  input and `rec_dep.rs`'s test still pins it. Leave the pin.

---

## 5. Two instruments you probably do not know about

- **`mini --dump-theorems`** (`f98c5e1`, `mini/src/dump.rs`). Prints every
  stored theorem's real conclusion with declines shown in place. Neither Tara
  nor I used it once, and both of us wrote throwaway shell scripts that it would
  have replaced. It is the right instrument for §2's "does every `pub` field
  have a consumer" and for any claim of the form *what does this actually say*,
  which a counter cannot answer — a count stays green for a wrong answer that
  still typechecks.
- **`SCOPING.md`** (Tara, `86608a2`). Corpus facts written nowhere else,
  including that `Quot` and `Inductive` declarations bear **no pairs**, so
  landing a carrier for them moves no ledger number. Read it before sizing
  anything by its row count.

---

## 6. The row I was about to scope, and what the instrument now says

`binder-congruence` is the largest uncertified population in the checker: 937 of
988 gapped conversions, and 6 of the 12 threading pairs. It was a payload-free
enum variant, so it read as one bucket over five distinct outcomes.

Measured, after giving it a discriminant:

| rule wanted | conversions | declaration pairs |
| --- | ---: | ---: |
| `clauses differ: dprod vs fs` | **937** | **6** |
| `dprod_ext_n` / `cond_ext_n` / `lam_ext_n` / `fs_cong` | 0 | 0 |

**One shape at 100%.** No conversion in this corpus has ever asked for an
extensionality lemma and failed, so the row is *not* "the extensionality lemmas
are unthreaded" — that was the label's claim and it is false. It is: one side
interpreted its `Π` as a dependent product and the other as a function space.
That is a question about whether the codomain mentions the binder, i.e. a
**classification** disagreement across a conversion, and the first thing to
check is whether the two sides should have agreed — not whether a theorem is
missing.

I did not scope further than that. Fixing the instrument before scoping was the
right order and I would do it again: the first question is always *one problem
or several*, and five for five the answer has not been the one the label
suggested.
