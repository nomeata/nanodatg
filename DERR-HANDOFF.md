# `derived/` → `DResult`: the rules, the traps, and what is left

Written for the seat that takes `inductive` and `cumul`, which are the long tail
and want a seat of their own. Everything here was learned by doing the first
nine modules; none of it is speculative, and the three places where a belief of
mine turned out to be wrong are marked as such, because those are the ones a
successor is most likely to re-derive.

The **rules** live in `derived/src/err.rs`'s header, next to the code they
govern, and that is the normative copy. This file is the seat-facing part: how
to size a module, what order to take them in, what has already been decided,
and what will bite.

---

## 1. Where the migration stands

Migrated, in order: `rules`, `nat` (another seat), `universe`, `csb`, `cantor`,
`separation`, `funcs`, `empty`, `acc`.

`derived/` outside `nat/`, at the time of writing:

```text
raw fallible kernel call sites    1 658
return None                       1 234
err::imported boundaries             18
```

`universe/` is at **zero** `imported` boundaries, down from fourteen.

The remaining work is concentrated: `inductive` (~450 sites), `cumul` (~376),
`rec_acc` (~298), `ext` (~271), `recursion` (~191), `quot` (~133), `bound`
(~112), `wpath` (~99), `wrec` (~98). Everything else is under 90.

---

## 2. Size a module by **call site**, never by file

This is the single most useful measurement rule, and it was learned the
expensive way. Three estimates in a row deflated by a factor of three to five:

| module | files mentioning it | files needing a patch | call sites |
|---|---|---|---|
| `separation` | 41 | **7** | ~28 |
| `funcs` | 149 | **70** | 157 |
| `empty` | 42 | **12** | 33 |
| `acc` | 38 | **3** | 18 |

Four in a row, none within a factor of three of its file count.

The gap is always the same thing: most files touch the module only through a
name that is **already an `.ok()` adaptor** (`hyp_syl` is in ~200 places) or
that is **infallible** (`or_intro_left`, `empty::empty`, the `Formula`
builders). Neither needs touching.

`funcs` was budgeted as the worst target in the crate on its 149 files and was
not. **Take the measurement before deciding the order.** The script shape:
enumerate the module's `Option`-returning exports, subtract the adaptors and the
infallibles, then grep for the rest with the module actually in scope.

---

## 3. What the migration does, per module

1. `-> Option<T>` becomes `-> DResult<T>`; `Some(x)` becomes `Ok(x)`.
2. Kernel primitives move to `crate::prim` — `Thm::mp` → `prim::mp`,
   `.as_imp()` → `.imp_parts()`, and so on. **`Thm::gen` stays**: it panics only
   when the generalised variable is free in a hypothesis, and outside
   `crate::nat` nothing assumes, so the side condition is unreachable.
   `crate::discharge` is still the only sanctioned introduction site.
3. Toolkit imports move to `crate::rules`.
4. Calls into modules that have **not** migrated go through
   `crate::err::imported("crate::foo::bar", …)`, which reports an `Assembly`
   naming the path at the caller's line. Every one is a debt: it is a refusal
   whose reason was dropped at the boundary.
5. Every `return None` gets a reason — `decline!`, `decline_at_caller!` or
   `assembly!`. This is the part that is not mechanical.
6. Consumers that still return `Option` take `.ok()?`. That moves the seam one
   layer out rather than widening it.

---

## 4. The verdict rules

### 4.1 Declined or Assembly: where did the value come from

* the checked value traces back to a **parameter of a public entry** — including
  one instantiated at our own terms and then compared — so the guard enforces a
  documented precondition. `decline!`. The contract working.
* the value was built **entirely from what this function derived**. `assembly!`,
  naming the check and attaching the operands. A bug, always.

A **private** helper's caller is the module itself, so guards on its arguments
are `assembly!`. That is why `universe/shared.rs`, `csb/shared.rs`,
`cantor/shared.rs` and `empty/readers.rs` are assembly throughout. Check
`mod x;` versus `pub mod x;` before deciding — it is the whole difference.

### 4.2 Shape versus fit: how it presents

* one argument's **shape** wrong — not an implication, not an equation, not a
  `∀` — stays **`Assembly`**. The operand *is* the diagnosis.
* two arguments not **fitting** each other — a term list longer than a
  quantifier prefix, a count that is not the symbol's arity, a premise that is
  not the lemma this entry composes — is **`Declined`**. Both look correct
  alone, so the reason is the whole content.

### 4.3 A fresh variable compared against caller data is a **decline**

Recurred in every module and went the same way each time. `csb_scheme`,
`csb_fixpoint`, `cantor::image_in_universe`, `no_diagonal_surjection` and
`funcs::cond_relation_unique` all draw working variables with
`env.fresh_var()` and then test them against caller-supplied formulas and terms.
Nothing the function did could have avoided the collision, and reporting a bug
for input the caller can fix is the wrong verdict. Rule 4.1 points at the
parameter, 4.2 calls it a fit, and the two agree.

---

## 5. Siting: the fold rule, and the trap in it

`#[track_caller]` **chains** through consecutively annotated frames and **stops
at the first plain one**. This was measured after I asserted the opposite;
`derived/tests/err.rs::track_caller_chains_and_a_plain_frame_stops_it` pins it,
because it is a property of the compiler and nothing else here would notice it
changing.

Two halves, and **the first without the second changes nothing**:

* annotate a function that is a thin composition over its arguments;
* **its own guards must then use `decline_at_caller!`**, because `decline!`
  expands to `file!()`/`line!()` and no annotation moves it. `rules.rs:108` —
  the site issue #99 complained about — was a `decline!`, not a shim failure.

### 5.1 The knob cuts both ways

"Thin composition" is necessary but **not sufficient**. The test is *"is the
line inside me worth more than the line above me"*. Annotating is a **choice to
discard one frame** in exchange for a more useful one, and it is wrong exactly
when the frame you would discard is the one that discriminates. The pair:

* `csb::csb_clauses` is two calls to `clauses::injection_clauses` and nothing
  else — as thin as a function gets — and is **not** annotated, because
  `injection_clauses` already is, so refusals already land on one of
  `csb_clauses`'s two call lines and which one says whether `F`'s clauses or
  `G`'s were malformed. Annotating would chain that out.
* `funcs::sets::union_intro` **is** annotated, precisely because
  `snd_in_union2` calls it at two lines, one per rung of
  `y ∈ {a,y} ∈ ⟨a,y⟩ ∈ f` — the attribute is what makes those two lines say
  which rung failed. `snd_in_union2` itself stays plain, for `csb_clauses`'s
  reason.

Same rule, opposite answers, one frame apart.

### 5.2 Never inside a closure

A closure carries no attribute, so `foo().map_err(|_| decline_at_caller!("…"))`
sites the decline at the closure and silently undoes the whole thing. Write the
`match` out. This cost one test cycle to find.

---

## 6. The check that keeps finding real defects

> **Wherever a destructuring runs before a comparison, the verdict depends on
> how far wrong the caller was.**

The destructuring reports `Assembly` with the operand; the comparison below it
reports `Declined` with the reason; which one a caller trips is decided by
*which* mistake they made rather than by whether they made one.

**Procedure.** For each public entry taking a `&Thm`, find the first
`prim::`/`Shape` call that touches it and ask whether a guard *below* that call
is meant to be the contract. If so, the destructuring is the contract check too,
and it declines.

Four instances found, the first three by accident:

| where | the two spellings of one mistake |
|---|---|
| `rules::inst_all` | no `∀` left, versus a `∀` at the wrong depth |
| `universe::least_universe_pairing` | a two-quantifier theorem, versus a three-quantifier one with the wrong body |
| `separation::separation` | `⊢ z = z`, versus `⊢ ∀z. z = z` |
| `funcs::separation_full` | the same, and it is what made a pinned test flip |

**Twice the doc header already claimed the behaviour the code lacked.**
`separation::separation`'s header said its four checks on the `empty` premise
"decline, and they are the whole of this entry's contract" — and they did not.
So read the header as a specification, not as a description: the documentation
is often already right and the code is what drifted.

---

## 7. Tests: pin the verdict, not the rejection

Every negative test that said `.is_none()` becomes `.expect_err(…).is_decline()`
or `.is_assembly()`, and where the reason is the finding, `assert_eq!` on the
reason string too. `is_err()` is not enough: the whole point of the type is the
split, and a guard drifting to the wrong side is exactly what regresses
silently.

Where a verdict is **wrong but not yours to fix** — because the refusal comes
back through an `imported` boundary from an unmigrated module — pin the
wrong-but-honest verdict *and name the condition that flips it*. That happened
once and it worked: `derived/tests/cantor.rs` asserted an `Assembly` named
`crate::funcs::separation_full` with a comment saying it would flip when `funcs`
migrated, and when `funcs` migrated the test failed, was inspected, and became a
decline with the history recorded in place. **Nothing in `cantor/` changed.**
That is the cleanest evidence available that the boundaries were the defect.

---

## 8. The probe, which is the reason any of this matters

A temporary `eprintln!` in `DerErr::assembly`, then the tutorial corpus:

```sh
cargo build -p mini --release
for f in vendor/arena-tests/good/tutorial/*.ndjson; do
  ./target/release/mini --verbose "$f"
done
```

It has fired **zero** times through nine modules. That is what makes an
`Assembly` line in a log a finding rather than noise, and it is a property worth
protecting: **the day it fires in normal operation, that is a real bug that was
being silently swallowed, and it goes first in the report.** Re-run it every
module. Remove the probe before committing.

The ratchet alongside it: `accept 89 / decline 2 / reject 0`, `constEv 218/218`.

---

## 9. Two things to leave alone, and why

### 9.1 `funcs::beta::beta_conditional_n` wraps `inst_all` in a closure

Both its call sites therefore report the one line inside the closure. It is not
the `decline_at_caller!`-in-a-closure bug of §5.2 — no reason is mis-sited — but
it is the same family, and it is a **restructure**, not a migration: fixing it
means inlining at two sites. Flagged rather than done, deliberately, because a
migration licence does not cover reshaping a derivation.

### 9.2 `funcs::{sets, coll, apply}` produce no new reasons at all

Every refusal in those three files is inherited from `rules` or `prim`. What
retiring their `imported` boundaries bought was the toolkit's reason arriving at
the line that composed the call — not a bespoke label. **Do not budget them as
reason-writing work; they are pure inheritance.** The same is likely true of
other thin apparatus files, and it is worth checking before estimating.

---

## 10. The hub adaptors, and what clears them (#97)

`Option`-shaped `.ok()` wrappers that exist for exactly one reason: `mini/` and
`checker/` call them with `?` from `Option`-returning functions, and `?` cannot
cross from `Result` to `Option`. This seat may not edit either crate.

| adaptor | at | called by |
|---|---|---|
| the ~40 in `lib.rs` (`syl`, `hyp_mp`, `inst_all`, …) | crate root, over `rules::` | `mini/`, `checker/` |
| `acc::{acc_intro, acc_pred_closed, acc_rect}` | hub, over `intro::`/`preds::`/`rect::` | `mini/src/{rec_acc,rec_acc_value,rec_acc_ap}.rs` |
| `Acc::{new, with_apply, over}` | over the `_checked` methods | `mini/src/{acc,interp}.rs` |
| `separation::hyp_syl`, `funcs::logic::hyp_syl` | over `rules::hyp_syl` | ~200 sites crate-wide |
| `universe::{universe_replacement_n, least_universe_replacement_n}` | over `replacement_n::` | `mini/src/interp.rs` |
| `funcs::{lambda_n, beta_conditional_n}` | over `funcs::beta::` | `checker/src/tg.rs`, `checker/src/sealed.rs` |
| `funcs::app_off_domain` | over `funcs::apply::` | `mini/src/rec_acc_ap.rs` |

They are a **migration seam, not a design**. The endgame is one commit per
consumer crate: switch `mini/` and `checker/` to `DResult`, delete the wrappers,
and `crate::syl` and `rules::syl` become the same function. Until then, new code
inside `derived/` imports from `rules::`/`beta::`/`replacement_n::`, and the
crate-root or hub name is for the two consumers that have not moved.

---

## 11. Working notes that cost time

* **`ci/check.sh` takes ~50 minutes.** Run it with `run_in_background`. A
  foreground wait that hits the 600 s tool timeout **SIGTERMs the running
  cargo**, and the step then reports `Terminated` as a failure.
* **Check `git log --oneline -1 origin/master` before believing a red.** Master
  is shared and moves under you; one red I reported was real when measured and
  fixed seven minutes later, and I then repeated the stale claim in two
  subsequent commit messages without re-measuring. A true-at-the-time claim
  repeated later is the same defect as a stale doc header.
* **Never a worktree or `target/` under `/tmp`** — it is a tmpfs here and
  compiling into RAM has taken the machine down.
* Delegating a module to two or three subagents with the recipe works well; give
  each the neighbouring files' status so `?` assumptions are right, and have
  them write to a scratch directory rather than the repo, so the tree only ever
  moves in one atomic step.
