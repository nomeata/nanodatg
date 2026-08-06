# Performance review — driven by the 2026-08-01 profile

*Scope: `init-prelude` (2059 declarations, the 3.7 MB export) through
`nanoda_bin --features tg`, release + debuginfo, single-threaded
(`num_threads` defaults to 0). Wall time 42.3 s, stable across runs
(42.26 / 42.44 / 42.35, and 42.28 re-measured during this review).
Profile: `perf` at 300 Hz with dwarf call graphs, 12K samples; allocation
behaviour cross-checked with heaptrack and with allocator-substitution A/B
runs. No source file was modified; every experiment was `LD_PRELOAD` or a
reading of the existing binary.*

> **Status, 2026-08-06.** **F1, F3 and F4 landed**; each is cited from the code
> that implements it (`checker/src/main.rs`, `kernel/src/term.rs`'s `subst_pair`,
> `kernel/src/thm.rs`'s `mk_union`), each is pinned by a test, and F1's own A/B
> was redone more carefully in `main.rs` than here. **F2, F5, F6 and F9 did
> not.** F2 is the largest item and is a `kernel/` change, so it benefits `mini/`
> as much as `checker/`; F5 is checker-scoped and is frozen with `checker/`.
> Consequently the profile itself is historical: it was taken against a binary
> with the glibc allocator and without F3/F4, so the 42.3 s baseline and the
> 47%-allocator flat profile no longer describe any binary that exists. Two
> claims below are now **false of the code** and say so where they stand (F3's
> `thm.rs:674`, F4's `thm.rs:569`); `tg.rs:4801` has drifted ~860 lines.
>
> Everything below respects the standing instruction: nothing proposed weakens a
guard, discards a certificate, or trades a correctness property for speed. The
two headline fixes are of the shape the project has already found once — the
run gets faster *because* the code stops doing something it never needed to do.

---

## Where the 42 seconds go

Flat self-time (perf, whole run):

| bucket | % of cycles | symbols |
| --- | ---: | --- |
| glibc allocator | **47.1%** | `_int_malloc` 13.65, `_int_free_chunk` 10.86, `malloc` 8.15, `cfree` 7.34, `malloc_consolidate` 4.57, `__libc_malloc2` 1.37, `unlink_chunk` 1.13 |
| kernel term construction | **12.1%** | `Term::new` 8.43, `Formula::new` 3.69 |
| kernel term teardown | **11.0%** | `Rc<TermData>::drop_slow` 6.36, `drop_glue::<FormulaData>` 2.37, `Rc<FormulaData>::drop_slow` 1.50, `drop_glue::<Thm>` 0.75 |
| kernel term traversal | **11.7%** | `Term::open` 5.97, `Term::close` 3.65, `Formula::close` 1.20, `Formula::open` 0.91 |
| structural equality | **6.9%** | `Term::eq` 5.03, `Formula::eq` 1.86 |
| kernel rules proper | ~2% | `Thm::mp` 1.12, `Thm::ax_s` 0.48, … |
| checker infrastructure | ~3% | nanoda hashmaps, `TcCtx::alloc_expr`/`inst_aux`, hashing |

That is ~89% of all cycles in the kernel's term layer and the allocator
underneath it. The checker's own data structures — the caches keyed on
`ExprPtr`, the indexmaps, the union-find — are noise (<3% combined). Inclusive
(children) numbers put the demand under: `interp` 12.1%, `def_eq` 10.1%,
`gen_ind_build` 10.1%, `certify_reduct` 8.0%, and within those `open`
9.4%+7.7%, `close` 5.7%+5.6%, `subst` 5.8%, `eq_leibniz` 5.4%, `instantiate`
4.5%.

**The headline "a quarter of runtime in the allocator" is an undercount: it is
47%** once `malloc`'s wrapper, `cfree` and `malloc_consolidate` are included.

### Why (the one mechanism behind all of it)

`kernel/src/term.rs` — `Term::close` (line 227), `Term::open` (line 248), and
the `Formula` versions — rebuild **every** `App`/`Formula` node they pass over,
whether or not anything under it changed:

```rust
TermData::App(f, args) => Term::new(TermData::App(*f, args.iter().map(|a| a.open(depth, t)).collect())),
```

Each visited `App` node costs a fresh `Vec`, a fresh `Rc<TermData>`, a hash
re-mix — and, shortly after, a matching free when the input tree's temporaries
drop. `Formula::subst` (line 584) is `close` **then** `open`: two full-tree
rebuilds per substitution. `Thm::eq_leibniz` calls `subst` twice — four
full-tree rebuilds of `φ` per Leibniz instance — and Leibniz sits under every
derived `trans`, `symm`, and congruence step the certifier takes
(`derived::eq_trans`, `congr_arg`, `hyp_eq_trans`, …). `Formula::forall`
(`close`) is under every `gen`/`ax_dist`; `instantiate` (`open`) is under every
`ax_inst`. A sampled malloc stack is typical: 28 recursive `close` frames under
`Formula::forall` under `ax_dist` under `derived::separation`.

The rebuilds have a second, quieter cost: they **destroy sharing**. The
rebuilt copy of an unchanged subtree is a different `Rc` with the same hash, so
every later `==` on it misses the `Rc::ptr_eq` fast path, matches on the cached
hash, and must walk the whole structure to confirm equality. That is the 6.9%
in `Term::eq`/`Formula::eq` — the perf call graph shows it as deep recursive
slice-equality chains, i.e. *confirming that equal things are equal*, node by
node. `Thm::mp`'s premise match and the checker's endpoint checks
(`certify_reduct`, `const_abbrev`'s guard at `tg.rs:4801`) all pay it.

So: one representation decision — rebuild-always instead of rebuild-on-change —
accounts for the allocator's 47%, the construction/teardown 23%, and most of
the equality 7%.

---

## Findings — obvious and fixable now

Ranked by (impact × confidence) / effort.

### F1. Link a modern allocator into `nanoda_bin` — measured −30%, two lines

**Evidence (measured, this review).** Same binary, same corpus, same machine,
back-to-back:

| allocator | wall | peak RSS |
| --- | ---: | ---: |
| glibc 2.42 (baseline) | 42.28 s | 437 MB |
| **tcmalloc** (gperftools 2.17.2, `LD_PRELOAD`) | **29.41 s** | 467 MB |
| jemalloc 5.3.1 (unprefixed build, `LD_PRELOAD`) | 35.10 s | 430 MB |

(A first jemalloc run showed no change because the nixpkgs default build
prefixes its symbols `_rjem_` and never intercepted `malloc` — verify any A/B
by symbol table, as I had to.)

**Mechanism.** The workload is millions of small, short-lived, same-sized
allocations (`Rc<TermData>` boxes and small `Vec<Term>` buffers) freed in
near-LIFO order. This is the exact pattern Poly/ML's minor heap makes nearly
free for Isabelle — allocation is a pointer bump, death is collective — and the
exact pattern glibc malloc handles worst (`malloc_consolidate` alone is 4.6% of
the run; free-bin management is most of the rest). tcmalloc's thread-local
size-class free lists are the closest malloc-shaped approximation of the
Poly/ML cost model.

**Fix.** `#[global_allocator]` (mimalloc or tcmalloc crate) in the *binary*
crate. `kernel/` keeps its zero-dependency policy — the allocator is linked by
the executable, not by the trusted crate, and today's glibc malloc is already
unaudited foreign code on exactly the same footing. No semantic change of any
kind; nothing in the soundness story mentions the allocator.

**Estimate I will defend:** −25–30% wall time today (measured 30.4% with
tcmalloc via preload; a compiled-in mimalloc typically does as well or
better). Interacts with F2: after F2 lands the *absolute* saving shrinks
because there are fewer allocations to serve; do both.

### F2. Make `open`/`close` rebuild only what changes (sharing-preserving substitution)

**Evidence.** The mechanism section above; specifically `open` at 9.4%+7.7%
inclusive, `close` 5.7%+5.6%, `subst` 5.8%, `eq_leibniz` 5.4%, `instantiate`
4.5%, and the construction/teardown/allocator buckets they feed.

**Mechanism of the fix.** This is the standard efficient-LCF discipline, and
its absence is the single real divergence from known-good designs in
`kernel/src/term.rs`. Isabelle's kernel term operations are written in the
`Same` idiom (`Term_Subst`, `Envir.norm_term_same`, `Logic.incr_indexes_same`):
an operation that changes nothing *says so* instead of returning a rebuilt
copy, and unchanged subtrees are returned as the very same pointer. HOL Light's
`vsubst` does the same with an explicit "unchanged → return the original term"
check. The point is not saving the walk (the walk is cheap, 12%) — it is that
the result **shares** every untouched subtree with the input, so (a) no
allocation happens off the changed path, and (b) every later `==` against
related terms hits `Rc::ptr_eq` at the highest unchanged node instead of
walking to the leaves.

Concretely: give `Term`/`Formula` private variants
`close_opt/open_opt : … -> Option<Term>` returning `None` for "unchanged", and
have the `App` case rebuild only if some child returned `Some`:

```rust
fn open_opt(&self, depth: u32, t: &Term) -> Option<Term> {
    match self.data() {
        TermData::Bound(i) => (*i == depth).then(|| t.clone()),
        TermData::Free(_) => None,
        TermData::App(f, args) => {
            let mut new: Option<Vec<Term>> = None;
            for (k, a) in args.iter().enumerate() {
                if let Some(a2) = a.open_opt(depth, t) {
                    new.get_or_insert_with(|| args[..k].to_vec()).push(a2);
                } else if let Some(v) = new.as_mut() { v.push(a.clone()); }
            }
            new.map(|v| Term::new(TermData::App(*f, v)))
        }
    }
}
pub(crate) fn open(&self, depth: u32, t: &Term) -> Term {
    self.open_opt(depth, t).unwrap_or_else(|| self.clone())
}
```

Same shape for `close` and for the five `Formula` cases. ~60 lines total, all
private, all inside the file the adversarial substitution tests already cover.

**Correctness posture.** The function computes the *same value* — the change is
which `Rc` represents it. No guard is weakened; the `deeper` overflow check,
the `locally_closed` assertion in `subst`, and the constructor discipline are
untouched. It is a kernel edit, so it deserves kernel-edit care (and a test
asserting `open`/`close` on a variable-free subtree returns a pointer-equal
subtree would pin the new property), but there is no soundness trade being
made. If anything the sharing *tightens* behaviour: `PartialEq`'s `ptr_eq`
fast path starts doing the job it was written for — today it almost never
fires on rebuilt terms.

**Why this and not hash-consing** — see F6.

**Estimate I will defend:** the fraction of visited nodes actually on a changed
path is small for the dominant call sites — `eq_leibniz`'s `φ` contains the
substituted variable at one or two positions inside equations over large
interpreted terms; `instantiate` replaces `Bound(0)` at a few positions in a
big body; `close` over `forall` bodies likewise. If even half of rebuilt nodes
become shared, the ~70% of cycles that scale with rebuilt-node count
(allocator + new + drop + deep-eq) drops by a third or more: **−20–40% wall
time, multiplicative with F1**. Inferred, not measured — this is the one fix
whose exact win needs the prototype to know. It also cuts peak RSS and, unlike
F1, reduces *work* rather than doing the same work faster.

### F3. `eq_leibniz`: close once, open twice

**Landed.** `Formula::subst_pair` (`kernel/src/term.rs`) is the hoisted form and
`eq_leibniz` uses it, pinned by `kernel/tests/substitution.rs`; `term.rs`'s
header corrects the arithmetic below — four full-tree rebuilds per Leibniz
instance became **three**, not "one of four removed as well as a `locally_closed`
walk". The finding as written, and no longer true of the code:

`kernel/src/thm.rs:674` computes `phi.subst(x, &a)` and `phi.subst(x, &b)`;
each `subst` is `close(x)∘open`. The `close(x, 0)` result is the same both
times. Hoisting it —

```rust
let closed = /* phi.close(x, 0) */;
let phi_a = closed.open(0, &a);
let phi_b = closed.open(0, &b);
```

— removes one of four full-tree walks-with-rebuild per Leibniz instance (and
one of the two `locally_closed` walks if the assertion moves with it; the
assertion itself stays). `subst` is *defined* as close-then-open, so this is
the same computation with a common subexpression named; nothing about the
result or the checks changes. Worth ~2–4% today on its own; still worth having
after F2 (it halves the changed-path work too). Needs a `pub(crate)` `close`
or a small kernel-internal helper — same file, trusted-crate care applies.

### F4. `Thm::mp`'s hypothesis union: merge, don't re-sort

**Landed.** `Thm::mk_union` is a linear merge of two sorted lists with
`extend_from_slice` tails and one `dedup`, pinned by `kernel/tests/hypotheses.rs`
against the re-sort it replaced. The finding as written, and no longer true of
the code:

`thm.rs:569` builds `Γ ∪ Δ` as `chain().cloned().collect()` then
`mk_hyps` → `sort_unstable` + `dedup`. Both inputs are already canonical
(sorted, dedup'd — the struct invariant), so this is an
`O((m+n) log(m+n))` comparison sort where a linear sorted merge does the same
job, *by construction* preserving the invariant instead of re-establishing it.
`implies_intr` similarly re-sorts a filtered — hence still sorted — vector.

**Today this costs ~nothing** — every theorem the checker builds has `Γ = ∅`
(the census verified `assume` has no shipped caller), so the vectors are empty.
The reason to fix it *now* is the reason the hypothesis machinery exists at
all: `THREADING-CENSUS.md` §2 plans to move binder-context evidence into
kernel `Γ`, at which point `mp` runs on non-empty sets on the hot path, and the
constant-cost claim the sequent design was adopted for ("one merge of two
sorted lists" — `thm.rs` module doc) should be literally true in the code.
This is Isabelle's actual implementation choice: `Thm` hypotheses are ordered
lists combined with ord-list `union`, not re-sorted per rule. ~15 lines,
inside the 700-line CI cap (662 today). The `Vec<Formula>` itself is the right
structure — see Q3 below.

---

## Findings — architectural, needs a decision

### F5. Canonical constant interpretation (the project's own 21 seconds)

The run doubled from 21.0 s to 41.9 s on 2026-08-01 when the general inductive
translation was wired, and `MEASUREMENTS.md` already carries the exact
diagnosis: the per-thread `GenInd` cache is guarded by re-walking the
declaration, and the guard misses **3783 of 3803** times on `init-prelude`
because the *constant* interpretation is not canonical across backends
(`shared symbols declined: body not canonical` = 7922). So `Inductive::build`
runs per (declaration, inductive) pair instead of per inductive — "that is the
21 extra seconds", and this profile corroborates it: `gen_ind_build` 10.1%
inclusive, `ind_const` 8.8%, plus the `interp` share underneath.

The same non-canonicality taxes every ordinary constant: `interp` of a
`Const` with a value **re-interprets the whole monomorphised body first** and
only then consults `Shared::const_syms`, because the hit must be validated
against the body just built (`const_abbrev`, `tg.rs:4801`) — and that
validation is itself a full-tree `Formula::eq` (part of the 6.9% equality
bucket; a *hit* still pays interp + deep compare). The known causes are listed
in `MEASUREMENTS.md` ("Why the store answers 49 uses and not more"):
`ind_syms` was moved, but `rec_nests`, `let` abbreviations, `level_reps` and
friends are still per-backend, and `idx_term` was one such cause already found
and fixed.

**This is the largest single item in the run and it is already on the
project's books.** The fix direction is the one the code comments name: move
the remaining identity-bearing tables into `Shared` until interpretation is a
function of `(name, levels)` alone. The guards then *hit* instead of being
deleted — the honest structure stays, the rebuilds go. Expected effect: most
of the 21 s regression back, plus a large cut of `interp`'s 12% — call it
−30–50% of today's wall time, with the caveat that it is a design effort
(brand/identity questions per table), not an afternoon. Nothing here trades
soundness: as the measurements note, "a stale entry costs a rebuild, never a
wrong theorem" — the point is to stop paying for rebuilds that a canonical
interpretation makes unnecessary. F2 independently makes the residual
validation compares cheap (shared subtrees → `ptr_eq`).

### F6. Hash-consing / a term table: **not yet, and maybe never** (Q2)

The case for: a global intern table would make equality `ptr_eq`, dedupe
memory, and make the checker's `Term`-keyed maps O(1)-exact.

The case against, which I find stronger:

* **Isabelle does not hash-cons terms**, and its reasons transfer. Sharing in
  Isabelle comes from operations that *preserve* it (the `Same` idiom — F2
  here), from `aconv`'s pointer fast path, and from Poly/ML's GC-time
  structure-sharing pass. A global table puts a probe on every construction —
  and construction is this kernel's hottest operation (`Term::new` 8.4% before
  any table) — to optimise equality, which is a quarter as hot and collapses
  anyway once F2 restores sharing.
* **Rust makes the table expensive in kind, not just degree**: no GC means
  weak references and eviction-on-drop (or a leak), a `'static` or
  thread-local table with brand questions, and interaction with the kernel's
  zero-dependency policy.
* **The cached hash is already doing its job.** Inequality is decided in one
  `u64` compare (`PartialEq` short-circuits, `Ord` compares hash first); the
  hash is computed once per node, incrementally from child hashes. The 6.9%
  equality cost is *equal* terms being confirmed structurally — a sharing
  problem (F2), not a hashing problem. Do not be tempted to "trust the hash"
  on equality: a collision must lose, not win, and nothing proposed here
  touches that.

**Decision point:** revisit after F1+F2 with a fresh profile. If deep
equality-confirmation is still >3%, intern *at the cache boundaries only*
(keys of the `Shared` maps), not in `Term::new`.

### F7. Take the kernel `Γ` the checker already paid for (Q3-adjacent)

The kernel grew sequents precisely to replace the formula-level antecedent
discipline (`⊢ conj(hs) → φ`, the measured `13u² + 73u − 134` kernel calls per
merge), yet the checker still runs the old discipline: the census's own words
are that constant-cost hypotheses are "available and not yet taken", with
`guard_and_generalise_at` re-implementing `implies_intr` + `gen` above the
kernel. In this profile the formula-level layer is visible but modest:
`hyp_eq_trans` 2.71%, `hyp_mp` 1.65%, `conj`/`cond` machinery ~1% — call it
**~5–6% today**, growing with every construction that carries assumptions
(each `hyp_eq_trans` buys a Leibniz instance plus two `ax_s` instances over
formulas that drag `H` along).

This is a design item, not a quick fix, because the census already flags the
two things that must move with it: the `ci/check-boundary.sh` ban on
`Thm::assume` outside `kernel/`, and the cache-key obligation (option 1 —
refuse hypothetical entries — is implemented and must stay; option 2 would
change what `impl Ord for Formula` is trusted for, and whoever takes it owes
that argument). Do F4's merge first so the promised constant cost is real.

### F8. Term representation micro-structure (later)

Each `App` node is two allocations (`Rc<TermData>` box + `Vec<Term>` buffer,
with an unused capacity field). After F1/F2 land, if construction is still
hot: `Box<[Term]>` shaves the capacity word; small-arity inlining or a
`Rc<[Term]>`-style DST shaves the second allocation. None of this is worth
kernel churn before the two big fixes are in, and an arena/GC redesign is
exactly the kind of ground-shifting move the project's standing instruction
counsels against right now.

### F9. Parallel checking exists and is off

`num_threads` defaults to 0; the run is serial on a 96-core machine. Caveats
before reaching for it: the cost distribution is heavy-tailed (the top-10
declarations were 58% of a 9.4 s run; `Lean.ParserDescr.noConfusion` alone 42%),
so Amdahl bites early; `Shared` is per-thread, so threads re-derive skeleton
graphs and worsen F5; and glibc malloc under threads adds arena contention
(F1's allocator swap then matters even more). Sequencing: F5 first, then
threads become nearly-linear on the residue.

---

## The five questions, answered directly

**1. Why is a quarter (actually 47%) of time in the allocator, and what
allocates?** The kernel's `open`/`close`/`subst` rebuild every node they visit
(fresh `Vec` + fresh `Rc` per `App`/`Formula` node) and drop the inputs'
temporaries immediately after; `eq_leibniz` does four full-tree rebuilds per
instance and sits under every derived trans/symm/congruence step;
`interp`/`gen_ind` re-interpret constant bodies and inductive packages that a
canonical interpretation would share (F5). Yes — the representation is forcing
rebuilds where sharing would do (F2), and the biggest single client of those
rebuilds is re-interpretation the project has already diagnosed (F5).
Heaptrack totals: see the appendix figures below.

**2. Would hash-consing pay?** Not as the next move. Isabelle's reasons for
not hash-consing apply with extra force in Rust (F6). The cached hash *is*
short-circuiting inequality as intended; what it cannot do is confirm equality
of pointer-distinct equal terms cheaply, and the cure for that is to stop
manufacturing pointer-distinct equal terms (F2), not to tax every `Term::new`
with a table probe.

**3. Is `Vec<Formula>` the right structure for `Thm::hyps`?** Yes. It *is*
sorted and deduplicated (the canonical-order invariant in `thm.rs`), which is
Isabelle's representation too — ordered list, not a set type. The one
deviation from Isabelle's cost model is that `mp` re-sorts the concatenation
instead of merging two sorted lists (F4); fix that before the checker starts
producing non-empty `Γ`, and the design's constant-cost claim holds as stated.
At observed set sizes (single digits) any tree/hash set would be strictly
worse. The hash-first `Ord` is the right kind of order for this job — cheap,
total, consistent with `==` — and nothing here proposes trusting it for more
than canonicality.

**4. Do the checker's caches show the census's evidence-rebuilding in the
profile?** Barely, today. `has_type_a` + `has_type_uncached` are ~1.3%
inclusive each; the search family the census wants deleted is real
architecture debt but is not where the 42 seconds are. The caches that *do*
show up are the ones whose **hits are expensive to validate**: `const_syms`
(re-interpret body + full-tree equality per mention, F5) and the `GenInd`
guard (3783 misses → full rebuilds, F5). The lesson of the census's own
success story (the 36%-that-wasn't) repeats here: the cost is never the
storing, it is the searching/rebuilding around a store that cannot yet be
trusted to hit.

**5. Anything else obvious?** The needless clones/reallocation are exactly the
rebuilds of F2/F3; `Formula`'s `Ord` is not hot (the `derived::hyp::order`
thread-local registry ranks are inside the ~5% of F7 and disappear with it);
no quadratic merge is visible at today's `Γ = ∅`; `Rc` churn *is* the story,
and the fixes are F1/F2. I found no hot spot attributable to the
overflow-checks profile setting or to the `locally_closed` assertion in
`subst` — the latter was measured by the project at noise level and this
profile agrees (`locally_closed` ~0.9% self, mostly under `forall`); leave
both exactly as they are.

---

## Measured vs. inferred vs. unsettled

**Measured here:** the flat and inclusive profile percentages (perf, 12K
samples); the allocator A/B (glibc 42.28 s / tcmalloc 29.41 s / jemalloc
35.10 s, single runs each, baseline re-confirmed within the historical
42.26–42.44 band); the placebo result that symbol-prefixed jemalloc changes
nothing (a useful control); heaptrack allocation totals (appendix).

**Measured by the project, relied on here:** the 21.0→41.9 s regression and
its 3783/3803 guard-miss diagnosis; the 7922 non-canonical constant declines;
the `13u²+73u−134` merge cost; the 88% def-eq cache hit rate; the heavy-tail
declaration distribution.

**Inferred:** F2's win range (mechanism is certain from the code and profile;
the changed-path fraction is not instrumentable without editing source, which
this review was barred from); F5's win range (bounded below by the documented
21 s, discounted for overlap with F1/F2).

**Not settled:** how F1 and F2 compose quantitatively (the allocator win
shrinks as allocation count falls — the honest expectation for F1+F2+F3
together is 42 s → high teens, and I would not promise better than that
without the prototype); whether after F2 the residual deep-equality cost
justifies boundary interning (F6's decision point); mathlib-scale behaviour
(everything above is init-prelude).

## What was deliberately not proposed

Per the standing instruction, and because each of these buys speed with
something that is not speed's to spend: skipping the structural confirm when
hashes match (a collision must lose); demoting the `subst`/`apply`/`deeper`
assertions (measured ≈ free); caching `FV(Γ)` in `Thm` (already rejected in
`gen_checked`'s docs, for reasons this profile does not disturb — the scan is
not on any hot path); dropping or key-widening the equality-cache guards
(`is_unconditional` stays; F5 makes its cost irrelevant by making hits
genuine); and any arena/unsafe rewrite of the term representation while the
ground is still moving.

---

## Appendix: heaptrack allocation totals

Collected with `heaptrack` on the same binary and corpus (21× tracing
overhead; numbers are counts, which tracing does not distort):

| | |
| --- | ---: |
| calls to allocation functions | **1,700,036,832** |
| … per second of native runtime (÷ 42.3 s) | ~40 million/s |
| … per declaration (÷ 2059) | ~826,000 |
| peak heap | 368.9 MB |
| total leaked | 634 KB (one-off setup; nothing cumulative) |

1.7 billion allocations against a 369 MB peak is the profile of a program
that allocates almost everything only to free it moments later: the mean
lifetime of an allocation is *milliseconds*. That ratio — turnover ≈ 4600× the
peak — is the quantitative form of the F2 diagnosis (rebuild-and-discard), and
it is why the allocator swap (F1) is worth 30% before a single line of logic
changes. For calibration, Isabelle on Poly/ML pays roughly a pointer bump and
an amortised minor-GC sweep for the same pattern; glibc malloc pays a
free-list transaction per node, twice.
