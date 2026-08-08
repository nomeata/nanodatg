# nanodatg

A proof-carrying Lean checker: a fork of
[`nanoda_lib`](https://github.com/ammkrn/nanoda_lib) that turns Lean's export
format into derivations in a small LCF-style kernel for **Tarski–Grothendieck
set theory**, rather than into a trusted `true`/`false` verdict.

Today an external Lean checker is trusted: you believe its ~10k lines of
inference and definitional-equality code. Here the type checker itself is
**untrusted**, and the only trusted component is `kernel/`.

## The threat model determines everything

The single threat is: **a bug in Lean's kernel lets someone derive `False`.**

We are *not* showing that translated theorems mean what the Lean originals mean.
Only this: if a development translates and the kernel accepts every step, the
development proves no contradiction. That holds as long as the translation of
`False` is genuinely refutable in the target.

So a translation bug is **not** a soundness bug — it yields a rejection, never a
false theorem. The translator may be liberal and clever. The kernel may not.

## Layout

| path | trusted? | what |
| --- | --- | --- |
| `kernel/` | **yes — the entire TCB** | FOL-with-∈ kernel for TG set theory: `Thm`, `Formula`, `Term`, the rules, the axioms |
| `derived/` | no | derived inference rules and conservative constructions |
| | | *Nothing Lean-syntax or Lean-`Expr` specific goes here.* Any construction useful **to model type theory** does. The test is vocabulary, not motivation: a lemma stated in `Term`s and `Formula`s belongs in `derived/` even when Lean's `Π` is the reason it exists; anything mentioning `ExprPtr`, `NamePtr` or Lean's `Expr` variants stays in `checker/`. |
| `checker/` | no | fork of nanoda_lib: parser, `Expr`, inference, defeq, reduction, and the `Certifier` proof-backend boundary |
| `mini/` | no | a Rust port of [`lean-mini-kernel`](https://github.com/nomeata/lean-mini-kernel), where the evidence-threading design is built with no caches, no hash-consing and no arena to confound it. Reuses `checker/`'s parser and level pre-pass and changes nothing in it. See `MINI-DESIGN.md`. |
| `ci/` | — | boundary enforcement, and a self-test for it |
| `scripts/` | — | corpus harness |

`checker/` is imported with full upstream history, so the instrumentation diff
is exactly:

```sh
git diff nanoda-upstream/master -- checker/
```

## Getting started

```sh
direnv allow          # or: nix develop
./ci/check.sh         # everything CI runs
```

The corpus tests want the Lean Kernel Arena suite, which is gitignored for size:

```sh
mkdir -p vendor/arena-tests
curl -sSL https://arena.lean-lang.org/lean-arena-tests.tar.gz \
  | tar xz -C vendor/arena-tests
./scripts/arena.sh    # 102 good + 55 bad export files
```

`ci/check.sh` runs this too, as `ci/check-arena.sh`, and **SKIPs loudly** rather
than passing when the corpus is not there. `good/` must be accepted. `bad/` is a
**ratchet**, not a blanket must-reject: a `bad/` file we accept fails unless it
is listed in `scripts/arena-accept.txt` with a reason, and an entry there that
we have started rejecting again fails as stale. The reasoning — the certificate
is the guarantee, not acceptance fidelity — is in `scripts/arena.sh`'s header.
The list is empty today.

Without it, `cargo test` still runs the committed fixtures in
`checker/tests/fixtures/{good,bad}`, so there is always negative coverage.

## Where the project is

**The fork changes the shape of the roadmap.** Because `checker/` inherits
nanoda, the untrusted side — inductives, recursors, `Prop`, proof irrelevance,
quotients, mutual and nested inductives, literals — is *already implemented and
passing*. The remaining frontier is the interpretation and the kernel.

> **Read this first: `mini/` is the frontier, not `checker/`.** This section and
> the two that follow it were last measured on 2026-08-01, hours after `mini/`
> was created and without accounting for it. Since then `checker/src` has taken
> **one** commit (docs and tests in `scope.rs`) against **~130** to `mini/src`;
> `mini/` is now larger than `checker/` and is where every current corpus number
> comes from. Today's ledger — `accept 89 / decline 2 / reject 0`,
> `constEv 218/218`, `unsealed 0`, `gapped 0` over the 91 tutorial exports — is
> `mini`'s, and is carried by `MEASUREMENTS.md` and `MINI-HANDOFF.md`. The
> figures below are `checker`'s and are still true of `checker`; the roadmap
> below is `checker`'s and has been overtaken on `mini`, item by item, as each
> item now says. `MINI-DESIGN.md` §0 is the statement of what `mini` is for.

### The trusted base

`kernel/` is **676 non-comment lines**, no `unsafe`, no dependencies,
CI-enforced against a 700-line budget. Eight set axioms — extensionality,
pairing, union, power, regularity, replacement (a scheme), Tarski's Axiom A, and
choice — plus the Łukasiewicz propositional axioms, instantiation and
distribution, the rules (modus ponens, generalisation, reflexivity, Leibniz),
the two structural rules `assume` and `implies_intr` that came with the sequent
judgement, and conservative definitional extension. `kernel/README.md`'s
itemisation is the authoritative one.

What it exports is the type theory and nothing else. The `Certifier`
proof-backend trait and its null implementation used to live here; they moved to
`checker/src/certify.rs` (−58 lines), because neither constructs a `Thm` and so
neither can affect soundness, and the boundary is stated in the checker's own
`ExprPtr`/`TcCtx` rather than in associated types with one inhabitant each.

*Singleton*, *ordered pair* and the *empty set* are derived rather than assumed.
The empty set was an axiom until 2026-07-31, on the grounds that deriving it
from Tarski needed the recursion theorem and a transitive closure; adding the
transitivity clause to Tarski's Axiom A removed that obstacle, and Regularity
applied to a universe now yields it in four steps.

**The selection rule is "assert what we have not yet derived"** — not "assume
only what cannot be constructed", which is what this section used to imply and
which the list does not obey. Four of the eight are redundant *in principle*:
Tarski's Axiom A plus Replacement yields **pairing, union and power set** (TG
folklore — Mizar assumes union and derives power), and Tarski's Axiom A alone
implies **choice**, through well-ordering by the universe hierarchy. None of
those derivations exists in `derived/`, so all four are asserted. The four that
are genuinely needed are extensionality, regularity, replacement and Tarski's
Axiom A.

That is defensible because the property wanted of this TCB is not minimality but
truth in the intended model: every one of the eight holds in `V_κ` for `κ`
inaccessible, so each redundant assertion leaves theory and consistency strength
untouched and costs one more formula that has to be read against a reference
statement. Choice is stated in the standard ZFC form (Jech §1, Kunen I.12.1),
guarded at non-empty members; note that the thesis's unguarded phrasing at §6.2
is literally unsatisfiable, since `∅` is a member of every universe.
`kernel/README.md` itemises all eight. **Infinity is not among them**: it was
briefly an open question — assert it by the trade already accepted for choice,
or derive it — and the answer was to derive it. `derived::infinity` proves the
Jech §1 / Kunen I.2 statement `∃I. (0 ∈ I ∧ ∀n ∈ I. succ(n) ∈ I)`, and also its
**primitive form** with `0` and `succ` expanded, so that the claim rests on no
definitional extension at all.

**Five soundness bugs have been found and fixed in the trusted base, none of
them by the test suite.** All were found by reading with intent to break — see
`DECISIONS.md`. That practice is now standing policy for any change to
`kernel/`, *including fixes*: bug #5 existed only because of the fix for #4. A
full adversarial audit of every axiom and rule against the thesis found no
sixth, but did find two *false statements* in the trusted crate's own
documentation — which is the same failure mode one level up, and is why stale
prose is treated here as a defect rather than as untidiness.

Separately, three **claim-matching** bugs have been found in the untrusted
checker, all by chasing certificates rather than by tests: `def_eq` skipping the
composition of its whnf legs (so a step where one side reduces to the other got
*reflexivity* as its certificate), `derive_beta` counting contractions on the
substituted head rather than the syntactic lambda nesting, and a memoised reduct
with no certificate to recall. None could produce a false theorem — the kernel
cannot — but each let the checker report a step as derived that it had not
derived. Each was caught by a guard rather than by a test, which is the argument
for the guards.

### What is derived, not assumed

`derived/` (101,600 lines, untrusted, 873 tests) builds on the kernel: a
propositional and quantifier toolkit, "reasoning under a fixed hypothesis" (the
nearest a Hilbert system gets to a deduction theorem), Separation from
Replacement, unordered pairs, singletons and Kuratowski ordered pairs with
injectivity, union, power set, Cartesian products, function spaces, the
least-universe operator `U(x)`, lambda graphs, application, **beta reduction**,
graph and image extensionality, dependent products, and the bridge showing a
constant-fibre dependent product *is* the function space.

### Coverage

With `--features tg`, **69 of 91** tutorial exports check with *every*
definitional-equality step discharged by a real kernel derivation — zero gaps —
and 78 have zero *escapes*. Acceptance across the whole arena corpus is
unchanged with the backend active (152 matched, 0 mismatched), so the backend
adds evidence without changing verdicts.

Note `zero-gap ⊆ zero-escape`: an escape row is itself a gap row, so the two
counts move independently. They last read 68/79, and the pair drifted because
one file reached zero gaps while a *different* file went from zero escapes to
some — the gaps-into-escapes trade that hoisting a guarded family makes, which
`checker/tests/tg_tutorial.rs` documents. The figures above were measured 104
commits after the ones they replace; re-measure before quoting them.

**All 27 inductive-free exports check with zero gaps and zero escapes**, and
`Bool`, `N` and `List` are interpreted as W-types with their recursors' ι rules
discharged — `073_boolRecEqns` is at zero and zero.

That fragment count went 27 → 25 → 27. The two that left it and came back — the
Church numerals `028_peano2` and `029_peano3` — are the clearest statement of
what the interpretation had to learn. Carneiro's §6.2 gives `∀` and `Π` two
different interpretations:

```text
⟦∀x : α. β⟧ = {•} ∩ ⋂_{x∈⟦α⟧} ⟦β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — β a Prop
⟦Π x : α. β⟧ = ∏_{x∈⟦α⟧} ⟦β⟧                              — β a Type
```

and the checker used to build the second for every `Π`. It now builds each where
it belongs, which is what makes `⟦∀…⟧ ∈ ⟦Prop⟧` provable at all: 446 of
`init-prelude`'s 449 `Prop`-valued `Π`s and 136 of the tutorials' 137 now carry a
real membership theorem, where none did before.

It also exposed a **third case**. `Π A B : Sort (imax u v)` with `v` a universe
*parameter* does not simplify — it is `0` when the parameter is instantiated at
`0` and `max(u,v)` otherwise — so at a level-polymorphic declaration's own
parameters the `Π` is *neither* clause, and the two clauses name different sets.
The checker applied neither and reported the gap: **2366 of `init-prelude`'s
5718 `Π` typing sites (41%) and 336 of the tutorials' 660 (51%)** were in that
case, and the Church numerals were exactly that —
`two.{u} : Π (α : Sort u). (α → α) → α → α` is a proposition when `u := 0`.

That was never a gap a lemma could close. It bounded what any interpretation
performed *once, at a declaration's own parameters* could reach, and the way
past it was to stop doing that. **`checker/src/instantiations.rs` is the
level-instantiation pre-pass**: before any checking starts, a worklist fixpoint
over the export file computes every `(declaration, ground universe levels)` pair
the run will need — 2652 pairs for `init-prelude`'s 2059 declarations, closing
in 13 rounds — and each declaration is then checked once per instantiation, with
the backend told which σ it is under. At a ground σ every `imax` simplifies to a
numeral and exactly one clause applies. The third case collapses: **2366 → 12**
undetermined `Π` typing sites on `init-prelude`, **336 → 36** on the tutorials.
The cost is 1.14× wall-clock and 1.16× kernel derivations.

The pre-pass's prediction is *syntactic*, so it could in principle miss an
instantiation the checker mints itself — literal expansion, or the temporary
declarations created for nested inductives. That is not argued, it is counted:
the backend audits every constant instantiation it interprets against the
schedule and reports the misses as their own row of the ledger. The row is
**zero** on the tutorials and on `init-prelude`, and a test pins it there.

`MEASUREMENTS.md` carries the gap ledger. The remaining escapes fall into
exactly three categories, all measured: constructor memberships for inductives
not yet interpreted (the largest), the typing `⟦T⟧ ∈ ⟦Sort u⟧` — now *derived*
for `N`, `Bool`, `Unit` and `Empty` at `⟦Type 0⟧` via `derived::cumul`'s
cumulative hierarchy, and still out of reach at a universe *parameter*, where
`⟦Sort u⟧` is an opaque symbol — and the typings of *ambient context locals* —
which, on Carneiro's Theorem 6.7, may not be gaps at all, since a Lean judgment
is context-relative and the bare equation compared against is strictly stronger.
That last one is an open question, not a fix.

### Remaining work, in order

1. **Interpret the remaining inductives.** ***Done on `mini`***, and well past
   this item: the general translation is `derived/src/inductive/` with
   `mini/src/zoneb.rs` above it, and no export on the tutorial corpus stops.
   The item as written — "the cheap next step is a constructor with two or more
   plain recursive arguments, which changes only the fibre" — is
   `derived/tests/genrec.rs` and `mini/tests/fixtures/prop_recursive_interleaved.lean`.
   `checker/src/tg.rs` still runs the hand-written `Bool`/`N`/`List` recognisers
   and has not taken the general path for them.

   Its *negative* content is still exactly right and is why it is kept.
   `116_rtreeRecReduction` is not the `m ≥ 2` test, which this list named until
   2026-08-01: `RTree.node` has exactly **one** field, `children : (Bool →
   RTree)` — the export marks `RTree` `isReflexive: true` — so it is a
   *function-typed* recursive argument, a different and harder shape (the reduct
   puts a lambda under the minor premise, and it needs a `Σ(z::γ)` fibre). The
   tutorial corpus has **no** plain `m ≥ 2` non-indexed constructor at all: the
   only `m ≥ 2` constructors in it are `RBTree.red` and `RBTree.black`
   (`042`/`068`/`077`), and `RBTree` is an indexed family (`numIndices: 2`),
   which is item 2 below. The witnesses for the plain shape are in
   `init-prelude`: `Lean.ParserDescr.binary`, `sepBy` and `sepBy1`. *(The
   `Σ(z::γ)` fibre that "does not exist" now does —
   `CtorSpec::with_rec_doms` — and `115`–`118` certify on `mini`.)*
2. **Indexed families** — §5.2's `spec` judgment and its `good` predicate.
   ***Done on `mini`***: `derived/src/inductive/family/` and
   `mini/src/{ctor_ix,class_s_ix,class_p_ix,rec_ix_dep,rec_ix_prop,rec_s_ix,minor_ix,iota_ix_dep}.rs`;
   `042`/`068`/`077` all certify. Not taken in `checker/src/tg.rs`, where
   `gen_scope` still returns `Decline::Indices`. The reasoning below is why the
   route was available at all, and is kept for that.
   This item used to say they need `acc` and §5.3's subsingleton elimination
   first, because `good`'s base case wants `Eq`'s *elimination*. That chain is
   **void**: `good`'s base case is kernel equality inside a Separation, and its
   elimination is the primitive `eq_leibniz`, which is what `⟦rec₌ e b h⟧ = ⟦e⟧`
   (thesis.txt:2124) says. §5.2-indexed depends on neither §5.3 nor `acc`.
   `good` is the existing `wrec` at target `𝒫(Idx)`, the carrier is one further
   Separation, and the recursor is the *erased* declaration's `GenRecursor` —
   indices are dead binders in the nest. See `INDEXED-DESIGN.md`.
3. **A universe closed under W-types** (thesis §6.2.1), which is what the `Sort`
   obstruction reduces to at a universe *parameter*. At level 0 it is settled:
   `derived::cumul` catches the W-type inside a cumulative hierarchy over a
   finite seed and lands it in `U(ω)`, which is `⟦Type 0⟧`. *(This item added
   that "one route to the general statement was checked and dies on `⋃`-closure;
   the thesis reaches it by a rank/cofinality argument this project has so far
   avoided". **A third route was found and taken**: `derived/src/wpath/` bounds
   `W(A,B,u)` by its labelled path codes at an arbitrary fibre family, with no
   ordinals and no condition on the fibres, and hands that to
   `cantor::image_in_universe`. See DECISIONS.md's 2026-08-05 "Infinitary
   branching is wired" and SCOPING.md §14. What remains at a universe
   *parameter* is the `⟦Sort u⟧`-is-opaque half, not the W-type half.)*
4. Decide whether a top-level certificate asserts a **context-relative** claim,
   and if so make the ambient context visible so the entitlement can be checked
   rather than assumed. *(The machinery exists on `mini` and is unused on
   `checker`: `mini/src/scope.rs`'s `Scopes::open` acquires `w ∈ dom` as a real
   kernel hypothesis and `Closed::discharge` generalises it away, with
   `checker/src/sealed.rs` the funnel that refuses a stored theorem whose
   `hyps()` is non-empty. The *decision* this item asks for has still not been
   recorded anywhere.)*
5. Primitive `ℕ` with native bignum arithmetic — deliberately shelved; the
   inductive-free fragment does not need it.

## The honest progress metric

`cargo build --release --features stepcount` makes the checker report where every
definitional-equality conclusion came from — a real backend rule, or an `admit`
naming a hole still to be closed:

```
definitional-equality certificate provenance
  certified (real rule)           70830
  admit whnf                       2681
  admit lazy_delta                 1126
  admit eq_cache                    687
  ...
  TOTAL admitted                   4520
```

**This number must reach zero before the backend can be trusted.** Admits are an
enum, not scattered strings, so a new hole cannot be introduced without naming
it. See `MEASUREMENTS.md` for the full data and `DECISIONS.md` for the reasoning.

*The block above is the 2026-07-30 reading and is kept only to show the report's
shape; do not read the rows as current.* Two of its four labels no longer mean
what they meant: there is no `LazyDelta` admit any more (`lazy_delta_step`
composes its own certificate), `Admit::Whnf` is pinned at **zero** corpus-wide
and a non-zero count there is a bug report (`checker/src/certify.rs`), and
`eq_cache`'s 687 became 272 on `init-prelude`. `Admit::Binder` and `Admit::App`
are annotated *"No longer raised"* in the enum. `Admit::ALL` in
`checker/src/certify.rs` is the authoritative list, and `MEASUREMENTS.md` has
the current numbers. On `mini` this metric has a different and stricter form —
`constEv`/`typeEv`/`unsealed`/`gapped`, in the default verdict and in the exit
code — recorded in `DECISIONS.md` 2026-08-04 and `MINI-DESIGN.md` §0.5.

## Licence

`checker/` derives from nanoda_lib, Apache-2.0; see `checker/LICENSE` and
`NOTICE`.
