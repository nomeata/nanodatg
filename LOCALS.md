# Locals, canonical free variables, and the cache obligation

**Status: design note. No code was written for it. `checker/` and `kernel/` were
read only.**

Written against the in-flight change that moves hypotheses into the kernel
judgement (`Thm { hyps, concl }`, `kernel/src/thm.rs`), and against the
obligation that change creates, recorded in `kernel/src/thm.rs` under *THE CACHE
OBLIGATION* and in `QUESTIONS.md` §1.

The proposal worked through here is the project owner's:

> The certificates are globally sound if they are used in the right context.
> Nanoda has an implicit context (de Bruijn level with type annotations). If the
> variable name in the target is derived from the de Bruijn-level-plus-type, then
> the cached certificates should be valid and compatible. This may require either
> the kernel client having control over the fvars, or else the checker to
> maintain a map from nanoda fvar (level with type) to kernel fvar.

## Verdict, up front

**The mechanism is right about what goes wrong and wrong about what fixes it.**

1. Making `⟦local⟧` a function of `(de Bruijn level, type)` rather than of
   allocation order is a **real and independently justified improvement**. Today
   the key is the level *alone*, which conflates two genuinely different Lean
   locals into one kernel free variable. That is a latent defect in the
   interpretation, present before hypotheses and unrelated to them.

2. It does **not** make hypothesis-carrying certificates reusable, and it does
   not make a cache hit safe. A de Bruijn level is not a name; it is a *position
   in a stack*. Two contexts can agree at level 3 and disagree at level 1, and a
   certificate whose hypotheses mention both is compatible with neither. "The
   de Bruijn level already encodes which locals are in scope" is the step that
   does not hold: the level encodes *how many* binders are open, not *which*.

3. There is nevertheless a sound scheme with an **O(1)** retrieval check, and it
   is close to the owner's shape. It is not the variable key; it is a **stamp on
   the binder prefix** — the open-binder stack interned the way `alloc_expr`
   interns an `Expr`, with each cached certificate recording the depth its
   hypotheses reach and the prefix id at that depth. Details in §5.

4. Whatever is done about (3), **the safe fix must land first and separately**,
   because it is three lines and the migration is landing now: `is_unconditional`
   must stop meaning `is_proved()` and start meaning `hyps().is_empty()` (§6).

5. **The kernel note undercounts the problem.** It names one cache. There are
   **four** places in `checker/` that store a `Thm` and hand it back later, and
   three of them can hold hypotheses after the migration. Two of the three have
   never been examined (§7). One of them, `TcCache::infer_cache_*`, carries a
   written justification for storing conditional certificates whose premise
   **stops being true** the moment definitional-equality certificates can carry
   hypotheses.

Line numbers are deliberately omitted throughout: `checker/src/tg.rs` and
`kernel/src/thm.rs` were both being edited while this was written. Everything is
cited by function or field name.

---

## 1. What nanoda's local representation actually is

`checker/src/expr.rs`:

```
Local { hash, binder_name, binder_style, binder_type, id: FVarId }
enum FVarId { DbjLevel(u16), Unique(u32) }
```

Four facts, all load-bearing.

**A local carries a level, not an index, and it does carry its type.** So the
raw material the proposal asks for is present. But the identity of the `Expr`
node is the whole tuple — `hash` is computed over `binder_name`, `binder_style`,
`binder_type` and `id` — so within a `TcCtx` the hash-consed `ExprPtr` of a local
is finer than `(level, type)`: it distinguishes `(x : A)` from `(y : A)` at the
same level by binder *name*.

**There are two kinds of local and only one of them is a level.** `mk_unique`
(`checker/src/util.rs`) draws from a monotonic `unique_counter` and is used by
`inductive.rs` (heavily), `quot.rs`, `pretty_printer.rs`, and by `tg.rs` itself
when it opens a lambda or `Π` binder to interpret the body. `mk_dbj_level` draws
from `dbj_level_counter` and is used by `tc.rs` alone — `infer_lambda`,
`infer_pi`, `strong_reduce`, `def_eq_binder_aux`. So the "implicit context" the
proposal appeals to governs the *definitional-equality and inference* paths and
nothing else. `Unique` ids are never reused and pose no identification question;
they also can never be discharged by a binder, which matters in §5.

**`dbj_level_counter` is a stack discipline, and it is shared between two
independent binder stacks.** `mk_dbj_level` takes the current counter and
increments; `replace_dbj_level` asserts `level + 1 == counter` and decrements.
`def_eq_binder_aux` bypasses `replace_dbj_level` and does
`dbj_level_counter -= locals.len()` directly, twice, but the discipline is the
same. What the counter does *not* respect is a single lexical origin: `infer`
runs inside `def_eq` (through `infer_then_whnf` and friends), so at any moment
the open locals are an interleaving of binders opened by inference and binders
opened by the equality check. The consequence:

> **A de Bruijn level is a runtime open-binder depth, not a syntactic position.**
> The same level denotes different binders at different moments *within one
> declaration*, and which binder it denotes depends on the checker's control flow,
> not on the term.

At any single moment the live locals are exactly levels `0 .. dbj_level_counter-1`,
and they are pairwise distinct. That is the property that saves the scheme from
being outright broken (§3), and it is the only one.

**Is `(level, type)` enough to identify a local within a declaration? No — it is
enough to identify it *among the locals live at one moment*, which is a much
weaker statement.** Across declarations it identifies nothing at all: `TcCtx`,
and with it every `ExprPtr`, is created fresh per declaration
(`ExportFile::with_tc_and_declar`), so level 0 of one declaration and level 0 of
the next have no relation beyond both being "the outermost open binder".

## 2. How `⟦local⟧` is minted today

`TgBackend::interp`, `Expr::Local` arm:

```
key = match id { DbjLevel(n) => n as u64, Unique(n) => (n as u64) | (1 << 32) }
v   = self.locals.get(&key)  or  { let v = env.fresh_var(); locals.insert(key, v); v }
Term::var(v)
```

with `locals: HashMap<u64, FreeVar>` a **per-backend** field, and `TgBackend`
created per declaration by `TypeChecker::new`. The same key computation is
duplicated in the free function `local_key`, used by the three sites that
*reserve* a variable before interpreting (`interp_lambda`, `interp_pi`, and the
recursor-shape opener) — those mint `fresh_var()` first and insert, so that the
body's interpretation puts the reserved variable in the bound positions.

Three consequences.

**(a) The key is the level alone. The type is not in it.** So `⟦Local{0, A}⟧` and
`⟦Local{0, B}⟧` are *the same kernel term* whenever the level-0 binder has been
opened and closed and reopened at a different type — which happens constantly,
because the counter is a stack. The interpretation is therefore **not injective
on Lean locals**, and this is true today, independently of hypotheses.

This has not yet produced a wrong answer, because the checker decides
definitional equality itself and `def_eq_local` requires equal `FVarId` *and*
definitionally equal binder types before it will call two locals equal. The
backend only certifies decisions already taken. But it does mean that "the
certificate is about the claim" — the guard every rule in `tg.rs` applies — is a
weaker statement than it reads as: two claims that differ only in a retired
level's type interpret to the same pair of kernel terms.

**(b) Variables are allocated through `Env::fresh_var`, and the field comment
says exactly why**, in terms that decide §4:

> Allocated through `Env` rather than derived from the Lean id: the derived rules
> mint fresh variables for Leibniz holes, and a collision between such a hole and
> a Lean local would substitute at the wrong occurrences — a genuine soundness
> bug, not just a wrong answer.

**(c) The map is per-backend, the `Env` is per-thread.** `TgBackend` holds an
`Rc<RefCell<Shared>>` containing the single `Env` every backend on the thread
builds terms in, so every `FreeVar` in circulation on a thread carries the same
brand and is mutually usable. What is *not* shared is the `locals` map, so two
declarations' level-0 locals get different variables even when they are the same
binder shape.

### The `idx_term` precedent, and why it is not the same shape

`MEASUREMENTS.md` records it: `idx_term` minted a fresh nullary symbol per de
Bruijn *index* per backend, so `⟦#0⟧` — and hence every value containing a binder
— differed between consecutive declarations. Moving it into `Shared` took
"shared symbols declined: body not canonical" from **15439 to 13406** and moved
no other number. `MEASUREMENTS.md` names `level_reps` and the other per-backend
tables as the places to look next.

`locals` is on that list, and moving it to `Shared` would very likely move the
counter again. But the two are **not** the same fix, and treating them as the
same is the trap:

> A de Bruijn *index* is context-free — `#0` means "the innermost binder of this
> term", and it means that in every declaration. A de Bruijn *level* is not: it
> means "the `n`-th binder the checker currently has open", which is a fact about
> the checker's stack, not about any term.

Sharing `idx_syms` was sound because the key already denoted the same thing
everywhere. Sharing `locals` on a level key would be sound only for a *different*
reason (§3), and would need the type in the key to be sound at all.

## 3. Is the identification sound? — the crux

The kernel's own statement of what a theorem means settles most of this. From
`kernel/src/thm.rs`:

> **`Γ ⊢ φ` asserts `∀x⃗. (⋀Γ → φ)`, where `x⃗ = FV(Γ ∪ {φ})`.** … A free
> variable is *schematic* — it stands for an arbitrary object, not for a
> particular one the theorem knows about — and the *same* assignment is read on
> both sides of the turnstile.

Two things follow immediately.

**A `Thm` is invariant under injective renaming of its free variables.** The
identity of a `FreeVar` carries no meaning by itself. So "which kernel variable
does this local get" is *not a kernel-soundness question at all*. It is entirely
a question about the checker's bookkeeping: whether the checker's idea of "what
is assumed about `v`" is consistent across every place `v` occurs.

**Distinct simultaneously-live locals must get distinct variables.** If
`⟦Local{0,A}⟧ = ⟦Local{1,A}⟧` then `⟦λx:A.λy:A. x⟧ = ⟦λx:A.λy:A. y⟧` and the
whole interpretation collapses. The level guarantees this, because live locals
have pairwise distinct levels. This is the one thing the level does buy, and it
buys it unconditionally.

So the question reduces to: **when may two locals that are never live at once be
identified?**

### 3.1 Identification across scopes is harmless *when the types agree*

Suppose `l = Local{0, A}` in one scope and `l' = Local{0, A}` in another, and
both interpret to `v₀`. In both scopes the standing assumption about the binder
is the *same formula*, `v₀ ∈ ⟦A⟧`. A certificate derived under one can be read
under the other by exactly the renaming argument above. This is the owner's
intuition and it is correct.

It is also correct for a subtler reason worth writing down, because it is what
makes the whole design fail *safe* rather than fail *silently*:

> **The type is already in the formula.** A binder's standing assumption is
> `Formula::mem(Term::var(w), dom)` with `dom = ⟦binder_type⟧`, and
> `guard_and_generalise_at` discharges a hypothesis **only if it is literally
> equal** to that formula (`if *f == guard`). Discharge is matched on the
> formula, never on the variable.

So a hypothesis `v₀ ∈ ⟦Nat⟧` can never be discharged by a binder whose domain is
`⟦Bool⟧`. It is *hoisted* instead, to `∀w. (w ∈ ⟦Bool⟧ → w ∈ ⟦Nat⟧)`, which stays
in the assumption list, stays owed, and is counted by the escape ledger at the
boundary. A type mismatch therefore produces a **reported gap**, not a false
certificate. That is a genuinely strong property and it should be stated as an
invariant rather than left as a happy accident (§8).

### 3.2 Where it fails: the level is a stack position, not a name

The proposal's load-bearing sentence is "a cached certificate is compatible
exactly where the same locals are in scope — which the de Bruijn level already
encodes". It does not.

**Counterexample (agreement at a level does not imply agreement below it).**
Within one declaration, consider two moments at depth 2:

| | level 0 | level 1 |
| --- | --- | --- |
| moment ①  | `n : Nat` | `m : Nat` |
| moment ②  | `b : Bool` | `m : Nat` |

Level 1 has the same level *and* the same type at both moments, so under the
proposal `⟦level 1⟧` is one variable `v₁` at both. That much is fine, by §3.1.
But a certificate derived at ① may carry hypotheses about **both** `v₀` and `v₁`
— for instance a beta domain obligation `v₀ ∈ ⟦Nat⟧` acquired by
`has_type_local` for an argument mentioning the outer binder. Retrieved at ②,
`v₀` now denotes `b : Bool`, and the certificate silently asserts something about
the wrong local.

The mixed context is not exotic. It is the *normal* case, because inference and
`def_eq` share one counter (§1): the level-0 binder is very often one `infer`
opened, and the level-1 binder one `def_eq_binder_aux` opened underneath it, and
the same `def_eq` sub-question recurs under different inference stacks.

By §3.1 this is not a *lie* — the false hypothesis will not match `⟦Bool⟧`'s
guard and will be hoisted rather than discharged. But it is a certificate that
asserts less than the claim it is handed back for, and the mechanism that catches
it is the escape ledger, i.e. it shows up as a gap somewhere else entirely. That
is the failure mode `MEASUREMENTS.md`/`certify.rs` already measured once, from
the other direction: caching conditional certificates blind took the tutorial
corpus from **49 escapes to 96** and **265 gaps to 291**, a net loss, *even
though it closed more `eq_cache` gaps*.

**Counterexample (hypotheses outlive the terms that caused them).** This is the
one that defeats "the terms in the key tell you which locals are involved".

A beta step's domain obligation `⟦a⟧ ∈ ⟦A⟧` survives the reduction that consumes
`a`. `(λ z:C. c) l₀ ⟶ c` leaves a hypothesis about `v₀` on a certificate whose
right-hand side no longer mentions `v₀`. Worse, the equality cache is a
**union-find with a proof forest**: `recall_eq` composes the certificates along
an explain path, so a hit on a pair `(a, b)` where *neither* term mentions any
local can still yield a theorem whose hypotheses mention `v₀`, because an
intermediate node on the path did.

> `FV(hypotheses) ⊆ FV(⟦x⟧) ∪ FV(⟦y⟧)` is **not** an invariant, and no cache key
> built from the terms alone can stand in for a context check.

### 3.3 Universe instantiation

Asked in the brief, and the answer is: not a separate problem, but only because
of an accident that should be made explicit. `binder_type` is a Lean `ExprPtr`
that has already had universe parameters substituted (`subst_expr_levels` runs
before the binder is opened), so two instantiations give two different
`ExprPtr`s and two different `⟦·⟧`. The `Sort` interpretation is a definitional
extension for literal successors and an opaque symbol otherwise, and level
equality is canonicalised through `level_reps`/`level_canon` — which is
**per-backend**. So two declarations can canonicalise the same level to different
representatives. That is another reason a `(level, type)` key must be keyed on
the *interpreted* type `⟦T⟧` (§4) and not on the `ExprPtr`, and another reason
sharing the map across declarations needs care.

### 3.4 A cost the proposal has, which is easy to miss

`def_eq_local` accepts two locals as equal when their ids match and their binder
types are **definitionally equal** — not syntactically equal. Today both
interpret to the same variable (the type is not in the key), so the equation is
trivially `v = v`. Put the type in the key and they become *distinct* free
variables, and `v₁ = v₂` is not derivable — it is false, schematically. The rule
is an `Admit::Local` today so nothing breaks immediately, but the proposal
**forecloses ever certifying that rule by reflexivity**.

The mitigation is to key on the *interpreted* type `⟦T⟧` rather than the
syntactic `ExprPtr`: definitionally equal types that interpret identically then
still share a variable, and the residue — types that are definitionally equal but
interpret differently — becomes an honest, countable gap rather than a silent
identification. That residue should be measured before the change lands.

## 4. Which route: kernel-minted keys, or a checker-side map

**The checker-side map. Route (A) is not merely worse; it moves a kernel
invariant into untrusted code, and it does not even avoid the map.**

The kernel's discipline is that `FreeVar` has no public constructor and
`Env::fresh_var` is the only source, so *freshness is a property of the kernel*
(`kernel/src/term.rs`: "**Not public.** The only way to obtain a `FreeVar` is
`Env::fresh_var`, so every variable in circulation belongs to some `Env` and
carries its brand"). A client-supplied key inverts that: the kernel would be
promising freshness it cannot check, on the basis that the checker does not reuse
a key for two different things.

And it is not a hypothetical hazard here. `tg.rs`'s own `locals` field comment
names the exact failure: derived rules mint fresh variables for Leibniz holes
(`Thm::eq_leibniz`, and `ty_conv` does it inline), and a key-derived variable
colliding with a hole substitutes at the wrong occurrences. To make route (A)
safe the kernel would have to partition the id space — reserve a range for keyed
variables and have `fresh_var` skip it — which is a change to the trusted base
for a client's convenience.

**The brand settles the rest.** `FreeVar` carries the brand of the `Env` that
minted it, and terms from different `Env`s must never mix. So `var_for_key` would
have to be an `Env` method anyway, stamping the shared `Env`'s brand — meaning
route (A) is route (B) with the map relocated *into the TCB*. There is no version
of route (A) that removes a map; there is only a version that makes the kernel
own it.

Route (B) also already exists. `TgBackend::locals` *is* the map. The change is to
its key, not to its existence, and the three reserve-then-insert sites plus the
`interp` lookup are the four places that touch it.

### The brand/sharing interaction, and where the earlier bug lived

The relevant structure is: **one `Env` per thread, inside `Shared`; one
`TgBackend` per declaration; `locals` per backend.** Because the `Env` is shared,
every `FreeVar` on the thread carries one brand and is usable in any
declaration's terms — that is what makes cross-declaration sharing *possible* at
all, and it is why `idx_syms`, `const_syms`, `param_syms` and the lambda/`Π`
skeleton tables could move into `Shared` without touching the kernel.

`locals` could move too, and the sharing-decline evidence says it should. But
three conditions attach, and the third is the one the `idx_term` bug teaches:

1. **The key must be brand-stable and `TcCtx`-free.** `ExprPtr`, `NamePtr`,
   `LevelPtr` are all per-`TcCtx` and cannot appear in a shared key — this is
   already why `const_syms` is keyed by `name_key` rather than by `NamePtr`. A
   kernel `Term` (`⟦binder_type⟧`) is brand-stable within the thread and is a
   legitimate shared key.
2. **The map may never be lifted above the thread.** `Shared` is `thread_local!`;
   a `static` version would mix brands and is a soundness bug, not a bug.
3. **A shared level key is sound for a different reason than a shared index key,
   and that reason must be written down.** `idx_syms` is sound because `#0` means
   the same thing in every declaration. A shared `locals` entry is sound *only*
   because free variables are schematic and the type travels inside the guard
   formula (§3.1) — not because level 0 of declaration 17 has anything to do with
   level 0 of declaration 18. If anyone later builds a cache that crosses
   declarations, that difference is exactly where it will break, and the stamp of
   §5 does **not** extend across declarations without a declaration id in it.

Recommendation on sharing: key `locals` on `(level, ⟦binder_type⟧)` and move it
to `Shared`, but **as a separate, separately-measured change from the cache
fix**. It is a sharing optimisation with a soundness precondition; it is not the
cache fix and must not be confused with it.

## 5. What the cache key becomes, and what is checked on retrieval

### 5.1 The shape the kernel note suggests does not fit this cache

`kernel/src/thm.rs` offers "key the cache on the hypothesis set as well, i.e. on
`(a, b, thm.hyps())`". That is written for a map-shaped memo and **does not
apply here**: `TcCache::eq_cache` is a `UnionFind<ExprPtr, Cert>` with a proof
forest, so there is no lookup by key — you union a pair and later ask
`explain(x, y)`, which composes the certificates on the edges of a path you did
not choose. You cannot key on hypotheses you do not have yet. What is needed is a
**retrieval-time validity predicate on each edge**, not a finer insertion key.

### 5.2 The proposal, concretely

Three pieces. All of them are in `checker/`; none touches `kernel/`.

**(i) A hash-consed context prefix in `TcCtx`.** The prefix of open binders is a
list, and this project already has the right way to give a list an O(1) identity:
intern it, the way `alloc_expr` interns an `Expr`. Concretely

```
ctx_intern: FxIndexMap<(CtxId, ExprPtr), CtxId>   // (parent, the local) -> id
ctx_ids:    Vec<CtxId>                            // ctx_ids[k] = id of the length-k prefix
```

maintained in lockstep with `dbj_level_counter`:

- `mk_dbj_level` pushes `intern(*ctx_ids.last(), the_local_ExprPtr)`.
- `replace_dbj_level` pops.
- `def_eq_binder_aux`'s two raw `dbj_level_counter -= n` must become `n` pops.
  Behaviour-preserving; it is the only place that skips the accessor.

`ctx_ids[k]` is then an **exact** identity for the entire binder prefix of length
`k` — names, styles, types and levels, since a local's `ExprPtr` already
distinguishes all four. `ctx_ids[k] == ctx_ids'[k]` iff the two moments have the
same first `k` locals, hence the same first `k` guard formulas.

Two notes on why it is built this way.

*Not a 64-bit Merkle hash.* That was the first shape I wrote and it is wrong for
this codebase. `Expr`'s `PartialEq` is derived and structural — the precomputed
`hash` field is only a bucket hint for the `IndexSet`, so nothing in the checker
currently rests identity on a 64-bit digest. A hashed context chain would be the
first thing that does, and it would do it in order to gate certificate reuse.
Interning costs one hash-map probe per binder push and removes the question.

*Keyed on the Lean `ExprPtr`, not on `⟦binder_type⟧`.* It needs no backend, it is
available at the push site, and it is strictly finer than the interpretation —
the safe direction. It also keeps `TcCtx` ignorant of the certifier, which the
crate is careful about elsewhere.

An exact-but-cheaper variant exists and is worth knowing about: give each push a
monotonic generation number and stamp `ctx_gen[depth]`. That is collision-free
with no interning, but it identifies a *frame occurrence* rather than a *frame
shape*, so a context that is re-entered with identical binders later in the
declaration will not match — which is precisely the reuse this whole design is
for. Interning is the version that keeps it.

**(ii) A reverse map in the backend.** `var_levels: HashMap<FreeVar, u16>`,
written at the same moment `locals` is written, for `DbjLevel` locals only.

**(iii) The stored certificate gains two words.** At `union` time:

```
let fv = free variables of every formula in cert.hyps();
if every v in fv is in var_levels {
    depth = 0 if fv empty else 1 + max(var_levels[v]);
    keep  = Some((cert, depth, ctx_ids[depth]));
} else {
    keep = None;          // a Unique local, or a derived-rule variable: refuse
}
```

and at `explain`/`hop` time, per edge:

```
usable  ⟺  depth <= cur_depth  &&  ctx_ids[depth] == stamp
```

**The retrieval check is O(1)** — one comparison and one indexed load. That is
the requirement the whole hypotheses-in-the-kernel change exists to satisfy, and
it is met: nothing walks `Γ` on the hot path.

The *insertion* check is `O(|FV(Γ)|)`, paid once per union, on a hypothesis list
that was just constructed. `|Γ|` is bounded by the open-binder depth and the
escape report already prints its maximum. This is bookkeeping proportional to an
object already built, not a kernel-call cost, so it does not reintroduce the
`13u² + 73u − 134` problem that the judgement change was made to avoid.

### 5.3 Why the check is exactly right

The predicate says: *no formula in `Γ` mentions a variable whose meaning differs
between the derivation context and the retrieval context.* Prefix agreement gives
precisely that, because a variable at level `ℓ` is determined by `ctx_ids[ℓ+1]`,
which the check pins. Levels *above* `depth` are irrelevant to `Γ` and are
deliberately left unconstrained — that is where the reuse comes from, and it is
the sound residue of the owner's idea.

Note what this does **not** claim. It does not claim each `h ∈ Γ` is a standing
assumption in the retrieval context; `Γ` may hold acquired beta obligations and
hoisted families that no binder will discharge. Those ride out and are counted,
exactly as they are today. The check's job is only to guarantee that they are
*about the locals they think they are about*.

### 5.4 Two invariants the implementation must not break

- **The stamp gates the certificate, never the union.** `eq_cache.union(x, y,
  keep)` must still happen unconditionally. What the checker decides may not come
  to depend on what the backend could prove; `tc.rs` already says this and it is
  the reason the `Option<C>` on `ProofEdge` exists.
- **A failed stamp is a declined hit, not a wrong one.** `explain` already gives
  up on a whole path if any edge carries no certificate; a stamp failure takes
  the same route and the caller admits `Admit::Cache`. Fail-closed.

### 5.5 Note on the level key, now that the stamp exists

With the stamp in place, the cache is safe **even with today's level-only
`locals` key**: if level 0 was `A` earlier and is `B` now, the chain prefix
differs and the hit is declined. The `(level, ⟦type⟧)` key is therefore *not*
required for cache soundness. It is required for the **interpretation** to be
injective on locals (§2a), which is a separate and older defect. Keeping the two
changes separate is worth insisting on: they have different justifications,
different risks, and different measurements.

## 6. What must land first, and it is three lines

`certify::is_unconditional` is currently:

```
pub fn is_unconditional(c: &Cert<'_, '_>) -> bool { c.is_proved() }
```

with `is_proved()` meaning `matches!(self, TgCert::Proved(_))`. **The migration
breaks this predicate without changing its text.** Today `Proved` means "derived,
full stop" because the only way to carry an assumption is the separate
`TgCert::Conditional` variant. Once hypotheses live in `Thm`, a `Proved(thm)`
with `thm.hyps()` non-empty is exactly the thing this predicate exists to
exclude, and it will answer `true`.

The fix, and it should go in with the migration commit, not after it:

```
pub fn is_unconditional(c: &Cert<'_, '_>) -> bool {
    c.thm().is_some_and(|t| t.hyps().is_empty())
}
```

This is option 1 of the kernel note ("cache only hypothesis-free theorems"),
adapted to a cache whose certificates now carry their hypotheses inside the
`Thm`. It costs nothing measurable — it is what the code does today — and it
turns a property of today's callers into a property of the code, which is the
kernel note's own stated reason for preferring it.

Everything in §5 is an *optimisation on top of this*, and given the measured
history (§3.2) it should be treated as one: implement it, A/B it, and keep it only
if the gap ledger improves.

## 7. The other three caches — this is the part nobody has looked at

The kernel note names "the definitional-equality cache". `checker/` has four
places that store a `Thm` and hand it back later. Three of them can hold
hypotheses after the migration and only one has been considered.

**`TcCache::eq_cache`** — the one everybody means. Guarded by
`is_unconditional`; §6 fixes it.

**`TcCache::infer_cache_check` / `infer_cache_no_check`** — keyed on `ExprPtr`
alone, and they store `(ty, typing_certificate)`. These **deliberately admit
conditional entries**, on a written argument:

> A memoised typing may be *conditional* on the ambient locals, and that is safe
> here in a way it is not for equality certificates: a typing's hypotheses are
> always about locals occurring in the very expression the entry is keyed on, so
> a hit under a different context asks about the same locals or does not mention
> them at all.

**That premise does not survive the migration, and arguably does not survive
today.** `ty_conv` merges the *equation's* hypotheses into the typing's
(`merge_hyps(&hyps, eq_hyps)`), and an equation's hypotheses are not confined to
the locals of the subject term — §3.2's second counterexample is precisely a beta
obligation about an argument that the reduction consumed. The argument is
asserted, not enforced, and it is the same shape as arguments this project has
twice watched evaporate. It needs either enforcement (check
`FV(hyps) ⊆ FV(⟦e⟧)` at insertion and refuse otherwise) or the §5 stamp.

**`reduct::Trace::cert`** — the reduct memos hold an `Rc`-shared trace with a
certificate slot, and `reduct.rs` is explicit that "the certificate is then
written into `Trace::cert` … and every later hit clones it". A beta step's
certificate carries the domain obligation `⟦a⟧ ∈ ⟦A⟧`. So this is a third
hypothesis-carrying store, keyed by input `ExprPtr` alone, shared across the
whole declaration. It has the same obligation and no guard at all.

**`Shared::declar_typings`** — the only cross-declaration store, and it is
**already correct**: `store_declar_typing` says "*Nothing conditional is
stored.* If the typing rests on an antecedent, the entry is skipped and the uses
report gaps". That rule is the right precedent for the other three, and it is
worth noting that it was arrived at independently.

Similarly `has_type`'s memo is keyed on `(e, ty, assms)` — assumptions *in the
key* — which is the shape the kernel note describes, and it is correct there
because the caller supplies the assumptions before the lookup. That is the
structural difference from `eq_cache` (§5.1) and it is why the same fix does not
transfer.

## 8. Invariants, and where each is enforced

Stated so they can be tested, and placed at the single site that can enforce
each.

1. **Live locals are pairwise distinct and occupy exactly levels
   `0..dbj_level_counter`.** Enforced by `mk_dbj_level`/`replace_dbj_level`;
   already asserted in debug. `def_eq_binder_aux`'s raw decrements are the one
   place that can violate it and should go through the accessor.
2. **`ctx_ids.len() == dbj_level_counter + 1`, always.** One `debug_assert` in
   each of the two accessors.
3. **`⟦·⟧` is injective on locals that are live simultaneously.** Guaranteed by
   (1) plus a level in the key. Testable: interpret two locals at different
   levels, assert different `Term`s.
4. **A hypothesis is discharged only by literal formula equality with a binder's
   guard.** True today in `guard_and_generalise_at` (`if *f == guard`), and it is
   the property that makes a type mismatch a reported gap rather than a false
   certificate (§3.1). It is currently an implementation detail; it should be
   promoted to a documented invariant with a test, because everything in this
   note's failure analysis rests on it.
5. **Nothing with non-empty `hyps` enters a cache that is not stamped.** §6 for
   `eq_cache`, §7 for the other two. This is the one that is a live unsoundness
   if skipped.
6. **The stamp gates certificates, never decisions.** §5.4.
7. **No key stored in `Shared` may mention a `TcCtx`-scoped pointer.** Existing
   convention (`name_key`); becomes load-bearing if `locals` moves.

## 9. What I could not determine

Honestly, and none of it blocks §6.

- **Whether §5 pays for itself.** The only evidence is against: caching
  conditional certificates without a context check took the tutorials from 49 to
  96 escapes and 265 to 291 gaps. The stamp turns most of those wrong retrievals
  into declined hits, so the outcome should land between "no conditional caching"
  and that measurement — but *where* between is unknown, and the honest prior is
  that the upside is modest. It needs an A/B before it is worth the machinery.
- **How often `Γ` mentions a level below the query's own binders.** This is the
  single number that decides §5's value, and nothing instruments it today. It is
  cheap to get: at each `union`, histogram `depth` against `cur_depth`. If
  `depth == cur_depth` almost always, the stamp buys nothing over §6 and should
  not be built.
- **Whether `def_eq_local`'s "same id, definitionally-but-not-syntactically-equal
  types" case ever fires**, and with what frequency. That is the entire cost of
  putting the type in the key (§3.4) and it is a counter, not an argument.
- **Whether hypotheses ever mention a `Unique` local.** §5.2 refuses to store
  those; if it turns out to be a large fraction, §5's yield drops further.
- **Whether the `infer_cache` invariant (§7) is violated in practice or only in
  principle.** I could construct the counterexample but not confirm it fires. A
  debug assertion — `FV(hyps) ⊆ FV(⟦e⟧)` at insertion — would answer it in one
  run, and is worth adding regardless of what else happens.
- **The memory cost of a `Shared` `locals` keyed on `(level, Term)`.** It grows
  with the whole run rather than with one declaration, and `MEASUREMENTS.md`
  already flags the caches as 91 MB. Unmeasured.
- **The cost of interning the context prefix.** One hash-map probe per binder
  push, on a path (`mk_dbj_level`) that is currently two field writes. `infer`
  and `def_eq` open binders constantly, so this is the one part of §5 that lands
  on a hot path rather than beside it, and I have no measurement for it. If it
  shows up, the generation-number variant in §5.2 is the fallback — cheaper,
  exact, and strictly less reuse.
- **How large `depth` typically is.** §5 refuses to store a certificate whose
  hypotheses mention any variable outside `var_levels`. If most conditional
  certificates mention a `Unique` local or a derived-rule variable, the refusal
  fires more often than the stamp does and the machinery is dead weight. This
  falls out of the same histogram as the previous point and should be collected
  in the same run.
