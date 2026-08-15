# The model basis — scoping the retirement of certified inductive construction

*A design and measurement tranche, not a build. Nothing in `checker/`, `derived/`
or `kernel/` was changed; `git diff` over those three trees is empty. Every
number below was produced with the release binary at master `4c6426a` — line
counts re-verified unchanged at `5bab7c0` — or read off the external tool's own
source. Where a claim is unmeasured it says so.*

*Revised 2026-08-15 at master `dd1996e`, again with no change to `checker/`,
`derived/` or `kernel/`. The revision is confined to `PSigma'`: §0, §3.3, §3.5,
§3.6, §8.2, §8.6 and §9. **The claim that closing `PSigma'` needs a new
`derived/` construction was wrong**, and the statement it was scoped around,
`⊢ Σ ∈ U₀`, is refutable rather than missing. Corrections are made in place;
where a conclusion reversed, the superseded reasoning is stated so the reversal
can be checked rather than taken.*

*Revised again 2026-08-15 at master `5813df2`, on branch `joachim/model-scale`,
once more with no change to `checker/`, `derived/` or `kernel/` — this document
is the only change on the branch. The revision adds **§6.1**, which runs the
external tool over the full 5.6 GB Mathlib export and a five-point size ladder
below it, and rewrites **§8.1**, which said the tool had not been run over
Mathlib. It also corrects **§0** and one bullet of **§8.6**, whose estimate of
the added-declaration count was low by a factor of 2.4. The tool was built in a
scratch copy; `vendor/lean-inductive-models` is untouched at `5a9a70f`.*

The proposal: **every non-basis inductive arrives in the export as a *model*
built over a fixed basis, and the checker recognises the model and cases on its
theorems, instead of constructing a carrier, recursor and ι rule itself.** The
owner's dispatch rule is three-way and total:

1. **basis** — `Eq`, `Nat`, `PUnit`, `PSigma'`, `Quot`: our own clauses;
2. **non-basis with a `_model`** — recognise it, case on its theorems, use it;
3. **non-basis without a `_model`** — **decline, loudly and by name.** There is
   no construction to fall back to, because the construction is gone.

The external producer is `github.com/nomeata/lean-inductive-models`, read here at
`vendor/lean-inductive-models` (HEAD `5a9a70f`, 2026-08-14). It is a separate
product and a `vendor/` read-only dependency; this document cites its own
contract rather than speculating about it.

## 0. Verdict in one paragraph

The pivot is sound and the retirement is real: **up to 23 656 of
`checker/src/mini`'s 55 255 lines retire** (§5 says why that is an upper bound
and not yet a measurement), and they retire *by policy* — unreachable because no
dispatch reaches them — not merely by circumstance. The load-bearing claim holds:
a model is a pile of `def`s and `theorem`s, those route to **nanoda**, and
nanoda's `def_eq` has had the identity fast path since the beginning. But the
tranche's stated motivation is void: **the `def_eq` defect that prompted it was
fixed sixteen commits before this branch point**, so the pivot must be justified
on the retirement and on §6 instead.

**§6 is the strongest result here and it is new.** Running the external tool over
`init-prelude` gives **144 model families, 0 declines, 3 exempt** — and every one
of the 91 declarations and 10 eliminators we currently refuse as `type former
spine` or `field type uninterpretable` is among the modelled: the machine words,
`Char`, `String`, `Fin`, `BitVec`, `ByteArray`, `Lean.Syntax`, the heterogeneous
operator classes, `Trans`, `False`, `PEmpty`, `HEq`. **That entire category of
refusal disappears.** Nobody had considered it and it is now measured.

**§6.1 carries that result to full Mathlib, and it holds: 6 882 model families,
0 declines, 3 exempt, 48 677 statements compared at 0 differing, the whole-stream
kernel replay accepted, in 53 minutes and 10.6 GiB of peak RSS, growing the export
1.05× in bytes.** Zero declines at every rung of a six-point ladder from 3.7 MB
to 5.6 GB. The scale risk §8.1 was written around is closed, and the producer's
half of the pivot is measured rather than assumed. **The unmeasured half is now
the recognition side alone** (§4.2, §8.4, §8.6), which cannot be run until our
recogniser and the tool agree on a name.

Two costs the brief did not price stand against it, one measured red here for the
first time: **`PSigma'` is partly untranslatable by our current machinery** — at
`σ = (1,1)` it declines `ind-spec(PSigma': class (P) above Prop)` — and **`Acc`
has left the basis**, so the 3 519-line `Acc` family retires and every
well-founded definition arrives instead as a `Classical.choice`-bearing model.

*Corrected 2026-08-15, by measurement, against the §3.6/§8.2 this document first
shipped: closing `PSigma'` needs **no new `derived/` construction at all**. Both
memberships it wants already exist and are each measured on this exact shape —
`⊢ ‖a‖ ∈ U₀` at `σ = (0,0)`, where `PSigma'` **already translates today**, and
the general data carrier at `Uₙ` for `n ≥ 1`, measured on `PSigma.{1,1}`, which
is the same instantiated declaration. The obstruction is a classification in
`checker/`, not a missing set-theoretic fact. §3.6 and §8.2 carry the corrected
account and the derivation of why `⊢ Σ ∈ U₀` must never be built.*

## 1. The decisive question, answered

> Would a model's declarations be checked by **nanoda's** `def_eq`, which has the
> identity check and the certification machinery, or still by **mini's**?

**By nanoda's.** Established three independent ways, none of them an assumption.

### 1.1 The external contract requires the two kinds

`vendor/lean-inductive-models/README.md`:

> The generated type formers, constructors, and recursors are safe definitions;
> reduction rules are theorems.

This is *enforced*, not merely documented. `src/InductiveModels/Check.lean`'s
structural checker rejects any implementation slot that is not a safe definition
and any proof slot that is not a theorem:

```lean
-- Check.lean:642-651
if declaration.kind != .defn then
  #[.declarationKind owner declaration.name .defn declaration.kind]
else if declaration.safety? != some "safe" then
  #[.declarationSafety owner declaration.name (declaration.safety?.getD "<missing>")]
...
if declaration.kind == .thm then #[] else #[.declarationKind owner declaration.name .thm declaration.kind]
```

with the same test repeated at `:731-741`, `:910-914` and `:952` for the private
mutual and one-layer bookkeeping. `DeclarationKind` (`Check.lean:423-431`) can
express `.induct`, `.ctor`, `.recursor`, `.axiom`, `.opaq` and `.quotient`; the
checker admits **none of them** at a model slot. The kind restriction is part of
the advertised contract, not an artefact of the current routes.

### 1.2 Our dispatch sends exactly those two kinds to nanoda

Every hop, in order:

| step | site | what happens |
| --- | --- | --- |
| 1 | `checker/src/mini/route.rs:103-105` | `Declaration::Def{kind: DefKind::Def}` → `DeclKind::Definition`; `DefKind::Theorem` → `DeclKind::Theorem` |
| 2 | `route.rs:116-122` | `Mode::Split::pick` sends `Definition`, `Theorem`, `Opaque`, `Axiom` to `Pick::Checker`; only `Inductive` and `Quotient` go to `Pick::Mini` |
| 3 | `route.rs:390-411` | `Routed::accept`'s `Pick::Checker` arm calls `via(c, d)` — the `GroupEngine` seam |
| 4 | `route.rs:167-189` | `CheckerEngine::check_group` calls `RoutedChecker::check_anchor` per group name |
| 5 | `checker/src/routed.rs:196-205` | `check_anchor` walks the group's export entries into `check_declar_scheduled` |
| 6 | `routed.rs:70-90` | `check_declar_scheduled`'s `matches!(d, Declar::Inductive(..) \| Declar::Quot{..})` early return **does not fire** for a `def` or a `theorem`; it goes down the schedule path to `check_declar_at` |
| 7 | `checker/src/tc.rs:2914` | nanoda's `def_eq_quick_check` opens `if x == y { … refl … }` |

And the negative half, which matters as much: `Driver::evidence`
(`route.rs:337-350`) returns `false` on `Pick::Checker`. **Mini's evidence walk
never touches a model declaration.** `install_checked_noninductive`
(`kernel.rs:5471-5493`) puts the accepted syntax into mini's environment
*without* inferring a type, comparing a value, or applying mini's acceptance
rules — its own doc comment says so — solely so a later mini-routed inductive can
name it.

**Routing is the default, not a flag.** `checker/src/bin/checker.rs:166-176`:
`--route` was *removed*; `Mode::Split` is what a plain invocation gets, and
`--naive` is the opt-out. (A `--naive` run is mini-only and would put models on
mini's `def_eq` — that is the one configuration in which the pivot does not
dissolve the question, and it is not the production path.)

### 1.3 Measured on a real export

`checker/tests/fixtures/nested_keying.ndjson` carries 27 `_model` declarations.
Classified out of the export by kind: **16 `def`, 11 `thm`, zero inductives,
zero axioms.** The run reports

```
nested_keying.ndjson	accept	39 declarations	untranslated: 2 declarations	tg gaps:526
route	mode=Split	toMini=8	toChecker=31	unclaimed=0
```

31 of 39 declaration groups to nanoda, 8 to mini — the 8 being the inductives and
the quotient bundle.

**So the pivot dissolves the question rather than relocating it.** The residue is
named in §7.

## 2. The premise is stale: the defect was already fixed

The tranche was prompted by mini's evidence-producing `def_eq` lacking an
identity fast path, normalising 262 144 unary `Nat.sub` steps twice to discover
that a term equals itself.

**That fast path is in the tree and has been since before this branch existed.**
`checker/src/mini/kernel.rs:4298`, inside `assert_def_eq_as`:

```rust
if e1 == e2 {
    match (&tm1, &tm2) {
        (None, None) => { … return Ok(Conv { to: *e2, ev: Ev::missing(Gap::NoEndpoint) }) }
        (Some(a), Some(b)) if a == b => { … return Ok(Conv::refl(*e2, a)) }
        _ => {}
    }
}
```

`def_eq_ev` has exactly **one** caller — `assert_def_eq_as` at `:4357` — so the
guard covers every conversion. It landed in `d263be2`, *"checker: syntactic
equality before reduction — init-prelude ACCEPTS, prefix 44 → 152"*, dated
2026-08-15, **sixteen commits before** the branch point `4c6426a`, and
`MEASUREMENTS.md:11000-11090` records its effect: `init-prelude` went from
declining at declaration 44 to accepting 1 822 declarations, 28.211 T → 0.507 T
instructions, certified prefix 44 → 152.

Two consequences.

* **The pivot cannot be justified by the `def_eq` issue.** It must stand or fall
  on the retirement in §5 and the frontier in §6.
* **The alternative the owner rejected is also cheaper than it looked.** "Make
  the checker for inductives use the nanoda `def_eq` routine" was priced against
  a mini `def_eq` that lacked the check Lean opens with. It no longer lacks it.
  That does not make the alternative *good* — mini's `def_eq` still has no
  `is_def_eq` cache where Lean's kernel keeps one (`kernel.rs:4300-4306`) — but
  the gap between the two engines is one fix narrower than the brief assumed.

The identity guard is also *partial*, and the residue is the interesting part:
it fires when both endpoints are absent, or when the two endpoints are the same
`Term`. A caller that hands in two different spellings of one interpretation
falls through to the full walk. `MEASUREMENTS.md:11036-11046` records six such
pairs on `nat_char_equations`. That residue is not addressed by this pivot
either way.

## 3. The basis — what exists, and what `PUnit` and `PSigma'` need

### 3.1 The basis is five, and `Acc` is not one of them

`vendor/lean-inductive-models/src/InductiveModels/Simple.lean:204`:

```lean
def basis : List Name := [`Eq, `PSigma', `Nat, `PUnit, `Quot]
def inductiveBasis : List Name := [`Eq, `PSigma', `Nat, `PUnit]   -- :221
```

with `Quot` the kernel quotient bundle rather than an ordinary inductive. The
same file, `:210-215`, states the change that costs us the most:

> **`Acc` was the fifth and is not here any more.** Its one grant — the
> subsingleton-recursive large eliminator — is derived by `graphArm`, so `Acc` is
> an ordinary declaration and models like one.

`README.md` states the consumer's obligation in one sentence: *"A consumer using
models as an inductive front end must implement the five-member basis and admit
the standard axioms used by the selected generated route."* Those axioms are
`Quot.sound` on the funext routes, plus `Classical.choice` and `propext` where a
route requires them.

**This supersedes `MODELGEN.md`'s basis.** That document records
`Modelgen.primBasis = [Eq, PSigma, Nat, PULiftP]` (`MODELGEN.md:2411, 2822,
3461`) — Lean's `PSigma` with its `max 1`, and `PULiftP` in place of `PUnit`. The
successor tool changed both. `MODELGEN.md` describes a tool this repository is
retiring and should be read as history from here on.

### 3.2 What we have today

| basis member | our clause | where | state |
| --- | --- | --- | --- |
| `Eq` | `direct.rs` row `Clause::Eq`, plus `eq_rec`/`eq_bottom` | `direct.rs:257`, `recursor.rs:399-549` | **exists** |
| `Nat` | `direct.rs` row `Clause::Nat`, `nat_clause.rs`, `rec_nat.rs`, `iota_nat.rs` | 1 046 lines + the row | **exists** |
| `Quot` | `quot.rs`, `quot_classes.rs`, `quot_iota.rs` | 1 595 lines | **exists** |
| `PUnit` | none — served by the *general* class-(S) rule | `class_s.rs`, `unit_like.rs` | **not a clause** |
| `PSigma'` | none, and the general machinery **declines it** | — | **red, measured** |

The brief said clauses exist for `Eq`, `Nat` and `Quot`. **Verified — they do.**
It implied `PUnit` might be one. It is not, and the tree contains a test
asserting the opposite, `direct.rs:720`:

```rust
assert_eq!(clause_for(&nm("PUnit")), None, "PUnit is not a direct clause");
```

`direct.rs:716` and `class_s.rs:45` record why: `And` and `PUnit` **used to be**
rows of the closed-form table and were deliberately retired into the general
class-(S) rule. Reinstating a `PUnit` clause is therefore a re-derivation of
something this repository once had and chose to delete — which is exactly the
case where a provenance marker is worth only a re-derivation, not a revert.

### 3.3 `PSigma'`, and the measurement that decides part 1

`PSigma'` is defined canonically at
`vendor/lean-inductive-models/src/InductiveModels/Simple.lean:261`, and the
fixture `test/fixtures/inductive-models/tight_psigma_prime.lean:13` spells it:

```lean
inductive PSigma' {α : Sort u} (β : α → Sort v) : Sort (max u v) where
  | mk (fst : α) (snd : β fst) : PSigma' β
```

It differs from Lean's `PSigma` in exactly one place — the resulting universe is
`max u v`, with **no built-in `1`** — and it therefore crosses Lean's bootstrap
resulting-universe boundary: the elaborator refuses it, the kernel takes it. That
is the whole point of it: `Subtype`, every structure with a `Prop` field, and
every `Prop`-fibred pair need a Σ that does not raise the level.

**The external repository ships an export of that fixture, so this is measurable
rather than arguable.** Running our checker on it:

```
tight_psigma_prime.ndjson	accept	3 declarations	untranslated: 3 declarations
elim	PSigma'	computed=false	oracle=false
untranslated	declarations=3	constructors=0	eliminators=0
  notrans:ind-spec(PSigma': class (P) above Prop)=1
  notrans:ind-spec(PI2:     class (P) above Prop)=1
  notrans:ind-spec(PIDep:   class (P) above Prop)=1
```

**A mandatory basis member is partly untranslatable by our current machinery
today.** So are `PI2` and `PIDep`, the two companion shapes the same fixture
carries for the same reason.

**It is not red at every σ, and which σ is red decides the whole shape of the
fix.** The verdict line counts a declaration once, so it hides the split. Per σ
(`--dump-theorems --dump-only=PSigma'`, release binary, same fixture):

```text
PSigma'   σ = [0,0]   ⊢ ⟦PSigma'.{0,0}⟧ ∈ f69(⟦Sort 0⟧, ⟦Sort 0⟧, ⟦Sort 0⟧)
PSigma'.mk   σ = [0,0]   stored          PSigma'.rec   σ = [0,0]   stored
  class-(P) PSigma' σ = [0,0]   1 constructor(s), truncated
    ‖a‖ ∈ U₀      ⊢ ∀x0 x1. f61(f60(x0, x1)) ∈ ⟦Sort 0⟧
    only_point    ⊢ ∀x0 x1 x2. (x2 ∈ f61(f60(x0, x1)) → x2 = ⟦PSigma'.mk.{0,0}⟧)
    ι             (none — every inhabitant of ‖a‖ is •, so the reduction is
                   reflexivity and no equation is retained)

PSigma'   σ = [1,1]   declaration not translated:
                      ind-spec(PSigma': class (P) above Prop)
```

**`PSigma'.{0,0}` translates today, with its full class-(P) apparatus.** The two
scheduled σ are `[0,0]` and `[1,1]`; only the second declines.

The refusal site says precisely what is missing —
`checker/src/mini/zoneb.rs:1402`, `if shape.result_level != 0` — and the comment
above it, `zoneb.rs:1394-1400`, is a written commitment rather than an open
problem:

> The replacement is scheduled rather than open: `TruncCarrier::in_un`,
> `⊢ ∀p⃗∀x⃗. ‖a‖ ∈ Uₙ` for `n ≥ 1`, from `in_u0` + `Rung::u0_mem` +
> `Rung::transitive` — all present, **a signature change rather than a
> derivation** … A `good/` `Squash.{u} (α : Sort u) : Sort u | mk : α → Squash α`
> is what would open it.

It was deferred for one stated reason: *"no accepted file can exercise it and no
fixture can test it"* — every class-(P) declaration in `good/` has resultant sort
literally `Sort 0`, and the only witness lived in `bad/`. **`PSigma'` is that
witness, and the pivot supplies it.** The blocker was never the mathematics; it
was the absence of an input that could test the wiring, and the external repo
ships one.

### 3.4 What `PSigma'` actually demands of us — less than a recursor

The natural fear is that a basis `PSigma'` means building a large-eliminating
recursor for it. It does not, and the external repo says so at
`Simple.lean:252-259`:

> Only the inductive and its constructor are primitive. The named projections
> and the universe-polymorphic eliminator below are ordinary definitions over
> primitive `.proj` expressions. In particular, `PSigma'.rec'` does not add a
> second kernel exception: **structure eta** makes `mk t.1 t.2` convertible to
> `t`, so `fun h t => h t.1 t.2` has an arbitrary `Sort w` motive and its
> constructor rule is reflexivity.

Confirmed against the shipped export: `PSigma'.rec` carries level params
`[u, v]` — **two, with no motive level** — where Lean's own `PSigma.rec` carries
`[u_1, u, v]`. `PSigma'.rec` is small-eliminating; the large eliminator `rec'` is
an ordinary `def`, which under §1 routes to nanoda like any other.

So the obligation on our side is:

1. `⟦PSigma' α β⟧` at every `(u, v)`, landing in `⟦Sort (max u v)⟧` — including
   `u = v = 0`, where the carrier must be a **subsingleton**, and mixed
   `(0, 1)` / `(1, 0)`;
2. `⟦PSigma'.mk⟧` and its membership;
3. **primitive projections** `⟦t.1⟧`, `⟦t.2⟧` with their computation rules;
4. **structure eta** as a certified definitional equality;
5. the small recursor `⟦PSigma'.rec⟧` and its one ι rule.

Items 3 and 4 are where our current state is weakest and it is recorded in the
tree: `proj_prop.rs:422-426` states that `PProd.{1,1}` and `PSigma.{1,1}` *reach
that route and decline*, because at `u = v = 1` the field is data and the
projection owes a term rather than `•`; those pairs belong on `proj_data.rs`'s
route instead. Lean's `PSigma` does translate today — `081_PSigma.snd.ndjson`
accepts at **1 tg gap**, `untranslated declarations=0` — so the data-side
projection route works. What is unmeasured is that route at `PSigma'`'s tighter
universe, and in particular at `u = v = 0`.

`PUnit`'s obligation is smaller and better understood: a carrier in `⟦Sort u⟧`
for every `u` (Prop at `u = 0`, a singleton above), the constructor, the small
recursor and its ι rule, and unit-like η — for which `unit_like.rs` already
exists and whose header (`unit_like.rs:39-46`) records `PUnit`'s two σ as the
worked case.

### 3.5 The design choice this forces — and why the obvious answer is wrong

The obvious move is **closed-form clauses**: new `direct.rs` rows for `PUnit` and
`PSigma'`, in the style the `Eq`, `Acc` and `Nat` rows use, sharing
`direct::build`'s λ-nest walk, after which `class_s.rs`, `proj_prop.rs` and the
rest of the general machinery genuinely delete. **This tranche drafted that
recommendation and then had to withdraw it.** Two findings kill it.

**First, `direct.rs` carries a standing rule against exactly this**, and it is
about `PUnit` by name — `direct.rs:44-58`:

> `And` and `PUnit` were the other two, with closed forms `and_set(a,b)` and `1`
> and a delete-by attached … Both rows are gone and both declarations now go
> through `crate::mini::class_s`. **The table takes no fourth row**, and this is
> the standing rule rather than a note about the past: a declaration that seems to
> want one is evidence that the general clause is missing a case, and belongs in
> the ledger as a gap naming that construction.

**Second, the general route already serves both types, measured.**
`MINI-HANDOFF.md:855,857,894,896` records `PProd.{0,0}` / `PSigma.{0,0}` — 4 pairs,
closed via `DeclFields` — and `Prod` / `PProd.{1,1}` / `PSigma.{1,1}` — 16 pairs,
closed via `DeclProj`. `proj_prop.rs:582` records `⊢ ⟦PUnit.{1}⟧ ∈ ⟦Sort 0⟧`
sitting in the store. A closed-form clause would be replacing working coverage,
which is the `direct.rs` header's exact objection.

**So the answer is (b): a slice of the general machinery stays, deliberately, to
serve the basis.** That is `class_s.rs` (616), `proj_data.rs` (962),
`proj_prop.rs` (1 006), `unit_like.rs` (133), and the part of `zoneb.rs` that
builds a non-recursive, non-indexed class-(T)/class-(S) carrier. The last is not
a clean file boundary and the retirement in §5 counts `zoneb.rs` as retiring
*in full*, which is therefore an over-count by an unmeasured amount. Bounding it
is the first piece of implementation work, not a design question.

This costs the pivot some of its purity — a general construction path survives,
reachable for exactly four declarations — but the alternative is deleting working,
certified coverage and rebuilding it as a special case, against a rule the file
already states.

#### The standing rule, applied to `PSigma'` — and why the basis is the exception

*Added 2026-08-15, from a tranche briefed to build a custom clause for
`PSigma'`. A rule overridden without its reasoning addressed is how a good rule
rots, so this records the argument rather than the verdict — and the argument
turns out to narrow the override rather than justify it.*

`direct.rs:44-58` says the table takes no fourth row, and gives the test: **"a
declaration that seems to want one is evidence that the general clause is missing
a case, and belongs in the ledger as a gap naming that construction."** Apply it
literally to `PSigma'` and the rule *acquits itself* — §3.6 shows the general
clause is missing no construction at all. Both carriers exist, both are measured
green on this exact shape, and no set-theoretic statement is absent. Under the
rule's own test, a closed-form `PSigma'` row would be exactly the mistake the
rule forbids.

**What `PSigma'` needs is not a construction but a *policy* — and the general
route is forbidden that policy on purpose.** `zoneb::large_eliminating` must read
the declaration's own level expression and never σ's, because deciding the class
per instantiation would hand a W-type to a declaration that is a `Prop` at
`u := 0` (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3, pinned by
`zoneb::tests::a_possibly_prop_declaration_never_acquires_a_w_type`). `PSigma'`
is a declaration whose two instantiations genuinely want two carriers. So it is
not evidence of an incomplete general clause; it is evidence that the general
clause is **correctly complete and correctly conservative**, and that one
declaration needs a licence the general clause must not be given.

That is what "basis" buys, and it is the narrowest possible exception: five
named declarations, name-keyed and shape-verified against the export
(`direct.rs:62-80`), where §3.1 already establishes that nothing ever compares
carriers across instantiations. The rule stands unamended for every non-basis
declaration — which, after the pivot, is a population that no longer reaches
this code at all.

### 3.6 What `derived/` already has — which is everything `PSigma'` needs

Against §3.4's five obligations, the set-theoretic side is **complete**, and the
`PSigma'` build this section originally scoped **must not be built**.
*(Statements are quoted as the constructions conclude them; how the evidence
reaches TG is `tc.rs`'s business and is being reworked separately.)*

| obligation | construction | concludes | state |
| --- | --- | --- | --- |
| dependent sum | `derived/src/sigma/dsum.rs:103` | `⊢ ∀p⃗∀q. (q ∈ Σ(p⃗) ↔ (q ∈ dom(p⃗) × ⋃img(p⃗) ∧ π₂q ∈ fib(p⃗,π₁q)))` | **exists** |
| pair + projections + β | `derived/src/proj.rs:86-91` | `⊢ ∀a∀b. π₁⟨a,b⟩ = a`, `π₂⟨a,b⟩ = b` | **exists**, used by `proj_data.rs:275` |
| singleton at a rung | `derived/src/isum/in_universe.rs:138`, `derived/src/tower.rs:33` | `⊢ ∀c. 1 ∈ U(c)`; `⊢ 1 ∈ U₀` | **exists**, two lemmas not one |
| unit-like η | `derived/src/sums/unit_type.rs` | `⊢ x ∈ 1 → x = •` | **exists** |
| structure η | `derived/src/sigma/dsum.rs:111`, `derived/src/inductive/decl_proj.rs:322` | `⊢ ∀p⃗∀q. (q ∈ Σ(p⃗) → ⟨π₁q,π₂q⟩ = q)`; `⊢ ∀p⃗∀z. (z ∈ ind(p⃗) → ctor₀(π₀z,…) = z)` | **exists**, used by `proj_data.rs:649` |
| **Σ in a rung** | `derived/src/cumul/sigma.rs:311`, `sigma_n.rs:373` | `Σ(p⃗) ∈ Uₙ ⇐ β₀ ∈ Uₙ ∧ img ∈ Uₙ` | **exists and is public** — `unary_telescope_at`, `unary_summand_at`, `summand_at`, all re-exported at `derived/src/cumul.rs:96-100` |
| **Σ is a subsingleton when its components are** | — | `⊢ ∀x∀y. ((x ∈ Σ(p⃗) ∧ y ∈ Σ(p⃗)) → x = y)` | **not found — and not needed**, see below |

Two corrections to this table as it first shipped. "Private and telescope-bound"
was half wrong: the `Uₙ` route has **five public entry points**, and
`unary_telescope_at` has already been freed of the declaration — its doc
(`cumul/sigma.rs:295-300`) says "This form takes the telescope directly … The
declaration was never used for anything but its parameters and that pin."
*Apparatus*-bound (an `IndChain`, a `Machine`, a `Telescope`) is the accurate
word. And there is **no `max(1, …)` clamp in `derived/`'s executable code at
all** — all six occurrences (`cumul/sigma.rs`, `cumul/sigma_n.rs`,
`cumul/decl.rs`, `cumul/tags.rs`, `inductive/family/trunc_rec_ix.rs`,
`tower/cumulative.rs`) are inside `//!` doc comments, stating a *caller
scheduling rule* that avoids minting a second Replacement symbol. The
restriction to `n ≥ 1` is type-level: every entry takes `rung: &Rung`, and
`Tower::at(0)` is `None`.

#### `⊢ Σ ∈ U₀` is not missing. It is **false**, and the thesis excludes it

This is the correction that matters, because the original text scoped a build
around reaching it. `derived/src/tower.rs:69-80` says why no *route* exists:

> `U₀` is `Prop`, not a universe … it is not closed under power set … So `U₀`
> gets the membership condition, the subsingleton property and `[φ] ∈ U₀`, and
> **none of the closure clauses**; `Tower::at(0)` is `None` rather than a `Rung`
> whose fields would be unprovable.

But the statement is not merely unreachable, it is **refutable**, and no amount
of new construction can close it:

* `U₀ = {0,1}` exactly — `Tower::u0_members`, `⊢ ∀p. (p ∈ U₀ ↔ (p = 0 ∨ p = 1))`
  (`derived/src/tower/rungs.rs:57`), built literally as the unordered-pair axiom
  at `{0,1}`.
* `0 = • = ∅` and `1 = {∅}` (`derived/src/sums/unit_type.rs:12`), and pairs are
  Kuratowski (`derived/src/proj.rs:21`).
* So `Σ(1, λ_.1) = {⟨∅,∅⟩} = {{{∅}}} = {1}`, which is neither `0` nor `1`.
  **A non-empty Σ is provably not in `U₀`.**

Carneiro agrees by construction. `thesis.txt:2461-2470` states the tagged-type
clauses **"For n > 0"**, with `T₀ = U₀` and `⌜p⌝ = p` at zero; the `(Σ, A, B)`
clause has no instance at `n = 0`. **There is no Σ at Prop in the model.** A
`Prop`-valued dependent pair is a conditional singleton, and `Tower::cond_in_u0`
(`⊢ [φ] ∈ U₀`) is the door — the only door, and the right one.

**This repository has already made exactly this argument once, for `Quot`, and
acted on it.** `derived/src/quot/universe.rs:37-46`, arrived at independently:

> **Rung 0 is not** [of the form `U(c)`], and the theorem is false there:
> `U₀ = {0,1}`, `quot(1,R) = 1` for the one-point carrier, and `{1} ∈ U₀` is
> refutable. That is not a gap to be closed — `QUOT-MODEL.md` §2 establishes
> that at `Sort 0` the interpretation is the **identity**, `⟦Quot α r⟧ = ⟦α⟧`,
> and `derived/src/quot/` is not consulted at all. So the `c ≥ 1` restriction is
> where the two branches meet, not a weakness of this route.

Same shape, same refutation, same resolution: **a basis member whose carrier is
built at rung `n ≥ 1` takes a different interpretation at `Sort 0`, and the
`derived/` construction is simply not consulted there.** `Quot` is a basis
member that already branches per σ and is green. So the per-σ split §8.2 asks
for on `PSigma'` is not a new exception being invented for it — it is the
established treatment of the one other basis member with a rung-bound carrier.

Hence the missing "Σ of subsingletons is a subsingleton" is **not needed**: the
only thing that wanted it was the derivation of `Σ ∈ U₀`, which must not exist.
Likewise the absent `z ⊆ 1 → z ∈ U₀` (confirmed absent; only the converse
`∈ U₀ ⟹ ⊆ 1` exists, at `checker/src/mini/rec_prop.rs:578`) is not on this path.

#### So what does `PSigma'` need? Two carriers, both already built and measured

`⟦Sort ℓ⟧ = U_ℓ` (`derived/src/inductive/family/universe.rs:34`), so the rung is
read off the *instantiated* resultant sort `max u v`:

| σ | rung | carrier | construction | measured |
| --- | --- | --- | --- | --- |
| `max u v = 0` | `U₀` | truncation `‖a‖` | `TruncCarrier::in_u0` over `Tower::cond_in_u0` (`derived/src/inductive/family/trunc.rs:214`) | **green today** — §3.3 dumps the full apparatus at `σ = (0,0)` |
| `max u v ≥ 1` | `Uₙ` | the general data carrier | `DeclUniverse::over_at` / `IndexedUniverse::over_at`, over `cumul/sigma.rs`'s `Σ ∈ Uₙ` | **green today on the identical shape** — `PSigma.{1,1}` |

The second row is the load-bearing one. `PSigma.{1,1}` and `PSigma'.{1,1}` are
**the same instantiated declaration**: they differ only in the declared sort,
`Sort (max 1 u v)` against `Sort (max u v)`, which at `u = v = 1` is `Sort 1`
either way. `081_PSigma.snd.ndjson` dumps the whole apparatus for it — carrier,
carrier ax, `ctor 0 mem`, `ctor 0 inj`, rec typing, `ι 0`, `gen ι 0`, rec abbrev
at `σ = [1,1,1]` — with `untranslated declarations=0`.

**Therefore the honest cost of basis member `PSigma'` in `derived/` is nothing.**
Both memberships exist; each is measured on this exact shape. What blocks
`PSigma'.{1,1}` is a **classification in `checker/`**: `zoneb::large_eliminating`
(`zoneb.rs:1149`) reads *the declaration's own* level expression, and `max u v`
is not `provably_nonzero`, while two data fields fail the subsingleton test — so
`PSigma'` is class (P), goes to `build_trunc`, and `build_trunc` refuses a
nonzero numeral sort at `zoneb.rs:1402`. §8.2 carries the consequence.

## 4. The recognition path — what it takes to generalise

The brief said `modelgen.rs` and `nested_splice.rs` recognise a spliced `_model`.
**One correction: `modelgen.rs` (227 lines) recognises nothing.** It discovers the
filter binary and streams the export through it as a subprocess; the recogniser is
`nested_splice.rs` (926 lines) alone.

### 4.1 The recogniser is already generic; the *gate* is not

`nested_splice.rs` produces (`:1-15`, `:311`):

* `model_of : HashMap<ModelKey, Name>` — which model constant carries `⟦T⟧`,
  `⟦T.ctorᵢ⟧`, `⟦T.rec_k⟧`, keyed with σ included;
* `model_iota : HashMap<(ModelKey, Name), Name>` — which theorem is `T.rec_k`'s
  rule on a given constructor;
* the σ propagation from the export constant onto the model constant.

It keys on a **table filled from statement-shape checks**, deliberately not on a
name rule — `nested_splice.rs:47-67` argues the point at length, and the argument
is the `_auxCarrier` incident: a name rule answers for a constant that exists for
some other reason. The shape check is explicitly a *diagnostic* and not the trust
root (`:69-92`); what makes a conclusion trustworthy is the certificate, and a
`_model` tower with wrong statements produces none.

The consumer, `zoneb::model_alias` (`zoneb.rs:299-332`), is **already free of any
mention of nesting** except in its reason strings. It is four lines of real work:
look up the model constant at this σ, look up its interpretation, republish it
under the export constant's key, and deliberately *not* carry the defining
equation across (`zoneb.rs:295-298` — `T` is a primitive inductive and has no δ
step, so handing the model's δ equation on would be offering a reduction Lean does
not have).

**The nesting specificity is two gates and nothing else:**

| gate | site | what it does |
| --- | --- | --- |
| the recogniser's | `nested_splice.rs:458-465` | `crate::mini::nested::plan(env, …)`; `Ok(None)` means "an ordinary declaration" and the loop body **ignores it**. Nothing else decides. |
| the consumer's | `zoneb.rs:248` | `if let Some(why) = nested_seen(c, &ind_name)`, where `nested_seen` (`:279-282`) is membership in `app.nested` — the table the recogniser fills only for nested declarations. |

Generalising is: drop the `nested::plan` gate so the recogniser attempts every
inductive, and change `nested_seen` from "is in `app.nested`" to "is a non-basis
inductive". Under the owner's rule the second gate becomes **total**: a non-basis
inductive with no `model_of` entry at this σ declines — which is already
`model_alias`'s behaviour (`zoneb.rs:314-316`, `nested model not keyed here`), and
already what `zoneb.rs:243-247` argues is the *right* behaviour, in terms:

> A declaration in `nested` and not in `model_of` **declines here.** It does not
> fall through … any later route that *did* succeed would be interpreting `T` as
> something the splice never checked.

That is the owner's rule, already written down, for a smaller population.

### 4.2 What the recogniser must be taught

*Item 1 **landed** on 2026-08-15 at `236ba86`, "checker: read
lean-inductive-models' model names beside modelgen's". It is corrected in place
below rather than struck through, and the one claim in it that was wrong is
named where it was made. Items 2 and 3 are open and unchanged.*

Three things, none of them structural:

1. **The new naming scheme, which shares no name with the old one.** Measured,
   not read off the README: the names in the tool's own output fixture
   `test/fixtures/inductive-models/filtered/nested_keying.ndjson` are

   ```text
   Tree._model                 the carrier          (we look for Tree._model.self)
   Tree.leaf._model            a constructor        (we look for Tree._model.ctor_0)
   Tree.node._model            a constructor        (we look for Tree._model.ctor_1)
   Tree.rec._model             the recursor         (we look for Tree._model.rec_0)
   Tree.rec._model.iota_0      a rule               (we look for Tree._model.iota_0_0)
   Tree._model._impl.pack_0    private bookkeeping  (README: not API)
   ```

   against `nested_splice.rs:289-304`, which builds `T._model.self`,
   `T._model.ctor_j`, `T._model.rec_k`, `T._model.iota_k_j`. **The two schemes
   overlap in nothing.** The mismatch fails closed — a name that is not found
   reads as "no model", which under the owner's rule is a loud decline — but it
   fails *uniformly*, so the first end-to-end run reports "no model" for
   everything (§8.4). Measured before the fix, on that fixture: `untranslated:
   2 declarations`, `ind-spec(Tree: no nested model in the export)`.

   **The difference is the key and not the spelling**, and the authority for
   that is the producer's own `Naming.lean` rather than this fixture.
   `modelName n = n._model` (`:77`) is one total function on the exact
   declaration being modelled, applied to the type former, each constructor and
   each recursor alike; ours makes `_model` a namespace under the type former
   and names every leaf by a role word plus a position. An index survives on
   the tool's side in exactly the places where the modelled thing has no
   declaration of its own — `R._model.iota_j` (`:82`), the projections, and the
   metadata theorems.

   Two structural differences ride along and are improvements rather than
   translations. **A constructor is keyed by its own name** (`Tree.leaf._model`),
   not by an index into the block, so the recogniser stops depending on
   constructor order; and **a rule is keyed off the recursor**
   (`R._model.iota_j`), not off the triple `(T, k, j)`. `model_of`'s `ModelKey`
   and `model_iota`'s `(ModelKey, Name)` both survive that; what changes is the
   name-building functions and nothing downstream of them. *That last clause was
   right about the tables and wrong about the total cost: `modelgen/` is still
   what makes `init-prelude` accept and is not this arc's to change, so the
   recogniser reads **both** schemes —* `nested_splice::Scheme` *— deciding on
   the carrier and then reading the whole tower in one scheme. The legacy arm
   retires with `modelgen/`.*
2. **Projections.** `T._model.proj_i` and `T._model.proj_i.iota` are new slots
   with no counterpart in our table. `Naming.lean:93-97` is the contract and
   says why they are the one family indexed off the *type former*: a projection
   "does not model a source constant", so there is no name to suffix, and `i` is
   the field's position in the unique constructor's telescope rather than a
   constructor index. Today a projection out of a structure is
   *constructed* by `proj_data.rs` / `proj_prop.rs`; under the pivot it should be
   *recognised*, which is a fifth family beside carrier / ctor / rec / ι.
3. **The optional metadata theorems.** The tool "may additionally emit exact
   structure-eta, unit-like, and recursor-rule-K theorems when the exported kernel
   metadata calls for them" (README); their names are `T._model.eta`,
   `T._model.unitlike` and `R._model.ruleK` (`Naming.lean:85-107`), and the
   `ruleK` slot is one this document's earlier name table omitted. Those
   correspond to `fun_eta.rs`,
   `unit_like.rs` and the K-rule handling. **Whether they subsume the clauses we
   carry is not established** — see §8.

`eq_cash.rs` (889 lines) and `iota_model.rs` (346) are the machinery that turns a
model's ι *theorem* into a firing reduction rule inside mini's `whnf`. Both are
already keyed off `model_iota` rather than off nesting, and both grow rather than
change.

### 4.3 What step 2 costs, measured

*Added 2026-08-15 from the same modelled `init-prelude` §6 is now corrected
against. Step 2 is §4.1's "drop the `nested::plan` gate and make the second gate
total". Nothing below is an estimate.*

**The good news first: the second gate needs no `zoneb.rs` change.**
`zoneb.rs:248`'s `nested_seen` is *membership in `app.nested`*, and `app.nested`
is filled by `nested_splice`. Populating it for every non-basis inductive makes
`ensure` route them all to `model_alias`, which already declines by name when
there is no entry. The basis exemption also belongs on the `nested_splice` side,
because `Eq` and `Nat` reach `direct::build` from *inside* `build` — i.e. after
the gate — so putting them in `app.nested` would hijack them. `Quot` is handled
at `zoneb.rs:193`, before the gate, and is safe either way. **Two string
literals in `zoneb.rs` would still be wrong for a non-nested declaration:
`"nested model not keyed here"` (`:315`) and `"nested model not interpreted"`
(`:319`), and `Missing::label`'s seven strings on our side say "nested" too.**

**Item 1 — the type former and constructors are keyed at `σ = []` only.**
**Landed 2026-08-15 at `8dba64c`, and doing it uncovered item 1b.**
`Model::mono`'s own doc calls this a limitation and says why it has never
mattered: "every nested fixture mini has is monomorphic". Step 2 ends that
immediately. Of `init-prelude`'s **126 inductive type formers, 88 are
universe-polymorphic**, and `zoneb::model_alias` looks up
`model_of[(T, σ)]` at the constant's own σ — so every one of the 88 misses and
reports `nested model not keyed here`. The fix is to key them the way recursors
already are, from `schedule ∪ applied`; it is perhaps fifteen lines and it is
entirely inside `nested_splice.rs`.

*Done — `Recogniser::decl_sigmas`. Measured on the producer's
`poly_nested_used`, where `PTree.{u}` is used at three universes:
`ind-spec(PTree: nested model not keyed here)` **3 → 0**, `untranslated`
17 → 15. Nothing moved on `init-prelude`, and that was measured rather than
assumed — its only nested declaration, `Lean.Syntax`, binds no level
parameters, so with the first gate closed the 88 are unreachable. Every nested
fixture this repository had was universe-monomorphic (`PT (α : Type)` is
parameterised, which is a different thing), so no existing test could have
caught the defect; `checker/tests/fixtures/tool_poly_nested.ndjson` is the
producer's fixture reduced to one model family and is now the pin.*

**Item 1b — propagating σ is necessary and not sufficient.** Found by doing
item 1, and it **refutes a written claim** in `nested_splice.rs`'s header,
which said the seeding trap was unreachable because "a σ added here can only be
one the export constant was already going to be interpreted at". That holds
only up to `DEFAULT_LEVELS`, which is `&[0, 1]`
(`checker/src/instantiations.rs:148`). **Nothing mentions a model constant** —
the same fact the header's mention-graph section turns on — so the model tower
is scheduled at `[0]` and `[1]` and nowhere else, while the export constant is
scheduled at every σ the file genuinely uses. Dumped on `tool_poly_nested`:
`⟦PTree._model.{0}⟧` and `⟦PTree._model.{1}⟧` are interpreted,
`⟦PTree._model.{2}⟧` is not, and neither is the `_impl.0` / `_auxCarrier` /
`_auxTag` chain beneath it.

So the keying defect is closed and `ind-spec(PTree: nested model not
interpreted)` at the one σ past `DEFAULT_LEVELS` is what remains. The demand
**closure** is taken by the pre-pass before the recogniser runs and is not
re-taken over the σ the recogniser adds. Closing it is
`checker::instantiations`' business rather than `nested_splice.rs`'s, so it is
reported rather than edited. **It bites every polymorphic declaration used
above `Sort 1`**, which at step 2 is a population and not a curiosity.

**Item 2 — the projection family is not optional, and it is the bulk of the
work.** This is the finding that decides step 2's size. Counted over the tool's
`init-prelude` output, the **1 044 public model declarations** are:

| family | count | do we read it? |
| --- | ---: | --- |
| `X._model` — carrier, constructors, recursors | 453 | **yes** |
| `R._model.iota_j` | 174 | **yes** |
| `T._model.proj_i` | 153 | no slot |
| `T._model.proj_i.iota` | 153 | no slot |
| `T._model.eta` | 104 | no slot |
| `R._model.ruleK` | 4 | no slot |
| `T._model.unitlike` | 3 | no slot |
| (`T._model._impl.*`, not API) | 100 | n/a |

**417 of 1 044 — 40% of the public model surface — is families we have no table
for**, against §4.2(2)'s "a fifth family beside carrier / ctor / rec / ι".

And they are load-bearing rather than decorative, because `model_alias`
publishes strictly less than `build` does. `model_alias` writes one
`Interp::consts` entry (`zoneb.rs:321`); the projection route reads
`IndApparatus::decls[(T, σ)] : Translated`, which is inserted in exactly one
place, `zoneb::build` at `zoneb.rs:1029-1048`. Everything else the route needs
is *derived from* that value and takes it as an argument —
`IndApparatus::decl_proj` (`interp.rs:1430`) builds `DeclProj::typed[j]` and
`DeclProj::eta` from a `&Translated`, and `decl_fields` likewise. So a structure
that takes the model route has:

* `proj_data::typing` (`proj_data.rs:421`) and `proj_prop::typing`
  (`proj_prop.rs:139`) returning `Gap::StructProj(T)` — the projection gets **no
  interpretation and no certificate**;
* `whnf_conv`'s proj-of-ctor ι (`kernel.rs:2071`) dropping its certificate;
* structure-η in `def_eq` (`kernel.rs:4866`) dropping its certificate.

**`init-prelude` has 107 single-constructor inductives out of 126 — 85%** — so
this is the common case and not an edge. Those three tool families
(`proj_i`, `proj_i.iota`, `eta`) are precisely the replacements for
`DeclProj::typed[j]`, `decl_proj::computes` and `DeclProj::eta`.

**And it fails soft, which is the part to be careful about.** `kernel.rs:4860`
records that the structure-η *probe* decides acceptance and the certificate is
separate, and `proj_data::iota` returning a gap leaves `whnf` reducing with
`cur_tm = None`. So a step 2 that stops at carrier / ctor / rec / ι **still
accepts every file** and merely stops certifying the projections — the type
former reads green while the family is red, which §8.2 already names as the
failure mode this project pays for most. The `nested`/adoption row does not
catch it either; a projection census would.

**Order of work, therefore:** (1) σ-key `Model::mono`; (2) grow the
`proj_i` / `proj_i.iota` / `eta` families and their consumers; (3) only then
open the first gate. Doing (3) first produces a green run that has quietly
stopped certifying 85% of the file's structures.

## 5. The retirement, in lines

`checker/src/mini/*.rs` is **55 255 lines** across 60 files. Of the 32 358 lines
in the 38 files this pivot touches:

| bucket | lines | files |
| --- | ---: | --- |
| **retires** — construction of non-basis inductives | **20 137** | `zoneb.rs` 5875, `rec_dep.rs` 2757, `ctor_ix.rs` 1443, `mutual_aux.rs` 1258, `class_p_ix.rs` 1028, `minor_ix.rs` 895, `rec_prop.rs` 876, `iota_dep.rs` 839, `recursor.rs` 737, `iota_ix_dep.rs` 670, `rec_ix_dep.rs` 645, `class_s.rs` 616, `rec_trunc.rs` 614, `class_s_ix.rs` 536, `rec_ix_prop.rs` 490, `rec_s_ix.rs` 489, `rec_trunc_ix.rs` 369 |
| **retires** — the `Acc` family, because `Acc` left the basis | **3 519** | `rec_acc_iota.rs` 970, `rec_acc_value.rs` 732, `rec_acc.rs` 692, `rec_acc_ih.rs` 471, `acc.rs` 432, `rec_acc_ap.rs` 222 |
| **stays** — basis clauses | **3 582** | `quot_classes.rs` 833, `direct.rs` 941, `nat_clause.rs` 399, `rec_nat.rs` 405, `iota_nat.rs` 242, `quot.rs` 569, `quot_iota.rs` 193 |
| **stays** — recognition, and grows | **2 388** | `nested_splice.rs` 926, `eq_cash.rs` 889, `iota_model.rs` 346, `modelgen.rs` 227 |
| **stays** — the basis slice of the general machinery (§3.5) | **2 101** | `proj_prop.rs` 1006, `proj_data.rs` 962, `unit_like.rs` 133 |
| **stays** — zone-A nested acceptance | **631** | `nested.rs` |
| | **32 358** | |

**23 656 lines retire**, and the brief's ~25 500 was close and slightly high. Two
honest qualifications on that number, both in the same direction:

* `nested.rs` (631) does not retire — §5.2.
* **`zoneb.rs` is counted as retiring in full and it does not.** §3.5 keeps the
  non-recursive class-(T)/class-(S) build alive to serve `PUnit` and `PSigma'`,
  and that lives inside `zoneb.rs`'s 5 875 lines at a boundary nobody has drawn.
  Until it is drawn, **23 656 is an upper bound**, not a measurement.

Roughly 4 700 of the retiring lines are `#[cfg(test)]` blocks — 1 997 in
`zoneb.rs` alone — so the executable surface removed is nearer 19 000.

### 5.1 Two files do not delete wholesale, and `direct.rs` is not one bucket

`direct.rs` (941) is **mostly basis and stays**, but not entirely:

* `clause_for` (`:252-263`) matches exactly `"Eq" | "Acc" | "Nat"`. The `Acc` row
  goes with the `Acc` family; `Eq` and `Nat` stay; `PUnit` and `PSigma'` are added
  under §3.5(a).
* `direct::build` (`:265+`) is a **shared walk** — "the shape of the walk is
  `zoneb::build`'s … what differs is only the bottom of each nest" — so it is
  basis infrastructure, not a per-type clause, and it survives all four rows.
* The `Acc`-specific arms are five sites (`:229`, `:404`, `:537`, `:606-611`),
  perhaps 40 lines.

`recursor.rs` (737) is counted as retiring, but **`eq_rec` and `eq_bottom` at
`:399-549` are `Eq`'s entire interpretation clause** and must be extracted into
the basis before the file goes. Likewise `zoneb.rs` (5 875) retires, but its first
statements are dispatch that must be lifted out first: `:193-194` routes `Quot` to
`quot::build`, `:843-845` routes `Eq`/`Nat` to `direct::build`, and `:248-252`
routes a recognised model to `model_alias`. Call it ~200 lines to extract before
~23 650 delete.

### 5.2 What remains inductive-shaped after the pivot

The pivot removes the *certified construction* of inductives. It does not remove
inductives.

* **The export still declares `T`.** The tool "adds an ordinary-declaration model
  of each supported inductive **while retaining the original declaration**"
  (README). Under `Mode::Split` a `Declaration::Inductive` still routes to
  `Pick::Mini`, and `kernel::add` (`kernel.rs:5453`) still calls
  `add_maybe_nested` — mini's *syntactic* acceptance: positivity, constructor
  typing, recursor generation, ι rules. **None of that retires.** What retires is
  the *interpretation* half, zone B. The original declaration becomes the key
  under which the model's interpretation is published, exactly as
  `model_alias` already does it.
* **`nested.rs` (631) therefore stays.** It is the zone-A specialise / check /
  restore that makes `kernel::add` accept a nested inductive at all, called from
  `kernel.rs:5550`, and it is independent of whether zone B builds a carrier.
* **The basis five must still be declared.** `Eq`, `Nat`, `PUnit`, `PSigma'` are
  ordinary inductives that route to mini and are accepted there; `Quot` is not an
  inductive at all and takes `add_quot` (`kernel.rs:5450`) and the four-entry
  route anchor `routed.rs:97`. The external tool splices any basis member the
  input lacks, so their *presence* is guaranteed; their *interpretation* is ours.
* **`nanoda`'s own `checker/src/inductive.rs` is untouched** by this. Under
  `Mode::Split` it does not see inductives at all; it is exercised by
  `--naive`-adjacent paths and by `check_declar_scheduled`'s `Inductive` arm when
  a run is not routed.

### 5.3 The fourth bucket: `mini::kernel::Checker`, demoted

The owner's endgame statement:

> After the pivot, we don't have much inductive handling left, only fixed clauses
> and the recognizers. Then all that is materially left from mini is a certifying
> type checker that is working but **naive and not usable in practice**. So we'll
> drag it along for inspiration and maybe comparison on simple input, but **it
> will not play a role in practice.**

That is a fourth bucket beside retires / basis / recognition: **stays but
demoted.** It is `checker/src/mini/kernel.rs` (6 876 lines) and the conversion
machinery around it — `conv.rs`, `ev.rs`, and the `Checker` half of `interp.rs`.
Not deleted, not production.

**§1 is what makes this coherent, and bucket 4 makes §1 more important rather than
less.** If any model declaration were still checked by mini's `Checker` after the
pivot, production would depend on a component the owner has just designated
non-production. §1 shows it is not: under `Mode::Split` every `def` and `theorem`
— which is every model declaration — goes to nanoda, and `Driver::evidence`
returns `false` on that arm so mini's evidence walk does not run on them either.
Mini's `Checker` remains reachable in production for exactly two things: accepting
inductive declarations (`kernel::add` → `add_maybe_nested`, §5.2) and firing a
model's ι rule inside `whnf_conv` (§7). Neither is "checking a model".

**Where the label belongs.** A checker that is "working but not usable in
practice" and still compiled into the binary is precisely what a future reader
mistakes for a live path, and this project has a long record of that failure —
`SEAM-DESIGN.md:579-598`'s three heads for one constant, and `fire_list` being
structurally dead code that nobody had deleted, are the same mistake twice. The
label should go in three places, in decreasing order of importance:

1. **`checker/src/mini/kernel.rs`'s module header**, as the first thing in it:
   what the `Checker` is, that it is not the production type checker, what still
   *does* reach it (inductive acceptance and ι firing), and what does not (any
   `def`, `theorem`, `opaque` or `axiom`). A header that says only "certifying
   type checker" will be read as a live path.
2. **`route.rs`'s `Mode` doc**, which today explains the split as a performance
   argument ("the measured escape from the matcher wall"). After the pivot the
   split is also a *policy* statement about which engine is production, and the
   doc should say so, because a future reader tempted to route a `def` to mini
   for some local reason needs to meet that sentence.
3. **`MINI-DESIGN.md` §0**, which frames mini as one of two axes.

**Should anything stop it being reachable?** No new mechanism is needed, and
adding one would be the wrong shape: `Mode::pick` is already the single policy
function — `route.rs:110-113` says in terms that "there is no second place a
routing decision is made" — so the reachability question is already answered by
one `match`. What is worth adding is a *test* that pins it: a run over a fixture
carrying a model, asserting that no `_model` declaration was dispatched to
`Pick::Mini`. That converts the guarantee from a reading of `Mode::pick` into
something that fails when someone changes it.

### 5.4 `--naive` cannot survive the pivot in its current meaning

`--naive` today selects `Driver::Plain` (`route.rs:270-273`,
`checker/src/bin/checker.rs:176`), the historical whole-file mini run: mini
accepts *and* certifies every declaration, inductives included, via
`kernel::add`. `CLAUDE-HANDOFF.md` records it as the only way to run that policy.

**After the pivot that policy no longer exists**, and the reason is bucket 1, not
bucket 4: `Driver::Plain`'s inductive half is `zoneb` and the `rec_*`/`iota_*`
families — the 23 656 lines that are being deleted. A `--naive` run over any file
with a non-basis inductive would decline on every one of them. So `--naive` does
not survive as "mini does everything"; it survives, if at all, as something
narrower.

**What the owner actually asked for — "comparison on simple input" — is narrower
than `--naive` and is better served by a different flag.** The comparison that
still means something after the pivot is: *for a declaration both engines can
take, do they agree?* That population is the `def`s, `theorem`s, `opaque`s and
axioms — precisely `Mode::Split`'s `Pick::Checker` set — plus the basis
inductives. So the useful mode is **the split policy with the ordinary-declaration
side flipped to mini**, not the whole-file walk. That is a second `Mode` variant,
which `route.rs:87-95` already anticipates: its `DeclKind` enum tells the
`DefKind`s apart explicitly "because a future policy may want to split them, not
because today's does."

**Recommendation: retire `--naive` with the construction code and introduce
`Mode::MiniDefs` (or similar) in its place**, so that the demoted checker keeps
exactly one entry point, that entry point is a routing mode rather than a separate
driver, and the differential oracle keeps working on the population where both
engines are still defined. Keeping `Driver::Plain` as a second driver beside the
routed one, after its inductive half is gone, would leave a mode that silently
declines most real files — the "names where a value stopped rather than why"
failure this project pays for most.

## 6. The 91 untranslated declarations

`init-prelude` currently reports, with `--verbose --mutual --nested`
(`CLAUDE-HANDOFF.md:142-151`):

```
accept  1822 declarations
untranslated: 91 declarations, 10 eliminators
uncertified:  32 const typings, 29 type typings
tg gaps: 11909      prefix declarations=152 pairs=32      exit 4
```

in two families: **`type former spine`** — the heterogeneous-operator classes
(`HAdd`, `HSub`, `HMul`, `HPow`, `HAnd`, `HOr`, `HXor`, `HShiftLeft/Right`,
`HAppend`, `HAndThen`, `HOrElse`, `HDiv`, `HMod`, `HSMul`), the `Monad*` classes,
`Membership`, `EStateM.Backtrackable`, `Trans` — and **`field type
uninterpretable`** — the machine words `UInt8/16/32/64`, `USize`, plus `Char`,
`String`, `Fin`, `BitVec`, `ByteArray`, `Substring.Raw`, `Hashable` and the
`Lean.*` syntax types. The 10 eliminators are `False` and `PEmpty` (class-(S)
eliminator, no constructors) and `HEq` (a result index is not a bare field).

**Every one of those refusals is minted inside code that retires.** The four sites:

| site | reason |
| --- | --- |
| `zoneb.rs:3625` | `type former spine` — `ip.beta_spine` could not decompose the stored type |
| `class_s.rs:440` | `type former spine`, class-(S) arm |
| `direct.rs:553`, `recursor.rs:498` | `type former spine` on the `Eq` clause |
| `zoneb.rs:2268` | `field type uninterpretable` — the field's inferred typing carries no interpretation term |

All four are reached from `zoneb::build`, and `zoneb::ensure` returns at the model
route (`:248-252`) **before** `build` is ever called. So under the owner's rule
these declarations no longer produce *our* refusals at all: they either arrive
with a model and work, or they arrive without one and we complain that the model
is missing. **The category `type former spine` / `field type uninterpretable`
disappears as a category.** That is the largest single consequence of the pivot
and the brief was right to flag that nobody had considered it.

What replaces it is *the producer's* decline ledger rather than ours, so whether
that is a net win depends entirely on the producer's coverage. **This tranche
measured it, and the answer is that the coverage is total.**

`lean-inductive-models` was built from `vendor/` in a scratch copy and run over
the same export:

```console
$ lean-inductive-models --no-output --no-type-check-output \
      vendor/arena-tests/good/init-prelude.ndjson
…
Nat:   exempt — prim model: a basis primitive
Eq:    exempt — prim model: a basis primitive
PUnit: exempt — prim model: a basis primitive
statements: 658 compared, 0 differ
levels: 3 planner comparisons, 0 escapes
output check: 144 model families checked
EXIT=0
```

**144 model families, 0 declines, 3 exempt.** Exit 0; exit 2 is the tool's code
for "a requested generation route declined an unsupported owner" and it did not
fire. And the models are exactly the declarations we refuse:

| our refusal | the tool's verdict |
| --- | --- |
| `field type uninterpretable` — `UInt8/16/32/64`, `USize` | `model of 7 declarations` each |
| — `Char`, `String`, `Fin` | `model of 9 declarations` each |
| — `BitVec`, `ByteArray`, `Hashable` | `model of 7` each |
| — `Lean.Name`, `Lean.Syntax` | `model of 8`, `model of 26` |
| `type former spine` — `HAdd`, `HSub`, `HMul`, `HDiv`, `HMod`, `HPow`, `HAppend`, `Membership`, `Trans`, the `Monad*` classes | `model of 7 declarations` each |
| the 10 **eliminator** declines — `False`, `PEmpty` (no constructors), `HEq` (result index not a bare field) | `model of 2`, `model of 2`, `model of 5` |

**So the 91 untranslated declarations and the 10 untranslated eliminators go, all
of them.** That is the largest single consequence of the pivot, it was
unconsidered before this tranche, and it is now measured rather than inferred.

#### The claim is **conditional on §4.1's step 2, and this section did not say so**

*Corrected in place 2026-08-15, by running it. The modelling side of §6 above is
confirmed exactly — 144 families, 0 declines, exit 0, and now also `output
kernel check: accepted`. What was wrong is the sentence directly above.*

`lean-inductive-models` was run over `init-prelude` **with output**, and our
checker run over the result — `checker --verbose --mutual --nested
--no-modelgen`, the pivot's production path, at `236ba86`:*

```
init-prelude-lim.ndjson  accept 3123 declarations
                         untranslated: 109 declarations, 17 eliminators
prefix declarations=171  pairs=32  certified=0
nested  seen=1  models=1  tool=1  legacy=0
route   mode=Split  toMini=149  toChecker=2974  unclaimed=0
```

**The count went from 91/10 to 109/17. It did not go to 0.** Every name §6
lists is still refused, by the same reason string: all fourteen `H*` classes,
every `Monad*`, `Membership`, `Trans`, `EStateM.Backtrackable`, the machine
words, `Char`, `String`, `Fin`, `BitVec`, `ByteArray`, `Hashable`, `Lean.Name`,
`Lean.Syntax`, and the `False` / `PEmpty` / `HEq` eliminators. By reason: 60
`type former spine`, 30 `field type uninterpretable`, 4 `parameter type
uninterpretable`, over 62 distinct declarations.

**Why, and it is not a defect in the tool.** §6's mechanism is right —
`zoneb::ensure` does return at the model route before `build`, so a declaration
that reaches `model_alias` never mints these reasons. But it reaches
`model_alias` only if it is in `app.nested`, and `app.nested` is filled only for
declarations `nested::plan` calls nested (§4.1's *first* gate). `HAdd` is not
nested. So it still goes to `build`, and `build` still refuses it — **with a
model sitting unread three declarations earlier in the same file.**

**§6 is therefore a consequence of step 2 and not of the pivot**, and it should
be read as the payoff for opening the first gate rather than as something the
models deliver on arrival. Its own §5 evidence is intact; only the tense was
wrong.

Three further things the same run establishes, none of them previously measured:

* **`--no-modelgen` no longer declines on `Lean.Syntax`.** `CLAUDE-HANDOFF.md`
  records that it stops there at declaration 1; the tool splices the nested
  model and our recogniser reads it — `nested seen=1 models=1 tool=1 legacy=0`,
  which is §8.4's rename working on a real export rather than a fixture.
* **§8.3's `Acc` cost is now a number.** `_wcore.Acc: recursive argument
  telescope depth` = 3 and `_wcore.WellFounded: field type uninterpretable` = 3.
  The `Classical.choice`-bearing `_wcore.*` prelude arrives as predicted and
  its `Acc` is *not* translatable by the machinery that survives.
* **§8.2's `PSigma'` red is the single largest untranslated family in the run** —
  `ind-spec(PSigma': class (P) above Prop)` = 11 pairs, because the tool splices
  `PSigma'` into every export that lacks it. It is not a fixture curiosity.

`route mode=Split toMini=149 toChecker=2974` confirms §1 at scale: 95% of the
declarations go to nanoda.

Two details from the same run worth carrying:

* **`PSigma'` is spliced, not assumed.** `init-prelude` declares no `PSigma'`, and
  the tool emits it — `LT: prelude spliced — PSigma', PSigma'.rec, PSigma'.mk,
  PSigma'.fst, PSigma'.snd, PSigma'.rec', PSigma'.fst_mk, PSigma'.snd_mk,
  PSigma'.rec'_mk`. That is the whole family §3.4 describes: the primitive
  inductive and its constructor, then projections, the large eliminator `rec'` and
  the three computation rules, all as ordinary declarations.
* **`Acc` models, confirming §3.1.** `_wcore.Acc: prelude spliced —
  _wcore.Acc._model._impl.funext`. `Lean.Syntax` reaches it through a `_wcore.*`
  prelude of some 250 declarations including `WellFounded`, `Classical.choice`
  and `Quot.sound` — which is the concrete shape of the cost §8.3 raises.

The predecessor's numbers point the same way and are now corroboration rather
than the argument: `MODELGEN.md:2569-2591` records `--prim-models` modelling
**122 of `init-prelude`'s 125 simple inductives**, and `MODELGEN.md:6930` records
**6 882 closed, 0 declined, 3 exempt** on full Mathlib with 18 511 statements
compared at 0 differing and 6 796 recursors at 0 differing.

### 6.1 The same measurement at Mathlib scale — 6 882 families, 0 declines

*Measured 2026-08-15 on branch `joachim/model-scale` at master `5813df2`. This
retires §8.1, which said the tool "has not been run over Mathlib". Nothing in
`checker/`, `derived/` or `kernel/` was touched; this document is the only
change on the branch.*

**The pivot survives Mathlib.** The external tool was run over the full 5.6 GB
export and over five size-graded prefixes of it. **At every size the decline
count is zero**, and at full scale the tool reports

```console
$ lean-inductive-models mathlib.ndjson --no-output
… 6 882 "X: model of N declarations" lines and 85 "prelude spliced" lines elided …
Nat:   exempt — prim model: a basis primitive
PUnit: exempt — prim model: a basis primitive
Eq:    exempt — prim model: a basis primitive
statements: 48677 compared, 0 differ
levels: 203 planner comparisons, 0 escapes
output check: 6882 model families checked
output kernel check: accepted
EXIT=0
```

**6 882 model families, 0 declines, 3 exempt** — and the exempt set is exactly
`{Eq, Nat, PUnit}`, which is what `scripts/check-mathlib-result.sh` pins. There
is **no systematic decline class and there are no one-off declines either**:
`grep -c ': declined'` is `0` on **all twelve runs across the six input sizes**
(a streaming pass at each size, a named-output pass at five, and the serialized
re-read), so the decline grouping this tranche was asked to produce is empty.

**6 882 is the predecessor's number exactly.** `MODELGEN.md:6930` records
`6 882 closed, 0 declined, 3 exempt` for the retired modelgen on full Mathlib.
A different program, over a changed basis (`PULiftP` → `PUnit`,
`PSigma` → `PSigma'`, `Acc` out), lands on an identical population count. §8.1
was right that a changed basis is a changed coverage argument and the number was
not transferable *a priori* — but it transferred. What did **not** transfer is
the amount of checking behind it: this tool compares **48 677** statements where
modelgen compared 18 511, a 2.6× larger correspondence check over the same
families.

#### The ladder

| input | bytes | lines | decls | inds | families | **declined** | exempt | statements | differ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `init-prelude` | 3.7 MB | — | 1 822 | — | 144 | **0** | 3 | 658 | 0 |
| `m1-A` | 50 MB | 952 385 | 12 035 | 507 | 529 | **0** | 2 | 3 546 | 0 |
| `m3000000-A` | 157 MB | 2 897 273 | 28 644 | 1 039 | 1 089 | **0** | 2 | 7 499 | 0 |
| `m10000000-A` | 508 MB | 9 343 370 | 75 851 | 2 065 | 2 141 | **0** | 2 | 14 161 | 0 |
| `m20000000-A` | 1.03 GB | 18 643 079 | 135 781 | 3 606 | 3 769 | **0** | 2 | 26 788 | 0 |
| **`mathlib`** | **5.64 GB** | **100 001 405** | **654 504** | **6 644** | **6 882** | **0** | **3** | **48 677** | **0** |

The `mN-A` files are line prefixes of the same export truncated to a declaration
boundary (`m30000000-A` is exactly 30 000 000 lines), so each is closed under
dependencies and is a valid standalone input. The prefixes exempt only `Nat` and
`Eq` because they do not themselves declare `PUnit` — the tool splices it, which
is the correct behaviour and not a coverage gap.

Families exceed inductives (6 882 against 6 644) because splicing adds families:
85 splice events at full scale, the large one being a `_wcore.*` well-founded
prelude reached through `Acc`, exactly as §6 saw at `init-prelude` scale.

#### Fidelity — the tool's own three checks, all green at 5.6 GB

The tool makes three independent checks and all three pass on the full export:

| check | what it is | verdict at 5.6 GB |
| --- | --- | --- |
| per-declaration kernel replay | every generated declaration kernel-checked before emission, in an owner-free environment (mandatory, cannot be disabled) | no rejection reported |
| `statements: N compared, M differ` | generated statements against the exact exported owner interface after renaming | **48 677 compared, 0 differ** |
| `output check: N model families checked` | the structural correspondence checker over the final stream | **6 882 families** |
| `output kernel check: accepted` | whole-stream kernel replay of the transformed export | **accepted** |
| `input check` on the written bytes | re-read the 5.94 GB actually serialized, structurally | **6 882 families, 0 violations** |
| `input kernel check` on the written bytes | replay every declaration of the written file through Lean's kernel | **accepted** |

Note the `init-prelude` run in §6 was taken with `--no-type-check-output`, so it
never exercised the whole-stream kernel gate. **These runs leave it on**, which
makes them a strictly stronger result than §6's, not merely a larger one.

The last two rows are a separate 20 m 35 s pass (14.79 T `instructions:u`,
8 390 MiB RSS) over the bytes on disk rather than over an in-memory structure, so
**the serialization round-trip is checked and not assumed** — this is the leg
`ci-mathlib.sh` calls the authoritative kernel verdict.

**An independent oracle agrees.** The tool's own
`scripts/check-mathlib-result.sh` was run unmodified against these three
artifacts and passes, exit 0:

```console
mathlib result: generation, exact interfaces, levels, basis, and kernel reread pass
```

That script independently asserts what this section claims — a positive,
single-valued statement comparison at 0 differing, a nonzero output family
count, the full-AST backend, nonzero level planning at 0 escapes, the basis
exemption set being **exactly** `{Eq, Nat, PUnit}`, ordinary `PSigma` modelled
like any other source inductive, `PSigma'` spliced and present as an exact name
in the serialized bytes, **no surviving `PULiftP`** anywhere in either log or
the output, and the serialized re-read accepted by the kernel.

#### Cost — linear, and `m20` is a content anomaly rather than a scaling law

*All memory below is MiB/GiB — `Maximum resident set size` from GNU `time -v`,
which reports KiB, divided by 1024.*

| input | wall | `task-clock` | `instructions:u` | peak RSS | instr/line |
| --- | ---: | ---: | ---: | ---: | ---: |
| `init-prelude` | 2.79 s | 2.7 s | 0.029 T | 132 MiB | — |
| `m1-A` | 29.8 s | 29.7 s | 0.333 T | 292 MiB | 350 K |
| `m3000000-A` | 82.6 s | 82.5 s | 0.869 T | 542 MiB | 300 K |
| `m10000000-A` | 4 m 03 s | 242.5 s | 2.469 T | 1 276 MiB | 264 K |
| `m20000000-A` | 14 m 34 s | 873.0 s | 7.689 T | 2 985 MiB | 412 K |
| **`mathlib`** (stream) | **53 m 04 s** | **3 181.9 s** | **27.27 T** | **10 881 MiB** | **273 K** |
| `mathlib` (gen, `-o`) | 14 m 56 s | 895.6 s | 9.44 T | 11 983 MiB | — |
| `mathlib` (serialized re-read) | 20 m 35 s | 1 234.0 s | 14.79 T | 8 390 MiB | — |

**Which number to trust.** `task-clock` and elapsed agree to within 0.1 % on
every row (3 181.9 s against 3 184.1 s at full scale), so the process is
single-threaded and was **not** contended by the other seat building
concurrently; `instructions:u` and wall therefore tell the same story here, and
wall is safe to quote. `instructions:u` is still the more portable figure and is
the one to compare against on a different box. **RSS is the number that decides
feasibility.** An independent 5-second sampler over the whole process tree — the
tool forks an internal worker, so `time -v` alone could have missed it — gives
**14.9 GiB** as an upper bound including the parse-phase peak and the `perf`
wrapper; the two agree to within 10 % on every prefix rung. **10.6–14.9 GiB is
the honest range for a 5.6 GB input**, and the three legs together never exceed
it.

**Cost is linear in the export.** Full Mathlib runs at 273 K instructions per
line, sitting between `m3` (300 K) and `m10` (264 K). The `m20` rung reads 412 K
and briefly suggested a superlinear regime — instructions per declaration nearly
doubled there — but the full run refutes that: **`m20` is a local content
anomaly, not a scaling law.** A linear-in-declarations fit taken from `m1` and
`m3` alone predicted `m10` at 1 253 MiB (actual 1 276) and full Mathlib at
9 962 MiB (actual 10 881, 8 % low). This is why the ladder was walked to the top
rather than extrapolated from it: **the extrapolation from `m20` alone would
have predicted 78 minutes and been wrong by 25 minutes in the pessimistic
direction**, and a seat that stopped at 508 MB would have reported a clean
linear law it had not earned.

The tool's own `scripts/ci-mathlib.sh` caps the generation worker at a 10 GiB
`RLIMIT_AS` and the full export fits, which corroborates the measured 11–12 GB
against a second source.

#### The output's size — 1.05× in bytes, 1.11× in declarations

A model retains the original declaration and adds to it, so the export grows.
**Measured, with `-o OUT --no-type-check-output`, the same invocation
`ci-mathlib.sh` uses** (`output backend: legacy`, the full-AST path):

| input | bytes in | bytes out | **factor** | added |
| --- | ---: | ---: | ---: | ---: |
| `m1-A` | 50.9 MB | 76.7 MB | 1.508 | +25.8 MB |
| `m3000000-A` | 157.0 MB | 205.1 MB | 1.306 | +48.1 MB |
| `m10000000-A` | 508.3 MB | 601.1 MB | 1.183 | +92.9 MB |
| `m20000000-A` | 1 031.3 MB | 1 233.9 MB | 1.197 | +202.6 MB |
| **`mathlib`** | **5 636.3 MB** | **5 943.2 MB** | **1.0545** | **+306.9 MB** |

**5.6 GB in, 5.9 GB out.** The factor falls with scale because models are
proportional to *inductives* while the export is dominated by theorems, and
inductive density drops sharply — 5.3 × 10⁻⁴ inductives per line in the prelude
against 6.6 × 10⁻⁵ across Mathlib. The early rungs' 1.5× is prelude-shaped and
is not the number to plan against; **1.05× is.**

Declarations are the constraint that actually matters downstream, and they grow
faster than bytes because the added declarations are small:

| input | decls in | decls out | factor | added | added per family |
| --- | ---: | ---: | ---: | ---: | ---: |
| `m1-A` | 12 035 | 17 431 | 1.448 | +5 396 | 10.20 |
| `m3000000-A` | 28 644 | 40 138 | 1.401 | +11 494 | 10.55 |
| `m10000000-A` | 75 851 | 97 162 | 1.281 | +21 311 | 9.95 |
| `m20000000-A` | 135 781 | 176 192 | 1.298 | +40 411 | 10.72 |
| **`mathlib`** | **654 504** | **727 155** | **1.111** | **+72 651** | **10.56** |

**A model family costs about 10.4 declarations**, stable to ±5 % across two
orders of magnitude — and the rate measured on the prefixes predicted the full
run's added declarations to within 1 % (projected ~72 000, actual 72 651).
§8.6's estimate — "Mathlib's 6 882 inductives become on the order of 30 000
extra declarations to check" — is **low by a factor of 2.4**: the measured
figure is **72 651**, and that bullet is corrected where it stands.

**The added declarations are `def`s and `thm`s and essentially nothing else.**
Over the full export: **+41 566 `def`, +30 843 `thm`, +242 `inductive`** (the
spliced basis and `_wcore` members), and **no new axioms and no new opaques** —
the `axiom` count is 7 and the `opaque` count 3 082 in both input and output.
That is §1's load-bearing claim — "a model is a pile of `def`s and `theorem`s,
those route to nanoda" — confirmed against 72 651 real added declarations at
Mathlib scale rather than against `nested_keying.ndjson`'s 27. The output
carries **25 373** `_model` name-table entries against 0 in the input.

#### How these runs were established to be non-vacuous

"Skip is not pass", and exit 0 is specifically *not* sufficient here:
`Main.lean:114-125`'s `unsupportedDeclines` filters the decline list before it
reaches the exit code, so a run **can print `X: declined — …` and still exit 0**
when the decline is fulfilled elsewhere. Five checks were made instead of
trusting the code:

1. **A control that reproduces a known number.** `init-prelude` was run first
   and returned §6's `144 model families, 0 declines, 3 exempt, 658 statements
   compared / 0 differ` exactly.
2. **Decline lines are counted, not inferred from the exit code.**
   `grep -c ': declined'` is 0 on all six runs.
3. **The counts scale with the input.** Families track inductives (529 / 1 089 /
   2 141 / 3 769 / 6 882 against 507 / 1 039 / 2 065 / 3 606 / 6 644) and
   statements per family sit at 6.6–7.1 throughout. A run that modelled nothing
   would show a flat or zero count.
4. **The output was inspected independently of the report.** The full-scale
   output carries **25 373** `_model` name-table entries against **0** in its
   input and its declaration count rose 654 504 → 727 155; `m1-A`'s output
   likewise carries 1 757 against 0, holds `PSigma'` and no `PULiftP`.
5. **The tool's own verdict script.** `scripts/check-mathlib-result.sh` was run
   unmodified against the full-scale artifacts as an independent oracle and
   passes at exit 0. It fails closed on a vacuous run: it requires a *positive*
   statement count, a *positive* family count, and the exact basis exemption
   set, so a run that modelled nothing cannot pass it.

#### Method note

The tool was built from a scratch copy at `_tmp/lim`, never from `vendor/`;
`vendor/lean-inductive-models` is unmodified at `5a9a70f` with an empty
`git status`. `_tmp/` is project-local, on XFS, and gitignored — no large file
was written to `/tmp` or the scratchpad, both of which are tmpfs here. Every run
was capped with `ulimit -S -v`/`-H -v` in a subshell (10 GiB for the prefixes
through `m3`, 16 GiB for `m10`/`m20`, 24 GiB for the full export, raised
deliberately per rung rather than removed), and `user.slice` `anon` was sampled
every 5 s throughout; it peaked near 18 GB with another seat building
concurrently, against the ~50 GB session-kill threshold. Measurement used GNU
`time -v` and `perf stat -e instructions:u,task-clock`. Inputs are the exports
already on disk in the `mathlib-work` worktree, which was read and not written.

**This measures the *tool*, not the integration.** Our recogniser and the tool
still share no name (§4.2, §8.4), so nothing here says our checker consumes this
output — that remains the sequenced tranche it was.

## 7. What is *not* dissolved

* **`--naive`.** A mini-only run puts model `def`s and `theorem`s on mini's
  `def_eq`. The pivot's guarantee is a property of the default split, not of the
  binary.
* **Reduction still happens in mini.** A model's ι rule fires inside mini's
  `whnf_conv` (`kernel.rs:1474-1693` dispatches `iota_model::selects`), and
  `eq_cash` cashes the model's `Eq` theorem into a TG equation there. That is a
  single rewrite per redex rather than a normalisation, so it is not the failure
  mode §2 describes — but mini's `def_eq` is not eliminated from the picture, only
  removed from the *checking of model bodies*.
* **The identity guard's residue** (§2, last paragraph) is untouched.
* **The basis five are still constructed by us**, with mini's `def_eq` doing the
  work. They are five fixed declarations rather than an open population, which is
  the point, but "the checker constructs no inductives" would be false.

## 8. Risks and what is not established

### 8.1 The producer's coverage — retired as a risk, at Mathlib scale

*Rewritten 2026-08-15. This section previously read "The producer's coverage is
measured on `init-prelude` and nowhere else" and said the tool **had not been run
over Mathlib**. It has now, and the risk it named is closed — §6.1 carries the
measurement.*

**Retired.** `lean-inductive-models` at `5a9a70f` over the full 5.6 GB Mathlib
export gives **6 882 model families, 0 declines, 3 exempt, 48 677 statements
compared at 0 differing, whole-stream kernel replay accepted, exit 0** — and
zero declines at every rung of a six-point size ladder from 3.7 MB up. The
tool's decline rate *is* our decline rate under the owner's rule, and it is
zero on the corpus that matters.

The reasoning this section used to close on was sound and is worth keeping: the
tool exits **2** when "a requested generation route declined an unsupported
owner", and exit 2 never fired. But **exit 0 alone would not have been
sufficient evidence** — `Main.lean:114-125` filters fulfilled declines out
before the exit code is computed, so decline *lines* were counted directly.
They are absent. §6.1's non-vacuity paragraph records the other four checks.

One caution this section raised survives in amended form. It said the
predecessor's 6 882/0/3 "is not transferable — the basis changed". That was
correct as an argument and wrong as a prediction: the count came out identical,
6 882/0/3, across the basis change. The lesson is that the *population of
modellable Mathlib inductives* is robust to the basis change, not that the
prior number should have been assumed.

What remains open is **not** coverage but consumption: our recogniser shares no
name with the tool's output (§4.2, §8.4), so the recognition side is still
unmeasured above fixture scale (§8.6). §6.1 measures the producer only.

### 8.2 `PSigma'` is red at `σ = (1,1)`, and the fix is a classification, not a construction

*Rewritten 2026-08-15. This section previously named `TruncCarrier::in_un` as the
experiment to run first and predicted a new `derived/` construction behind it.
Both were wrong, and the second was worse than wrong — see the warning below.*

§3.3 and §3.6, measured. `PSigma'.{0,0}` translates today; `PSigma'.{1,1}`
declines. Neither `Σ ∈ U₀` nor "a Σ of subsingletons is a subsingleton" is on
the path: the first is **false** (§3.6) and the second was only ever wanted in
order to derive it.

**What remains is one decision in `checker/`.** `zoneb::large_eliminating`
(`zoneb.rs:1149`) deliberately reads the declaration's own level expression and
never σ's, and the comment above it names the design rule and the test that
pins it:

> **The declaration's own types, never σ's.** Reading the substituted ones would
> decide the class per instantiation, which is the design error
> `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3 closes … `zoneb::tests::
> a_possibly_prop_declaration_never_acquires_a_w_type` is that case.

`PSigma'`'s declared sort `max u v` is not `provably_nonzero` and its two data
fields fail the subsingleton test, so it is class (P) at every σ, and
`build_trunc` refuses any σ where `max u v` is a nonzero numeral. A basis clause
for `PSigma'` is exactly a licence to pick the carrier **per σ** — truncation at
rung 0, the data carrier at rung `n ≥ 1` — for one name-keyed, shape-verified
declaration, which is the policy the general rule must not have.

**Warning, and it is the reason this section was rewritten rather than
extended: do not build `TruncCarrier::in_un` in order to close `PSigma'`.** It
would make `PSigma'.{1,1}`'s *type former* go green with a carrier
`‖a‖ ⊆ {•}` — and the rest of the mandatory family cannot live on that carrier.
`PSigma'.rec'` (`vendor/lean-inductive-models/src/InductiveModels/Simple.lean:594`)
is an ordinary `def` with an **arbitrary `Sort w` motive**, `fun … => minor
self.1 self.2`, and `fst_mk`/`snd_mk`/`rec'_mk` are `Eq.refl`. On a subsingleton
carrier `⟦mk a b⟧ = ⟦mk c d⟧ = •`, so `fst_mk` would demand `⟦a⟧ = ⟦c⟧` for
every pair of inhabitants — at `α := Nat` that is `∅ = {∅}`, refutable. It
**fails closed** (the projections have no `DeclProj` structure-eta on a
truncated carrier, so they decline rather than certify), but the failure mode is
the one this project pays for most: the type former reads green while the family
is red, and a later seat scores it as progress. `in_un` remains the right and
promised fix for `Squash`/`MyBool` (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.5) —
which is a **different** tranche, and must not be merged with this one.

**Mixed σ is measured now, and it makes this section's fix cover more while
costing no more.** *(Added 2026-08-15. The paragraph here said the mixed
question was "genuinely unmeasured" and that the corpus schedules only `[0,0]`
and `[1,1]`. The second half was right and is the reason for the first: a
default is `vec![l; nparams]`, uniform by construction, so **no** value of
`DEFAULT_LEVELS` can produce a mixed σ and no amount of re-running the corpus
would have found one.)*

`checker/tests/fixtures/psigma_mixed_sigma.lean` demands all four σ of
`PSigma'` by name. `PSigma'.{0,1}` and `PSigma'.{1,0}` **decline**, with
`ind-spec(PSigma': class (P) above Prop)` — the same reason, the same site, as
`(1,1)`. So mixed σ is **not a second gap**: `PSigma'` is red at three σ and
green at one, and the single classification decision above closes all three.
That is a narrowing of the blocker, not a widening of it.

And the carrier those three should get is green today. The same fixture
declares `PSigma` (`Sort (max 1 u v)`) beside it, which is **the same
instantiated declaration** at every σ here — `max 0 1`, `max 1 0`, `max 1 0 1`
and `max 1 1 0` are all `1` — differing only in the level expression
`large_eliminating` reads. It derives at all four σ, mixed included: the general
data carrier takes one `Prop` component and one data component at rung 1 with
no complaint. `Cumul::lift(0,n)`, the lemma §8.6 predicted this case would
spend, is built (`derived/src/tower/cumulative.rs:180`), public through
`Interp::raise_in_gamma` and `Interp::cumul_lift`, and already in the path at
`zoneb.rs:2953`. **`derived/` is owed nothing by mixed σ.**

### 8.3 The `Acc` retirement is a real cost, not a saving

3 519 lines of `Acc` machinery retire, and everything that used `Acc` — every
well-founded recursion in Mathlib — must then arrive with a model produced by the
graph arm, whose ι rule is **not** `Eq.refl` and whose axiom bill includes
`Classical.choice`, plus `funext`/`Quot.sound` when a recursive field has binders
(`MODELGEN.md:3509-3527`). Our `Acc` clause is `thesis.txt:2126`'s own clause and
is cheap and exact. Trading it for a `Classical.choice`-bearing model on every
well-founded definition is a decision with a cost, and this document is where the
cost should be argued rather than absorbed. **It has not been argued anywhere.**

### 8.4 The naming scheme did not match — **closed 2026-08-15 at `236ba86`**

*Retired as a risk for the four families a nested declaration needs. The
account below is kept because the diagnosis was right and the fix is scoped by
it; what changed is the verdict line.*

§4.2(1). Our recogniser looked for `T._model.self`; the tool emits `T._model`. A
name that is not found reads as "no model", which under the owner's rule is a
loud decline — so it failed closed, not open. But it failed *uniformly*, which
means the first end-to-end run reported "no model" for everything and said
nothing about why. The shape-check diagnostics `nested_splice.rs:214-262` exist
precisely to prevent that class of report and needed the same treatment for the
new slots.

**Measured, on `lean-inductive-models`' own filtered `nested_keying` — which is
now checked in as `checker/tests/fixtures/tool_nested_keying.ndjson`:**

| | before | after |
| --- | --- | --- |
| `untranslated declarations` | **2** | **0** |
| the reasons | `Tree: no nested model in the export`, `UTree: nested model over a later declaration` | none |
| ledger `typesOk` / `valuesOk` | 119 / 117 of 121 | **121 / 121** |
| adoption, split by producer | — | `nested seen=2 models=2 tool=2 legacy=0` |

and the legacy side is unmoved — `nested_keying.ndjson` still reports `accept 39
declarations`, `untranslated: 1`, `nested seen=2 models=1 tool=0 legacy=1`.

**Two things this closes that a total could not show, and they are the reason
the `nested` row is now printed at all.** A recogniser that stops recognising
*declines*, and a decline moves no total on any line — the declarations are
counted in the `untranslated` column instead. So the split adoption count is
the measurement, and it is asserted per fixture rather than inferred.

**The `init-prelude` ratchets are unmoved, by construction rather than by a
run.** `vendor/arena-tests/good/init-prelude.ndjson` interns **zero** names
containing `_model`, and `modelgen`'s tower declares `T._model.self` and never a
bare `T._model` — verified on all five `modelgen`-filtered nested fixtures,
where `T._model` exists only as an interned *prefix* and `env.get` therefore
misses it. The `Scheme::Tool` carrier lookup cannot fire on a `modelgen` export,
so the legacy path is taken and behaviour is identical. It was not re-measured
end to end: `modelgen/` is not built in this worktree, and building it needs a
Lean toolchain.

**What is left of this section is the slots, not the names.** `T._model.proj_i`,
`T._model.proj_i.iota`, `T._model.eta`, `T._model.unitlike` and `R._model.ruleK`
still have no table here, and they are §4.2(2)–(3) rather than a naming
mismatch.

### 8.5 The structural checker is a second contract we would depend on

The tool's structural checker deliberately "does not unfold definitions, use proof
irrelevance, ask Lean for definitional equality, or inspect arbitrary declaration
values" (README) — it is a syntactic correspondence check, independent of the
kernel verdict. Our `nested_splice::shape` is our own version of the same check,
and `nested_splice.rs:69-92` is emphatic that it is a *diagnostic* and not the
trust root. That remains right and must stay right: **we must not come to rely on
the producer's checker having run.** The certificate is the trust root; the shape
check buys the reason string.

### 8.6 Not established

* Whether the tool's optional structure-eta / unit-like / recursor-rule-K
  theorems subsume `fun_eta.rs`, `unit_like.rs` and our K handling. The README
  says they are emitted "when the exported kernel metadata calls for them", which
  is a weaker guarantee than "always".
* ~~Whether `PSigma'` translates at mixed universes `(0,1)` and `(1,0)`.~~
  **Closed 2026-08-15, and closed as a decline.** `PSigma'` declines at both,
  with `ind-spec(PSigma': class (P) above Prop)` — the same reason and site as
  `(1,1)`, so §8.2's one classification fix covers all three red σ. The
  `derived/` side is **not** open: the same fixture measures Lean's `PSigma`,
  which is the identical instantiated declaration at both mixed σ, deriving its
  data carrier at all four. `Cumul::lift(0,n)` exists and is already spent on
  that path. `checker/tests/fixtures/psigma_mixed_sigma.lean` and
  `mini_designed::psigma_at_mixed_sigma_declines_only_where_the_declared_sort_may_be_prop`.

  *Why it stayed open so long is worth keeping.* It was not under-measured, it
  was **unreachable**: `instantiations::compute_in` spells a default as
  `vec![l; nparams]`, so a mixed σ can only come from a declaration that demands
  one, and no file in `vendor/arena-tests` or `checker/tests/fixtures` did.
  Re-running the corpus at any `DEFAULT_LEVELS` would have produced the same
  nothing and read as a pass.
* Whether the recognition path scales. **The modelling side is now measured at
  full Mathlib scale — §6.1: 6 882 families, 0 declines, kernel replay accepted.**
  The **recognition** side has never been run at more than fixture scale. *The
  naming blocker is gone (§8.4) and step 1 has landed, so it is now runnable —
  and the one end-to-end run there has been (§4.3) says the recognition side is
  where the remaining work is: `untranslated` went 91/10 → **109/17**, not to 0.*
  That asymmetry is the one thing the brief identified that survives intact, and
  it is now the only unmeasured half.
* The performance consequence, **now priced on the input side and still unpriced
  on ours.** *Corrected 2026-08-15: this bullet estimated "on the order of
  30 000 extra declarations" from `2 + 2c` per inductive. Measured, a model
  family costs **10.4 declarations**, stable to ±5 % from 12 000 to 176 000
  declarations (§6.1), so Mathlib's 6 882 families are nearer **72 000** extra
  declarations — low by a factor of about 2.4.* They are almost entirely `def`s
  and `thm`s, so under §1 every one of them goes through nanoda and its
  schedule. The export itself grows only **1.05×** in bytes and **~1.11×** in
  declarations, which is a mild operational cost; what is still unpriced is what
  72 000 extra nanoda-routed declarations do to *our* run time.
* Where inside `zoneb.rs` the basis slice ends and the retiring construction
  begins (§5.3's qualification on the 23 656).

### 8.7 A note on scope

This document deliberately says nothing about *how* TG evidence is produced —
only about which engine type-checks which declaration, and which statements a
construction concludes. That is so it survives the `Certifier`-trait retirement
now in flight on `joachim/retire-certifier`, which threads evidence directly
through `tc.rs`. Nothing here depends on the trait, on `NullCertifier`, or on the
compile-time backend selection; §1's trace is about `Mode::pick` and
`check_declar_scheduled`, and §3.6's table quotes constructions by the statement
they conclude.

## 9. Measurement log

*Release binary at `4c6426a`, `--features tg`. `ci/corpus-dir.sh --link` run
first.*

| what | result |
| --- | --- |
| `nested_keying.ndjson` `_model` declarations by kind | 16 `def`, 11 `thm`, 0 inductive, 0 axiom |
| `nested_keying.ndjson` routing | `toMini=8 toChecker=31 unclaimed=0` |
| `tight_psigma_prime.ndjson` (external fixture) | `accept 3 declarations`, **`untranslated: 3`**, all `class (P) above Prop` |
| — the same, **per σ** (2026-08-15) | `PSigma'.{0,0}` **translated**, with `‖a‖ ∈ U₀`, `only_point`, `elim`, ι-by-reflexivity; `PSigma'.{1,1}` declined. Two scheduled σ, one red |
| `081_PSigma.snd.ndjson` (Lean's `PSigma`) | `accept`, `untranslated declarations=0`, **1 tg gap** |
| — `PSigma.{1,1}` apparatus (2026-08-15) | full data carrier: carrier ax, `ctor 0 mem`, `ctor 0 inj`, rec typing, `ι 0`, `gen ι 0`, rec abbrev at `σ = [1,1,1]`; `elim PSigma computed=true oracle=true` |
| `⊢ Σ ∈ U₀` | **refutable**, not missing: `U₀ = {0,1}`, `1 = {∅}`, Kuratowski pairs ⟹ `Σ(1,λ_.1) = {1} ∉ U₀`. `thesis.txt:2461` states the Σ clause "For n > 0" only |
| `Σ ∈ Uₙ` entry points | **public**, five of them, `derived/src/cumul.rs:96-100`; no `max(1,…)` clamp exists in `derived/`'s executable code |
| **mixed σ, `psigma_mixed_sigma.ndjson`** (2026-08-15, release binary, `--naive`) | `accept 10 declarations`, `pairs=8`, `constEv=5`, `waiting:ind-spec(PSigma': class (P) above Prop)=3`, **TOTAL gaps 0** |
| — `PSigma'` per σ | `[0,0]` **class-(P) truncation carrier**; `[0,1]`, `[1,0]`, `[1,1]` **declined**, one reason |
| — `PSigma` per σ (control, `max 1 u v`) | **data carrier at all four**, `[0,1]` and `[1,0]` included — carrier, carrier ax, `closed`, `ctor 0 mem`, `ctor 0 inj`, universe placement |
| — the two shapes at mixed σ | **identical instantiated declarations**: `max 0 1 = max 1 0 1 = 1`, `max 1 0 = max 1 1 0 = 1` |
| — `Cumul::lift(0,n)`, §8.6's predicted spend | already built and already in the path: `derived/src/tower/cumulative.rs:180` → `Interp::raise_in_gamma`/`cumul_lift` → `zoneb.rs:2953` |
| — a mixed σ from a default | **impossible**: `instantiations::compute_in` seeds `vec![l; nparams]` |
| `PSigma'.rec` level params | `[u, v]` — small-eliminating |
| `PSigma.rec` level params (control) | `[u_1, u, v]` — large-eliminating |
| `init-prelude.ndjson` with `--no-modelgen` | declines at `Lean.Syntax`, as `CLAUDE-HANDOFF.md` records |
| `checker/src/mini/*.rs` | 55 255 lines, 60 files (unchanged `4c6426a` → `5bab7c0`) |
| retiring / staying split | 23 656 / 8 702 of the 32 358 in scope |
| model names in the tool's own output fixture | `T._model`, `C._model`, `R._model`, `R._model.iota_j` — **no overlap** with our `T._model.self` / `ctor_j` / `rec_k` / `iota_k_j` |
| the naming contract, from `Naming.lean` rather than a fixture (2026-08-15) | `modelName n = n._model` on the exact modelled declaration; `iota_j`, `proj_i`, `proj_i.iota`, `eta`, `unitlike`, `ruleK` are the only indexed or role-named slots |
| **our checker over the tool's filtered `nested_keying`** (2026-08-15) | before: `untranslated 2`, `typesOk 119/121`, `valuesOk 117/121`. After `236ba86`: **`untranslated 0`, `121/121`, `nested seen=2 models=2 tool=2 legacy=0`** |
| — the `modelgen` fixture beside it, same run | unchanged: `accept 39`, `untranslated 1`, `nested seen=2 models=1 tool=0 legacy=1` |
| `_model` names interned by unfiltered `init-prelude` | **0** — so `Scheme::Tool`'s carrier lookup cannot fire on a `modelgen` export |
| **`lean-inductive-models` over `init-prelude`** | **144 model families, 0 declines, 3 exempt (`Nat`, `Eq`, `PUnit`), 658 statements compared / 0 differ, exit 0** |
| — the same **with output**, and our checker over it (2026-08-15, `236ba86`) | `accept 3123`, **`untranslated: 109 declarations, 17 eliminators`** (was 91/10 — §6 corrected), `prefix 171`, `nested seen=1 models=1 tool=1 legacy=0`, `route toMini=149 toChecker=2974`, `output kernel check: accepted` |
| — the public model surface, by family | 1 044 declarations: 453 `X._model`, 174 `iota_j`, **153 `proj_i` + 153 `proj_i.iota` + 104 `eta` + 4 `ruleK` + 3 `unitlike` with no slot on our side (40%)**, 100 `_impl` |
| — `init-prelude`'s inductives | 126 type formers; **88 universe-polymorphic**, **107 single-constructor**, 4 indexed, 0 mutual |
| **σ keying of the type former and constructors** (2026-08-15, `8dba64c`) | on `poly_nested_used`, `PTree.{u}` at three universes: `nested model not keyed here` **3 → 0**, `untranslated` 17 → 15. `init-prelude` **byte-identical** — its only nested declaration binds no level parameters |
| — what it exposed | `DEFAULT_LEVELS = [0,1]` and nothing mentions a model constant, so `⟦PTree._model.{2}⟧` is never interpreted: propagating σ does not re-take the demand **closure** (§4.3 item 1b) |
| **`lean-inductive-models` over full Mathlib** (2026-08-15, §6.1) | **6 882 model families, 0 declines, 3 exempt, 48 677 statements compared / 0 differ, 203 level comparisons / 0 escapes, `output kernel check: accepted`, exit 0** |
| — declines at every rung of the ladder (3.7 MB → 5.6 GB) | **0**, at all six sizes; `grep -c ': declined'` is the check, not the exit code |
| — families against inductives, full Mathlib | 6 882 families over 6 644 input inductives; 85 splice events supply the difference |
| — the predecessor's number | `MODELGEN.md:6930`'s **6 882/0/3** reproduced exactly by a different tool over a changed basis; statements compared 18 511 → **48 677** |
| — cost, full Mathlib | **53 m 04 s** wall, 3 181.9 s `task-clock`, **27.27 T `instructions:u`**, peak RSS **10 881 MiB** (tree sampler upper bound 14.9 GiB) |
| — is cost linear? | **yes**: 273 K instructions/line at full scale, against 300 K at `m3` and 264 K at `m10`. `m20`'s 412 K is a **content anomaly, not a scaling law** |
| — an `m1`/`m3` linear-in-declarations fit, tested upward | predicted `m10` 1 253 MiB (actual 1 276) and Mathlib 9 962 MiB (actual 10 881) |
| — **output growth, full Mathlib** | **5 636.3 MB → 5 943.2 MB = 1.0545×**, +306.9 MB; declarations **654 504 → 727 155 = 1.111×**, +72 651 |
| — cost of one model family | **10.4 declarations**, ±5 % from `m1-A` to full Mathlib; corrects §8.6's "order of 30 000" to **72 651** |
| — what the added declarations are | +41 566 `def`, +30 843 `thm`, +242 `inductive`, **0 new axioms, 0 new opaques** — §1's routing claim at Mathlib scale |
| — `_model` name entries in the output | **25 373**, against **0** in the input |
| — serialized re-read of the 5.94 GB written | **`input check: 6882 model families checked`, `input kernel check: accepted`**, 0 violations, exit 0; 20 m 35 s, 14.79 T instr, 8 390 MiB RSS |
| — independent oracle | the tool's own `scripts/check-mathlib-result.sh`, run unmodified on the three artifacts: **pass, exit 0** |
| `vendor/lean-inductive-models` after all runs | **unmodified**, `5a9a70f`, empty `git status`; tool built from a scratch copy at `_tmp/lim` |
| — the `field type uninterpretable` family | all modelled (`UInt8/16/32/64`, `USize`, `Char`, `String`, `Fin`, `BitVec`, `ByteArray`, `Hashable`, `Lean.Name`, `Lean.Syntax`) |
| — the `type former spine` family | all modelled (`HAdd`…`HAppend`, `Membership`, `Trans`, `Monad*`) |
| — the 10 untranslated eliminators | all modelled (`False`, `PEmpty`, `HEq`) |

The tool was built from a scratch copy at `_tmp/lim`, never from `vendor/`, which
is unmodified. `_tmp/` is project-local and gitignored.

**Gates, at `5bab7c0` with this document as the only change:** `unified_cli`
6/6, `mini_designed` 34/34, `tg_tutorial` 36/36, `--no-default-features --lib`
251/251, `cargo check` 10 warnings, `ci/check-boundary.sh` OK.
