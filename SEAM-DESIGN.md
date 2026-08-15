# The TG/mini seam — what TG may hold of mini's state, and where the line falls

Design tranche, 2026-08-14, at master `ea81018`. No production Rust changed.

Provenance, per the standing rule: **[read]** = verified against this
worktree's code during this design, with `file:line`; **[unverified]** = not
established here, marked with the date so a later seat re-derives rather than
inherits.

Two independent, well-measured tranches stalled at what looked like the same
wall — `NAT-CHAR-CENSUS.md` §3 B (the `Nat` equation bridge) and
`INDEXED-DESIGN.md` §8.2 (the indexed dependent ι rule, −89 gaps, rank 1 in
`ORIGIN-RANKING.md`). Both were diagnosed as "`TgBackend` holds no live mini
`Checker`". This document establishes that the diagnosis is right about the
fact and wrong about the consequence.

---

## 1. Verdict up front

1. **The seam is already in the right place, and `TgBackend` is already on the
   correct side of it.** `TgBackend` holds `core: EnvCore` **[read**,
   `checker/src/tg.rs:3028`**]** — the one-per-run shared semantic state that
   mini writes and TG reads. Every kernel-level object either site needs is
   either already on that handle or can be put on it as inert data. Neither
   tranche is blocked by the seam's *location*.

2. **Neither site wants `mini::Environment`, and acquiring it would not help
   either one.** `Environment` is two `HashMap`s of syntax and holds no kernel
   `Term` or `Thm` at all **[read**, `checker/src/mini/env.rs:156–165`: `consts:
   HashMap<Name, ConstantInfo>`, `owners: HashMap<Name, Name>`**]**. The brief's
   framing — "`TgBackend` holds no `mini::Environment`/`Interp` at any site" —
   is factually true **[read**, both grep to 0 in `tg.rs`**]** but the inference
   from it is void: the state these sites need is `Interp`-level, and `Interp`
   itself holds `core: EnvCore` **[read**, `checker/src/mini/interp.rs:96`**]**,
   which TG already has.

3. **`minor_ix.rs`'s dependence on Lean syntax is essential; its dependence on
   *mini* is incidental to the point of being a newtype.** `mini::expr::E` is
   `pub struct E(pub ExprPtr<'static>)` **[read**,
   `checker/src/mini/expr.rs:363`**]** over `pub type ExprPtr<'a> = Ptr<&'a
   Expr<'a>>` **[read**, `checker/src/util.rs:94`**]** — the *same hash-consed
   pointer into the same arena* that `TgBackend` already keys twenty of its maps
   on. "Index expressions out of Lean syntax in mini's `E`" and "the Lean syntax
   TG holds as `ExprPtr<'t>`" are the same objects. §5 has how this was
   established and what it does and does not license.

4. **Both sites want the same thing, so it is one seam, not two:** *publish the
   characteristic theorem of any mini-minted symbol as inert data on `EnvCore`;
   perform the premise discharge TG-native, over `ExprPtr`, using TG's own
   `has_type_a`.* What differs is only how much publication each needs — site 2
   needs **none** (it already landed), site 1 needs **exactly one** package.

5. **A live handle to mini's `Checker` or `Interp` is the wrong answer and is
   also structurally obstructed.** Using it means calling `infer_type` /
   `whnf_typing`, which is "invoke the other checker" and "rerun reduction" —
   both forbidden by the settled architecture. §4(b) records the two independent
   mechanical obstacles as well, so that nobody re-costs it.

---

## 2. The factual map

### 2.1 What `TgBackend` holds

`pub struct TgBackend<'x, 't: 'x, 'p: 't>` **[read**, `checker/src/tg.rs:3021`,
fields through `:3338`**]**. It has 40 fields; the four that decide this
question are:

| field | line | what it is |
| --- | --- | --- |
| `shared: Rc<RefCell<Shared>>` | `tg.rs:3023` | the per-thread signature and everything keyed on it |
| `core: EnvCore` | `tg.rs:3028` | **a clone of the shared core — mini's live semantic state** |
| `decls: &'x crate::env::Env<'x, 't>` | `tg.rs:3034` | nanoda's *declaration* environment (constant → value, so δ is justifiable) |
| `exprs: HashMap<ExprPtr<'t>, Term>` | `tg.rs:3049` | TG's own `⟦·⟧` memo, keyed by the Lean node |

The remaining 36 are per-backend memo tables and site maps (`has_types`,
`arg_mems`, `ctor_rules`, `gen_ty_nests`, `rec_nests`, …) **[read**,
`tg.rs:3037–3338`**]**.

**Lifetime.** One `TgBackend` per (declaration, σ): the sole constructor
`TgBackend::new(decls)` **[read**, `tg.rs:4360`**]** is reached only from
`certify::new_backend` **[read**, `checker/src/certify.rs:834`**]** from
`TypeChecker::new` **[read**, `checker/src/tc.rs:461`**]**, and its `'x` is tied
to a local created inside `ExportFile::with_tc_and_declar` **[read**,
`checker/src/util.rs:252–260`**]**. It takes *only* `decls`; everything else is
copied out of thread state (`sh.syms`, `sh.core.clone()`, `sh.decl_seq`)
**[read**, `tg.rs:4363–4367`**]**.

### 2.2 `EnvCore` — the publication channel, and it is shared state, not a wall

`pub struct EnvCore` **[read**, `checker/src/tg.rs:2064–2122`**]**, `#[derive(Clone)]`,
every field an `Rc` or `Copy`, so a clone *aliases the same cells*. It is `!Send`
by construction, and the header says that is the concurrency decision, not an
accident **[read**, `tg.rs:2034–2037`**]**.

| field | line | carries |
| --- | --- | --- |
| `env: Rc<RefCell<Env>>` | `:2066` | the kernel signature and variable source — "the brand" |
| `x_canon: FreeVar` | `:2068` | the canonical binder slot inside every skeleton key |
| `hole_vars: Rc<RefCell<Vec<FreeVar>>>` | `:2072` | the canonical hole series |
| `wtb: Rc<RefCell<Option<Option<(Wtype, Bound)>>>>` | `:2076` | the W-type and its bound |
| `machine: Rc<RefCell<Option<Option<Rc<RefCell<Machine>>>>>>` | `:2078` | the one `derived::inductive::Machine` |
| `nat: Rc<RefCell<Option<Option<Rc<NatClause>>>>>` | `:2088` | the one `derived::nat` apparatus |
| `projections: Rc<RefCell<ProjectionStore>>` | `:2097` | mini's class-(T) translations, `DeclProj`, dependent-recursor packages |
| `consts: Rc<RefCell<ConstStore>>` | `:2107` | **the shared constant store** — `⟦c.{σ}⟧` carriers, typings, defining equations |
| `lams: Rc<RefCell<LamStore>>` | `:2119` | the shared λ mint |
| `pis: Rc<RefCell<PiStore>>` | `:2122` | the shared dependent-product mint |

`ProjectionStore` **[read**, `tg.rs:2046–2058`**]** holds `translated`,
`evidence` and `dep_elims`, keyed by `crate::const_store::ConstKey =
(NameKey, Vec<LevelKey>)`.

Production installs one core for both engines in a single statement:
`crate::tg::install_shared_core(ip.core().clone())` **[read**,
`checker/src/mini/route.rs:309`**]**; mini gets the same one via `Interp::over`
**[read**, `checker/src/mini/interp.rs:1512`**]**.

**A `ConstEntry` carries three things and no more** **[read**,
`checker/src/const_store.rs:165–183`**]**: the carrier `term`, an optional
`typing` (`⊢ term ∈ ⟦ty[σ]⟧`), and an optional `defeq` (`⊢ term = ⟦val[σ]⟧`).
This is the fact that decides site 1 — see §3.1.

### 2.3 State computed once versus a live engine — the whole decision

| object | kind | why |
| --- | --- | --- |
| `EnvCore` and everything on it | **computed once, read later** | every payload is `Term`/`Thm`/`FnSym` behind an `Rc`; the getters `.get(key).cloned()` an `Rc` and construct nothing |
| `mini::Environment` | **inert, and empty of kernel content** | `HashMap<Name, ConstantInfo>` + `HashMap<Name, Name>` **[read**, `env.rs:156–165`**]** |
| `Interp` | **mixed** — mostly memo tables, but its methods mint symbols and derive | 30 fields **[read**, `interp.rs:90–256`**]**, of which `direct`, `eta`, `quotient`, `nat`, `acc`, `choice`, `rec_acc` are `Option<Rc<…>>` computed-once packages |
| `mini::kernel::Checker` | **a live engine** | `{ env: &'e Environment, lenv: Vec<E>, th: Option<Th<'i>>, wt_memo, frames, defeq_depth, whnf_depth }` **[read**, `checker/src/mini/kernel.rs:444–467`**]**; `Th<'i>` holds `ip: &'i mut Interp` **[read**, `kernel.rs:595–603`**]**. Its `infer_type` and `whnf_typing` re-run inference and reduction. |

### 2.4 The precedent: `73307c7` on `joachim/indexed-dep-iota`

The indexed-ι seat's publication commit adds two producer calls and two
receiving `HashMap` rows on `ProjectionStore` — `ix_translated` keyed by the
*inductive* at its ground instance, `ix_dep_elims` keyed by the *recursor* at
its ground instance — plus a readiness counter deliberately **not** behind
`stepcount`, "because the failure mode of a publication channel is silence".

What crosses is strictly inert: `IndexedDepRecursor` is `FreeVar`/`Term`/
`Formula`/`Thm` and `Vec`s thereof, with no closure, no `Env`, no `&mut`;
`IndexedTranslation`, `WRec` and `DepElim` likewise. The getters clone an `Rc`.
The commit moved **zero** gaps and says so, and `indexed_translation` /
`ix_dep_elim` / `has_ix_dep_elim` have zero call sites — the store is filled and
never queried. That is the correct shape of a publication and the correct
demonstration that publication alone does not reach either site's blocker.

---

## 3. What each site actually needs — minimally

The discipline here is the project's own: **look a construction up by the
statement it concludes, never by its identifier.** Both sites below were sized
as "needs a `Checker`"; both actually need one theorem and one TG-native walk.

### 3.1 Site 1 — the `Nat` equation bridge

`cash_stmt(c: &mut Checker, stmt: &E, mem: Thm) -> Result<Cashed, Gap>`
**[read**, `checker/src/mini/eq_cash.rs:353`**]** returns `Cashed { eq: Thm,
lhs: Term, rhs: Term }` with `eq : Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧` **[read**, `:290–297`**]**.
Its own header states the content exactly: *"Nothing here inspects the proof
term: the whole content is that a Lean proof's typing and a TG equation are the
same judgement under the interpretation"* **[read**, `eq_cash.rs:26–28`**]**.

It touches the `Checker` in six places and nowhere else **[read**, grep over
`eq_cash.rs`**]**:

| use | line | what it really is | TG's own |
| --- | --- | --- | --- |
| `c.stored_term(Eq, inst)` | `:368` | store read of `⟦Eq.{v}⟧` | the shared `ConstStore` |
| `c.infer_type(e)` ×3 (the three sides) | `:379` | `(⟦e⟧, ⊢ ⟦e⟧ ∈ ⟦ty⟧)` | `has_type_a` |
| `c.infer_type(&stmt)` | `:397` | ditto, for proof irrelevance | `has_type_a` |
| `c.interp().point()` | `:393` | store read | prelude-owned |
| `ip.direct()` | `:402` | **mini's `Direct` package** | **not published** |
| `ip.prelude.tower.sums` | `:403` | the prelude tower | TG has the same tower |

So the minimal thing that suffices for site 1 is **not a `Checker` and not an
`Interp`. It is one published package.** `Direct` **[read**,
`checker/src/mini/direct.rs:108–124`**]** is held privately at
`interp.rs:151` (`pub(crate) direct: Option<Rc<Direct>>`) and appears **nowhere**
on `EnvCore` **[read**, grep of `tg.rs:2064–2122` for `direct` returns 0**]**.

It must be *published*, not rebuilt, and the reason is exactly the
semantic-ownership rule rather than economy: `Direct::build` mints its `eq_set`
through `conditional_singleton` **[read**, `direct.rs:132`**]**, and
`derived::prop::Props` mints its own **[read**,
`derived/src/prop/apparatus.rs:84`**]**. `Direct`'s own doc says so in terms —
"`Props::new` mints a *fresh* `Sums`, hence a second `1`, so it cannot be the
thing an interpretation store already committed to a unit set uses" **[read**,
`direct.rs:100–107`**]**. TG rebuilding it would produce a second `eq_set`
symbol that no theorem relates to the `⟦Eq.{v}⟧` already in the shared const
store. `tg.rs` today has **zero** occurrences of `eq_ax`, `cond_elim`,
`eq_sound` or `Props::` **[read**, grep = 0**]**.

**Prize, and it is smaller than the site's prominence suggests.**
`NAT-CHAR-CENSUS.md` §4 already established that the `nat_char_equations`
fixture's wall is `PProd` projection inside the `brecOn` nest, not arithmetic;
the bridge proper measures **−11 of 152, bounded 11 ≤ prize ≤ 26**. Site 1
should be scheduled on that number, not on 152.

### 3.2 Site 2 — the indexed dependent ι rule

The rule is `∀p⃗ ∀m ∀S⃗ ∀T. (PRE → …)` with `PRE = ICOD(m,T) ∧ IDEP(m,S⃗)`, and
`tg.rs` contains **zero** occurrences of `IDEP`/`ICOD`/`idep`/`icod` **[read**,
grep = 0**]**. `derived/` only *states* the premise, and must — that boundary is
load-bearing and correct. The sole discharge is `checker/src/mini/minor_ix.rs`
(895 lines).

`minor_ix.rs` touches the `Checker` in exactly nine ways **[read**, grep over
the file**]**:

| method | count | what it is |
| --- | ---: | --- |
| `c.interp(…)` | 9 | store read |
| `c.iter(…)` | 2 | telescope iteration |
| **`c.infer_type(…)`** | **2** | **the only live-engine call** |
| `c.scope_vars`, `c.push_interpreted`, `c.local_type`, `c.len`, `c.close_one`, `c.binder` | 1 each | scope/telescope management |

Everything else in the walk is `derived::` composition over already-computed
data: `index_congr`, `beta_spine`, `eq_symm`, `eq_trans`, and the published
`CtorIndexAx::rec_args` axioms **[read**, `minor_ix.rs:596–680`**]**.

The two `infer_type` calls are:

* `ctor_ix::infer_indices(c, &ds_e)` **[read**,
  `checker/src/mini/ctor_ix.rs:498–505`**]**, which is a three-line loop over
  `c.infer_type(e)` producing `(⟦dₖ⟧, ⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧)` per index expression.
  The module header names this "the only place `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` exists"
  **[read**, `minor_ix.rs:66–68`**]**;
* `c.infer_type(&dom_e)` on the `clause.trunc` branch only — class (P), not
  class (T), so not on site 2's path **[read**, `minor_ix.rs:628–631`**]**.

**So the minimal thing that suffices for site 2 is one derivation TG can already
perform**: `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` for each index expression of a recursive field.
TG's `has_type_a` concludes exactly `⊢ conj(assms') → (⟦e⟧ ∈ ty)` **[read**,
`checker/src/tg.rs:10328`, doc at `:10331`**]**, and the target `⟦Iₖ⟧` is
recoverable by `inst_all` from `IndexAx::indices`, whose entries are
`⊢ ∀p⃗ ∀x⃗<ₖ. ιₖ(p⃗,x⃗<ₖ) = ⟦Iₖ⟧` **[read**, `checker/src/mini/zoneb.rs:1900–1923`,
axiom shape stated at `:1897`**]**. `IndexAx` rides on `IndexedTranslation.ax`
**[read**, `zoneb.rs:625–636`, `:511–513`**]**, which `73307c7` already
publishes — twice, standalone and inside `IxDepRec.tr`.

**Site 2 therefore needs no new publication at all.** That is a finding against
the `INDEXED-DESIGN.md` §8.2 route-(B) sketch, which proposed publishing a
*discharged, generalised* premise from mini and flagged, correctly, that no such
machinery exists.

---

## 4. The options, costed

### (a) Publish more across `EnvCore`

**Right for site 1, and only for the one thing mini mints.** Cost: a
`ProjectionStore`-shaped row plus a `publish_direct`/`direct()` pair on
`EnvCore`, following `publish_dep_elim` **[read**, `tg.rs:2191`**]** exactly,
with the idempotence guard comparing the `eq` `FnSym` — ~60 lines and a
readiness counter, on `73307c7`'s pattern.

**Wrong as a *general* answer**, and `73307c7` is the proof: it published
correctly and moved zero gaps, because publication cannot cross a
premise-discharge boundary.

### (b) Give `TgBackend` a read-only handle to mini's computed state

**Already true, and not what these sites lacked.** `TgBackend` holds `core:
EnvCore` **[read**, `tg.rs:3028`**]**. Extending it to `&mini::Environment`
should not be attempted, for three reasons in increasing order of severity:

1. **It would buy nothing.** `Environment` holds no kernel objects (§2.3).
2. **Borrow conflict.** `Routed::accept` holds `env: &mut Environment` live
   across the whole TG call at `route.rs:398`, and mutates it in the same call
   at `route.rs:409` (`install_checked_noninductive`) **[read]**.
3. **`'static` engine.** The object that persists across the loop is
   `chk: Option<CheckerEngine<'static, 'static>>` **[read**, `route.rs:278`**]**,
   whose `ef: &'x ExportFile<'p>` comes from
   `arena::installed_export_file() -> Option<&'static ExportFile<'static>>`
   **[read**, `checker/src/mini/arena.rs:162`**]**. A non-`'static` reference
   cannot be stored there; six signatures would need a new parameter and
   `TgBackend` a new lifetime.

A `&mut Interp` is *borrow-wise* feasible — `Pass::step`'s `ip` is unused during
`driver.accept` **[read**, `decl_pass.rs:241–258`**]** — but that only makes the
forbidden thing mechanically possible. Constructing `Checker::threaded(env, ip)`
**[read**, `kernel.rs:621`**]** and calling `infer_type`/`whnf_typing` is
"invoke the other checker" and "rerun reduction". **Out, by the settled
architecture, and independently unnecessary by §3.**

There is also a standing ordering constraint worth not tripping: a routed run
installs the caller's core as the thread's core and "must run on a thread where
no `TgBackend` has been built yet" **[read**, `route.rs:285–288`**]**.

### (c) Move the discharge to the TG side

**Right for both sites.** For site 2 this is `INDEXED-DESIGN.md` §8.2's route
(A) — `ix_dep_minor_typed` beside `dep_minor_typed`. The precedent is exact:
`dep_minor_typed` already takes `dom_exprs: &[ExprPtr<'t>]` — Lean syntax — and
`obligations: &[(Thm, Vec<Formula>)]`, and discharges the non-indexed `DEP`
TG-native **[read**, `checker/src/tg.rs:15355–15369`**]**. §8.2's own sizing of
~400–600 lines stands; nothing here refutes it.

For site 1 it is the same move at a much smaller scale: a TG-native `cash_stmt`
over `ExprPtr`, ~150 lines, given (a)'s one publication.

### (d) What the brief did not list, and it is the actual finding

**The seam is not mis-drawn; the question was mis-framed.** Both tranches
described their blocker as *state TG does not hold*. The blocker is *a
derivation TG has never been asked to perform*. `EnvCore` is not a wall with a
letterbox — it is one shared object both engines already write and read. What
does not and must not cross it is **capability**: the `&mut Interp` inside a
`Checker`, and the `infer_type`/`whnf_typing` that re-run work.

That gives a rule sharper than "hold a handle or don't", and it is the
document's recommendation:

> **A mini-minted *symbol* obliges a publication; a mini-computed *inference*
> obliges a TG-native re-derivation.** Publish the characteristic theorem of
> anything mini mints, because a second mint is a second symbol no theorem
> relates to the first. Never publish, and never reach for, the *ability to
> infer* — TG has `has_type_a` and holds the same `ExprPtr`.

Under that rule: site 2 is pure (c), zero publication; site 1 is (a)+(c), one
publication (`Direct`, because `eq_set` is minted) plus a TG-native walk.

**One answer serves both.** The seam is one seam.

---

## 5. Is `minor_ix.rs`'s Lean-syntax dependence essential or incidental?

**Both, in two different senses, and separating them is the whole answer.**

**Essential with respect to Lean syntax.** At a `Slot::Rec` level the walk calls
`zoneb::ind_spine_at(&site.ind, &dom_e, &lifted, ni)` **[read**,
`minor_ix.rs:611–613`**]** — a *syntactic* recognition of the recursive field's
binder type as `T p⃗ d⃗`, from which the index expressions `d⃗` are extracted.
Those expressions exist nowhere else. The module header states the reason and it
is sound: the atom `minor_atoms_at` states is `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))` while
the binder was opened at `⟦T p⃗ d⃗⟧`; the two differ by one β, β consumes one
membership per index, and "`d⃗ᵢⱼ`'s defining axioms give the *terms* and not the
memberships" **[read**, `minor_ix.rs:44–57`**]**. No interpretation-level walk
recovers them. **A design that tries to discharge `PRE` from published set-level
data alone will fail, and route (B) of §8.2 is that design.**

**Incidental with respect to *mini*.** The dependence is on Lean syntax, not on
mini's copy of it — and there is no second copy. `mini::expr::E` is
`pub struct E(pub ExprPtr<'static>)` **[read**, `checker/src/mini/expr.rs:363`**]**,
a newtype over `ExprPtr` **[read**, `checker/src/util.rs:94`**]**, hash-consed
so "pointer identity *is* structural identity" **[read**, `expr.rs:347–349`**]**,
into the arena the unified driver installs once — "one file, one arena, one
`NameKey` identity" **[read**, `route.rs:296–300`**]**. `TgBackend` keys
`exprs`, `has_types`, `const_defs`, `lam_sites` and a dozen more on exactly that
type **[read**, `tg.rs:3037–3230`**]**.

**How this was established.** Not by reading the header's claim and believing
it — the header does assert the separation ("*That reason is about Lean syntax,
not about a telescope*", `minor_ix.rs:70–76`), and a brief is a hypothesis. It
was established three ways, each independently sufficient:

1. **Grepping the `Checker` surface.** Nine methods, one of which re-runs work
   (§3.2). A dependence on a live engine that is one function call wide is not a
   dependence on the engine.
2. **Reading the type.** `E`'s definition is one line and settles it: mini and
   TG hold the *same pointers*. This is the check that cost nothing and should
   have been run before either tranche was sized.
3. **Finding the author's own factoring already in the code.** `Source { mty: E,
   params: Vec<E> }` **[read**, `minor_ix.rs:350–355`**]** exists precisely so
   that `transport_at` **[read**, `:428`**]** can be called with a frame that is
   *not* the eliminator's telescope; `from_telescope` **[read**, `:365`**]** is
   documented as "the only one the three eliminator routes present", with the
   use-site case — "a ι rule firing at arbitrary arguments" — named as the
   motivation. **The split this tranche was asked to design already exists and
   has no second caller.** That is the fifth time on this line that a brief has
   sized work that was already built.

**What this settles.** It settles the seam in the direction of TG-native
discharge (§4(c)). It does **not** license transliterating `minor_ix` into
`tg.rs` — §8.2 is right that this would be a second copy of a module mini owns
— and it does not make site 2 cheap. `ix_dep_minor_typed` still has to be
written against `ExprPtr` rather than `E`, needs an `ind_spine_at` equivalent
(~40 mechanical lines, per §8.2), and needs the per-child index memberships from
`has_type_a`.

---

## 6. The falsifiable claim, and its check

> **Claim.** Everything `minor_ix.rs` and `eq_cash.rs` obtain from a live
> `mini::kernel::Checker` is available to `TgBackend` without one, because the
> only engine call at either site is `infer_type`, and at every occurrence the
> *target set is known to TG in advance* — so TG's checking-mode `has_type_a`
> suffices where mini used synthesis.

**What would make it wrong.** `infer_type` **synthesizes** a type; `has_type_a`
**checks** against a `ty: &Term` the caller must already have **[read**,
`tg.rs:10328`**]**. If at any of these occurrences the target set is not
computable by TG before the call, the claim fails and the site genuinely needs a
synthesis engine — which TG does not have and which would have to be either
built or borrowed. This is a single, decidable question per call site.

**The check — all six occurrences, exhaustively.**

| site | expression typed | target set | available to TG? |
| --- | --- | --- | --- |
| `minor_ix` → `infer_indices` | each index expr `dₖ` of a recursive field | `⟦Iₖ⟧` | **yes** — `inst_all` on `IndexAx::indices[k]`, `⊢ ∀p⃗ ∀x⃗<ₖ. ιₖ(p⃗,x⃗<ₖ) = ⟦Iₖ⟧` **[read**, `zoneb.rs:1900–1923`**]**, published inside `IndexedTranslation.ax` |
| `minor_ix` `clause.trunc` branch | recursive field's binder type | `⟦T p⃗ d⃗⟧` | **yes**, and moot — class (P) only, not site 2's path |
| `eq_cash` sides[0] = `α` | the type argument | `⟦Sort v⟧` | **yes** — `v` is the ground level already extracted at `eq_cash.rs:363–364` |
| `eq_cash` sides[1] = `lhs` | left endpoint | `⟦α⟧` | **yes** — `self.interp(ctx, α)` |
| `eq_cash` sides[2] = `rhs` | right endpoint | `⟦α⟧` | **yes** — same |
| `eq_cash` `stmt` (proof-irrelevance branch) | the `Eq` statement itself | the `Prop` clause's set | **yes** — the branch is entered only when the subject is already known not to be `•` **[read**, `eq_cash.rs:394–400`**]** |

**Result: the claim survives at all six.** Six of six targets are computable in
advance; no synthesis is required at either site.

**Residual risk, stated rather than hidden.** The claim is about *availability
of the target*, which is what distinguishes checking from synthesis. It is
**not** a claim that `has_type_a` will *succeed* on these expressions — it
returns `Option` and caches negative results **[read**, `tg.rs:10326–10327`**]**,
and its corpus discharge rate is far from total (`tg.rs:10934` records 40 060
obligations asked and 6 389 discharged). **[unverified, 2026-08-14]** What
fraction of index expressions `has_type_a` actually types is not measured here,
and it is the right first measurement for whoever writes `ix_dep_minor_typed`:
instrument the `infer_indices` call sites on a `--features tg,stepcount` build
over `077_RBTree`, `094`, `117`, `118`, `071`, `072`, and compare against mini's
success on the same expressions. If TG's rate is materially worse, the tranche
is larger than §8.2's 400–600 lines — but the *seam* conclusion is unaffected,
because the remedy would be improving `has_type_a`, which is TG-native work.

---

## 7. Recommendation, per site

| | site 1 — `Nat` equation bridge | site 2 — indexed dependent ι |
| --- | --- | --- |
| **recommendation** | **(a) + (c)** | **(c)** — §8.2 route (A) |
| publication needed | `Direct` (or `eq_ax` + `point`) on `EnvCore`, ~60 lines | **none** — `73307c7` already suffices |
| TG-native work | `cash_stmt` over `ExprPtr` via `has_type_a`, ~150 lines | `ix_dep_minor_typed` + `RecBottom::IxDep` + `fire_ix_dep`, ~400–600 + ~800–1000 lines |
| what is **not** needed | a `Checker`, an `Interp`, an `Environment` | the same |
| measured prize | 11–26 gaps (`NAT-CHAR-CENSUS.md` §2) | −89 gaps, priced under `NANODA_ASSUME` and therefore conditional on the premise being *establishable*, not merely true |

**Ordering.** Site 2 first: larger prize, and it needs no publication, so it is
pure TG-native work that cannot collide with the three seats live in `tg.rs`
once they land. Site 1's publication half can be done independently of them at
any time.

**Do not** take §8.2 route (B). §3.2 shows the data it would publish is already
published, and §5 shows the derivation it would move cannot be performed from
set-level data alone.

---

## 8. Corrections to the brief that scoped this tranche

Recorded because a brief is a hypothesis and this project keeps the refutations.

1. **`INDEXED-DESIGN.md` §8.2 does not exist on `master`.** It is on
   `joachim/indexed-dep-iota` at `47d5a0a` (with `bbacb9f` before it). A seat
   sent to master's `INDEXED-DESIGN.md` finds §8.1 at line 1151 and §9 at 1246,
   with nothing between. **[read]**
2. **"`TgBackend` holds no `mini::Environment`/`Interp` at any site" is true but
   misleads.** `TgBackend` holds `core: EnvCore` **[read**, `tg.rs:3028`**]**,
   which *is* mini's live shared semantic state, and `mini::Environment` holds
   no kernel objects, so acquiring it would unblock nothing. The obstruction was
   never state.
3. **"index expressions out of Lean syntax in mini's `E`" overstates the
   distance.** `E` is a newtype over the `ExprPtr` TG already holds, into the
   same arena **[read**, `expr.rs:363`, `util.rs:94`, `route.rs:296–300`**]**.
4. **The `Source`/`transport_at` split the brief asks to design already
   exists**, is documented as existing for exactly the use-site ι case, and has
   no second caller **[read**, `minor_ix.rs:350–365`, `:428`**]**.
5. **Site 1's prize is not the `nat_char_equations` fixture.**
   `NAT-CHAR-CENSUS.md` §4 established that the fixture's wall is `PProd`
   projection in the `brecOn` nest; the bridge is 11 ≤ prize ≤ 26.

## 9. What this document does not establish

* **[unverified, 2026-08-14]** No build, test or corpus run was performed for
  this tranche — it is a read of the code at `ea81018`. Every claim above is
  cited to `file:line` and was checked in this worktree; none was measured at
  runtime.
* **[unverified, 2026-08-14]** `has_type_a`'s success rate on index expressions
  (§6, residual risk).
* **[unverified, 2026-08-14]** Whether `Closed::discharge` yields the antecedent
  order §8.2 route (B) would need. Not checked, because §3.2 removes the reason
  to take route (B) at all; a seat reviving it must check this first.

---

## 9. What crosses the seam, and who reads it — the inventory

*Measured 2026-08-15 by counting field references in `checker/src/tg.rs` against
`checker/src/mini/*.rs`. §1–§8 settled **where** the seam belongs; nothing
enumerated **what actually crosses it and whether anyone reads it**, and three
tranches in a row were blocked by a published fact with no consumer.*

**How to read the numbers.** A **zero is exact** — a field with no `.field`
reference in a file is not read there, whatever it is named. A **non-zero is an
upper bound**: `.rec`, `.ctors`, `.spec`, `.ty`, `.minors` and `.mem` are common
enough that the count includes unrelated matches. So this table is a list of
*absences*, and that is the useful direction.

### 9.1 Published and read by mini, **never** by TG

| field | mini | TG | is the protocol meetable by TG? |
| --- | ---: | ---: | --- |
| `IndexedTranslation::field_abbrev` | 18 | **0** | yes — positional, instantiable at a site's terms |
| `IndexedTranslation::rec_dom_abbrev` | 12 | **0** | yes, but it is the function-typed-slot bridge, which the value walk declines by name |
| `IndexedGuardedMinors::hyp` | 12 | **0** | yes |
| `IndexedCtor::mem_lean` | 3 | **0** | **NO — see §9.3** |
| `IndexedCtor::lean_order` | 2 | **0** | yes |
| `IndexedGuardedMinors::typed` | 2 | **0** | yes |
| `IndexedCtor::mem_atoms` | 1 | **0** | yes |
| `IndexedCarrier::subset_w` | 1 | **0** | yes |
| `IndexedCtor::inv` | 1 | **0** | yes |

### 9.2 Published and read by **neither** engine

`IndexedCarrier::good_of`, `IndexedGuardedMinors::fires`, `::minor_typed`,
`::guard_atoms`, and `IndexedInductive::ix` / `gv` / `gs` / `good`. These are
not seam defects — they are the internals of the `good` recursion and the
guarded minors, reachable through the objects that *are* read. Listed so a
future reader does not mistake them for the same category as §9.1.

### 9.3 The correction this inventory exists for: **zero can measure an unmeetable protocol**

`IndexedCtor::mem_lean` was reported (INDEXED-DESIGN.md §8.7, since corrected in
place) as a published fact in exactly the right shape that TG simply had not
taken. **The count was right and the inference from it was wrong.** `mem_lean`'s
witness protocol demands each `wₖ` be *closed, prenex, and at `derived`'s own
working variables*; every consumer that could want it — a use site, or the
bottom of a λ-nest, which is where mini meets it — holds **open-scope,
already-instantiated** theorems, and generalising them back is unavailable
because the scope assumptions are live hypotheses and **a hypothesis-carrying
theorem cannot be generalised**. The bridge is filed as **task #38** and does
not exist. `checker/src/mini/ctor_ix.rs:43–68` had said all of this for months.

So the inventory needs the third column and not only the count. **A zero-consumer
row is a question, not a finding**, and the question is: *can the protocol be
met by anyone standing where the consumer stands?*

* **`Full::rule` / `want_full = false`** — meetable; nobody asked. A real
  opportunity, taken (INDEXED-DESIGN.md §8.4.1).
* **the type former's typing behind `Decline::Indices`** — meetable; a *cost*
  guard said no. A real opportunity, taken (ibid.).
* **`mem_lean`** — *not* meetable. Not an opportunity at all.

Two of three were what they looked like. The third is why the column exists.

### 9.4 What this does not cover

Only the indexed publications. The projection translation, `DepElim`, the shared
`LamStore`/`PiStore`/`ConstStore` and the `Nat` clause are unmeasured here, and
the same three-column treatment would apply to each. **Do not read the absence
of a row as a zero.**


## 10. Rank 3, censused: the named row is worth −1, and the −35 is one wall behind it

*Measured 2026-08-15 on `joachim/major-premise-domain`, binary
`cargo build -p nanoda_lib --features tg,stepcount --bin checker`,
`ci/corpus-dir.sh --link` run first. `stepcount` is mandatory: without it
`NANODA_ASSUME` is compiled out and every setting reports the baseline.*

### 10.1 The deletion reproduces, and the label is one cause

`ORIGIN-RANKING.md` rank 3,
`iota: the major premise's domain is not this inductive at this parameter`:
`076_listRecReduction` **45 → 10** under `NANODA_ASSUME` on that row alone,
own 5 / relayed 32 / sub-tree 37. Exactly as ranked.

**It is one cause on one recursor**, unlike rank 1. The string is raised at a
single site, `tg.rs:20197`, inside `fire_list`, and instrumenting it gives five
declines: **3 × `List.cons`, 2 × `List.nil`, all `List.rec`**. `IOTA_LABEL_OVERLAP`
does not cover this row — it censuses only the `iota: no interpretation — *`
chain — so the split was taken by instrumenting the site directly.

### 10.2 The cause: three independent mints of `⟦List⟧`

The check that fails is `app(⟦List⟧, α) == doms[major]`. Both sides are
`app(head, α)` with the *same* `α`; only the heads differ, and there are **three
different heads for one constant** in this binary:

| spelling | who mints it | who insists on it |
| --- | --- | --- |
| mini's published carrier, `L(S)` applied to the sort | `mini_const`, off the shared `const_store` | `interp` — so *every* domain term the nest walked |
| `derived::wlist_fun`'s hand-written abbreviation | `ind_const` → `list_const` | `fire_list` |
| a fresh nullary abbreviation | `gen_ty_nest` at `np > 0` | `fire_dep` → `gen_ty_bridge` |

`interp`'s `Const` arm consults `mini_const` **first**, above the elaborate guard
at `tg.rs:8452-8468` that exists to stop a second `⟦List⟧` being minted — the
guard's own comment records that losing injectivity of `interp` on that constant
"cost 54 ι sites". `mini_const` sits above it and does exactly what it forbids,
while `rec_bottom` still routes `List.rec` to the hand-written `fire_list`.
**Carrier from mini, recursor from `derived`.** Not one of `fire_list`'s five
sites can ever match, so on this file `fire_list` is structurally dead code.

### 10.3 The census inside the rule: the reachable prize is −1

`Δ = −35` prices *the equation being true*. What a construction can reach was
measured two ways, and both move the wall rather than remove it:

| probe | what it does | `076` | exports total |
| --- | --- | ---: | ---: |
| baseline | — | 45 | 172 |
| let the recogniser own `List` (`interp` tries `ind_const` first) | `fire_list` and `interp` agree | **44** | **247** |
| route `List.rec` to mini (`fire_dep`) | widen the two `np == 0` gates | **48** | 171 |

* **Recogniser-first**: the named row vanishes completely and the file falls by
  **one**. The 37-gap sub-tree survives, redistributed onto two successor walls
  inside the same ι engine — `iota: the reduct does not contract to what the
  recursor computes` (own 3, sub-tree 25) and `iota: the core equation does not
  match the reduction` (own 2, sub-tree 12). It also costs **+75 across the
  exports**, which is the ownership rule being right.
* **Route to `fire_dep`**: `mini_dep_rec_bottom` fully succeeds for `List.rec`
  once the gates are widened — mini *does* publish the `DepElim` (`dep_elim=true`),
  the adopted `GenInd` is pointer-identical, `gen_ty_nest` builds — and then
  `gen_ty_bridge` declines with `rhs_eq=true, lhs_eq=false`: mini's `ind(p⃗)`
  matches, and the `⟦T p⃗⟧` does not, because it is spelling three.

**So the row is worth −1, not −35.** The −35 is the value of the ι rule
*completing*, and the named decline is the first of at least three consecutive
matching points that all fail for the same reason.

### 10.4 The −35 is not behind a wall, it is behind a **layer** — measured at 0

*This section previously scoped the `np > 0` type-former adoption as the tranche
that would reach the −35, and warned only against pricing it at −47. It was
built behind a switch and measured, as it told the reader to do. **It works, and
it is worth zero.** Corrected here in place, with what the probe found.*

`fire_dep`'s parameterised path is a **layer** of constructions each written for
`np == 0`. Clearing one is small, correct, and moves the entire 37-gap sub-tree
onto the next one intact. Three walls were traversed on `076_listRecReduction`:

| # | wall | cause | fix | `076` | sub-tree after |
| --: | --- | --- | --- | ---: | ---: |
| 1 | `gen_ty_bridge`: `⟦T p⃗⟧` is a third spelling | `gen_ty_nest` mints its own abbreviation at `np > 0` | adopt mini's carrier, contracting it at the parameters through `adopted_lam_step` (~75 lines) | 45 | 37 |
| 2 | `iota: mini's nullary constructor abbreviation is not an equation` | `dep_minor_typed` does `inst_all(ax, &[])`; mini publishes `∀p. ⟦cᵢ⟧(p) = …` | `inst_all(ax, ps)` — **one line**, and identical at `np == 0` | 45 | 37 |
| 3 | `iota: the nullary minor is typed at another constructor` | the `from != mdom` check, same class again | not attempted | 45 | 37 |

**Every row is 45.** At each stage the origin's own count is 5, its sub-tree 37,
and `NANODA_ASSUME` on it still takes the file 45 → 10. The tranche does not
shrink as walls fall; it *migrates*. Across both populations the whole
configuration — adoption, the one-liner, and dropping the recogniser exclusion
so `List.rec` reaches `fire_dep` at all — moves **nothing**: exports 168,
every fixture identical.

**The wiring itself is confirmed available**, which is the one durable result
here. Mini's carrier *is* a registered lambda graph in the shared store: the
`np > 0` adoption contracts it at the parameter variables, lands on `ind(p⃗)`,
and produces `⊢ H_p → app-spine(⟦T⟧,p⃗) = ind(p⃗)` with no decline, for `Prod`
(np = 2) and `List` (np = 1) alike. `adopted_lam_step` is exactly mini's
`beta_spine` step and needs nothing new. So whoever finally takes this layer
does not have to rediscover that; they have to get through *all* of it.

Two implementation notes the probe settled, so the next attempt does not
re-derive them:

* the adopted nest must carry `head_sym: None`. `adopt_ty_nest` rebuilds the
  head as `mk(head_sym, vec![])` — nullary — and mini's carrier is a graph
  symbol applied to its domain, so the cross-backend share must be refused
  rather than taken;
* `head_ax` has no honest filler at `np > 0` — mini's carrier *is* the outermost
  graph, so there is no `⟦T⟧ = <graph>` step. `Thm::eq_refl(head)` is truthful
  and weakest-safe; every reader wanting the stronger form checks the shape and
  declines.

**What this says about scheduling.** Do not take this as a tranche on the
strength of the −35. The correct next act is a *census of the layer*: walk
`fire_dep` and count the constructions that assume `np == 0`, before writing
any of them.

**That census was taken on 2026-08-15 and the count is twelve — ten hard sites
and two latent, of which seven were unknown when this paragraph was written.**
All three walls named above are still present and unfixed. The full enumeration,
with `file:line` and fix size for each, is in `ORIGIN-RANKING.md`, "Question (b),
answered". Six of the ten are one-liners or small; the cost is two substantial
pieces — the `gen_ty_nest` carrier adoption (#1 above) and a rewrite of
`mini_ctor_spine_bridge` into the parameterised form its already-general sibling
`ctor_spine_bridge` has. Roughly half of `fire_dep`'s parameterised path needs
nothing at all.

**And the scheduling answer is no.** Because the sub-tree migrates rather than
shrinking — every row of the table above is 45 — there is **no partial credit
anywhere in this layer**: the payoff is 0 until all ten hard sites are done, and
then it is −35, on one file, in a population that is 168 of 10 645 gaps
tree-wide. The same re-census priced a `Nat` bridge at **−3 780** on
`init-prelude`. This layer should not be started. Cheapest useful act if anyone
touches it anyway: land wall #2 (`inst_all(ax, ps)`, one line) and see whether
wall #3 disappears with it — the only sub-question in the layer with an answer
shorter than the whole tranche.


### 10.5 What landed instead

The census turned up an adjacent defect worth taking on its own terms:
`gen_ind_build`'s adoption clause required `params == 0`, so TG built a **second
carrier** for parameterised declarations mini had already published and
`interp` was already using. `mini_adoptable_translation_at` splits the
predicate — the readiness mirror stays narrow, adoption widens to `params > 0`
declarations no hand-written recogniser owns. **Exports 172 → 168**, all of it
`074_prodRecEqns` 14 → 10; every fixture byte-identical.

Two guard rails, both measured rather than reasoned:

* widening the *shared* predicate takes `proj_reduced_subject` 2 → 8 and
  `proj_reduced_carrier` 13 → 169. `wants_proj_red_iota` is a **prediction**, and
  readying a structure whose ι cannot be certified trades a projection gap for
  an ι one;
* the recogniser exclusion is what keeps `076` at 45 rather than 48.

And one reporting defect, which is `TEST-INVENTORY.md` §4.5 in reporting code.
The degenerate and dependent rows all live in `gen_report`, whose early return
asked only about the **general** path. Adoption returns before `GEN_BUILT` is
incremented and notes no `Decline`, so a fixture that adopts every carrier lost
the entire section — the dependent arm fired and printed nothing, and
`unified_cli`'s `ι sites the DEPENDENT rule computed` assertion read
"no report row" instead of a wrong number. It had been witnessing only runs in
which the general path had also been consulted. The gate now counts the arms
whose rows it guards.
