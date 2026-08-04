# The interpretation's unwitnessed decisions — an audit of `mini/`

*2026-08-04. Sweep of `isDefEq`/conversion, `infer` and `whnf` in `mini/` for
steps whose validity depends on a side condition that **no certificate
demands**. Not a threading census (that is `THREADING-CENSUS.md`, and it is
about `checker/`): this asks a narrower and sharper question.*

## 0. The question, and why it is not the obvious one

`Ev` is `Proved(Thm) | Gap(Gap)` with no third state, gaps propagate
monotonically through `and_then`/`zip`, `Gap::EndpointDrift` exists for a
certificate that arrived somewhere other than the walk did, and composition
itself fails when endpoints do not match. So the naive worry — *a certificate
about the wrong thing slips through* — is already handled and is not what this
audit is about.

The risk that survives all of that is a **consistently wrong interpretation**.
`⟦·⟧` is a function mini *computes*; certificates witness facts *about its
outputs*. If `⟦·⟧` takes a decision that no certificate witnesses, every
downstream theorem is a true statement about the wrong interpretation, they all
agree with each other, and nothing trips. The clean example is proof
irrelevance: `⊢ • = •` is a true theorem and nothing is wrong with it; the
unwitnessed step happened earlier, in deciding that the term *is a proof*.

So each step is asked three questions:

1. what must be true for it to be valid in the model?
2. is that demanded anywhere — threaded, checked against a certificate, or
   established by an `_ev` form?
3. if not, is it **dispatch** (the decision only picks which construction to
   attempt, so a wrong pick yields a `Gap`) or **load-bearing for `⟦·⟧`** (the
   decision changes what the interpretation *is*)?

**One asymmetry organises the whole table.** The dangerous direction of every
`Prop` classifier is the **`true`** branch. Calling a `Type` a `Prop` collapses
a family to `•` and makes `⟦a⟧ = ⟦b⟧` derivable for terms that are not equal.
The reverse — calling a `Prop` a `Type` — interprets a truth value as a
dependent product, which loses derivability (proof irrelevance stops composing)
but collapses nothing. That is why the `false` branches below are dispatch even
where they are unwitnessed, and why every `true` branch is checked one by one.

## 1. The table, ordered by risk

| # | site | the step | side condition | supplied by | kind | fix cost / `_ev` exists? | end-to-end testable? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **L1** | `mini/src/kernel.rs:1716` (`pi_evidence`) | `if n2 == 0` selects `⟦Π x:A.B⟧ = [∀x∈⟦A⟧. •∈⟦B⟧]` (a truth value) over `∏_{x∈⟦A⟧}⟦B⟧` | `lvl(Γ ⊢ B) = 0`, i.e. `⟦B⟧ ∈ U₀` | **nothing.** `n2` is `ground::eval` of `as_sort(whnf(infer B).ty)`. `cond_typing` is *unconditional* by design and says so (`interp.rs:2757–2760`). The witness `⟦B⟧ ∈ ⟦Sort l2⟧` is in hand as `tb.ev` (transported at `kernel.rs:1438`) and is **not referenced anywhere on the branch** (`1716–1727`) | **load-bearing** | 3 lines, no `derived/` work: require `tb.ev.mem_set() == Some(ip.sort(0))` on the branch. No `_ev` form to write — the evidence is already an argument of the function | **no** (see §2); the check landing at zero across the corpus is the ratchet |
| **L2** | `mini/src/kernel.rs:1395` (`infer_type`, `App`) | `body_clause(&out_ty) == Prop` selects `tm = •` over `app(⟦f⟧,⟦a⟧)` | `sort(Γ ⊢ f a) = 0` | **nothing at this node.** The *certificate* on the same node is built from `shape` (`1383–1387`), read off `⟦type of f⟧` by `as_pi` — a different source. `cond_app` concludes about `•`, `dprod_app` about `app(⟦f⟧,⟦a⟧)`; nothing compares the certificate's subject with `tm` | **load-bearing**, and the one place mini has *two* classifiers for one clause — which `kernel.rs:2136–2138` says must not happen | 3 lines for the subject check (`ev`'s `as_mem().0 == tm`, else gap). Reading the clause off `shape` instead is the deeper fix but needs care: `shape` is `None` whenever the function's *evidence* gapped, where `body_clause` still yields a usable `•` | **no** for the wrong branch; the subject check itself is exercised by every application in the corpus |
| **L3** | `mini/src/zoneb.rs:2951–2969` (`store`) | `ConstInterp { term: t.tm, typing: Sealed(t.ev) }` for `⟦T⟧`/`⟦T.ctor⟧`/`⟦T.rec⟧` | the sealed theorem's subject **is** `term` | **nothing.** Contrast the *declaration* funnel (`ledger.rs:623–635`), which gets it for free: `retarget_subject` refuses unless the membership's subject is `⟦val⟧` (`interp.rs:2746`). Zone B has no such step | **load-bearing** (it is the store the corpus reads by key) — but holds today *by construction*, since `lam_evidence` builds `tm` and `ev` from one site. A guard, not a live defect | one line before `put_const`. No `_ev` form needed | **no**; unit test + a zero-firings ratchet |
| **L4** | `mini/src/kernel.rs:1532–1539` + `mini/src/proj_prop.rs:572` (`field_in_u0`) | the proof route is tried first and, on success, `⟦proj[T,j] x⟧ = •` | §6.2 wants `sort(Γ ⊢ proj) = 0` — the *Lean* sort of the field | **a different, weaker condition**: `field_in_u0` demands `⊢ ⟦βⱼ⟧ ∈ U₀` and **deliberately accepts a second route** — the field type's own declaration's carrier being in `U₀` even when its Lean sort is not `Prop` (`PUnit.{1}`; argued at `proj_prop.rs:549–571`) | **load-bearing**, divergence documented and one-directional | either accept and keep the argument, or gate the route on `is_prop_ev(&ty)` — **the `_ev` form exists**. The second changes which declarations type, so it needs a corpus run | **yes** — `structure W : Type where u : PUnit.{1}`. No corpus member reaches it today; that is the test to write with the fix |
| **L5** | `mini/src/kernel.rs:1793–1795` (`lam_evidence`) | on a domain that did not interpret, the λ still gets `tm = Some(•)` while `ev` is a `Gap` | `sort(Γ ⊢ λ…) = 0` | the `prop` flag from `is_prop_ev` — which *is* witnessed, but the witness is discarded with the rest of the evidence on this path | load-bearing but **inert**: `Ev::Gap` cannot compose, so no certificate is ever built from the term; it can only propagate gaps | none proposed — recorded because it is the one place a term is minted with nothing behind it | n/a |
| **L6** | `mini/src/kernel.rs:2454` (`def_eq_ev`) | the drift guard `t1.tm != tm1 ⇒ EndpointDrift` runs for `e1` and **not** for `e2` | `tm2 = ⟦e2⟧` | nothing names it; a wrong `tm2` produces a true theorem about the term the caller named, which then fails to compose at `retarget_set` (`interp.rs:2224`) | **dispatch** (robustness, not interpretation) | 3 lines mirroring `2454`, after `infer_type(e2)` — which `proof_irrel_ev` already computes | no; the value is a named gap instead of a composition failure |

## 2. Why L1 and L2 are not end-to-end testable, stated plainly

`l2` and `body_clause` are Lean's own sort, computed by mini's own
`infer`/`whnf`/`as_sort`. There is no Lean declaration that makes them come out
wrong — a Lean term either has a `Prop` codomain or it does not. What L1 and L2
defend against is a **defect in mini's inference** silently redirecting `⟦·⟧`,
which is exactly the class the owner's invariant is aimed at and exactly the
class no end-to-end run can exhibit. So the fixes are unit-testable (hand
`pi_evidence` a `Typing` whose evidence disagrees with `l2`) and their
end-to-end content is negative: `constEv` stays 218/218 and the new gap variant
counts zero. That is a ratchet, not a test case, and it should land as one.

L4 is the exception and is the only entry in the table with a real Lean witness.

## 3. Dispatch — the population that is fine, with the reason

* **The K-rule gate**, `is_def_eq(major_ty, kt)` (`kernel.rs:685`). Acceptance
  only. On the `direct` route the certificate is `nest_iota`'s β chain, which is
  *unconditional on the major* by construction (`kernel.rs:1165–1170`) and whose
  endpoint is checked against `infer_type(rhs).tm` (`1214–1217`). A wrong K
  decision moves acceptance — the fidelity gate's business — never a
  certificate.
* **The four ι routes** (`quot_iota`, `rec_acc_iota`, `iota_ix_dep`, `iota_dep`,
  `kernel.rs:794–865`), selected by primitive name, `direct::Clause` and
  `num_indices`. Each returns a real theorem or `Err`; a wrong table is
  `Gap::Iota`. The comments at `804–812` record `118`'s twelve gapped
  conversions as exactly this failure mode — gaps, as predicted.
* **`try_structure_eta` / `try_fun_eta`** (`2339`, `2369`) and their certifiers
  (`2740–2803`). The probe decides acceptance; the certificate is built second
  and its failure is a gap, never a verdict. Stated in place at `2748–2753`.
* **Eight `is_prop(&site.codomain)` calls in the recursor modules**
  (`rec_dep.rs:362`, `rec_prop.rs:248`, `rec_ix_dep.rs:189`,
  `rec_ix_prop.rs:159`, `rec_trunc.rs:175`, `rec_s_ix.rs:221`,
  `rec_acc.rs:190`, `rec_acc_value.rs:114`). Each is a *cross-check* against the
  recursor's declared eliminator level (`prop != (site.u1 == 0)` ⇒ gap,
  `rec_prop.rs:366`, `rec_dep.rs:366`), and the construction it selects must
  land in `goal = infer_type(&site.codomain).tm`, computed independently. Wrong
  choice ⇒ the kernel theorem does not match the goal ⇒ gap.
* **`is_prop_or_unit_ev`'s unit-like branch** (`2304–2309`). The environment's
  `is_unit` flag gates acceptance; the certificate still has to come from
  `unit_like::certify` (`2493`) and its absence is a gap.
* **`is_prop_ev` at `1468`, `1927`, `2482` and `is_prop_or_unit_ev` at `2457` —
  witnessed, and this is the model to copy.** The witness is consumed by
  `point_of_proof`, which refuses unless the type's membership is literally
  `mem(set, sort(0))` (`interp.rs:1512`). The λ `Prop` clause, defeq's proof
  irrelevance and `rec_acc_iota.rs:171` are all closed by that one test. L1 is
  the same decision one level up with the same evidence in hand and no test.
* **Zeta and `NatLit` in `whnf`** (`956–961`, `1031–1048`). Both carry `cur_tm`
  across with no leg, and both are *identities* of `⟦·⟧` rather than decisions:
  `nat_unfold` is literally shared between the reduction and the interpretation
  (`1572–1579`), and the `let` identity is spelled `subst(body, val)` in both
  arms (`960`, `1494`).
* **Literal/`Nat` acceleration: the population is empty.** `nat_unfold` refuses
  above 10 and there is no arithmetic fast path anywhere in `mini/`
  (`grep -n "Nat.add\|nat_lit\|NatLit" mini/src/kernel.rs` — four hits, all the
  unary expansion). `StrLit` interprets to nothing and says so.
* **`split_app` returning `(None,None)`** (`1061`) for a term that is not an
  `app`: an absence, not a decision. Downstream gets gaps.
* **`def_eq_struct`'s `same` shortcut** (`2645`) and the `Sort`/`Const` arms
  (`2657`, `2695`): reflexivity of an *identical* term, with the acceptance
  recursion (`assert_level_eq`, the sub-`def_eq`s) running first in every arm
  (`2567`, `2658`, `2718`).
* **Congruence at `App` and `Proj`.** In a set-theoretic target `⟦a⟧ = ⟦b⟧` is
  untyped set equality, so ordinary congruence needs no transport and no typing
  premise. Not a gap.
* **The `false` branch of every classifier**, by the asymmetry in §0: it is the
  non-collapsing direction, and its cost is lost derivability, not a false
  conclusion.

**The strongest positive result of the audit**, worth stating because it is what
the funnel was supposed to do: the declaration store's `term` and its `typing`
*are* checked against each other, and not by an explicit test but by the shape
of the derivation — `ledger.rs:623` moves the value's membership onto the
abbreviation with `retarget_subject`, and `interp.rs:2746` refuses unless the
membership's subject is `⟦val⟧`. The axiom arm makes the same point in prose at
`ledger.rs:656–661`. Zone B is the one funnel that does not get this (L3).

## 4. What the notes did not survive

Three doc claims were found false against the code and **corrected in place**:

1. `mini/src/proj_prop.rs:41–44` — *"the `Expr::Proj` arm … returns `tm: None`
   unconditionally with no `is_prop` test"*, while `kernel.rs:1534` returns
   `proj_prop::point_of(self)`. `git blame` puts the sentence in `9e60a27`, the
   same commit that added the `point_of` call: born stale.
2. `mini/src/interp.rs:2346–2347` — *"the clause … has to be decided by
   `Checker::body_clause`"*. `cond_site`'s only callers are `pi_evidence` (a
   level numeral, L1) and `lam_evidence` (`is_prop_ev`); `body_clause` never
   reaches it.
3. `mini/src/ledger.rs:47–48` — *"every clause is decided by
   `body_clause`/`term_clause`"*. `term_clause` has **zero** production callers
   in `mini/` (repo-wide grep: `kernel.rs:2139` definition plus four tests; every
   live caller is `checker/src/tg.rs`). The paragraph's point — that all of this
   is inference and not search — is right; the two function names were not.
   *(This third correction is in the working tree but **not** in this audit's
   commit: `mini/src/ledger.rs` carries another agent's 229-line change at the
   same moment, and `--only` on that path would have swept it in.)*

## 5. Method — how the population was enumerated

Complete greps, not samples; each is reproducible.

* **Classifier sites**, the spine of the audit:
  `grep -rn "is_prop\b\|is_prop(\|body_clause\|term_clause\|is_prop_ev\|is_prop_or_unit_ev\|Clause::Prop" mini/src --include=*.rs`
  — 17 production call sites (the rest are docs and tests): `kernel.rs` 1395,
  1468, 1927, 2200, 2209, 2221, 2457, 2482; the eight `rec_*` codomain checks;
  `rec_acc_iota.rs:171`.
* **Every mint of `•` as an interpretation**:
  `grep -rn "point()" mini/src/kernel.rs mini/src/interp.rs mini/src/proj_prop.rs`
  — four in the checker: `kernel.rs` 1396 (L2), 1794 (L5), 1803 (witnessed), and
  `proj_prop.rs:546` reached from `kernel.rs:1534` (L4).
* **Every write to the interpretation store**:
  `grep -rn "put_const\|ConstInterp {" mini/src` — two funnels, `zoneb.rs:2967`
  (L3) and `ledger.rs:640–703` (checked, §3).
* **Arms read end to end**: `infer_type`'s ten (`kernel.rs:1337–1569`); `whnf`'s
  twelve steps (`596–1053`: delta, K-ι direct and declining, the four derived ι
  routes, stuck-recursor, app-peel, β, ζ, proj-of-ctor, `NatLit`, default);
  `def_eq`'s eleven (proof-irrelevance gate and unit-like, plus the eight
  structural arms and the two ηs, `2443–2808`); and the evidence builders
  `app_evidence`/`pi_evidence`/`lam_evidence`/`binder_cong` (`1617–1889`,
  `2547–2627`).

**Roughly 50 steps examined; 4 load-bearing findings (L1–L4), 2 recorded but
inert (L5–L6), the remainder dispatch.** The three algorithms are, on this
question, in much better shape than the brief's framing allows for — the λ
clause, defeq's proof irrelevance and the declaration funnel are all genuinely
witnessed, and `point_of_proof`'s `mem(set, sort(0))` test is doing most of that
work single-handed. What L1 says is that the *same* test is missing at the `Π`
clause, with the *same* evidence already in the function's arguments.

## 6. The "5 186" trail, since the brief asked

`conv.rs:247`, `scope.rs:428`, `kernel.rs:1309` and `kernel.rs:1610` all cite
"the case that is 5 186 of nanoda's `has_type` misses". Read: they are one
claim, not four, and it is `THREADING-CENSUS.md` §3.1 — nanoda's `has_type`
search is entered with `assms = []` even under open binders, so a `bvar`'s
typing has to be guessed by `local_premises` scanning for `Local` nodes, and
5 186 of those misses are "a local at the top level". Mini's answer is that the
scope stack *is* that information: `kernel.rs:1343` reads it at one vector
index, and `conv.rs`/`scope.rs` pin the property with unit tests. There is no
outstanding item behind those comments; they are a completed migration's
epitaph, and they are accurate.
