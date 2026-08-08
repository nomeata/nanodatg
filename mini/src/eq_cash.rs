//! **A Lean `Eq` theorem, cashed into the TG equation it asserts** —
//! `Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧` from a proof of `Eq α lhs rhs`.
//!
//! # Interface
//!
//! ```text
//! eq_cash::cash(checker, proof_expr) -> Result<Cashed, Gap>
//! Cashed { eq: Thm, lhs: Term, rhs: Term }
//! ```
//!
//! `proof_expr` is a **fully applied** proof term whose type is an equation:
//! for a nested inductive's ι rule that is `iotaNode m1 m2 lf nd nl cs a`, the
//! rule theorem `modelgen` splices into the export, applied to the site's own
//! arguments.
//! What comes back is one kernel theorem about the two sides' interpretations,
//! together with those two terms, so that a caller can compare its own
//! endpoints against what the equation actually says instead of trusting a
//! name.
//!
//! # Why an equation is reachable from a *typing* at all
//!
//! `⟦Eq α a b⟧` is not opaque. §6.2's direct clause sends it to the conditional
//! singleton `eq_set(⟦a⟧,⟦b⟧) = [⟦a⟧ = ⟦b⟧]` ([`crate::direct`]'s
//! `Clause::Eq`), whose characteristic theorem is `Direct::eq_ax`; so a proof's
//! typing `⊢ • ∈ ⟦Eq α a b⟧` **is** the assertion `⟦a⟧ = ⟦b⟧` behind one
//! `derived::prop::cond_elim`. Nothing here inspects the proof term: the whole
//! content is that a Lean proof's *typing* and a TG *equation* are the same
//! judgement under the interpretation.
//!
//! # What the binders cost, measured against `rcompat_at`
//!
//! [`crate::quot_classes`]'s `rcompat_at` is the working precedent — the same
//! pipeline, on `Quot.lift`'s compatibility hypothesis — and it peels
//! [`PiShape::Prop`](crate::interp::PiShape) three times by hand, opening a
//! scope and calling [`Interp::cond_app`](crate::interp::Interp::cond_app) at
//! each level. **None of that peeling is repeated here, and the reason is that
//! `h` is a `bvar` there and a constant here.** `rcompat_at`'s hypothesis is a
//! binder of the eliminator's own nest, so there is no expression to infer and
//! the instantiation has to be performed on the certificate; an ι rule is a
//! *declared* theorem, so the caller can simply apply it, and
//! `Checker::infer_type`'s `App` arm already runs `cond_app` once per argument
//! — a `∀` into `Prop` takes §6.2's `cond` clause whatever its domain's sort
//! is, so all six or seven binders of a rule are `PiShape::Prop` and the arm
//! that fires is the same one.
//!
//! So the composed chain is the *last three* steps of `rcompat_at` and none of
//! the first: the β chain down `⟦Eq.{v}⟧`'s stored nest, `retarget_set` onto
//! its bottom, and `cond_elim`. Two consequences worth having in view:
//!
//! * the arguments' typings are inferred rather than held, which is
//!   [`crate::quot_iota`]'s trade and is made for the same reason — `whnf`
//!   holds expressions, not memberships;
//! * a caller that *does* hold a binder rather than an expression — a scope
//!   variable — is not served by this and would need `rcompat_at`'s shape. No
//!   such caller exists: the dispatch arm's arguments are the redex's own.
//!
//! # Scope: three qualifications, all real
//!
//! 1. **Per ground σ.** The rule's own levels must evaluate to numerals, as
//!    every store lookup in mini does.
//! 2. **Hypothetical under whatever scopes the caller opened.** The result is a
//!    sequent: applied to closed arguments it is closed, and applied to a
//!    telescope's binders it carries that telescope's memberships in `Γ`. It is
//!    returned as a [`Thm`] and never sealed here, so [`crate::ev::Sealed`]'s
//!    funnel is what refuses to persist a hypothetical one.
//! 3. **Only as available as the proof's own typing.** If `⊢ • ∈ ⟦Eq α a b⟧`
//!    is missing there is nothing to cash and the *proof's* gap is what comes
//!    back, per MINI-DESIGN.md §0.4.
//!
//! # What the nested model's four ι rules do, measured
//!
//! `mini/tests/fixtures/nested_model.lean` states all four of `Tree`'s ι rules
//! about its **defined** recursors, and this module cashes **all four**:
//!
//! | rule | proof | cashes |
//! | --- | --- | --- |
//! | `iotaLeaf` | `Eq.refl` | **yes** — the block's own ι rule, unchanged |
//! | `iota1Nil` | `Eq.refl` | **yes** — the transport collapses on `List.nil` |
//! | `iotaNode` | `transportNode` applied | **yes** |
//! | `iota1Cons` | `transportCons` applied | **yes** |
//!
//! **The split was never the `rfl`/not-`rfl` split**, and reading it as one
//! would have misplaced the work: a non-`rfl` proof cashes — `rcompat_at`'s
//! occupant is an arbitrary proof term, and the fast test below cashes
//! `myCongr`, an `Eq.rec`. What stopped the bottom two was that the run left
//! their own constant typings uncertified, and nothing about *that* was ever
//! reachable from this module.
//!
//! *(This table read two `yes`es and two `no`s across three rounds, under three
//! different accounts of what was missing, and every one of them was about a
//! residual outside this file.
//!
//! **First**: four residuals — `transportNode`, `transportCons` and the two
//! rules those are applied in — with "the two lemmas are the root; the two rules
//! only inherit it". `#90(b)` closed the lemmas' typings and the count went
//! 4 → 2, and the two rules did **not** move with them. The inheritance reading
//! was wrong.
//!
//! **Second**: the two rules' own trail, read as 2 675 mints at
//! `def_eq_struct`'s `Const` arm and 918 at `delta_evidence` and scoped as a
//! second `#90(b)`. Both counts are real and neither is the residual: they are
//! the **acceptance** walk, which mints `no-endpoint` at those two lines
//! because it hands in no endpoints and wants none, and there were 4 108 of them
//! against a `TRAIL_CAP` of 4 096, so the pair overflowed and evicted the
//! origin. [`crate::blocker::Quiet`] is what stopped an unasked-for conversion
//! filing, and the same pair's trail is **17** mints with it.
//!
//! **Third**, and this one is the answer: [`crate::kernel::Checker::whnf_conv`]
//! on a **proof-valued spine**, which this note has recorded below as open and
//! unreachable since `#90(b)`. It is reachable, `iotaNode` is what reaches it,
//! and closing it takes `nested_model` from 39/41 constant typings to 41/41.)*
//!
//! **The two lemmas still do not cash**, and that is now a fact about them
//! rather than about the rules. With their typings in hand [`cash`] gets four
//! steps further and stops at `conv-compose(eq-cash-beta)` — `Interp::beta_spine`
//! refusing `⟦Eq.{v}⟧`'s nest at these three arguments, whose type argument is
//! a *variable* application `m (N.s b)` where every input that cashed before
//! them had a constant there. **Nothing is waiting on it**: `crate::iota_model`
//! calls [`cash_stmt`] on the *rule's* statement and never on a lemma's, so the
//! four rows above are what the dispatch arm reads. It is a real residual of
//! this module and it is not on anyone's path.
//!
//! # The generated population, and why no test enumerates it
//!
//! `nested_model.lean` is hand-written and has four rules;
//! `modelgen` now generates them into the export, and
//! [`crate::nested_splice::Recognised::model_iota`] is
//! `(member, the export's constructor, the theorem)` for **36** rules over the
//! eight nested declarations in the fixture directory — `Tree` 4, `PT α` 4,
//! `BTree` 6, `DTree` 6, and the `nested_shapes` set. That is the real
//! population, and it carries three shapes the hand-written one does not: a
//! parameter telescope, a second mimic, and depth.
//!
//! **Nothing here is keyed to `nested_model`.** [`cash`] takes an applied proof
//! expression and asks the store; it is already the route for all 36, and the
//! tests below run it over four different exports to say so.
//!
//! What is *not* here is a test that enumerates them, and the reason is cost
//! rather than doubt. Cashing a generated rule needs that tower's
//! `Ledger::run`, not merely its `kernel::add`, and on `nested_model` the ratio
//! is about three seconds of acceptance to **two minutes** of interpretation.
//! The generated towers cost 10.3 s (`Tree`) to 91.1 s (`DTree`) on acceptance
//! *alone*, so an enumerating test is hours, not minutes, and would land in
//! `ci/check.sh`. The fast inner loop is the hand-written fixture and
//! `transport_through_eq_rec`; sizing what the generated set actually cashes
//! belongs with whoever wires the dispatch arm, who has to pay the
//! interpretation pass anyway.
//!
//! # The transport residual, what it was, and the hypothesis it refuted
//!
//! `mini/tests/fixtures/transport_through_eq_rec.lean` is `transportNode` with
//! the nesting taken out — **21 509 conversions against `nested_model`'s
//! 7 261 645** — and it was the small witness for the two lemmas' residual.
//! **The fixture now certifies whole** (`gapped 0`, `constEv 2/2`, 12 705
//! conversions), and `transportNode`/`transportCons` carry their constant
//! typings. Cashing them is a separate step and still declines; see the
//! qualification under the table above.
//!
//! The first hypothesis about it was that a **δ step on a proof** has no
//! endpoints — §6.2 sends a proof to `•`, and `Checker::split_app` cannot take
//! `•` apart, so `delta_evidence` mints `NoEndpoint` at `kernel.rs`'s `Const`
//! node. `mini/tests/fixtures/delta_inside_a_proof.lean` is that prediction as
//! an export and it **certifies with `gapped = 0`**: the major's own conversion
//! is closed by proof irrelevance before anything needs the δ leg. Both files
//! are pinned by a test here, and the pair was the finding: one shape certified
//! and one did not, so the reason was not "inside a proof".
//!
//! **What it actually was is one line of `Checker::def_eq_struct`.** The pair
//! that gapped is `Eq.rec … (myCongr a b h)` compared with **itself** — the
//! declared type against the inferred one, identical after the motive's β. Its
//! two interpretations are the same `Term`, so the equation owed is
//! `⊢ ⟦e⟧ = ⟦e⟧` and reflexivity discharges it. Every structural arm of
//! `def_eq_struct` answers that with `refl()` except `App`/`App`, which
//! descended into `app_cong` of its two halves unconditionally — and the half
//! holding the major could not state its own endpoints, because the major *is*
//! a proof and `split_app` hands back `None` on `•`. So a certificate that was
//! already in hand was replaced by a congruence that could not be built. The
//! δ-on-a-proof mechanism is real; it was never load-bearing on its own, and
//! it stopped being reachable here once the arm took the decision.
//!
//! The endpoint loss inside `whnf_conv` on a proof-valued spine is what
//! remained, and **it is closed**:
//! [`crate::kernel::Checker::proof_point_leg`]. `⟦e⟧` and `⟦whnf e⟧` are both
//! `•`, so the leg is `eq_refl •`, and the walk could not say so because it
//! never interpreted the reduct. Its small witness is
//! `mini/tests/fixtures/whnf_of_a_proof.lean` at **8 393 conversions**, and its
//! big one is `iotaNode` here.
//!
//! *(This section read "nothing on the corpus or in the fixture directory
//! reaches it now, and a pair whose two sides differ *and* whose reduction runs
//! through a proof would". The second half was exactly right and the first was
//! wrong about a file two lines above it: `nested_model`'s `iotaNode` is that
//! pair. `treeRec … (treeNode l)` δι-reduces to a transport along
//! `packUnpack (pack l)` where the theorem states one along
//! `congrPack (unpack (pack l)) l (unpackPack l)`, so the two sides differ and
//! the reduction runs through three proofs. What hid it is that the *trail*
//! named `def_eq_struct`'s `Const` arm and `delta_evidence` — the acceptance
//! walk, 4 108 mints against a `TRAIL_CAP` of 4 096, with the origin evicted.
//! [`crate::blocker::Quiet`] is the instrument repair and the same trail is 17
//! mints with it.)*
//!
//! # `refl_proved` is the line to widen, and this is the measurement
//!
//! `nested_splice.rs`'s seeding note left the transported ι rules out because
//! "their proofs go through `#90(b)`, so their own constant typings are
//! `no-endpoint`", and said that when it lands `refl_proved` is the one line to
//! widen. `#90(b)` landed and the guard **still** should not have moved, because
//! the rules' own residual was the proof-valued spine and not the lemmas.
//! Measured on `nested_iota_arm` by widening the guard behind an environment
//! variable, three rounds apart:
//!
//! ```text
//!                                conversions   time   uncertified
//! seeded, before #90(b)           13 441 025   3m35   4 const typings, all no-endpoint
//! seeded, after  #90(b)            5 906 744   2m41   4 const typings, all no-endpoint
//! seeded, with the proof leg       6 031 316   5m     none — 39/39, gapped 0
//! not seeded, with the proof leg     469 765    20s   2 const typings, both "no rule"
//! ```
//!
//! So the guard moves now, and what it buys is the last two rules of the arm
//! and the last seven of `nested_iota`. The cost is real and is stated at the
//! seeding site: about **13× the conversions** on a file that applies a nested
//! recursor. Nothing else in the repository pays it — a file with no nested
//! declaration splices no model, and the tutorial corpus is bit-identical
//! either way at 829 661 conversions.
//!
//! # This module is **not** a black box, and the allowlist does not move
//!
//! `modelgen` generates the model of a nested declaration's
//! primitives — carrier, `pack`/`unpack`, round trips, recursors, and the ι
//! rules — as ordinary Lean declarations, and names no [`Thm`]: it is on
//! `ci/check-mutual-blackbox.sh`'s three-file allowlist and belongs there,
//! because "the encoding could be written in Lean world" is the claim that
//! makes the nested repeat cheap.
//!
//! **This file names `Thm` freely and must never claim that header.** The split
//! is deliberate and it is where the boundary should be: *generation* stays
//! black-box, *cashing* is the evidence side by construction — its output is a
//! certificate. Adding this file to `FILES` in that script would make the check
//! fail on its first line, which is the correct outcome and is why the
//! allowlist is a literal list rather than a directory glob.
//!
//! # What the tests kill, measured
//!
//! Seven mutations of [`cash`], against the five fast tests (the model's table
//! is two minutes a mutant and adds nothing the route needs):
//!
//! ```text
//! KILLED   report the two sides swapped
//! KILLED   invent a reason instead of propagating the proof's
//! KILLED   drop the head-is-`Eq` check
//! KILLED   skip the retarget onto the β bottom
//! KILLED   swap the two arguments the β chain consumes
//! SURVIVED drop the bottom-sides guard
//! SURVIVED drop the final conclusion check
//! ```
//!
//! Two survive and both are guards **no well-typed input can reach**; the note
//! at each says why it is kept anyway, and a third such guard was *deleted*
//! rather than excused. The head-is-`Eq` mutant needed an input the obvious
//! fixture does not have — a statement that is a three-argument constant
//! application and is not `Eq` — which is why the test for it borrows
//! `indexed_two_params`; `N.z`, whose type is a constant applied to nothing,
//! fails on arity and leaves the check untested.
//!
//! # Never an assumption
//!
//! Lean 3's `define_theorem` adds a failed proof's *statement* as an axiom
//! (`LEAN3-INDUCTIVE-COMPILER.md`; `nested.cpp:370–383`), so a rule its
//! elaborator could not prove became one anyway. There is no such path here and
//! there must not be one: every exit below is either a [`Thm`] whose conclusion
//! has been compared against `Formula::eq(lhs, rhs)` or a [`Gap`]. Nothing in
//! this module constructs a theorem from a statement.

use kernel::{FnSym, Formula, Term, Thm};

use crate::ev::Gap;
use crate::expr::{get_app, Expr, Name, E};
use crate::interp::Interp;
use crate::kernel::Checker;

/// The equation a Lean `Eq` theorem cashes to, with the two sides it is about.
///
/// The sides are returned because a consumer's own endpoints are the thing that
/// has to match: `eq` is a theorem about `lhs` and `rhs` and *saying so* is
/// what lets a dispatch arm refuse a rule that is about other terms. Reading
/// them back off `eq.concl()` would be the same two terms; handing them over
/// spares every caller the destructuring and the `expect`.
#[derive(Debug, Clone)]
pub struct Cashed {
    /// `Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧`. **`Γ` may be non-empty** — see the module note's
    /// qualification 2; read `hyps()` before persisting.
    pub eq: Thm,
    /// `⟦lhs⟧`.
    pub lhs: Term,
    /// `⟦rhs⟧`.
    pub rhs: Term,
}

/// `Eq`, as the direct clause knows it. A statement headed by anything else is
/// not this module's business and says so rather than guessing.
fn eq_name() -> Name { Name::simple("Eq") }

/// **`Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧`** from a fully applied Lean proof of `Eq α lhs rhs`.
///
/// Every shape is checked rather than assumed — that the statement really is an
/// `Eq` at one ground level, that the β chain's left endpoint is the very set
/// the proof's typing is about (by `retarget_set`'s own refusal, not by a
/// second comparison here — see step 4), that the chain's bottom is an `eq_set`
/// and at which two arguments, and that the final conclusion is the equation
/// claimed. A mismatch is a [`Gap`] with its own reason; it is never a weaker
/// theorem and never an assumption.
pub fn cash(c: &mut Checker<'_, '_>, proof: &E) -> Result<Cashed, Gap> {
    // ── 1. the proof's own typing, at its own statement ─────────────────────
    //
    // `whnf_typing` rather than `whnf`: the membership has to travel to the
    // reduced type, and the reduced type is what the decomposition below reads.
    // For an ι rule the statement is already an `Eq` application and the leg is
    // reflexivity, so this costs nothing on the path it exists for.
    let t = c.infer_type(proof).map_err(|_| gap!(Gap::Classifier))?;
    let (stmt, _, t) = c.whnf_typing(t).map_err(|_| gap!(Gap::Classifier))?;
    let mem = match t.ev.thm() {
        Some(m) => m.clone(),
        // §0.4: the reason is the sub-result's. This is the arm a rule whose
        // own proof did not certify comes back through, and the gap it carries
        // is the one that stopped the proof — not a reason invented here.
        None => return Err(gap!(t.ev.reason(Gap::NoEndpoint))),
    };
    cash_stmt(c, &stmt, mem)
}

/// **`Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧`** from a membership in `⟦Eq α lhs rhs⟧` the caller
/// already holds, and the Lean statement it is about.
///
/// [`cash`] is this with step 1 in front of it: infer the proof, reduce its
/// type, take the membership. The split exists because **one caller cannot take
/// step 1** — [`crate::iota_model::fire`] holds a theorem of a nested
/// declaration's *model*, whose binders are typed at the model's carrier while
/// the redex's arguments are typed at the export's. The two are the same set
/// (`⟦T⟧ = ⟦T._model.self⟧`, by `crate::nested_splice`'s table) and **not** the
/// same Lean type, so the application `infer_type` would have to check is
/// ill-typed in Lean world and well-formed in set world. That arm therefore
/// walks the nest itself, at the interpretation, and arrives here with the
/// membership in hand and with `stmt` spelled in the **export's** constants.
///
/// Nothing is weakened by that. `stmt` is what steps 2 and 3 read the three
/// sides off, and step 4's `retarget_set` refuses unless the `Eq` nest they
/// build **is** the very set `mem` is about — so a `stmt` that is not the
/// membership's own statement stops at `eq-cash-retarget` with a reason, and a
/// caller cannot use this entry point to assert an equation its theorem does
/// not prove. That refusal is the same one the module note describes at step 4
/// and it is why no comparison is added here.
pub fn cash_stmt(c: &mut Checker<'_, '_>, stmt: &E, mem: Thm) -> Result<Cashed, Gap> {
    let stmt = *stmt;

    // ── 2. the statement, as `Eq.{v} α lhs rhs` ─────────────────────────────
    let (head, sides) = get_app(&stmt);
    let Expr::Const(nm, ls) = &head.view() else { return Err(gap!(Gap::NotDecomposable)) };
    if *nm != eq_name() || sides.len() != 3 {
        return Err(gap!(Gap::NotDecomposable))
    }
    let empty = std::collections::HashMap::new();
    let inst: Option<Vec<u32>> = ls.iter().map(|l| crate::ground::eval(l, &empty)).collect();
    let Some(inst) = inst.filter(|v| v.len() == 1) else {
        return Err(gap!(Gap::SymbolicLevel))
    };
    let eq_former = c
        .stored_term(&eq_name(), &inst)
        .ok_or_else(|| gap!(Gap::NoInterpretation(eq_name(), inst.clone())))?;

    // ── 3. the three arguments' interpretations and typings ─────────────────
    //
    // By inference on the arguments, [`crate::quot_iota::fire`]'s trade: the
    // caller of a use site holds expressions and not memberships, and inferring
    // twice is cheaper than a second spelling of one argument.
    let mut tms: Vec<Term> = Vec::with_capacity(3);
    let mut mems: Vec<Thm> = Vec::with_capacity(3);
    for e in &sides {
        let ta = c.infer_type(e).map_err(|_| gap!(Gap::Classifier))?;
        let tm = ta.tm.clone().ok_or_else(|| gap!(ta.ev.reason(Gap::NoEndpoint)))?;
        let m = ta.ev.thm().cloned().ok_or_else(|| gap!(ta.ev.reason(Gap::NoEndpoint)))?;
        tms.push(tm);
        mems.push(m);
    }

    // **The subject must be `•` before `cond_elim` can consume it.** §6.2 sends
    // a proof-valued application to `•`, which is the case a use site is in;
    // a proof that interprets to something else — a scope variable, a stored
    // constant symbol — is *equal* to `•` by proof irrelevance and is moved
    // there rather than refused. This is `Interp::cond_app`'s own step, at one
    // level up, and it needs the statement's own typing, which is inferred only
    // on the branch that uses it.
    let point = c.interp().ok_or_else(|| gap!(Gap::SymbolicLevel))?.point();
    let ty_mem = if mem.concl().as_mem().map(|(s, _)| s) == Some(point.clone()) {
        None
    } else {
        let ts = c.infer_type(&stmt).map_err(|_| gap!(Gap::Classifier))?;
        Some(ts.ev.thm().cloned().ok_or_else(|| gap!(ts.ev.reason(Gap::NoEndpoint)))?)
    };

    let ip = c.interp().ok_or_else(|| gap!(Gap::SymbolicLevel))?;
    let d = ip.direct().ok_or_else(|| gap!(Gap::IndApparatus))?;
    let sums = ip.prelude.tower.sums.clone();

    let mem = match ty_mem {
        None => mem,
        Some(ty_mem) => {
            let to_pt = ip
                .point_of_proof(&ty_mem, &mem)
                .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-proof-irrelevance")))?;
            // `point_of_proof` proves `⟦proof⟧ = •`; the subject moves along
            // its symmetric, which is what `retarget_subject` takes.
            let back = derived::eq_symm(&mut ip.env, &to_pt)
                .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-subject-symm")))?;
            ip.retarget_subject(&mem, &back)
                .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-subject")))?
        }
    };

    // ── 4. β down `⟦Eq.{v}⟧`'s stored nest ──────────────────────────────────
    //
    // `⟦Eq α a b⟧` at a use site is the *applied spine* `app³(⟦Eq.{v}⟧, …)`;
    // the direct clause's `eq_set` sits at the bottom of the stored λ-nest.
    // The two are related by three β steps, each consuming one argument's own
    // typing — `rcompat_at`'s third transport, unchanged.
    //
    // **The chain's left endpoint is not compared here, deliberately.**
    // `⟦Eq.{v}⟧`'s nest is not the statement's own term until it is, and the
    // rule that needs them equal is the next one: `Interp::retarget_set` refuses
    // unless the equation's left side *is* the membership's set. A comparison
    // here would be that check in a second spelling, and `Gap::EndpointDrift`'s
    // note is this repository's own measurement of what such a guard is worth —
    // three of them, each firing on nothing across 11 578 061 conversions, all
    // removed, because the property is kept by the rules composing. A wrong
    // statement therefore stops at `eq-cash-retarget`, with a reason, and never
    // as a true theorem about the wrong set.
    let (eq_bot, beta) = ip
        .beta_spine(&eq_former, &tms, &mems)
        .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-beta")))?;
    let at_eq = ip
        .retarget_set(&mem, &beta)
        .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-retarget")))?;

    // ── 5. `cond_elim`, at the bottom's *own* two arguments ─────────────────
    //
    // Read back rather than reused from `tms`, which is `rcompat_at`'s
    // `eq_bot_args` and its reason: it refuses a nest whose bottom is some
    // other conditional singleton instead of asserting an equation about terms
    // the chain never mentioned.
    //
    // **This guard and the conclusion check below are the two that no input can
    // make fire, measured by mutation, and they are kept where the endpoint
    // comparison above was deleted.** The discriminator is the one
    // `PiShape`'s retired `Fs` variant was retired on — *can a wrong input reach
    // it* — and the answer is no for all three. What separates them is that
    // nothing follows these two: they are the only statements of the two
    // properties [`Cashed`]'s doc promises, that the equation is about the
    // **caller's** two terms and that the theorem says what is claimed. The
    // deleted one had `retarget_set` behind it and these have nothing.
    let (lhs, rhs) = eq_set_sides(&eq_bot, ip, d.eq).ok_or_else(|| gap!(Gap::NotDecomposable))?;
    if lhs != tms[1] || rhs != tms[2] {
        return Err(gap!(Gap::ConvCompose("eq-cash-bottom-sides")))
    }
    let phi = Formula::eq(lhs.clone(), rhs.clone());
    let chi = derived::inst_all(&d.eq_ax, &[lhs.clone(), rhs.clone()])
        .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-eq-ax")))?;
    let elim = derived::prop::cond_elim(&sums, &phi, &eq_bot, &chi)
        .ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-cond-elim")))?;
    let out = Thm::mp(&elim, &at_eq).ok_or_else(|| gap!(Gap::ConvCompose("eq-cash-mp")))?;
    if *out.concl() != phi {
        return Err(gap!(Gap::ConvCompose("eq-cash-conclusion")))
    }
    Ok(Cashed { eq: out, lhs, rhs })
}

/// `eq_set`'s two arguments, read off the term the β chain landed on.
///
/// A bottom that is not a two-argument application of *this* `Interp`'s `eq`
/// symbol is `None`: the check is the whole point, since `cond_elim` would
/// otherwise be handed a singleton of a different condition and the mismatch
/// would surface only as an unhelpful `mp` failure.
fn eq_set_sides(t: &Term, ip: &Interp, eq: FnSym) -> Option<(Term, Term)> {
    let (f, args) = ip.parts_of(t)?;
    (f == eq && args.len() == 2).then(|| (args[0].clone(), args[1].clone()))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::convert::{load_with, LoadOptions};
    use crate::env::Environment;
    use crate::expr::{app_n, bvars, konst, Expr};
    use crate::interp::Interp;
    use crate::ledger::Ledger;

    /// **The four ι rules the model states, and whether each one cashes.**
    ///
    /// All four. `iotaLeaf` and `iota1Nil` are `Eq.refl` — the two the
    /// pack/unpack encoding leaves definitional — and `iotaNode` and
    /// `iota1Cons` are `transportNode`/`transportCons` applied. What separated
    /// them was never this module: it was that the transporting two had no
    /// constant typing of their own, and the run now derives every one of
    /// `nested_model`'s 41.
    ///
    /// **The `bool` stays** even with no `false` left in it. It is what makes
    /// the loop below distinguish "cashed" from "declined for the right
    /// reason", and a table with a column that can only hold one value is the
    /// table to re-scope when a row moves — not one to delete, which is what
    /// happened to the two `false`s' *explanations* three times running. The
    /// module note keeps that history.
    ///
    /// *(Twice `false`, under two accounts. First: the two **lemmas** are the
    /// root and closing them closes the rules — refuted, `#90(b)` closed the
    /// lemmas and the rules did not move. Second: the rules have a residual of
    /// their own at `def_eq_struct`'s `Const` arm and `delta_evidence` — also
    /// refuted, those mints are the acceptance walk. It is
    /// `Checker::whnf_conv` on a proof-valued spine, and it was recorded in
    /// this file as open and *unreachable* while `iotaNode` was reaching it.)*
    const MODEL_IOTA: [(&str, bool); 4] = [
        ("iotaLeaf", true),
        ("iota1Nil", true),
        ("iotaNode", true),
        ("iota1Cons", true),
    ];

    fn fixture(name: &str) -> PathBuf {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures")
            .join(format!("{name}.ndjson"));
        assert!(p.exists(), "{} is missing; run scripts/export-fixture.sh", p.display());
        p
    }

    /// A fixture, checked and then **interpreted** — `crate::run`'s own pass,
    /// minus the parts that only produce a report.
    ///
    /// The store is what [`cash`] reads, so nothing shorter will do: a bare
    /// `Checker::threaded` has an empty store and every constant comes back
    /// `no-interp`, which is a different answer from the one being measured.
    fn interpreted(name: &str) -> (Environment, Interp, Ledger) {
        let opts = LoadOptions { mutual: true, ..Default::default() };
        let loaded = load_with(&fixture(name), opts).expect("load");
        let mut env = Environment::empty();
        for d in &loaded.decls {
            crate::kernel::add(&mut env, d).unwrap_or_else(|e| panic!("{}: {e}", d.name()));
        }
        let ex = crate::mutual_aux::expand(&env, &loaded.decls, &loaded.schedule);
        let mut ip = Interp::new();
        let led = Ledger::run(&ex.env, &ex.decls, &ex.schedule, &mut ip);
        (ex.env, ip, led)
    }

    /// Cash a declared theorem **at its own telescope**, every binder opened as
    /// a scope: the general statement rather than one ground instance, and the
    /// hypothetical mode qualification 2 names.
    ///
    /// The binder types are pushed in order and the rule is applied to the de
    /// Bruijn variables they opened, so the expression handed to [`cash`] is the
    /// theorem at exactly the arguments its own `∀`s declare. Returns the
    /// telescope's depth beside the answer, because "how many hypotheses should
    /// this equation carry" is that number and the test asserts it.
    fn cash_at_telescope(
        env: &Environment,
        ip: &mut Interp,
        name: &str,
    ) -> (Result<Cashed, Gap>, usize) {
        let nm = Name::simple(name);
        let ty = *env.get(&nm).unwrap_or_else(|| panic!("{name} is not declared")).ty();
        let mut c = Checker::threaded(env, ip);
        let mut n = 0usize;
        let out = c.in_scope(|c| {
            let mut cur = ty;
            while let Expr::Forall { ty: dom, body } = &cur.clone().view() {
                c.interpret_and_open(dom).map_err(|_| Gap::Classifier)?;
                n += 1;
                cur = *body;
            }
            let args = bvars(u32::try_from(n).expect("small telescope"), 0);
            Ok(cash(c, &app_n(konst(nm, [].into()), &args)))
        });
        (out.unwrap_or_else(Err), n)
    }

    /// The three things a cashed equation owes, checked together.
    ///
    /// Not just the `Ok`: that the theorem's conclusion really is
    /// `⟦lhs⟧ = ⟦rhs⟧` at the two terms reported; that the two sides are
    /// **different terms**, since an equation between one term and itself is
    /// `Thm::eq_refl` and would measure nothing; and that the hypotheses are
    /// exactly the telescope's, so a route that quietly assumed something extra
    /// is visible rather than hidden in a sequent nobody reads.
    fn assert_well_formed(name: &str, cashed: &Cashed, n: usize) {
        assert_eq!(
            *cashed.eq.concl(),
            Formula::eq(cashed.lhs.clone(), cashed.rhs.clone()),
            "`{name}`: the theorem is not about the two sides it reports"
        );
        assert_ne!(
            cashed.lhs, cashed.rhs,
            "`{name}`: the two sides are the same term, so the equation is reflexivity and \
             nothing has been measured"
        );
        assert_eq!(
            cashed.eq.hyps().len(),
            n,
            "`{name}`: the equation carries {} hypotheses at a telescope of {n} — it must carry \
             the binders' memberships and nothing else",
            cashed.eq.hyps().len()
        );
    }

    /// The ledger's own name for a gap, which is the vocabulary the reports and
    /// the ratchets are written in.
    fn reason(g: &Gap) -> String { Ledger::key(Some(g)) }

    // ───────────────────────────── the fast witnesses ─────────────────────────
    //
    // `transport_through_eq_rec` is `nested_model`'s `transportNode` with the
    // nesting taken out — 21 509 conversions against 7 261 645, and it carries
    // *both* outcomes: `myCongr` is a proof mini types and `transportS` is one
    // it does not. Every functional property of this module is measured there,
    // and `nested_model` is consulted once, for the four-rule table it owns.

    /// **A proof that is not `rfl` cashes.**
    ///
    /// `myCongr : ∀ a b, Eq a b → Eq (N.s a) (N.s b)` is `congrArg` written out
    /// — an `Eq.rec` on the hypothesis landing at `Eq.refl` — so its two sides
    /// are `⟦N.s a⟧` and `⟦N.s b⟧` at two *different* scope variables, and the
    /// equation is hypothetical under the three memberships its telescope
    /// opened. This is `rcompat_at`'s property at a different theorem: what is
    /// cashed is the proof's typing, and what the proof *is* never comes up.
    #[test]
    fn a_non_rfl_proof_of_an_equation_cashes() {
        let (env, mut ip, _) = interpreted("transport_through_eq_rec");
        let (got, n) = cash_at_telescope(&env, &mut ip, "myCongr");
        assert_eq!(n, 3, "`myCongr` has three binders");
        let cashed = got.unwrap_or_else(|g| panic!("`myCongr` did not cash: {}", reason(&g)));
        assert_well_formed("myCongr", &cashed, n);
        assert!(
            !cashed.eq.hyps().is_empty(),
            "an equation about scope variables must be hypothetical; an unconditional one here \
             would mean the memberships were never consumed"
        );
    }

    /// **The transport shape's typing lands, and the reason cashing declines
    /// has moved off `no-endpoint`** — `#90(b)`, measured at this module.
    ///
    /// `transportS` is `transportNode` with the nesting removed and it was the
    /// fixture's one uncertified constant typing. Its statement is an equation
    /// between two pieces of **data** whose left side only reaches its right by
    /// firing an inner `Eq.rec` through a *named* proof, so nothing about it is
    /// closed by proof irrelevance. The typing now certifies — the fixture is
    /// `is_clean()` — and that is the whole of what `#90(b)` was.
    ///
    /// **It still does not cash, and the new reason is the deliverable.** With
    /// `⊢ • ∈ ⟦Eq α lhs rhs⟧` in hand, [`cash`] gets four steps further and
    /// stops at [`Interp::beta_spine`]: `conv-compose(eq-cash-beta)`, step 4,
    /// this module's own and not `kernel.rs`'s. Asserting the *reason* rather
    /// than merely `is_err()` is the point — a decline that went back to
    /// `no-endpoint` would mean the typing had come undone, and a test that
    /// only said "declines" could not tell those apart.
    ///
    /// *(This test read `a_proof_with_no_typing_hands_back_its_own_gap` and
    /// asserted that `transportS` had no typing at all. The §0.4 property it
    /// was measuring — a result carries the reason of the sub-result that
    /// stopped it — is still measured, twice: on the model's table below, where
    /// `iotaNode` and `iota1Cons` still have no typing and still say
    /// `no-endpoint`, and here, where the reason moved precisely because the
    /// sub-result it was propagating stopped being missing.)*
    #[test]
    fn the_transport_shapes_typing_lands_and_cashing_stops_later() {
        let (env, mut ip, led) = interpreted("transport_through_eq_rec");
        assert!(
            led.uncertified().is_clean(),
            "`transport_through_eq_rec` no longer certifies fully: {:?} — this is the fixture \
             `#90(b)` closed and a residual here is that closure coming undone",
            led.uncertified()
        );
        let (got, n) = cash_at_telescope(&env, &mut ip, "transportS");
        assert_eq!(n, 5, "`transportS` binds the motive, the value, `a`, `b` and `h`");
        let g = got.err().unwrap_or_else(|| {
            panic!(
                "`transportS` cashed — `eq-cash-beta` has closed too, and this is where to \
                 record it"
            )
        });
        assert_eq!(
            reason(&g),
            "conv-compose(eq-cash-beta)",
            "the decline is not step 4's; a `no-endpoint` here means the constant typing that \
             `#90(b)` closed has come undone"
        );
    }

    /// **A statement that is still a `∀` is refused by name, not mis-cashed.**
    ///
    /// `myCongr` applied to *nothing* leaves a `∀` at the top. The
    /// decomposition must say `not-decomposable` rather than reach into the
    /// telescope on its own: a route that peeled binders it was not given would
    /// be asserting an equation about terms the caller never named — and every
    /// caller of this module names its own arguments, because that is what a
    /// use site has.
    #[test]
    fn a_statement_that_is_still_a_forall_is_refused() {
        let (env, mut ip, _) = interpreted("transport_through_eq_rec");
        let mut c = Checker::threaded(&env, &mut ip);
        let g = cash(&mut c, &konst(Name::simple("myCongr"), [].into()))
            .expect_err("a `∀` is not an equation");
        assert_eq!(reason(&g), "not-decomposable");
    }

    /// **A statement that is a three-argument constant application and is *not*
    /// `Eq` is refused by the head symbol.**
    ///
    /// `indexed_two_params`'s `ixMk α β a b : Ix α β N.z` is the input this
    /// needs and the reason it is a different fixture: the head check is the
    /// module's primary dispatch, and an input that fails it on *arity* — `N.z`,
    /// whose type `N` is a constant applied to nothing — leaves the check
    /// untested. `Ix α β N.z` matches `Expr::Const` and has exactly three
    /// arguments, so only the name stands between it and `⟦Eq.{v}⟧`'s nest.
    ///
    /// The fixture certifies fully (`constEv 2/2`, `gapped 0`), which is what
    /// makes the assertion about the *name* rather than about `ixMk`'s typing.
    #[test]
    fn a_three_argument_statement_that_is_not_an_equation_is_refused() {
        let (env, mut ip, led) = interpreted("indexed_two_params");
        assert!(
            led.uncertified().is_clean(),
            "`indexed_two_params` no longer certifies fully, so a decline below would not be \
             about the head symbol: {:?}",
            led.uncertified()
        );
        let (got, n) = cash_at_telescope(&env, &mut ip, "ixMk");
        assert_eq!(n, 4, "`ixMk` takes two parameters and two fields");
        let g = got.expect_err("`Ix α β N.z` is not an equation");
        assert_eq!(reason(&g), "not-decomposable");
    }

    /// **Both transport shapes certify, and neither one's certificate is the
    /// other's** — `#90(b)` as a regression, and the refuted hypothesis kept.
    ///
    /// `delta_inside_a_proof.lean` is a data-valued `Eq.rec` whose major premise
    /// is a *named* proof, and it certified before `#90(b)` and after it: the
    /// major's own conversion is closed by proof irrelevance before anything
    /// needs the δ leg. That is what refuted "a δ step on a proof has no
    /// endpoints, because §6.2 sends a proof to `•`, which `Checker::split_app`
    /// cannot take apart" as *the* explanation, and the file earns its place by
    /// pinning that negative — a run in which it starts gapping has refuted the
    /// refutation, which is a result.
    ///
    /// `transport_through_eq_rec.lean` is the shape that did gap, at
    /// **21 509 conversions against `nested_model`'s 7 261 645**. What it added
    /// was a transport that has to be *reduced* rather than compared, between
    /// terms that are **data** — so proof irrelevance does not apply — and the
    /// pair the run could not close was that `Eq.rec` compared with **itself**.
    /// `Checker::def_eq_struct`'s `App`/`App` arm was the only structural arm
    /// that did not answer identical interpretations with `refl()`; it built an
    /// `app_cong` instead, and the half carrying the proof-valued major could
    /// state no endpoints. Both files are asserted clean here because the pair
    /// is the finding: two shapes, one that never needed the arm and one that
    /// did.
    ///
    /// **The `whnf`-on-a-proof endpoint loss is closed** and its own witness is
    /// `mini/tests/fixtures/whnf_of_a_proof.lean`, asserted in
    /// `mini/tests/designed.rs`. This test does not measure it — neither file
    /// here reaches it, which is the third ingredient that fixture's header
    /// names and the one `transport_through_eq_rec` lacks: its two sides are the
    /// same expression, so `#90(b)`'s reflexivity answers before any leg through
    /// the proof is asked for.
    ///
    /// *(This paragraph read "still there … no pair in the corpus or the fixture
    /// directory now depends on it". The fixture directory did: `nested_model`,
    /// measured by the table below.)*
    #[test]
    fn the_two_transport_shapes_certify_and_the_refutation_still_holds() {
        let (_, _, clean) = interpreted("delta_inside_a_proof");
        assert!(
            clean.uncertified().is_clean(),
            "`delta_inside_a_proof` no longer certifies fully: {:?} — the refutation this test \
             records has itself been refuted, which is a result",
            clean.uncertified()
        );
        let (_, _, residual) = interpreted("transport_through_eq_rec");
        let u = residual.uncertified();
        assert!(
            u.is_clean(),
            "`transport_through_eq_rec` is uncertified again: {u:?} — `#90(b)` is back, and the \
             arm to read first is `def_eq_struct`'s `App`/`App` reflexivity decision"
        );
        assert!(
            residual.convs.gapped_by.is_empty(),
            "the witness gaps somewhere: {:?}",
            residual.convs.gapped_by
        );
        // …and it is not clean by having stopped *doing* anything: the shape is
        // still the expensive one, and a fixture that quietly stopped reaching
        // its own transport would pass every assertion above.
        assert!(
            residual.convs.moved > 0,
            "the witness performs no non-trivial conversion at all, so the assertions above are \
             about a walk that no longer happens"
        );
    }

    // ─────────────────────────── the model's own table ────────────────────────

    /// **The four ι rules of the nested model, cashed** — [`MODEL_IOTA`] as an
    /// assertion, and the deliverable's own measurement.
    ///
    /// One `interpreted` call for the whole table: `nested_model`'s
    /// interpretation pass is 3.1 million conversions and about eighty seconds,
    /// so the four rules and the two lemmas behind them are measured together
    /// rather than once per test. Everything that does *not* need this fixture
    /// is measured on `transport_through_eq_rec` above.
    ///
    /// *(7.2 million and about two minutes before `#90(b)`. The fall is
    /// `def_eq_struct`'s `App` reflexivity decision, not a smaller walk: the
    /// same declarations are checked and two more of them now certify.)*
    ///
    /// **`is_clean()`, not a count.** This asserted `const_typings == 2` and
    /// then `== 0` would have been the same kind of statement — a number to
    /// update rather than a property. What the table below needs is that *every*
    /// pair of the fixture certifies, because that is precisely the condition
    /// under which `cash` can be measured at all: a rule declines with its
    /// proof's own reason (§0.4), so a rule that did not cash while the run was
    /// leaving typings behind would be reporting someone else's residual.
    #[test]
    fn the_models_four_iota_rules_cash_exactly_where_their_proofs_type() {
        let (env, mut ip, led) = interpreted("nested_model");
        assert!(
            led.uncertified().is_clean(),
            "`nested_model` no longer certifies fully: {:?} — the model's own residual is back, \
             and the arm to read first is `whnf_conv`'s proof-valued spine",
            led.uncertified()
        );
        for (name, cashes) in MODEL_IOTA {
            let (got, n) = cash_at_telescope(&env, &mut ip, name);
            assert!(n >= 6, "`{name}` has {n} binders; the model's rules have at least six");
            match (got, cashes) {
                (Ok(cashed), true) => assert_well_formed(name, &cashed, n),
                (Err(g), false) => assert_eq!(
                    reason(&g),
                    "no-endpoint",
                    "`{name}` declines, but not for the reason its proof's own typing does"
                ),
                (Ok(_), false) => panic!(
                    "`{name}` cashed. Its proof's typing has become available — that is a \
                     result, and this table is what should be re-scoped, not edited away"
                ),
                (Err(g), true) => panic!("`{name}` did not cash: {}", reason(&g)),
            }
        }
        // …and the two **lemmas** the rules' proofs are built on still decline,
        // at step 4 and not at `no-endpoint`. That is now a fact about the
        // lemmas alone and it is asserted here because it is the sharpest form
        // of the module note's "the split was never the `rfl`/not-`rfl` split":
        // the two rules cash while the two lemmas they apply do not, which is
        // only possible because `cash` reads a *typing* and not a proof term.
        //
        // **Nothing is waiting on the two lemmas.** `crate::iota_model` calls
        // `cash_stmt` on the rule's own statement, never on a lemma's, so
        // `eq-cash-beta` is a residual of this module that is on no path.
        //
        // *(This loop carried "the two lemmas are the root, not a second
        // problem: closing them closes the rules with no change to `cash`", and
        // then "whatever stops the two rules is theirs: the trail on `iotaNode`
        // is 2 675 mints at `def_eq_struct`'s `Const` arm and 918 at
        // `delta_evidence`". Both were wrong and in opposite directions. The
        // rules did not need the lemmas to cash, and the trail was the
        // acceptance walk — `crate::blocker::Quiet` is what made it readable
        // and `Checker::proof_point_leg` is what it then said.)*
        for name in ["transportNode", "transportCons"] {
            let (got, _) = cash_at_telescope(&env, &mut ip, name);
            let g = got.err().unwrap_or_else(|| {
                panic!("`{name}` cashed — `eq-cash-beta` has closed too, and this is where to \
                        record it")
            });
            assert_eq!(
                reason(&g),
                "conv-compose(eq-cash-beta)",
                "`{name}` declines for some other reason; `no-endpoint` here means its constant \
                 typing has come undone"
            );
        }
    }
}
