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
//! rule theorem [`crate::nested_ev`] emits applied to the site's own arguments.
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
//! about its **defined** recursors, and this module cashes exactly two of them:
//!
//! | rule | proof | cashes | why |
//! | --- | --- | --- | --- |
//! | `iotaLeaf` | `Eq.refl` | **yes** | the block's own ι rule, unchanged |
//! | `iota1Nil` | `Eq.refl` | **yes** | the transport collapses on `List.nil` |
//! | `iotaNode` | `transportNode` applied | no | `transportNode`'s own typing is missing |
//! | `iota1Cons` | `transportCons` applied | no | `transportCons`'s own typing is missing |
//!
//! **The split is not the `rfl`/not-`rfl` split**, and reading it as one would
//! misplace the work. A non-`rfl` proof cashes: `rcompat_at`'s occupant is an
//! arbitrary proof term, and the fast test below cashes `myCongr`, an `Eq.rec`.
//! What stops the other two is that the run leaves **four** uncertified
//! constant typings, all `no-endpoint`, and they are exactly `transportNode`,
//! `transportCons` and the two rules those are applied in. The two lemmas are
//! the root; the two rules only inherit it. Nothing about that is reachable
//! from here — see the residual note below — and if it is closed the table's
//! third column becomes four `yes`es with no change to [`cash`].
//!
//! # The generated population, and why no test enumerates it
//!
//! `nested_model.lean` is hand-written and has four rules;
//! [`crate::nested_ev`] now *generates* them, and
//! [`Iso::iotas`](crate::nested_ev::Iso::iotas) is
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
//! # The residual, and the hypothesis it refuted
//!
//! `mini/tests/fixtures/transport_through_eq_rec.lean` is `transportNode` with
//! the nesting taken out: **21 509 conversions against `nested_model`'s
//! 7 261 645**, carrying the same one uncertified constant typing. It exists so
//! that whoever closes the residual can iterate in a second rather than in two
//! minutes.
//!
//! The first hypothesis about it was that a **δ step on a proof** has no
//! endpoints — §6.2 sends a proof to `•`, and `Checker::split_app` cannot take
//! `•` apart, so `delta_evidence` mints `NoEndpoint` at `kernel.rs`'s `Const`
//! node. `mini/tests/fixtures/delta_inside_a_proof.lean` is that prediction as
//! an export and it **certifies with `gapped = 0`**: the major's own conversion
//! is closed by proof irrelevance before anything needs the δ leg. What the
//! transport shape adds is a transport that has to be *reduced* rather than
//! compared — the minor premise's declared type is `motive a (Eq.refl a)`,
//! reachable only by firing an inner `Eq.rec` through a named proof — and there
//! proof irrelevance does not apply, because the terms being related are
//! **data**. Both files are pinned by a test here, and the pair is the finding:
//! one shape certifies and one does not, so the reason is not "inside a proof".
//!
//! The trail on the small witness is `beta_evidence`, `delta_evidence` and
//! `def_eq_struct`'s reflexivity arm, all at a `None` endpoint. It is a `whnf`
//! threading question in `mini/src/kernel.rs` — **not** a clause of §6.2, not a
//! `derived/` construction, and not something this module can reach.
//!
//! # This module is **not** a black box, and the allowlist does not move
//!
//! [`crate::nested_ev`] generates the model of a nested declaration's
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

    // ── 2. the statement, as `Eq.{v} α lhs rhs` ─────────────────────────────
    let (head, sides) = get_app(&stmt);
    let Expr::Const(nm, ls) = &*head else { return Err(gap!(Gap::NotDecomposable)) };
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
    /// `iotaLeaf` and `iota1Nil` are `Eq.refl` — the two the pack/unpack
    /// encoding leaves definitional — and their constant typings are in the
    /// store, so both cash. `iotaNode` and `iota1Cons` are
    /// `transportNode`/`transportCons` applied, and *those two lemmas'* own
    /// typings are two of the run's four `waiting:no-endpoint` residuals; the
    /// rules built on them therefore have none either, and there is nothing to
    /// cash. That is qualification 3 of the module note, as a table.
    ///
    /// The module note carries the table and why the split is *not* the
    /// `rfl`/not-`rfl` split; this is it as an assertion.
    const MODEL_IOTA: [(&str, bool); 4] = [
        ("iotaLeaf", true),
        ("iota1Nil", true),
        ("iotaNode", false),
        ("iota1Cons", false),
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
        let ty = env.get(&nm).unwrap_or_else(|| panic!("{name} is not declared")).ty().clone();
        let mut c = Checker::threaded(env, ip);
        let mut n = 0usize;
        let out = c.in_scope(|c| {
            let mut cur = ty.clone();
            while let Expr::Forall { ty: dom, body } = &*cur.clone() {
                c.interpret_and_open(dom).map_err(|_| Gap::Classifier)?;
                n += 1;
                cur = body.clone();
            }
            let args = bvars(u32::try_from(n).expect("small telescope"), 0);
            Ok(cash(c, &app_n(konst(nm.clone(), [].into()), &args)))
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

    /// **A proof whose own typing is missing hands back that gap, not another.**
    ///
    /// §0.4: a result carries the reason of the sub-result that stopped it.
    /// `transportS` is the fixture's uncertified pair, and its reason is
    /// `no-endpoint`; a route that answered `not-decomposable` or
    /// `no-interp(transportS)` would be reporting its own confusion as the
    /// input's, which is the mislabel this project has paid for repeatedly.
    #[test]
    fn a_proof_with_no_typing_hands_back_its_own_gap() {
        let (env, mut ip, led) = interpreted("transport_through_eq_rec");
        assert_eq!(
            led.uncertified().const_typings,
            1,
            "the fixture is supposed to leave exactly one constant typing missing"
        );
        let (got, _) = cash_at_telescope(&env, &mut ip, "transportS");
        let g = got.expect_err("`transportS` has no typing, so there is nothing to cash");
        assert_eq!(reason(&g), "no-endpoint", "the gap is not the one the proof's typing carries");
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

    /// **The residual is the transport shape, and it is a `whnf` threading gap
    /// rather than anything this module can reach.**
    ///
    /// `nested_model` leaves four `waiting:no-endpoint` constant typings and
    /// they are exactly `transportNode`, `transportCons` and the two ι rules
    /// those are applied in. `transport_through_eq_rec.lean` is the first of
    /// them with the nesting removed and reproduces it at 0.3 % of the
    /// conversions, which is what makes the residual actionable.
    ///
    /// **The first hypothesis about it was wrong and
    /// `delta_inside_a_proof.lean` is the refutation.** "A δ step on a proof has
    /// no endpoints, because §6.2 sends a proof to `•`, which
    /// `Checker::split_app` cannot take apart" predicts that a data-valued
    /// `Eq.rec` whose major premise is a *named* proof gaps. It does not: that
    /// file certifies with `gapped = 0`, because the major's own conversion is
    /// closed by proof irrelevance before anything needs the δ leg. What
    /// `transport_through_eq_rec` adds is a transport that has to be *reduced*
    /// rather than compared — the minor premise's declared type is
    /// `motive a (Eq.refl a)`, whose reduct is reached only by firing an inner
    /// `Eq.rec` through a named proof — and there proof irrelevance does not
    /// apply, because the terms being related are **data**.
    ///
    /// Both fixtures are pinned here, and the pair is the finding: one shape
    /// certifies and one does not, so the reason is not "inside a proof".
    #[test]
    fn the_residual_is_the_transport_shape_and_it_is_a_whnf_threading_gap() {
        let (_, _, clean) = interpreted("delta_inside_a_proof");
        assert!(
            clean.uncertified().is_clean(),
            "`delta_inside_a_proof` no longer certifies fully: {:?} — the refutation this test \
             records has itself been refuted, which is a result",
            clean.uncertified()
        );
        let (_, _, residual) = interpreted("transport_through_eq_rec");
        let u = residual.uncertified();
        assert_eq!(u.const_typings, 1, "the witness stopped carrying the residual");
        assert!(u.conversions > 0, "the witness stopped gapping any conversion");
        assert_eq!(
            residual.convs.gapped_by.keys().collect::<Vec<_>>(),
            vec!["no-endpoint"],
            "the witness gaps for some reason other than the residual's"
        );
    }

    // ─────────────────────────── the model's own table ────────────────────────

    /// **The four ι rules of the nested model, cashed** — [`MODEL_IOTA`] as an
    /// assertion, and the deliverable's own measurement.
    ///
    /// One `interpreted` call for the whole table: `nested_model`'s
    /// interpretation pass is 7.2 million conversions and about two minutes, so
    /// the four rules and the two lemmas behind them are measured together
    /// rather than once per test. Everything that does *not* need this fixture
    /// is measured on `transport_through_eq_rec` above.
    #[test]
    fn the_models_four_iota_rules_cash_exactly_where_their_proofs_type() {
        let (env, mut ip, led) = interpreted("nested_model");
        assert_eq!(
            led.uncertified().const_typings,
            4,
            "the model's residual moved; the table below is about the four pairs it leaves"
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
        // …and the two lemmas the failing half is built on are the root, not a
        // second problem: closing them closes the rules with no change to
        // `cash`. Asserted here because it is the sentence that says whose the
        // residual is.
        for name in ["transportNode", "transportCons"] {
            let (got, _) = cash_at_telescope(&env, &mut ip, name);
            let g = got.err().unwrap_or_else(|| {
                panic!("`{name}` cashed — the model's residual has closed, and this is where to \
                        record it")
            });
            assert_eq!(reason(&g), "no-endpoint", "`{name}` declines for some other reason");
        }
    }
}
