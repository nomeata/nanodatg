//! **The ι rule of `Acc.rec` at `u₁ ≥ 1`, at a use site** — the certificate
//! `whnf`'s recursor arm needs when the major premise is `Acc.intro` and the
//! motive is a family of values.
//!
//! # Interface
//!
//! ```text
//! rec_acc_iota::fire(checker, Acc.rec, σ, …) -> Result<(Thm, Term), Gap>
//! ```
//!
//! One **composed** equation
//!
//! ```text
//! Γ ⊢ app(…app(⟦Acc.rec.{u₁,u}⟧, ⟦α⟧)…, ⟦Acc.intro α r a h⟧) = ⟦rhs⟧
//! ```
//!
//! together with `⟦rhs⟧`, or a named absence. Called from
//! [`crate::kernel::Checker::whnf_conv`]'s constructor-match branch and nowhere
//! else.
//!
//! # Which arm of `whnf` this is, and it is not the one a design note names
//!
//! `MINI-HANDOFF.md` §27's sizing routes this row through
//! [`Checker::nest_iota`](crate::kernel::Checker) — the β chain the *`Eq`*
//! clause's ι is, on the **K-rule** arm. Measured, `Acc` never reaches that arm:
//! `crate::kernel::add` sets `k_type` only for a one-constructor inductive
//! proposition whose constructor has **no fields**, and `Acc.intro` has two. So
//! the major premise is reduced, matched against the rule, and the decline that
//! `118` reported came from the *constructor-match* branch — from
//! `iota_ix_dep::fire`, which `Acc`'s `num_indices = 1` routes it to and which is
//! about an [`derived::inductive::IndexedDepRecursor`] that no `direct::Clause`
//! declaration has.
//!
//! The route this module takes is nevertheless the β chain §27 describes: the
//! stored `⟦Acc.rec.{u₁,u}⟧` nest has `pack` at its bottom, and
//! [`Interp::beta_spine`] walks it. What §27 got right is the *derivation*; what
//! it got wrong is which of `whnf`'s two ι arms asks for it, and the hook is
//! placed accordingly — beside [`crate::quot_iota`]'s, which is a
//! `ConstantInfo::Recursor` with a rule of its own for the same reason.
//!
//! # The composite
//!
//! Writing `ē` for `⟦m⟧`, `ā` for `⟦a⟧` and `accrec` for `accrec(A,R̄,T,ē)`:
//!
//! | step | from | to | how |
//! |---|---|---|---|
//! | 1 | `app(…⟦Acc.rec⟧…, ⟦t⟧)` | `app(app(pack,ā),•)` | `beta_spine` down the stored nest, then [`RecAccElim::ax`](crate::interp::RecAccElim) |
//! | 2 | that | `app(app(app(ē,ā),•), ih(accrec,A,R̄,ā))` | `RecAcc::pack_iota`, discharged with `step_typed` and `ā ∈ acc(A,R̄)` |
//! | 3 | `ih(accrec,A,R̄,ā)` | `⟦fun y hy => Acc.rec α r C m y (h y hy)⟧` | [`rows_agree`] — two graph extensionalities |
//! | 4 | step 2 | `⟦rhs⟧` | one `app` congruence over step 3 |
//!
//! **Step 3 is the whole of the work and it is an extensionality, not a
//! transport.** `derived`'s induction hypothesis is a set of rows
//! `{ ⟨y, cval(ep(R̄,y,ā), app(accrec,y))⟩ : y ∈ A }` and Lean's is a λ-graph
//! `{ ⟨y, t(p⃗,y)⟩ : y ∈ A }`; they are the same function and nothing relates
//! them for free. Both are Replacement images over the *same* domain, so one
//! lemma — [`same_rows`] — closes both levels, given the rows agree pointwise.
//!
//! # Where §27's sizing is one β step optimistic
//!
//! §27 says the inner λ's body is `app(app(pack,y),•)`. It is not:
//! [`Interp::app`] builds `⟦f a⟧ = app(⟦f⟧,⟦a⟧)` and never reduces, so
//! `⟦Acc.rec α r C m y (h y hy)⟧` is the six-fold *applicative spine* over
//! `⟦Acc.rec.{u₁,u}⟧` — a redex over the stored λ-graph, exactly `SCOPING.md`
//! §1's cost axis. So step 1 is run a **second** time, at `y` and `•`, and
//! `pack_app` closes it; the accessibility that both need comes from **A4** at
//! `ā ∈ acc(A,R̄)` and the pair, and the pair is `pair_in_graph` at the proof
//! binder `w`, whose own inhabitation is what makes it available at all.
//!
//! Off the relation there is nothing to prove and no case analysis anywhere:
//! `cval(∅,v)` and a λ-graph over `∅` are both `∅`, and the pointwise premise is
//! guarded by `w ∈ ⟦r y ā⟧`. That is `derived::rec_acc::cval`'s
//! guarded-by-inhabitation discipline paying for the second time.

use kernel::{Formula, FreeVar, Term, Thm};

use derived::funcs::{hyp_syl, Sets};
use derived::rec_acc::{cval_of, ep_of, ih_of};
use derived::sums::Sums;

use crate::ev::{Cause, Gap};
use crate::expr::{Name, E};
use crate::interp::{Interp, RecAccElim};
use crate::kernel::Checker;
use crate::rec_acc::At;
use crate::rec_acc_value::{acc_point, in_carrier, major, step_typed_at, Cx};
use crate::scope::Scopes;

use std::rc::Rc;

/// `α, r, C, m, a, t` — the eliminator's whole nest, and the arguments `whnf`
/// consumes before the rule fires.
const DEPTH: usize = 6;

const CLAUSE: &str = "iota: the declaration is not the Acc clause";
const SHAPE: &str = "iota: the recursor's arity or its level list disagree";
const PROP: &str = "iota: a Prop-valued motive has no pack";
const RUNG: &str = "iota: the recursor's target sort is not a universe rung";
const CARRIER: &str = "iota: the Acc clause's carrier is not in the store";
const ABBREV: &str = "iota: Acc.rec's nest bottom has no stored abbreviation";
const MAJOR: &str = "iota: the major premise's accessibility";
const POINT: &str = "iota: the major premise is not a proof";
const STEP_TYPED: &str = "iota: step_typed does not discharge here";
const NEST: &str = "iota: the beta chain down the stored eliminator";
const IOTA: &str = "iota: pack_iota does not instantiate here";
const INTRO: &str = "iota: the major premise is not Acc.intro at the eliminator's own point";
const MINOR: &str = "iota: the Lean right-hand side is not the minor at the point and the graph";
const LAM: &str = "iota: the recursive-call argument is not a lambda graph over the carrier";
const EDGE: &str = "iota: the edge proposition is not Lean's own relation value";
const PRED: &str = "iota: a predecessor of the major premise is not accessible";
const SPINE: &str = "iota: the recursive call does not reduce to the recursor's own value";
const ROWS: &str = "iota: the two induction hypotheses are not the same set";
const RHS: &str = "iota: the composite did not land on the Lean right-hand side";

/// The ι certificate at one use site: `Γ ⊢ ⟦Acc.rec α r C m a t⟧ = ⟦rhs⟧`.
///
/// `args`/`arg_tms` are the six arguments up to and including the major
/// premise, with their interpretations, and `rhs` the Lean right-hand side
/// `whnf` is about to move to.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fire(
    c: &mut Checker<'_, '_>,
    rec: &Name,
    rec_inst: &[u32],
    rec_ty: &E,
    head_tm: &Term,
    args: &[E],
    arg_tms: &[Term],
    ctor_args: &[E],
    rhs: &E,
) -> Result<(Thm, Term), Gap> {
    let ind_name = c
        .environment()
        .owner(rec)
        .cloned()
        .ok_or_else(|| Gap::NoInterpretation(*rec, rec_inst.to_vec()))?;
    let bad = |w: &'static str| Gap::Recursor(ind_name, w, Cause::Threading);
    if crate::direct::clause_for(&ind_name) != Some(crate::direct::Clause::Acc) {
        return Err(bad(CLAUSE))
    }
    if args.len() != DEPTH || arg_tms.len() != DEPTH {
        return Err(bad(SHAPE))
    }
    let u1 = crate::rec_dep::motive_level(rec_ty, 2, 1).ok_or_else(|| bad(SHAPE))?;
    if u1 == 0 {
        return Err(bad(PROP))
    }
    let ind_inst = rec_inst.get(1..).ok_or_else(|| bad(SHAPE))?.to_vec();
    // `Acc.intro α r a h` at the eliminator's **own** parameters and point.
    // Well-typedness makes them convertible; making them *equal* is a
    // conversion nothing here holds, and the transport would be about a
    // different carrier.
    if ctor_args.len() != 4 || ctor_args[..2] != args[..2] || ctor_args[2] != args[4] {
        return Err(bad(INTRO))
    }

    // `⟦rhs⟧` first, because everything after this point holds `Interp` mutably
    // and inference is the checker's.
    let want = c.infer_type(rhs).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;

    // **`⟦h⟧` is not `•`.** §6.2 sends every proof to `•` at an *application*,
    // and `Acc.intro α r a h` is one — but `h` itself is a binder of the
    // declaration under check, so its interpretation is that binder's own scope
    // variable. `pack_iota` is stated at `•`, so the two are bridged by proof
    // irrelevance, exactly as the major premise's `⟦t⟧` is in
    // [`crate::rec_acc_value`]'s value clause.
    let h_typing = c.infer_type(&ctor_args[3]).map_err(|_| Gap::Classifier)?;
    let h_tm = h_typing.tm.clone().ok_or_else(|| h_typing.ev.reason(Gap::NoEndpoint))?;
    let h_mem = h_typing.ev.thm().cloned().ok_or_else(|| h_typing.ev.reason(Gap::NoEndpoint))?;
    let (h_is_prop, h_ty_ev) = c.is_prop_ev(&h_typing.ty).map_err(|_| Gap::Classifier)?;
    if !h_is_prop {
        return Err(bad(INTRO))
    }
    let h_ty_mem = h_ty_ev.thm().cloned().ok_or_else(|| h_ty_ev.reason(Gap::NoEndpoint))?;
    let mems = c.nest_arg_mems(head_tm, rec_ty, args, arg_tms)?;
    let former = c.stored_term(&ind_name, &ind_inst).ok_or_else(|| bad(CARRIER))?;

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let elim: Rc<RecAccElim> = ip
        .rec_acc_elims
        .get(&(*rec, rec_inst.to_vec()))
        .cloned()
        .ok_or_else(|| bad(ABBREV))?;
    let ac = ip.acc().ok_or(Gap::IndApparatus)?;
    let ra = ip.rec_acc().ok_or(Gap::IndApparatus)?;

    let (a, r, cm) = (arg_tms[0].clone(), arg_tms[1].clone(), arg_tms[2].clone());
    let (em, aa, tt) = (arg_tms[3].clone(), arg_tms[4].clone(), arg_tms[5].clone());
    let point = ip.point();
    // `t : Acc α r a` is a proof, so the pack is applied at `•` and `pack_iota`
    // is stated there. Checked rather than assumed: everything below is about
    // the term the equation names.
    if tt != point {
        return Err(bad(POINT))
    }
    let graph = Term::apply(ac.graph, vec![a.clone(), r.clone()]);
    let acc_t = ac.sets.of(a.clone(), graph.clone());
    let t = ip.sort(u1);
    let rung = ip.prelude.tower.at(u1 as usize).ok_or_else(|| bad(RUNG))?;
    if rung.set != t {
        return Err(bad(RUNG))
    }
    let (empty_mem, transitive) = (rung.empty_mem.clone(), rung.transitive.clone());
    let accrec = ra.ra.of(a.clone(), graph.clone(), t.clone(), em.clone());
    let cx = Cx {
        ac: &ac,
        ra: &ra,
        a,
        a_mem: mems[0].clone(),
        r,
        r_mem: mems[1].clone(),
        graph,
        acc_t,
        cm,
        c_mem: mems[2].clone(),
        em,
        m_mem: mems[3].clone(),
        t,
        empty_mem,
        transitive,
        accrec,
    };
    let at = At {
        xs: arg_tms.to_vec(),
        mems,
        vars: Vec::new(),
        former,
        goal: want.clone(),
    };

    // ── the major premise, and the guard `pack_iota` carries ────────────────
    let (a_in_acc, _) = major(ip, &cx, &at, &aa).ok_or_else(|| bad(MAJOR))?;
    let a_in_carrier = in_carrier(&cx, &aa, &a_in_acc).ok_or_else(|| bad(MAJOR))?;
    let st = step_typed_at(ip, &cx, &at).ok_or_else(|| bad(STEP_TYPED))?;

    // ── step 1: down the eliminator's nest and off mini's own name ──────────
    let (bottom, beta_eq) =
        ip.beta_spine(head_tm, arg_tms, &at.mems).ok_or_else(|| bad(NEST))?;
    if bottom != ip.mk(elim.sym, arg_tms.to_vec()) {
        return Err(bad(NEST))
    }
    let unfold = derived::inst_all(&elim.ax, arg_tms).ok_or_else(|| bad(ABBREV))?;
    let step1 = eq_trans(ip, &beta_eq, &unfold).ok_or_else(|| bad(ABBREV))?;

    // ── step 2: ι at the thesis's spelling ──────────────────────────────────
    let iota = derived::inst_all(
        &ra.ra.pack_iota,
        &[cx.a.clone(), cx.graph.clone(), cx.t.clone(), cx.em.clone()],
    )
    .and_then(|x| Thm::mp(&x, &st))
    .and_then(|x| derived::inst_all(&x, std::slice::from_ref(&aa)))
    .and_then(|x| Thm::mp(&x, &a_in_acc))
    .ok_or_else(|| bad(IOTA))?;
    let step2 = eq_trans(ip, &step1, &iota).ok_or_else(|| bad(IOTA))?;

    // ── the Lean side: `⟦m a h (fun y hy => …)⟧`, taken apart ───────────────
    //
    // `⟦h⟧ = •` — `h : ∀ y, r y x → Acc α r y` is a proof — so the first two
    // arguments are the ones `Base::step_at` already applied, and what is left
    // is the recursive-call function. Compared rather than assumed: a right-hand
    // side of some other shape is a decline, not a wrong certificate.
    let (head, margs) = peel_app(ip, &want, 3).ok_or_else(|| bad(MINOR))?;
    if head != cx.em || margs[0] != aa || margs[1] != h_tm {
        return Err(bad(MINOR))
    }
    let lam = margs[2].clone();

    // ── step 3: the two induction hypotheses are one set ────────────────────
    let ih_tm = ih_of(
        ra.ra.base.ih,
        cx.accrec.clone(),
        cx.a.clone(),
        cx.graph.clone(),
        aa.clone(),
    );
    let rows = rows_agree(
        ip,
        &ind_name,
        &cx,
        &at,
        head_tm,
        &elim,
        &Major { aa: &aa, in_acc: &a_in_acc, in_carrier: &a_in_carrier },
        &ih_tm,
        &lam,
    )?;

    // ── step 4: two congruences, at the two arguments the spellings differ in ─
    let ap_sym = ip.prelude.ap.app;
    let pt_eq_h = {
        let h_pt = ip.point_of_proof(&h_ty_mem, &h_mem).ok_or_else(|| bad(INTRO))?;
        derived::eq_symm(&mut ip.env_mut(), &h_pt).ok_or_else(|| bad(INTRO))?
    };
    let at_a = ip.app(cx.em.clone(), aa.clone());
    let head_cong = derived::congr(&mut ip.env_mut(), ap_sym, &[Thm::eq_refl(at_a), pt_eq_h])
        .ok_or_else(|| bad(RHS))?;
    let cong = derived::congr(&mut ip.env_mut(), ap_sym, &[head_cong, rows])
        .ok_or_else(|| bad(RHS))?;
    let out = eq_trans(ip, &step2, &cong).ok_or_else(|| bad(RHS))?;
    if out.concl().as_eq().map(|(_, r)| r) != Some(want.clone()) {
        return Err(bad(RHS))
    }
    Ok((out, want))
}

/// The major premise's point and the two facts every predecessor step wants.
struct Major<'a> {
    /// `ā = ⟦a⟧`.
    aa: &'a Term,
    /// `Γ ⊢ ā ∈ acc(A,R̄)`.
    in_acc: &'a Thm,
    /// `Γ ⊢ ā ∈ A` — **A0**.
    in_carrier: &'a Thm,
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 3 — the induction hypothesis, in two spellings
// ─────────────────────────────────────────────────────────────────────────────

/// `Γ ⊢ ih(accrec,A,R̄,ā) = ⟦fun y hy => Acc.rec α r C m y (h y hy)⟧`.
///
/// Both sides are Replacement images over `A`, so [`same_rows`] closes it given
/// that the rows agree; the row equation is [`row_agrees`], and it is itself a
/// second instance of the same lemma one level down.
#[allow(clippy::too_many_arguments)]
fn rows_agree(
    ip: &mut Interp,
    ind: &Name,
    cx: &Cx<'_>,
    at: &At,
    head_tm: &Term,
    elim: &RecAccElim,
    major: &Major<'_>,
    ih_tm: &Term,
    lam: &Term,
) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind, w, Cause::Threading);
    let sums = ip.prelude.tower.sums.clone();
    let base = cx.ra.ra.base.clone();
    let (lsite, ldom) = ip.as_lam(lam).ok_or_else(|| bad(LAM))?;
    if ldom != cx.a {
        return Err(bad(LAM))
    }

    // ── the rows agree at every `y ∈ A` ─────────────────────────────────────
    let mut sc = Scopes::new();
    let tok_y = sc.open(&mut ip.env_mut(), cx.a.clone());
    let (yv, y, y_in_a) = {
        let s = sc.get(0).ok_or_else(|| bad(ROWS))?;
        (s.var(), s.term(), s.assumption().clone())
    };
    // `t(p⃗,y)` off the body symbol and onto the λ it abbreviates.
    //
    // [`Interp::body_unfold`] rather than a bare `inst_all` against the site's
    // axiom. The two produce the same `Term`, and once did not deliver the same
    // thing: only `body_unfold` filed the result's applicative structure, and a
    // term absent from that table could not be taken apart — which is exactly
    // what [`Interp::as_lam`] does to it next.
    let t_at_y = ip.body_unfold(&lsite, y.clone()).ok_or_else(|| bad(LAM))?;
    let inner = t_at_y.concl().as_eq().ok_or_else(|| bad(LAM))?.1.clone();
    let row_eq = row_agrees(
        ip, ind, cx, at, head_tm, elim, major, &y, &y_in_a, &inner, &mut sc,
    )?;
    let back = derived::eq_symm(&mut ip.env_mut(), &t_at_y).ok_or_else(|| bad(LAM))?;
    let body = eq_trans(ip, &row_eq, &back).ok_or_else(|| bad(ROWS))?;
    let pw = sc.close(tok_y).discharge(&body).map_err(|_| bad(ROWS))?;

    // ── …hence the two images are one set ───────────────────────────────────
    let pv = ip.fresh_var();
    let p = Term::var(pv);
    let ep_t = ep_of(base.ep, cx.graph.clone(), y.clone(), major.aa.clone());
    let v1 = cval_of(&sums, ep_t, ip.app(cx.accrec.clone(), y.clone()));
    let v2 = {
        let mut a = lsite.holes.clone();
        a.push(y.clone());
        Term::apply(lsite.t, a)
    };
    let ax1 = derived::inst_all(
        &base.ih_ax,
        &[
            cx.accrec.clone(),
            cx.a.clone(),
            cx.graph.clone(),
            major.aa.clone(),
            p.clone(),
        ],
    )
    .ok_or_else(|| bad(ROWS))?;
    let ax2 = {
        let mut a = lsite.holes.clone();
        a.push(ldom);
        a.push(p);
        derived::inst_all(&lsite.lam_ax, &a).ok_or_else(|| bad(LAM))?
    };
    let rule = same_rows(
        &mut ip.env_mut(),
        &sums.ap.sets,
        pv,
        yv,
        &cx.a,
        &v1,
        &v2,
        ih_tm,
        lam,
        &ax1,
        &ax2,
    )
    .ok_or_else(|| bad(ROWS))?;
    Thm::mp(&rule, &pw).ok_or_else(|| bad(ROWS))
}

/// `Γ ⊢ cval(ep(R̄,y,ā), app(accrec,y)) = ⟦fun hy : r y ā => Acc.rec … y (h y hy)⟧`
/// under `y ∈ A`.
///
/// The conditional value is `prod(c,{v})` and the λ is a graph over
/// `⟦r y ā⟧`, so once the two domains are identified — which is
/// [`RecAccApparatus::edge_value`](crate::rec_acc_ap::RecAccApparatus), the one
/// statement in the project wanting both graph bridges — this is [`same_rows`]
/// again, at a row whose value does not mention the binder.
///
/// # The caller's stack, and what happens on a `None`
///
/// `sc` is the caller's own [`Scopes`], and the scope this opens is abandoned —
/// token and all — on every early exit between the open and the close. That is
/// sound because the caller `?`-propagates out of the function that owns the
/// stack, so the stack is dropped rather than closed; and a caller that did not
/// would abort at [`Scopes::close`]'s LIFO assertion rather than derive
/// anything. `mini/src/scope.rs`'s I2 is the argument in full.
#[allow(clippy::too_many_arguments)]
fn row_agrees(
    ip: &mut Interp,
    ind: &Name,
    cx: &Cx<'_>,
    at: &At,
    head_tm: &Term,
    elim: &RecAccElim,
    major: &Major<'_>,
    y: &Term,
    y_in_a: &Thm,
    inner: &Term,
    sc: &mut Scopes,
) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind, w, Cause::Threading);
    let sums = ip.prelude.tower.sums.clone();
    let base = cx.ra.ra.base.clone();
    let up = sums.ap.sets.up;
    let (l2, rel) = ip.as_lam(inner).ok_or_else(|| bad(LAM))?;

    // `⟦r y ā⟧ ∈ ⟦Prop⟧`, and the check inside `rel_typing` is what identifies
    // the λ's declared domain with `app(app(⟦r⟧,y),ā)`.
    let rel_u0 = crate::rec_acc::rel_typing(
        ip,
        &cx.r,
        &cx.r_mem,
        y,
        y_in_a,
        major.aa,
        major.in_carrier,
        &rel,
    )
    .ok_or_else(|| bad(EDGE))?;
    let edge_eq = Thm::mp(
        &derived::inst_all(
            &cx.ra.edge_value,
            &[cx.a.clone(), cx.r.clone(), y.clone(), major.aa.clone()],
        )
        .ok_or_else(|| bad(EDGE))?,
        &derived::and_intro(y_in_a, &derived::and_intro(major.in_carrier, &rel_u0)),
    )
    .ok_or_else(|| bad(EDGE))?;

    let v = ip.app(cx.accrec.clone(), y.clone());
    let ep_t = ep_of(base.ep, cx.graph.clone(), y.clone(), major.aa.clone());
    let sing_v = derived::singleton(up, v.clone());
    let cval_eq =
        derived::congr_arg(&mut ip.env_mut(), sums.prod.prod, &[ep_t, sing_v], 0, &edge_eq)
            .ok_or_else(|| bad(EDGE))?;
    let at_rel = cval_of(&sums, rel.clone(), v.clone());
    if cval_eq.concl().as_eq().ok_or_else(|| bad(EDGE))?.1 != at_rel {
        return Err(bad(EDGE))
    }

    // ── the value agrees at every proof `w ∈ ⟦r y ā⟧` ───────────────────────
    let tok_w = sc.open(&mut ip.env_mut(), rel.clone());
    let (wv, w, w_in_rel) = {
        let s = sc.get(0).ok_or_else(|| bad(SPINE))?;
        (s.var(), s.term(), s.assumption().clone())
    };
    let spine_eq = recursive_call(
        ip, ind, cx, at, head_tm, elim, major, y, y_in_a, &rel_u0, &w_in_rel,
    )?;
    let t2_at_w = ip.body_unfold(&l2, w).ok_or_else(|| bad(LAM))?;
    let (t2_lhs, t2_rhs) = {
        let (l, r) = t2_at_w.concl().as_eq().ok_or_else(|| bad(LAM))?;
        (l.clone(), r.clone())
    };
    if spine_eq.concl().as_eq().ok_or_else(|| bad(SPINE))?.1 != t2_rhs {
        return Err(bad(SPINE))
    }
    let back = derived::eq_symm(&mut ip.env_mut(), &t2_at_w).ok_or_else(|| bad(LAM))?;
    let body = eq_trans(ip, &spine_eq, &back).ok_or_else(|| bad(SPINE))?;
    if body.concl().as_eq().map(|(l, r)| (l.clone(), r.clone())) != Some((v.clone(), t2_lhs))
    {
        return Err(bad(SPINE))
    }
    let pw = sc.close(tok_w).discharge(&body).map_err(|_| bad(SPINE))?;

    // ── …hence the constant function and the λ-graph are one set ────────────
    let pv = ip.fresh_var();
    let p = Term::var(pv);
    let ax1 = cval_members(&mut ip.env_mut(), &sums, &rel, &v, &p).ok_or_else(|| bad(ROWS))?;
    let ax2 = {
        let mut a = l2.holes.clone();
        a.push(rel.clone());
        a.push(p);
        derived::inst_all(&l2.lam_ax, &a).ok_or_else(|| bad(LAM))?
    };
    let v2 = {
        let mut a = l2.holes.clone();
        a.push(Term::var(wv));
        Term::apply(l2.t, a)
    };
    let rule = same_rows(
        &mut ip.env_mut(),
        &sums.ap.sets,
        pv,
        wv,
        &rel,
        &v,
        &v2,
        &at_rel,
        inner,
        &ax1,
        &ax2,
    )
    .ok_or_else(|| bad(ROWS))?;
    let same = Thm::mp(&rule, &pw).ok_or_else(|| bad(ROWS))?;
    eq_trans(ip, &cval_eq, &same).ok_or_else(|| bad(ROWS))
}

/// `Γ ⊢ app(accrec,y) = ⟦Acc.rec α r C m y (h y hy)⟧`, under `w ∈ ⟦r y ā⟧`.
///
/// **This is step 1 a second time**, and it is what `MINI-HANDOFF.md` §27's
/// sizing left out: the interpretation of a Lean application is an applicative
/// spine over the stored eliminator, not the value that spine β-reduces to. What
/// closes it is `pack_app` — and the accessibility it wants is **A4** at the
/// major premise, whose pair antecedent is available exactly because the proof
/// binder `w` inhabits `⟦r y ā⟧`.
#[allow(clippy::too_many_arguments)]
fn recursive_call(
    ip: &mut Interp,
    ind: &Name,
    cx: &Cx<'_>,
    at: &At,
    head_tm: &Term,
    elim: &RecAccElim,
    major: &Major<'_>,
    y: &Term,
    y_in_a: &Thm,
    rel_u0: &Thm,
    w_in_rel: &Thm,
) -> Result<Thm, Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind, w, Cause::Threading);
    let point = ip.point();

    // `w` is a proof, so it is `•` — which is what puts the pair in the graph.
    let w_pt = ip.point_of_proof(rel_u0, w_in_rel).ok_or_else(|| bad(PRED))?;
    let pt_eq_w = derived::eq_symm(&mut ip.env_mut(), &w_pt).ok_or_else(|| bad(PRED))?;
    let pt_in_rel = ip.retarget_subject(w_in_rel, &pt_eq_w).ok_or_else(|| bad(PRED))?;
    let pair = Thm::mp(
        &derived::inst_all(
            &cx.ac.pair_in_graph,
            &[cx.a.clone(), cx.r.clone(), y.clone(), major.aa.clone()],
        )
        .ok_or_else(|| bad(PRED))?,
        &derived::and_intro(y_in_a, &derived::and_intro(major.in_carrier, &pt_in_rel)),
    )
    .ok_or_else(|| bad(PRED))?;
    // **A4** — a predecessor of an accessible point is accessible.
    let y_in_acc = derived::inst_all(
        &cx.ra.pred_closed,
        &[cx.a.clone(), cx.graph.clone(), y.clone(), major.aa.clone()],
    )
    .and_then(|x| Thm::mp(&x, major.in_acc))
    .and_then(|x| Thm::mp(&x, &derived::and_intro(y_in_a, &pair)))
    .ok_or_else(|| bad(PRED))?;

    // β down the stored nest at `y` and at the accessibility proof, then off
    // mini's own name and onto `pack`.
    let pt_acc = acc_point(ip, cx, at, y, y_in_a, &y_in_acc).ok_or_else(|| bad(SPINE))?;
    let jargs = [
        cx.a.clone(),
        cx.r.clone(),
        cx.cm.clone(),
        cx.em.clone(),
        y.clone(),
        point,
    ];
    let jmems = [
        at.mems[0].clone(),
        at.mems[1].clone(),
        at.mems[2].clone(),
        at.mems[3].clone(),
        y_in_a.clone(),
        pt_acc,
    ];
    let (_, jbeta) = ip.beta_spine(head_tm, &jargs, &jmems).ok_or_else(|| bad(NEST))?;
    let jax = derived::inst_all(&elim.ax, &jargs).ok_or_else(|| bad(ABBREV))?;
    let to_pack = eq_trans(ip, &jbeta, &jax).ok_or_else(|| bad(ABBREV))?;
    let pa = derived::inst_all(
        &cx.ra.ra.pack_app,
        &[cx.a.clone(), cx.graph.clone(), cx.t.clone(), cx.em.clone()],
    )
    .and_then(|x| derived::inst_all(&x, std::slice::from_ref(y)))
    .and_then(|x| Thm::mp(&x, &y_in_acc))
    .ok_or_else(|| bad(SPINE))?;
    let to_value = eq_trans(ip, &to_pack, &pa).ok_or_else(|| bad(SPINE))?;
    derived::eq_symm(&mut ip.env_mut(), &to_value).ok_or_else(|| bad(SPINE))
}

// ─────────────────────────────────────────────────────────────────────────────
// The one lemma both levels are closed by
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ (∀y. (y ∈ D → v₁ = v₂)) → S₁ = S₂`, given that each `Sᵢ` has exactly the
/// members `{ ⟨y, vᵢ⟩ : y ∈ D }`.
///
/// The `A = A'` instance of [`derived::ext::image_ext_n`], taking the two
/// membership conditions as *theorems* rather than as symbols with a parameter
/// prefix. That is what it has to be here: `derived`'s `ih(g,A,R,x)` carries its
/// domain in the **middle** of its argument list, and an `img`-shaped
/// extensionality wants it last, so the library lemma cannot be instantiated at
/// this pair however the prefixes are threaded. Nothing else differs — this is
/// that derivation with the domain equation dropped, which is why the shapes are
/// checked rather than assumed.
///
/// Both axioms must be **unconditional**: the checks below read `concl()`, and
/// [`Thm::mp`] would union an open `Γ` into a result this header states as `⊢`.
/// That guard is also what makes the three generalisations here safe — every
/// other ingredient is a kernel primitive or a `derived` composition of them,
/// so nothing in this derivation can carry a hypothesis for `y` or `p` to be
/// free in. They are nevertheless spelled [`Thm::gen_checked`] and not
/// `Thm::gen`: R6′ I3 (`ci/check-mini-scope.sh`, `MINI-DESIGN.md` §4.4) is what
/// keeps a module whose *callers* work under open scopes from holding a
/// panicking entry behind an argument, and the `None` costs one `?` in a
/// function that already declines by returning `None`.
#[allow(clippy::too_many_arguments)]
fn same_rows(
    env: &mut kernel::Env,
    sets: &Sets,
    pv: FreeVar,
    yv: FreeVar,
    dom: &Term,
    v1: &Term,
    v2: &Term,
    s1: &Term,
    s2: &Term,
    ax1: &Thm,
    ax2: &Thm,
) -> Option<Thm> {
    use derived::{
        a1i, and_left, and_right, com12, exists_elim_imp, exists_intro_imp, hyp_and, hyp_mp,
        iff_mp, iff_mpr, syl, uncurry,
    };
    if !derived::all_unconditional(&[ax1, ax2]) {
        return None
    }
    let (p, y) = (Term::var(pv), Term::var(yv));
    // The caller's terms must be clear of the variable this derivation binds.
    if v1.occurs_free(pv) || v2.occurs_free(pv) || dom.occurs_free(pv) || dom.occurs_free(yv) {
        return None
    }
    let ext = Thm::ax_extensionality(env);

    let mem_yd = Formula::mem(y.clone(), dom.clone());
    let pair1 = sets.pair(y.clone(), v1.clone());
    let pair2 = sets.pair(y.clone(), v2.clone());
    let eq_p1 = Formula::eq(p.clone(), pair1);
    let eq_p2 = Formula::eq(p.clone(), pair2);
    let body1 = Formula::and(mem_yd.clone(), eq_p1.clone());
    let body2 = Formula::and(mem_yd.clone(), eq_p2.clone());
    let ex1 = Formula::exists(yv, body1.clone());
    let ex2 = Formula::exists(yv, body2.clone());
    let mem1 = Formula::mem(p.clone(), s1.clone());
    let mem2 = Formula::mem(p.clone(), s2.clone());

    // The two membership conditions, at exactly the shape this argument needs.
    if *ax1.concl() != Formula::iff(mem1.clone(), ex1.clone()) {
        return None
    }
    if *ax2.concl() != Formula::iff(mem2.clone(), ex2.clone()) {
        return None
    }

    let h = Formula::forall(yv, Formula::imp(mem_yd.clone(), Formula::eq(v1.clone(), v2.clone())));

    // ── Forward ─────────────────────────────────────────────────────────────
    let k = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_yd = syl(&k_body, &and_left(mem_yd.clone(), eq_p1.clone()))?;
    let k_eq = syl(&k_body, &and_right(mem_yd.clone(), eq_p1.clone()))?;
    let k_vv = hyp_mp(&syl(&k_h, &Thm::ax_inst(h.clone(), y.clone())?)?, &k_yd)?;
    let w1 = env.fresh_var();
    let carry1 = Thm::eq_leibniz(
        v1.clone(),
        v2.clone(),
        w1,
        Formula::eq(p.clone(), sets.pair(y.clone(), Term::var(w1))),
    );
    let k_eq2 = hyp_mp(&hyp_mp(&a1i(&carry1, k), &k_vv)?, &k_eq)?;
    let k_ex2 = syl(&hyp_and(&k_yd, &k_eq2)?, &exists_intro_imp(yv, body2.clone(), y.clone())?)?;
    let fwd_ex = com12(&exists_elim_imp(
        yv,
        &Thm::gen_checked(yv, &com12(&uncurry(&k_ex2)?)?)?,
        &Formula::imp(h.clone(), ex2.clone()),
    )?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(ax1)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(ax2)?, h.clone()),
    )?;

    // ── Backward, with one symmetry ─────────────────────────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_yd = syl(&j_body, &and_left(mem_yd.clone(), eq_p2.clone()))?;
    let j_eq = syl(&j_body, &and_right(mem_yd.clone(), eq_p2.clone()))?;
    let j_vv = hyp_mp(&syl(&j_h, &Thm::ax_inst(h.clone(), y.clone())?)?, &j_yd)?;
    let j_vv = syl(&j_vv, &derived::eq_symm_imp(env, v1.clone(), v2.clone()))?;
    let w2 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(
        v2.clone(),
        v1.clone(),
        w2,
        Formula::eq(p.clone(), sets.pair(y.clone(), Term::var(w2))),
    );
    let j_eq1 = hyp_mp(&hyp_mp(&a1i(&carry2, j), &j_vv)?, &j_eq)?;
    let j_ex1 = syl(&hyp_and(&j_yd, &j_eq1)?, &exists_intro_imp(yv, body1.clone(), y.clone())?)?;
    let bwd_ex = com12(&exists_elim_imp(
        yv,
        &Thm::gen_checked(yv, &com12(&uncurry(&j_ex1)?)?)?,
        &Formula::imp(h.clone(), ex1.clone()),
    )?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(ax2)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(ax1)?, h.clone()),
    )?;

    // ── Same members, hence equal ───────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_p = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), Formula::iff(mem1, mem2))?,
        &Thm::gen_checked(pv, &h_iff)?,
    )?;
    let out = syl(&all_p, &derived::inst_all(&ext, &[s1.clone(), s2.clone()])?)?;
    // The statement the callers rely on; a release build must not skip it.
    (*out.concl() == Formula::imp(h, Formula::eq(s1.clone(), s2.clone()))).then_some(out)
}

/// `⊢ p ∈ cval(c,v) ↔ ∃w. (w ∈ c ∧ p = ⟨w,v⟩)`.
///
/// `cval(c,v)` is `prod(c,{v})`, whose membership condition has one existential
/// too many: `derived::rec_acc::cval`'s header spells exactly this reduction and
/// the module derives no theorem for it, because nothing there needs the members
/// one at a time. [`same_rows`] does.
///
/// Takes terms only and no theorem, so the result is unconditional by
/// construction and its three generalisations cannot meet a hypothesis; they go
/// through [`Thm::gen_checked`] anyway, for R6′ I3's reason — see
/// [`same_rows`].
fn cval_members(
    env: &mut kernel::Env,
    sums: &Sums,
    c: &Term,
    v: &Term,
    p: &Term,
) -> Option<Thm> {
    use derived::{
        a1i, and_left, and_right, exists_intro_imp, exists_mono, hyp_and, hyp_mp, iff_mp, iff_mpr,
        imp_refl, inst_all, syl,
    };
    let sets = &sums.ap.sets;
    let sing = derived::singleton(sets.up, v.clone());
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (x, y) = (Term::var(xv), Term::var(yv));

    let at = inst_all(&sums.prod.prod_ax, &[c.clone(), sing.clone(), p.clone()])?;
    let mem_xc = Formula::mem(x.clone(), c.clone());
    let mem_ys = Formula::mem(y.clone(), sing.clone());
    let eq_pxy = Formula::eq(p.clone(), sets.pair(x.clone(), y.clone()));
    let eq_pxv = Formula::eq(p.clone(), sets.pair(x.clone(), v.clone()));
    let inner_body = Formula::and(mem_ys.clone(), eq_pxy.clone());
    let inner = Formula::exists(yv, inner_body.clone());
    if *at.concl()
        != Formula::iff(
            Formula::mem(p.clone(), sums.prod.of(c.clone(), sing.clone())),
            Formula::exists(xv, Formula::and(mem_xc.clone(), inner.clone())),
        )
    {
        return None
    }

    // `∃y. (y ∈ {v} ∧ p = ⟨x,y⟩)` and `p = ⟨x,v⟩`, each way.
    let ms = inst_all(&sums.ap.mem_sing, &[v.clone(), y.clone()])?;
    let to_eq = syl(&and_left(mem_ys.clone(), eq_pxy.clone()), &iff_mp(&ms)?)?;
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        y.clone(),
        v.clone(),
        w,
        Formula::eq(p.clone(), sets.pair(x.clone(), Term::var(w))),
    );
    let inner_fwd = hyp_mp(
        &hyp_mp(&a1i(&carry, inner_body.clone()), &to_eq)?,
        &and_right(mem_ys.clone(), eq_pxy.clone()),
    )?;
    let inner_fwd = derived::exists_elim_imp(yv, &Thm::gen_checked(yv, &inner_fwd)?, &eq_pxv)?;
    let v_in_sing = Thm::mp(
        &iff_mpr(&inst_all(&sums.ap.mem_sing, &[v.clone(), v.clone()])?)?,
        &Thm::eq_refl(v.clone()),
    )?;
    let inner_bwd = syl(
        &hyp_and(&a1i(&v_in_sing, eq_pxv.clone()), &imp_refl(eq_pxv.clone()))?,
        &exists_intro_imp(yv, inner_body, v.clone())?,
    )?;

    // …lifted under `∃x. (x ∈ c ∧ ·)`.
    let mono_fwd = {
        let step = hyp_and(
            &and_left(mem_xc.clone(), inner.clone()),
            &syl(&and_right(mem_xc.clone(), inner.clone()), &inner_fwd)?,
        )?;
        exists_mono(xv, &Thm::gen_checked(xv, &step)?)?
    };
    let mono_bwd = {
        let step = hyp_and(
            &and_left(mem_xc.clone(), eq_pxv.clone()),
            &syl(&and_right(mem_xc.clone(), eq_pxv.clone()), &inner_bwd)?,
        )?;
        exists_mono(xv, &Thm::gen_checked(xv, &step)?)?
    };

    let fwd = syl(&iff_mp(&at)?, &mono_fwd)?;
    let bwd = syl(&mono_bwd, &iff_mpr(&at)?)?;
    let out = derived::and_intro(&fwd, &bwd);
    let want = Formula::iff(
        Formula::mem(p.clone(), cval_of(sums, c.clone(), v.clone())),
        Formula::exists(xv, Formula::and(mem_xc, eq_pxv)),
    );
    (*out.concl() == want).then_some(out)
}

// ─────────────────────────────────────────────────────────────────────────────

/// Take `n` applications off a spine: the head and the arguments, in order.
fn peel_app(ip: &Interp, t: &Term, n: usize) -> Option<(Term, Vec<Term>)> {
    let ap = ip.prelude.ap.app;
    let mut cur = t.clone();
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let (f, args) = ip.parts_of(&cur)?;
        if f != ap || args.len() != 2 {
            return None
        }
        out.push(args[1].clone());
        cur = args[0].clone();
    }
    out.reverse();
    Some((cur, out))
}

fn eq_trans(ip: &mut Interp, a: &Thm, b: &Thm) -> Option<Thm> {
    derived::eq_trans(&mut ip.env_mut(), a, b)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **The row lemma is the library's own extensionality, at the instance
    /// where the library has one.**
    ///
    /// [`same_rows`] is stated over two arbitrary membership conditions because
    /// `derived`'s `ih(g,A,R,x)` carries its domain in the *middle* of its
    /// argument list and no `img`-shaped lemma can be instantiated at it. That
    /// generality is what makes it worth pinning: at the one instance both
    /// sides are `cval`, [`derived::rec_acc::Base::cval_ext`] states exactly the
    /// same implication, and the two conclusions are compared **whole**.
    ///
    /// Non-vacuity, three ways: the two values are *different* variables, so
    /// nothing passes on reflexivity; the comparison is against a theorem this
    /// module never touches, derived from `prod_inhabited` rather than from
    /// Extensionality over rows; and both inputs are checked unconditional, so a
    /// `Γ` riding in from [`cval_members`] would fail here rather than later.
    #[test]
    fn the_row_lemma_agrees_with_the_library_at_a_constant_fibre() {
        let mut ip = Interp::new();
        let ra = ip.rec_acc().expect("the recursor's apparatus builds");
        let sums = ip.prelude.tower.sums.clone();
        let cval_ext = ra.ra.base.cval_ext.clone();

        let (cv, v1v, v2v, pv, yv) = (
            ip.fresh_var(),
            ip.fresh_var(),
            ip.fresh_var(),
            ip.fresh_var(),
            ip.fresh_var(),
        );
        let (c, v1, v2, p) =
            (Term::var(cv), Term::var(v1v), Term::var(v2v), Term::var(pv));
        assert_ne!(v1, v2, "the two values must not already be one term");

        let ax1 = cval_members(&mut ip.env_mut(), &sums, &c, &v1, &p)
            .expect("cval's members, one at a time");
        let ax2 = cval_members(&mut ip.env_mut(), &sums, &c, &v2, &p).expect("…at the other value");
        assert!(ax1.hyps().is_empty() && ax2.hyps().is_empty(), "both are ⊢, not Γ ⊢");

        let (s1, s2) = (
            cval_of(&sums, c.clone(), v1.clone()),
            cval_of(&sums, c.clone(), v2.clone()),
        );
        let sets = sums.ap.sets.clone();
        let rule = same_rows(
            &mut ip.env_mut(), &sets, pv, yv, &c, &v1, &v2, &s1, &s2, &ax1, &ax2,
        )
        .expect("the extensionality");
        let want = derived::inst_all(&cval_ext, &[c, v1, v2]).expect("cval_ext at these terms");
        assert_eq!(
            *rule.concl(),
            *want.concl(),
            "the row lemma and cval_ext must state the same implication"
        );
        assert!(rule.hyps().is_empty(), "no binder is open, so Γ must be empty");
    }

    /// **`cval`'s members, one at a time** — the reduction
    /// `derived::rec_acc::cval`'s header spells and derives no theorem for.
    ///
    /// Asserted against the formula rather than against a shape: the whole
    /// point of the lemma is that the *inner* existential over `{v}` is gone,
    /// and a derivation that left it in place would still be sound and would
    /// make [`same_rows`] decline four functions deeper.
    #[test]
    fn cval_has_one_row_per_member_of_its_condition() {
        let ip = Interp::new();
        let sums = ip.prelude.tower.sums.clone();
        let (cv, vv, pv, xv) = (
            ip.fresh_var(),
            ip.fresh_var(),
            ip.fresh_var(),
            ip.fresh_var(),
        );
        let (c, v, p) = (Term::var(cv), Term::var(vv), Term::var(pv));
        let out = cval_members(&mut ip.env_mut(), &sums, &c, &v, &p).expect("the members");
        let want = Formula::iff(
            Formula::mem(p.clone(), cval_of(&sums, c.clone(), v.clone())),
            Formula::exists(
                xv,
                Formula::and(
                    Formula::mem(Term::var(xv), c),
                    Formula::eq(p, sums.ap.sets.pair(Term::var(xv), v)),
                ),
            ),
        );
        assert_eq!(*out.concl(), want, "the condition is one existential, not two");
        assert!(out.hyps().is_empty(), "⊢, not Γ ⊢");
    }
}
