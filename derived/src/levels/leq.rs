//! The certified `≤`-kit for levels, at the width the corpus demands:
//! the `⊆` facts that feed `imax` collapse, and the flagship
//! **`imax(u,v) = v` under a guarded `u ≤ v`**.
//!
//! # Interface
//!
//! Over a caller-supplied [`Rec`] (one chain of definitional extensions, so
//! `∅`, `succ` and `ω` are *its* symbols) plus the caller's [`Ite0`] and
//! [`Order`] built over the same chain, writing `m ∪ n` for
//! [`Order::max`] and `ite0(g,a,b)` for [`Ite0::at`], the exports are
//!
//! ```text
//! ⊢ ∀x. ∅ ⊆ x                                                  [Leq::empty_sub]
//! ⊢ ∀x. x ⊆ x                                                  [Leq::sub_refl]
//! ⊢ ∀v. ((v ∈ ω ∧ ¬(v = ∅)) → succ(∅) ⊆ v)                     [Leq::one_sub_nonzero]
//! ⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → (p ∪ q) ⊆ v)                  [Leq::union_sub]
//! ⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → ite0(q, ∅, p ∪ q) ⊆ v)        [Leq::imax_sub]
//! ⊢ ∀u ∀v. (((u ∈ ω ∧ v ∈ ω) ∧ (¬(v = ∅) → u ⊆ v))
//!             → ite0(v, ∅, u ∪ v) = v)                         [Leq::imax_absorb]
//! ```
//!
//! where `⊆` is spelled [`kernel::thm::subset`] exactly. This is the kit for
//! the single dominant identity the `init-prelude` measurement found
//! (`LEVELPOLY.md` §1.5, and the raw-versus-canon census under §5.4 blocker 3):
//! 1005 of 2103 remaining misses are a raw `imax(a,…,u)` chain whose canonical
//! form is the bare parameter `u`, with the `a`s being `0`, `1`, `max(1,u)`
//! and nested `imax` chains — every one an instance of `imax(a,b) = b` when
//! `a ≤ b`. [`Leq::imax_absorb`] is that identity; the `⊆` exports above it
//! are exactly the facts that discharge its premise at those `a`s
//! (`empty_sub` for `0`, `one_sub_nonzero` for `1`, `union_sub`/`imax_sub`
//! for `max`/`imax` arms, `sub_refl` for the bare parameter).
//!
//! **The guard on the premise is the content.** `imax(1,u) = u` holds for
//! every `u ∈ ω` *including* `u = ∅`, but `1 ⊆ ∅` is false — the `u ⊆ v`
//! premise is only ever needed in the branch where `v ≠ ∅`, and stating it as
//! `¬(v = ∅) → u ⊆ v` is what makes the lemma usable at `u = 1`. An unguarded
//! premise would be a strictly weaker lemma the corpus's dominant shape could
//! not use.
//!
//! **This is not the full certified `leq` mirror** of `LEVELPOLY.md` §1.5.
//! Not built here: the succ/succ recursion arm (`u ⊆ v → succ u ⊆ succ v`),
//! the max-on-the-left split (`(max a b) ≤ v` elimination is here as
//! [`Leq::union_sub`], but `u ≤ max a b` introduction beyond
//! [`Order::max_ub`] is not), the offset-counting arms of the checker's
//! decision procedure, and the parameter case split (that is
//! [`Order::cases`], consumed by a future mirror, not re-exported here).
//!
//! # Where the content is
//!
//! [`Leq::sub_refl`] is [`crate::cumul::subset_refl`] **re-exported, not
//! re-derived** — one construction per fact; it is carried in the bundle so
//! the level consumer has one place to look. [`Leq::empty_sub`] is the
//! `∀`-closed form of the inline `∅ ⊆ S` arguments the crate has at fixed
//! seeds (`cumul/enums.rs`, `anchor/wtype.rs`): `z ∈ ∅` refutes itself and
//! `ex_falso` supplies `z ∈ x`. [`Leq::one_sub_nonzero`] cases on
//! [`Order::zero_least`]'s disjunction — `∅ = v` is killed against the
//! `¬(v = ∅)` hypothesis, and from `∅ ∈ v` the successor's membership
//! condition sends every `z ∈ succ(∅)` to `∅`, hence into `v` (no
//! transitivity needed: `succ(∅)`'s members are refuted or equal to `∅`).
//! [`Leq::union_sub`] is [`Order::mem_bin_union_iff`] pointwise.
//! [`Leq::imax_sub`] and [`Leq::imax_absorb`] are classical cases on the
//! guard `v = ∅` (resp. `q = ∅`), exactly the route
//! [`crate::levels::apparatus`]'s `derive_imax_in_omega` takes — `or(P,¬P)`
//! unabbreviates to `¬P → ¬P`, so excluded middle *is* [`imp_refl`]. In the
//! zero branch [`Ite0::when_zero`] computes the term to `∅` and the goal is
//! `empty_sub` (resp. the branch hypothesis reversed); in the nonzero branch
//! [`Ite0::when_nonzero`] computes it to the union and `union_sub`
//! (resp. absorption — [`crate::levels::order`]'s `union_absorb_one`, the
//! same Extensionality argument [`Order::max_absorb`] spends, reused rather
//! than re-derived) finishes. `imax_absorb`'s `ω` conjunct is not consumed by
//! the derivation — the identity holds for all sets — but is kept in the
//! statement because the consumer instantiates it at level interpretations
//! whose `ω`-membership it holds anyway, and the pinned kit shape is the
//! measured one; a caller without the facts in hand should ask for the
//! stronger unguarded statement instead of weakening this one.

use kernel::{Env, Formula, Term, Thm};

use crate::levels::ite0::Ite0;
use crate::levels::order::{union_absorb_one, Order};
use crate::recursion::Rec;
use crate::separation::hyp_syl;
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, ex_falso, gen_all, hyp_mp, hyp_or_elim, iff_mp,
    imp_refl, inst_all, mpd_const, syl, uncurry,
};

/// The `≤`-kit, assembled once over a caller-supplied chain. See the module
/// header for the statements.
pub struct Leq {
    /// `⊢ ∀x. ∅ ⊆ x`.
    pub empty_sub: Thm,
    /// `⊢ ∀x. x ⊆ x` — [`crate::cumul::subset_refl`], re-exported.
    pub sub_refl: Thm,
    /// `⊢ ∀v. ((v ∈ ω ∧ ¬(v = ∅)) → succ(∅) ⊆ v)`.
    pub one_sub_nonzero: Thm,
    /// `⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → (p ∪ q) ⊆ v)`.
    pub union_sub: Thm,
    /// `⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → ite0(q, ∅, p ∪ q) ⊆ v)`.
    pub imax_sub: Thm,
    /// `⊢ ∀u ∀v. (((u ∈ ω ∧ v ∈ ω) ∧ (¬(v = ∅) → u ⊆ v)) → ite0(v, ∅, u ∪ v) = v)`
    /// — the flagship; see the module header on the guard.
    pub imax_absorb: Thm,
}

/// Derive the lot over the caller's chain.
///
/// `r`'s `∅` must be the one `i`'s guard compares against and `r`'s pairing
/// and union the ones `ord`'s `max` is spelled with — the same one-chain rule
/// [`crate::levels::srt`] enforces. Returns `None` on a symbol mismatch.
pub fn leq(env: &mut Env, r: &Rec, i: &Ite0, ord: &Order) -> Option<Leq> {
    if i.empty != r.ap.empty {
        return None
    }
    if ord.sets.up != r.ap.sets.up || ord.sets.un != r.ap.sets.un {
        return None
    }

    let empty_sub = empty_sub(env, r)?;
    let sub_refl = crate::cumul::subset_refl(env)?;
    let one_sub_nonzero = one_sub_nonzero(env, r, ord)?;
    let union_sub = union_sub(env, ord)?;
    let imax_sub = imax_sub(env, r, i, ord, &empty_sub, &union_sub)?;
    let imax_absorb = imax_absorb(env, r, i, ord)?;

    Some(Leq { empty_sub, sub_refl, one_sub_nonzero, union_sub, imax_sub, imax_absorb })
}

/// `⊢ ∀x. ∅ ⊆ x` — nothing is a member of `∅`, so every member of `∅` is
/// anywhere one likes.
fn empty_sub(env: &mut Env, r: &Rec) -> Option<Thm> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));
    let body = syl(
        &inst_all(&r.core().empty_ax, std::slice::from_ref(&tz))?,
        &ex_falso(Formula::mem(tz, tx.clone())),
    )?;
    let sub = Thm::gen(z, &body);
    debug_assert_eq!(
        *sub.concl(),
        kernel::thm::subset(env, r.zero(), tx),
        "empty_sub: unexpected shape"
    );
    Some(Thm::gen(x, &sub))
}

/// `⊢ ∀v. ((v ∈ ω ∧ ¬(v = ∅)) → succ(∅) ⊆ v)` — the level `1` is below every
/// nonzero natural.
///
/// [`Order::zero_least`] gives `∅ ∈ v ∨ ∅ = v`; the equation contradicts the
/// `¬(v = ∅)` hypothesis (one symmetry step — mind the direction), and from
/// `∅ ∈ v` the successor's membership condition finishes: a `z ∈ succ(∅)` is
/// `z ∈ ∅` (refuted) or `z = ∅` (rewrite `∅ ∈ v`).
fn one_sub_nonzero(env: &mut Env, r: &Rec, ord: &Order) -> Option<Thm> {
    let core = r.core();
    let v = env.fresh_var();
    let tv = Term::var(v);
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let v_om = Formula::mem(tv.clone(), r.omega());
    let np = Formula::not(Formula::eq(tv.clone(), zero.clone()));
    let g = Formula::and(v_om.clone(), np.clone());
    let sub = kernel::thm::subset(env, one.clone(), tv.clone());

    // ── `∅ ∈ v → succ(∅) ⊆ v`, under `H := ∅ ∈ v ∧ z ∈ succ(∅)` ─────────────
    let mem0 = Formula::mem(zero.clone(), tv.clone());
    let z = env.fresh_var();
    let tz = Term::var(z);
    let mem_z1 = Formula::mem(tz.clone(), one.clone());
    let mem_zv = Formula::mem(tz.clone(), tv.clone());
    let split = iff_mp(&inst_all(&core.succ_ax, &[zero.clone(), tz.clone()])?)?;
    let h_disj = syl(&and_right(mem0.clone(), mem_z1.clone()), &split)?;
    // Case `z ∈ ∅`: refuted outright.
    let case_empty = syl(
        &inst_all(&core.empty_ax, std::slice::from_ref(&tz))?,
        &ex_falso(mem_zv.clone()),
    )?;
    let h_left = a1i(&case_empty, Formula::and(mem0.clone(), mem_z1.clone()));
    // Case `z = ∅`: rewrite `∅ ∈ v` along the reversed equation.
    let hole = env.fresh_var();
    let leib =
        Thm::eq_leibniz(zero.clone(), tz.clone(), hole, Formula::mem(Term::var(hole), tv.clone()));
    let case_eq = com12(&syl(&eq_symm_imp(env, tz.clone(), zero.clone()), &leib)?)?;
    let h_right = syl(&and_left(mem0.clone(), mem_z1.clone()), &case_eq)?;
    let h_goal = hyp_or_elim(&h_disj, &h_left, &h_right)?;
    let mem_imp = uncurry(&h_goal)?;
    let mem_sub = Thm::mp(
        &Thm::ax_dist(z, mem0.clone(), Formula::imp(mem_z1, mem_zv))?,
        &Thm::gen(z, &mem_imp),
    )?;
    debug_assert_eq!(
        *mem_sub.concl(),
        Formula::imp(mem0, sub.clone()),
        "one_sub_nonzero: the membership case drifted"
    );

    // ── Assemble under `G := v ∈ ω ∧ ¬(v = ∅)` ──────────────────────────────
    let g_disj = syl(
        &and_left(v_om.clone(), np.clone()),
        &inst_all(&ord.zero_least, std::slice::from_ref(&tv))?,
    )?;
    let g_left = a1i(&mem_sub, g.clone());
    // Case `∅ = v`: symmetry, then the hypothesis refutes it.
    let g_np = and_right(v_om, np);
    let g_eq_false = com12(&syl(&eq_symm_imp(env, zero, tv), &com12(&g_np)?)?)?;
    let g_right = hyp_syl(&g_eq_false, &a1i(&ex_falso(sub.clone()), g.clone()))?;
    let body = hyp_or_elim(&g_disj, &g_left, &g_right)?;
    debug_assert_eq!(*body.concl(), Formula::imp(g, sub), "one_sub_nonzero: unexpected shape");
    Some(Thm::gen(v, &body))
}

/// `⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → (p ∪ q) ⊆ v)` — the union is the least
/// upper bound's easy half, by the membership condition pointwise.
fn union_sub(env: &mut Env, ord: &Order) -> Option<Thm> {
    let (p, q, v, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tq, tv, tz) = (Term::var(p), Term::var(q), Term::var(v), Term::var(z));
    let bu = ord.max(tp.clone(), tq.clone());
    let sub_p = kernel::thm::subset(env, tp.clone(), tv.clone());
    let sub_q = kernel::thm::subset(env, tq.clone(), tv.clone());
    let h = Formula::and(sub_p.clone(), sub_q.clone());
    let mem_zbu = Formula::mem(tz.clone(), bu.clone());
    let mem_zv = Formula::mem(tz.clone(), tv.clone());

    // Under `L := H ∧ z ∈ p ∪ q`, split the membership and spend one premise.
    let at = inst_all(&ord.mem_bin_union_iff, &[tp, tq, tz.clone()])?;
    let l_disj = syl(&and_right(h.clone(), mem_zbu.clone()), &iff_mp(&at)?)?;
    let l_h = and_left(h.clone(), mem_zbu.clone());
    let via_p = syl(
        &and_left(sub_p.clone(), sub_q.clone()),
        &Thm::ax_inst(sub_p.clone(), tz.clone())?,
    )?;
    let via_q = syl(&and_right(sub_p, sub_q.clone()), &Thm::ax_inst(sub_q, tz)?)?;
    let l_goal = hyp_or_elim(&l_disj, &syl(&l_h, &via_p)?, &syl(&l_h, &via_q)?)?;
    let h_imp = uncurry(&l_goal)?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_zbu, mem_zv))?,
        &Thm::gen(z, &h_imp),
    )?;
    debug_assert_eq!(
        *h_sub.concl(),
        {
            let sub = kernel::thm::subset(env, bu, tv);
            Formula::imp(h, sub)
        },
        "union_sub: unexpected shape"
    );
    Some(gen_all(&[p, q, v], &h_sub))
}

/// `⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → ite0(q, ∅, p ∪ q) ⊆ v)` — the `imax`
/// interpretation is below any common bound, whichever branch it takes.
///
/// Classical cases on `q = ∅`: the zero branch computes to `∅` and
/// [`empty_sub`] finishes; the nonzero branch computes to the union and
/// [`union_sub`] finishes. Both transports are one Leibniz step against the
/// reversed branch equation.
fn imax_sub(
    env: &mut Env,
    r: &Rec,
    i: &Ite0,
    ord: &Order,
    empty_sub: &Thm,
    union_sub: &Thm,
) -> Option<Thm> {
    let (p, q, v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tq, tv) = (Term::var(p), Term::var(q), Term::var(v));
    let zero = r.zero();
    let muv = ord.max(tp.clone(), tq.clone());
    let t = i.at(tq.clone(), zero.clone(), muv.clone());
    let sub_p = kernel::thm::subset(env, tp.clone(), tv.clone());
    let sub_q = kernel::thm::subset(env, tq.clone(), tv.clone());
    let h = Formula::and(sub_p, sub_q);
    let goal = kernel::thm::subset(env, t.clone(), tv.clone());
    let pf = Formula::eq(tq.clone(), zero.clone());
    let npf = Formula::not(pf.clone());

    // ── Case `P`: the term is `∅`, and `∅ ⊆ v` unconditionally ──────────────
    let wz = inst_all(&i.when_zero, &[tq.clone(), zero.clone(), muv.clone()])?;
    debug_assert_eq!(
        *wz.concl(),
        Formula::imp(pf.clone(), Formula::eq(t.clone(), zero.clone())),
        "imax_sub: when_zero instantiated to an unexpected shape"
    );
    let e_sub = inst_all(empty_sub, std::slice::from_ref(&tv))?;
    let hole = env.fresh_var();
    let sub_hole = kernel::thm::subset(env, Term::var(hole), tv.clone());
    let leib_z = Thm::eq_leibniz(zero.clone(), t.clone(), hole, sub_hole);
    let z_gives = mpd_const(&syl(&eq_symm_imp(env, t.clone(), zero.clone()), &leib_z)?, &e_sub)?;
    let case_p = a1i(&syl(&wz, &z_gives)?, h.clone());
    debug_assert_eq!(
        *case_p.concl(),
        Formula::imp(h.clone(), Formula::imp(pf.clone(), goal.clone())),
        "imax_sub: the P-case has an unexpected shape"
    );

    // ── Case `¬P`: the term is `p ∪ q`, and `union_sub` finishes ────────────
    let wnz = inst_all(&i.when_nonzero, &[tq.clone(), zero, muv.clone()])?;
    debug_assert_eq!(
        *wnz.concl(),
        Formula::imp(npf.clone(), Formula::eq(t.clone(), muv.clone())),
        "imax_sub: when_nonzero instantiated to an unexpected shape"
    );
    let h_mu = inst_all(union_sub, &[tp, tq, tv.clone()])?;
    debug_assert_eq!(
        *h_mu.concl(),
        {
            let sub_mu = kernel::thm::subset(env, muv.clone(), tv.clone());
            Formula::imp(h.clone(), sub_mu)
        },
        "imax_sub: union_sub instantiated to an unexpected shape"
    );
    let hole2 = env.fresh_var();
    let sub_hole2 = kernel::thm::subset(env, Term::var(hole2), tv);
    let leib_m = Thm::eq_leibniz(muv.clone(), t.clone(), hole2, sub_hole2);
    let sy = syl(&eq_symm_imp(env, t, muv), &leib_m)?;
    let h_eq_gives = syl(&h_mu, &com12(&sy)?)?;
    let case_np = hyp_syl(&a1i(&wnz, h.clone()), &h_eq_gives)?;
    debug_assert_eq!(
        *case_np.concl(),
        Formula::imp(h.clone(), Formula::imp(npf.clone(), goal.clone())),
        "imax_sub: the ¬P-case has an unexpected shape"
    );

    // ── Excluded middle: `or(P, ¬P)` is `¬P → ¬P`, i.e. `imp_refl` ──────────
    let em = a1i(&imp_refl(npf), h.clone());
    debug_assert_eq!(
        em.concl().as_imp()?.1,
        Formula::or(pf, Formula::not(Formula::eq(Term::var(q), r.zero()))),
        "imax_sub: excluded middle is not the or the case split eliminates"
    );
    let out = hyp_or_elim(&em, &case_p, &case_np)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, goal), "imax_sub: unexpected shape");
    Some(gen_all(&[p, q, v], &out))
}

/// `⊢ ∀u ∀v. (((u ∈ ω ∧ v ∈ ω) ∧ (¬(v = ∅) → u ⊆ v)) → ite0(v, ∅, u ∪ v) = v)`
/// — **`imax(u,v) = v` whenever `u ≤ v`**, the premise guarded by `v ≠ ∅`.
///
/// Classical cases on `v = ∅`. In the zero branch [`Ite0::when_zero`]
/// computes the term to `∅` and the goal is the branch hypothesis reversed;
/// the guarded premise is never consulted, which is exactly what makes the
/// lemma usable at `u ⊄ v` instances like `(1, ∅)`. In the nonzero branch
/// [`Ite0::when_nonzero`] computes it to `u ∪ v`, the guard discharges the
/// premise to `u ⊆ v`, and `union_absorb_one` (the [`Order`] file's
/// Extensionality argument, reused) collapses the union to `v`.
fn imax_absorb(env: &mut Env, r: &Rec, i: &Ite0, ord: &Order) -> Option<Thm> {
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let (tu, tv) = (Term::var(u), Term::var(v));
    let zero = r.zero();
    let omega = r.omega();
    let muv = ord.max(tu.clone(), tv.clone());
    let t = i.at(tv.clone(), zero.clone(), muv.clone());
    let j = Formula::and(
        Formula::mem(tu.clone(), omega.clone()),
        Formula::mem(tv.clone(), omega),
    );
    let pf = Formula::eq(tv.clone(), zero.clone());
    let npf = Formula::not(pf.clone());
    let sub_uv = kernel::thm::subset(env, tu.clone(), tv.clone());
    let guard = Formula::imp(npf.clone(), sub_uv.clone());
    let h = Formula::and(j.clone(), guard.clone());
    let goal = Formula::eq(t.clone(), tv.clone());

    // ── Case `P`: the term is `∅`, and `∅ = v` is the hypothesis reversed ───
    let wz = inst_all(&i.when_zero, &[tv.clone(), zero.clone(), muv.clone()])?;
    debug_assert_eq!(
        *wz.concl(),
        Formula::imp(pf.clone(), Formula::eq(t.clone(), zero.clone())),
        "imax_absorb: when_zero instantiated to an unexpected shape"
    );
    let hole = env.fresh_var();
    let leib_z =
        Thm::eq_leibniz(zero.clone(), tv.clone(), hole, Formula::eq(t.clone(), Term::var(hole)));
    let p_chain = syl(&eq_symm_imp(env, tv.clone(), zero.clone()), &leib_z)?;
    let case_p = a1i(&hyp_mp(&p_chain, &wz)?, h.clone());
    debug_assert_eq!(
        *case_p.concl(),
        Formula::imp(h.clone(), Formula::imp(pf.clone(), goal.clone())),
        "imax_absorb: the P-case has an unexpected shape"
    );

    // ── Case `¬P`, under `L := H ∧ ¬P`: discharge the guard, absorb ─────────
    let l = Formula::and(h.clone(), npf.clone());
    let l_np = and_right(h.clone(), npf.clone());
    let l_guard = syl(&and_left(h.clone(), npf.clone()), &and_right(j, guard))?;
    let l_sub = hyp_mp(&l_guard, &l_np)?;
    let absorb = union_absorb_one(env, &ord.sets, &ord.mem_bin_union_iff, false)?;
    let l_union_eq = syl(&l_sub, &inst_all(&absorb, &[tu, tv.clone()])?)?;
    debug_assert_eq!(
        *l_union_eq.concl(),
        Formula::imp(l.clone(), Formula::eq(muv.clone(), tv)),
        "imax_absorb: absorption instantiated to an unexpected shape"
    );
    let wnz = inst_all(&i.when_nonzero, &[Term::var(v), zero, muv.clone()])?;
    let l_teq = syl(&l_np, &wnz)?;
    let hole2 = env.fresh_var();
    let leib_m = Thm::eq_leibniz(
        muv.clone(),
        Term::var(v),
        hole2,
        Formula::eq(t.clone(), Term::var(hole2)),
    );
    let l_chain = syl(&l_union_eq, &leib_m)?;
    let l_goal = hyp_mp(&l_chain, &l_teq)?;
    let case_np = uncurry(&l_goal)?;
    debug_assert_eq!(
        *case_np.concl(),
        Formula::imp(h.clone(), Formula::imp(npf.clone(), goal.clone())),
        "imax_absorb: the ¬P-case has an unexpected shape"
    );

    // ── Excluded middle, as in `derive_imax_in_omega` ───────────────────────
    let em = a1i(&imp_refl(npf), h.clone());
    debug_assert_eq!(
        em.concl().as_imp()?.1,
        Formula::or(pf, Formula::not(Formula::eq(Term::var(v), r.zero()))),
        "imax_absorb: excluded middle is not the or the case split eliminates"
    );
    let out = hyp_or_elim(&em, &case_p, &case_np)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, goal), "imax_absorb: unexpected shape");
    Some(gen_all(&[u, v], &out))
}
