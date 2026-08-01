//! The two ι rules.
//!
//! # Interface
//!
//! Private to [`crate::wnat_rec`]; surfaced as
//! [`crate::wnat_rec::NatRec::iota_zero`] and
//! [`crate::wnat_rec::NatRec::iota_succ`]:
//!
//! ```text
//! ⊢ ∀z ∀s ∀T. (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)
//! ⊢ ∀z ∀s ∀T ∀n. ((HYP ∧ n ∈ N) →
//!       app(nrec(z,s,T), ⟨inr •,{⟨•,n⟩}⟩) = app(app(s,n), app(nrec(z,s,T), n)))
//! ```
//!
//! # What makes these the payoff
//!
//! [`crate::wrec_total`] supplies the general ι rule — the recursor's value at
//! `⟨a,f⟩` is the step applied to `⟨a,⟨f, comp(rec,f,B(a))⟩⟩` — and everything
//! here is the work of specialising it at the two constructors: computing the
//! composite `comp` at a one-point fibre, and rewriting the step's argument into
//! the form [`super::computes`] evaluated.
//!
//! `iota_succ_at` is the one that matters. Its right-hand side mentions `nrec`
//! again, so it is not an equation two constant terms could satisfy by accident;
//! `tests/wnat_rec.rs` checks that its two sides are different terms and that the
//! recursive occurrence is really there.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::wnat::Nat;
use crate::point_fun::PointFun;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, and_left, and_right, hyp_and, hyp_mp, inst_all, syl, uncurry};

use super::shared::{congr_ctx, gen_under};

/// From `⊢ H → ∀v₁…∀vₙ. φ` infer `⊢ H → φ[t₁…tₙ]`.
fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// `⊢ HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z` — **ι at `N.zero`**.
///
/// Line for line [`crate::wbool_rec`]'s: the fibre `B(inl •)` is `0`, so the
/// composite is over an empty domain and [`crate::wrec_unit::comp_empty_domain`]
/// collapses it, leaving the step applied to `k₀`. The one thing that differs is
/// that the fibre has to be *computed* — for `Bool` the family was literally
/// `∅`, here it is `rec₊(λ_.0, λ_.1)` and [`crate::wnat::Nat::fibre_zero`] is
/// what says its value at the left tag is `0`.
#[allow(clippy::too_many_arguments)]
pub(super) fn iota_zero_at(
    env: &mut Env,
    wt: &Wtype,
    nat: &Nat,
    r: &Recursor,
    dis: &Thm,
    app_zero: &Thm,
    nrec: &Term,
    step: &Term,
    z: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point, zero_s) = (s.unit(), s.point(), s.zero());
    let tag = s.inl(point.clone());
    let (hyp, _) = dis.concl().as_imp()?;

    // `inl • ∈ 1+1`, and `∅ ∈ fs(B(inl •), N)`.
    let tag_mem = Thm::mp(
        &inst_all(&s.inl_mem, &[one.clone(), one.clone(), point.clone()])?,
        &s.unit_mem,
    )?;
    let hole = env.fresh_var();
    let f_in = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                zero_s.clone(),
                wt.fibre(nat.fam.clone(), tag.clone()),
                hole,
                Formula::mem(zero_s.clone(), s.fs.of(Term::var(hole), nat.ty.clone())),
            ),
            &crate::eq_symm(env, &nat.fibre_zero)?,
        )?,
        &inst_all(&wt.empty_fun, std::slice::from_ref(&nat.ty))?,
    )?;
    let fired = hyp_mp(
        &hyp_inst(dis, &[tag.clone(), zero_s.clone()])?,
        &a1i(&and_intro(&tag_mem, &f_in), hyp.clone()),
    )?;

    // The composite over the empty fibre is `∅`, so the step's argument is `k₀`.
    let fib = wt.fibre(nat.fam.clone(), tag.clone());
    let coll = crate::congr_arg(
        env,
        r.comp,
        &[nrec.clone(), zero_s.clone(), fib],
        2,
        &nat.fibre_zero,
    )?;
    let empty = inst_all(
        &crate::wrec_unit::comp_empty_domain(env, ap, r.comp, &r.comp_ax)?,
        &[nrec.clone(), zero_s.clone()],
    )?;
    let to_empty = crate::eq_trans(env, &coll, &empty)?;
    let rhs = congr_ctx(env, &to_empty, |q| {
        ap.apply(
            step.clone(),
            ap.sets.pair(tag.clone(), ap.sets.pair(zero_s.clone(), q)),
        )
    })?;
    let at_key = crate::eq_trans(env, &rhs, app_zero)?;
    let out = hyp_eq_trans(env, &fired, &a1i(&at_key, hyp.clone()))?;
    if *out.concl()
        != Formula::imp(
            hyp,
            Formula::eq(ap.apply(nrec.clone(), wt.sup(tag, zero_s)), z.clone()),
        )
    {
        return None
    }
    Some(out)
}

/// `⊢ (HYP ∧ n ∈ N) → app(nrec, ⟨inr •,{⟨•,n⟩}⟩) = app(app(s,n), app(nrec,n))`
/// — **ι at `N.succ`, with the recursive call live**.
///
/// The fibre `B(inr •)` is `1`, so nothing collapses. Three things have to be
/// supplied that `Bool` never needed:
///
/// * the subterm family is the one-point graph `{⟨•,n⟩}`, in `fs(1,N)` by
///   [`crate::point_fun::point_in_funspace`];
/// * the composite `comp(nrec,{⟨•,n⟩},1)` has to be shown to lie in `FT(T)`
///   before the step can be applied to it — [`crate::wrec_typing::composite_typed`]
///   with its hypothesis discharged from `nrec ∈ fs(N,T)`;
/// * and the recursive value is read back out with
///   [`crate::wrec_typing::composite_app`] at `b := •`, which is the lemma the
///   `N.rec` feasibility read landed in advance.
#[allow(clippy::too_many_arguments)]
pub(super) fn iota_succ_at(
    env: &mut Env,
    wt: &Wtype,
    nat: &Nat,
    r: &Recursor,
    pf: &PointFun,
    dis: &Thm,
    fs_thm: &Thm,
    app_succ: &Thm,
    nrec: &Term,
    step: &Term,
    su: &Term,
    t: &Term,
    nv: FreeVar,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point) = (s.unit(), s.point());
    let tag = s.inr(point.clone());
    let tn = Term::var(nv);
    let pfn = PointFun::of(s, point.clone(), tn.clone());
    let (hyp, _) = dis.concl().as_imp()?;
    let mem_n = Formula::mem(tn.clone(), nat.ty.clone());
    let p = Formula::and(hyp.clone(), mem_n.clone());
    let p_hyp = and_left(hyp.clone(), mem_n.clone());
    let p_n = and_right(hyp.clone(), mem_n.clone());

    // ── `{⟨•,n⟩} ∈ fs(1,N)`, and the same at the fibre `B(inr •)` ───────────
    let in_fs_1 = syl(
        &p_n,
        &inst_all(&pf.in_fs, &[point.clone(), tn.clone(), nat.ty.clone()])?,
    )?;
    let hole = env.fresh_var();
    let to_fibre = Thm::mp(
        &Thm::eq_leibniz(
            one.clone(),
            wt.fibre(nat.fam.clone(), tag.clone()),
            hole,
            Formula::mem(pfn.clone(), s.fs.of(Term::var(hole), nat.ty.clone())),
        ),
        &crate::eq_symm(env, &nat.fibre_succ)?,
    )?;
    let p_f_fib = syl(&in_fs_1, &to_fibre)?;

    let tag_mem = Thm::mp(
        &inst_all(&s.inr_mem, &[one.clone(), one.clone(), point.clone()])?,
        &s.unit_mem,
    )?;
    let fired = hyp_mp(
        &syl(&p_hyp, &hyp_inst(dis, &[tag.clone(), pfn.clone()])?)?,
        &hyp_and(&a1i(&tag_mem, p.clone()), &p_f_fib)?,
    )?;

    // ── The fibre is `1`, so the composite has domain `1` ───────────────────
    let fib = wt.fibre(nat.fam.clone(), tag.clone());
    let cmp = comp_of(r.comp, nrec.clone(), pfn.clone(), one.clone());
    let coll = crate::congr_arg(
        env,
        r.comp,
        &[nrec.clone(), pfn.clone(), fib.clone()],
        2,
        &nat.fibre_succ,
    )?;
    let rhs = congr_ctx(env, &coll, |q| {
        ap.apply(
            step.clone(),
            ap.sets.pair(tag.clone(), ap.sets.pair(pfn.clone(), q)),
        )
    })?;
    let at_one = hyp_eq_trans(env, &fired, &a1i(&rhs, p.clone()))?;

    // ── `comp(nrec,{⟨•,n⟩},1) ∈ fs(1,T)` ────────────────────────────────────
    let p_nrec = syl(&p_hyp, fs_thm)?;
    let p_val = {
        let bv = env.fresh_var();
        let tb = Term::var(bv);
        let mem_b = Formula::mem(tb.clone(), one.clone());
        let k = Formula::and(p.clone(), mem_b.clone());
        let k_b = and_right(p.clone(), mem_b.clone());
        let k_p = and_left(p.clone(), mem_b.clone());
        let k_pt = syl(&k_b, &inst_all(&s.unit_eta, std::slice::from_ref(&tb))?)?;
        // `K → app(f,b) = n`, the one-point graph computing at `•`.
        let k_cong = hyp_congr(env, &k_pt, |q| ap.apply(pfn.clone(), q))?;
        let k_app = hyp_eq_trans(
            env,
            &k_cong,
            &a1i(&inst_all(&pf.app, &[point.clone(), tn.clone()])?, k.clone()),
        )?;
        let k_in_t = hyp_mp(
            &a1i(
                &inst_all(
                    &wt.app_mem,
                    &[nat.ty.clone(), t.clone(), nrec.clone(), tn.clone()],
                )?,
                k.clone(),
            ),
            &hyp_and(&syl(&k_p, &p_nrec)?, &syl(&k_p, &p_n)?)?,
        )?;
        let k_back = hyp_eq_symm(env, &k_app)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            tn.clone(),
            ap.apply(pfn.clone(), tb.clone()),
            hole,
            Formula::mem(ap.apply(nrec.clone(), Term::var(hole)), t.clone()),
        );
        let k_goal = hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &k_back)?, &k_in_t)?;
        gen_under(bv, &p, &uncurry(&k_goal)?)?
    };
    let ct = inst_all(
        &crate::wrec_typing::composite_typed(env, s, r.comp, &r.comp_ax)?,
        &[nrec.clone(), pfn.clone(), one.clone(), t.clone()],
    )?;
    let p_cmp_fs = hyp_mp(&a1i(&ct, p.clone()), &p_val)?;

    // ── …and both arguments are where the step's Replacement ranges ─────────
    let sub = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
        let inc = inst_all(&s.fs.fs_sub, &[one.clone(), cod.clone()])?;
        let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
        syl(prem, &at)
    };
    let p_fw = sub(&syl(&p_n, &inst_all(&pf.in_fs, &[point.clone(), tn.clone(), nat.ty.clone()])?)?, &nat.ty, &pfn)?;
    let p_ft = sub(&p_cmp_fs, t, &cmp)?;
    let p_step = hyp_mp(
        &a1i(&inst_all(app_succ, &[pfn.clone(), cmp.clone()])?, p.clone()),
        &hyp_and(&p_fw, &p_ft)?,
    )?;
    let at_val = hyp_eq_trans(env, &at_one, &p_step)?;

    // ── The value: `app(f,•) = n` and `app(cmp,•) = app(nrec,n)` ────────────
    let f_at = inst_all(&pf.app, &[point.clone(), tn.clone()])?;
    let comp_app = Thm::mp(
        &inst_all(
            &crate::wrec_typing::composite_app(env, ap, r.comp, &r.comp_ax)?,
            &[nrec.clone(), pfn.clone(), one.clone(), point.clone()],
        )?,
        &s.unit_mem,
    )?;
    let f_lift = congr_ctx(env, &f_at, |q| ap.apply(nrec.clone(), q))?;
    let c_at = crate::eq_trans(env, &comp_app, &f_lift)?;
    let v1 = congr_ctx(env, &f_at, |q| {
        ap.apply(
            ap.apply(su.clone(), q),
            ap.apply(cmp.clone(), point.clone()),
        )
    })?;
    let v2 = congr_ctx(env, &c_at, |q| {
        ap.apply(ap.apply(su.clone(), tn.clone()), q)
    })?;
    let value = crate::eq_trans(env, &v1, &v2)?;
    let out = hyp_eq_trans(env, &at_val, &a1i(&value, p.clone()))?;
    if *out.concl()
        != Formula::imp(
            p,
            Formula::eq(
                ap.apply(nrec.clone(), wt.sup(tag, pfn)),
                ap.apply(
                    ap.apply(su.clone(), tn.clone()),
                    ap.apply(nrec.clone(), tn.clone()),
                ),
            ),
        )
    {
        return None
    }
    Some(out)
}
