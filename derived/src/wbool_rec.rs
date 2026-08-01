//! **The recursor for a two-constructor enumeration**, and its ι rule —
//! Lean's `Bool.rec`, computed.
//!
//! # What this is
//!
//! [`crate::enums`] interprets `Bool` as the W-type `enum(1+1) = W(1+1, ∅, U(1+1))`
//! with constructors `⟨inl •, ∅⟩` and `⟨inr •, ∅⟩`. [`crate::wrec`] and
//! [`crate::wrec_total`] build the W-recursor and prove the **unguarded** ι
//! rule for it. This file is the join: it packs Lean's two minor premises into
//! the single step `e` the W-recursor takes, discharges both of that rule's
//! hypotheses, and reads off the two computation rules
//!
//! ```text
//! Bool.rec fls tru Bool.false  ≡  fls        Bool.rec fls tru Bool.true  ≡  tru
//! ```
//!
//! as equations between sets, **unconditional in `fls` and `tru`**.
//!
//! # The construction
//!
//! ```text
//! A  := 1 + 1        B := ∅        u := U(1+1)        W := W(A,B,u)
//! T  := {fls, tru}                                    the target
//! kf := ⟨inl •, ⟨∅,∅⟩⟩          kt := ⟨inr •, ⟨∅,∅⟩⟩   the two step arguments
//! e  := {⟨kf, fls⟩, ⟨kt, tru⟩}                        the packed step
//! brec(fls,tru) := wrec(A, B, u, T, e)
//! ```
//!
//! The W-recursor applies its step to the **triple** `⟨a, ⟨f, r⟩⟩` — the tag,
//! the subterm family and the family of recursive values. Every fibre here is
//! empty, so `f` and `r` are forced to be `∅` ([`crate::wtype::empty_funspace`])
//! and the triple takes exactly two values, one per tag. The step is therefore
//! a graph on two points, which is [`crate::twopoint`]; `INDUCTIVES.md` suggests
//! packing with `rec₊`, and that would work too, but `rec₊` is a function of the
//! *tag* and what has to be applied here is a function of the whole triple.
//!
//! `T := {fls, tru}` rather than anything read off a motive. That is what makes
//! [`crate::wrec_total`]'s `step_typed` hypothesis discharge with no assumption
//! about the minor premises at all: the step's only two values are `fls` and
//! `tru`, and an unordered pair contains both by construction.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inl •, ∅⟩) = fls        [BoolRec::iota_false]
//! ⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inr •, ∅⟩) = tru         [BoolRec::iota_true]
//! ```
//!
//! Both are unconditional, both have `⟨inl •,∅⟩` and `⟨inr •,∅⟩` — the terms
//! [`crate::enums::Enum2`] gives Lean's `Bool.false` and `Bool.true` — on the
//! left, and both compute: the right-hand side is the caller's own variable,
//! not another application. Callers need nothing else from this file.
//!
//! # Non-vacuity
//!
//! Everything [`crate::wrec`] proves would hold of an empty recursor, which is
//! why [`crate::wrec_unit`] exists. The two equations above are the same kind of
//! witness at a *different* instance, and a stronger one: they are parametric in
//! the two values, so `brec` is a recursor that returns whatever it was given,
//! and `tests/wbool_rec.rs` checks the two sides of each are different terms.
//! The two are also *distinct* equations at one recursor — the same `brec(fls,tru)`
//! returns `fls` at one constructor and `tru` at the other — so neither can be
//! an artefact of a degenerate step.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::bound::Bound;
use crate::funcs::Apply;
use crate::twopoint::TwoPoint;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, and_left, and_right, exists_elim_imp, gen_all, hyp_mp, hyp_or_elim, inst_all,
    syl, uncurry, upair_members,
};

/// The two computation rules, at fresh universally quantified variables.
pub struct BoolRec {
    /// `⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inl •, ∅⟩) = fls`.
    pub iota_false: Thm,
    /// `⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inr •, ∅⟩) = tru`.
    pub iota_true: Thm,
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
fn gen_under(v: FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
fn congr<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}

/// From `⊢ x = y` and `⊢ y = z` infer `⊢ x = z`.
fn eq_trans(env: &mut Env, xy: &Thm, yz: &Thm) -> Option<Thm> {
    let (x, y) = xy.concl().as_eq()?;
    let (y2, z) = yz.concl().as_eq()?;
    if y != y2 {
        return None
    }
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(y, z, hole, Formula::eq(x, Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, yz)?, xy)
}

impl BoolRec {
    /// The tag set `1 + 1`.
    pub fn tags(wt: &Wtype) -> Term {
        let s = &wt.sums;
        s.sum_of(s.unit(), s.unit())
    }

    /// The step's argument at the `i`th tag: `⟨inl •, ⟨∅,∅⟩⟩` or `⟨inr •, ⟨∅,∅⟩⟩`.
    pub fn key(wt: &Wtype, second: bool) -> Term {
        let s = &wt.sums;
        let z = wt.empty();
        let tag = if second { s.inr(s.point()) } else { s.inl(s.point()) };
        s.ap.sets.pair(tag, s.ap.sets.pair(z.clone(), z))
    }

    /// The target `{fls, tru}`.
    pub fn target(ap: &Apply, fls: &Term, tru: &Term) -> Term {
        Term::apply(ap.sets.up, vec![fls.clone(), tru.clone()])
    }

    /// The packed step `{⟨kf, fls⟩, ⟨kt, tru⟩}`.
    pub fn step(wt: &Wtype, fls: &Term, tru: &Term) -> Term {
        TwoPoint::of(
            &wt.sums.ap,
            Self::key(wt, false),
            fls.clone(),
            Self::key(wt, true),
            tru.clone(),
        )
    }

    /// The recursor term `brec(fls,tru) = wrec(1+1, ∅, U(1+1), T, e)`.
    pub fn of(wt: &Wtype, bnd: &Bound, r: &Recursor, fls: &Term, tru: &Term) -> Term {
        let tags = Self::tags(wt);
        let u = Term::apply(bnd.lu, vec![tags.clone()]);
        r.of(
            &tags,
            &wt.empty(),
            &u,
            &Self::target(&wt.sums.ap, fls, tru),
            &Self::step(wt, fls, tru),
        )
    }

    /// Derive both computation rules.
    ///
    /// `closed` is [`crate::enums::enum_closed`], `iota` is
    /// [`crate::wrec_total::iota`], and `tp` the [`TwoPoint`] built over the
    /// same [`Apply`] — all three have to be about the *same* symbols, which is
    /// why none of them is rebuilt here.
    #[allow(clippy::too_many_arguments)]
    pub fn over(
        env: &mut Env,
        wt: &Wtype,
        bnd: &Bound,
        r: &Recursor,
        closed: &Thm,
        iota: &Thm,
        tp: &TwoPoint,
    ) -> Option<BoolRec> {
        let (fv, tv) = (env.fresh_var(), env.fresh_var());
        let (fls, tru) = (Term::var(fv), Term::var(tv));

        let keys_ne = keys_distinct(env, wt)?;
        let steps = step_values(env, wt, tp, &keys_ne, &fls, &tru)?;
        let st = step_typed(env, wt, bnd, &steps, &fls, &tru)?;
        let cl = inst_all(closed, std::slice::from_ref(&Self::tags(wt)))?;

        let iota_false =
            iota_at(env, wt, bnd, r, iota, &cl, &st, &steps, false, &fls, &tru)?;
        let iota_true = iota_at(env, wt, bnd, r, iota, &cl, &st, &steps, true, &fls, &tru)?;
        Some(BoolRec {
            iota_false: gen_all(&[fv, tv], &iota_false),
            iota_true: gen_all(&[fv, tv], &iota_true),
        })
    }
}

/// `⊢ ¬(kf = kt)` — the step's two arguments are different sets.
///
/// They differ in their first component, and
/// [`crate::sums::Sums::disjoint`] says `inl(•) ≠ inr(•)`. This is the whole
/// content of "a two-constructor enumeration has two constructors" as far as
/// the step function is concerned, and it is what [`TwoPoint`] needs.
fn keys_distinct(env: &mut Env, wt: &Wtype) -> Option<Thm> {
    let s = &wt.sums;
    let (point, z) = (s.point(), wt.empty());
    let (l, rr) = (s.inl(point.clone()), s.inr(point.clone()));
    let inner = s.ap.sets.pair(z.clone(), z);
    let inj = inst_all(
        &s.ap.pair_inj,
        &[l.clone(), inner.clone(), rr.clone(), inner.clone()],
    )?;
    let tags_eq = Formula::eq(l.clone(), rr.clone());
    let inner_eq = Formula::eq(inner.clone(), inner.clone());
    let to_tags = syl(&inj, &and_left(tags_eq, inner_eq))?;
    let disjoint = inst_all(&s.disjoint, &[point.clone(), point])?;
    let out = syl(&to_tags, &disjoint)?;
    let _ = env;
    if *out.concl()
        != Formula::not(Formula::eq(BoolRec::key(wt, false), BoolRec::key(wt, true)))
    {
        return None
    }
    Some(out)
}

/// The two values the step takes: `⊢ app(e, kf) = fls` and `⊢ app(e, kt) = tru`.
fn step_values(
    env: &mut Env,
    wt: &Wtype,
    tp: &TwoPoint,
    keys_ne: &Thm,
    fls: &Term,
    tru: &Term,
) -> Option<(Thm, Thm)> {
    let (kf, kt) = (BoolRec::key(wt, false), BoolRec::key(wt, true));
    let at = |thm: &Thm| -> Option<Thm> {
        Thm::mp(
            &inst_all(thm, &[kf.clone(), fls.clone(), kt.clone(), tru.clone()])?,
            keys_ne,
        )
    };
    let _ = env;
    Some((at(&tp.left)?, at(&tp.right)?))
}

/// **The step is typed**, with no hypothesis on the minor premises:
///
/// ```text
/// ⊢ step_typed(1+1, ∅, U(1+1), {fls,tru}, e)
/// ```
///
/// Every fibre is `∅`, so the step's second and third arguments are forced to
/// be `∅` ([`crate::wtype::empty_funspace`]) and the first is one of the two
/// tags ([`crate::sums::Sums::sum_cases`] and
/// [`crate::sums::Sums::unit_eta`]). The step's value is then `fls` or `tru`,
/// and `{fls,tru}` contains both by [`crate::upair_members`].
fn step_typed(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    steps: &(Thm, Thm),
    fls: &Term,
    tru: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point, z) = (s.unit(), s.point(), wt.empty());
    let tags = BoolRec::tags(wt);
    let u = Term::apply(bnd.lu, vec![tags.clone()]);
    let w_t = wt.of(tags.clone(), z.clone(), u.clone());
    let t_t = BoolRec::target(ap, fls, tru);
    let e_t = BoolRec::step(wt, fls, tru);

    let prod_empty = crate::wtype::empty_product(env, s)?;
    let empty_fs = crate::wtype::empty_funspace(env, s, &prod_empty)?;

    let (av, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tr) = (Term::var(av), Term::var(fv), Term::var(rv));
    let fibre = wt.fibre(z.clone(), ta.clone());

    let ma = Formula::mem(ta.clone(), tags.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), w_t.clone()));
    let mr = Formula::mem(tr.clone(), s.fs.of(fibre.clone(), t_t.clone()));
    let front = Formula::and(ma.clone(), mf.clone());
    let p = Formula::and(front.clone(), mr.clone());
    let p_front = and_left(front.clone(), mr.clone());
    let p_mr = and_right(front.clone(), mr);
    let p_ma = syl(&p_front, &and_left(ma.clone(), mf.clone()))?;
    let p_mf = syl(&p_front, &and_right(ma.clone(), mf))?;

    // ── `f = ∅` and `r = ∅`, the fibre being empty ──────────────────────────
    let app_empty = inst_all(&wt.app_empty, std::slice::from_ref(&ta))?;
    let forced = |env: &mut Env, prem: &Thm, cod: &Term, x: &Term| -> Option<Thm> {
        let cong = congr(env, &app_empty, |t| s.fs.of(t, cod.clone()))?;
        let hole = env.fresh_var();
        let into = Thm::mp(
            &Thm::eq_leibniz(
                s.fs.of(fibre.clone(), cod.clone()),
                s.fs.of(z.clone(), cod.clone()),
                hole,
                Formula::mem(x.clone(), Term::var(hole)),
            ),
            &cong,
        )?;
        syl(prem, &syl(&into, &inst_all(&empty_fs, &[cod.clone(), x.clone()])?)?)
    };
    let p_f = forced(env, &p_mf, &w_t, &tf)?;
    let p_r = forced(env, &p_mr, &t_t, &tr)?;

    let step_of = |x: &Term, y: &Term, w: &Term| {
        ap.apply(e_t.clone(), ap.sets.pair(x.clone(), ap.sets.pair(y.clone(), w.clone())))
    };
    let e1 = hyp_congr(env, &p_f, |t| step_of(&ta, &t, &tr))?;
    let e2 = hyp_congr(env, &p_r, |t| step_of(&ta, &z, &t))?;
    let collapse = hyp_eq_trans(env, &e1, &e2)?; // P → app(e,⟨a,⟨f,r⟩⟩) = app(e,⟨a,⟨∅,∅⟩⟩)

    // ── At either tag, the value is in `{fls,tru}` ──────────────────────────
    let (fls_in, tru_in) = upair_members(&ap.sets.up_ax, fls, tru)?;
    let at_key = |env: &mut Env, second: bool| -> Option<Thm> {
        let (eq, mem) = if second { (&steps.1, &tru_in) } else { (&steps.0, &fls_in) };
        let back = crate::eq_symm(env, eq)?;
        let hole = env.fresh_var();
        Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    if second { tru.clone() } else { fls.clone() },
                    ap.apply(e_t.clone(), BoolRec::key(wt, second)),
                    hole,
                    Formula::mem(Term::var(hole), t_t.clone()),
                ),
                &back,
            )?,
            mem,
        )
    };
    let at_left = at_key(env, false)?;
    let at_right = at_key(env, true)?;

    let goal = Formula::mem(step_of(&ta, &z, &z), t_t.clone());
    let branch = |env: &mut Env, second: bool, at_pt: &Thm| -> Option<Thm> {
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let inj = |t: Term| if second { s.inr(t) } else { s.inl(t) };
        let k = Formula::and(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(ta.clone(), inj(tx.clone())),
        );
        let k_mem = and_left(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(ta.clone(), inj(tx.clone())),
        );
        let k_eq = and_right(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(ta.clone(), inj(tx.clone())),
        );
        let k_x = syl(&k_mem, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;
        let k_inj = hyp_congr(env, &k_x, inj)?;
        let k_a = hyp_eq_trans(env, &k_eq, &k_inj)?;
        let k_back = hyp_eq_symm(env, &k_a)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            inj(point.clone()),
            ta.clone(),
            hole,
            Formula::mem(step_of(&Term::var(hole), &z, &z), t_t.clone()),
        );
        let k_goal = hyp_mp(&syl(&k_back, &leib)?, &a1i(at_pt, k.clone()))?;
        exists_elim_imp(xv, &Thm::gen(xv, &k_goal), &goal)
    };

    let cases = syl(
        &p_ma,
        &inst_all(&s.sum_cases, &[one.clone(), one.clone(), ta.clone()])?,
    )?;
    let left = a1i(&branch(env, false, &at_left)?, p.clone());
    let right = a1i(&branch(env, true, &at_right)?, p.clone());
    let at_tag = hyp_or_elim(&cases, &left, &right)?; // P → app(e,⟨a,⟨∅,∅⟩⟩) ∈ T

    // ── Back to the un-collapsed value ──────────────────────────────────────
    let back = hyp_eq_symm(env, &collapse)?;
    let hole = env.fresh_var();
    let lift = hyp_mp(
        &a1i(
            &Thm::eq_leibniz(
                step_of(&ta, &z, &z),
                step_of(&ta, &tf, &tr),
                hole,
                Formula::mem(Term::var(hole), t_t.clone()),
            ),
            p.clone(),
        ),
        &back,
    )?;
    let body = hyp_mp(&lift, &at_tag)?;

    let over_r = gen_under(rv, &front, &uncurry(&body)?)?;
    let over_f = gen_under(fv, &ma, &uncurry(&over_r)?)?;
    let out = Thm::gen(av, &over_f);
    if *out.concl() != crate::wrec_total::step_typed(env, s, wt, &tags, &z, &u, &t_t, &e_t) {
        return None
    }
    Some(out)
}

/// **ι at one constructor**: `⊢ app(brec(fls,tru), ⟨inj •, ∅⟩) = minor`.
///
/// [`crate::wrec_total::iota`] with both hypotheses discharged and both
/// premises supplied — `inj(•) ∈ 1+1` and `∅ ∈ fs(B(inj •), W)` — then the
/// composite collapsed by [`crate::wrec_unit::comp_empty_domain`] and the step
/// computed by [`TwoPoint`]. Line for line
/// [`crate::wrec_unit::unit_iota`] at a different instance.
#[allow(clippy::too_many_arguments)]
fn iota_at(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    r: &Recursor,
    iota: &Thm,
    closed: &Thm,
    st: &Thm,
    steps: &(Thm, Thm),
    second: bool,
    fls: &Term,
    tru: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point, z) = (s.unit(), s.point(), wt.empty());
    let tags = BoolRec::tags(wt);
    let u = Term::apply(bnd.lu, vec![tags.clone()]);
    let w_t = wt.of(tags.clone(), z.clone(), u.clone());
    let t_t = BoolRec::target(ap, fls, tru);
    let e_t = BoolRec::step(wt, fls, tru);
    let rec_t = BoolRec::of(wt, bnd, r, fls, tru);

    let tag = if second { s.inr(point.clone()) } else { s.inl(point.clone()) };
    let w0 = wt.sup(tag.clone(), z.clone());

    let dis = Thm::mp(
        &inst_all(iota, &[tags.clone(), z.clone(), u.clone(), t_t.clone(), e_t.clone()])?,
        &and_intro(closed, st),
    )?;
    let at_cf = inst_all(&dis, &[tag.clone(), z.clone()])?;

    // `inj(•) ∈ 1+1`.
    let tag_mem = Thm::mp(
        &inst_all(
            if second { &s.inr_mem } else { &s.inl_mem },
            &[one.clone(), one.clone(), point.clone()],
        )?,
        &s.unit_mem,
    )?;

    // `∅ ∈ fs(app(∅, inj •), W)`.
    let app_empty = inst_all(&wt.app_empty, std::slice::from_ref(&tag))?;
    let back = crate::eq_symm(env, &app_empty)?;
    let cong = congr(env, &back, |t| s.fs.of(t, w_t.clone()))?;
    let hole = env.fresh_var();
    let f_in = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                s.fs.of(z.clone(), w_t.clone()),
                s.fs.of(ap.apply(z.clone(), tag.clone()), w_t.clone()),
                hole,
                Formula::mem(z.clone(), Term::var(hole)),
            ),
            &cong,
        )?,
        &inst_all(&wt.empty_fun, std::slice::from_ref(&w_t))?,
    )?;
    let fired = Thm::mp(&at_cf, &and_intro(&tag_mem, &f_in))?;

    // The composite over an empty fibre is empty, so the step's argument is `k`.
    let coll = congr(env, &app_empty, |t| comp_of(r.comp, rec_t.clone(), z.clone(), t))?;
    let empty = inst_all(
        &crate::wrec_unit::comp_empty_domain(env, ap, r.comp, &r.comp_ax)?,
        &[rec_t.clone(), z.clone()],
    )?;
    let to_empty = eq_trans(env, &coll, &empty)?;
    let rhs = congr(env, &to_empty, |t| {
        ap.apply(e_t.clone(), ap.sets.pair(tag.clone(), ap.sets.pair(z.clone(), t)))
    })?;
    let at_key = eq_trans(env, &fired, &rhs)?;

    // …and the step computes.
    let value = if second { &steps.1 } else { &steps.0 };
    let out = eq_trans(env, &at_key, value)?;
    let minor = if second { tru.clone() } else { fls.clone() };
    if *out.concl() != Formula::eq(ap.apply(rec_t, w0), minor) {
        return None
    }
    Some(out)
}
