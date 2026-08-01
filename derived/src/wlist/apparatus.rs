//! `List α` as a W-type: the symbol, and every theorem about it.
//!
//! # Interface
//!
//! [`WList::over`] builds the symbol `lt(α)` and derives every theorem, over a
//! caller-supplied [`crate::wtype::Wtype`]. The fields are the theorems;
//! [`WList::ty_of`], [`WList::nil_term`], [`WList::cons_term`],
//! [`WList::fam_of`] and [`WList::tags_of`] build the terms. Callers need none
//! of the derivations in the sibling files.
//!
//! # What the parameter costs: one constant function on an arbitrary set
//!
//! For `N` both fibre branches were constant functions on `1`, and a constant
//! function on a *singleton* is a one-point graph, so [`crate::point_fun`]
//! covered them. Here the right branch is `λ_ : α. 1` on an **arbitrary** `α`,
//! which is not a one-point graph. It is built instead as a lambda graph
//! ([`crate::funcs::lambda`]) over a constant body symbol `co(y) = 1`, typed by
//! [`crate::ext::lam_in_funspace`] — whose hypothesis `∀y ∈ α. co(y) ∈ 2` is
//! discharged by `1 ∈ 2` alone. That is the one piece of new machinery the
//! parameter costs, and it is four lines.
//!
//! Note the asymmetry it produces: `app(fam(α), inl •) = 0` is unconditional,
//! because the left fibre function lives on `1` and `• ∈ 1` is a theorem,
//! whereas `app(fam(α), inr h) = 1` carries `h ∈ α`, because `α` is arbitrary
//! and `h` might not be in it. `cons`'s membership inherits that hypothesis —
//! which is exactly the one Lean's `cons : α → List α → List α` states.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::bound::Bound;
use crate::point_fun::PointFun;
use crate::sums::{Cases, Sums};
use crate::wrec::{hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm, gen_all, hyp_mp, inst_all, syl,
    upair_members,
};

use super::typing::typing_at;
use super::distinct::{cons_inj, distinct3, nil_ne_cons, three_in};

/// The whole development, over a free parameter `α`.
pub struct WList {
    /// `{0,1}`, the codomain of the fibre family.
    pub two: Term,
    /// The constant body symbol `co(y) = 1`.
    pub co: FnSym,
    /// `lam_co(A) = {⟨y,1⟩ : y ∈ A}` — the constant function `λ_:A. 1`.
    pub lam_co: FnSym,
    /// `⊢ ∀A. lam_co(A) ∈ fs(A, 2)`.
    pub const_fun_fs: Thm,
    /// `lt(α) = W(1+α, fam(α), U(1+α))` — the list type, as a unary symbol.
    pub lt: FnSym,
    /// `⊢ ∀α. lt(α) = W(1+α, fam(α), U(1+α))`.
    pub lt_ax: Thm,
    /// `⊢ ∀α. app(fam(α), inl •) = 0`.
    pub fibre_nil: Thm,
    /// `⊢ ∀α ∀h. (h ∈ α → app(fam(α), inr h) = 1)`.
    pub fibre_cons: Thm,
    /// `⊢ ∀α. closed(1+α, fam(α), U(1+α))` — the W-type's bound, discharged.
    pub closed: Thm,
    /// `⟨inl •, ∅⟩`.
    pub nil_t: Term,
    /// `⊢ ∀α. ⟨inl •,∅⟩ ∈ lt(α)`.
    pub nil: Thm,
    /// `⊢ ∀α ∀h ∀t. ((h ∈ α ∧ t ∈ lt(α)) → ⟨inr h,{⟨•,t⟩}⟩ ∈ lt(α))`.
    pub cons: Thm,
    /// `⊢ ∀h ∀t. ¬(⟨inl •,∅⟩ = ⟨inr h,{⟨•,t⟩}⟩)`.
    pub nil_ne_cons: Thm,
    /// `⊢ ∀h ∀t ∀h′ ∀t′. (cons h t = cons h′ t′ → (h = h′ ∧ t = t′))`.
    pub cons_inj: Thm,
    /// `⊢ ∀h. (¬(nil = c₁) ∧ (¬(nil = c₂) ∧ ¬(c₁ = c₂)))`.
    pub distinct3: Thm,
    /// `⊢ ∀α ∀h. (h ∈ α → (nil ∈ lt(α) ∧ (c₁ ∈ lt(α) ∧ c₂ ∈ lt(α))))`.
    pub three_in: Thm,
}

/// From `⊢ H → ∀v. φ` infer `⊢ H → φ[t]`.
fn hyp_inst(h_all: &Thm, t: Term) -> Option<Thm> {
    let (_, all) = h_all.concl().as_imp()?;
    syl(h_all, &Thm::ax_inst(all, t)?)
}

impl WList {
    /// The term `⟨inr h, {⟨•,t⟩}⟩`, for callers building `cons` applications.
    pub fn cons_term(wt: &Wtype, h: Term, t: Term) -> Term {
        let s = &wt.sums;
        wt.sup(s.inr(h), PointFun::of(s, s.point(), t))
    }

    /// The term `⟨inl •, ∅⟩`.
    pub fn nil_term(wt: &Wtype) -> Term {
        let s = &wt.sums;
        wt.sup(s.inl(s.point()), wt.empty())
    }

    /// The tag set `1 + α`.
    pub fn tags_of(s: &Sums, alpha: Term) -> Term { s.sum_of(s.unit(), alpha) }

    /// The fibre family `rec₊(λ_:1. 0, λ_:α. 1)`, as a set-function on `1 + α`.
    pub fn fam_of(&self, s: &Sums, cases: &Cases, alpha: Term) -> Term {
        cases.of(
            s.unit(),
            alpha.clone(),
            self.two.clone(),
            PointFun::of(s, s.point(), s.zero()),
            Term::apply(self.lam_co, vec![alpha]),
        )
    }

    /// The type term `lt(α)`.
    pub fn ty_of(&self, alpha: Term) -> Term { Term::apply(self.lt, vec![alpha]) }

    /// Build the whole development.
    ///
    /// `cases` must be [`Cases`] over the *same* [`Sums`] as `wt`, and `pf` the
    /// [`PointFun`] over it — building a second copy of either would mint new
    /// symbols whose theorems do not compose with these. `empty_u` is
    /// [`crate::enums::empty_in_least_universe`].
    pub fn over(
        env: &mut Env,
        wt: &Wtype,
        bnd: &Bound,
        cases: &Cases,
        pf: &PointFun,
        empty_u: &Thm,
    ) -> Option<WList> {
        let s = &wt.sums;
        let ap = &s.ap;
        let (zero_s, one, point) = (s.zero(), s.unit(), s.point());
        let two = Term::apply(ap.sets.up, vec![zero_s.clone(), one.clone()]);
        let (zero_in_two, one_in_two) = upair_members(&ap.sets.up_ax, &zero_s, &one)?;

        // ── the constant function `λ_:A. 1`, as a lambda graph ──────────────
        let yv = env.fresh_var();
        let (co, co_ax) = define_abbrev(env, &[yv], &one)?;
        let (lam_co, lam_co_ax) = crate::funcs::lambda(env, ap, co)?;
        let co_beta = crate::funcs::beta_conditional(env, ap, co, lam_co, &lam_co_ax)?;
        let const_fun_fs = {
            let rule = crate::ext::lam_in_funspace(env, ap, &s.prod, &s.fs, co, lam_co, &lam_co_ax)?;
            let (dv, xv) = (env.fresh_var(), env.fresh_var());
            let (td, tx) = (Term::var(dv), Term::var(xv));
            // `⊢ co(x) ∈ 2`, from `⊢ 1 ∈ 2` backwards along `co(x) = 1`.
            let co_x = inst_all(&co_ax, std::slice::from_ref(&tx))?;
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                one.clone(),
                Term::apply(co, vec![tx.clone()]),
                hole,
                Formula::mem(Term::var(hole), two.clone()),
            );
            let at_x = Thm::mp(&Thm::mp(&carry, &eq_symm(env, &co_x)?)?, &one_in_two)?;
            let body = Thm::gen(xv, &a1i(&at_x, Formula::mem(tx.clone(), td.clone())));
            debug_assert_eq!(
                *body.concl(),
                crate::ext::body_in(env, co, &td, &two),
                "wlist: the constant body's typing has the wrong shape"
            );
            let out = Thm::mp(&inst_all(&rule, &[td.clone(), two.clone()])?, &body)?;
            debug_assert_eq!(
                *out.concl(),
                Formula::mem(Term::apply(lam_co, vec![td.clone()]), s.fs.of(td.clone(), two.clone())),
                "wlist: const_fun_fs has the wrong shape"
            );
            Thm::gen(dv, &out)
        };

        // ── the parameter, and the terms over it ────────────────────────────
        let av = env.fresh_var();
        let ta = Term::var(av);
        let tags = WList::tags_of(s, ta.clone());
        let u = bnd.universe_of(tags.clone());
        let f0 = PointFun::of(s, point.clone(), zero_s.clone());
        let cf = Term::apply(lam_co, vec![ta.clone()]);
        let fam = cases.of(one.clone(), ta.clone(), two.clone(), f0.clone(), cf.clone());

        let f0_fs = Thm::mp(
            &inst_all(&pf.in_fs, &[point.clone(), zero_s.clone(), two.clone()])?,
            &zero_in_two,
        )?;
        debug_assert_eq!(
            *f0_fs.concl(),
            Formula::mem(f0.clone(), s.fs.of(one.clone(), two.clone())),
            "wlist: the nil fibre function is not in fs(1,2)"
        );
        let cf_fs = inst_all(&const_fun_fs, std::slice::from_ref(&ta))?;

        // ── `app(fam, inl •) = 0` ───────────────────────────────────────────
        let fibre_nil_at = {
            let at = inst_all(
                &cases.beta_left,
                &[one.clone(), ta.clone(), two.clone(), f0.clone(), cf.clone(), point.clone()],
            )?;
            let eq1 = Thm::mp(&Thm::mp(&at, &f0_fs)?, &s.unit_mem)?;
            let eq2 = inst_all(&pf.app, &[point.clone(), zero_s.clone()])?;
            crate::eq_trans(env, &eq1, &eq2)?
        };
        debug_assert_eq!(
            *fibre_nil_at.concl(),
            Formula::eq(wt.fibre(fam.clone(), s.inl(point.clone())), zero_s.clone()),
            "wlist: fibre_nil has the wrong shape"
        );

        // ── `∀h. (h ∈ α → app(fam, inr h) = 1)` ─────────────────────────────
        let hv = env.fresh_var();
        let th = Term::var(hv);
        let h_in_a = Formula::mem(th.clone(), ta.clone());
        let fibre_cons_at = {
            let at = inst_all(
                &cases.beta_right,
                &[one.clone(), ta.clone(), two.clone(), f0.clone(), cf.clone(), th.clone()],
            )?;
            // `⊢ h ∈ α → app(fam, inr h) = app(lam_co(α), h)`
            let eq1 = Thm::mp(&at, &cf_fs)?;
            // `⊢ h ∈ α → app(lam_co(α), h) = co(h)`
            let eq2 = inst_all(&co_beta, &[ta.clone(), th.clone()])?;
            let eq3 = a1i(&inst_all(&co_ax, std::slice::from_ref(&th))?, h_in_a.clone());
            let chain = hyp_eq_trans(env, &eq1, &eq2)?;
            Thm::gen(hv, &hyp_eq_trans(env, &chain, &eq3)?)
        };
        debug_assert_eq!(
            *fibre_cons_at.concl(),
            Formula::forall(
                hv,
                Formula::imp(
                    h_in_a.clone(),
                    Formula::eq(wt.fibre(fam.clone(), s.inr(th.clone())), one.clone())
                )
            ),
            "wlist: fibre_cons has the wrong shape"
        );

        // ── the typing antecedent `T(A,B,A)`, and `closed` ──────────────────
        let typing = typing_at(
            env,
            wt,
            bnd,
            empty_u,
            &tags,
            &fam,
            &fibre_nil_at,
            &fibre_cons_at,
            av,
        )?;
        let closed_at = Thm::mp(
            &inst_all(&bnd.least_universe_closed, &[tags.clone(), tags.clone(), fam.clone()])?,
            &typing,
        )?;
        debug_assert_eq!(
            *closed_at.concl(),
            crate::wtype::closed(env, s, &tags, &fam, &u),
            "wlist: closed has the wrong shape"
        );

        // ── the type symbol ─────────────────────────────────────────────────
        let wty = wt.of(tags.clone(), fam.clone(), u.clone());
        let (lt, lt_ax) = define_abbrev(env, &[av], &wty)?;
        let lt_a = Term::apply(lt, vec![ta.clone()]);
        // `⊢ W(…) = lt(α)`, the direction every transport below runs in.
        let to_lt = eq_symm(env, &inst_all(&lt_ax, std::slice::from_ref(&ta))?)?;

        // ── the `sup` rule at this instance ─────────────────────────────────
        let sup = Thm::mp(
            &inst_all(&bnd.sup_mem, &[tags.clone(), tags.clone(), fam.clone()])?,
            &typing,
        )?;

        // ── `nil ∈ lt(α)` ───────────────────────────────────────────────────
        let nil_t = WList::nil_term(wt);
        let nil = {
            let l_tag = Thm::mp(
                &inst_all(&s.inl_mem, &[one.clone(), ta.clone(), point.clone()])?,
                &s.unit_mem,
            )?;
            // `∅ ∈ fs(app(fam, inl •), W)`, by rewriting the fibre back to `∅`.
            let empty_fun = inst_all(&wt.empty_fun, std::slice::from_ref(&wty))?;
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                zero_s.clone(),
                wt.fibre(fam.clone(), s.inl(point.clone())),
                hole,
                Formula::mem(wt.empty(), s.fs.of(Term::var(hole), wty.clone())),
            );
            let in_fs = Thm::mp(&Thm::mp(&carry, &eq_symm(env, &fibre_nil_at)?)?, &empty_fun)?;
            let at_tag =
                Thm::mp(&inst_all(&sup, std::slice::from_ref(&s.inl(point.clone())))?, &l_tag)?;
            let raw = Thm::mp(&inst_all(&at_tag, std::slice::from_ref(&wt.empty()))?, &in_fs)?;
            // transport `W(…)` to `lt(α)`
            let hole = env.fresh_var();
            let leib =
                Thm::eq_leibniz(wty.clone(), lt_a.clone(), hole, Formula::mem(nil_t.clone(), Term::var(hole)));
            Thm::gen(av, &Thm::mp(&Thm::mp(&leib, &to_lt)?, &raw)?)
        };
        debug_assert_eq!(
            *nil.concl(),
            Formula::forall(av, Formula::mem(nil_t.clone(), lt_a.clone())),
            "wlist: nil has the wrong shape"
        );

        // ── `∀h ∀t. ((h ∈ α ∧ t ∈ lt(α)) → cons h t ∈ lt(α))` ───────────────
        let tv = env.fresh_var();
        let tt = Term::var(tv);
        let cons_t = WList::cons_term(wt, th.clone(), tt.clone());
        let cons = {
            let t_in_w = Formula::mem(tt.clone(), wty.clone());
            let both_raw = Formula::and(h_in_a.clone(), t_in_w.clone());
            let ptf = PointFun::of(s, point.clone(), tt.clone());

            // `⊢ h ∈ α → 1 = app(fam, inr h)`, then Leibniz into the domain.
            let fib_h = inst_all(&fibre_cons_at, std::slice::from_ref(&th))?;
            let back = hyp_eq_symm(env, &fib_h)?;
            let hole = env.fresh_var();
            let leib = Thm::eq_leibniz(
                one.clone(),
                wt.fibre(fam.clone(), s.inr(th.clone())),
                hole,
                Formula::mem(ptf.clone(), s.fs.of(Term::var(hole), wty.clone())),
            );
            let widen = syl(&back, &leib)?; // h ∈ α → (fs(1,W) → fs(B(inr h),W))
            let in_fs_1 = inst_all(&pf.in_fs, &[point.clone(), tt.clone(), wty.clone()])?;
            let p1 = syl(&and_left(h_in_a.clone(), t_in_w.clone()), &widen)?;
            let p2 = syl(&and_right(h_in_a.clone(), t_in_w.clone()), &in_fs_1)?;
            let in_fs = hyp_mp(&p1, &p2)?;

            // `⊢ h ∈ α → ∀f. (f ∈ fs(B(inr h), W) → ⟨inr h, f⟩ ∈ W)`
            let r_tag = inst_all(&s.inr_mem, &[one.clone(), ta.clone(), th.clone()])?;
            let at_tag = syl(&r_tag, &inst_all(&sup, std::slice::from_ref(&s.inr(th.clone())))?)?;
            let at_f = hyp_inst(&at_tag, ptf.clone())?;
            let raw = hyp_mp(&syl(&and_left(h_in_a.clone(), t_in_w.clone()), &at_f)?, &in_fs)?;
            debug_assert_eq!(
                *raw.concl(),
                Formula::imp(both_raw, Formula::mem(cons_t.clone(), wty.clone())),
                "wlist: the raw cons membership has the wrong shape"
            );

            // transport both occurrences of `W(…)` at once
            let hole = env.fresh_var();
            let phi = Formula::imp(
                Formula::and(h_in_a.clone(), Formula::mem(tt.clone(), Term::var(hole))),
                Formula::mem(cons_t.clone(), Term::var(hole)),
            );
            let leib = Thm::eq_leibniz(wty.clone(), lt_a.clone(), hole, phi);
            gen_all(&[av, hv, tv], &Thm::mp(&Thm::mp(&leib, &to_lt)?, &raw)?)
        };
        debug_assert_eq!(
            *cons.concl(),
            Formula::forall(
                av,
                Formula::forall(
                    hv,
                    Formula::forall(
                        tv,
                        Formula::imp(
                            Formula::and(
                                h_in_a.clone(),
                                Formula::mem(tt.clone(), lt_a.clone())
                            ),
                            Formula::mem(cons_t.clone(), lt_a.clone())
                        )
                    )
                )
            ),
            "wlist: cons has the wrong shape"
        );

        // ── non-vacuity ─────────────────────────────────────────────────────
        let nil_ne_cons = nil_ne_cons(wt, hv, tv)?;
        let cons_inj = cons_inj(env, wt)?;
        let distinct3 = distinct3(env, wt, hv, &nil_ne_cons, &cons_inj)?;
        let three_in = three_in(env, wt, av, hv, &nil, &cons)?;

        Some(WList {
            two,
            co,
            lam_co,
            const_fun_fs,
            lt,
            lt_ax,
            fibre_nil: Thm::gen(av, &fibre_nil_at),
            fibre_cons: Thm::gen(av, &fibre_cons_at),
            closed: Thm::gen(av, &closed_at),
            nil_t,
            nil,
            cons,
            nil_ne_cons,
            cons_inj,
            distinct3,
            three_in,
        })
    }
}
