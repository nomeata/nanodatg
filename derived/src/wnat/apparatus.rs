//! `N` as a W-type: the symbol, and every theorem about it.
//!
//! # Interface
//!
//! [`Nat::over`] builds the symbol and derives every theorem, over a
//! caller-supplied [`crate::wtype::Wtype`]. The fields are the theorems;
//! `succ_of` and [`Nat`]'s term builders build the terms. Callers need none
//! of the derivations in the sibling files.
//!
//! # Why the bound is `U(A)` and where the work actually is
//!
//! `N` is `W(1+1, B, U(A))` with `B` the family sending the `zero` tag to `0`
//! and the `succ` tag to `1`. The bound hypothesis is discharged from three
//! memberships, all cheap:
//!
//! * `A ∈ U(A)` — [`crate::universe::mem_least_universe`];
//! * `0 = ∅ ∈ U(A)` — [`crate::enums::empty_in_least_universe`], the subset
//!   clause `C₂` at `∅ ⊆ A`;
//! * `1 = {∅} ∈ U(A)` — [`crate::bound::Bound::least_pairing`] at `a = b = ∅`,
//!   since `{∅,∅}` *is* the term `1`.
//!
//! So the real work is the **case analysis**: computing `app(B,a)` for
//! `a ∈ 1 + 1`, which is [`crate::sums::Sums::sum_cases`] plus
//! [`crate::sums::Sums::unit_eta`] plus the two `rec₊` computation rules. No
//! ω-tower, no recursion theorem, no new axiom.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::bound::Bound;
use crate::point_fun::PointFun;
use crate::sums::Cases;
use crate::wtype::Wtype;
use crate::{inst_all, syl, upair_members};

use super::typing::typing_at;
use super::distinct::{succ_inj, zero_ne_succ};

/// The whole development, at closed terms.
pub struct Nat {
    /// `1 + 1`, the tag set.
    pub tags: Term,
    /// `{0,1}`, the codomain of the fibre family.
    pub two: Term,
    /// `rec₊(λ_. 0, λ_. 1)` — the fibre family, as a set-function on `1 + 1`.
    pub fam: Term,
    /// `N = W(1+1, B, U(1+1))`.
    pub ty: Term,
    /// `⟨inl •, ∅⟩`.
    pub zero_t: Term,
    /// `⊢ app(B, inl •) = 0`.
    pub fibre_zero: Thm,
    /// `⊢ app(B, inr •) = 1`.
    pub fibre_succ: Thm,
    /// `⊢ closed(1+1, B, U(1+1))` — the W-type's bound hypothesis, discharged.
    pub closed: Thm,
    /// `⊢ ⟨inl •, ∅⟩ ∈ N`, unconditionally.
    pub zero: Thm,
    /// `⊢ ∀n. (n ∈ N → ⟨inr •, {⟨•,n⟩}⟩ ∈ N)`.
    pub succ: Thm,
    /// `⊢ ∀n. ¬(⟨inl •,∅⟩ = ⟨inr •,{⟨•,n⟩}⟩)`.
    pub zero_ne_succ: Thm,
    /// `⊢ ∀m ∀n. (succ m = succ n → m = n)`.
    pub succ_inj: Thm,
    /// The unary symbol `sc`, with `sc(x) = ⟨inr •, {⟨•,x⟩}⟩`.
    pub sc: FnSym,
    /// `⊢ ∀x. sc(x) = ⟨inr •, {⟨•,x⟩}⟩`.
    pub sc_ax: Thm,
    /// `succ_fun = { ⟨x, sc(x)⟩ : x ∈ N }` — the successor as a *set*.
    pub succ_fun: Term,
    /// `⊢ succ_fun ∈ fs(N, N)`.
    pub succ_in_funspace: Thm,
    /// `⊢ ∀n. (n ∈ N → app(succ_fun, n) = sc(n))`.
    pub succ_beta: Thm,
}

/// The term `⟨inr •, {⟨•,n⟩}⟩`.
pub(super) fn succ_of(wt: &Wtype, n: Term) -> Term {
    let s = &wt.sums;
    wt.sup(s.inr(s.point()), PointFun::of(s, s.point(), n))
}

impl Nat {
    /// The term `⟨inr •, {⟨•,n⟩}⟩`, for callers building `succ` applications.
    pub fn succ_term(wt: &Wtype, n: Term) -> Term { succ_of(wt, n) }

    /// Build the whole development.
    ///
    /// `cases` must be [`Cases`] over the *same* `Sums` as `wt`, and `pf` the
    /// [`PointFun`] over it — building a second copy of either would mint new
    /// symbols whose theorems do not compose with these.
    pub fn over(
        env: &mut Env,
        wt: &Wtype,
        bnd: &Bound,
        cases: &Cases,
        pf: &PointFun,
        empty_u: &Thm,
    ) -> Option<Nat> {
        let s = &wt.sums;
        let ap = &s.ap;
        let (zero_s, one, point) = (s.zero(), s.unit(), s.point());
        let tags = s.sum_of(one.clone(), one.clone());
        let two = Term::apply(ap.sets.up, vec![zero_s.clone(), one.clone()]);
        let u = bnd.universe_of(tags.clone());

        // ── the two constant functions on `1`, as one-point graphs ──────────
        let (zero_in_two, one_in_two) = upair_members(&ap.sets.up_ax, &zero_s, &one)?;
        let f0 = PointFun::of(s, point.clone(), zero_s.clone());
        let f1 = PointFun::of(s, point.clone(), one.clone());
        let f0_fs = Thm::mp(
            &inst_all(&pf.in_fs, &[point.clone(), zero_s.clone(), two.clone()])?,
            &zero_in_two,
        )?;
        let f1_fs = Thm::mp(
            &inst_all(&pf.in_fs, &[point.clone(), one.clone(), two.clone()])?,
            &one_in_two,
        )?;
        debug_assert_eq!(
            *f0_fs.concl(),
            Formula::mem(f0.clone(), s.fs.of(one.clone(), two.clone())),
            "wnat: the zero fibre function is not in fs(1,2)"
        );

        let fam = cases.of(one.clone(), one.clone(), two.clone(), f0.clone(), f1.clone());

        // ── `app(B, inl •) = 0` and `app(B, inr •) = 1` ─────────────────────
        let fibre = |env: &mut Env, left: bool| -> Option<Thm> {
            let (rule, val, fs_thm) = if left {
                (&cases.beta_left, zero_s.clone(), &f0_fs)
            } else {
                (&cases.beta_right, one.clone(), &f1_fs)
            };
            let at = inst_all(
                rule,
                &[
                    one.clone(),
                    one.clone(),
                    two.clone(),
                    f0.clone(),
                    f1.clone(),
                    point.clone(),
                ],
            )?;
            // `f ∈ fs(1,2)` and `• ∈ 1`, both proved.
            let eq1 = Thm::mp(&Thm::mp(&at, fs_thm)?, &s.unit_mem)?;
            let eq2 = inst_all(&pf.app, &[point.clone(), val.clone()])?;
            crate::eq_trans(env, &eq1, &eq2)
        };
        let fibre_zero = fibre(env, true)?;
        let fibre_succ = fibre(env, false)?;
        debug_assert_eq!(
            *fibre_zero.concl(),
            Formula::eq(wt.fibre(fam.clone(), s.inl(point.clone())), zero_s.clone()),
            "wnat: fibre_zero has the wrong shape"
        );
        debug_assert_eq!(
            *fibre_succ.concl(),
            Formula::eq(wt.fibre(fam.clone(), s.inr(point.clone())), one.clone()),
            "wnat: fibre_succ has the wrong shape"
        );

        // ── the typing antecedent `T(A,B,A)` ────────────────────────────────
        let typing = typing_at(env, wt, bnd, empty_u, &tags, &fam, &fibre_zero, &fibre_succ)?;

        // ── `closed(A,B,U(A))` ──────────────────────────────────────────────
        let closed = Thm::mp(
            &inst_all(
                &bnd.least_universe_closed,
                &[tags.clone(), tags.clone(), fam.clone()],
            )?,
            &typing,
        )?;
        debug_assert_eq!(
            *closed.concl(),
            crate::wtype::closed(env, s, &tags, &fam, &u),
            "wnat: closed has the wrong shape"
        );

        let ty = wt.of(tags.clone(), fam.clone(), u.clone());

        // ── the `sup` rule, at this instance ────────────────────────────────
        // `⊢ ∀a. (a ∈ A → ∀f. (f ∈ fs(app(B,a), N) → ⟨a,f⟩ ∈ N))`
        let sup = Thm::mp(
            &inst_all(&bnd.sup_mem, &[tags.clone(), tags.clone(), fam.clone()])?,
            &typing,
        )?;

        // ── `zero ∈ N` ──────────────────────────────────────────────────────
        let l_tag = Thm::mp(
            &inst_all(&s.inl_mem, &[one.clone(), one.clone(), point.clone()])?,
            &s.unit_mem,
        )?;
        let r_tag = Thm::mp(
            &inst_all(&s.inr_mem, &[one.clone(), one.clone(), point.clone()])?,
            &s.unit_mem,
        )?;
        let zero_t = wt.sup(s.inl(point.clone()), wt.empty());
        let zero = {
            // `∅ ∈ fs(app(B, inl •), N)`, by rewriting the fibre to `∅`.
            let empty_fun = inst_all(&wt.empty_fun, std::slice::from_ref(&ty))?;
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                zero_s.clone(),
                wt.fibre(fam.clone(), s.inl(point.clone())),
                hole,
                Formula::mem(wt.empty(), s.fs.of(Term::var(hole), ty.clone())),
            );
            let in_fs =
                Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, &fibre_zero)?)?, &empty_fun)?;
            let at_tag = Thm::mp(&inst_all(&sup, std::slice::from_ref(&s.inl(point.clone())))?, &l_tag)?;
            Thm::mp(&inst_all(&at_tag, std::slice::from_ref(&wt.empty()))?, &in_fs)?
        };
        debug_assert_eq!(
            *zero.concl(),
            Formula::mem(zero_t.clone(), ty.clone()),
            "wnat: zero has the wrong shape"
        );

        // ── `∀n. (n ∈ N → succ n ∈ N)` ──────────────────────────────────────
        let nv = env.fresh_var();
        let tn = Term::var(nv);
        let h_n = Formula::mem(tn.clone(), ty.clone());
        let succ = {
            // `n ∈ N → {⟨•,n⟩} ∈ fs(1, N)`, then rewrite `1` to `app(B, inr •)`.
            let in_fs_1 = inst_all(&pf.in_fs, &[point.clone(), tn.clone(), ty.clone()])?;
            let hole = env.fresh_var();
            let carry = Thm::eq_leibniz(
                one.clone(),
                wt.fibre(fam.clone(), s.inr(point.clone())),
                hole,
                Formula::mem(
                    PointFun::of(s, point.clone(), tn.clone()),
                    s.fs.of(Term::var(hole), ty.clone()),
                ),
            );
            let back = Thm::mp(&carry, &crate::eq_symm(env, &fibre_succ)?)?;
            let in_fs = syl(&in_fs_1, &back)?;
            let at_tag = Thm::mp(&inst_all(&sup, std::slice::from_ref(&s.inr(point.clone())))?, &r_tag)?;
            let at_f = inst_all(
                &at_tag,
                std::slice::from_ref(&PointFun::of(s, point.clone(), tn.clone())),
            )?;
            Thm::gen(nv, &syl(&in_fs, &at_f)?)
        };
        debug_assert_eq!(
            *succ.concl(),
            Formula::forall(
                nv,
                Formula::imp(h_n.clone(), Formula::mem(succ_of(wt, tn.clone()), ty.clone()))
            ),
            "wnat: succ has the wrong shape"
        );

        // ── the two distinctness theorems ───────────────────────────────────
        let zero_ne_succ = zero_ne_succ(wt, nv)?;
        let succ_inj = succ_inj(env, wt)?;

        // ── the successor as a function ─────────────────────────────────────
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let (sc, sc_ax) = crate::define_abbrev(env, &[xv], &succ_of(wt, tx.clone()))?;
        let (lam, lam_ax) = crate::funcs::lambda(env, ap, sc)?;
        let succ_fun = Term::apply(lam, vec![ty.clone()]);

        // `body_in(N,N) = ∀x. (x ∈ N → sc(x) ∈ N)`, from `succ` along `sc_ax`.
        let body_in = {
            let at = inst_all(&succ, std::slice::from_ref(&tx))?;
            let sc_x = inst_all(&sc_ax, std::slice::from_ref(&tx))?;
            let hole = env.fresh_var();
            // `sc_ax` reads `sc(x) = ⟨…⟩`, and the membership is known of the
            // right-hand side, so the Leibniz step runs *backwards*.
            let carry = Thm::eq_leibniz(
                succ_of(wt, tx.clone()),
                Term::apply(sc, vec![tx.clone()]),
                hole,
                Formula::mem(Term::var(hole), ty.clone()),
            );
            let back = Thm::mp(&carry, &crate::eq_symm(env, &sc_x)?)?;
            Thm::gen(xv, &syl(&at, &back)?)
        };
        debug_assert_eq!(
            *body_in.concl(),
            crate::ext::body_in(env, sc, &ty, &ty),
            "wnat: body_in has the wrong shape"
        );
        let in_fs_rule =
            crate::ext::lam_in_funspace(env, ap, &s.prod, &s.fs, sc, lam, &lam_ax)?;
        let succ_in_funspace = Thm::mp(
            &inst_all(&in_fs_rule, &[ty.clone(), ty.clone()])?,
            &body_in,
        )?;
        debug_assert_eq!(
            *succ_in_funspace.concl(),
            Formula::mem(succ_fun.clone(), s.fs.of(ty.clone(), ty.clone())),
            "wnat: succ_in_funspace has the wrong shape"
        );

        let beta = crate::funcs::beta_conditional(env, ap, sc, lam, &lam_ax)?;
        let succ_beta = Thm::gen(nv, &inst_all(&beta, &[ty.clone(), tn.clone()])?);

        Some(Nat {
            tags,
            two,
            fam,
            ty,
            zero_t,
            fibre_zero,
            fibre_succ,
            closed,
            zero,
            succ,
            zero_ne_succ,
            succ_inj,
            sc,
            sc_ax,
            succ_fun,
            succ_in_funspace,
            succ_beta,
        })
    }
}
