//! **`List`, `List.nil` and `List.cons` as set functions** — the layer between
//! [`crate::wlist`]'s terms and a checker that *applies* them.
//!
//! # Why this exists
//!
//! [`crate::wlist`] gives `lt(α)`, `nil` and `cons h t` as **terms**: a unary
//! symbol and two term-formers. Lean does not have term-formers. It has
//!
//! ```text
//! List     : Type u → Type u
//! List.nil : ∀ {α : Type u}, List α
//! List.cons: ∀ {α : Type u}, α → List α → List α
//! ```
//!
//! and it *applies* all three, so an interpretation that turns `List α` into
//! `app(⟦List⟧, ⟦α⟧)` — which is what the backend does with every application —
//! needs `⟦List⟧` to be a **set**. Same for the two constructors. This is
//! [`crate::wnat`]'s `succ_fun` again, three times over and with one new twist.
//!
//! # `cons` is curried, not a function on a pair
//!
//! `cons` is binary, so its graph could be either a function of the pair
//! `⟨h,t⟩` or a function of `h` returning a function of `t`. **Curried**, for a
//! reason that is not a matter of taste: the checker interprets `f a b` as
//! `app(app(⟦f⟧,⟦a⟧),⟦b⟧)`, one `app` per Lean argument, because that is the
//! only shape available before knowing which constant is being applied. A
//! pair-taking graph would need the interpretation of *application itself* to
//! depend on the head, which it does not. So `⟦List.cons⟧` is a nest of three
//! graphs — one for the implicit `α`, one for the head, one for the tail — and
//! the innermost two carry the outer arguments as parameters, which is why
//! [`crate::funcs::lambda_n`] is needed rather than [`crate::funcs::lambda`].
//!
//! ```text
//! L(S)    := { ⟨α, lt(α)⟩ : α ∈ S }
//! Nil(S)  := { ⟨α, nil⟩   : α ∈ S }
//! C(S)    := { ⟨α, { ⟨h, { ⟨t, cons h t⟩ : t ∈ lt(α) }⟩ : h ∈ α }⟩ : α ∈ S }
//! ```
//!
//! # Interface
//!
//! `S` is the interpretation of the sort `α` ranges over; it stays a parameter,
//! so nothing here knows or cares what `⟦Sort u⟧` is.
//!
//! ```text
//! ⊢ ∀S ∀α. (α ∈ S → app(L(S), α) = lt(α))                    [ListFun::l_beta]
//! ⊢ ∀S ∀α. (α ∈ S → app(Nil(S), α) ∈ app(L(S), α))           [ListFun::nil_rule]
//! ⊢ ∀S ∀α ∀h ∀t. ((α ∈ S ∧ (h ∈ α ∧ t ∈ app(L(S), α)))
//!                    → app(app(app(C(S), α), h), t) ∈ app(L(S), α))  [ListFun::cons_rule]
//! ```
//!
//! Both rules are stated *entirely* in terms of `app(L(S), α)` — never `lt(α)` —
//! because that is the term the checker will have in hand: it is what
//! `⟦List α⟧` interprets to. Callers need none of the derivations.
//!
//! # Where `α ∈ ⟦Sort u⟧` finally does enter, and why it is harmless
//!
//! [`crate::wlist`] derives every membership with `α` free and **no** hypothesis
//! — see its header, which refutes `INDUCTIVES.md`'s prediction on that point.
//! The hypothesis `α ∈ S` reappears here, and for a reason that has nothing to
//! do with inductives: a set-theoretic function has a **set domain**, and
//! `app(f,x)` off the domain is `∅` ([`crate::funcs::app_off_domain`]). So
//! `app(L(S), α) = lt(α)` cannot hold for an `α` outside `S`, whatever `lt` is.
//! Every lambda in the interpretation pays this, not just these three.
//!
//! It is also the hypothesis a caller has: `α` arrives as a bound variable whose
//! binder is `Type u`, so `⟦α⟧ ∈ ⟦Type u⟧` is in force as the binder's own
//! assumption wherever the rules are used.
//!
//! What is **not** derivable, here or anywhere, is `lt(α) ∈ S` — i.e.
//! `⟦List α⟧ ∈ ⟦Sort u⟧`. That is the obstruction already on record for
//! `⟦Bool⟧ ∈ ⟦Sort 1⟧`, it comes from the `Sort` encoding, and it is why
//! `⟦List⟧ ∈ fs(S,S)` is *not* among the exports above.
//!
//! # Non-vacuity
//!
//! Every statement above would hold of an `S` with no members. `tests/wlist.rs`
//! discharges that by instantiating `S := U(α)` — so `α ∈ S` is
//! [`crate::universe::mem_least_universe`], free of charge — and reading off
//! `app(Nil(U(α)), α) ∈ app(L(U(α)), α)` with **no hypothesis left**, together
//! with the same for one `cons`. The three graphs therefore compute at a real
//! argument, rather than being three empty sets.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::wlist::WList;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{a1i, and_left, and_right, define_abbrev, gen_all, hyp_and, hyp_mp, inst_all, syl};

/// The three graphs, and the two rules a checker consumes.
pub struct ListFun {
    /// `L(S) = {⟨α, lt(α)⟩ : α ∈ S}` — the type former as a set.
    pub lam_l: FnSym,
    /// `Nil(S) = {⟨α, nil⟩ : α ∈ S}`.
    pub lam_nil: FnSym,
    /// `C(S)` — the outermost of `cons`'s three graphs.
    pub lam_cons: FnSym,
    /// `⊢ ∀S ∀α. (α ∈ S → app(L(S), α) = lt(α))`.
    pub l_beta: Thm,
    /// `⊢ ∀S ∀α. (α ∈ S → app(Nil(S), α) ∈ app(L(S), α))`.
    pub nil_rule: Thm,
    /// `⊢ ∀S ∀α ∀h ∀t. ((α ∈ S ∧ (h ∈ α ∧ t ∈ app(L(S),α)))
    ///                     → app(app(app(C(S),α),h),t) ∈ app(L(S),α))`.
    pub cons_rule: Thm,
    /// `⊢ ∀S ∀α. (α ∈ S → app(Nil(S),α) = ⟨inl •,∅⟩)`.
    ///
    /// The *equation* behind [`ListFun::nil_rule`]. The membership is what a
    /// typing obligation wants; ι wants the equation, because the recursor's
    /// computation rule is stated at the W-type element and the checker's major
    /// premise is the applied graph.
    pub nil_beta: Thm,
    /// `⊢ ∀S ∀α ∀h ∀t. ((α ∈ S ∧ (h ∈ α ∧ t ∈ app(L(S),α)))
    ///                     → app(app(app(C(S),α),h),t) = ⟨inr h,{⟨•,t⟩}⟩)`.
    pub cons_beta: Thm,
}

/// From `⊢ H → x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`, for a formula context
/// given as a closure over the hole.
fn rewrite_under<F: Fn(Term) -> Formula>(
    env: &mut Env,
    h_eq: &Thm,
    ctx: F,
    h_prev: &Thm,
) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    hyp_mp(&syl(h_eq, &leib)?, h_prev)
}

impl ListFun {
    /// The term `L(S)`.
    pub fn l_of(&self, s: Term) -> Term { Term::apply(self.lam_l, vec![s]) }
    /// The term `Nil(S)`.
    pub fn nil_of(&self, s: Term) -> Term { Term::apply(self.lam_nil, vec![s]) }
    /// The term `C(S)`.
    pub fn cons_of(&self, s: Term) -> Term { Term::apply(self.lam_cons, vec![s]) }

    /// Build the three graphs and both rules, over a caller-supplied
    /// [`WList`] — so that `lt`, `nil` and `cons` are the *same* symbols the
    /// membership theorems are stated about.
    pub fn over(env: &mut Env, wt: &Wtype, wl: &WList) -> Option<ListFun> {
        let ap = &wt.sums.ap;

        // ── the three bodies, and their graphs ──────────────────────────────
        let (lam_l, lam_l_ax) = crate::funcs::lambda(env, ap, wl.lt)?;
        let l_beta = crate::funcs::beta_conditional(env, ap, wl.lt, lam_l, &lam_l_ax)?;

        let xv = env.fresh_var();
        let (nb, nb_ax) = define_abbrev(env, &[xv], &wl.nil_t)?;
        let (lam_nil, lam_nil_ax) = crate::funcs::lambda(env, ap, nb)?;
        let nil_beta = crate::funcs::beta_conditional(env, ap, nb, lam_nil, &lam_nil_ax)?;

        // innermost: `λt : D. cons h t`, with `h` a parameter
        let (hv, tv) = (env.fresh_var(), env.fresh_var());
        let (th0, tt0) = (Term::var(hv), Term::var(tv));
        let (ci, ci_ax) =
            define_abbrev(env, &[hv, tv], &WList::cons_term(wt, th0.clone(), tt0.clone()))?;
        let (lam_ci, lam_ci_ax) = crate::funcs::lambda_n(env, ap, ci)?;
        let ci_beta = crate::funcs::beta_conditional_n(env, ap, ci, lam_ci, &lam_ci_ax)?;

        // middle: `λh : D. lam_ci(h, lt(α))`, with `α` a parameter
        let (a0v, h0v) = (env.fresh_var(), env.fresh_var());
        let (ta0, th1) = (Term::var(a0v), Term::var(h0v));
        let (cm, cm_ax) = define_abbrev(
            env,
            &[a0v, h0v],
            &Term::apply(lam_ci, vec![th1.clone(), wl.ty_of(ta0.clone())]),
        )?;
        let (lam_cm, lam_cm_ax) = crate::funcs::lambda_n(env, ap, cm)?;
        let cm_beta = crate::funcs::beta_conditional_n(env, ap, cm, lam_cm, &lam_cm_ax)?;

        // outermost: `λα : S. lam_cm(α, α)`
        let a1v = env.fresh_var();
        let ta1 = Term::var(a1v);
        let (cq, cq_ax) =
            define_abbrev(env, &[a1v], &Term::apply(lam_cm, vec![ta1.clone(), ta1.clone()]))?;
        let (lam_cons, lam_cons_ax) = crate::funcs::lambda(env, ap, cq)?;
        let cq_beta = crate::funcs::beta_conditional(env, ap, cq, lam_cons, &lam_cons_ax)?;

        // ── the two rules ───────────────────────────────────────────────────
        let (sv, av, hv2, tv2) =
            (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (ts, ta, th, tt) = (Term::var(sv), Term::var(av), Term::var(hv2), Term::var(tv2));
        let l_s = Term::apply(lam_l, vec![ts.clone()]);
        let lt_a = wl.ty_of(ta.clone());
        let app_l = ap.apply(l_s.clone(), ta.clone());
        let a_in_s = Formula::mem(ta.clone(), ts.clone());

        // `⊢ α ∈ S → app(L(S),α) = lt(α)`, the equation both rules turn on.
        let e_l = inst_all(&l_beta, &[ts.clone(), ta.clone()])?;

        // `⊢ α ∈ S → app(Nil(S),α) = nil`, the equation the ι rule consumes.
        let nil_eq = {
            let h = a_in_s.clone();
            let e_n = inst_all(&nil_beta, &[ts.clone(), ta.clone()])?;
            let e_nb = a1i(&inst_all(&nb_ax, std::slice::from_ref(&ta))?, h.clone());
            hyp_eq_trans(env, &e_n, &e_nb)?
        };
        debug_assert_eq!(
            *nil_eq.concl(),
            Formula::imp(
                a_in_s.clone(),
                Formula::eq(
                    ap.apply(Term::apply(lam_nil, vec![ts.clone()]), ta.clone()),
                    wl.nil_t.clone()
                )
            ),
            "wlist_fun: nil_beta has the wrong shape"
        );

        let nil_rule = {
            let h = a_in_s.clone();
            // `⊢ H → nil ∈ lt(α)`
            let m = a1i(&inst_all(&wl.nil, std::slice::from_ref(&ta))?, h.clone());
            // subject: `nil` ⇒ `app(Nil(S),α)`
            let e_full = nil_eq.clone();
            let lt_a2 = lt_a.clone();
            let back = hyp_eq_symm(env, &e_full)?;
            let step1 =
                rewrite_under(env, &back, move |w| Formula::mem(w, lt_a2.clone()), &m)?;
            // target: `lt(α)` ⇒ `app(L(S),α)`
            let subj = ap.apply(Term::apply(lam_nil, vec![ts.clone()]), ta.clone());
            let subj2 = subj.clone();
            let back_l = hyp_eq_symm(env, &e_l)?;
            rewrite_under(env, &back_l, move |w| Formula::mem(subj2.clone(), w), &step1)?
        };
        debug_assert_eq!(
            *nil_rule.concl(),
            Formula::imp(
                a_in_s.clone(),
                Formula::mem(
                    ap.apply(Term::apply(lam_nil, vec![ts.clone()]), ta.clone()),
                    app_l.clone()
                )
            ),
            "wlist_fun: nil_rule has the wrong shape"
        );

        let (cons_rule, cons_eq) = {
            let inner = Formula::and(
                Formula::mem(th.clone(), ta.clone()),
                Formula::mem(tt.clone(), app_l.clone()),
            );
            let h = Formula::and(a_in_s.clone(), inner.clone());
            let h_a = and_left(a_in_s.clone(), inner.clone());
            let h_rest = and_right(a_in_s.clone(), inner.clone());
            let h_h = syl(
                &h_rest,
                &and_left(
                    Formula::mem(th.clone(), ta.clone()),
                    Formula::mem(tt.clone(), app_l.clone()),
                ),
            )?;
            let h_t = syl(
                &h_rest,
                &and_right(
                    Formula::mem(th.clone(), ta.clone()),
                    Formula::mem(tt.clone(), app_l.clone()),
                ),
            )?;

            // `⊢ H → app(L(S),α) = lt(α)`, and hence `⊢ H → t ∈ lt(α)`.
            let e_l_h = syl(&h_a, &e_l)?;
            let tt2 = tt.clone();
            let h_t_lt = rewrite_under(env, &e_l_h, move |w| Formula::mem(tt2.clone(), w), &h_t)?;

            // `⊢ H → cons h t ∈ lt(α)`, from `wlist`'s membership rule.
            let cons_mem = {
                let rule = inst_all(&wl.cons, &[ta.clone(), th.clone(), tt.clone()])?;
                hyp_mp(&a1i(&rule, h.clone()), &hyp_and(&h_h, &h_t_lt)?)?
            };

            // ── the spine computes ──────────────────────────────────────────
            // `⊢ H → app(C(S),α) = lam_cm(α,α)`
            let e_c = syl(&h_a, &inst_all(&cq_beta, &[ts.clone(), ta.clone()])?)?;
            let e_cq = a1i(&inst_all(&cq_ax, std::slice::from_ref(&ta))?, h.clone());
            let e_1 = hyp_eq_trans(env, &e_c, &e_cq)?;

            // `⊢ H → app(app(C(S),α),h) = cm(α,h) = lam_ci(h, lt(α))`
            let th_c = th.clone();
            let e_1b = hyp_congr(env, &e_1, move |w| ap.apply(w, th_c.clone()))?;
            let e_m = syl(&h_h, &inst_all(&cm_beta, &[ta.clone(), ta.clone(), th.clone()])?)?;
            let e_cm = a1i(&inst_all(&cm_ax, &[ta.clone(), th.clone()])?, h.clone());
            let e_1c = hyp_eq_trans(env, &e_1b, &e_m)?;
            let e_2 = hyp_eq_trans(env, &e_1c, &e_cm)?;

            // `⊢ H → app(app(app(C(S),α),h),t) = ci(h,t) = cons h t`
            let tt_c = tt.clone();
            let e_2b = hyp_congr(env, &e_2, move |w| ap.apply(w, tt_c.clone()))?;
            let e_i = hyp_mp(
                &a1i(&inst_all(&ci_beta, &[th.clone(), lt_a.clone(), tt.clone()])?, h.clone()),
                &h_t_lt,
            )?;
            let e_ci = a1i(&inst_all(&ci_ax, &[th.clone(), tt.clone()])?, h.clone());
            let e_2c = hyp_eq_trans(env, &e_2b, &e_i)?;
            let e_3 = hyp_eq_trans(env, &e_2c, &e_ci)?;

            // subject, then target
            let lt_a3 = lt_a.clone();
            let back_3 = hyp_eq_symm(env, &e_3)?;
            let step1 =
                rewrite_under(env, &back_3, move |w| Formula::mem(w, lt_a3.clone()), &cons_mem)?;
            let spine = ap.apply(
                ap.apply(
                    ap.apply(Term::apply(lam_cons, vec![ts.clone()]), ta.clone()),
                    th.clone(),
                ),
                tt.clone(),
            );
            let spine2 = spine.clone();
            let back_l = hyp_eq_symm(env, &e_l_h)?;
            let rule =
                rewrite_under(env, &back_l, move |w| Formula::mem(spine2.clone(), w), &step1)?;
            (rule, e_3)
        };
        debug_assert_eq!(
            *cons_eq.concl(),
            Formula::imp(
                Formula::and(
                    a_in_s.clone(),
                    Formula::and(
                        Formula::mem(th.clone(), ta.clone()),
                        Formula::mem(tt.clone(), app_l.clone())
                    )
                ),
                Formula::eq(
                    ap.apply(
                        ap.apply(
                            ap.apply(Term::apply(lam_cons, vec![ts.clone()]), ta.clone()),
                            th.clone()
                        ),
                        tt.clone()
                    ),
                    WList::cons_term(wt, th.clone(), tt.clone())
                )
            ),
            "wlist_fun: cons_beta has the wrong shape"
        );
        debug_assert_eq!(
            *cons_rule.concl(),
            Formula::imp(
                Formula::and(
                    a_in_s.clone(),
                    Formula::and(
                        Formula::mem(th.clone(), ta.clone()),
                        Formula::mem(tt.clone(), app_l.clone())
                    )
                ),
                Formula::mem(
                    ap.apply(
                        ap.apply(
                            ap.apply(Term::apply(lam_cons, vec![ts.clone()]), ta.clone()),
                            th.clone()
                        ),
                        tt.clone()
                    ),
                    app_l.clone()
                )
            ),
            "wlist_fun: cons_rule has the wrong shape"
        );

        Some(ListFun {
            lam_l,
            lam_nil,
            lam_cons,
            l_beta,
            nil_rule: gen_all(&[sv, av], &nil_rule),
            cons_rule: gen_all(&[sv, av, hv2, tv2], &cons_rule),
            nil_beta: gen_all(&[sv, av], &nil_eq),
            cons_beta: gen_all(&[sv, av, hv2, tv2], &cons_eq),
        })
    }
}

/// The application `app(f,x)`, spelled out for callers that hold only an
/// [`Apply`].
pub fn app_of(ap: &Apply, f: Term, x: Term) -> Term { ap.apply(f, x) }
