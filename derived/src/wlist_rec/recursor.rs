//! `List.rec`, packaged.
//!
//! # Interface
//!
//! [`ListRec::over`] builds every symbol and derives every theorem over a
//! caller-supplied [`crate::wlist::WList`]. The fields are the theorems —
//! `app_nil`, `app_cons`, `step_typed`, `iota_nil`, `iota_cons` — and
//! [`ListRec::of`] builds the recursor term.
//!
//! [`premise_witness`] discharges `HYP` at a concrete instance, which is what
//! `tests/wlist_rec.rs` uses to show the theorems are not about an unsatisfiable
//! antecedent.
//!
//! # Why it is a struct
//!
//! Every theorem here is about *the* `List α`, *the* step symbol and *the*
//! recursor of one definitional extension. Building any of them twice would mint
//! a second `upair`, and then none of the theorems would compose.

use kernel::{Env, Formula, Term, Thm};
use crate::bound::Bound;
use crate::point_fun::PointFun;
use crate::proj::Proj;
use crate::sums::Cases;
use crate::wlist::WList;
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, gen_all, hyp_and, inst_all, syl};

use super::step::StepSyms;
use super::values::step_single_valued;
use super::computes::step_apps;
use super::typed::{premise, step_typed_at};
use super::iota::{iota_cons_at, iota_nil_at};

/// **The hypothesis both ι rules carry is satisfiable**, at `α := 1`, `T := 1`.
///
/// ```text
/// ⊢ • ∈ 1  ∧  {⟨•, const(lt(1))⟩} ∈ fs(1, fs(lt(1), fs(1,1)))
/// ```
///
/// A theorem whose antecedent no four sets satisfy proves nothing. `α := 1` is
/// chosen rather than `α := 0` deliberately: with an empty parameter the cons
/// rule's own extra hypothesis `h ∈ α` would be unsatisfiable and that rule would
/// still be vacuous. At `α := 1` the head `•` is available.
///
/// Returns the four terms alongside the theorem so a caller can instantiate the
/// ι rules at them.
pub fn premise_witness(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    pf: &PointFun,
) -> Option<(Term, Term, Term, Term, Thm)> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point) = (s.unit(), s.point());
    let (alpha, t) = (one.clone(), one.clone());
    let lt = wl.ty_of(alpha.clone());

    // `{⟨•,•⟩} ∈ fs(1,1)`.
    let id1 = PointFun::of(s, point.clone(), point.clone());
    let id1_fs = Thm::mp(
        &inst_all(&pf.in_fs, &[point.clone(), point.clone(), one.clone()])?,
        &s.unit_mem,
    )?;
    let fs11 = s.fs.of(one.clone(), one.clone());
    if *id1_fs.concl() != Formula::mem(id1.clone(), fs11.clone()) {
        return None
    }

    // The constant function `lt(1) → fs(1,1)`.
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let (c, c_ax) = crate::define_abbrev(env, &[xv], &id1)?;
    let (lam, lam_ax) = crate::funcs::lambda(env, ap, c)?;
    let g = Term::apply(lam, vec![lt.clone()]);

    let hole = env.fresh_var();
    let at_x = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                id1.clone(),
                Term::apply(c, vec![tx.clone()]),
                hole,
                Formula::mem(Term::var(hole), fs11.clone()),
            ),
            &crate::eq_symm(env, &inst_all(&c_ax, std::slice::from_ref(&tx))?)?,
        )?,
        &id1_fs,
    )?;
    let body_in = Thm::gen(xv, &a1i(&at_x, Formula::mem(tx.clone(), lt.clone())));
    if *body_in.concl() != crate::ext::body_in(env, c, &lt, &fs11) {
        return None
    }
    let rule = crate::ext::lam_in_funspace(env, ap, &s.prod, &s.fs, c, lam, &lam_ax)?;
    let g_fs = Thm::mp(&inst_all(&rule, &[lt.clone(), fs11.clone()])?, &body_in)?;

    // `s := {⟨•, g⟩} ∈ fs(1, fs(lt(1), fs(1,1)))`, the domain being a singleton.
    let inner = s.fs.of(lt.clone(), fs11);
    let su = PointFun::of(s, point.clone(), g.clone());
    let su_fs = Thm::mp(
        &inst_all(&pf.in_fs, &[point.clone(), g.clone(), inner.clone()])?,
        &g_fs,
    )?;

    let out = and_intro(&s.unit_mem, &su_fs);
    if *out.concl() != premise(s, wl, &alpha, &point, &su, &t) {
        return None
    }
    Some((alpha, point, su, t, out))
}

/// The whole development, at fresh universally quantified variables.
pub struct ListRec {
    /// The Replacement symbol the step is built from.
    pub syms: StepSyms,
    /// `⊢ ∀α ∀z ∀s ∀T. app(e(α,z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z`.
    pub app_nil: Thm,
    /// `⊢ ∀α ∀z ∀s ∀T ∀h ∀f ∀r. ((h ∈ α ∧ (f ∈ FW(α) ∧ r ∈ FT(T))) →
    ///        app(e, ⟨inr h,⟨f,r⟩⟩) = app(app(app(s,h),app(f,•)),app(r,•)))`.
    pub app_cons: Thm,
    /// `⊢ ∀α ∀z ∀s ∀T. sv(e(α,z,s,T))`.
    pub sv: Thm,
    /// `⊢ ∀α ∀z ∀s ∀T. (HYP → step_typed(1+α, fam(α), U(1+α), T, e))`.
    pub step_typed: Thm,
    /// `⊢ ∀α ∀z ∀s ∀T. (HYP → app(lrec(α,z,s,T), ⟨inl •,∅⟩) = z)`.
    pub iota_nil: Thm,
    /// `⊢ ∀α ∀z ∀s ∀T ∀h ∀t. ((HYP ∧ (h ∈ α ∧ t ∈ lt(α))) →
    ///        app(lrec, ⟨inr h,{⟨•,t⟩}⟩) = app(app(app(s,h),t), app(lrec, t)))`.
    pub iota_cons: Thm,
}

impl ListRec {
    /// The recursor term `lrec(α,z,s,T) = wrec(1+α, fam(α), U(1+α), T, e(α,z,s,T))`.
    #[allow(clippy::too_many_arguments)]
    pub fn of(
        &self,
        wt: &Wtype,
        bnd: &Bound,
        wl: &WList,
        cases_s: &Cases,
        r: &Recursor,
        alpha: &Term,
        z: &Term,
        su: &Term,
        t: &Term,
    ) -> Term {
        let s = &wt.sums;
        let tags = WList::tags_of(s, alpha.clone());
        let fam = wl.fam_of(s, cases_s, alpha.clone());
        let u = bnd.universe_of(tags.clone());
        r.of(&tags, &fam, &u, t, &self.syms.step_of(wt, alpha, z, su, t))
    }

    /// Build the step and derive both ι rules.
    ///
    /// `iota` is [`crate::wrec_total::iota`] and `funspace`
    /// [`crate::wrec_total::wrec_funspace`], both over the *same* [`Recursor`] as
    /// `r`; `pf` is the [`crate::point_fun::PointFun`] and `cases_s` the
    /// [`Cases`] that `wl` was built over. None of them is rebuilt here, because
    /// a second copy would mint new symbols and none of the theorems would
    /// compose.
    #[allow(clippy::too_many_arguments)]
    pub fn over(
        env: &mut Env,
        wt: &Wtype,
        bnd: &Bound,
        wl: &WList,
        cases_s: &Cases,
        rc: &Recursor,
        pf: &PointFun,
        pj: &Proj,
        iota: &Thm,
        funspace: &Thm,
    ) -> Option<ListRec> {
        let syms = StepSyms::new(env, wt, wl, pj)?;
        let (av, zv, suv, tv) =
            (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (hv0, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (alpha, z, su, t) = (Term::var(av), Term::var(zv), Term::var(suv), Term::var(tv));
        let (h0, f, r) = (Term::var(hv0), Term::var(fv), Term::var(rv));

        let sv = step_single_valued(env, wt, wl, pj, &syms, &alpha, &z, &su, &t)?;
        let (app_nil, app_cons) =
            step_apps(env, wt, wl, pj, &syms, &sv, &alpha, &z, &su, &t, &h0, &f, &r)?;
        let app_cons = gen_all(&[hv0, fv, rv], &app_cons);
        let st = step_typed_at(
            env, wt, bnd, wl, cases_s, &syms, &app_nil, &app_cons, &alpha, &z, &su, &t,
        )?;

        // ── The ι rule, with both of its hypotheses discharged ──────────────
        let s = &wt.sums;
        let tags = WList::tags_of(s, alpha.clone());
        let fam = wl.fam_of(s, cases_s, alpha.clone());
        let u = bnd.universe_of(tags.clone());
        let step = syms.step_of(wt, &alpha, &z, &su, &t);
        let lrec = rc.of(&tags, &fam, &u, &t, &step);
        let hyp = premise(s, wl, &alpha, &z, &su, &t);
        let args = [tags, fam, u, t.clone(), step.clone()];
        let closed = inst_all(&wl.closed, std::slice::from_ref(&alpha))?;
        let both = hyp_and(&a1i(&closed, hyp.clone()), &st)?;
        let dis = syl(&both, &inst_all(iota, &args)?)?;
        let fs_thm = syl(&both, &inst_all(funspace, &args)?)?;

        let inl = iota_nil_at(
            env, wt, wl, cases_s, rc, &dis, &app_nil, &lrec, &step, &alpha, &z,
        )?;
        let (hv, lv) = (env.fresh_var(), env.fresh_var());
        let ic = iota_cons_at(
            env, wt, wl, cases_s, rc, pf, &dis, &fs_thm, &app_cons, &lrec, &step, &alpha, &su,
            &t, hv, lv,
        )?;

        Some(ListRec {
            syms,
            app_nil: gen_all(&[av, zv, suv, tv], &app_nil),
            app_cons: gen_all(&[av, zv, suv, tv], &app_cons),
            sv: gen_all(&[av, zv, suv, tv], &sv),
            step_typed: gen_all(&[av, zv, suv, tv], &st),
            iota_nil: gen_all(&[av, zv, suv, tv], &inl),
            iota_cons: gen_all(&[av, zv, suv, tv, hv, lv], &ic),
        })
    }
}
