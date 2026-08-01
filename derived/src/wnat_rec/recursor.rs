//! `N.rec`, packaged.
//!
//! # Interface
//!
//! [`NatRec::over`] builds every symbol and derives every theorem over a
//! caller-supplied [`crate::wnat::Nat`]. The fields are the
//! theorems, and [`NatRec::of`] builds the term `nrec(z,s,T)`. With
//! `HYP := z ∈ T ∧ s ∈ fs(N, fs(T,T))`:
//!
//! ```text
//! ⊢ ∀z ∀s ∀T. app(e(z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z                       [app_zero]
//! ⊢ ∀z ∀s ∀T ∀f ∀r. ((f ∈ FW ∧ r ∈ FT(T)) → …)                       [app_succ]
//! ⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))     [step_typed]
//! ⊢ ∀z ∀s ∀T. (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)              [iota_zero]
//! ⊢ ∀z ∀s ∀T ∀n. ((HYP ∧ n ∈ N) → …)                               [iota_succ]
//! ```
//!
//! [`premise_witness`] discharges `HYP` at a concrete instance, which is what
//! `tests/wnat_rec.rs` uses to show the theorems are not about an unsatisfiable
//! antecedent.
//!
//! # Why it is a struct
//!
//! Every theorem here is about *the* `N`, *the* step symbol and *the* recursor
//! of one definitional extension. Building any of them twice would mint a second
//! `upair`, and then none of the theorems would compose.

use kernel::{Env, Formula, Term, Thm};
use crate::bound::Bound;
use crate::wnat::Nat;
use crate::point_fun::PointFun;
use crate::proj::Proj;
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, gen_all, hyp_and, inst_all, syl};

use super::step::StepSyms;
use super::values::step_single_valued;
use super::computes::step_apps;
use super::typed::{premise, step_typed_at};
use super::iota::{iota_succ_at, iota_zero_at};

/// **The hypothesis both ι rules carry is satisfiable**, at `T := 1`.
///
/// ```text
/// ⊢ • ∈ 1  ∧  const(N) ∈ fs(N, fs(1,1))
/// ```
///
/// A theorem whose antecedent no three sets satisfy proves nothing, and `HYP`
/// is not one [`crate::wbool_rec`] had to worry about — `Bool`'s `step_typed`
/// was discharged outright. Here it is a real hypothesis, so a witness is
/// needed: `T := 1`, `z := •`, and for `s` the constant function on `N` taking
/// the value `{⟨•,•⟩}`, which is in `fs(1,1)` by
/// [`crate::point_fun::point_in_funspace`]. Returns the two terms alongside the
/// theorem so a caller can instantiate the ι rules at them.
pub fn premise_witness(
    env: &mut Env,
    wt: &Wtype,
    nat: &Nat,
    pf: &PointFun,
) -> Option<(Term, Term, Term, Thm)> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (one, point) = (s.unit(), s.point());
    let t = one.clone();

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

    // The constant function `N → fs(1,1)`.
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let (c, c_ax) = crate::define_abbrev(env, &[xv], &id1)?;
    let (lam, lam_ax) = crate::funcs::lambda(env, ap, c)?;
    let su = Term::apply(lam, vec![nat.ty.clone()]);

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
    let body_in = Thm::gen(
        xv,
        &a1i(&at_x, Formula::mem(tx.clone(), nat.ty.clone())),
    );
    if *body_in.concl() != crate::ext::body_in(env, c, &nat.ty, &fs11) {
        return None
    }
    let rule = crate::ext::lam_in_funspace(env, ap, &s.prod, &s.fs, c, lam, &lam_ax)?;
    let in_fs = Thm::mp(&inst_all(&rule, &[nat.ty.clone(), fs11])?, &body_in)?;

    let out = and_intro(&s.unit_mem, &in_fs);
    if *out.concl() != premise(s, nat, &point, &su, &t) {
        return None
    }
    Some((point, su, t, out))
}

/// The whole development, at fresh universally quantified variables.
pub struct NatRec {
    /// The two Replacement symbols the step is built from.
    pub syms: StepSyms,
    /// `⊢ ∀z ∀s ∀T. app(e(z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z`.
    pub app_zero: Thm,
    /// `⊢ ∀z ∀s ∀T ∀f ∀r. ((f ∈ FW ∧ r ∈ FT(T)) → app(e(z,s,T), ⟨inr •,⟨f,r⟩⟩)
    ///        = app(app(s,app(f,•)),app(r,•)))`.
    pub app_succ: Thm,
    /// `⊢ ∀z ∀s ∀T. sv(e(z,s,T))`.
    pub sv: Thm,
    /// `⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))`.
    pub step_typed: Thm,
    /// `⊢ ∀z ∀s ∀T. (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)`.
    pub iota_zero: Thm,
    /// `⊢ ∀z ∀s ∀T ∀n. ((HYP ∧ n ∈ N) → app(nrec(z,s,T), ⟨inr •,{⟨•,n⟩}⟩)
    ///        = app(app(s,n), app(nrec(z,s,T), n)))`.
    pub iota_succ: Thm,
}

impl NatRec {
    /// The recursor term `nrec(z,s,T) = wrec(1+1, B, U(1+1), T, e(z,s,T))`.
    #[allow(clippy::too_many_arguments)]
    pub fn of(
        &self,
        wt: &Wtype,
        bnd: &Bound,
        nat: &Nat,
        r: &Recursor,
        z: &Term,
        su: &Term,
        t: &Term,
    ) -> Term {
        let u = bnd.universe_of(nat.tags.clone());
        r.of(&nat.tags, &nat.fam, &u, t, &self.syms.step_of(wt, z, su, t))
    }

    /// Build the step and derive both ι rules.
    ///
    /// `iota` is [`crate::wrec_total::iota`] and `funspace`
    /// [`crate::wrec_total::wrec_funspace`], both over the *same* [`Recursor`]
    /// as `r`; `pf` is the [`crate::point_fun::PointFun`] `nat` was built over.
    /// None of them is rebuilt here, because a second copy would mint new
    /// symbols and none of the theorems would compose.
    #[allow(clippy::too_many_arguments)]
    pub fn over(
        env: &mut Env,
        wt: &Wtype,
        bnd: &Bound,
        nat: &Nat,
        rc: &Recursor,
        pf: &PointFun,
        pj: &Proj,
        iota: &Thm,
        funspace: &Thm,
    ) -> Option<NatRec> {
        let syms = StepSyms::new(env, wt, nat, pj)?;
        let (zv, suv, tv, fv, rv) = (
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
        );
        let (z, su, t, f, r) = (
            Term::var(zv),
            Term::var(suv),
            Term::var(tv),
            Term::var(fv),
            Term::var(rv),
        );
        let sv = step_single_valued(env, wt, nat, pj, &syms, &z, &su, &t)?;
        let (app_zero, app_succ) =
            step_apps(env, wt, nat, pj, &syms, &sv, &z, &su, &t, &f, &r)?;
        let app_succ = gen_all(&[fv, rv], &app_succ);
        let st = step_typed_at(env, wt, bnd, nat, &syms, &app_zero, &app_succ, &z, &su, &t)?;

        // ── The ι rule, with both of its hypotheses discharged ──────────────
        let u = bnd.universe_of(nat.tags.clone());
        let step = syms.step_of(wt, &z, &su, &t);
        let nrec = rc.of(&nat.tags, &nat.fam, &u, &t, &step);
        let hyp = premise(&wt.sums, nat, &z, &su, &t);
        let args = [nat.tags.clone(), nat.fam.clone(), u, t.clone(), step.clone()];
        let both = hyp_and(&a1i(&nat.closed, hyp.clone()), &st)?;
        let dis = syl(&both, &inst_all(iota, &args)?)?;
        let fs_thm = syl(&both, &inst_all(funspace, &args)?)?;

        let iz = iota_zero_at(env, wt, nat, rc, &dis, &app_zero, &nrec, &step, &z)?;
        let nv = env.fresh_var();
        let is = iota_succ_at(
            env, wt, nat, rc, pf, &dis, &fs_thm, &app_succ, &nrec, &step, &su, &t, nv,
        )?;

        Some(NatRec {
            syms,
            app_zero: gen_all(&[zv, suv, tv], &app_zero),
            app_succ: gen_all(&[zv, suv, tv], &app_succ),
            sv: gen_all(&[zv, suv, tv], &sv),
            step_typed: gen_all(&[zv, suv, tv], &st),
            iota_zero: gen_all(&[zv, suv, tv], &iz),
            iota_succ: gen_all(&[zv, suv, tv, nv], &is),
        })
    }
}
