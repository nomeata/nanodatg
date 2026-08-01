//! **The stages** `V₀ = S`, `V₍ₙ₊₁₎ = Vₙ ∪ 𝒫Vₙ`, and the two facts every later
//! argument spends: the chain increases, and it is **directed**.
//!
//! # Interface
//!
//! Writing `Vₜ` for `app(iter(S), t)` — the value at `t` of the function
//! [`crate::recursion::recursion`] defines from the base `S` and the step
//! [`super::Step`] — the exports are
//!
//! ```text
//! ⊢ V₀ = S                                                    [Stages::base]
//! ⊢ ∀n. (n ∈ ω → V₍succ n₎ = G(Vₙ))                           [Stages::step_eq]
//! ⊢ ∀z. (z ∈ T(S) ↔ ∃n. (n ∈ ω ∧ z ∈ Vₙ))                     [Stages::members]
//!
//! ⊢ ∀x. x ⊆ x                                                 [subset_refl]
//! ⊢ ∀n. (n ∈ ω → Vₙ ⊆ V₍succ n₎)                              [Stages::incr]
//! ⊢ ∀m. (m ∈ ω → V₀ ⊆ Vₘ)                                     [Stages::zero_least]
//! ⊢ ∀n. (n ∈ ω → ∀m. (m ∈ ω →
//!         ∃p. (p ∈ ω ∧ (Vₙ ⊆ Vₚ ∧ Vₘ ⊆ Vₚ))))                 [Stages::directed]
//! ```
//!
//! `S` is a free variable, so every statement is really about `∀S`; the whole
//! development is parameterised by the seed and nothing here fixes one. Callers
//! need none of the derivations below.
//!
//! # Directedness without any order on `ω`
//!
//! [`Stages::directed`] is the fact that lets two stage indices be merged, and
//! merging indices is what every finiteness argument downstream needs — a
//! function out of a fibre lands in one `Vₙ` per argument, and the fibre's worth
//! of them has to be pushed into a single stage.
//!
//! The obvious route is through the linear order of `ω`: take `p := max(n,m)`.
//! That needs **trichotomy**, which this development does not have and which is
//! a two-nested-induction job on its own. It is not needed. The step operator is
//! monotone ([`super::Step::mono`]), so `Vₙ ⊆ Vₚ` implies
//! `V₍succ n₎ = G(Vₙ) ⊆ G(Vₚ) = V₍succ p₎`, and the induction on `n` can build
//! the merge point by *applying `succ` to the one the hypothesis produced*:
//!
//! ```text
//! n = 0        p := m,       by zero_least and reflexivity
//! n = succ n′  p := succ p′,  where p′ merges n′ and m
//! ```
//!
//! No comparison of naturals occurs anywhere, and `V₍succ p′₎` is reached by one
//! application of [`crate::recursion::Peano`]'s `succ`-closure. This is the one
//! place where choosing `x ∪ 𝒫x` over `𝒫x` as the step pays for itself twice:
//! the chain increases at *any* seed, and monotonicity of the operator is what
//! replaces the order.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funspace::discharge;
use crate::recursion::{
    induction_scheme, omega_tower, recursion, OmegaTower, Rec, Recursion,
};
use crate::separation::hyp_syl;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, exists_intro_imp, hyp_and, hyp_mp,
    imp_refl, inst_all, syl,
};

use super::step::{curry, Step};

/// `⊢ ∀x. x ⊆ x`.
pub fn subset_refl(env: &mut Env) -> Option<Thm> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));
    let body = imp_refl(Formula::mem(tz, tx.clone()));
    let out = Thm::gen(z, &body);
    debug_assert_eq!(*out.concl(), kernel::thm::subset(env, tx.clone(), tx));
    Some(Thm::gen(x, &out))
}

/// The cumulative hierarchy over a seed, and everything derived about it.
pub struct Stages {
    /// The step operator.
    pub step: Step,
    /// The recursion, its symbol `iter` and its two equations.
    pub rec: Recursion,
    /// The union `T(S) = ⋃ₙ Vₙ`, and its membership condition.
    pub tower: OmegaTower,
    /// The seed, as a free variable; `iter` and `tower` are unary in it.
    pub seed: FreeVar,
    /// `⊢ ∀n. (n ∈ ω → Vₙ ⊆ V₍succ n₎)`.
    pub incr: Thm,
    /// `⊢ ∀m. (m ∈ ω → V₀ ⊆ Vₘ)`.
    pub zero_least: Thm,
    /// `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ ω → ∃p. (p ∈ ω ∧ (Vₙ ⊆ Vₚ ∧ Vₘ ⊆ Vₚ))))`.
    pub directed: Thm,
    /// `⊢ ∀x. x ⊆ x`, which every caller needs too.
    pub subset_refl: Thm,
}

impl Stages {
    /// The term `Vₜ = app(iter(S), t)`.
    pub fn v(&self, r: &Rec, t: Term) -> Term { r.apply(self.rec.set(), t) }

    /// The term `T(S)`.
    pub fn tower_set(&self) -> Term { self.tower.set() }

    /// Run the recursion at [`Step`] and derive the three facts.
    pub fn new(env: &mut Env, r: &Rec, step: Step) -> Option<Stages> {
        let seed = env.fresh_var();
        let s = Term::var(seed);
        let rec = recursion(env, r, step.g, &s, &[seed])?;
        let tower = omega_tower(env, r, &rec, &[seed])?;

        let subset_refl = subset_refl(env)?;
        let incr = increasing(env, r, &step, &rec)?;
        let zero_least = zero_least(env, r, &rec, &incr, &subset_refl, &step.subset_trans)?;
        let directed =
            directed(env, r, &step, &rec, &incr, &zero_least, &subset_refl)?;

        Some(Stages { step, rec, tower, seed, incr, zero_least, directed, subset_refl })
    }
}

/// `⊢ ∀n. (n ∈ ω → Vₙ ⊆ V₍succ n₎)`.
///
/// One rewrite along the step equation: `V₍succ n₎` **is** `G(Vₙ)`, and
/// [`super::Step::mem`] puts every member of `Vₙ` into it.
fn increasing(env: &mut Env, r: &Rec, step: &Step, rec: &Recursion) -> Option<Thm> {
    let it = rec.set();
    let (n, z, w) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, tz) = (Term::var(n), Term::var(z));
    let vn = r.apply(it.clone(), tn.clone());
    let vsn = r.apply(it, r.succ_of(tn.clone()));
    let gvn = step.of(vn.clone());
    let h = Formula::mem(tn.clone(), r.omega());

    let h_eq = inst_all(&rec.step, std::slice::from_ref(&tn))?;
    debug_assert_eq!(
        *h_eq.concl(),
        Formula::imp(h.clone(), Formula::eq(vsn.clone(), gvn.clone())),
        "increasing: the step equation has the wrong shape"
    );
    let h_sym = syl(&h_eq, &eq_symm_imp(env, vsn.clone(), gvn.clone()))?;
    let leib = Thm::eq_leibniz(gvn, vsn.clone(), w, Formula::mem(tz.clone(), Term::var(w)));
    let h_move = syl(&h_sym, &leib)?;

    let mem_at = inst_all(&step.mem, &[vn.clone(), tz.clone()])?;
    let body = hyp_syl(&a1i(&mem_at, h.clone()), &h_move)?;

    let inner =
        Formula::imp(Formula::mem(tz.clone(), vn.clone()), Formula::mem(tz, vsn.clone()));
    let out = Thm::mp(&Thm::ax_dist(z, h.clone(), inner)?, &Thm::gen(z, &body))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::subset(env, vn, vsn)),
        "increasing: unexpected shape"
    );
    Some(Thm::gen(n, &out))
}

/// `⊢ ∀m. (m ∈ ω → V₀ ⊆ Vₘ)` — the seed stage is below every stage.
///
/// An induction on `m` whose step is [`increasing`] and [`super::subset_trans`].
/// It replaces the fact that `0` is the least natural, which would otherwise
/// have to be proved to instantiate a `n ∈ m → Vₙ ⊆ Vₘ` at `n = 0`.
fn zero_least(
    env: &mut Env,
    r: &Rec,
    rec: &Recursion,
    incr: &Thm,
    subset_refl: &Thm,
    subset_trans: &Thm,
) -> Option<Thm> {
    let it = rec.set();
    let mv = env.fresh_var();
    let tm = Term::var(mv);
    let v0 = r.apply(it.clone(), r.zero());
    let vm = r.apply(it.clone(), tm.clone());
    let vsm = r.apply(it, r.succ_of(tm.clone()));
    let phi = kernel::thm::subset(env, v0.clone(), vm.clone());

    let base = inst_all(subset_refl, std::slice::from_ref(&v0))?;
    debug_assert_eq!(*base.concl(), phi.subst(mv, &r.zero()), "zero_least: base drifted");

    // `K := m ∈ ω ∧ V₀ ⊆ Vₘ`.
    let m_om = Formula::mem(tm.clone(), r.omega());
    let k = Formula::and(m_om.clone(), phi.clone());
    let k_incr = syl(&and_left(m_om.clone(), phi.clone()), &inst_all(incr, std::slice::from_ref(&tm))?)?;
    let k_phi = and_right(m_om, phi.clone());
    let conj = hyp_and(&k_phi, &k_incr)?;
    let trans_at = inst_all(subset_trans, &[v0.clone(), vm, vsm.clone()])?;
    let step = syl(&conj, &trans_at)?;
    debug_assert_eq!(
        *step.concl(),
        Formula::imp(k, phi.subst(mv, &r.succ_of(tm.clone()))),
        "zero_least: step drifted"
    );
    let _ = vsm;

    let scheme = induction_scheme(env, r.core(), mv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(mv, &step)))
}

/// `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ ω → ∃p. (p ∈ ω ∧ (Vₙ ⊆ Vₚ ∧ Vₘ ⊆ Vₚ))))` —
/// **the chain is directed**.
///
/// See the module header: the merge point is built by applying `succ` to the
/// one the induction hypothesis produced, so no order on `ω` is needed.
fn directed(
    env: &mut Env,
    r: &Rec,
    step: &Step,
    rec: &Recursion,
    incr: &Thm,
    zero_least: &Thm,
    subset_refl: &Thm,
) -> Option<Thm> {
    let it = rec.set();
    let (nv, mv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, tm, tp) = (Term::var(nv), Term::var(mv), Term::var(pv));
    let om = r.omega();

    let v = |t: Term| r.apply(it.clone(), t);
    let (vn, vm, vp) = (v(tn.clone()), v(tm.clone()), v(tp.clone()));
    let (vsn, vsp) = (v(r.succ_of(tn.clone())), v(r.succ_of(tp.clone())));

    // `body(n,m,p) := p ∈ ω ∧ (Vₙ ⊆ Vₚ ∧ Vₘ ⊆ Vₚ)`, and the goal `∃p. body`.
    let body = |env: &mut Env, a: &Term, b: &Term, p: &Term| {
        let pa = v(p.clone());
        Formula::and(
            Formula::mem(p.clone(), om.clone()),
            Formula::and(
                kernel::thm::subset(env, v(a.clone()), pa.clone()),
                kernel::thm::subset(env, v(b.clone()), pa),
            ),
        )
    };
    let ex_body = body(env, &tn, &tm, &tp);
    let goal_inner = Formula::exists(pv, ex_body.clone());
    let m_om = Formula::mem(tm.clone(), om.clone());
    // `φ(n) := ∀m. (m ∈ ω → ∃p. body(n,m,p))`.
    let phi = Formula::forall(mv, Formula::imp(m_om.clone(), goal_inner.clone()));

    // ── Base: `p := m` ──────────────────────────────────────────────────────
    let zero = r.zero();
    let ex_body_0 = ex_body.subst(nv, &zero);
    let witness_0 = ex_body_0.subst(pv, &tm);
    let h_pom = imp_refl(m_om.clone());
    let h_zl = inst_all(zero_least, std::slice::from_ref(&tm))?;
    let h_refl = a1i(&inst_all(subset_refl, std::slice::from_ref(&vm))?, m_om.clone());
    let h_body = hyp_and(&h_pom, &hyp_and(&h_zl, &h_refl)?)?;
    debug_assert_eq!(
        *h_body.concl(),
        Formula::imp(m_om.clone(), witness_0),
        "directed: the base witness drifted"
    );
    let base_body = syl(&h_body, &exists_intro_imp(pv, ex_body_0, tm.clone())?)?;
    let base = Thm::gen(mv, &base_body);
    debug_assert_eq!(*base.concl(), phi.subst(nv, &zero), "directed: the base drifted");

    // ── Step: `p := succ p′` ────────────────────────────────────────────────
    let n_om = Formula::mem(tn.clone(), om.clone());
    let k = Formula::and(n_om.clone(), phi.clone());
    let j = Formula::and(k.clone(), m_om.clone());

    let j_k = and_left(k.clone(), m_om.clone());
    let j_m = and_right(k.clone(), m_om.clone());
    let j_phi = syl(&j_k, &and_right(n_om.clone(), phi.clone()))?;
    let j_ex = hyp_mp(&syl(&j_phi, &Thm::ax_inst(phi.clone(), tm.clone())?)?, &j_m)?;

    // `L := J ∧ body(n,m,p)`; unpack the three conjuncts.
    let e = ex_body.clone();
    let l_j = and_left(j.clone(), e.clone());
    let (p_om, rest) = (
        Formula::mem(tp.clone(), om.clone()),
        Formula::and(
            kernel::thm::subset(env, vn.clone(), vp.clone()),
            kernel::thm::subset(env, vm.clone(), vp.clone()),
        ),
    );
    let l_e = and_right(j.clone(), e.clone());
    let l_p = syl(&l_e, &and_left(p_om.clone(), rest.clone()))?;
    let l_rest = syl(&l_e, &and_right(p_om.clone(), rest.clone()))?;
    let sub_np = kernel::thm::subset(env, vn.clone(), vp.clone());
    let sub_mp = kernel::thm::subset(env, vm.clone(), vp.clone());
    let l_np = syl(&l_rest, &and_left(sub_np.clone(), sub_mp.clone()))?;
    let l_mp = syl(&l_rest, &and_right(sub_np, sub_mp))?;
    let l_n = syl(&l_j, &syl(&j_k, &and_left(n_om.clone(), phi.clone()))?)?;

    // `succ p ∈ ω`.
    let succ_closed_at = inst_all(&r.core().succ_closed, std::slice::from_ref(&tp))?;
    let l_sp = hyp_mp(&a1i(&succ_closed_at, Formula::and(j.clone(), e.clone())), &l_p)?;

    // `V₍succ n₎ ⊆ V₍succ p₎`, by monotonicity of the step across both equations.
    let l = Formula::and(j.clone(), e.clone());
    let (gvn, gvp) = (step.of(vn.clone()), step.of(vp.clone()));
    let mono_at = inst_all(&step.mono, &[vn.clone(), vp.clone()])?;
    let l_gmono = hyp_mp(&a1i(&mono_at, l.clone()), &l_np)?;

    let eq_n = hyp_mp(&a1i(&inst_all(&rec.step, std::slice::from_ref(&tn))?, l.clone()), &l_n)?;
    let eq_p = hyp_mp(&a1i(&inst_all(&rec.step, std::slice::from_ref(&tp))?, l.clone()), &l_p)?;
    let w = env.fresh_var();
    let tw = Term::var(w);
    let sym_n = syl(&eq_n, &eq_symm_imp(env, vsn.clone(), gvn.clone()))?;
    let sym_p = syl(&eq_p, &eq_symm_imp(env, vsp.clone(), gvp.clone()))?;
    let leib_l = Thm::eq_leibniz(
        gvn.clone(),
        vsn.clone(),
        w,
        kernel::thm::subset(env, tw.clone(), gvp.clone()),
    );
    let leib_r = Thm::eq_leibniz(
        gvp.clone(),
        vsp.clone(),
        w,
        kernel::thm::subset(env, vsn.clone(), tw),
    );
    let l_step1 = hyp_mp(&syl(&sym_n, &leib_l)?, &l_gmono)?;
    let l_step2 = hyp_mp(&syl(&sym_p, &leib_r)?, &l_step1)?;

    // `Vₘ ⊆ V₍succ p₎`, by `Vₘ ⊆ Vₚ ⊆ V₍succ p₎`.
    let l_incr = hyp_mp(&a1i(&inst_all(incr, std::slice::from_ref(&tp))?, l.clone()), &l_p)?;
    let trans_at = inst_all(&step.subset_trans, &[vm.clone(), vp.clone(), vsp.clone()])?;
    let l_msp = hyp_mp(&a1i(&trans_at, l.clone()), &hyp_and(&l_mp, &l_incr)?)?;

    let succ_n = r.succ_of(tn.clone());
    let succ_p = r.succ_of(tp.clone());
    let ex_body_s = ex_body.subst(nv, &succ_n);
    let witness_s = ex_body_s.subst(pv, &succ_p);
    let l_witness = hyp_and(&l_sp, &hyp_and(&l_step2, &l_msp)?)?;
    debug_assert_eq!(
        *l_witness.concl(),
        Formula::imp(l, witness_s),
        "directed: the step witness drifted"
    );
    let l_goal = syl(&l_witness, &exists_intro_imp(pv, ex_body_s, succ_p)?)?;

    let j_goal = discharge(pv, &j_ex, &l_goal)?;
    let curried = curry(&j_goal)?;
    let inner = Formula::imp(m_om, goal_inner.subst(nv, &succ_n));
    let step_thm = Thm::mp(&Thm::ax_dist(mv, k.clone(), inner)?, &Thm::gen(mv, &curried))?;
    debug_assert_eq!(
        *step_thm.concl(),
        Formula::imp(k, phi.subst(nv, &succ_n)),
        "directed: the step drifted"
    );

    let scheme = induction_scheme(env, r.core(), nv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &step_thm)))
}
