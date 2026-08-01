//! The graph of the recursion is a function on `ω` satisfying both equations.
//!
//! # Interface
//!
//! Writing `Γ` for [`crate::recursion::Family`]'s symbol, [`Iter`] bundles
//!
//! ```text
//! ⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → ⟨n, app(h,n)⟩ ∈ Γ)        [Iter::intro]
//! ⊢ ∀a ∀b. (⟨a,b⟩ ∈ Γ → (a ∈ ω ∧ ∃h. (Approx(succ a,h) ∧ b = app(h,a))))
//!                                                                 [Iter::decompose]
//! ⊢ SingleValued(Γ)                                               [Iter::single]
//! ⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → app(Γ,n) = app(h,n))      [Iter::value]
//! ⊢ RecFn(Γ)                                                      [Iter::property]
//! ```
//!
//! where `RecFn(f)` is [`rec_fn`]'s five conjuncts:
//!
//! ```text
//! R1  ∀p. (p ∈ f → ∃a. (a ∈ ω ∧ ∃b. p = ⟨a,b⟩))       f holds nothing but pairs over ω
//! R2  ∀x ∀y ∀y′. ((⟨x,y⟩ ∈ f ∧ ⟨x,y′⟩ ∈ f) → y = y′)  f is single-valued
//! R3  ∀a. (a ∈ ω → ∃b. ⟨a,b⟩ ∈ f)                     f is total on ω
//! R4  app(f, 0) = c                                    the base equation
//! R5  ∀n. (n ∈ ω → app(f, succ n) = G(app(f,n)))       the step equation
//! ```
//!
//! R1–R3 together are "`f` is a function with domain `ω`", spelled without a
//! `dom` symbol and without a codomain — the first three conjuncts of
//! [`crate::recursion::Approx`] at `m := ω`, which is why they are taken from
//! there rather than restated. Only R5 differs from A5: `Approx` states the step
//! as a membership, because that is the form its induction produces, while the
//! recursion theorem states it as an equation between applications, because that
//! is the form its consumers want. Single-valuedness converts one into the other.
//!
//! # Where the two equations come from
//!
//! R4 is the base pair of the *one-point* approximation, read back through
//! [`crate::recursion::app_of_graph`]. R5 is the only place the cross-domain
//! form of [`crate::recursion::approx_agree`] is spent: `app(Γ, succ n)` is read
//! off the approximation with domain `succ(succ n)` and `app(Γ, n)` off the one
//! with domain `succ n`, and the step equation of the former relates the two at
//! the single point `n`.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, exists_elim_imp, exists_intro_imp, exists_mono, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, inst_all, syl,
};
use crate::funspace::discharge;
use super::approximation::{approx, conj, conj_proj};
use super::existence::{approx_one, one_point_graph};
use super::family::Family;
use super::hyp::{hyp_eq_symm, hyp_eq_trans};
use super::peano::mem_succ_self;
use super::rec::Rec;

/// The five conjuncts of "`f` is the recursion with base `c` and step `G`".
pub struct RecFn {
    /// R1 — every member of `f` is a pair whose first component lies in `ω`.
    pub bounded: Formula,
    /// R2 — `f` is single-valued.
    pub single: Formula,
    /// R3 — `f` is total on `ω`.
    pub total: Formula,
    /// R4 — `app(f,0) = c`.
    pub base: Formula,
    /// R5 — `∀n. (n ∈ ω → app(f, succ n) = G(app(f,n)))`.
    pub step: Formula,
}

impl RecFn {
    /// The five conjuncts, in order.
    pub fn parts(&self) -> [Formula; 5] {
        [
            self.bounded.clone(),
            self.single.clone(),
            self.total.clone(),
            self.base.clone(),
            self.step.clone(),
        ]
    }

    /// `RecFn(f)` itself.
    pub fn formula(&self) -> Formula { conj(&self.parts()) }

    /// `⊢ RecFn(f) → Rᵢ`, counting from zero.
    pub fn proj(&self, i: usize) -> Option<Thm> { conj_proj(&self.parts(), i) }
}

/// Build [`RecFn`] for a base value `c`, a unary step symbol `g` and a candidate
/// function `f`.
///
/// R1–R4 are the corresponding conjuncts of [`crate::recursion::Approx`] at
/// `m := ω`; only R5 is new.
pub fn rec_fn(env: &mut Env, r: &Rec, g: FnSym, c: &Term, f: &Term) -> Option<RecFn> {
    let ax = approx(env, r, g, c, &r.omega(), f)?;
    let n = env.fresh_var();
    let tn = Term::var(n);
    let step = Formula::forall(
        n,
        Formula::imp(
            Formula::mem(tn.clone(), r.omega()),
            Formula::eq(
                r.apply(f.clone(), r.succ_of(tn.clone())),
                Term::apply(g, vec![r.apply(f.clone(), tn)]),
            ),
        ),
    );
    let base = Formula::eq(r.apply(f.clone(), r.zero()), c.clone());
    Some(RecFn { bounded: ax.bounded, single: ax.single, total: ax.total, base, step })
}

/// The recursion's graph, together with everything proved about it.
pub struct Iter {
    /// The Replacement instance the graph came from.
    pub fam: Family,
    /// `⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → ⟨n, app(h,n)⟩ ∈ Γ)`.
    pub intro: Thm,
    /// `⊢ ∀a ∀b. (⟨a,b⟩ ∈ Γ → (a ∈ ω ∧ ∃h. (Approx(succ a,h) ∧ b = app(h,a))))`.
    pub decompose: Thm,
    /// `⊢ SingleValued(Γ)`.
    pub single: Thm,
    /// `⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → app(Γ,n) = app(h,n))`.
    pub value: Thm,
    /// `⊢ RecFn(Γ)`.
    pub property: Thm,
}

impl Iter {
    /// The term `Γ`.
    pub fn set(&self) -> Term { self.fam.set() }
}

/// The body `∃h. (Approx(succ a, h) ∧ b = app(h,a))` of [`Iter::decompose`], at
/// a caller-supplied bound variable.
fn value_exists(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    vh: FreeVar,
    a: &Term,
    b: &Term,
) -> Option<Formula> {
    let tvh = Term::var(vh);
    let ax = approx(env, r, g, c, &r.succ_of(a.clone()), &tvh)?;
    Some(Formula::exists(
        vh,
        Formula::and(ax.formula(), Formula::eq(b.clone(), r.apply(tvh, a.clone()))),
    ))
}

/// `⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → ⟨n, app(h,n)⟩ ∈ Γ)`.
pub fn graph_intro(env: &mut Env, r: &Rec, g: FnSym, c: &Term, fam: &Family) -> Option<Thm> {
    let (n, h, v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, th, tv) = (Term::var(n), Term::var(h), Term::var(v));
    let sn = r.succ_of(tn.clone());
    let axn = approx(env, r, g, c, &sn, &th)?;
    let axv = approx(env, r, g, c, &sn, &tv)?;
    let n_om = Formula::mem(tn.clone(), r.omega());
    let hyp = Formula::and(n_om.clone(), axn.formula());
    let yv = r.pair(tn.clone(), r.apply(th.clone(), tn.clone()));

    let body = Formula::and(
        axv.formula(),
        Formula::eq(yv.clone(), r.pair(tn.clone(), r.apply(tv, tn.clone()))),
    );
    debug_assert_eq!(
        Formula::exists(v, body.clone()),
        fam.phi.subst(fam.x, &tn).subst(fam.y, &yv),
        "graph_intro: the relation drifted"
    );
    let h_inner = hyp_mp(
        &a1i(&exists_intro_imp(v, body, th.clone())?, hyp.clone()),
        &hyp_and(
            &and_right(n_om.clone(), axn.formula()),
            &a1i(&Thm::eq_refl(yv.clone()), hyp.clone()),
        )?,
    )?;

    let outer = Formula::and(
        Formula::mem(Term::var(fam.x), r.omega()),
        fam.phi.subst(fam.y, &yv),
    );
    let h_outer = hyp_mp(
        &a1i(&exists_intro_imp(fam.x, outer, tn.clone())?, hyp.clone()),
        &hyp_and(&and_left(n_om, axn.formula()), &h_inner)?,
    )?;
    let out = hyp_mp(
        &a1i(&iff_mpr(&inst_all(&fam.members, std::slice::from_ref(&yv))?)?, hyp.clone()),
        &h_outer,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::mem(yv, fam.set())),
        "graph_intro: unexpected shape"
    );
    Some(gen_all(&[n, h], &out))
}

/// `⊢ ∀a ∀b. (⟨a,b⟩ ∈ Γ → (a ∈ ω ∧ ∃h. (Approx(succ a,h) ∧ b = app(h,a))))`.
///
/// Injectivity of the Kuratowski pair turns the index the graph was built with
/// into the index the pair displays; everything downstream reads the graph
/// through this lemma rather than through
/// [`crate::recursion::Family::members`].
pub fn graph_decompose(env: &mut Env, r: &Rec, g: FnSym, c: &Term, fam: &Family) -> Option<Thm> {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (vx, vh, w) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tvx, tvh) = (Term::var(a), Term::var(b), Term::var(vx), Term::var(vh));
    let pab = r.pair(ta.clone(), tb.clone());
    let mem_ab = Formula::mem(pab.clone(), fam.set());

    let a_om = Formula::mem(ta.clone(), r.omega());
    let target = value_exists(env, r, g, c, vh, &ta, &tb)?;
    let goal = Formula::and(a_om.clone(), target.clone());

    // `Φ(w) := Approx(succ w, h) ∧ ⟨a,b⟩ = ⟨w, app(h,w)⟩`, the body of the
    // relation with its index left open.
    let phi_of = |env: &mut Env, t: &Term| -> Option<Formula> {
        let ax = approx(env, r, g, c, &r.succ_of(t.clone()), &tvh)?;
        Some(Formula::and(
            ax.formula(),
            Formula::eq(pab.clone(), r.pair(t.clone(), r.apply(tvh.clone(), t.clone()))),
        ))
    };
    let body_x = phi_of(env, &tvx)?;
    let body_w = phi_of(env, &Term::var(w))?;
    let e_x = Formula::and(Formula::mem(tvx.clone(), r.omega()), Formula::exists(vh, body_x.clone()));
    debug_assert_eq!(
        Formula::exists(vx, e_x.clone()),
        Formula::exists(fam.x, Formula::and(Formula::mem(Term::var(fam.x), r.omega()), fam.phi.clone()))
            .subst(fam.y, &pab),
        "graph_decompose: the image drifted"
    );
    let ex_x = iff_mp(&inst_all(&fam.members, std::slice::from_ref(&pab))?)?;

    let j = Formula::and(mem_ab.clone(), e_x.clone());
    let j_e = and_right(mem_ab.clone(), e_x.clone());
    let j_xom = syl(&j_e, &and_left(Formula::mem(tvx.clone(), r.omega()), Formula::exists(vh, body_x.clone())))?;
    let j_phi = syl(&j_e, &and_right(Formula::mem(tvx.clone(), r.omega()), Formula::exists(vh, body_x.clone())))?;

    let k = Formula::and(j.clone(), body_x.clone());
    let k_j = and_left(j.clone(), body_x.clone());
    let k_body = and_right(j.clone(), body_x.clone());
    let ax_x = approx(env, r, g, c, &r.succ_of(tvx.clone()), &tvh)?;
    let eq_pair = Formula::eq(pab.clone(), r.pair(tvx.clone(), r.apply(tvh.clone(), tvx.clone())));
    let k_eq = syl(&k_body, &and_right(ax_x.formula(), eq_pair))?;
    let pinj = inst_all(
        &r.ap.pair_inj,
        &[ta.clone(), tb.clone(), tvx.clone(), r.apply(tvh.clone(), tvx.clone())],
    )?;
    let k_comp = hyp_mp(&a1i(&pinj, k.clone()), &k_eq)?;
    let k_ax_eq = syl(
        &k_comp,
        &and_left(
            Formula::eq(ta.clone(), tvx.clone()),
            Formula::eq(tb.clone(), r.apply(tvh.clone(), tvx.clone())),
        ),
    )?;
    let k_xa = hyp_eq_symm(env, &k_ax_eq)?;

    let w1 = env.fresh_var();
    let leib1 = Thm::eq_leibniz(tvx.clone(), ta.clone(), w1, Formula::mem(Term::var(w1), r.omega()));
    let k_aom = hyp_mp(&hyp_mp(&a1i(&leib1, k.clone()), &k_xa)?, &syl(&k_j, &j_xom)?)?;

    let leib2 = Thm::eq_leibniz(tvx.clone(), ta.clone(), w, body_w);
    let ax_a = approx(env, r, g, c, &r.succ_of(ta.clone()), &tvh)?;
    let body_a = Formula::and(
        ax_a.formula(),
        Formula::eq(pab.clone(), r.pair(ta.clone(), r.apply(tvh.clone(), ta.clone()))),
    );
    let k_body_a = hyp_mp(&hyp_mp(&a1i(&leib2, k.clone()), &k_xa)?, &k_body)?;
    debug_assert_eq!(
        *k_body_a.concl(),
        Formula::imp(k.clone(), body_a.clone()),
        "graph_decompose: the transported body drifted"
    );
    let pinj_a = inst_all(
        &r.ap.pair_inj,
        &[ta.clone(), tb.clone(), ta.clone(), r.apply(tvh.clone(), ta.clone())],
    )?;
    let k_eq_a = syl(&k_body_a, &and_right(ax_a.formula(), Formula::eq(pab.clone(), r.pair(ta.clone(), r.apply(tvh.clone(), ta.clone())))))?;
    let k_val = syl(
        &hyp_mp(&a1i(&pinj_a, k.clone()), &k_eq_a)?,
        &and_right(
            Formula::eq(ta.clone(), ta.clone()),
            Formula::eq(tb.clone(), r.apply(tvh.clone(), ta.clone())),
        ),
    )?;
    let k_ax_a = syl(&k_body_a, &and_left(ax_a.formula(), Formula::eq(pab, r.pair(ta.clone(), r.apply(tvh.clone(), ta.clone())))))?;
    let inner_a = Formula::and(ax_a.formula(), Formula::eq(tb.clone(), r.apply(tvh.clone(), ta.clone())));
    let k_ex = hyp_mp(
        &a1i(&exists_intro_imp(vh, inner_a, tvh)?, k.clone()),
        &hyp_and(&k_ax_a, &k_val)?,
    )?;
    let k_goal = hyp_and(&k_aom, &k_ex)?;
    debug_assert_eq!(*k_goal.concl(), Formula::imp(k, goal.clone()));

    let j_goal = discharge(vh, &j_phi, &k_goal)?;
    let out = discharge(vx, &ex_x, &j_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(mem_ab, goal),
        "graph_decompose: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

/// `⊢ SingleValued(Γ)`.
///
/// Two pairs over the same index come from two approximations over the same
/// domain, and [`crate::recursion::approx_unique`] makes those equal.
pub fn graph_single(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    fam: &Family,
    decompose: &Thm,
    unique: &Thm,
) -> Option<Thm> {
    let (a, b, b2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (vh1, vh2) = (env.fresh_var(), env.fresh_var());
    let (ta, tb, tb2) = (Term::var(a), Term::var(b), Term::var(b2));
    let (tvh1, tvh2) = (Term::var(vh1), Term::var(vh2));
    let sa = r.succ_of(ta.clone());

    let m1 = Formula::mem(r.pair(ta.clone(), tb.clone()), fam.set());
    let m2 = Formula::mem(r.pair(ta.clone(), tb2.clone()), fam.set());
    let j = Formula::and(m1.clone(), m2.clone());
    let a_om = Formula::mem(ta.clone(), r.omega());
    let goal = Formula::eq(tb.clone(), tb2.clone());

    let inner1 = value_exists(env, r, g, c, vh1, &ta, &tb)?;
    let inner2 = value_exists(env, r, g, c, vh2, &ta, &tb2)?;
    let d1 = syl(&and_left(m1.clone(), m2.clone()), &inst_all(decompose, &[ta.clone(), tb.clone()])?)?;
    let d2 = syl(&and_right(m1, m2), &inst_all(decompose, &[ta.clone(), tb2.clone()])?)?;
    let j_aom = syl(&d1, &and_left(a_om.clone(), inner1.clone()))?;
    let j_e1 = syl(&d1, &and_right(a_om.clone(), inner1))?;
    let j_e2 = syl(&d2, &and_right(a_om, inner2))?;

    let ax1 = approx(env, r, g, c, &sa, &tvh1)?;
    let ax2 = approx(env, r, g, c, &sa, &tvh2)?;
    let eq1 = Formula::eq(tb.clone(), r.apply(tvh1.clone(), ta.clone()));
    let eq2 = Formula::eq(tb2.clone(), r.apply(tvh2.clone(), ta.clone()));
    let body1 = Formula::and(ax1.formula(), eq1.clone());
    let body2 = Formula::and(ax2.formula(), eq2.clone());

    let k = Formula::and(j.clone(), body1.clone());
    let k_j = and_left(j.clone(), body1.clone());
    let k_body = and_right(j.clone(), body1.clone());
    let l = Formula::and(k.clone(), body2.clone());
    let l_k = and_left(k.clone(), body2.clone());
    let l_body = and_right(k.clone(), body2.clone());

    let l_ax1 = syl(&l_k, &syl(&k_body, &and_left(ax1.formula(), eq1.clone()))?)?;
    let l_eq1 = syl(&l_k, &syl(&k_body, &and_right(ax1.formula(), eq1))?)?;
    let l_ax2 = syl(&l_body, &and_left(ax2.formula(), eq2.clone()))?;
    let l_eq2 = syl(&l_body, &and_right(ax2.formula(), eq2))?;
    let l_aom = syl(&l_k, &syl(&k_j, &j_aom)?)?;
    let l_sa_om = hyp_mp(
        &a1i(&inst_all(&r.core().succ_closed, std::slice::from_ref(&ta))?, l.clone()),
        &l_aom,
    )?;
    let uniq_at = inst_all(unique, &[sa, tvh1.clone(), tvh2.clone()])?;
    let l_same = hyp_mp(
        &a1i(&uniq_at, l.clone()),
        &hyp_and(&l_sa_om, &hyp_and(&l_ax1, &l_ax2)?)?,
    )?;
    let wv = env.fresh_var();
    let leib = Thm::eq_leibniz(
        tvh1,
        tvh2,
        wv,
        Formula::eq(tb.clone(), r.apply(Term::var(wv), ta.clone())),
    );
    let l_b_at_2 = hyp_mp(&hyp_mp(&a1i(&leib, l.clone()), &l_same)?, &l_eq1)?;
    let l_eq2s = hyp_eq_symm(env, &l_eq2)?;
    let l_goal = hyp_eq_trans(env, &l_b_at_2, &l_eq2s)?;

    let k_goal = discharge(vh2, &syl(&k_j, &j_e2)?, &l_goal)?;
    let out = discharge(vh1, &j_e1, &k_goal)?;
    debug_assert_eq!(*out.concl(), Formula::imp(j, goal), "graph_single: unexpected shape");
    let sv = gen_all(&[a, b, b2], &out);
    debug_assert_eq!(
        *sv.concl(),
        crate::funspace::is_single_valued(env, &r.ap.sets, &fam.set()),
        "graph_single: the single-valuedness statement drifted"
    );
    Some(sv)
}

/// `⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → app(Γ,n) = app(h,n))`.
pub fn graph_value(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    fam: &Family,
    intro: &Thm,
    single: &Thm,
) -> Option<Thm> {
    let (n, h) = (env.fresh_var(), env.fresh_var());
    let (tn, th) = (Term::var(n), Term::var(h));
    let axn = approx(env, r, g, c, &r.succ_of(tn.clone()), &th)?;
    let n_om = Formula::mem(tn.clone(), r.omega());
    let hyp = Formula::and(n_om, axn.formula());
    let value = r.apply(th.clone(), tn.clone());
    let h_mem = inst_all(intro, &[tn.clone(), th.clone()])?;
    let aog = inst_all(&r.app_of_graph, &[fam.set(), tn.clone(), value.clone()])?;
    let out = hyp_mp(&a1i(&aog, hyp.clone()), &hyp_and(&a1i(single, hyp.clone()), &h_mem)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(hyp, Formula::eq(r.apply(fam.set(), tn), value)),
        "graph_value: unexpected shape"
    );
    Some(gen_all(&[n, h], &out))
}

/// `⊢ ∀p. (p ∈ Γ → ∃a. (a ∈ ω ∧ ∃b. p = ⟨a,b⟩))` — conjunct R1.
fn graph_bounded(env: &mut Env, r: &Rec, g: FnSym, c: &Term, fam: &Family) -> Option<Thm> {
    let (p, va, vb, vh) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tva, tvb, tvh) = (Term::var(p), Term::var(va), Term::var(vb), Term::var(vh));
    let ax = approx(env, r, g, c, &r.succ_of(tva.clone()), &tvh)?;
    let body = Formula::and(
        ax.formula(),
        Formula::eq(tp.clone(), r.pair(tva.clone(), r.apply(tvh.clone(), tva.clone()))),
    );
    let a_om = Formula::mem(tva.clone(), r.omega());
    let ex_b = Formula::exists(vb, Formula::eq(tp.clone(), r.pair(tva.clone(), tvb.clone())));

    let to_ex_b = syl(
        &and_right(
            ax.formula(),
            Formula::eq(tp.clone(), r.pair(tva.clone(), r.apply(tvh.clone(), tva.clone()))),
        ),
        &exists_intro_imp(
            vb,
            Formula::eq(tp.clone(), r.pair(tva.clone(), tvb)),
            r.apply(tvh, tva.clone()),
        )?,
    )?;
    let inner = exists_elim_imp(vh, &Thm::gen(vh, &to_ex_b), &ex_b)?;
    let mapped = hyp_and(
        &and_left(a_om.clone(), Formula::exists(vh, body.clone())),
        &syl(&and_right(a_om.clone(), Formula::exists(vh, body)), &inner)?,
    )?;
    let lifted = exists_mono(va, &Thm::gen(va, &mapped))?;
    let out = syl(&iff_mp(&inst_all(&fam.members, std::slice::from_ref(&tp))?)?, &lifted)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::mem(tp, fam.set()),
            Formula::exists(va, Formula::and(a_om, ex_b))
        ),
        "graph_bounded: unexpected shape"
    );
    Some(Thm::gen(p, &out))
}

/// `⊢ ∀a. (a ∈ ω → ∃b. ⟨a,b⟩ ∈ Γ)` — conjunct R3.
fn graph_total(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    fam: &Family,
    intro: &Thm,
    exists: &Thm,
) -> Option<Thm> {
    let (a, vb, vh) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tvb, tvh) = (Term::var(a), Term::var(vb), Term::var(vh));
    let ax = approx(env, r, g, c, &r.succ_of(ta.clone()), &tvh)?;
    let a_om = Formula::mem(ta.clone(), r.omega());
    let goal = Formula::exists(vb, Formula::mem(r.pair(ta.clone(), tvb.clone()), fam.set()));

    let ex_h = Thm::mp(&Thm::ax_inst(exists.concl().clone(), ta.clone())?, exists)?;
    let k = Formula::and(a_om.clone(), ax.formula());
    let k_mem = hyp_mp(
        &a1i(&inst_all(intro, &[ta.clone(), tvh.clone()])?, k.clone()),
        &hyp_and(&and_left(a_om.clone(), ax.formula()), &and_right(a_om.clone(), ax.formula()))?,
    )?;
    let k_goal = syl(
        &k_mem,
        &exists_intro_imp(
            vb,
            Formula::mem(r.pair(ta.clone(), tvb), fam.set()),
            r.apply(tvh, ta.clone()),
        )?,
    )?;
    let out = discharge(vh, &ex_h, &k_goal)?;
    debug_assert_eq!(*out.concl(), Formula::imp(a_om, goal), "graph_total: unexpected shape");
    Some(Thm::gen(a, &out))
}

/// `⊢ app(Γ, 0) = c` — conjunct R4.
fn graph_base(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    fam: &Family,
    value: &Thm,
) -> Option<Thm> {
    let zero = r.zero();
    let h0 = one_point_graph(r, c);
    let one = approx_one(env, r, g, c)?;
    let ax0 = approx(env, r, g, c, &r.succ_of(zero.clone()), &h0)?;

    let at_zero = inst_all(value, &[zero.clone(), h0.clone()])?;
    let v = Thm::mp(&at_zero, &crate::and_intro(&r.core().zero_mem, &one))?;
    // `app(h0, 0) = c`, from the base pair of `h0` and its single-valuedness.
    let aog = inst_all(&r.app_of_graph, &[h0, zero.clone(), c.clone()])?;
    let inner = Thm::mp(
        &aog,
        &crate::and_intro(&Thm::mp(&ax0.proj(1)?, &one)?, &Thm::mp(&ax0.proj(3)?, &one)?),
    )?;
    let out = crate::eq_trans(env, &v, &inner)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(r.apply(fam.set(), zero), c.clone()),
        "graph_base: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀n. (n ∈ ω → app(Γ, succ n) = G(app(Γ,n)))` — conjunct R5.
///
/// The only place the cross-domain form of [`crate::recursion::approx_agree`] is
/// spent: `app(Γ, succ n)` is read off the approximation with domain
/// `succ(succ n)`, `app(Γ, n)` off the one with domain `succ n`, and the step
/// equation of the former relates the two at the single point `n`.
#[allow(clippy::too_many_arguments)]
fn graph_step(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    fam: &Family,
    value: &Thm,
    exists: &Thm,
    agree: &Thm,
) -> Option<Thm> {
    let core = r.core();
    let (n, vh, vh2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, th, th2) = (Term::var(n), Term::var(vh), Term::var(vh2));
    let sn = r.succ_of(tn.clone());
    let ssn = r.succ_of(sn.clone());
    let gam = fam.set();
    let g_of = |t: Term| Term::apply(g, vec![t]);

    let ax1 = approx(env, r, g, c, &sn, &th)?;
    let ax2 = approx(env, r, g, c, &ssn, &th2)?;
    let n_om = Formula::mem(tn.clone(), r.omega());
    let goal = Formula::eq(r.apply(gam.clone(), sn.clone()), g_of(r.apply(gam.clone(), tn.clone())));

    let j_sn_om = crate::syl(
        &crate::imp_refl(n_om.clone()),
        &inst_all(&core.succ_closed, std::slice::from_ref(&tn))?,
    )?;
    let ex_h = Thm::mp(&Thm::ax_inst(exists.concl().clone(), tn.clone())?, exists)?;
    let ex_h2 = crate::syl(
        &j_sn_om,
        &Thm::mp(&Thm::ax_inst(exists.concl().clone(), sn.clone())?, exists)?,
    )?;

    let k = Formula::and(n_om.clone(), ax1.formula());
    let l = Formula::and(k.clone(), ax2.formula());
    let l_k = and_left(k.clone(), ax1.formula());
    let l_ax2 = and_right(k.clone(), ax2.formula());
    let l_nom = crate::syl(&and_left(k.clone(), ax2.formula()), &and_left(n_om.clone(), ax1.formula()))?;
    let l_ax1 = crate::syl(&and_left(k.clone(), ax2.formula()), &and_right(n_om.clone(), ax1.formula()))?;
    let _ = l_k;
    let l_sn_om = crate::syl(&l_nom, &inst_all(&core.succ_closed, std::slice::from_ref(&tn))?)?;
    let l_ssn_om = crate::syl(&l_sn_om, &inst_all(&core.succ_closed, std::slice::from_ref(&sn))?)?;

    // `app(Γ,n) = app(h,n)` and `app(Γ, succ n) = app(h₂, succ n)`.
    let l_v1 = hyp_mp(
        &a1i(&inst_all(value, &[tn.clone(), th.clone()])?, l.clone()),
        &hyp_and(&l_nom, &l_ax1)?,
    )?;
    let l_v2 = hyp_mp(
        &a1i(&inst_all(value, &[sn.clone(), th2.clone()])?, l.clone()),
        &hyp_and(&l_sn_om, &l_ax2)?,
    )?;

    // `app(h₂, succ n) = G(app(h₂, n))`, from A5 of `h₂` at `n`.
    let new_pair = r.pair(sn.clone(), g_of(r.apply(th2.clone(), tn.clone())));
    let a5_at = Thm::ax_inst(ax2.step.clone(), tn.clone())?;
    let l_pair = hyp_mp(
        &crate::syl(&crate::syl(&l_ax2, &ax2.proj(4)?)?, &a5_at)?,
        &a1i(&mem_succ_self(core, &sn)?, l.clone()),
    )?;
    let aog2 = inst_all(
        &r.app_of_graph,
        &[th2.clone(), sn.clone(), g_of(r.apply(th2.clone(), tn.clone()))],
    )?;
    let _ = new_pair;
    let l_v3 = hyp_mp(
        &a1i(&aog2, l.clone()),
        &hyp_and(&crate::syl(&l_ax2, &ax2.proj(1)?)?, &l_pair)?,
    )?;

    // `app(h,n) = app(h₂,n)`, by agreement across the two domains.
    let agree_at = Thm::mp(&Thm::ax_inst(agree.concl().clone(), tn.clone())?, agree)?;
    let (_, agree_body) = agree_at.concl().as_imp()?;
    let agree_inst = crate::syl(
        &agree_at,
        &super::hyp::inst_chain(&agree_body, &[sn.clone(), th.clone(), ssn.clone(), th2.clone()])?,
    )?;
    let n_in_sn = a1i(&mem_succ_self(core, &tn)?, l.clone());
    let into_ssn = crate::syl(
        &crate::funcs::or_intro_left(
            Formula::mem(tn.clone(), sn.clone()),
            Formula::eq(tn.clone(), sn.clone()),
        ),
        &iff_mpr(&inst_all(&core.succ_ax, &[sn.clone(), tn.clone()])?)?,
    )?;
    let n_in_ssn = crate::syl(&n_in_sn, &into_ssn)?;
    let l_agree = hyp_mp(
        &hyp_mp(&a1i(&agree_inst, l.clone()), &l_nom)?,
        &hyp_and(
            &l_sn_om,
            &hyp_and(
                &l_ax1,
                &hyp_and(&l_ssn_om, &hyp_and(&l_ax2, &hyp_and(&n_in_sn, &n_in_ssn)?)?)?,
            )?,
        )?,
    )?;

    // Chain: `app(Γ, succ n) = app(h₂, succ n) = G(app(h₂,n)) = G(app(Γ,n))`.
    let l_left = hyp_eq_trans(env, &l_v2, &l_v3)?;
    let l_gam_h2 = hyp_eq_trans(env, &l_v1, &l_agree)?;
    let cg = {
        let w = env.fresh_var();
        crate::mpd_const(
            &Thm::eq_leibniz(
                r.apply(gam.clone(), tn.clone()),
                r.apply(th2.clone(), tn.clone()),
                w,
                Formula::eq(g_of(r.apply(gam.clone(), tn.clone())), g_of(Term::var(w))),
            ),
            &Thm::eq_refl(g_of(r.apply(gam.clone(), tn.clone()))),
        )?
    };
    let l_gg = crate::syl(&l_gam_h2, &cg)?;
    let l_ggs = hyp_eq_symm(env, &l_gg)?;
    let l_goal = hyp_eq_trans(env, &l_left, &l_ggs)?;
    debug_assert_eq!(*l_goal.concl(), Formula::imp(l, goal.clone()));

    let k_goal = discharge(vh2, &crate::syl(&and_left(n_om.clone(), ax1.formula()), &ex_h2)?, &l_goal)?;
    let out = discharge(vh, &ex_h, &k_goal)?;
    debug_assert_eq!(*out.concl(), Formula::imp(n_om, goal), "graph_step: unexpected shape");
    Some(Thm::gen(n, &out))
}

/// Assemble [`Iter`]: everything about `Γ`, ending in `⊢ RecFn(Γ)`.
///
/// `unique`, `exists` and `agree` must be the theorems of
/// [`crate::recursion::approx_unique`], [`crate::recursion::approx_exists`] and
/// [`crate::recursion::approx_agree`] at the same `g` and `c` as `fam`; all are
/// instantiated, never rebuilt.
#[allow(clippy::too_many_arguments)]
pub fn iterate(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    fam: Family,
    unique: &Thm,
    exists: &Thm,
    agree: &Thm,
) -> Option<Iter> {
    let intro = graph_intro(env, r, g, c, &fam)?;
    let decompose = graph_decompose(env, r, g, c, &fam)?;
    let single = graph_single(env, r, g, c, &fam, &decompose, unique)?;
    let value = graph_value(env, r, g, c, &fam, &intro, &single)?;

    let bounded = graph_bounded(env, r, g, c, &fam)?;
    let total = graph_total(env, r, g, c, &fam, &intro, exists)?;
    let base = graph_base(env, r, g, c, &fam, &value)?;
    let step = graph_step(env, r, g, c, &fam, &value, exists, agree)?;

    let spec = rec_fn(env, r, g, c, &fam.set())?;
    debug_assert_eq!(*bounded.concl(), spec.bounded, "iterate: R1 drifted");
    debug_assert_eq!(*single.concl(), spec.single, "iterate: R2 drifted");
    debug_assert_eq!(*total.concl(), spec.total, "iterate: R3 drifted");
    debug_assert_eq!(*base.concl(), spec.base, "iterate: R4 drifted");
    debug_assert_eq!(*step.concl(), spec.step, "iterate: R5 drifted");
    let property = crate::and_intro(
        &bounded,
        &crate::and_intro(&single, &crate::and_intro(&total, &crate::and_intro(&base, &step))),
    );
    debug_assert_eq!(*property.concl(), spec.formula(), "iterate: unexpected shape");
    Some(Iter { fam, intro, decompose, single, value, property })
}
