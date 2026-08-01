//! [`Approx`]: what it is to be an approximation to the recursion, and the
//! bookkeeping its five clauses need.
//!
//! # Interface
//!
//! For a base value `c`, a unary step symbol `G`, a domain `m` and a candidate
//! graph `h`, [`approx`] builds the five conjuncts of `Approx(m,h)`:
//!
//! ```text
//! A1  ∀p. (p ∈ h → ∃a. (a ∈ m ∧ ∃b. p = ⟨a,b⟩))            h holds nothing but pairs over m
//! A2  ∀x ∀y ∀y′. ((⟨x,y⟩ ∈ h ∧ ⟨x,y′⟩ ∈ h) → y = y′)       h is single-valued
//! A3  ∀a. (a ∈ m → ∃b. ⟨a,b⟩ ∈ h)                          h is total on m
//! A4  ⟨0, c⟩ ∈ h                                            the base value
//! A5  ∀k. (succ k ∈ m → ⟨succ k, G(app(h,k))⟩ ∈ h)          the step equation
//! ```
//!
//! together with the one lemma every argument about A5 needs:
//!
//! ```text
//! ⊢ ∀m. (m ∈ ω → ∀k. (succ(k) ∈ m → k ∈ m))    [pred_in_omega_member]
//! ```
//!
//! Every term is *handed in*: nothing here reconstructs `m` or `h` from a
//! theorem, so a caller cannot end up with a lemma about a different graph than
//! the one it means.
//!
//! # Why these five clauses
//!
//! A1 and A3 together say `dom(h) = m` without a `dom` symbol, and A1 is what
//! makes two approximations with the same domain *equal* rather than merely
//! agreeing: without it `h` could carry junk that is not a pair at all. That is
//! the only place A1 is used, in [`crate::recursion::approx_subset`].
//!
//! A4 is stated unconditionally rather than under `0 ∈ m`, which is why the
//! induction downstream runs at `Approx(succ n, ·)` — every domain in the family
//! then contains `0`, and the empty approximation never has to be special-cased.
//!
//! [`pred_in_omega_member`] is transitivity of a natural
//! ([`crate::recursion::Peano::trans`]) applied at `a := succ(k)`, using
//! `k ∈ succ(k)` ([`crate::recursion::mem_succ_self`]). A5 mentions `app(h,k)`
//! under the hypothesis `succ(k) ∈ m`, and every argument about it needs `k`
//! itself to be in the domain.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, and_left, and_right, eq_symm_imp, gen_all, hyp_and, hyp_mp, imp_refl, inst_all, syl,
    uncurry,
};
use super::peano::mem_succ_self;
use super::rec::Rec;

/// Right-nested conjunction of `parts`, which must be non-empty.
pub(super) fn conj(parts: &[Formula]) -> Formula {
    let (last, init) = parts.split_last().expect("conj: at least one conjunct");
    init.iter().rev().fold(last.clone(), |acc, p| Formula::and(p.clone(), acc))
}

/// `⊢ conj(parts) → parts[i]` — projection out of a right-nested conjunction.
pub(super) fn conj_proj(parts: &[Formula], i: usize) -> Option<Thm> {
    let n = parts.len();
    if i >= n {
        return None
    }
    let mut cur = imp_refl(conj(parts));
    for (j, p) in parts.iter().enumerate().take(i) {
        cur = syl(&cur, &and_right(p.clone(), conj(&parts[j + 1..])))?;
    }
    if i + 1 < n {
        cur = syl(&cur, &and_left(parts[i].clone(), conj(&parts[i + 1..])))?;
    }
    Some(cur)
}

/// `Approx(m, h)` — `h` is an *approximation* to the recursion with domain `m`.
///
/// Five conjuncts, in the order the derivations consume them:
///
/// ```text
/// A1  ∀p. (p ∈ h → ∃a. (a ∈ m ∧ ∃b. p = ⟨a,b⟩))     h holds nothing but pairs over m
/// A2  ∀x ∀y ∀y′. ((⟨x,y⟩ ∈ h ∧ ⟨x,y′⟩ ∈ h) → y = y′)      h is single-valued
/// A3  ∀a. (a ∈ m → ∃b. ⟨a,b⟩ ∈ h)                          h is total on m
/// A4  ⟨0, c⟩ ∈ h                                            the base value
/// A5  ∀k. (succ k ∈ m → ⟨succ k, G(app(h,k))⟩ ∈ h)          the step equation
/// ```
///
/// A1 and A3 together say `dom(h) = m` without a `dom` symbol, and A1 is what
/// makes two approximations with the same domain *equal* rather than merely
/// agreeing: without it `h` could carry junk that is not a pair at all.
///
/// A4 is stated unconditionally rather than under `0 ∈ m`, which is why the
/// induction below runs at `Approx(succ n, ·)` — every domain in the family
/// then contains `0`, and the empty approximation never has to be special-cased.
pub struct Approx {
    /// A1 — every member of `h` is a pair whose first component lies in `m`.
    pub bounded: Formula,
    /// A2 — `h` is single-valued.
    pub single: Formula,
    /// A3 — `h` is total on `m`.
    pub total: Formula,
    /// A4 — `⟨0,c⟩ ∈ h`.
    pub base: Formula,
    /// A5 — the step equation, for every successor in `m`.
    pub step: Formula,
}

impl Approx {
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

    /// `Approx(m, h)` itself.
    pub fn formula(&self) -> Formula { conj(&self.parts()) }

    /// `⊢ Approx(m,h) → Aᵢ`, counting from zero.
    pub fn proj(&self, i: usize) -> Option<Thm> { conj_proj(&self.parts(), i) }
}

/// Build [`Approx`] for a base value `c`, a unary step symbol `g`, a domain `m`
/// and a candidate graph `h`.
///
/// Every term is *handed in*: nothing here reconstructs `m` or `h` from a
/// theorem, so a caller cannot end up with a lemma about a different graph than
/// the one it means.
pub fn approx(env: &mut Env, r: &Rec, g: FnSym, c: &Term, m: &Term, h: &Term) -> Option<Approx> {
    if g.arity() != 1 {
        return None
    }
    let sets = &r.ap.sets;
    let (p, a, b, k) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, ta, tb, tk) = (Term::var(p), Term::var(a), Term::var(b), Term::var(k));

    let bounded = Formula::forall(
        p,
        Formula::imp(
            Formula::mem(tp.clone(), h.clone()),
            Formula::exists(
                a,
                Formula::and(
                    Formula::mem(ta.clone(), m.clone()),
                    Formula::exists(b, Formula::eq(tp, sets.pair(ta.clone(), tb.clone()))),
                ),
            ),
        ),
    );
    let single = crate::funspace::is_single_valued(env, sets, h);
    let total = Formula::forall(
        a,
        Formula::imp(
            Formula::mem(ta.clone(), m.clone()),
            Formula::exists(b, Formula::mem(sets.pair(ta, tb), h.clone())),
        ),
    );
    let base = Formula::mem(sets.pair(r.zero(), c.clone()), h.clone());
    let sk = r.succ_of(tk.clone());
    let step = Formula::forall(
        k,
        Formula::imp(
            Formula::mem(sk.clone(), m.clone()),
            Formula::mem(
                sets.pair(sk, Term::apply(g, vec![r.apply(h.clone(), tk)])),
                h.clone(),
            ),
        ),
    );
    Some(Approx { bounded, single, total, base, step })
}

/// `⊢ ∀m. (m ∈ ω → ∀k. (succ(k) ∈ m → k ∈ m))` — a natural number contains the
/// predecessor of each of its successor members.
///
/// Every natural is transitive ([`crate::recursion::Peano::trans`]) and `k ∈ succ(k)`
/// ([`mem_succ_self`]), so this is transitivity applied at `a := succ(k)`. It
/// is used constantly: the step conjunct A5 of [`Approx`] mentions `app(h,k)`
/// under the hypothesis `succ(k) ∈ m`, and every argument about it needs `k`
/// itself to be in the domain.
pub fn pred_in_omega_member(env: &mut Env, r: &Rec) -> Option<Thm> {
    let (m, k) = (env.fresh_var(), env.fresh_var());
    let (tm, tk) = (Term::var(m), Term::var(k));
    let sk = r.succ_of(tk.clone());

    let m_om = Formula::mem(tm.clone(), r.omega());
    let sk_m = Formula::mem(sk.clone(), tm.clone());
    let h = Formula::and(m_om.clone(), sk_m.clone());

    // `⊢ Trans(m) → ((k ∈ succ k ∧ succ k ∈ m) → k ∈ m)`.
    let trans_m = crate::empty::transitive(env, &tm);
    let t1 = Thm::ax_inst(trans_m.clone(), sk.clone())?;
    let (_, t1b) = t1.concl().as_imp()?;
    let trans_at = syl(&t1, &Thm::ax_inst(t1b, tk.clone())?)?;

    let h_trans = syl(&and_left(m_om.clone(), sk_m.clone()), &inst_all(&r.peano.trans, std::slice::from_ref(&tm))?)?;
    let h_pair = hyp_and(
        &a1i(&mem_succ_self(r.core(), &tk)?, h.clone()),
        &and_right(m_om.clone(), sk_m.clone()),
    )?;
    let out = hyp_mp(&syl(&h_trans, &trans_at)?, &h_pair)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tk.clone(), tm.clone())),
        "pred_in_omega_member: unexpected shape"
    );
    let inner = Thm::mp(
        &Thm::ax_dist(k, m_om.clone(), Formula::imp(sk_m, Formula::mem(tk, tm)))?,
        &Thm::gen(k, &uncurry(&out)?),
    )?;
    Some(Thm::gen(m, &inner))
}

/// `⊢ ∀m ∀h ∀a ∀b. ((Approx(m,h) ∧ ⟨a,b⟩ ∈ h) → a ∈ m)` — **an approximation
/// holds no pair outside its domain**.
///
/// Conjunct A1 says every member of `h` is *some* pair over `m`; this says it is
/// *the* pair it looks like, which takes injectivity of the Kuratowski pair
/// ([`crate::funcs::Apply::pair_inj`]) to see. Every argument that extends a
/// graph needs it: the new point must be shown absent from the old graph, and
/// what is known about the new point is that it is not in the old domain.
pub fn approx_dom(env: &mut Env, r: &Rec, g: FnSym, c: &Term) -> Option<Thm> {
    let (m, h, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (a2, b2) = (env.fresh_var(), env.fresh_var());
    let (tm, th, ta, tb) = (Term::var(m), Term::var(h), Term::var(a), Term::var(b));
    let (ta2, tb2) = (Term::var(a2), Term::var(b2));

    let ax = approx(env, r, g, c, &tm, &th)?;
    let pab = r.pair(ta.clone(), tb.clone());
    let mem_ab = Formula::mem(pab.clone(), th.clone());
    let hyp = Formula::and(ax.formula(), mem_ab.clone());
    let goal = Formula::mem(ta.clone(), tm.clone());

    // A1 at `p := ⟨a,b⟩`.
    let a2_m = Formula::mem(ta2.clone(), tm.clone());
    let eq_p = Formula::eq(pab.clone(), r.pair(ta2.clone(), tb2.clone()));
    let e_inner = Formula::exists(b2, eq_p.clone());
    let e_a = Formula::and(a2_m.clone(), e_inner.clone());
    let bounded_at = Thm::ax_inst(ax.bounded.clone(), pab)?;
    debug_assert_eq!(
        bounded_at.concl().as_imp()?.1,
        Formula::imp(mem_ab.clone(), Formula::exists(a2, e_a.clone())),
        "approx_dom: conjunct A1 has an unexpected shape"
    );
    let h_ex = hyp_mp(
        &syl(
            &and_left(ax.formula(), mem_ab.clone()),
            &syl(&ax.proj(0)?, &bounded_at)?,
        )?,
        &and_right(ax.formula(), mem_ab),
    )?;

    // Open the two witnesses, then read `a = a′` off the pair.
    let j = Formula::and(hyp.clone(), e_a.clone());
    let j_e = and_right(hyp.clone(), e_a.clone());
    let j_am = syl(&j_e, &and_left(a2_m.clone(), e_inner.clone()))?;
    let j_ex_b = syl(&j_e, &and_right(a2_m, e_inner))?;

    let k = Formula::and(j.clone(), eq_p.clone());
    let k_j = and_left(j.clone(), eq_p.clone());
    let k_eq = and_right(j.clone(), eq_p.clone());
    let pinj = inst_all(&r.ap.pair_inj, &[ta.clone(), tb.clone(), ta2.clone(), tb2])?;
    let k_components = hyp_mp(&a1i(&pinj, k.clone()), &k_eq)?;
    let (_, both) = k_components.concl().as_imp()?;
    let (eq_a, eq_b) = (Formula::eq(ta.clone(), ta2.clone()), both.clone());
    let _ = eq_b;
    let k_aa2 = syl(&k_components, &and_left(eq_a, Formula::eq(tb, Term::var(b2))))?;
    let k_a2a = syl(&k_aa2, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;

    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(ta2, ta, w, Formula::mem(Term::var(w), tm));
    let k_goal = hyp_mp(&hyp_mp(&a1i(&leib, k), &k_a2a)?, &syl(&k_j, &j_am)?)?;

    let j_goal = crate::funspace::discharge(b2, &j_ex_b, &k_goal)?;
    let out = crate::funspace::discharge(a2, &h_ex, &j_goal)?;
    debug_assert_eq!(*out.concl(), Formula::imp(hyp, goal), "approx_dom: unexpected shape");
    Some(gen_all(&[m, h, a, b], &out))
}
