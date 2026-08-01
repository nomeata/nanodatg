//! From Lean's compatibility hypothesis to the one `lift` consumes.
//!
//! # Interface
//!
//! ```text
//! ker(A,f)       := { p ∈ A² : ∀u ∀v. (p = ⟨u,v⟩ → app(f,u) = app(f,v)) }
//! rcompat(A,R,f) := ∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → app(f,x) = app(f,y))
//! ```
//!
//! ```text
//! ⊢ ∀A ∀f ∀p. (p ∈ ker(A,f)
//!        ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → app(f,u) = app(f,v))))     [ker_symbol]
//! ⊢ ∀A ∀f ∀u ∀v. (⟨u,v⟩ ∈ ker(A,f) → app(f,u) = app(f,v))           [ker_pair]
//! ⊢ ∀A ∀f ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ app(f,u) = app(f,v)))
//!                     → ⟨u,v⟩ ∈ ker(A,f))                          [pair_in_ker]
//! ⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → eqv_closed(A,R,ker(A,f)))           [ker_closed]
//! ⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → compat(A,R,f))                      [compat_closure]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why this exists
//!
//! Lean's primitive is
//!
//! ```lean
//! Quot.lift : (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
//! ```
//!
//! — the hypothesis is about `r`, the *raw* relation. [`super::lift`] needs it
//! about `∼`, the equivalence closure, because that is what identifies classes.
//! The two are not the same statement, and the gap is not bridgeable by
//! unfolding: `∼` contains pairs `r` never mentions.
//!
//! It is bridgeable by **induction**. The set of pairs `f` cannot tell apart,
//!
//! ```text
//! ker(A,f) = { ⟨u,v⟩ ∈ A² : app(f,u) = app(f,v) }
//! ```
//!
//! is reflexive, symmetric and transitive *for free* — those are exactly the
//! three properties of equality, transported along `app(f,·)` — and `rcompat`
//! says precisely that it contains `R` restricted to `A`. So `ker(A,f)` is one
//! of the sets [`super::eqv::eqv_induction`] quantifies over, `∼ ⊆ ker(A,f)`,
//! and that inclusion *is* [`super::lift::compat`].
//!
//! This is the only consumer of [`super::eqv::eqv_induction`] in the module, and
//! it is what makes the intersection definition earn its keep: an `eqv` that was
//! merely *some* equivalence relation containing `R` would not support this
//! step, and `Quot.lift` would be underivable at Lean's hypothesis.
//!
//! # The `∀`-form of the kernel condition
//!
//! `ker` is carved with `∀u ∀v. (p = ⟨u,v⟩ → …)` rather than the more obvious
//! `∃u ∃v. (p = ⟨u,v⟩ ∧ …)`. Both define the same set — `p` ranges over `A²`, so
//! it *is* a pair — but the `∀`-form is cheaper at both ends: putting a pair in
//! needs injectivity of the Kuratowski pair once ([`pair_in_ker`]), and taking
//! one out is an instantiation against `Thm::eq_refl` ([`ker_pair`]). The
//! `∃`-form would need a witness-elimination in the second direction.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, conj_of, define_by_membership, eq_symm_imp, gen_all, hyp_and,
    hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl, uncurry,
};

use super::eqv::{eqv_atoms, eqv_guard};
use super::lift::compat;
use super::shared::{eq_chain, hyp_gen, inst_formula};

/// `∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → app(f,x) = app(f,y))` — Lean's
/// compatibility hypothesis `∀ a b, r a b → f a = f b`, as a formula.
///
/// The two membership guards are what `⟦R⟧ ⊆ ⟦α⟧²` would give for free and does
/// not: Lean's `r` is an arbitrary `α → α → Prop`, so the interpretation of a
/// pair outside `⟦α⟧²` is not constrained. Compare
/// [`super::eqv::contains_rel`], which guards for the same reason.
pub fn rcompat(env: &mut Env, s: &Sums, a: &Term, r: &Term, f: &Term) -> Formula {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let hyp = Formula::and(
        Formula::mem(tx.clone(), a.clone()),
        Formula::and(
            Formula::mem(ty.clone(), a.clone()),
            Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), r.clone()),
        ),
    );
    let eq = Formula::eq(s.ap.apply(f.clone(), tx), s.ap.apply(f.clone(), ty));
    Formula::forall(x, Formula::forall(y, Formula::imp(hyp, eq)))
}

/// The `ker` symbol and its defining axiom, bundled.
///
/// Same discipline as [`super::classes::Classes`] and [`super::lift::Lift`]:
/// [`Ker::parts`] rebuilds the biconditional and refuses a `ker_ax` that is not
/// the theorem of this `ker` over this pairing.
#[derive(Clone, Copy)]
pub struct Ker<'a> {
    /// Pairing, product, power set and function space.
    pub s: &'a Sums,
    /// The kernel symbol, from [`ker_symbol`].
    pub ker: FnSym,
    /// `⊢ ∀A ∀f ∀p. (p ∈ ker(A,f) ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → …)))`.
    pub ker_ax: &'a Thm,
}

impl Ker<'_> {
    /// The term `ker(A,f)`.
    fn of(&self, a: &Term, f: &Term) -> Term {
        Term::apply(self.ker, vec![a.clone(), f.clone()])
    }

    /// `∀u ∀v. (p = ⟨u,v⟩ → app(f,u) = app(f,v))` — the condition `ker`
    /// separates with.
    fn cond(&self, env: &mut Env, f: &Term, p: &Term) -> Formula {
        ker_cond(env, self.s, f, p)
    }

    /// The defining biconditional, instantiated and split.
    ///
    /// Returns `(p ∈ A², cond, forward, backward)`.
    fn parts(
        &self,
        env: &mut Env,
        a: &Term,
        f: &Term,
        p: &Term,
    ) -> Option<(Formula, Formula, Thm, Thm)> {
        let mem_prod = Formula::mem(p.clone(), self.s.prod.of(a.clone(), a.clone()));
        let cond = self.cond(env, f, p);
        let at = inst_all(self.ker_ax, &[a.clone(), f.clone(), p.clone()])?;
        let mem_ker = Formula::mem(p.clone(), self.of(a, f));
        if *at.concl() != Formula::iff(mem_ker, Formula::and(mem_prod.clone(), cond.clone())) {
            return None
        }
        Some((mem_prod, cond, iff_mp(&at)?, iff_mpr(&at)?))
    }
}

/// `∀u ∀v. (p = ⟨u,v⟩ → app(f,u) = app(f,v))`, as a formula.
fn ker_cond(env: &mut Env, s: &Sums, f: &Term, p: &Term) -> Formula {
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let (tu, tv) = (Term::var(u), Term::var(v));
    Formula::forall(
        u,
        Formula::forall(
            v,
            Formula::imp(
                Formula::eq(p.clone(), s.ap.sets.pair(tu.clone(), tv.clone())),
                Formula::eq(s.ap.apply(f.clone(), tu), s.ap.apply(f.clone(), tv)),
            ),
        ),
    )
}

/// Introduce `ker(A,f) = { p ∈ A² : ∀u ∀v. (p = ⟨u,v⟩ → app(f,u) = app(f,v)) }`.
///
/// One Separation on `prod(A,A)`, unconditional.
pub fn ker_symbol(env: &mut Env, s: &Sums) -> Option<(FnSym, Thm)> {
    let (av, fv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tp) = (Term::var(av), Term::var(fv), Term::var(pv));
    let prod_aa = s.prod.of(ta.clone(), ta.clone());
    let cond = ker_cond(env, s, &tf, &tp);
    let existence = separation_full(env, pv, &cond, &prod_aa, &s.ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(tp, prod_aa), cond);
    define_by_membership(env, &[av, fv], &existence, pv, &guard)
}

/// `⊢ ∀A ∀f ∀u ∀v. (⟨u,v⟩ ∈ ker(A,f) → app(f,u) = app(f,v))` — read the
/// condition off a member.
///
/// One instantiation of the `∀u ∀v`, discharged against `Thm::eq_refl`.
pub fn ker_pair(env: &mut Env, k: &Ker<'_>) -> Option<Thm> {
    let (av, fv, uv, vv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tu, tv) = (Term::var(av), Term::var(fv), Term::var(uv), Term::var(vv));
    let p = k.s.ap.sets.pair(tu.clone(), tv.clone());
    let (mem_prod, cond, fwd, _) = k.parts(env, &ta, &tf, &p)?;
    let to_cond = syl(&fwd, &and_right(mem_prod, cond.clone()))?;
    let at = inst_formula(&cond, &[tu.clone(), tv.clone()])?;
    let disch = syl(&to_cond, &at)?;
    let mem_ker = Formula::mem(p.clone(), k.of(&ta, &tf));
    let out = hyp_mp(&disch, &a1i(&Thm::eq_refl(p), mem_ker))?;
    Some(gen_all(&[av, fv, uv, vv], &out))
}

/// `⊢ ∀A ∀f ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ app(f,u) = app(f,v))) → ⟨u,v⟩ ∈ ker(A,f))`
/// — put a pair in.
///
/// The only step with content is turning `⟨u,v⟩ = ⟨u′,v′⟩` into `u = u′` and
/// `v = v′` (injectivity of the Kuratowski pair) and transporting the equation
/// along both.
pub fn pair_in_ker(env: &mut Env, k: &Ker<'_>) -> Option<Thm> {
    let s = k.s;
    let (av, fv, uv, vv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (u2, v2) = (env.fresh_var(), env.fresh_var());
    let (ta, tf, tu, tv) = (Term::var(av), Term::var(fv), Term::var(uv), Term::var(vv));
    let (tu2, tv2) = (Term::var(u2), Term::var(v2));
    let app = |t: &Term| s.ap.apply(tf.clone(), t.clone());
    let p = s.ap.sets.pair(tu.clone(), tv.clone());

    let (mem_u, mem_v, eq_uv) = (
        Formula::mem(tu.clone(), ta.clone()),
        Formula::mem(tv.clone(), ta.clone()),
        Formula::eq(app(&tu), app(&tv)),
    );
    let tail = Formula::and(mem_v.clone(), eq_uv.clone());
    let h = Formula::and(mem_u.clone(), tail.clone());
    let h_u = and_left(mem_u.clone(), tail.clone());
    let h_v =
        syl(&and_right(mem_u.clone(), tail.clone()), &and_left(mem_v.clone(), eq_uv.clone()))?;
    let h_eq = syl(&and_right(mem_u, tail), &and_right(mem_v, eq_uv))?;

    // `⟨u,v⟩ ∈ A²`.
    let pip = inst_all(&s.pair_in_prod, &[ta.clone(), ta.clone(), tu.clone(), tv.clone()])?;
    let h_prod = syl(&hyp_and(&h_u, &h_v)?, &iff_mpr(&pip)?)?;

    // `∀u′ ∀v′. (⟨u,v⟩ = ⟨u′,v′⟩ → app(f,u′) = app(f,v′))`.
    let is_eq = Formula::eq(p.clone(), s.ap.sets.pair(tu2.clone(), tv2.clone()));
    let big = Formula::and(h.clone(), is_eq.clone());
    let inj = inst_all(&s.ap.pair_inj, &[tu.clone(), tv.clone(), tu2.clone(), tv2.clone()])?;
    let parts = syl(&and_right(h.clone(), is_eq.clone()), &inj)?;
    let (e_u, e_v) = (Formula::eq(tu.clone(), tu2.clone()), Formula::eq(tv.clone(), tv2.clone()));
    let g_u = syl(&parts, &and_left(e_u.clone(), e_v.clone()))?;
    let g_v = syl(&parts, &and_right(e_u, e_v))?;
    let g_eq = syl(&and_left(h.clone(), is_eq), &h_eq)?;

    let w1 = env.fresh_var();
    let move_l =
        Thm::eq_leibniz(tu.clone(), tu2.clone(), w1, Formula::eq(app(&Term::var(w1)), app(&tv)));
    let step1 = hyp_mp(&syl(&g_u, &move_l)?, &g_eq)?;
    let w2 = env.fresh_var();
    let move_r =
        Thm::eq_leibniz(tv.clone(), tv2.clone(), w2, Formula::eq(app(&tu2), app(&Term::var(w2))));
    let step2 = hyp_mp(&syl(&g_v, &move_r)?, &step1)?;
    debug_assert_eq!(
        *step2.concl(),
        Formula::imp(big, Formula::eq(app(&tu2), app(&tv2))),
        "pair_in_ker: inner shape"
    );

    let mut cond_thm = uncurry(&step2)?;
    for v in [v2, u2] {
        cond_thm = hyp_gen(v, &cond_thm)?;
    }
    let (_, _, _, bwd) = k.parts(env, &ta, &tf, &p)?;
    let out = syl(&hyp_and(&h_prod, &cond_thm)?, &bwd)?;
    if out.concl().as_imp()?.0 != h {
        return None
    }
    Some(gen_all(&[av, fv, uv, vv], &out))
}

/// `⊢ ∀A ∀f. ker(A,f) ⊆ prod(A,A)` — the kernel is a relation on `A`.
pub fn ker_subset(env: &mut Env, k: &Ker<'_>) -> Option<Thm> {
    let (av, fv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tp) = (Term::var(av), Term::var(fv), Term::var(pv));
    let (mem_prod, cond, fwd, _) = k.parts(env, &ta, &tf, &tp)?;
    let out = Thm::gen(pv, &syl(&fwd, &and_left(mem_prod, cond))?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, k.of(&ta, &tf), k.s.prod.of(ta.clone(), ta.clone())),
        "ker_subset: not the subset formula the induction guard wants"
    );
    Some(gen_all(&[av, fv], &out))
}

/// `⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → eqv_closed(A,R,ker(A,f)))` — the kernel is an
/// equivalence relation on `A` containing `R`.
///
/// Three of the four clauses are **unconditional** — reflexivity, symmetry and
/// transitivity of `ker(A,f)` are reflexivity, symmetry and transitivity of `=`
/// pulled back along `app(f,·)`, and hold whatever `R` is. Only the fourth,
/// "contains `R|A`", spends the hypothesis, and it spends it by direct
/// instantiation.
pub fn ker_closed(
    env: &mut Env,
    k: &Ker<'_>,
    ker_pair: &Thm,
    pair_in_ker: &Thm,
) -> Option<Thm> {
    let s = k.s;
    let (av, rv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tf) = (Term::var(av), Term::var(rv), Term::var(fv));
    let ker_t = k.of(&ta, &tf);
    let app = |t: &Term| s.ap.apply(tf.clone(), t.clone());
    let atoms = eqv_atoms(env, s, &ta, &tr, &ker_t);
    let rc = rcompat(env, s, &ta, &tr, &tf);

    let into = |u: &Term, v: &Term| -> Option<Thm> {
        inst_all(pair_in_ker, &[ta.clone(), tf.clone(), u.clone(), v.clone()])
    };
    let outof = |u: &Term, v: &Term| -> Option<Thm> {
        inst_all(ker_pair, &[ta.clone(), tf.clone(), u.clone(), v.clone()])
    };
    let in_a = |t: &Term| Formula::mem(t.clone(), ta.clone());
    let in_ker =
        |u: &Term, v: &Term| Formula::mem(s.ap.sets.pair(u.clone(), v.clone()), ker_t.clone());

    // Both components of a member of `ker(A,f)` lie in `A`.
    let components = |env: &mut Env, u: &Term, v: &Term| -> Option<(Thm, Thm)> {
        let pair = s.ap.sets.pair(u.clone(), v.clone());
        let (mem_prod, cond, fwd, _) = k.parts(env, &ta, &tf, &pair)?;
        let to_prod = syl(&fwd, &and_left(mem_prod, cond))?;
        let pip = inst_all(&s.pair_in_prod, &[ta.clone(), ta.clone(), u.clone(), v.clone()])?;
        let both = syl(&to_prod, &iff_mp(&pip)?)?;
        Some((
            syl(&both, &and_left(in_a(u), in_a(v)))?,
            syl(&both, &and_right(in_a(u), in_a(v)))?,
        ))
    };

    // ── Reflexivity ──────────────────────────────────────────────────────────
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let refl_body = {
        let h = in_a(&tx);
        let eq = a1i(&Thm::eq_refl(app(&tx)), h.clone());
        let triple = hyp_and(&imp_refl(h.clone()), &hyp_and(&imp_refl(h), &eq)?)?;
        syl(&triple, &into(&tx, &tx)?)?
    };
    let refl = Thm::gen(xv, &refl_body);
    if *refl.concl() != atoms[0] {
        return None
    }

    // ── Symmetry ─────────────────────────────────────────────────────────────
    let (uv, vv) = (env.fresh_var(), env.fresh_var());
    let (tu, tv) = (Term::var(uv), Term::var(vv));
    let sym_body = {
        let h = in_ker(&tu, &tv);
        let (m_u, m_v) = components(env, &tu, &tv)?;
        let eq = syl(&outof(&tu, &tv)?, &eq_symm_imp(env, app(&tu), app(&tv)))?;
        let triple = hyp_and(&m_v, &hyp_and(&m_u, &eq)?)?;
        let out = syl(&triple, &into(&tv, &tu)?)?;
        if out.concl().as_imp()?.0 != h {
            return None
        }
        out
    };
    let sym = Thm::gen(uv, &Thm::gen(vv, &sym_body));
    if *sym.concl() != atoms[1] {
        return None
    }

    // ── Transitivity ─────────────────────────────────────────────────────────
    let (av2, bv2, cv2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t1, t2, t3) = (Term::var(av2), Term::var(bv2), Term::var(cv2));
    let trans_body = {
        let (l, r) = (in_ker(&t1, &t2), in_ker(&t2, &t3));
        let h = Formula::and(l.clone(), r.clone());
        let hl = and_left(l.clone(), r.clone());
        let hr = and_right(l, r);
        let (m_1, _) = components(env, &t1, &t2)?;
        let (_, m_3) = components(env, &t2, &t3)?;
        let g_1 = syl(&hl, &m_1)?;
        let g_3 = syl(&hr, &m_3)?;
        let e12 = syl(&hl, &outof(&t1, &t2)?)?;
        let e23 = syl(&hr, &outof(&t2, &t3)?)?;
        let chain = eq_chain(env, app(&t1), app(&t2), app(&t3));
        let e13 = hyp_mp(&syl(&e23, &chain)?, &e12)?;
        let triple = hyp_and(&g_1, &hyp_and(&g_3, &e13)?)?;
        let out = syl(&triple, &into(&t1, &t3)?)?;
        if out.concl().as_imp()?.0 != h {
            return None
        }
        out
    };
    let trans = Thm::gen(av2, &Thm::gen(bv2, &Thm::gen(cv2, &trans_body)));
    if *trans.concl() != atoms[2] {
        return None
    }

    // ── Contains `R|A` — the one clause that needs the hypothesis ────────────
    let (pv, qv) = (env.fresh_var(), env.fresh_var());
    let (tp, tq) = (Term::var(pv), Term::var(qv));
    let contains = {
        let in_r = Formula::mem(s.ap.sets.pair(tp.clone(), tq.clone()), tr.clone());
        let tail = Formula::and(in_a(&tq), in_r.clone());
        let h = Formula::and(in_a(&tp), tail.clone());
        let hl = and_left(rc.clone(), h.clone());
        let hr = and_right(rc.clone(), h.clone());
        let eq = hyp_mp(&syl(&hl, &inst_formula(&rc, &[tp.clone(), tq.clone()])?)?, &hr)?;
        let g_p = syl(&hr, &and_left(in_a(&tp), tail.clone()))?;
        let g_q = syl(
            &syl(&hr, &and_right(in_a(&tp), tail))?,
            &and_left(in_a(&tq), in_r),
        )?;
        let triple = hyp_and(&g_p, &hyp_and(&g_q, &eq)?)?;
        let mut out = uncurry(&syl(&triple, &into(&tp, &tq)?)?)?;
        for v in [qv, pv] {
            out = hyp_gen(v, &out)?;
        }
        out
    };
    if contains.concl().as_imp()?.1 != atoms[3] {
        return None
    }

    // Assemble: three unconditional clauses plus the conditional fourth.
    let out = hyp_and(
        &a1i(&refl, rc.clone()),
        &hyp_and(&a1i(&sym, rc.clone()), &hyp_and(&a1i(&trans, rc.clone()), &contains)?)?,
    )?;
    debug_assert_eq!(*out.concl(), Formula::imp(rc, conj_of(&atoms)?), "ker_closed: shape");
    Some(gen_all(&[av, rv, fv], &out))
}

/// `⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → compat(A,R,f))` — **compatibility with `R`
/// implies compatibility with `∼`**.
///
/// [`super::eqv::eqv_induction`] at `E := ker(A,f)`: the guard is
/// [`ker_subset`] and [`ker_closed`], the conclusion is `∼ ⊆ ker(A,f)`, and
/// [`ker_pair`] reads the equation back out. This is the lemma that lets a
/// caller hand [`super::lift`] Lean's own `Quot.lift` hypothesis.
pub fn compat_closure(
    env: &mut Env,
    k: &Ker<'_>,
    eqv: FnSym,
    eqv_induction: &Thm,
    thms: &(Thm, Thm, Thm),
) -> Option<Thm> {
    let (ker_sub, ker_pair, ker_closed) = thms;
    let s = k.s;
    let (av, rv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tf) = (Term::var(av), Term::var(rv), Term::var(fv));
    let ker_t = k.of(&ta, &tf);
    let rc = rcompat(env, s, &ta, &tr, &tf);

    // The guard of the induction principle, under `rcompat`.
    let sub = inst_all(ker_sub, &[ta.clone(), tf.clone()])?;
    let closed = inst_all(ker_closed, &[ta.clone(), tr.clone(), tf.clone()])?;
    let guard = hyp_and(&a1i(&sub, rc.clone()), &closed)?;
    debug_assert_eq!(
        *guard.concl(),
        Formula::imp(rc.clone(), eqv_guard(env, s, &ta, &tr, &ker_t)),
        "compat_closure: guard shape"
    );

    let ind = inst_all(eqv_induction, &[ta.clone(), tr.clone(), ker_t.clone()])?;
    let included = syl(&guard, &ind)?;

    // Instantiate the inclusion at `⟨x,y⟩` and read the equation out.
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let pair = s.ap.sets.pair(tx.clone(), ty.clone());
    let (_, body) = included.concl().as_imp()?;
    let at = Thm::ax_inst(body, pair.clone())?;
    let out_pair = inst_all(ker_pair, &[ta.clone(), tf.clone(), tx.clone(), ty.clone()])?;
    let mut step = syl(&included, &syl(&at, &crate::imp_mono_r(&out_pair, Formula::mem(pair, Term::apply(eqv, vec![ta.clone(), tr.clone()])))?)?)?;
    for v in [yv, xv] {
        step = hyp_gen(v, &step)?;
    }
    if step.concl().as_imp()?.1 != compat(env, s, eqv, &ta, &tr, &tf) {
        return None
    }
    Some(gen_all(&[av, rv, fv], &step))
}
