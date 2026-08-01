//! The **two-point function** `{⟨a,b⟩, ⟨c,d⟩}`: the graph that relates `a` to
//! `b`, `c` to `d`, and nothing else.
//!
//! # Interface
//!
//! Writing `tp(a,b,c,d)` for the unordered pair `{⟨a,b⟩, ⟨c,d⟩}`:
//!
//! ```text
//! ⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app(tp(a,b,c,d), a) = b)          [TwoPoint::left]
//! ⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app(tp(a,b,c,d), c) = d)         [TwoPoint::right]
//! ```
//!
//! The antecedent is the *only* hypothesis, and it is not removable: with
//! `a = c` the graph relates one point to two values and `app` cannot pick.
//! Nothing here needs `b ≠ d`, nor any typing of the values, which is what
//! makes the pair usable as a step function whose values are arbitrary sets.
//!
//! # Why it is wanted
//!
//! `INDUCTIVES.md`'s translation gives the W-recursor **one** packed step `e`,
//! applied to the triple `⟨a, ⟨f, r⟩⟩`, whereas Lean's recursor takes one minor
//! premise per constructor. For a two-constructor enumeration the fibres are
//! empty, so `f` and `r` are both `∅` and the triple takes exactly two values —
//! one per constructor tag. The step is therefore a graph on two points, and
//! [`crate::wbool_rec`] builds it as `tp` at those two triples.
//!
//! `crate::point_fun` is the one-point analogue and is not enough here: a union
//! of two one-point graphs needs the same disjointness argument this file makes
//! anyway, and then needs single-valuedness of the union on top of it.
//!
//! # How it computes, and why single-valuedness is not needed
//!
//! [`crate::point_fun::point_app`] goes through `app_of_pair`, which wants
//! `sv(f)` — a four-case analysis for a two-point graph. This file goes the
//! shorter way, the one [`crate::funcs::beta_conditional`] takes: show
//!
//! ```text
//! coll(tp, a) = { y : ⟨a,y⟩ ∈ tp } = {b}
//! ```
//!
//! by Extensionality and read `app(tp,a) = ⋃{b} = b` off it. The forward
//! inclusion is where `¬(a = c)` is used, and it is used once: a member
//! `⟨a,y⟩` of the pair is either `⟨a,b⟩`, giving `y = b`, or `⟨c,d⟩`, giving
//! `a = c` and hence anything at all.
//!
//! # Non-vacuity
//!
//! Both exports are *equations* whose two sides are visibly different terms at
//! fresh constants, and their shared antecedent is satisfiable — `tests/twopoint.rs`
//! discharges it at `a := ∅`, `c := {∅}` and reads off `app(tp(∅,b,{∅},d), ∅) = b`
//! with no hypothesis left.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funcs::hyp_syl;
use crate::{
    a1i, and_left, and_right, contrapos, eq_symm_imp, ex_falso, gen_all, hyp_and, hyp_mp,
    hyp_or_elim, iff_mp, iff_mpr, inst_all, singleton, syl, upair_members,
};

/// The two equations, at fresh universally quantified variables.
pub struct TwoPoint {
    /// `⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app({⟨a,b⟩,⟨c,d⟩}, a) = b)`.
    pub left: Thm,
    /// `⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app({⟨a,b⟩,⟨c,d⟩}, c) = d)`.
    pub right: Thm,
}

impl TwoPoint {
    /// Derive both, over a caller-supplied [`Apply`] — so that the pairing and
    /// the application are the *same* symbols everything else is stated over.
    pub fn over(env: &mut Env, ap: &Apply) -> Option<TwoPoint> {
        let left = two_point_app(env, ap, false)?;
        let right = two_point_app(env, ap, true)?;
        Some(TwoPoint { left, right })
    }

    /// The term `{⟨a,b⟩, ⟨c,d⟩}`.
    pub fn of(ap: &Apply, a: Term, b: Term, c: Term, d: Term) -> Term {
        Term::apply(ap.sets.up, vec![ap.sets.pair(a, b), ap.sets.pair(c, d)])
    }
}

/// `⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app({⟨a,b⟩,⟨c,d⟩}, p) = v)`, where `(p,v)` is
/// `(a,b)` when `second` is false and `(c,d)` when it is true.
///
/// One derivation, twice: the two cases differ only in which disjunct of the
/// pair's membership condition is the informative one and which is refuted by
/// the antecedent.
fn two_point_app(env: &mut Env, ap: &Apply, second: bool) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (av, bv, cv, dv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(av), Term::var(bv), Term::var(cv), Term::var(dv));

    let pab = ap.sets.pair(ta.clone(), tb.clone());
    let pcd = ap.sets.pair(tc.clone(), td.clone());
    let g = Term::apply(ap.sets.up, vec![pab.clone(), pcd.clone()]);

    let (pt, val) = if second { (tc.clone(), td.clone()) } else { (ta.clone(), tb.clone()) };
    let h = Formula::not(Formula::eq(ta.clone(), tc.clone())); // H := ¬(a = c)

    // ── `⟨p,v⟩ ∈ tp`, unconditionally ────────────────────────────────────────
    let (fst_mem, snd_mem) = upair_members(&ap.sets.up_ax, &pab, &pcd)?;
    let pt_in_g = if second { snd_mem } else { fst_mem };

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let pay = ap.sets.pair(pt.clone(), ty.clone());
    let mem_pay = Formula::mem(pay.clone(), g.clone());
    let goal = Formula::eq(ty.clone(), val.clone());

    // ── Forward: `(H ∧ ⟨p,y⟩ ∈ tp) → y = v` ─────────────────────────────────
    //
    // The pair's membership condition splits into two disjuncts. Exactly one is
    // informative — the pair is injective, so it hands back `y = v` — and the
    // other says `p` is the *other* point, which `H` refutes.
    let n = Formula::and(h.clone(), mem_pay.clone());
    let up_at = inst_all(&ap.sets.up_ax, &[pab.clone(), pcd.clone(), pay.clone()])?;
    let n_disj = syl(&and_right(h.clone(), mem_pay.clone()), &iff_mp(&up_at)?)?;

    // `⟨p,y⟩ = ⟨x,w⟩ → (p = x ∧ y = w)`, split into its two halves.
    let split = |x: &Term, w: &Term| -> Option<(Thm, Thm)> {
        let inj = inst_all(&ap.pair_inj, &[pt.clone(), ty.clone(), x.clone(), w.clone()])?;
        let (l, r) = (Formula::eq(pt.clone(), x.clone()), Formula::eq(ty.clone(), w.clone()));
        Some((syl(&inj, &and_left(l.clone(), r.clone()))?, syl(&inj, &and_right(l, r))?))
    };
    let (l_pt, l_val) = split(&ta, &tb)?;
    let (r_pt, r_val) = split(&tc, &td)?;

    // `⊢ H → ¬(p = q)` for the other point `q`: reflexivity when `p` is `a`,
    // symmetry of equality when it is `c`.
    let h_ne = if second {
        contrapos(&eq_symm_imp(env, tc.clone(), ta.clone()))?
    } else {
        crate::imp_refl(h.clone())
    };

    // The refuted case, as `⊢ N → (disjunct → y = v)`.
    let refuted = |bad_pt: &Thm| -> Option<Thm> {
        let n_ne = syl(&and_left(h.clone(), mem_pay.clone()), &h_ne)?; // N → ¬(p = q)
        let n_bad = a1i(bad_pt, n.clone()); // N → (disjunct → p = q)
        let n_false = hyp_syl(&n_bad, &n_ne)?; // N → (disjunct → ⊥)
        hyp_syl(&n_false, &a1i(&ex_falso(goal.clone()), n.clone()))
    };

    let (case_l, case_r) = if second {
        (refuted(&l_pt)?, a1i(&r_val, n.clone()))
    } else {
        (a1i(&l_val, n.clone()), refuted(&r_pt)?)
    };

    let n_val = hyp_or_elim(&n_disj, &case_l, &case_r)?;
    let fwd = crate::uncurry(&n_val)?; // H → (⟨p,y⟩ ∈ tp → y = v)

    // ── Backward: `H → (y = v → ⟨p,y⟩ ∈ tp)` ────────────────────────────────
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val.clone(),
        ty.clone(),
        w,
        Formula::mem(ap.sets.pair(pt.clone(), Term::var(w)), g.clone()),
    );
    let bwd_raw = hyp_mp(&carry, &a1i(&pt_in_g, Formula::eq(val.clone(), ty.clone())))?;
    let bwd = a1i(&syl(&eq_symm_imp(env, ty.clone(), val.clone()), &bwd_raw)?, h.clone());

    // ── `coll(tp, p)` and `{v}` have the same members ───────────────────────
    let sing = singleton(ap.sets.up, val.clone());
    let ms = inst_all(&ap.mem_sing, &[val.clone(), ty.clone()])?;
    let coll_term = ap.coll_of(g.clone(), pt.clone());
    let coll_at = inst_all(&ap.coll_members, &[g.clone(), pt.clone(), ty.clone()])?;
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let mem_ys = Formula::mem(ty.clone(), sing.clone());

    let h_c_sing = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&coll_at)?, h.clone()), &fwd)?,
        &a1i(&iff_mpr(&ms)?, h.clone()),
    )?;
    let h_sing_c = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&ms)?, h.clone()), &bwd)?,
        &a1i(&iff_mpr(&coll_at)?, h.clone()),
    )?;
    let h_same = Thm::mp(
        &Thm::ax_dist(yv, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(yv, &hyp_and(&h_c_sing, &h_sing_c)?),
    )?;
    let h_coll_eq = syl(&h_same, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    // ── `app(tp,p) = ⋃coll = ⋃{v} = v` ──────────────────────────────────────
    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w4 = env.fresh_var();
    let congr_u = crate::mpd_const(
        &Thm::eq_leibniz(coll_term, sing, w4, Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w4)))),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_term = ap.apply(g.clone(), pt.clone());
    let app_def = inst_all(&ap.app_ax, &[g.clone(), pt.clone()])?;
    let w5 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(ucoll, using.clone(), w5, Formula::eq(app_term.clone(), Term::var(w5)));
    let h_app_using = hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w6 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, val.clone(), w6, Formula::eq(app_term.clone(), Term::var(w6))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&val))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    if *out.concl() != Formula::imp(h, Formula::eq(app_term, val)) {
        return None
    }
    Some(gen_all(&[av, bv, cv, dv], &out))
}
