//! **The theorem** — a W-type over an arbitrary fibre family is a *member* of a
//! universe.
//!
//! # Interface
//!
//! Writing `W` for `W(A,B,u)`, `code(x,w)` for
//! `w ∈ W ∧ ∀q. (q ∈ x ↔ ⟨w,q⟩ ∈ paths(A,B,u,Q))` and `Uₙ` for `U(d)`:
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀Q ∀d. ( ((closed(A,B,u) ∧ amb(A,B,Q))
//!                      ∧ ((W ⊆ U(d) ∧ Q ∈ U(d)) ∧ A ∈ U(d)))
//!                        → W ∈ U(d) )                  [w_in_universe_paths]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # What the antecedent asks, and what it does **not**
//!
//! | clause | discharged by |
//! |---|---|
//! | `closed(A,B,u)` | [`crate::bound::least_universe_closed`] at `u := U(c)` — **no fibre condition** |
//! | [`super::amb`] | three facts about `Q`; at `Q := tower(S)` they are [`crate::cumul`]'s |
//! | `W ⊆ U(d)` | `W ⊆ u` is free, and `u := U(c) ⊆ U(d)` by leastness when `c ∈ U(d)` |
//! | `Q ∈ U(d)` | `crate::cumul::Inside::tower_mem` |
//! | `A ∈ U(d)` | `crate::cumul::tags` — the one antecedent `DeclUniverse` already carries |
//!
//! **There is no condition on the fibres anywhere in this list.** That is the
//! whole point: [`crate::cumul::bnd`] is gone, not weakened, and with it the
//! restriction to finitely branching declarations.
//!
//! # The argument
//!
//! [`crate::cantor::image_in_universe`] — regularity — takes a member `I` of a
//! universe, a subset `S` of it, and a single-valued relation from `I` onto `S`,
//! and concludes `S ∈ u`. Here
//!
//! ```text
//! I := 𝒫(prod(Q,A))                       a member, by pairing and power set
//! S := W                                   a subset, by hypothesis
//! R(x,w) := w ∈ W ∧ ∀q. (q ∈ x ↔ ⟨w,q⟩ ∈ paths)
//! ```
//!
//! and the three clauses are:
//!
//! * **DOM** — `x` is exactly the set of `w`'s labelled paths, and those live in
//!   `prod(Q,A)` by [`super::paths_subset`], so `x ⊆ prod(Q,A)`;
//! * **SV** — two trees with the same code have the same paths, hence
//!   [`super::paths_injective`] applies. The injectivity theorem asks only for
//!   the *inclusion*, which is one half of the biconditional `R` carries;
//! * **ONTO** — the code of a tree exists, by **one Separation** on
//!   `prod(Q,A)`. Nothing is recursed over and nothing is chosen: the code is
//!   `{q ∈ prod(Q,A) : ⟨w,q⟩ ∈ paths}` and the guard is redundant, again by
//!   [`super::paths_subset`].
//!
//! `R` is passed to [`crate::cantor::image_in_universe`] as a **formula**, so no
//! function set is ever built and the relation costs nothing.
//!
//! # Why this is not the thesis's proof, and why that is allowed
//!
//! Carneiro's §6.2.1 bounds `W` by `V_λ` for a regular `λ` above the fibre
//! sizes, which needs ordinals, ranks and transfinite recursion — a development
//! this crate does not have and would be a second `crate::recursion` in size.
//! The move made here is the one [`crate::wrec`] already made at the recursor,
//! and its header records the same reasoning: *"the union-of-attempts
//! construction lands in the same place and needs only W2"*. Here the
//! least-closed-set construction lands in the same place and needs only
//! regularity, which [`crate::cantor`] already proves.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::cantor::{image_in_universe, r_dom, r_onto, r_sv};
use crate::funcs::separation_full;
use crate::funspace::discharge;
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, syl, uncurry,
};

use super::condition::At;
use super::injective::sub_paths;
use super::shared::{gen_under, hyp_inst, hyp_inst_mp};

/// `w ∈ W ∧ ∀q. (q ∈ x ↔ ⟨w,q⟩ ∈ paths)` — "`x` is the code of the tree `w`".
///
/// Exported because it is the relation [`w_in_universe_paths`] hands to
/// [`crate::cantor::image_in_universe`], and a caller checking that theorem's
/// hypotheses has to build the same formula.
pub fn is_code(env: &mut Env, s: &Sums, at: &At, ps: &Term, x: &Term, w: &Term) -> Formula {
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    Formula::and(
        Formula::mem(w.clone(), at.w.clone()),
        Formula::forall(
            qv,
            Formula::iff(
                Formula::mem(tq.clone(), x.clone()),
                Formula::mem(at.pair(s, w.clone(), tq), ps.clone()),
            ),
        ),
    )
}

/// `⊢ K → q ∈ prod(Q,A)` from `⊢ K → ⟨w,q⟩ ∈ paths`.
fn entry_in_qa(
    s: &Sums,
    at: &At,
    paths_sub: &Thm,
    w: &Term,
    q: &Term,
    k_in: &Thm,
) -> Option<Thm> {
    let qa = s.prod.of(at.q.clone(), at.a.clone());
    let bnd = syl(
        k_in,
        &inst_all(
            paths_sub,
            &[
                at.a.clone(),
                at.b.clone(),
                at.u.clone(),
                at.q.clone(),
                at.pair(s, w.clone(), q.clone()),
            ],
        )?,
    )?;
    let split = inst_all(&s.pair_in_prod, &[at.w.clone(), qa.clone(), w.clone(), q.clone()])?;
    syl(
        &syl(&bnd, &iff_mp(&split)?)?,
        &and_right(Formula::mem(w.clone(), at.w.clone()), Formula::mem(q.clone(), qa)),
    )
}

/// **`⊢ W(A,B,u) ∈ U(d)`** under the five clauses in the module header.
///
/// `paths_sub` must be [`super::paths_subset`] and `injective`
/// [`super::paths_injective`], both over `paths`. `lu` is the least-universe
/// symbol, `is_universe_all` must be `⊢ ∀x. is_universe(U(x))`
/// ([`crate::universe::least_universe_is_universe`]), and `product` and `power`
/// the two closure clauses at `U(·)` (`crate::tower::Tower`'s `product` and
/// `pow`). All are required hypothesis-free and are used at pinned conclusions.
#[allow(clippy::too_many_arguments)]
pub fn w_in_universe_paths(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    paths_sub: &Thm,
    injective: &Thm,
    lu: FnSym,
    is_universe_all: &Thm,
    product: &Thm,
    power: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[paths_sub, injective, is_universe_all, product, power]) {
        return None
    }
    let s = wt.sums.clone();
    let (av, bv, uv, qv, dv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let ps = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);
    let ud = Term::apply(lu, vec![Term::var(dv)]);
    let qa = s.prod.of(at.q.clone(), at.a.clone());
    let i = Term::apply(s.pow, vec![qa.clone()]);

    // ── the antecedent ──────────────────────────────────────────────────────
    let closed = wt.closed_at(env, &at.a, &at.b, &at.u);
    let ambient = super::intro::amb(env, &s, &at);
    let core = Formula::and(closed, ambient);
    let sub_w = kernel::thm::subset(env, at.w.clone(), ud.clone());
    let size = Formula::and(
        Formula::and(sub_w.clone(), Formula::mem(at.q.clone(), ud.clone())),
        Formula::mem(at.a.clone(), ud.clone()),
    );
    let h = Formula::and(core.clone(), size.clone());
    let h_core = and_left(core.clone(), size.clone());
    let h_size = and_right(core, size.clone());
    let (left, h_a_mem) = {
        let (l, r) = (
            Formula::and(sub_w.clone(), Formula::mem(at.q.clone(), ud.clone())),
            Formula::mem(at.a.clone(), ud.clone()),
        );
        (
            syl(&h_size, &and_left(l.clone(), r.clone()))?,
            syl(&h_size, &and_right(l, r))?,
        )
    };
    let h_sub_w = syl(&left, &and_left(sub_w.clone(), Formula::mem(at.q.clone(), ud.clone())))?;
    let h_q_mem = syl(&left, &and_right(sub_w.clone(), Formula::mem(at.q.clone(), ud.clone())))?;

    // ── `I = 𝒫(Q × A)` is a member ──────────────────────────────────────────
    let h_i = {
        let prod_at = inst_all(product, &[Term::var(dv), at.q.clone(), at.a.clone()])?;
        let in_prod = hyp_mp(&a1i(&prod_at, h.clone()), &hyp_and(&h_q_mem, &h_a_mem)?)?;
        let pow_at = inst_all(power, &[Term::var(dv), qa.clone()])?;
        hyp_mp(&a1i(&pow_at, h.clone()), &in_prod)?
    };

    // ── the relation, and its three clauses ─────────────────────────────────
    let (xv, wv) = (env.fresh_var(), env.fresh_var());
    let (tx, tw) = (Term::var(xv), Term::var(wv));
    let r = is_code(env, &s, &at, &ps, &tx, &tw);

    let h_dom = dom_clause(env, &s, &at, &ps, paths_sub, &h, &r, xv, wv, &i)?;
    let h_sv = sv_clause(env, &s, &at, &ps, injective, &h, &h_core, &r, xv, wv)?;
    let h_onto = onto_clause(env, &s, &at, &ps, paths_sub, &h, &r, xv, wv)?;

    // ── regularity ──────────────────────────────────────────────────────────
    let iiu = image_in_universe(env, &s.ap.empty_ax, &ud, &i, &at.w, xv, wv, &r).ok()?;
    let h_univ = a1i(&inst_all(is_universe_all, &[Term::var(dv)])?, h.clone());
    let out = hyp_mp(
        &a1i(&iiu, h.clone()),
        &hyp_and(
            &hyp_and(&h_univ, &hyp_and(&h_i, &h_sub_w)?)?,
            &hyp_and(&h_dom, &hyp_and(&h_sv, &h_onto)?)?,
        )?,
    )?;
    if *out.concl() != Formula::imp(h, Formula::mem(at.w.clone(), ud)) {
        return None
    }
    Some(gen_all(&[av, bv, uv, qv, dv], &out))
}

/// `⊢ H → ∀x ∀w. (R(x,w) → x ∈ 𝒫(Q × A))`.
#[allow(clippy::too_many_arguments)]
fn dom_clause(
    env: &mut Env,
    s: &Sums,
    at: &At,
    ps: &Term,
    paths_sub: &Thm,
    h: &Formula,
    r: &Formula,
    xv: FreeVar,
    wv: FreeVar,
    i: &Term,
) -> Option<Thm> {
    let (tx, tw) = (Term::var(xv), Term::var(wv));
    let k = Formula::and(h.clone(), r.clone());
    let k_r = and_right(h.clone(), r.clone());
    let (mem_w, iff_all) = split_and(r)?;
    let k_iff = syl(&k_r, &and_right(mem_w, iff_all))?;

    // `x ⊆ prod(Q,A)`, one member at a time.
    let qv2 = env.fresh_var();
    let tq = Term::var(qv2);
    let qa = s.prod.of(at.q.clone(), at.a.clone());
    let mem_qx = Formula::mem(tq.clone(), tx.clone());
    let l_k = and_left(k.clone(), mem_qx.clone());
    let l_q = and_right(k.clone(), mem_qx.clone());
    let in_paths = Formula::mem(at.pair(s, tw.clone(), tq.clone()), ps.clone());
    let l_in_paths = {
        let at_q = hyp_inst(&syl(&l_k, &k_iff)?, &tq)?;
        let fwd = syl(
            &at_q,
            &and_left(
                Formula::imp(mem_qx.clone(), in_paths.clone()),
                Formula::imp(in_paths.clone(), mem_qx.clone()),
            ),
        )?;
        hyp_mp(&fwd, &l_q)?
    };
    let l_in_qa = entry_in_qa(s, at, paths_sub, &tw, &tq, &l_in_paths)?;
    let sub_body = Formula::imp(mem_qx, Formula::mem(tq.clone(), qa.clone()));
    let k_sub = gen_under(qv2, &k, &sub_body, &uncurry(&l_in_qa)?)?;
    if *k_sub.concl() != Formula::imp(k.clone(), kernel::thm::subset(env, tx.clone(), qa.clone()))
    {
        return None
    }

    let pow_at = inst_all(&s.pow_ax, &[qa, tx.clone()])?;
    let k_i = syl(&k_sub, &iff_mpr(&pow_at)?)?;
    if *k_i.concl() != Formula::imp(k, Formula::mem(tx.clone(), i.clone())) {
        return None
    }
    let body_w = Formula::imp(r.clone(), Formula::mem(tx.clone(), i.clone()));
    let g_w = gen_under(wv, h, &body_w, &uncurry(&k_i)?)?;
    let (_, inner) = g_w.concl().as_imp()?;
    let out = gen_under(xv, h, &inner, &g_w)?;
    (*out.concl() == Formula::imp(h.clone(), r_dom(r, xv, wv, i))).then_some(out)
}

/// `⊢ H → ∀x ∀w ∀w′. ((R(x,w) ∧ R(x,w′)) → w = w′)`.
#[allow(clippy::too_many_arguments)]
fn sv_clause(
    env: &mut Env,
    s: &Sums,
    at: &At,
    ps: &Term,
    injective: &Thm,
    h: &Formula,
    h_core: &Thm,
    r: &Formula,
    xv: FreeVar,
    wv: FreeVar,
) -> Option<Thm> {
    let cv = env.fresh_var();
    let (tx, tw, tc) = (Term::var(xv), Term::var(wv), Term::var(cv));
    let r2 = r.subst(wv, &tc);
    let both = Formula::and(r.clone(), r2.clone());
    let k = Formula::and(h.clone(), both.clone());
    let k_both = and_right(h.clone(), both.clone());
    let k_r = syl(&k_both, &and_left(r.clone(), r2.clone()))?;
    let k_r2 = syl(&k_both, &and_right(r.clone(), r2.clone()))?;
    let (mem_w, iff1) = split_and(r)?;
    let (mem_c, iff2) = split_and(&r2)?;
    let k_w = syl(&k_r, &and_left(mem_w.clone(), iff1.clone()))?;
    let k_iff1 = syl(&k_r, &and_right(mem_w, iff1))?;
    let k_c = syl(&k_r2, &and_left(mem_c.clone(), iff2.clone()))?;
    let k_iff2 = syl(&k_r2, &and_right(mem_c, iff2))?;

    // `sub_paths(w,w′)`: through `x`, one entry at a time.
    let qv2 = env.fresh_var();
    let tq = Term::var(qv2);
    let in1 = Formula::mem(at.pair(s, tw.clone(), tq.clone()), ps.clone());
    let in2 = Formula::mem(at.pair(s, tc.clone(), tq.clone()), ps.clone());
    let mem_qx = Formula::mem(tq.clone(), tx.clone());
    let k_step = {
        let a1 = syl(
            &hyp_inst(&k_iff1, &tq)?,
            &and_right(
                Formula::imp(mem_qx.clone(), in1.clone()),
                Formula::imp(in1.clone(), mem_qx.clone()),
            ),
        )?;
        let a2 = syl(
            &hyp_inst(&k_iff2, &tq)?,
            &and_left(
                Formula::imp(mem_qx.clone(), in2.clone()),
                Formula::imp(in2.clone(), mem_qx.clone()),
            ),
        )?;
        crate::separation::hyp_syl(&a1, &a2)?
    };
    let k_sub = gen_under(qv2, &k, &Formula::imp(in1, in2), &k_step)?;
    if *k_sub.concl() != Formula::imp(k.clone(), sub_paths(env, s, at, ps, &tw, &tc)) {
        return None
    }

    let inj_at = inst_all(
        injective,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()],
    )?;
    let k_core = syl(&and_left(h.clone(), both.clone()), h_core)?;
    let k_eq = hyp_mp(
        &hyp_inst_mp(&hyp_inst_mp(&syl(&k_core, &inj_at)?, &tw, &k_w)?, &tc, &k_c)?,
        &k_sub,
    )?;
    if *k_eq.concl() != Formula::imp(k, Formula::eq(tw.clone(), tc.clone())) {
        return None
    }
    let mut cur = uncurry(&k_eq)?;
    for v in [cv, wv, xv] {
        let (_, body) = cur.concl().as_imp()?;
        cur = gen_under(v, h, &body, &cur)?;
    }
    (*cur.concl() == Formula::imp(h.clone(), r_sv(r, xv, wv, cv).ok()?)).then_some(cur)
}

/// `⊢ H → ∀w. (w ∈ W → ∃x. R(x,w))` — the code exists, by one Separation.
#[allow(clippy::too_many_arguments)]
fn onto_clause(
    env: &mut Env,
    s: &Sums,
    at: &At,
    ps: &Term,
    paths_sub: &Thm,
    h: &Formula,
    r: &Formula,
    xv: FreeVar,
    wv: FreeVar,
) -> Option<Thm> {
    let tw = Term::var(wv);
    let mem_w = Formula::mem(tw.clone(), at.w.clone());
    let k = Formula::and(h.clone(), mem_w.clone());
    let k_w = and_right(h.clone(), mem_w.clone());

    let qa = s.prod.of(at.q.clone(), at.a.clone());
    let qv2 = env.fresh_var();
    let tq = Term::var(qv2);
    let in_paths = Formula::mem(at.pair(s, tw.clone(), tq.clone()), ps.clone());
    let sep = separation_full(env, qv2, &in_paths, &qa, &s.ap.empty_ax).ok()?;

    let sv2 = env.fresh_var();
    let ts = Term::var(sv2);
    let sep_body = |t: &Term| {
        Formula::forall(
            qv2,
            Formula::iff(
                Formula::mem(tq.clone(), t.clone()),
                Formula::and(Formula::mem(tq.clone(), qa.clone()), in_paths.clone()),
            ),
        )
    };
    if Formula::exists(sv2, sep_body(&ts)) != *sep.concl() {
        return None
    }

    let l = Formula::and(k.clone(), sep_body(&ts));
    let l_sep = and_right(k.clone(), sep_body(&ts));
    let l_k = and_left(k.clone(), sep_body(&ts));

    let mem_qs = Formula::mem(tq.clone(), ts.clone());
    let carved = Formula::and(Formula::mem(tq.clone(), qa.clone()), in_paths.clone());
    let l_at_q = hyp_inst(&l_sep, &tq)?;
    let fwd = syl(
        &syl(
            &l_at_q,
            &and_left(
                Formula::imp(mem_qs.clone(), carved.clone()),
                Formula::imp(carved.clone(), mem_qs.clone()),
            ),
        )?,
        &crate::imp_mono_r(
            &and_right(Formula::mem(tq.clone(), qa.clone()), in_paths.clone()),
            mem_qs.clone(),
        )?,
    )?;
    let bwd = {
        // `⟨w,q⟩ ∈ paths` already puts `q` in `prod(Q,A)`, so the guard is free.
        let m_l = and_left(l.clone(), in_paths.clone());
        let m_in = and_right(l.clone(), in_paths.clone());
        let m_qa = entry_in_qa(s, at, paths_sub, &tw, &tq, &m_in)?;
        let m_carved = hyp_and(&m_qa, &m_in)?;
        let m_s = hyp_mp(
            &syl(
                &syl(&m_l, &l_at_q)?,
                &and_right(
                    Formula::imp(mem_qs.clone(), carved.clone()),
                    Formula::imp(carved.clone(), mem_qs.clone()),
                ),
            )?,
            &m_carved,
        )?;
        uncurry(&m_s)?
    };
    let l_iff = hyp_and(&fwd, &bwd)?;
    let l_all = gen_under(
        qv2,
        &l,
        &Formula::iff(mem_qs, in_paths.clone()),
        &l_iff,
    )?;
    let l_code = hyp_and(&syl(&l_k, &k_w)?, &l_all)?;
    if *l_code.concl() != Formula::imp(l.clone(), is_code(env, s, at, ps, &ts, &tw)) {
        return None
    }
    let l_ex = syl(&l_code, &exists_intro_imp(xv, r.clone(), ts.clone())?)?;
    let k_ex = discharge(sv2, &a1i(&sep, k.clone()), &l_ex)?;

    let body = Formula::imp(mem_w, Formula::exists(xv, r.clone()));
    let out = gen_under(wv, h, &body, &uncurry(&k_ex)?)?;
    (*out.concl() == Formula::imp(h.clone(), r_onto(r, xv, wv, &at.w))).then_some(out)
}

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, npsi) = inner.as_imp()?;
    let (psi, fls2) = npsi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}
