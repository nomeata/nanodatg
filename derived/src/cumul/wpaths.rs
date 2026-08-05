//! **The tower is a legal path ambient** — [`crate::wpath::amb`] at
//! `Q := tower(S)`, from the *cheap* half of `Fin⁺`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B. ((∀a. (a ∈ A → B(a) ⊆ S)) → amb(A, B, T))            [tower_amb]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why this is the whole of the bridge
//!
//! [`crate::wpath::w_in_universe_paths`] replaces
//! [`super::WMem::w_in_universe_bnd`], and the two antecedents differ in exactly
//! one place. `Fin⁺` is
//!
//! ```text
//! A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ bnd(B(a))))
//! ```
//!
//! and `bnd(B(a))` — a whole fibre-indexed family landing in one stage — is
//! **refutable** at an infinite fibre. What the path construction wants of the
//! same tower is [`crate::wpath::amb`]: `∅ ∈ T`, every fibre element in `T`, and
//! `T` closed under the Kuratowski pair. The middle clause is `B(a) ⊆ S` carried
//! into `V₀`; the other two are unconditional facts about the tower. **The
//! fibre's size appears nowhere.**
//!
//! So the tower does not go: it stops being the *catcher* — the sup-closed set
//! `W` is bounded by — and becomes the set the **paths** live in, where its
//! height was never in question. `Inside::tower_mem` still supplies `T ∈ Uₙ`,
//! and that membership is the one thing about the tower the new route uses.
//!
//! # Where each clause comes from
//!
//! | clause | proof |
//! |---|---|
//! | `∅ ∈ T` | `∅ ⊆ V₀`, so `∅ ∈ V₁` by [`super::Chain::sub_in_stage`], then `mem_tower` |
//! | `b ∈ B(a) → b ∈ T` | `B(a) ⊆ S = V₀` ([`Stages`]' base equation), then `mem_tower` at `0` |
//! | `⟨x,y⟩ ∈ T` | `x ∈ Vₙ`, `y ∈ V_m`, [`Stages::directed`] merges them into `Vₚ`, `pair_in_stage` lands the pair in `V₍succ² p₎` |
//!
//! The third is the only one that uses directedness, and it uses it at **two**
//! stages — the two-way merge `Stages::directed` proves by successor-chasing.
//! That is the same fact `tower_closed_bnd` needed; what it does *not* need is
//! the `B(a)`-indexed version, which is what `bnd` was.

use kernel::{Env, Formula, Term, Thm};

use crate::funspace::discharge;
use crate::recursion::Rec;
use crate::wpath::{amb, At};
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, ex_falso, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};


use super::chain::Chain;
use super::stages::Stages;

/// From `⊢ H → ∀x. φ` infer `⊢ H → φ[t/x]`.
fn hyp_inst(h_all: &Thm, t: &Term) -> Option<Thm> {
    let (_, all) = h_all.concl().as_imp()?;
    syl(h_all, &Thm::ax_inst(all, t.clone())?)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`.
fn gen_under(v: kernel::FreeVar, h: &Formula, body: &Formula, thm: &Thm) -> Option<Thm> {
    Thm::mp(&Thm::ax_dist(v, h.clone(), body.clone())?, &Thm::gen(v, thm))
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

/// **`⊢ ∀A ∀B. ((∀a. (a ∈ A → B(a) ⊆ S)) → amb(A,B,T))`.**
///
/// The hypothesis is the fibre half of [`super::fin_bnd`] with `bnd` deleted —
/// literally the clause that survives when the fibre condition goes. Everything
/// else the path construction asks of the tower is unconditional.
pub fn tower_amb(env: &mut Env, chain: &Chain) -> Option<Thm> {
    tower_amb_over(
        env,
        &chain.r,
        &chain.st,
        &chain.wt,
        &chain.mem_tower,
        &chain.sub_in_stage,
        &chain.pair_in_stage,
    )
}

/// [`tower_amb`] over the pieces rather than over an assembled [`Chain`].
///
/// [`super::Paths::new`] runs **inside** [`super::Chain::assemble`], before the
/// `Chain` exists, so it cannot pass one. The three theorems are
/// [`super::closure`]'s and are the same values the `Chain` would carry; they
/// are used at pinned conclusions below, so a mismatched trio is a `None`.
pub(super) fn tower_amb_over(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    wt: &Wtype,
    mem_tower: &Thm,
    sub_in_stage: &Thm,
    pair_in_stage: &Thm,
) -> Option<Thm> {
    let s = wt.sums.clone();
    let core = r.core().clone();
    let tower = st.tower_set();
    let seed = Term::var(st.seed);
    let zero = r.zero();
    let v0 = st.v(r, zero.clone());

    let (av, bv, uv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), tower.clone());

    // `0 ∈ ω` and `succ 0 ∈ ω`.
    let zero_om = core.zero_mem.clone();
    let succ = |t: Term| r.succ_of(t);
    let succ_om = |th: &Thm, t: &Term| -> Option<Thm> {
        Thm::mp(&inst_all(&core.succ_closed, std::slice::from_ref(t))?, th)
    };
    let one_om = succ_om(&zero_om, &zero)?;

    // `⊢ z ∈ Vₚ → z ∈ T` at a stage index known to be in `ω`.
    let into_tower = |p_om: &Thm, p: &Term, z: &Term| -> Option<Thm> {
        let at_p = Thm::mp(&inst_all(mem_tower, std::slice::from_ref(p))?, p_om)?;
        inst_all(&at_p, std::slice::from_ref(z))
    };

    // ── `∅ ∈ T` ─────────────────────────────────────────────────────────────
    let empty_in_tower = {
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let empty_sub = Thm::gen(
            zv,
            &syl(
                &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?,
                &ex_falso(Formula::mem(tz.clone(), v0.clone())),
            )?,
        );
        if *empty_sub.concl() != kernel::thm::subset(env, zero.clone(), v0.clone()) {
            return None
        }
        let sub_at = Thm::mp(
            &inst_all(sub_in_stage, std::slice::from_ref(&zero))?,
            &zero_om,
        )?;
        let in_v1 = Thm::mp(&inst_all(&sub_at, std::slice::from_ref(&zero))?, &empty_sub)?;
        Thm::mp(&into_tower(&one_om, &succ(zero.clone()), &zero)?, &in_v1)?
    };
    if *empty_in_tower.concl() != Formula::mem(zero.clone(), tower.clone()) {
        return None
    }

    // ── every fibre element is in `T` ───────────────────────────────────────
    let hyp = {
        let a1 = env.fresh_var();
        let ta1 = Term::var(a1);
        Formula::forall(
            a1,
            Formula::imp(
                Formula::mem(ta1.clone(), at.a.clone()),
                kernel::thm::subset(env, s.ap.apply(at.b.clone(), ta1), seed.clone()),
            ),
        )
    };
    let fibres = {
        let (a2, b2) = (env.fresh_var(), env.fresh_var());
        let (ta, tb) = (Term::var(a2), Term::var(b2));
        let fibre = s.ap.apply(at.b.clone(), ta.clone());
        let mem_a = Formula::mem(ta.clone(), at.a.clone());
        let mem_b = Formula::mem(tb.clone(), fibre.clone());
        let k1 = Formula::and(hyp.clone(), mem_a.clone());
        let k2_k1 = and_left(k1.clone(), mem_b.clone());
        let k2_b = and_right(k1.clone(), mem_b.clone());
        let k2_hyp = syl(&k2_k1, &and_left(hyp.clone(), mem_a.clone()))?;
        let k2_a = syl(&k2_k1, &and_right(hyp.clone(), mem_a.clone()))?;

        let k2_sub = hyp_mp(&hyp_inst(&k2_hyp, &ta)?, &k2_a)?;
        let k2_in_seed = hyp_mp(&hyp_inst(&k2_sub, &tb)?, &k2_b)?;
        // `S = V₀`, the recursion's base equation, turned round.
        let hole = env.fresh_var();
        let to_v0 = Thm::mp(
            &Thm::eq_leibniz(
                seed.clone(),
                v0.clone(),
                hole,
                Formula::mem(tb.clone(), Term::var(hole)),
            ),
            &crate::eq_symm(env, &st.rec.base)?,
        )?;
        let k2_in_v0 = syl(&k2_in_seed, &to_v0)?;
        let k2_in_t = syl(&k2_in_v0, &into_tower(&zero_om, &zero, &tb)?)?;

        let body_b = Formula::imp(mem_b, Formula::mem(tb.clone(), tower.clone()));
        let g_b = gen_under(b2, &k1, &body_b, &uncurry(&k2_in_t)?)?;
        let (_, inner) = g_b.concl().as_imp()?;
        gen_under(a2, &hyp, &Formula::imp(mem_a, inner), &uncurry(&g_b)?)?
    };

    // ── `T` is closed under the Kuratowski pair ─────────────────────────────
    let pairing = pair_closed(env, r, st, wt, pair_in_stage, mem_tower, &at)?;

    // ── the three clauses, in `amb`'s own shape ─────────────────────────────
    let target = amb(env, &s, &at);
    let (c_empty, rest) = split_and(&target)?;
    let (c_fib, c_pair) = split_and(&rest)?;
    if *empty_in_tower.concl() != c_empty
        || *fibres.concl() != Formula::imp(hyp.clone(), c_fib)
        || *pairing.concl() != c_pair
    {
        return None
    }
    let out = hyp_and(
        &a1i(&empty_in_tower, hyp.clone()),
        &hyp_and(&fibres, &a1i(&pairing, hyp.clone()))?,
    )?;
    if *out.concl() != Formula::imp(hyp, target) {
        return None
    }
    Some(gen_all(&[av, bv], &out))
}

/// `⊢ ∀x ∀y. ((x ∈ T ∧ y ∈ T) → ⟨x,y⟩ ∈ T)` — the tower is closed under pairing.
///
/// Two stages, merged by [`super::Stages::directed`], and then
/// [`super::Chain::pair_in_stage`]. **This is the only use of directedness in
/// the path route, and it is the two-way merge the tower already proves** — not
/// the fibre-indexed version, which is what `bnd` was and what is refutable.
fn pair_closed(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    wt: &Wtype,
    pair_in_stage: &Thm,
    mem_tower: &Thm,
    at: &At,
) -> Option<Thm> {
    let s = wt.sums.clone();
    let core = r.core().clone();
    let tower = st.tower_set();

    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let pair = at.pair(&s, tx.clone(), ty.clone());
    let goal = Formula::mem(pair.clone(), tower.clone());

    let mem_x = Formula::mem(tx.clone(), tower.clone());
    let mem_y = Formula::mem(ty.clone(), tower.clone());
    let k = Formula::and(mem_x.clone(), mem_y.clone());
    let k_x = and_left(mem_x.clone(), mem_y.clone());
    let k_y = and_right(mem_x, mem_y);

    // `z ∈ T` unfolds to `∃n. (n ∈ ω ∧ z ∈ Vₙ)`.
    let stage_of = |z: &Term| -> Option<Thm> {
        syl(
            &if *z == tx { k_x.clone() } else { k_y.clone() },
            &iff_mp(&inst_all(&st.tower.members, std::slice::from_ref(z))?)?,
        )
    };
    let matrix = |z: &Term, n: &Term| {
        Formula::and(
            Formula::mem(n.clone(), r.omega()),
            Formula::mem(z.clone(), st.v(r, n.clone())),
        )
    };

    let (nv, mv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tn, tm, tp) = (Term::var(nv), Term::var(mv), Term::var(pv));
    if Formula::exists(nv, matrix(&tx, &tn)) != stage_of(&tx)?.concl().as_imp()?.1 {
        return None
    }

    let k1 = Formula::and(k.clone(), matrix(&tx, &tn));
    let k2 = Formula::and(k1.clone(), matrix(&ty, &tm));
    let k2_n = syl(&and_left(k1.clone(), matrix(&ty, &tm)), &and_right(k.clone(), matrix(&tx, &tn)))?;
    let k2_m = and_right(k1.clone(), matrix(&ty, &tm));
    let k2_n_om = syl(
        &k2_n,
        &and_left(
            Formula::mem(tn.clone(), r.omega()),
            Formula::mem(tx.clone(), st.v(r, tn.clone())),
        ),
    )?;
    let k2_x = syl(
        &k2_n,
        &and_right(
            Formula::mem(tn.clone(), r.omega()),
            Formula::mem(tx.clone(), st.v(r, tn.clone())),
        ),
    )?;
    let k2_m_om = syl(
        &k2_m,
        &and_left(
            Formula::mem(tm.clone(), r.omega()),
            Formula::mem(ty.clone(), st.v(r, tm.clone())),
        ),
    )?;
    let k2_y = syl(
        &k2_m,
        &and_right(
            Formula::mem(tm.clone(), r.omega()),
            Formula::mem(ty.clone(), st.v(r, tm.clone())),
        ),
    )?;

    // The two stages, merged.
    let dir = hyp_mp(
        &hyp_inst(&hyp_mp(&hyp_inst(&a1i(&st.directed, k2.clone()), &tn)?, &k2_n_om)?, &tm)?,
        &k2_m_om,
    )?;
    let sub_n = kernel::thm::subset(env, st.v(r, tn.clone()), st.v(r, tp.clone()));
    let sub_m = kernel::thm::subset(env, st.v(r, tm.clone()), st.v(r, tp.clone()));
    let m_body = Formula::and(
        Formula::mem(tp.clone(), r.omega()),
        Formula::and(sub_n.clone(), sub_m.clone()),
    );
    if Formula::exists(pv, m_body.clone()) != dir.concl().as_imp()?.1 {
        return None
    }

    let k3 = Formula::and(k2.clone(), m_body.clone());
    let k3_m = and_right(k2.clone(), m_body.clone());
    let k3_p_om = syl(
        &k3_m,
        &and_left(
            Formula::mem(tp.clone(), r.omega()),
            Formula::and(sub_n.clone(), sub_m.clone()),
        ),
    )?;
    let k3_subs = syl(
        &k3_m,
        &and_right(
            Formula::mem(tp.clone(), r.omega()),
            Formula::and(sub_n.clone(), sub_m.clone()),
        ),
    )?;
    let k3_sn = syl(&k3_subs, &and_left(sub_n.clone(), sub_m.clone()))?;
    let k3_sm = syl(&k3_subs, &and_right(sub_n, sub_m))?;
    let to_k2 = and_left(k2.clone(), m_body.clone());
    let k3_x = hyp_mp(&hyp_inst(&k3_sn, &tx)?, &syl(&to_k2, &k2_x)?)?;
    let k3_y = hyp_mp(&hyp_inst(&k3_sm, &ty)?, &syl(&to_k2, &k2_y)?)?;

    // The pair lands two stages up, and `succ²p` is still a natural.
    let pair_at = hyp_mp(&hyp_inst(&a1i(pair_in_stage, k3.clone()), &tp)?, &k3_p_om)?;
    let landed = hyp_mp(
        &hyp_inst(&hyp_inst(&pair_at, &tx)?, &ty)?,
        &hyp_and(&k3_x, &k3_y)?,
    )?;
    let s2 = r.succ_of(r.succ_of(tp.clone()));
    let s2_om = {
        let one = hyp_mp(
            &a1i(&inst_all(&core.succ_closed, std::slice::from_ref(&tp))?, k3.clone()),
            &k3_p_om,
        )?;
        hyp_mp(
            &a1i(
                &inst_all(&core.succ_closed, std::slice::from_ref(&r.succ_of(tp.clone())))?,
                k3.clone(),
            ),
            &one,
        )?
    };
    let k3_goal = hyp_mp(
        &hyp_inst(
            &hyp_mp(&hyp_inst(&a1i(mem_tower, k3.clone()), &s2)?, &s2_om)?,
            &pair,
        )?,
        &landed,
    )?;
    if *k3_goal.concl() != Formula::imp(k3, goal.clone()) {
        return None
    }

    let k2_goal = discharge(pv, &dir, &k3_goal)?;
    let k1_goal = discharge(
        mv,
        &syl(&and_left(k.clone(), matrix(&tx, &tn)), &stage_of(&ty)?)?,
        &k2_goal,
    )?;
    let k_goal = discharge(nv, &stage_of(&tx)?, &k1_goal)?;

    let out = Thm::gen(xv, &Thm::gen(yv, &k_goal));
    let want = Formula::forall(
        xv,
        Formula::forall(
            yv,
            Formula::imp(
                Formula::and(
                    Formula::mem(tx.clone(), tower.clone()),
                    Formula::mem(ty.clone(), tower.clone()),
                ),
                Formula::mem(pair, tower),
            ),
        ),
    );
    (*out.concl() == want).then_some(out)
}
