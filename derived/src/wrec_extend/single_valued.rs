//! **Clause 1 of the attempt condition**: the extension is single-valued.
//!
//! # Interface
//!
//! Private to [`crate::wrec_extend`]. `extension_single_valued` is the first of
//! the three clauses [`super::assemble`] needs to call `G` an attempt.
//!
//! # The one real case
//!
//! `G` is `g ∪ {⟨⟨a,f⟩, v⟩}`, so two pairs of `G` over the same point are either
//! both from `g` — where `g`'s own single-valuedness settles it — or both the
//! new pair, where they are equal outright. The crossed case is the one that has
//! to be refuted, and `collapse_at_new` is what refutes it: a pair of `g` over
//! `⟨a,f⟩` would contradict `¬indom(g, ⟨a,f⟩)`. That clause of
//! [`super::hypothesis`] is doing all the work here as well.

use kernel::{Env, Formula, Term, Thm};
use crate::funspace::is_single_valued;
use crate::separation::hyp_syl;
use crate::sums::Sums;
use crate::wrec::{hyp_eq_symm, hyp_eq_trans};
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{a1i, and_left, and_right, hyp_and, hyp_mp, hyp_or_elim, iff_mp, inst_all, syl, uncurry};

use super::shared::{gen_under, hyp_inst, hyp_leibniz};
use super::terms::Cx;

/// The case in which one of the two pairs is the new one:
/// `⊢ M → (⟨x,y⟩ = ⟨⟨a,f⟩,V⟩ → y = y′)`, given `⊢ M → ⟨x,y′⟩ ∈ G`.
///
/// If `⟨x,y⟩` is the new pair then `x` is `⟨a,f⟩` and `y` is `V`; the *other*
/// pair is then also a `G`-pair over `⟨a,f⟩`, so [`value_at_new_point`] makes
/// its value `V` too. Used twice, once for each side, which is why it takes the
/// two values as arguments rather than fixing them.
#[allow(clippy::too_many_arguments)]
fn collapse_at_new(
    env: &mut Env,
    s: &Sums,
    cx: &Cx,
    at_new: &Thm,
    m: &Formula,
    other: &Thm,
    x: &Term,
    y: &Term,
    y_other: &Term,
) -> Option<Thm> {
    let ap = &s.ap;
    let is_new = Formula::eq(ap.sets.pair(x.clone(), y.clone()), cx.q.clone());
    let n_m = and_left(m.clone(), is_new.clone());
    let n_new = and_right(m.clone(), is_new);

    let inj = syl(
        &n_new,
        &inst_all(&ap.pair_inj, &[x.clone(), y.clone(), cx.w0.clone(), cx.v.clone()])?,
    )?;
    let eq_x = Formula::eq(x.clone(), cx.w0.clone());
    let eq_y = Formula::eq(y.clone(), cx.v.clone());
    let n_x = syl(&inj, &and_left(eq_x.clone(), eq_y.clone()))?;
    let n_y = syl(&inj, &and_right(eq_x, eq_y))?;

    // The other pair, moved over `x = ⟨a,f⟩`.
    let hole = env.fresh_var();
    let carried = hyp_leibniz(
        &n_x,
        hole,
        &Formula::mem(
            ap.sets.pair(Term::var(hole), y_other.clone()),
            cx.g.clone(),
        ),
    )?;
    let n_other = hyp_mp(&carried, &syl(&n_m, other)?)?;
    let n_o = hyp_mp(
        &hyp_inst(&syl(&n_m, at_new)?, std::slice::from_ref(y_other))?,
        &n_other,
    )?;
    let n_flip = hyp_eq_symm(env, &n_o)?;
    uncurry(&hyp_eq_trans(env, &n_y, &n_flip)?)
}

/// **The extension is single-valued.** `⊢ K → sv(G)`
///
/// Two pairs of `G` over the same point. If either is the new one,
/// [`collapse_at_new`] makes both values `V`; otherwise both came from `wrec`,
/// which is single-valued under `closed(A,B,u)`. Three leaves, not four — see
/// the module header.
pub(super) fn extension_single_valued(
    env: &mut Env,
    wt: &Wtype,
    r: &Recursor,
    cx: &Cx,
    at_new: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let (xv, yv, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(xv), Term::var(yv), Term::var(y2v));
    let pair1 = ap.sets.pair(tx.clone(), ty.clone());
    let pair2 = ap.sets.pair(tx.clone(), ty2.clone());
    let p1 = Formula::mem(pair1.clone(), cx.g.clone());
    let p2 = Formula::mem(pair2.clone(), cx.g.clone());
    let both = Formula::and(p1.clone(), p2.clone());

    let m = Formula::and(cx.k.clone(), both.clone());
    let m_k = and_left(cx.k.clone(), both.clone());
    let m_both = and_right(cx.k.clone(), both);
    let m_1 = syl(&m_both, &and_left(p1.clone(), p2.clone()))?;
    let m_2 = syl(&m_both, &and_right(p1, p2))?;
    let at_new_m = syl(&m_k, at_new)?;

    // ── The first pair is the new one ───────────────────────────────────────
    let case_new = collapse_at_new(env, s, cx, &at_new_m, &m, &m_2, &tx, &ty, &ty2)?;

    // ── The first pair came from `wrec` ─────────────────────────────────────
    let old1 = Formula::mem(pair1.clone(), cx.rec_t.clone());
    let n = Formula::and(m.clone(), old1.clone());
    let n_m = and_left(m.clone(), old1.clone());
    let n_old = and_right(m.clone(), old1);
    let n_disj = syl(&syl(&n_m, &m_2)?, &iff_mp(&cx.mem(s, &pair2)?)?)?;

    // Both from `wrec`: the recursor is single-valued.
    let old2 = Formula::mem(pair2.clone(), cx.rec_t.clone());
    let n2_n = and_left(n.clone(), old2.clone());
    let n2_old2 = and_right(n.clone(), old2);
    let n2_sv = hyp_inst(
        &syl(
            &syl(&syl(&syl(&n2_n, &n_m)?, &m_k)?, &cx.cl)?,
            &inst_all(&r.sv, &cx.ps)?,
        )?,
        &[tx.clone(), ty.clone(), ty2.clone()],
    )?;
    let both_old = hyp_and(&syl(&n2_n, &n_old)?, &n2_old2)?;
    let case_both_old = uncurry(&hyp_mp(&n2_sv, &both_old)?)?;

    // The second pair is the new one: flip [`collapse_at_new`]'s conclusion.
    let n_at_new = syl(&syl(&n_m, &m_k)?, at_new)?;
    let flipped = collapse_at_new(
        env,
        s,
        cx,
        &n_at_new,
        &n,
        &syl(&n_m, &m_1)?,
        &tx,
        &ty2,
        &ty,
    )?;
    let case_new2 = hyp_syl(
        &flipped,
        &a1i(&crate::eq_symm_imp(env, ty2.clone(), ty.clone()), n.clone()),
    )?;

    let case_old = uncurry(&hyp_or_elim(&n_disj, &case_both_old, &case_new2)?)?;

    // ── The two cases of the first pair ─────────────────────────────────────
    let m_disj = syl(&m_1, &iff_mp(&cx.mem(s, &pair1)?)?)?;
    let body = uncurry(&hyp_or_elim(&m_disj, &case_old, &case_new)?)?;

    let out = gen_under(xv, &cx.k, &gen_under(yv, &cx.k, &gen_under(y2v, &cx.k, &body)?)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(cx.k.clone(), is_single_valued(env, &ap.sets, &cx.g)),
        "extension_single_valued: sv(G) has the wrong shape"
    );
    Some(out)
}
