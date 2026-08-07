//! **Closure under `⋃`**: a universe contains the union of any member.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀s. ((is_universe(u) ∧ s ∈ u) → ⋃s ∈ u)   [universe_union_closed]
//! ⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))                [least_universe_union]
//! ```
//!
//! The second carries **no hypothesis at all** — it is the usual transfer
//! through the intersection, so `is_universe(U(c))` (whose inaccessibility
//! clause is open) is never needed. Callers need none of the derivation below.
//!
//! # The argument
//!
//! `⋃s ⊆ u` by `C₁` twice — `z ∈ w ∈ s ∈ u` — so `C₄` offers `⋃s ∈ u` **or**
//! `⋃s ≈ u`, and the whole file is spent refuting the second disjunct. Note
//! that [`crate::cantor::member_not_equinumerous`] does *not* apply: it needs
//! `⋃s ∈ u`, which is what was to be proved.
//!
//! So assume a bijection `f : ⋃s ↠ u` and build a set that cannot exist. For
//! `w ∈ s` write
//!
//! ```text
//! img(w) := { y ∈ u : ∃x. (x ∈ w ∧ ⟨x,y⟩ ∈ f) }
//! ```
//!
//! — plain Separation on `u`, and **`img(w) ∈ u`** by
//! [`crate::cantor::image_in_universe`] at `I := w` (a member of `u`, by `C₁`)
//! and the relation `R(x,y) := x ∈ w ∧ ⟨x,y⟩ ∈ f`, whose `DOM` clause is a
//! projection, whose `SV` clause is `f`'s own single-valuedness and whose
//! `ONTO` clause is how `img(w)` was carved. Then
//!
//! ```text
//! S := { b ∈ u : ∃w. (w ∈ s ∧ b = img(w)) }
//! ```
//!
//! — Separation on `u` again, legitimate precisely because the previous step
//! put every `img(w)` *in* `u`, so no power set is needed anywhere. And
//! **`S ∈ u`** by [`crate::cantor::image_in_universe`] once more, at `I := s`
//! and `R'(w,b) := w ∈ s ∧ b = img(w)`; `b = img(w)` is spelled as the
//! biconditional `∀y. (y ∈ b ↔ (y ∈ u ∧ …))`, and `SV` for it is
//! **Extensionality**.
//!
//! Finally `u ⊆ ⋃S`: given `z ∈ u`, `f` is onto so some `⟨x,z⟩ ∈ f`; then
//! `x ∈ ⋃s`, so `x ∈ w` for some `w ∈ s`; so `z ∈ img(w) ∈ S`. Hence
//! `S ∈ u ⊆ ⋃S`, which unfolds to `∃e. (e ∈ S ∧ S ∈ e)` — a membership
//! 2-cycle, refuted by [`crate::empty::no_two_cycle`].
//!
//! # What this needs, and what it deliberately does not
//!
//! `C₁`, `C₄`, [`crate::cantor::image_in_universe`] twice, Separation,
//! Extensionality, Union and Regularity (inside `no_two_cycle`). **No
//! Cantor–Schröder–Bernstein, no ordinals, no cardinal arithmetic, and no
//! `member_not_equinumerous`.** No power set either: the earlier plan separated
//! `S` out of `𝒫u`, which works but is unnecessary once `img(w) ∈ u` is in
//! hand.
//!
//! Because [`universe_union_closed`] is stated at an *arbitrary* universe it
//! transfers to `U(c)` by the same argument
//! [`crate::universe::least_universe_pairing`] uses, so `is_universe(U(x))`
//! is not needed for [`least_universe_union`] either.
//!
//! # How this fails
//!
//! The two entry points are handed the symbols and the lemmas the construction
//! runs on — a `Sets` carrying the union axiom, `mem_mem`, `two_cycle`,
//! `union_closed` — and every guard that rebuilds one of those statements and
//! compares is a [`crate::err::DerErr::Declined`]: the contract working, and
//! the caller's to fix. The same three checks reappear inside the private steps
//! on the very same forwarded premises, and are declines there too. Everything
//! else — the `DOM` and `SV` clauses this file projects for itself, and the
//! statement [`image_in_universe`] is expected to have — is
//! [`crate::err::DerErr::Assembly`]: those values were built here, so a
//! mismatch is a bug above the guard.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::cantor::image_in_universe;
use crate::err::{imported, DResult, Operand};
use crate::funcs::{separation_full, union_intro, Sets};
use crate::prim::{self, Shape};
use crate::rules::{
    com12, exists_elim_imp, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_syl, iff_mp, iff_mpr,
    inst_all, syl, uncurry,
};
use crate::{a1i, and_left, and_right, assembly, decline, gen_all};

use super::closure::universe_clauses;
use super::least::{in_all_universes, least_universe_mem};
use super::closure::least_universe_transfer;
use super::predicate::is_universe;
use super::shared::{hyp_contract, open_exists, split_and};

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> DResult<Thm> {
    let (_, goal) = he_goal.concl().imp_parts()?;
    let (h, _) = h_ex.concl().imp_parts()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
pub(super) fn hyp_gen(v: FreeVar, t: &Thm) -> DResult<Thm> {
    let (h, phi) = t.concl().imp_parts()?;
    prim::mp(&prim::ax_dist(v, h, phi)?, &Thm::gen(v, t))
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — instantiation in implication form.
fn inst_all_imp(phi: &Formula, ts: &[Term]) -> DResult<Thm> {
    let first = ts.first().ok_or_else(|| {
        assembly!("inst_all_imp: no term to instantiate at", Operand::formula("phi", phi))
    })?;
    let mut cur = prim::ax_inst(phi.clone(), first.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().imp_parts()?;
        cur = syl(&cur, &prim::ax_inst(body, t.clone())?)?;
    }
    Ok(cur)
}

/// Everything the three steps of the refutation share: the terms, the ambient
/// hypothesis `N`, the clauses of the bijection read off it, and the two
/// relation schemes.
///
/// Reading formulas apart and carrying them around produces no `Thm`; only the
/// fields that *are* theorems are load-bearing, and each was built by the
/// kernel's rules.
struct Refutation {
    /// The universe.
    tu: Term,
    /// The member whose union is at issue.
    ts: Term,
    /// The bijection `⋃s ↠ u` supplied by `C₄`'s first disjunct.
    tf: Term,
    /// `N := (is_universe(u) ∧ s ∈ u) ∧ f-is-a-bijection`.
    n: Formula,
    /// `⊢ N → is_universe(u)`.
    n_univ: Thm,
    /// `⊢ N → s ∈ u`.
    n_s: Thm,
    /// `⊢ N → ∀a ∀b. (⟨a,b⟩ ∈ f → (a ∈ ⋃s ∧ b ∈ u))`.
    n_in_su: Thm,
    /// `⊢ N → ∀b. (b ∈ u → ∃a. ⟨a,b⟩ ∈ f)`.
    n_onto_u: Thm,
    /// `⊢ N → ∀a ∀b ∀c. ((⟨a,b⟩ ∈ f ∧ ⟨a,c⟩ ∈ f) → b = c)`.
    n_sv_f: Thm,
    /// The relation variable ranging over `⋃s`.
    xv: FreeVar,
    /// The relation variable ranging over `u` — the members of `img(w)`.
    yv: FreeVar,
    /// The variable `img(w)` and the members of `S` are named by.
    bv: FreeVar,
    /// The variable ranging over the members of `s`.
    wv: FreeVar,
    /// `R(x,y) := x ∈ w ∧ ⟨x,y⟩ ∈ f`.
    r_img: Formula,
    /// `ψ(w,y) := ∃x. R(x,y)`.
    psi: Formula,
    /// `IMG(w,b) := ∀y. (y ∈ b ↔ (y ∈ u ∧ ψ(w,y)))` — "`b` is `img(w)`".
    img: Formula,
    /// `⊢ ∃b. IMG(w,b)` — Separation, with `w` free.
    sep_img: Thm,
    /// `R'(w,b) := w ∈ s ∧ IMG(w,b)`.
    rp: Formula,
}

impl Refutation {
    fn tx(&self) -> Term { Term::var(self.xv) }
    fn ty(&self) -> Term { Term::var(self.yv) }
    fn tb(&self) -> Term { Term::var(self.bv) }
    fn tw(&self) -> Term { Term::var(self.wv) }
}

/// **Step 1** — `⊢ (N ∧ (w ∈ s ∧ IMG(w,b))) → b ∈ u`.
///
/// [`image_in_universe`] at `I := w`, `S := b`, `R(x,y) := x ∈ w ∧ ⟨x,y⟩ ∈ f`.
/// `w ∈ u` is `C₁` at `w ∈ s ∈ u`; `b ⊆ u` and `ONTO` are the two halves of the
/// separation condition; `DOM` is a projection; `SV` is `f`'s.
fn img_in_universe(
    env: &mut Env,
    c: &Refutation,
    empty: &Thm,
    mem_mem: &Thm,
) -> DResult<Thm> {
    let (tu, ts, tw, tb, ty) = (c.tu.clone(), c.ts.clone(), c.tw(), c.tb(), c.ty());
    let w_in_s = Formula::mem(tw.clone(), ts.clone());
    let g = Formula::and(c.n.clone(), c.rp.clone());

    let g_n = and_left(c.n.clone(), c.rp.clone());
    let g_rp = and_right(c.n.clone(), c.rp.clone());
    let g_ws = syl(&g_rp, &and_left(w_in_s.clone(), c.img.clone()))?;
    let g_img = syl(&g_rp, &and_right(w_in_s, c.img.clone()))?;
    let g_univ = syl(&g_n, &c.n_univ)?;
    let g_s = syl(&g_n, &c.n_s)?;

    // `w ∈ u`, by `C₁` at `w ∈ s ∈ u`.
    let mm = inst_all(mem_mem, &[tu.clone(), ts.clone(), tw.clone()])?;
    if *mm.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(ts.clone(), tu.clone()),
                    Formula::mem(tw.clone(), ts.clone()),
                ),
            ),
            Formula::mem(tw.clone(), tu.clone()),
        )
    {
        return Err(decline!("the supplied transitivity lemma is not the one universe_mem_mem states"))
    }
    let g_w_in_u = hyp_mp(&a1i(&mm, g.clone()), &hyp_and(&g_univ, &hyp_and(&g_s, &g_ws)?)?)?;

    // The separation condition, at a generic `y`.
    let g_iff = syl(&g_img, &prim::ax_inst(c.img.clone(), ty.clone())?)?;
    let g_fwd = hyp_iff_mp(&g_iff)?;

    // `b ⊆ u` and `ONTO(R, b)` — the two projections of that condition.
    let g_bsub = hyp_gen(
        c.yv,
        &hyp_syl(
            &g_fwd,
            &a1i(&and_left(Formula::mem(ty.clone(), tu.clone()), c.psi.clone()), g.clone()),
        )?,
    )?;
    let g_onto = hyp_gen(
        c.yv,
        &hyp_syl(
            &g_fwd,
            &a1i(&and_right(Formula::mem(ty.clone(), tu.clone()), c.psi.clone()), g.clone()),
        )?,
    )?;

    // `DOM(R, w)` is a projection of `R` and holds outright.
    let dom = crate::cantor::r_dom(&c.r_img, c.xv, c.yv, &tw);
    let dom_thm = Thm::gen(
        c.xv,
        &Thm::gen(
            c.yv,
            &and_left(
                Formula::mem(c.tx(), tw.clone()),
                kernel::thm::pair_in(env, c.tf.clone(), c.tx(), ty.clone()),
            ),
        ),
    );
    if *dom_thm.concl() != dom {
        return Err(assembly!(
            "img_in_universe: the DOM clause projected for img's relation",
            Operand::thm("dom_thm", &dom_thm),
            Operand::formula("dom", &dom),
        ))
    }

    // `SV(R)` — `f`'s own single-valuedness, with the `x ∈ w` conjunct dropped.
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let sv = imported(
        "crate::cantor::r_sv",
        crate::cantor::r_sv(&c.r_img, c.xv, c.yv, cv),
    )?;
    let r_c = c.r_img.subst(c.yv, &tc);
    let d = Formula::and(c.r_img.clone(), r_c.clone());
    let nd = Formula::and(c.n.clone(), d.clone());
    let nd_n = and_left(c.n.clone(), d.clone());
    let nd_d = and_right(c.n.clone(), d.clone());
    let pair_xy = kernel::thm::pair_in(env, c.tf.clone(), c.tx(), ty.clone());
    let pair_xc = kernel::thm::pair_in(env, c.tf.clone(), c.tx(), tc.clone());
    let nd_p1 = syl(
        &syl(&nd_d, &and_left(c.r_img.clone(), r_c.clone()))?,
        &and_right(Formula::mem(c.tx(), tw.clone()), pair_xy.clone()),
    )?;
    let nd_p2 = syl(
        &syl(&nd_d, &and_right(c.r_img.clone(), r_c))?,
        &and_right(Formula::mem(c.tx(), tw.clone()), pair_xc.clone()),
    )?;
    let sv_at = inst_all_imp(
        &c.n_sv_f.concl().imp_parts()?.1,
        &[c.tx(), ty.clone(), tc.clone()],
    )?;
    let nd_eq = hyp_mp(&syl(&syl(&nd_n, &c.n_sv_f)?, &sv_at)?, &hyp_and(&nd_p1, &nd_p2)?)?;
    debug_assert_eq!(
        *nd_eq.concl(),
        Formula::imp(nd, Formula::eq(ty.clone(), tc)),
        "SV for img's relation did not reach the equation"
    );
    let n_sv = hyp_gen(c.xv, &hyp_gen(c.yv, &hyp_gen(cv, &uncurry(&nd_eq)?)?)?)?;
    if *n_sv.concl() != Formula::imp(c.n.clone(), sv.clone()) {
        return Err(assembly!(
            "img_in_universe: the SV clause derived from f's single-valuedness",
            Operand::thm("n_sv", &n_sv),
            Operand::formula("sv", &sv),
        ))
    }
    let g_sv = syl(&g_n, &n_sv)?;

    // ── Regularity, at `I := w` ──────────────────────────────────────────────
    let iiu = imported(
        "crate::cantor::image_in_universe",
        image_in_universe(env, empty, &tu, &tw, &tb, c.xv, c.yv, &c.r_img),
    )?;
    let want = Formula::imp(
        Formula::and(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(tw.clone(), tu.clone()),
                    kernel::thm::subset(env, tb.clone(), tu.clone()),
                ),
            ),
            Formula::and(dom.clone(), Formula::and(sv, crate::cantor::r_onto(&c.r_img, c.xv, c.yv, &tb))),
        ),
        Formula::mem(tb.clone(), tu.clone()),
    );
    if *iiu.concl() != want {
        return Err(assembly!(
            "img_in_universe: image_in_universe's statement at I := w",
            Operand::thm("iiu", &iiu),
            Operand::formula("want", &want),
        ))
    }
    let out = hyp_mp(
        &a1i(&iiu, g.clone()),
        &hyp_and(
            &hyp_and(&g_univ, &hyp_and(&g_w_in_u, &g_bsub)?)?,
            &hyp_and(&a1i(&dom_thm, g.clone()), &hyp_and(&g_sv, &g_onto)?)?,
        )?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(g, Formula::mem(tb, tu)),
        "img_in_universe: wrong shape"
    );
    Ok(out)
}

/// **Step 2** — `⊢ (N ∧ SBODY(S)) → S ∈ u`, where
/// `SBODY(S) := ∀b. (b ∈ S ↔ (b ∈ u ∧ ∃w. (w ∈ s ∧ IMG(w,b))))`.
///
/// [`image_in_universe`] at `I := s`, `R'(w,b) := w ∈ s ∧ IMG(w,b)`. `S ⊆ u`
/// and `ONTO` are the two halves of the separation condition, `DOM` is a
/// projection, and **`SV` is Extensionality**: two sets with the same
/// membership condition `IMG(w,·)` are equal.
fn collection_in_universe(
    env: &mut Env,
    c: &Refutation,
    empty: &Thm,
    big_s: &Term,
    sbody: &Formula,
) -> DResult<Thm> {
    let (tu, ts, tb, ty, tw) = (c.tu.clone(), c.ts.clone(), c.tb(), c.ty(), c.tw());
    let m = Formula::and(c.n.clone(), sbody.clone());
    let m_n = and_left(c.n.clone(), sbody.clone());
    let m_sb = and_right(c.n.clone(), sbody.clone());
    let m_univ = syl(&m_n, &c.n_univ)?;
    let m_s = syl(&m_n, &c.n_s)?;

    let chi = Formula::exists(c.wv, c.rp.clone());
    let m_iff = syl(&m_sb, &prim::ax_inst(sbody.clone(), tb.clone())?)?;
    let m_fwd = hyp_iff_mp(&m_iff)?;
    let m_ssub = hyp_gen(
        c.bv,
        &hyp_syl(&m_fwd, &a1i(&and_left(Formula::mem(tb.clone(), tu.clone()), chi.clone()), m.clone()))?,
    )?;
    let m_onto = hyp_gen(
        c.bv,
        &hyp_syl(&m_fwd, &a1i(&and_right(Formula::mem(tb.clone(), tu.clone()), chi.clone()), m.clone()))?,
    )?;

    // `DOM(R', s)` is a projection and holds outright.
    let dom = crate::cantor::r_dom(&c.rp, c.wv, c.bv, &ts);
    let dom_thm = Thm::gen(
        c.wv,
        &Thm::gen(c.bv, &and_left(Formula::mem(tw.clone(), ts.clone()), c.img.clone())),
    );
    if *dom_thm.concl() != dom {
        return Err(assembly!(
            "collection_in_universe: the DOM clause projected for the collection's relation",
            Operand::thm("dom_thm", &dom_thm),
            Operand::formula("dom", &dom),
        ))
    }

    // ── `SV(R')` is Extensionality ───────────────────────────────────────────
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let sv = imported("crate::cantor::r_sv", crate::cantor::r_sv(&c.rp, c.wv, c.bv, cv))?;
    let rp_c = c.rp.subst(c.bv, &tc);
    let img_c = c.img.subst(c.bv, &tc);
    let d = Formula::and(c.rp.clone(), rp_c.clone());
    let d_img_b = syl(
        &and_left(c.rp.clone(), rp_c.clone()),
        &and_right(Formula::mem(tw.clone(), ts.clone()), c.img.clone()),
    )?;
    let d_img_c = syl(
        &and_right(c.rp.clone(), rp_c),
        &and_right(Formula::mem(tw.clone(), ts.clone()), img_c.clone()),
    )?;
    let d_iff_b = syl(&d_img_b, &prim::ax_inst(c.img.clone(), ty.clone())?)?;
    let d_iff_c = syl(&d_img_c, &prim::ax_inst(img_c, ty.clone())?)?;
    let d_same = hyp_and(
        &hyp_syl(&hyp_iff_mp(&d_iff_b)?, &hyp_iff_mpr(&d_iff_c)?)?,
        &hyp_syl(&hyp_iff_mp(&d_iff_c)?, &hyp_iff_mpr(&d_iff_b)?)?,
    )?;
    let d_all = hyp_gen(c.yv, &d_same)?;
    let ext = Thm::ax_extensionality(env);
    let ext_at = inst_all(&ext, &[tb.clone(), tc.clone()])?;
    let d_eq = hyp_mp(&a1i(&ext_at, d.clone()), &d_all)?;
    debug_assert_eq!(
        *d_eq.concl(),
        Formula::imp(d, Formula::eq(tb.clone(), tc)),
        "Extensionality did not close SV for the collection's relation"
    );
    let sv_thm = Thm::gen(c.wv, &Thm::gen(c.bv, &Thm::gen(cv, &d_eq)));
    if *sv_thm.concl() != sv {
        return Err(assembly!(
            "collection_in_universe: the SV clause Extensionality was to supply",
            Operand::thm("sv_thm", &sv_thm),
            Operand::formula("sv", &sv),
        ))
    }

    // ── Regularity, at `I := s` ──────────────────────────────────────────────
    let iiu = imported(
        "crate::cantor::image_in_universe",
        image_in_universe(env, empty, &tu, &ts, big_s, c.wv, c.bv, &c.rp),
    )?;
    let want = Formula::imp(
        Formula::and(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(ts.clone(), tu.clone()),
                    kernel::thm::subset(env, big_s.clone(), tu.clone()),
                ),
            ),
            Formula::and(
                dom.clone(),
                Formula::and(sv, crate::cantor::r_onto(&c.rp, c.wv, c.bv, big_s)),
            ),
        ),
        Formula::mem(big_s.clone(), tu.clone()),
    );
    if *iiu.concl() != want {
        return Err(assembly!(
            "collection_in_universe: image_in_universe's statement at I := s",
            Operand::thm("iiu", &iiu),
            Operand::formula("want", &want),
        ))
    }
    let out = hyp_mp(
        &a1i(&iiu, m.clone()),
        &hyp_and(
            &hyp_and(&m_univ, &hyp_and(&m_s, &m_ssub)?)?,
            &hyp_and(&a1i(&dom_thm, m.clone()), &hyp_and(&a1i(&sv_thm, m.clone()), &m_onto)?)?,
        )?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(m, Formula::mem(big_s.clone(), tu)),
        "collection_in_universe: wrong shape"
    );
    Ok(out)
}

/// **Step 3** — `⊢ (N ∧ SBODY(S)) → ∀z. (z ∈ u → z ∈ ⋃S)`.
///
/// `f` is onto, so `z ∈ u` has a pre-image `x ∈ ⋃s`, which lies in some
/// `w ∈ s`; then `z ∈ img(w)`, and `img(w) ∈ S` because it is in `u` (step 1)
/// and satisfies `S`'s condition by construction.
#[allow(clippy::too_many_arguments)]
fn covers_universe(
    env: &mut Env,
    c: &Refutation,
    sets: &Sets,
    big_s: &Term,
    sbody: &Formula,
    step1: &Thm,
    zv: FreeVar,
) -> DResult<Thm> {
    let (tu, ts, tb, tw) = (c.tu.clone(), c.ts.clone(), c.tb(), c.tw());
    let tz = Term::var(zv);
    let us = sets.union_of(ts.clone());
    let m = Formula::and(c.n.clone(), sbody.clone());

    // `P₀ := M ∧ z ∈ u`.
    let z_in_u = Formula::mem(tz.clone(), tu.clone());
    let p0 = Formula::and(m.clone(), z_in_u.clone());
    let p0_m = and_left(m.clone(), z_in_u.clone());
    let p0_z = and_right(m.clone(), z_in_u.clone());
    let p0_n = syl(&p0_m, &and_left(c.n.clone(), sbody.clone()))?;
    let p0_sb = syl(&p0_m, &and_right(c.n.clone(), sbody.clone()))?;

    // `f` is onto `u`, so `z` has a pre-image.
    let onto_at = inst_all_imp(&c.n_onto_u.concl().imp_parts()?.1, std::slice::from_ref(&tz))?;
    let p0_ex = hyp_mp(&syl(&syl(&p0_n, &c.n_onto_u)?, &onto_at)?, &p0_z)?;
    let pair_xz = kernel::thm::pair_in(env, c.tf.clone(), c.tx(), tz.clone());
    debug_assert_eq!(
        p0_ex.concl().imp_parts()?.1,
        Formula::exists(c.xv, pair_xz.clone()),
        "f's onto clause does not produce a pre-image of z"
    );

    // `P₁ := P₀ ∧ ⟨x,z⟩ ∈ f`.
    let p1 = Formula::and(p0.clone(), pair_xz.clone());
    let p1_p0 = and_left(p0.clone(), pair_xz.clone());
    let p1_pair = and_right(p0.clone(), pair_xz.clone());
    let in_su_at = inst_all_imp(&c.n_in_su.concl().imp_parts()?.1, &[c.tx(), tz.clone()])?;
    let p1_n = syl(&p1_p0, &p0_n)?;
    let p1_x_in_us = syl(
        &hyp_mp(&syl(&syl(&p1_n, &c.n_in_su)?, &in_su_at)?, &p1_pair)?,
        &and_left(Formula::mem(c.tx(), us.clone()), Formula::mem(tz.clone(), tu.clone())),
    )?;

    // The Union axiom turns `x ∈ ⋃s` into a `w ∈ s` containing `x`.
    let un_at = inst_all(&sets.un_ax, &[ts.clone(), c.tx()])?;
    let ubody = Formula::and(
        Formula::mem(tw.clone(), ts.clone()),
        Formula::mem(c.tx(), tw.clone()),
    );
    if *un_at.concl()
        != Formula::iff(Formula::mem(c.tx(), us.clone()), Formula::exists(c.wv, ubody.clone()))
    {
        return Err(decline!("the supplied union axiom does not characterise membership in the union of s"))
    }
    let p1_ex_w = syl(&p1_x_in_us, &iff_mp(&un_at)?)?;

    // `P₂ := P₁ ∧ (w ∈ s ∧ x ∈ w)`.
    let p2 = Formula::and(p1.clone(), ubody.clone());
    let p2_p1 = and_left(p1.clone(), ubody.clone());
    let p2_u = and_right(p1.clone(), ubody.clone());
    let p2_ws = syl(
        &p2_u,
        &and_left(Formula::mem(tw.clone(), ts.clone()), Formula::mem(c.tx(), tw.clone())),
    )?;
    let p2_xw = syl(
        &p2_u,
        &and_right(Formula::mem(tw.clone(), ts.clone()), Formula::mem(c.tx(), tw.clone())),
    )?;
    let p2_ex_b = a1i(&c.sep_img, p2.clone());
    debug_assert_eq!(
        p2_ex_b.concl().imp_parts()?.1,
        Formula::exists(c.bv, c.img.clone()),
        "Separation does not produce img(w)"
    );

    // `P₃ := P₂ ∧ IMG(w,b)`.
    let p3 = Formula::and(p2.clone(), c.img.clone());
    let p3_p2 = and_left(p2.clone(), c.img.clone());
    let p3_img = and_right(p2.clone(), c.img.clone());
    let p3_p1 = syl(&p3_p2, &p2_p1)?;
    let p3_p0 = syl(&p3_p1, &p1_p0)?;

    // `z ∈ b`: `z ∈ u` and `x` witnesses `ψ(w,z)`.
    let psi_z = c.psi.subst(c.yv, &tz);
    let p3_psi = syl(
        &hyp_and(&syl(&p3_p2, &p2_xw)?, &syl(&p3_p1, &p1_pair)?)?,
        &crate::rules::exists_intro_imp(c.xv, c.r_img.subst(c.yv, &tz), c.tx())?,
    )?;
    debug_assert_eq!(
        p3_psi.concl().imp_parts()?.1,
        psi_z,
        "the witness for img(w)'s condition has the wrong shape"
    );
    let p3_iff = syl(&p3_img, &prim::ax_inst(c.img.clone(), tz.clone())?)?;
    let p3_z_in_b = hyp_mp(
        &hyp_iff_mpr(&p3_iff)?,
        &hyp_and(&syl(&p3_p0, &p0_z)?, &p3_psi)?,
    )?;

    // `b ∈ u` (step 1), and `b` satisfies `S`'s condition with witness `w`.
    let p3_b_in_u = hyp_mp(
        &a1i(step1, p3.clone()),
        &hyp_and(&syl(&p3_p0, &p0_n)?, &hyp_and(&syl(&p3_p2, &p2_ws)?, &p3_img)?)?,
    )?;
    let p3_chi = syl(
        &hyp_and(&syl(&p3_p2, &p2_ws)?, &p3_img)?,
        &crate::rules::exists_intro_imp(c.wv, c.rp.clone(), tw.clone())?,
    )?;
    let p3_sb_iff = syl(&syl(&p3_p0, &p0_sb)?, &prim::ax_inst(sbody.clone(), tb.clone())?)?;
    let p3_b_in_s = hyp_mp(&hyp_iff_mpr(&p3_sb_iff)?, &hyp_and(&p3_b_in_u, &p3_chi)?)?;

    // `z ∈ b ∈ S`, so `z ∈ ⋃S`.
    let ui = imported(
        "crate::funcs::union_intro",
        union_intro(env, sets, big_s.clone(), tb.clone(), tz.clone()),
    )?;
    let p3_goal = hyp_mp(&a1i(&ui, p3.clone()), &hyp_and(&p3_b_in_s, &p3_z_in_b)?)?;

    // Discharge the three witnesses, then generalise over `z`.
    let p2_goal = discharge(c.bv, &p2_ex_b, &p3_goal)?;
    let p1_goal = discharge(c.wv, &p1_ex_w, &p2_goal)?;
    let p0_goal = discharge(c.xv, &p0_ex, &p1_goal)?;
    let out = hyp_gen(zv, &uncurry(&p0_goal)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            m,
            Formula::forall(
                zv,
                Formula::imp(z_in_u, Formula::mem(tz, sets.union_of(big_s.clone())))
            )
        ),
        "covers_universe: wrong shape"
    );
    Ok(out)
}

/// `⊢ ∀u ∀s. ((is_universe(u) ∧ s ∈ u) → ⋃s ∈ u)` — **every universe is closed
/// under `⋃`**.
///
/// `⋃s ⊆ u` by `C₁` twice, so `C₄` offers `⋃s ≈ u` or `⋃s ∈ u`; the first is
/// refuted by building, from the supposed bijection, a set `S ∈ u` with
/// `u ⊆ ⋃S`, hence `S ∈ ⋃S` — a membership 2-cycle. See the module header for
/// the construction.
///
/// `mem_mem` must be [`super::universe_mem_mem`] and `two_cycle`
/// [`crate::empty::no_two_cycle`]; both are checked against rebuilt statements,
/// so a mismatched theorem is declined rather than concluded from.
pub fn universe_union_closed(
    env: &mut Env,
    sets: &Sets,
    empty: &Thm,
    mem_mem: &Thm,
    two_cycle: &Thm,
) -> DResult<Thm> {
    let (uv, setv) = (env.fresh_var(), env.fresh_var());
    let (tu, ts) = (Term::var(uv), Term::var(setv));
    let us = sets.union_of(ts.clone());

    let univ_u = is_universe(env, &tu);
    let s_in_u = Formula::mem(ts.clone(), tu.clone());
    let h = Formula::and(univ_u.clone(), s_in_u.clone());
    let h_univ = and_left(univ_u.clone(), s_in_u.clone());
    let h_s = and_right(univ_u.clone(), s_in_u.clone());

    // ── `⋃s ⊆ u`, by `C₁` twice along `z ∈ w ∈ s ∈ u` ────────────────────────
    let (av, w0v) = (env.fresh_var(), env.fresh_var());
    let (ta, tw0) = (Term::var(av), Term::var(w0v));
    let a_in_us = Formula::mem(ta.clone(), us.clone());
    let q = Formula::and(h.clone(), a_in_us.clone());
    let q_h = and_left(h.clone(), a_in_us.clone());
    let q_mem = and_right(h.clone(), a_in_us.clone());

    let un_at = inst_all(&sets.un_ax, &[ts.clone(), ta.clone()])?;
    let ubody =
        Formula::and(Formula::mem(tw0.clone(), ts.clone()), Formula::mem(ta.clone(), tw0.clone()));
    if *un_at.concl() != Formula::iff(a_in_us.clone(), Formula::exists(w0v, ubody.clone())) {
        return Err(decline!("the supplied union axiom does not characterise membership in the union of s"))
    }
    let q_ex = syl(&q_mem, &iff_mp(&un_at)?)?;

    let q1 = Formula::and(q.clone(), ubody.clone());
    let q1_q = and_left(q.clone(), ubody.clone());
    let q1_u = and_right(q.clone(), ubody.clone());
    let q1_ws = syl(
        &q1_u,
        &and_left(Formula::mem(tw0.clone(), ts.clone()), Formula::mem(ta.clone(), tw0.clone())),
    )?;
    let q1_aw = syl(
        &q1_u,
        &and_right(Formula::mem(tw0.clone(), ts.clone()), Formula::mem(ta.clone(), tw0.clone())),
    )?;
    let q1_univ = syl(&q1_q, &syl(&q_h, &h_univ)?)?;
    let q1_s = syl(&q1_q, &syl(&q_h, &h_s)?)?;

    let mm_check = |env: &mut Env, y: &Term, z: &Term| -> DResult<Thm> {
        let at = inst_all(mem_mem, &[tu.clone(), y.clone(), z.clone()])?;
        let want = Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(y.clone(), tu.clone()),
                    Formula::mem(z.clone(), y.clone()),
                ),
            ),
            Formula::mem(z.clone(), tu.clone()),
        );
        if *at.concl() != want {
            return Err(decline!("the supplied transitivity lemma is not the one universe_mem_mem states"))
        }
        Ok(at)
    };
    let mm1 = mm_check(env, &ts, &tw0)?;
    let q1_w_in_u = hyp_mp(&a1i(&mm1, q1.clone()), &hyp_and(&q1_univ, &hyp_and(&q1_s, &q1_ws)?)?)?;
    let mm2 = mm_check(env, &tw0, &ta)?;
    let q1_a_in_u =
        hyp_mp(&a1i(&mm2, q1.clone()), &hyp_and(&q1_univ, &hyp_and(&q1_w_in_u, &q1_aw)?)?)?;
    let q_a_in_u = discharge(w0v, &q_ex, &q1_a_in_u)?;
    let h_sub = hyp_gen(av, &uncurry(&q_a_in_u)?)?;
    debug_assert_eq!(
        *h_sub.concl(),
        Formula::imp(h.clone(), kernel::thm::subset(env, us.clone(), tu.clone())),
        "⋃s ⊆ u has the wrong shape"
    );

    // ── The supposed bijection `f : ⋃s ↠ u`, taken apart once ────────────────
    let equi = kernel::thm::equinumerous(env, us.clone(), tu.clone());
    let fv = env.fresh_var();
    let tf = Term::var(fv);
    let fbody = open_exists(&equi, &tf)?;
    debug_assert_eq!(equi, Formula::exists(fv, fbody.clone()), "the ∃f did not reopen");
    let (in_su, k1) = split_and(&fbody)?;
    let (total, k2) = split_and(&k1)?;
    let (onto_u, k3) = split_and(&k2)?;
    let (sv_f, inj) = split_and(&k3)?;

    let n = Formula::and(h.clone(), fbody.clone());
    let n_h = and_left(h.clone(), fbody.clone());
    let n_f = and_right(h.clone(), fbody.clone());
    let n_univ = syl(&n_h, &h_univ)?;
    let n_s = syl(&n_h, &h_s)?;
    let n_in_su = syl(&n_f, &and_left(in_su.clone(), k1.clone()))?;
    let n_k2 = syl(&syl(&n_f, &and_right(in_su, k1))?, &and_right(total, k2))?;
    let n_onto_u = syl(&n_k2, &and_left(onto_u.clone(), k3.clone()))?;
    let n_sv_f = syl(&syl(&n_k2, &and_right(onto_u, k3))?, &and_left(sv_f, inj))?;

    // ── The two relation schemes, and `img(w)` by Separation on `u` ──────────
    let (xv, yv, bv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tb, tw) = (Term::var(xv), Term::var(yv), Term::var(bv), Term::var(wv));

    let r_img = Formula::and(
        Formula::mem(tx.clone(), tw.clone()),
        kernel::thm::pair_in(env, tf.clone(), tx.clone(), ty.clone()),
    );
    let psi = Formula::exists(xv, r_img.clone());
    let sep_img = imported(
        "crate::funcs::separation_full",
        separation_full(env, yv, &psi, &tu, empty),
    )?;
    let img = Formula::forall(
        yv,
        Formula::iff(
            Formula::mem(ty.clone(), tb.clone()),
            Formula::and(Formula::mem(ty.clone(), tu.clone()), psi.clone()),
        ),
    );
    debug_assert_eq!(
        *sep_img.concl(),
        Formula::exists(bv, img.clone()),
        "Separation did not produce img(w)'s characteristic property"
    );
    let rp = Formula::and(Formula::mem(tw.clone(), ts.clone()), img.clone());

    let ctx = Refutation {
        tu: tu.clone(),
        ts: ts.clone(),
        tf: tf.clone(),
        n: n.clone(),
        n_univ,
        n_s,
        n_in_su,
        n_onto_u,
        n_sv_f,
        xv,
        yv,
        bv,
        wv,
        r_img,
        psi,
        img: img.clone(),
        sep_img,
        rp: rp.clone(),
    };

    let step1 = img_in_universe(env, &ctx, empty, mem_mem)?;

    // ── `S`, by Separation on `u` — no power set needed ──────────────────────
    let chi = Formula::exists(wv, rp);
    let sep_coll = imported(
        "crate::funcs::separation_full",
        separation_full(env, bv, &chi, &tu, empty),
    )?;
    let bigv = env.fresh_var();
    let big_s = Term::var(bigv);
    let sbody = Formula::forall(
        bv,
        Formula::iff(
            Formula::mem(tb.clone(), big_s.clone()),
            Formula::and(Formula::mem(tb.clone(), tu.clone()), chi.clone()),
        ),
    );
    debug_assert_eq!(
        *sep_coll.concl(),
        Formula::exists(bigv, sbody.clone()),
        "Separation did not produce S's characteristic property"
    );

    let m = Formula::and(n.clone(), sbody.clone());
    let step2 = collection_in_universe(env, &ctx, empty, &big_s, &sbody)?;
    let zv = env.fresh_var();
    let step3 = covers_universe(env, &ctx, sets, &big_s, &sbody, &step1, zv)?;

    // ── `S ∈ u ⊆ ⋃S`, i.e. a membership 2-cycle ──────────────────────────────
    let us_big = sets.union_of(big_s.clone());
    let m_s_in_us = hyp_mp(
        &syl(&step3, &prim::ax_inst(step3.concl().imp_parts()?.1, big_s.clone())?)?,
        &step2,
    )?;
    debug_assert_eq!(
        *m_s_in_us.concl(),
        Formula::imp(m.clone(), Formula::mem(big_s.clone(), us_big.clone())),
        "S ∈ ⋃S has the wrong shape"
    );

    let ev = env.fresh_var();
    let te = Term::var(ev);
    let un_big = inst_all(&sets.un_ax, &[big_s.clone(), big_s.clone()])?;
    let cycle = Formula::and(
        Formula::mem(te.clone(), big_s.clone()),
        Formula::mem(big_s.clone(), te.clone()),
    );
    if *un_big.concl()
        != Formula::iff(
            Formula::mem(big_s.clone(), us_big.clone()),
            Formula::exists(ev, cycle.clone()),
        )
    {
        return Err(decline!("the supplied union axiom does not unfold S in its own union to a membership cycle"))
    }
    let m_ex_cycle = syl(&m_s_in_us, &iff_mp(&un_big)?)?;

    let tc_at = inst_all(two_cycle, &[te.clone(), big_s.clone()])?;
    if *tc_at.concl() != Formula::not(cycle.clone()) {
        return Err(decline!("the supplied two-cycle lemma does not refute the membership cycle it was instantiated at"))
    }
    let mc = Formula::and(m.clone(), cycle.clone());
    let mc_false = hyp_mp(&a1i(&tc_at, mc.clone()), &and_right(m.clone(), cycle))?;
    let m_false = discharge(ev, &m_ex_cycle, &mc_false)?;

    // Discharge `S`, then `f`, and cash `C₄` in.
    let n_false = discharge(bigv, &a1i(&sep_coll, n.clone()), &m_false)?;
    let h_not_equi = com12(&exists_elim_imp(
        fv,
        &Thm::gen(fv, &com12(&uncurry(&n_false)?)?),
        &Formula::imp(h.clone(), Formula::false_()),
    )?)?;
    debug_assert_eq!(
        *h_not_equi.concl(),
        Formula::imp(h.clone(), Formula::not(equi.clone())),
        "the refutation of ⋃s ≈ u has the wrong shape"
    );

    let cl = universe_clauses(env, &tu)?;
    let goal = Formula::mem(us.clone(), tu.clone());
    let h_disj = hyp_mp(
        &syl(&h_univ, &syl(&cl.to_c4, &prim::ax_inst(cl.c4, us.clone())?)?)?,
        &h_sub,
    )?;
    debug_assert_eq!(
        *h_disj.concl(),
        Formula::imp(h.clone(), Formula::or(equi, goal.clone())),
        "C₄ did not instantiate to the expected disjunction"
    );
    let out = hyp_mp(&h_disj, &h_not_equi)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, goal),
        "universe_union_closed: wrong shape"
    );
    Ok(gen_all(&[uv, setv], &out))
}

/// `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))` — **`U(c)` is closed under `⋃`**, with no
/// hypothesis at all.
///
/// The transfer [`super::least_universe_pairing`] uses: a closure property that
/// holds in *every* universe holds in their intersection, so
/// `is_universe(U(c))` — whose inaccessibility clause is open — is not needed.
///
/// `union_closed` must be [`universe_union_closed`] for this very `un`; a
/// mismatched theorem is declined.
pub fn least_universe_union(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    un: FnSym,
    union_closed: &Thm,
) -> DResult<Thm> {
    if lu.arity() != 1 || un.arity() != 1 {
        return Err(decline!("the least-universe symbol is not unary, or the union symbol is not unary"))
    }
    let (cv, setv) = (env.fresh_var(), env.fresh_var());
    let (tc, ts) = (Term::var(cv), Term::var(setv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let us = Term::apply(un, vec![ts.clone()]);

    let h = Formula::mem(ts.clone(), w.clone());

    // A universe `u` containing `c`, held fixed until the very end.
    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let univ_u = is_universe(env, &tu);
    let c_in_u = Formula::mem(tc.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), c_in_u.clone());

    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());
    let n_univ = syl(&n_a, &and_left(univ_u, c_in_u))?;

    let transfer = least_universe_transfer(env, lu_ax, &tc, &ts, &tu)?;
    let n_s_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &n_h)?, &n_a)?;

    let uc_at = inst_all(union_closed, &[tu.clone(), ts.clone()])?;
    let want = Formula::imp(
        Formula::and(is_universe(env, &tu), Formula::mem(ts.clone(), tu.clone())),
        Formula::mem(us.clone(), tu.clone()),
    );
    if *uc_at.concl() != want {
        return Err(decline!("the supplied closure theorem is not universe_union_closed for this union symbol"))
    }
    let n_us_in_u = hyp_mp(&a1i(&uc_at, n.clone()), &hyp_and(&n_univ, &n_s_in_u)?)?;

    // Generalise over `u`, then read the result back as membership in `U(c)`.
    let h_phi = prim::mp(
        &prim::ax_dist(uv, h.clone(), Formula::imp(a, Formula::mem(us.clone(), tu)))?,
        &Thm::gen(uv, &uncurry(&n_us_in_u)?),
    )?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h.clone(), in_all_universes(env, &tc, &us)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let out = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tc, &us)?)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(us, w)),
        "least_universe_union: wrong shape"
    );
    Ok(gen_all(&[cv, setv], &out))
}
