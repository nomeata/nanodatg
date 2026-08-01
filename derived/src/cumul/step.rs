//! **The step operator of the cumulative hierarchy**, `G(x) = x ∪ 𝒫x`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀b ∀c. ((a ⊆ b ∧ b ⊆ c) → a ⊆ c)                       [subset_trans]
//! ⊢ ∀a ∀b ∀z. (z ∈ a ∪ b → (z ∈ a ∨ z ∈ b))                   [mem_bin_union_elim]
//!
//! G(x) := ⋃{x, 𝒫x}                                            [Step::g]
//! ⊢ ∀x. G(x) = x ∪ 𝒫x                                         [Step::g_ax]
//! ⊢ ∀x ∀z. (z ∈ x → z ∈ G(x))                                 [Step::mem]
//! ⊢ ∀x ∀z. (z ⊆ x → z ∈ G(x))                                 [Step::sub]
//! ⊢ ∀x ∀z. (z ∈ G(x) → (z ∈ x ∨ z ⊆ x))                       [Step::elim]
//! ⊢ ∀x ∀y. (x ⊆ y → G(x) ⊆ G(y))                              [Step::mono]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why `x ∪ 𝒫x` and not `𝒫x`
//!
//! The tower this feeds ([`super::stages`]) is iterated from a **seed** `S`, and
//! every argument downstream needs the stages to increase: `Vₙ ⊆ V₍ₙ₊₁₎`. With
//! the step `𝒫` that holds only when the seed is transitive, and a transitive
//! seed containing a given set is a transitive *closure* — itself an `ω`
//! recursion, and one this development does not have. With the step `x ∪ 𝒫x` the
//! increase is immediate from the left disjunct of [`mem_bin_union_elim`], at
//! **any** seed whatsoever, and that is the whole reason for the union.
//!
//! The price is [`mem_bin_union_elim`]: `𝒫` is monotone by one instantiation,
//! whereas `x ∪ 𝒫x` needs the *elimination* rule for a binary union, which
//! [`crate::funspace::pow_pow`] does not have — it proves only the two
//! introduction halves. That is the only new set-theoretic fact here.
//!
//! # `G` is a genuine unary symbol, and has to be
//!
//! [`crate::recursion::recursion`] takes the step as a `FnSym` of the ambient
//! extension, *not* as a term: a symbol cannot be an argument of the symbol
//! being defined. So the step may carry no parameters, and everything the
//! hierarchy is built over — the seed, and through it `A` and `B` — has to enter
//! through the recursion's **base** `c`, which may have free variables as long
//! as they are declared as parameters. That is why the seed is the base and the
//! step is closed, and not the other way round.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::funspace::bin_union;
use crate::funspace::pow_pow::mem_bin_union;
use crate::separation::{hyp_syl, or_intro_left, or_intro_right};
use crate::{
    and_left, and_right, com12, define_abbrev, exists_elim_imp, gen_all, hyp_or_elim, iff_mp,
    iff_mpr, imp_mono_r, inst_all, syl,
};

/// `⊢ ∀a ∀b ∀c. ((a ⊆ b ∧ b ⊆ c) → a ⊆ c)` — transitivity of inclusion.
pub fn subset_trans(env: &mut Env) -> Option<Thm> {
    let (a, b, c, t) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, tt) = (Term::var(a), Term::var(b), Term::var(c), Term::var(t));

    let ab = kernel::thm::subset(env, ta.clone(), tb.clone());
    let bc = kernel::thm::subset(env, tb.clone(), tc.clone());
    let ac = kernel::thm::subset(env, ta.clone(), tc.clone());
    let h = Formula::and(ab.clone(), bc.clone());

    let h_ab = syl(&and_left(ab.clone(), bc.clone()), &Thm::ax_inst(ab.clone(), tt.clone())?)?;
    let h_bc = syl(&and_right(ab, bc.clone()), &Thm::ax_inst(bc, tt.clone())?)?;
    let body = hyp_syl(&h_ab, &h_bc)?;

    let inner = Formula::imp(Formula::mem(tt.clone(), ta), Formula::mem(tt, tc));
    let dist = Thm::ax_dist(t, h.clone(), inner)?;
    let out = Thm::mp(&dist, &Thm::gen(t, &body))?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, ac), "subset_trans: unexpected shape");
    Some(gen_all(&[a, b, c], &out))
}

/// `⊢ ∀a ∀b ∀z. (z ∈ a ∪ b → (z ∈ a ∨ z ∈ b))` — the **elimination** half of
/// the binary union, which [`crate::funspace::pow_pow`] does not prove.
///
/// `a ∪ b` is `⋃{a,b}`, so a member of it lies in some `y ∈ {a,b}`, and `y` is
/// `a` or `b` by the unordered pair's characterisation. The two cases are one
/// Leibniz step each, and the witness `y` is discharged by [`exists_elim_imp`].
pub fn mem_bin_union_elim(env: &mut Env, sets: &Sets) -> Option<Thm> {
    let (a, b, z, y, w) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz, ty) = (Term::var(a), Term::var(b), Term::var(z), Term::var(y));
    let up = Term::apply(sets.up, vec![ta.clone(), tb.clone()]);

    let mem_za = Formula::mem(tz.clone(), ta.clone());
    let mem_zb = Formula::mem(tz.clone(), tb.clone());
    let goal = Formula::or(mem_za.clone(), mem_zb.clone());

    // `K := y ∈ {a,b} ∧ z ∈ y`.
    let f1 = Formula::mem(ty.clone(), up.clone());
    let f2 = Formula::mem(tz.clone(), ty.clone());

    let up_at = inst_all(&sets.up_ax, &[ta.clone(), tb.clone(), ty.clone()])?;
    let k_disj = syl(&and_left(f1.clone(), f2.clone()), &iff_mp(&up_at)?)?;
    let k_zy = and_right(f1.clone(), f2.clone());

    let mem_zw = Formula::mem(tz.clone(), Term::var(w));
    let leib_a = Thm::eq_leibniz(ty.clone(), ta.clone(), w, mem_zw.clone());
    let to_a = syl(&k_zy, &com12(&leib_a)?)?;
    let k_left = syl(
        &to_a,
        &imp_mono_r(&or_intro_left(mem_za.clone(), mem_zb.clone()), Formula::eq(ty.clone(), ta.clone()))?,
    )?;

    let leib_b = Thm::eq_leibniz(ty.clone(), tb.clone(), w, mem_zw);
    let to_b = syl(&k_zy, &com12(&leib_b)?)?;
    let k_right = syl(
        &to_b,
        &imp_mono_r(&or_intro_right(mem_za, mem_zb), Formula::eq(ty.clone(), tb.clone()))?,
    )?;

    let cases = hyp_or_elim(&k_disj, &k_left, &k_right)?;
    let elim = exists_elim_imp(y, &Thm::gen(y, &cases), &goal)?;
    let un_at = inst_all(&sets.un_ax, &[up, tz.clone()])?;
    let out = syl(&iff_mp(&un_at)?, &elim)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(tz, bin_union(sets, ta, tb)), goal),
        "mem_bin_union_elim: unexpected shape"
    );
    Some(gen_all(&[a, b, z], &out))
}

/// The step operator `G(x) = x ∪ 𝒫x`, and everything the hierarchy needs of it.
pub struct Step {
    /// The unary symbol `G`.
    pub g: FnSym,
    /// `⊢ ∀x. G(x) = x ∪ 𝒫x`.
    pub g_ax: Thm,
    /// `⊢ ∀x ∀z. (z ∈ x → z ∈ G(x))`.
    pub mem: Thm,
    /// `⊢ ∀x ∀z. (z ⊆ x → z ∈ G(x))`.
    pub sub: Thm,
    /// `⊢ ∀x ∀z. (z ∈ G(x) → (z ∈ x ∨ z ⊆ x))`.
    pub elim: Thm,
    /// `⊢ ∀x ∀y. (x ⊆ y → G(x) ⊆ G(y))`.
    pub mono: Thm,
    /// `⊢ ∀a ∀b ∀c. ((a ⊆ b ∧ b ⊆ c) → a ⊆ c)`, which every caller needs too.
    pub subset_trans: Thm,
}

impl Step {
    /// The term `G(t)`.
    pub fn of(&self, t: Term) -> Term { Term::apply(self.g, vec![t]) }

    /// Introduce `G` and derive its five properties.
    ///
    /// `pow` must be the power set symbol of the same definitional chain as
    /// `sets`; passing a fresh one would make every theorem here about a
    /// different power set from the one the universe closure lemmas use.
    pub fn new(env: &mut Env, sets: &Sets, pow: FnSym, pow_ax: &Thm) -> Option<Step> {
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let body = bin_union(sets, tx.clone(), Term::apply(pow, vec![tx.clone()]));
        let (g, g_ax) = define_abbrev(env, &[xv], &body)?;

        let subset_trans = subset_trans(env)?;
        let bu_elim = mem_bin_union_elim(env, sets)?;
        let (bu_left, bu_right) = mem_bin_union(env, sets)?;

        // ── Moving across `G(x) = x ∪ 𝒫x` ───────────────────────────────────
        let (x, z) = (env.fresh_var(), env.fresh_var());
        let (tx, tz) = (Term::var(x), Term::var(z));
        let powx = Term::apply(pow, vec![tx.clone()]);
        let bu = bin_union(sets, tx.clone(), powx.clone());
        let gx = Term::apply(g, vec![tx.clone()]);
        let eq = inst_all(&g_ax, std::slice::from_ref(&tx))?;
        debug_assert_eq!(*eq.concl(), Formula::eq(gx.clone(), bu.clone()));

        let wv = env.fresh_var();
        let mem_zw = Formula::mem(tz.clone(), Term::var(wv));
        let out_of_g =
            Thm::mp(&Thm::eq_leibniz(gx.clone(), bu.clone(), wv, mem_zw.clone()), &eq)?;
        let into_g = Thm::mp(
            &Thm::eq_leibniz(bu.clone(), gx.clone(), wv, mem_zw),
            &crate::eq_symm(env, &eq)?,
        )?;

        // ── The three membership rules ──────────────────────────────────────
        let mem = syl(&inst_all(&bu_left, &[tx.clone(), powx.clone(), tz.clone()])?, &into_g)?;
        let pow_at = inst_all(pow_ax, &[tx.clone(), tz.clone()])?;
        let sub = syl(
            &syl(
                &iff_mpr(&pow_at)?,
                &inst_all(&bu_right, &[tx.clone(), powx.clone(), tz.clone()])?,
            )?,
            &into_g,
        )?;

        let raw = syl(&out_of_g, &inst_all(&bu_elim, &[tx.clone(), powx, tz.clone()])?)?;
        let mem_zx = Formula::mem(tz.clone(), tx.clone());
        let elim = syl(&raw, &imp_mono_r(&iff_mp(&pow_at)?, Formula::not(mem_zx.clone()))?)?;

        let mem = gen_all(&[x, z], &mem);
        let sub = gen_all(&[x, z], &sub);
        let elim = gen_all(&[x, z], &elim);

        let mono = monotone(env, g, &mem, &sub, &elim, &subset_trans)?;
        Some(Step { g, g_ax, mem, sub, elim, mono, subset_trans })
    }
}

/// `⊢ ∀x ∀y. (x ⊆ y → G(x) ⊆ G(y))`.
///
/// A member of `G(x)` is a member of `x` or a subset of it; the first case
/// travels along `x ⊆ y` pointwise and the second by [`subset_trans`], and both
/// land back in `G(y)`.
fn monotone(
    env: &mut Env,
    g: FnSym,
    mem: &Thm,
    sub: &Thm,
    elim: &Thm,
    subset_trans: &Thm,
) -> Option<Thm> {
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
    let (gx, gy) = (Term::apply(g, vec![tx.clone()]), Term::apply(g, vec![ty.clone()]));

    let h = kernel::thm::subset(env, tx.clone(), ty.clone());
    let mem_zgx = Formula::mem(tz.clone(), gx.clone());
    let mem_zgy = Formula::mem(tz.clone(), gy.clone());
    // `K := (x ⊆ y) ∧ z ∈ G(x)`.
    let k = Formula::and(h.clone(), mem_zgx.clone());
    let k_h = and_left(h.clone(), mem_zgx.clone());
    let k_z = and_right(h.clone(), mem_zgx.clone());

    let disj = syl(&k_z, &inst_all(elim, &[tx.clone(), tz.clone()])?)?;

    // Case `z ∈ x`: travel along `x ⊆ y`, then `mem`.
    let travel = syl(&k_h, &Thm::ax_inst(h.clone(), tz.clone())?)?;
    let left =
        hyp_syl(&travel, &crate::a1i(&inst_all(mem, &[ty.clone(), tz.clone()])?, k.clone()))?;

    // Case `z ⊆ x`: pair it with `x ⊆ y`, then `subset_trans`, then `sub`.
    let sub_zx = kernel::thm::subset(env, tz.clone(), tx.clone());
    let sub_xy = h.clone();
    let intro = com12(&crate::and_intro_imp(sub_zx.clone(), sub_xy.clone()))?;
    let to_conj = syl(&k_h, &intro)?;
    let trans_at = inst_all(subset_trans, &[tz.clone(), tx.clone(), ty.clone()])?;
    let to_sub_zy = hyp_syl(&to_conj, &crate::a1i(&trans_at, k.clone()))?;
    let right = hyp_syl(
        &to_sub_zy,
        &crate::a1i(&inst_all(sub, &[ty.clone(), tz.clone()])?, k.clone()),
    )?;

    let cases = hyp_or_elim(&disj, &left, &right)?;

    // `cases : K → z ∈ G(y)`; curry back to `(x ⊆ y) → (z ∈ G(x) → z ∈ G(y))`.
    let curried = curry(&cases)?;
    let inner = Formula::imp(mem_zgx, mem_zgy);
    let dist = Thm::ax_dist(z, h.clone(), inner)?;
    let out = Thm::mp(&dist, &Thm::gen(z, &curried))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::subset(env, gx, gy)),
        "step monotonicity: unexpected shape"
    );
    Some(gen_all(&[x, y], &out))
}

/// From `⊢ (φ ∧ ψ) → χ` infer `⊢ φ → (ψ → χ)` — the converse of
/// [`crate::uncurry`].
pub fn curry(t: &Thm) -> Option<Thm> {
    let (and, _chi) = t.concl().as_imp()?;
    let (phi, psi) = split_and(&and)?;
    let intro = crate::and_intro_imp(phi.clone(), psi.clone());
    syl(&intro, &imp_mono_r(t, psi)?)
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
