//! The union of an `ω`-indexed tower.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀z. (z ∈ tower(c) ↔ ∃n. (n ∈ ω ∧ z ∈ app(iter(c), n)))     [OmegaTower::members]
//! ```
//!
//! Callers need none of the derivation below. `tower` is a fresh symbol of the
//! same arity as `iter`.
//!
//! # Why a second Replacement
//!
//! `iter(c)` is a set of *pairs*, so no amount of `⋃` reaches its values without
//! also dragging in the indices: `⋃⋃iter(c)` is `ω ∪ {vₙ : n ∈ ω}`, and one more
//! `⋃` folds `ω` in as well. The values have to be collected as an image, which
//! is a Replacement instance — a trivial one, since `z = app(iter(c),x)`
//! determines `z` outright — and then `⋃` of that image is the tower.
//!
//! # What it is for
//!
//! `W(A,B,u) ∈ u` for a finitely-branching W-type reduces to exhibiting `W` as
//! `⋃ₙ Wₙ` for an `ω`-indexed family that stays inside the universe: each `Wₙ`
//! is in `u` by product and power closure, `{Wₙ : n ∈ ω}` is in `u` by
//! Replacement closure seeded at `ω ∈ u`
//! ([`crate::tower::Level`]), and the union is in `u` by `⋃`-closure. The one
//! thing that construction could not state before is the family `n ↦ Wₙ`, which
//! is [`crate::recursion::recursion`]; this file is the `⋃` at the end of it.

use kernel::{Env, Formula, FnSym, FreeVar, Term, Thm};

use crate::funcs::union_intro;
use crate::{
    a1i, and_intro, and_left, and_right, define_by_membership, exists_elim_imp, exists_intro,
    exists_intro_imp, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl,
};
use crate::funspace::discharge;
use super::rec::Rec;
use super::theorem::Recursion;

/// The union of the `ω`-indexed tower `n ↦ app(iter(c), n)`.
pub struct OmegaTower {
    /// The symbol collecting the values, `{app(iter(c),n) : n ∈ ω}`.
    pub range: FnSym,
    /// The tower symbol itself.
    pub tower: FnSym,
    /// `⊢ ∀z. (z ∈ tower(c) ↔ ∃n. (n ∈ ω ∧ z ∈ app(iter(c), n)))`.
    pub members: Thm,
    /// The term `tower(params)`.
    pub term: Term,
}

impl OmegaTower {
    /// The term `tower(params)`.
    pub fn set(&self) -> Term { self.term.clone() }
}

/// Build the tower over an already-derived [`Recursion`].
///
/// `params` must be the same list [`crate::recursion::recursion`] was given.
pub fn omega_tower(
    env: &mut Env,
    r: &Rec,
    rec: &Recursion,
    params: &[FreeVar],
) -> Option<OmegaTower> {
    let sets = r.ap.sets.clone();
    let it = rec.set();
    let args: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();

    // ── The image `{app(iter,x) : x ∈ ω}` ────────────────────────────────────
    let (x, z, z2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tz, tz2) = (Term::var(x), Term::var(z), Term::var(z2));
    let value = r.apply(it.clone(), tx.clone());
    let psi = Formula::eq(tz.clone(), value.clone());
    let x_om = Formula::mem(tx.clone(), r.omega());

    let eu_body = Formula::and(
        psi.clone(),
        Formula::forall(
            z2,
            Formula::imp(psi.subst(z, &tz2), Formula::eq(tz2.clone(), tz.clone())),
        ),
    );
    let witness = and_intro(
        &Thm::eq_refl(value.clone()),
        &Thm::gen(z2, &imp_refl(Formula::eq(tz2, value.clone()))),
    );
    let eu = exists_intro(z, eu_body, value.clone(), &witness)?;
    let functional = Thm::gen(x, &a1i(&eu, x_om.clone()));

    let repl = Thm::ax_replacement(env, x, z, psi.clone())?;
    let at_omega = Thm::mp(&Thm::ax_inst(repl.concl().clone(), r.omega())?, &repl)?;
    let ex_range = Thm::mp(&at_omega, &functional)?;
    let image = Formula::exists(x, Formula::and(x_om.clone(), psi));
    let (range, range_closed) = define_by_membership(env, params, &ex_range, z, &image)?;
    let rng = Term::apply(range, args.clone());
    let range_members = inst_all(&range_closed, &args)?;

    // ── `⋃` of it, characterised pointwise ───────────────────────────────────
    let (zz, y, x3) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tzz, ty, tx3) = (Term::var(zz), Term::var(y), Term::var(x3));
    let union = sets.union_of(rng.clone());
    let inner = Formula::and(x_om.clone(), Formula::mem(tzz.clone(), value.clone()));
    let cond = Formula::exists(x, inner.clone());
    let mem_union = Formula::mem(tzz.clone(), union.clone());

    // Forward.
    let y_rng = Formula::mem(ty.clone(), rng.clone());
    let zz_y = Formula::mem(tzz.clone(), ty.clone());
    let big_y = Formula::and(y_rng.clone(), zz_y.clone());
    let y_at = inst_all(&range_members, std::slice::from_ref(&ty))?;
    let e_x = Formula::and(x_om.clone(), Formula::eq(ty.clone(), value.clone()));
    let y_ex = syl(&and_left(y_rng.clone(), zz_y.clone()), &iff_mp(&y_at)?)?;
    let k = Formula::and(big_y.clone(), e_x.clone());
    let k_xom = syl(&and_right(big_y.clone(), e_x.clone()), &and_left(x_om.clone(), Formula::eq(ty.clone(), value.clone())))?;
    let k_eq = syl(&and_right(big_y.clone(), e_x.clone()), &and_right(x_om.clone(), Formula::eq(ty.clone(), value.clone())))?;
    let k_zzy = syl(&and_left(big_y.clone(), e_x.clone()), &and_right(y_rng, zz_y))?;
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        ty.clone(),
        value.clone(),
        w,
        Formula::mem(tzz.clone(), Term::var(w)),
    );
    let k_mem = hyp_mp(&hyp_mp(&a1i(&carry, k.clone()), &k_eq)?, &k_zzy)?;
    let k_goal = syl(&hyp_and(&k_xom, &k_mem)?, &exists_intro_imp(x, inner.clone(), tx.clone())?)?;
    let y_goal = discharge(x, &y_ex, &k_goal)?;
    let un_at = inst_all(&sets.un_ax, &[rng.clone(), tzz.clone()])?;
    debug_assert_eq!(
        *un_at.concl(),
        Formula::iff(mem_union.clone(), Formula::exists(y, big_y)),
        "omega_tower: the Union axiom has an unexpected shape"
    );
    let fwd = syl(&iff_mp(&un_at)?, &exists_elim_imp(y, &Thm::gen(y, &y_goal), &cond)?)?;

    // Backward.
    let img_at = Formula::exists(
        x3,
        Formula::and(
            Formula::mem(tx3.clone(), r.omega()),
            Formula::eq(value.clone(), r.apply(it.clone(), tx3.clone())),
        ),
    );
    debug_assert_eq!(
        img_at,
        image.subst(z, &value),
        "omega_tower: the image instance drifted"
    );
    let into_rng = syl(
        &hyp_and(
            &and_left(x_om.clone(), Formula::mem(tzz.clone(), value.clone())),
            &a1i(&Thm::eq_refl(value.clone()), inner.clone()),
        )?,
        &exists_intro_imp(
            x3,
            Formula::and(
                Formula::mem(tx3.clone(), r.omega()),
                Formula::eq(value.clone(), r.apply(it.clone(), tx3)),
            ),
            tx.clone(),
        )?,
    )?;
    let value_at = inst_all(&range_members, std::slice::from_ref(&value))?;
    let in_rng = syl(&into_rng, &iff_mpr(&value_at)?)?;
    let intro = union_intro(env, &sets, rng.clone(), value.clone(), tzz.clone())?;
    let inner_goal = syl(
        &hyp_and(&in_rng, &and_right(x_om.clone(), Formula::mem(tzz.clone(), value)))?,
        &intro,
    )?;
    let bwd = exists_elim_imp(x, &Thm::gen(x, &inner_goal), &mem_union)?;

    // ── The symbol ───────────────────────────────────────────────────────────
    let iff_body = and_intro(&fwd, &bwd);
    debug_assert_eq!(*iff_body.concl(), Formula::iff(mem_union, cond.clone()));
    let all = Thm::gen(zz, &iff_body);
    let s = env.fresh_var();
    let prop = Formula::forall(
        zz,
        Formula::iff(Formula::mem(tzz, Term::var(s)), cond.clone()),
    );
    let ex_tower = exists_intro(s, prop, union, &all)?;
    let (tower, tower_closed) = define_by_membership(env, params, &ex_tower, zz, &cond)?;
    let term = Term::apply(tower, args.clone());
    let members = inst_all(&tower_closed, &args)?;
    debug_assert_eq!(
        *members.concl(),
        Formula::forall(zz, Formula::iff(Formula::mem(Term::var(zz), term.clone()), cond)),
        "omega_tower: unexpected shape"
    );
    Some(OmegaTower { range, tower, members, term })
}
