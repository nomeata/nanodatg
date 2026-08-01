//! The unit W-type, over an arbitrary set's canonical universe.
//!
//! # Interface
//!
//! [`unit_wtype`] returns a [`UnitWtype`] holding
//!
//! ```text
//! ⊢ closed({c}, ∅, U(c))                                    [UnitWtype::closed]
//! ⊢ ⟨c,∅⟩ ∈ W({c}, ∅, U(c))                                    [UnitWtype::sup]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why `{c}` and `∅`
//!
//! One constructor, no fibres: the smallest W-type that is not empty. `∅` serves
//! as the family because [`crate::wtype::app_of_empty`] gives `app(∅,c) = ∅` for
//! every `c`, which is all `closed` asks of a family, and `U(c)` serves as the
//! bound because [`crate::bound::least_universe_closed`] discharges the
//! closure hypothesis from `{c} ∈ U(c)` and `∅ ∈ U(c)` — both immediate.
//!
//! `c` is the caller's: nothing here is special about it, so the statement is
//! not about one hand-picked set.

use kernel::{Env, Formula, Term, Thm};
use crate::bound::Bound;
use crate::wtype::Wtype;
use crate::{a1i, and_intro, ex_falso, iff_mpr, inst_all, singleton, syl};

/// The two facts about `W({c}, ∅, U(c))` that the instance needs.
pub struct UnitWtype {
    /// `⊢ closed({c}, ∅, U(c))` — the bound hypothesis, **discharged**.
    pub closed: Thm,
    /// `⊢ ⟨c,∅⟩ ∈ W({c}, ∅, U(c))` — the W-type is inhabited.
    pub sup: Thm,
}

/// Build [`UnitWtype`] at the caller's `c`.
///
/// This is the derivation `tests/bound.rs` runs inline, lifted so that it can
/// be *used* rather than only checked: `∅ ⊆ c` puts `∅` in `U(c)` by the
/// subset clause of the universe axiom, pairing puts `{c}` there, every fibre
/// of the constant-empty family is `∅`, and
/// [`crate::bound::least_universe_closed`] and [`crate::bound::sup_mem_at`]
/// then fire with no hypothesis left over.
pub fn unit_wtype(env: &mut Env, wt: &Wtype, bnd: &Bound, c: &Term) -> Option<UnitWtype> {
    let s = &wt.sums;
    let up = s.ap.sets.up;
    let u = Term::apply(bnd.lu, vec![c.clone()]);
    let z = wt.empty();
    let sing_c = singleton(up, c.clone());

    // `c ∈ U(c)`.
    let mem_lu = crate::universe::mem_least_universe(env, bnd.lu, &bnd.lu_ax)?;
    let c_in_u = inst_all(&mem_lu, std::slice::from_ref(c))?;

    // `∅ ⊆ c`, hence `∅ ∈ U(c)` by the subset clause.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let e_sub_c = Thm::gen(
        zv,
        &syl(
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?,
            &ex_falso(Formula::mem(tz, c.clone())),
        )?,
    );
    let c2 = crate::universe::least_universe_closed_sub(env, bnd.lu, &bnd.lu_ax)?;
    let all_sub = Thm::mp(&inst_all(&c2, &[c.clone(), c.clone()])?, &c_in_u)?;
    let e_in_u = Thm::mp(&inst_all(&all_sub, std::slice::from_ref(&z))?, &e_sub_c)?;

    // `{c} ∈ U(c)`, by pairing.
    let pairing = crate::universe::universe_pairing(
        env,
        up,
        &s.ap.sets.up_ax,
        s.ap.empty,
        &s.ap.empty_ax,
        s.pow,
        &s.pow_ax,
    )?;
    let pairing_lu =
        crate::universe::least_universe_pairing(env, bnd.lu, &bnd.lu_ax, up, &pairing)?;
    let sing_in_u = Thm::mp(
        &inst_all(&pairing_lu, &[c.clone(), c.clone(), c.clone()])?,
        &and_intro(&c_in_u, &c_in_u),
    )?;

    // Every fibre of the constant-empty family is `∅ ∈ U(c)`.
    let av = env.fresh_var();
    let ta = Term::var(av);
    let app_e = inst_all(&wt.app_empty, std::slice::from_ref(&ta))?;
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        z.clone(),
        wt.fibre(z.clone(), ta.clone()),
        hole,
        Formula::mem(Term::var(hole), u.clone()),
    );
    let fibre_in_u = Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, &app_e)?)?, &e_in_u)?;
    let fam = Thm::gen(av, &a1i(&fibre_in_u, Formula::mem(ta, sing_c.clone())));
    debug_assert_eq!(
        *fam.concl(),
        crate::bound::fibres_in(env, s, &sing_c, &z, &u),
        "unit_wtype: the family condition is not the one the theorems state"
    );

    // The antecedent of every unconditional rule, proved.
    let ante = and_intro(&sing_in_u, &fam);
    let closed = Thm::mp(
        &inst_all(&bnd.least_universe_closed, &[c.clone(), sing_c.clone(), z.clone()])?,
        &ante,
    )?;
    debug_assert_eq!(
        *closed.concl(),
        crate::wtype::closed(env, s, &sing_c, &z, &u),
        "unit_wtype: closed has the wrong shape"
    );

    // W1 at `a := c`, `f := ∅`.
    let rule = Thm::mp(
        &inst_all(&bnd.sup_mem, &[c.clone(), sing_c.clone(), z.clone()])?,
        &ante,
    )?;
    let w_t = wt.of(sing_c.clone(), z.clone(), u.clone());
    let mem_sing = inst_all(&s.ap.mem_sing, &[c.clone(), c.clone()])?;
    let c_in_sing = Thm::mp(&iff_mpr(&mem_sing)?, &Thm::eq_refl(c.clone()))?;
    let at_c = Thm::mp(&inst_all(&rule, std::slice::from_ref(c))?, &c_in_sing)?;

    // `∅ ∈ fs(app(∅,c), W)`, by rewriting the fibre to `∅`.
    let empty_fun = inst_all(&wt.empty_fun, std::slice::from_ref(&w_t))?;
    let hole2 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(
        z.clone(),
        wt.fibre(z.clone(), c.clone()),
        hole2,
        Formula::mem(z.clone(), s.fs.of(Term::var(hole2), w_t.clone())),
    );
    let app_e_c = inst_all(&wt.app_empty, std::slice::from_ref(c))?;
    let empty_in_fs =
        Thm::mp(&Thm::mp(&carry2, &crate::eq_symm(env, &app_e_c)?)?, &empty_fun)?;
    let sup = Thm::mp(&inst_all(&at_c, std::slice::from_ref(&z))?, &empty_in_fs)?;
    debug_assert_eq!(
        *sup.concl(),
        Formula::mem(wt.sup(c.clone(), z), w_t),
        "unit_wtype: sup has the wrong shape"
    );

    Some(UnitWtype { closed, sup })
}
