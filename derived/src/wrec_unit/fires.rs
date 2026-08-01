//! **ι fires** — the recursor has a member, and its value there is computed.
//!
//! # Interface
//!
//! ```text
//! ⊢ ⟨⟨c,∅⟩, V⟩ ∈ wrec({c}, ∅, U(c), T, e)                        [wrec_member]
//! ⊢ app(wrec({c}, ∅, U(c), T, e), ⟨c,∅⟩) = app(e, ⟨c,⟨∅,∅⟩⟩)      [iota_fires]
//! ```
//!
//! unconditional, with `V := app(e, ⟨c,⟨∅,∅⟩⟩)`. Callers need none of the
//! derivation below.
//!
//! # The point of the whole module
//!
//! Everything [`crate::wrec`] proves is **vacuously true of an empty recursor**:
//! `⊢ ∅ ∈ Att` says the attempt condition is satisfiable, not that `wrec` has a
//! single member, and every ι statement there is guarded by
//! `indom(wrec, ⟨a,f⟩)`. [`wrec_member`] discharges that guard — `wrec` is the
//! union of all attempts, and [`super::attempt`] exhibits one containing the
//! pair — and [`iota_fires`] then computes the value.
//!
//! **Both sides are computed**, the left-hand side really is an application of
//! the recursor, and the two sides are visibly different terms: `tests/wrec.rs`
//! asserts that they are, so the equation cannot be reflexivity in disguise.
//! And none of it needs totality.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::bound::Bound;
use crate::wrec::indom;
use crate::wtype::Wtype;
use crate::{and_intro, exists_intro_imp, inst_all, singleton};

use super::shared::eq_trans;
use super::instance::unit_wtype;
use super::attempt::{UnitAttempt, singleton_attempt, unit_graph, unit_target, unit_value};

/// **The recursor is not empty.**
///
/// ```text
/// ⊢ ⟨⟨c,∅⟩, V⟩ ∈ wrec({c}, ∅, U(c), {V}, e)
/// ```
///
/// One [`crate::wrec::attempt_subset_wrec`], at the one-point attempt. Stated
/// separately from [`iota_fires`] because it is the *set-level* non-vacuity:
/// `app(wrec, ·)` is total on sets and would return `∅` for an empty graph, so
/// an equation about `app(wrec, ⟨c,∅⟩)` alone does not by itself say `wrec` has
/// a member. This does, and it discharges the guard of
/// [`crate::wrec::iota_on_domain`] outright.
///
/// `subset` is [`crate::wrec::attempt_subset_wrec`] and `rec` the symbol
/// [`crate::wrec::wrec_symbol`] introduced.
#[allow(clippy::too_many_arguments)]
pub fn wrec_member(
    wt: &Wtype,
    bnd: &Bound,
    rec: FnSym,
    subset: &Thm,
    ua: &UnitAttempt,
    c: &Term,
    e: &Term,
) -> Option<Thm> {
    let ap = &wt.sums.ap;
    let up = ap.sets.up;
    let z = wt.empty();
    let args = [
        singleton(up, c.clone()),
        z.clone(),
        Term::apply(bnd.lu, vec![c.clone()]),
        unit_target(ap, c, e),
        e.clone(),
    ];
    let g = unit_graph(ap, c, e);
    let p = ap.sets.pair(wt.sup(c.clone(), z), unit_value(ap, c, e));

    let mut ts = args.to_vec();
    ts.push(g);
    ts.push(p.clone());
    let out = Thm::mp(&inst_all(subset, &ts)?, &and_intro(&ua.att, &ua.mem))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(p, Term::apply(rec, args.to_vec())),
        "wrec_member: unexpected shape"
    );
    Some(out)
}

/// **The recursor computes.**
///
/// ```text
/// ⊢ app(wrec({c}, ∅, U(c), {V}, e), ⟨c,∅⟩) = app(e, ⟨c, ⟨∅,∅⟩⟩)
/// ```
///
/// with `V := app(e, ⟨c, ⟨∅,∅⟩⟩)`. Unconditional — the bound hypothesis is
/// discharged by [`unit_wtype`] — and **both sides are computed**: the
/// left-hand side is an application of the recursor to a member of its W-type,
/// the right-hand side is the step applied to the flat triple with the
/// composite already collapsed, and the two are different terms.
///
/// This is the fact [`crate::wrec::iota_on_domain`] does not supply. That
/// theorem is guarded by `indom(wrec, ⟨a,f⟩)`, and nothing there rules out
/// `wrec = ∅`; here the guard is discharged, so `wrec` provably has a member
/// and the ι equation provably fires at it.
///
/// `value` is [`crate::wrec::wrec_value`] and `rec` the symbol
/// [`crate::wrec::wrec_symbol`] introduced.
#[allow(clippy::too_many_arguments)]
pub fn iota_fires(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    comp: FnSym,
    comp_ax: &Thm,
    att_ax: &Thm,
    rec: FnSym,
    value: &Thm,
    c: &Term,
    e: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let up = ap.sets.up;

    let u = Term::apply(bnd.lu, vec![c.clone()]);
    let z = wt.empty();
    let sing_c = singleton(up, c.clone());
    let w0 = wt.sup(c.clone(), z.clone());
    let v = unit_value(ap, c, e);
    let t_t = unit_target(ap, c, e);
    let g = unit_graph(ap, c, e);

    let uw = unit_wtype(env, wt, bnd, c)?;
    let ua = singleton_attempt(env, wt, comp, comp_ax, att_ax, &uw.sup, c, &u, e)?;

    // `indom(g, ⟨c,∅⟩)`, at the witness `V`.
    let yv = env.fresh_var();
    let dom_body = Formula::mem(ap.sets.pair(w0.clone(), Term::var(yv)), g.clone());
    let in_dom = Thm::mp(&exists_intro_imp(yv, dom_body, v.clone())?, &ua.mem)?;
    debug_assert_eq!(
        *in_dom.concl(),
        indom(env, ap, &g, &w0),
        "iota_fires: the domain condition has the wrong shape"
    );

    // `wrec_value` at this instance, this attempt and this point.
    let at = Thm::mp(
        &inst_all(value, &[sing_c.clone(), z.clone(), u.clone(), t_t.clone(), e.clone()])?,
        &uw.closed,
    )?;
    let at_g = Thm::mp(&inst_all(&at, std::slice::from_ref(&g))?, &ua.att)?;
    let transfer = Thm::mp(&inst_all(&at_g, std::slice::from_ref(&w0))?, &in_dom)?;

    let out = eq_trans(env, &transfer, &ua.value)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(
            ap.apply(Term::apply(rec, vec![sing_c, z, u, t_t, e.clone()]), w0),
            v
        ),
        "iota_fires: the computed equation has the wrong shape"
    );
    Some(out)
}
