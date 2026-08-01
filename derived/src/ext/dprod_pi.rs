//! Lean's dependent `Π` typing rule, with **no antecedent left over**.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(x) ∈ U(c))) → dprod(A) ∈ U(c))
//!                                                    [dprod_in_universe_pair]
//! ```
//!
//! This is **the form the checker wants**: a base set in a universe, every
//! fibre in the same universe, and the dependent product in it too. Callers
//! need none of the derivation below.
//!
//! # What it replaces
//!
//! [`super::dprod_in_universe_of`] carries `(A ∪ ⋃img(A)) ∈ U(c)` as an
//! explicit antecedent, and its module comment names the three closure
//! properties needed to discharge it: **Replacement** (to put
//! `img(A) = { b(x) : x ∈ A }` in `U(c)`), **`⋃`** (to strip it down to
//! `⋃img(A)`), and **binary union**. All three are now available —
//! [`crate::universe::least_universe_replacement`],
//! [`crate::universe::least_universe_union`] and
//! [`crate::universe::least_universe_bin_union`] — so the antecedent is
//! discharged and the rule is stated at the typing conditions a caller already
//! has.
//!
//! [`super::dprod_in_universe`] remains as the instance that needed none of
//! this, by choosing the universe after the union has been formed; it is
//! strictly weaker than what is here and is kept because `crate::checker`
//! consumes it.
//!
//! Until 2026-07-31 all three ingredients were *refutable*, not merely
//! unproved; see the countermodels at the end of [`crate::universe`] and the
//! date note on [`super::dprod_in_universe_of`].

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::bin_union;
use crate::universe::fibres_in;
use crate::{a1i, and_left, gen_all, hyp_and, hyp_mp, inst_all, syl};

use super::dprod::{base_of, DProd};

/// `⊢ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(x) ∈ U(c))) → dprod(A) ∈ U(c))` —
/// **the dependent `Π` typing rule, unconditionally**.
///
/// Three closure properties, in order: Replacement puts `img(A)` in `U(c)`,
/// `⋃`-closure puts `⋃img(A)` there, binary union puts `A ∪ ⋃img(A)` there,
/// and [`super::dprod_in_universe_of`] finishes.
///
/// Every argument is rebuilt at our own terms and compared, so a stack that
/// does not fit together — a `least_union` for a different universe operator, a
/// `least_replacement` for a different fibre symbol — is refused rather than
/// silently described.
#[allow(clippy::too_many_arguments)]
pub fn dprod_in_universe_pair(
    env: &mut Env,
    ap: &Apply,
    dp: &DProd,
    lu: FnSym,
    b: FnSym,
    least_replacement: &Thm,
    least_union: &Thm,
    least_bin_union: &Thm,
    general: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 || b.arity() != 1 {
        return None
    }
    let (cv, av) = (env.fresh_var(), env.fresh_var());
    let (tc, ta) = (Term::var(cv), Term::var(av));
    let w = Term::apply(lu, vec![tc.clone()]);

    let img_a = Term::apply(dp.img, vec![ta.clone()]);
    let u_img = base_of(ap, dp.img, &ta); // ⋃img(A)
    debug_assert_eq!(u_img, ap.sets.union_of(img_a.clone()), "⋃img(A) is not the union of img(A)");
    let un = bin_union(&ap.sets, ta.clone(), u_img.clone());

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let fib = fibres_in(env, b, &ta, &w);
    let h = Formula::and(a_in_w.clone(), fib.clone());
    let h_a = and_left(a_in_w.clone(), fib);

    // Replacement, then `⋃`.
    let lr = inst_all(least_replacement, &[tc.clone(), ta.clone()])?;
    if *lr.concl() != Formula::imp(h.clone(), Formula::mem(img_a.clone(), w.clone())) {
        return None
    }
    let lun = inst_all(least_union, &[tc.clone(), img_a.clone()])?;
    if *lun.concl()
        != Formula::imp(
            Formula::mem(img_a, w.clone()),
            Formula::mem(u_img.clone(), w.clone()),
        )
    {
        return None
    }
    let h_uimg = syl(&lr, &lun)?;

    // Binary union with the base set.
    let lbu = inst_all(least_bin_union, &[tc.clone(), ta.clone(), u_img.clone()])?;
    if *lbu.concl()
        != Formula::imp(
            Formula::and(a_in_w, Formula::mem(u_img, w.clone())),
            Formula::mem(un.clone(), w.clone()),
        )
    {
        return None
    }
    let h_un = hyp_mp(&a1i(&lbu, h.clone()), &hyp_and(&h_a, &h_uimg)?)?;

    // And the reduction that was already proved.
    let g = inst_all(general, &[ta.clone(), tc])?;
    let dp_t = dp.of(ta);
    if *g.concl() != Formula::imp(Formula::mem(un, w.clone()), Formula::mem(dp_t.clone(), w.clone()))
    {
        return None
    }
    let out = syl(&h_un, &g)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(dp_t, w)),
        "dprod_in_universe_pair: wrong shape"
    );
    Some(gen_all(&[cv, av], &out))
}
