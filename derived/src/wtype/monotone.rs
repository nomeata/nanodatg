//! **Step 1** — the function space is monotone in its target.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀X ∀Y ∀Z ∀f. ((f ∈ fs(X,Y) ∧ Y ⊆ Z) → f ∈ fs(X,Z))                [fs_mono]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why the W-type needs it
//!
//! It is what lets a function into a *smaller* closed set be fed to the closure
//! hypothesis of a *larger* one, which is the move [`super::induction`] makes and
//! the move [`crate::bound::least_universe_closed`] makes when it transfers a
//! closure property from an arbitrary universe down to `U(c)`. Without it the
//! intersection could not be shown closed, because a witness `f ∈ fs(B(a), W)`
//! has to be reused at every `S ⊇ W` in the intersection.
//!
//! The derivation is [`crate::ext::funspace_retarget`] with the values relocated
//! by [`crate::ext::values_in`]: `fs` only ever constrains a function through
//! its values, so a codomain may be swapped for any set the values land in, and
//! `Y ⊆ Z` says exactly that.

use kernel::{Env, Formula, Term, Thm};
use crate::ext::values_in;
use crate::sums::Sums;
use crate::{and_left, and_right, gen_all, hyp_and, hyp_mp, inst_all, syl, uncurry};


/// `⊢ ∀X ∀Y ∀Z ∀f. ((f ∈ fs(X,Y) ∧ Y ⊆ Z) → f ∈ fs(X,Z))` — enlarging the
/// codomain keeps a function a function.
///
/// Used at every step below, because the whole W-type argument consists of
/// moving one `f ∈ fs(B(a), ·)` between the various closed sets. It is *not*
/// re-derived from the three `isfun` clauses: [`crate::ext::funspace_app_mem`]
/// puts the values in `Y`, the inclusion moves them to `Z`, and
/// [`crate::ext::funspace_retarget`] — which already does the clause-by-clause
/// work — swaps the codomain.
///
/// `app_mem` and `retarget` must be what those two produce for `s`'s own
/// apparatus; a mismatch makes the composition fail and this returns `None`.
pub fn fs_mono(env: &mut Env, s: &Sums, app_mem: &Thm, retarget: &Thm) -> Option<Thm> {
    let (xv, yv, zv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tz, tf) = (Term::var(xv), Term::var(yv), Term::var(zv), Term::var(fv));

    let sub_yz = kernel::thm::subset(env, ty.clone(), tz.clone());
    let mem_fs_y = Formula::mem(tf.clone(), s.fs.of(tx.clone(), ty.clone()));
    let h = Formula::and(mem_fs_y.clone(), sub_yz.clone());

    // ── H → ∀x. (x ∈ X → app(f,x) ∈ Z) ───────────────────────────────────────
    let pv = env.fresh_var();
    let tp = Term::var(pv);
    let mem_px = Formula::mem(tp.clone(), tx.clone());
    let app_t = s.ap.apply(tf.clone(), tp.clone());
    let k = Formula::and(h.clone(), mem_px.clone());

    let k_h = and_left(h.clone(), mem_px.clone());
    let k_fs = syl(&k_h, &and_left(mem_fs_y.clone(), sub_yz.clone()))?;
    let k_px = and_right(h.clone(), mem_px.clone());
    let am = inst_all(app_mem, &[tx.clone(), ty.clone(), tf.clone(), tp.clone()])?;
    if *am.concl()
        != Formula::imp(
            Formula::and(mem_fs_y.clone(), mem_px.clone()),
            Formula::mem(app_t.clone(), ty.clone()),
        )
    {
        return None
    }
    let k_app_y = syl(&hyp_and(&k_fs, &k_px)?, &am)?;

    let k_sub = syl(&k_h, &and_right(mem_fs_y.clone(), sub_yz.clone()))?;
    let sub_at = Thm::ax_inst(sub_yz.clone(), app_t.clone())?;
    let k_app_z = hyp_mp(&syl(&k_sub, &sub_at)?, &k_app_y)?;
    debug_assert_eq!(
        *k_app_z.concl(),
        Formula::imp(k, Formula::mem(app_t.clone(), tz.clone())),
        "fs_mono: unexpected shape for the pointwise step"
    );

    let vi = values_in(env, &s.ap, &tx, &tz, &tf);
    let h_vi = Thm::mp(
        &Thm::ax_dist(
            pv,
            h.clone(),
            Formula::imp(mem_px, Formula::mem(app_t, tz.clone())),
        )?,
        &Thm::gen(pv, &uncurry(&k_app_z)?),
    )?;
    if *h_vi.concl() != Formula::imp(h.clone(), vi.clone()) {
        return None
    }

    // ── and then the codomain swap ───────────────────────────────────────────
    let rt = inst_all(retarget, &[tx.clone(), ty.clone(), tz.clone(), tf.clone()])?;
    let mem_fs_z = Formula::mem(tf.clone(), s.fs.of(tx.clone(), tz.clone()));
    if *rt.concl() != Formula::imp(Formula::and(mem_fs_y.clone(), vi), mem_fs_z.clone()) {
        return None
    }
    let h_fs = and_left(mem_fs_y, sub_yz);
    let out = syl(&hyp_and(&h_fs, &h_vi)?, &rt)?;

    debug_assert_eq!(*out.concl(), Formula::imp(h, mem_fs_z), "fs_mono: unexpected shape");
    Some(gen_all(&[xv, yv, zv, fv], &out))
}
