//! **Step 7** — what the same argument gives the function space.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀c ∀x ∀f. ((x ∈ U(c) ∧ f ∈ fs(x, U(c))) → f ∈ U(c))
//!                                             [least_universe_funspace_mem]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c))
//!                                          [funspace_subset_least_universe]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Note the `⊆` in the second, and what closes the gap
//!
//! [`funspace_subset_least_universe`] makes every *member* of `fs(a,b)` a member
//! of `U(c)`. That is **not** `fs(a,b) ∈ U(c)`, which is what
//! [`crate::funspace::funspace_in_universe_of`] wants, and the gap is one
//! application of `C₄`: refuting its equinumerosity disjunct needs a member of
//! `U(c)` surjecting onto `fs(a,b)`, for which the only candidate is
//! `𝒫(prod(a,b))` — so the obligation is `prod(a,b) ∈ U(c)`, hence
//! `(a ∪ b) ∈ U(c)`.
//!
//! That obligation was open when this file was written. It is **discharged**:
//! `(a ∪ b) ∈ U(c)` is [`crate::universe::least_universe_bin_union`] and
//! `prod(a,b) ∈ U(c)` is [`crate::funspace::product_in_universe`], so
//! [`crate::funspace::funspace_in_universe_pair`] proves
//! `(a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c)` outright — `crate::funspace`'s
//! header records the two-argument case as complete. No axiom was added to route
//! around anything.
//!
//! What this route *does* buy is that it reaches that point with **no product
//! and no binary union anywhere**: `f ∈ fs(a,b)` is a set of Kuratowski pairs of
//! members of `U(c)`, and [`least_universe_funspace_mem`] — the same transfer
//! through the intersection that [`super::least`] makes, over
//! [`super::funspace_mem_universe`] — puts each such `f` into `U(c)` directly.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::sums::Sums;
use crate::universe::is_universe;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mpr, inst_all, syl, uncurry};

use super::least::least_universe_subset;

/// `⊢ ∀c ∀x ∀f. ((x ∈ U(c) ∧ f ∈ fs(x, U(c))) → f ∈ U(c))` — the `U(c)` form of
/// [`crate::bound::funspace_mem_universe`], transferred through the intersection exactly as
/// [`crate::bound::least_universe_closed`] is.
///
/// `is_universe(U(c))` is not available, so this is not an instance: for each
/// universe `u ∋ c` we have `x ∈ u` and `U(c) ⊆ u`, so [`crate::wtype::fs_mono`]
/// re-aims `f` at `u` and [`crate::bound::funspace_mem_universe`] applies there.
pub fn least_universe_funspace_mem(
    env: &mut Env,
    s: &Sums,
    lu: FnSym,
    lu_ax: &Thm,
    fs_mono: &Thm,
    fs_mem: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (cv, xv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, tx, tf) = (Term::var(cv), Term::var(xv), Term::var(fv));
    let w = Term::apply(lu, vec![tc.clone()]);

    let x_in_w = Formula::mem(tx.clone(), w.clone());
    let f_in_fs_w = Formula::mem(tf.clone(), s.fs.of(tx.clone(), w.clone()));
    let h = Formula::and(x_in_w.clone(), f_in_fs_w.clone());
    let h_x = and_left(x_in_w, f_in_fs_w.clone());
    let h_f = and_right(Formula::mem(tx.clone(), w.clone()), f_in_fs_w.clone());

    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let univ_u = is_universe(env, &tu);
    let c_in_u = Formula::mem(tc.clone(), tu.clone());
    let a_univ = Formula::and(univ_u.clone(), c_in_u.clone());

    let k = Formula::and(h.clone(), a_univ.clone());
    let k_h = and_left(h.clone(), a_univ.clone());
    let k_au = and_right(h.clone(), a_univ.clone());
    let k_univ = syl(&k_au, &and_left(univ_u, c_in_u))?;

    let tr_x = crate::universe::least_universe_transfer(env, lu_ax, &tc, &tx, &tu).ok()?;
    let k_x_u = hyp_mp(&hyp_mp(&a1i(&tr_x, k.clone()), &syl(&k_h, &h_x)?)?, &k_au)?;

    let k_sub = syl(&k_au, &least_universe_subset(env, lu_ax, &tc, &w, &tu)?)?;
    let mono_at = inst_all(fs_mono, &[tx.clone(), w.clone(), tu.clone(), tf.clone()])?;
    let f_in_fs_u = Formula::mem(tf.clone(), s.fs.of(tx.clone(), tu.clone()));
    if *mono_at.concl()
        != Formula::imp(
            Formula::and(f_in_fs_w, kernel::thm::subset(env, w.clone(), tu.clone())),
            f_in_fs_u.clone(),
        )
    {
        return None
    }
    let k_f_u = syl(&hyp_and(&syl(&k_h, &h_f)?, &k_sub)?, &mono_at)?;

    let mem_at = inst_all(fs_mem, &[tu.clone(), tx.clone(), tf.clone()])?;
    if *mem_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(Formula::mem(tx.clone(), tu.clone()), f_in_fs_u),
            ),
            Formula::mem(tf.clone(), tu.clone()),
        )
    {
        return None
    }
    let k_goal =
        hyp_mp(&a1i(&mem_at, k.clone()), &hyp_and(&k_univ, &hyp_and(&k_x_u, &k_f_u)?)?)?;

    let h_all = Thm::mp(
        &Thm::ax_dist(uv, h.clone(), Formula::imp(a_univ, Formula::mem(tf.clone(), tu)))?,
        &Thm::gen(uv, &uncurry(&k_goal)?),
    )?;
    if *h_all.concl()
        != Formula::imp(h.clone(), crate::universe::in_all_universes(env, &tc, &tf))
    {
        return None
    }
    let out = syl(&h_all, &iff_mpr(&crate::universe::least_universe_mem(lu_ax, &tc, &tf).ok()?)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tf, w)),
        "least_universe_funspace_mem: wrong shape"
    );
    Some(gen_all(&[cv, xv, fv], &out))
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c))` — **every function
/// between members of `U(c)` is a member of `U(c)`**.
///
/// `b ⊆ U(c)` by transitivity ([`crate::universe::least_universe_transitive`]),
/// so [`crate::wtype::fs_mono`] makes a member of `fs(a,b)` a member of
/// `fs(a, U(c))`, and [`least_universe_funspace_mem`] puts it in `U(c)`.
///
/// # What this is not, and what is missing
///
/// It is **not** `fs(a,b) ∈ U(c)`, the strengthening
/// [`crate::funspace::funspace_in_universe_of`] would want. Getting there needs
/// one more application of `C₄`, whose equinumerosity disjunct has to be
/// refuted by exhibiting a member of `U(c)` that surjects onto `fs(a,b)` — and
/// the only candidate is `𝒫(prod(a,b))`, so the remaining obligation is exactly
///
/// ```text
/// (a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c)
/// ```
///
/// which reduces in turn to `(a ∪ b) ∈ U(c)` through
/// [`crate::funspace::product_subset_pow_pow`]. That is the binary-union
/// closure `funspace_in_universe_of` has always carried as its antecedent. It
/// is *not* refutable, and it is not out of reach either: `a ∪ b ⊆ U(c)`, so
/// `C₄` offers `a ∪ b ≈ u` or `a ∪ b ∈ u` in each universe `u ∋ c`, and a
/// bijection `h : a ∪ b → u` would make `u` the union of the two members
/// `h[a], h[b] ∈ u` (each a member by
/// [`crate::cantor::image_in_universe`], each image built by one Separation on
/// `u`) — whereupon `h[a] ∈ h[b]` and `h[b] ∈ h[a]`, a two-cycle Regularity
/// refutes. Nothing in that sketch is derived here: it needs the image sets, an
/// unpacking of `equinumerous`, and a no-two-cycle lemma, and the W-type's
/// bound — which is what this module exists for — never needs it.
pub fn funspace_subset_least_universe(
    env: &mut Env,
    s: &Sums,
    lu: FnSym,
    c1: &Thm,
    fs_mono: &Thm,
    fs_mem_lu: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (cv, av, bv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb, tf) = (Term::var(cv), Term::var(av), Term::var(bv), Term::var(fv));
    let w = Term::apply(lu, vec![tc.clone()]);

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let b_in_w = Formula::mem(tb.clone(), w.clone());
    let h = Formula::and(a_in_w.clone(), b_in_w.clone());
    let h_a = and_left(a_in_w.clone(), b_in_w.clone());
    let h_b = and_right(a_in_w, b_in_w);

    // `b ⊆ U(c)`, from transitivity at `b`.
    let c1_at = inst_all(c1, std::slice::from_ref(&tc))?;
    let c1_b = inst_all(&c1_at, std::slice::from_ref(&tb))?;
    let h_sub = hyp_mp(&a1i(&c1_b, h.clone()), &h_b)?;
    let sub_b_w = kernel::thm::subset(env, tb.clone(), w.clone());
    if *h_sub.concl() != Formula::imp(h.clone(), sub_b_w.clone()) {
        return None
    }

    // A member of `fs(a,b)` is a member of `fs(a, U(c))`, hence of `U(c)`.
    let f_in_fs = Formula::mem(tf.clone(), s.fs.of(ta.clone(), tb.clone()));
    let l = Formula::and(h.clone(), f_in_fs.clone());
    let l_h = and_left(h.clone(), f_in_fs.clone());
    let l_f = and_right(h.clone(), f_in_fs.clone());

    let mono_at = inst_all(fs_mono, &[ta.clone(), tb.clone(), w.clone(), tf.clone()])?;
    let f_in_fs_w = Formula::mem(tf.clone(), s.fs.of(ta.clone(), w.clone()));
    if *mono_at.concl() != Formula::imp(Formula::and(f_in_fs.clone(), sub_b_w), f_in_fs_w.clone())
    {
        return None
    }
    let l_f_w = syl(&hyp_and(&l_f, &syl(&l_h, &h_sub)?)?, &mono_at)?;

    let mem_at = inst_all(fs_mem_lu, &[tc.clone(), ta.clone(), tf.clone()])?;
    if *mem_at.concl()
        != Formula::imp(
            Formula::and(Formula::mem(ta.clone(), w.clone()), f_in_fs_w),
            Formula::mem(tf.clone(), w.clone()),
        )
    {
        return None
    }
    let l_goal = hyp_mp(&a1i(&mem_at, l.clone()), &hyp_and(&syl(&l_h, &h_a)?, &l_f_w)?)?;

    let out = Thm::mp(
        &Thm::ax_dist(
            fv,
            h.clone(),
            Formula::imp(f_in_fs, Formula::mem(tf.clone(), w.clone())),
        )?,
        &Thm::gen(fv, &uncurry(&l_goal)?),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::subset(env, s.fs.of(ta, tb), w)),
        "funspace_subset_least_universe: wrong shape"
    );
    Some(gen_all(&[cv, av, bv], &out))
}
