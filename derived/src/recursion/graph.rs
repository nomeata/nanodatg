//! Reading a value off a function graph.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀f ∀a ∀b. ((SingleValued(f) ∧ ⟨a,b⟩ ∈ f) → app(f,a) = b)   [app_of_graph]
//! ```
//!
//! `SingleValued` is [`crate::funspace::is_single_valued`] and `app` is
//! [`crate::funcs::Apply`]'s. Callers need none of the derivation below.
//!
//! # Why the general form is needed
//!
//! This is the bridge between the *graph* view of a function (a set of ordered
//! pairs) and the *application* view, in the direction the recursion theorem
//! needs: every step of the approximation argument establishes membership of a
//! pair in a graph and then has to talk about `app`.
//!
//! [`crate::funcs::beta_conditional`] is the same bridge for the special case of
//! a graph built by [`crate::funcs::lambda`], where the value is given by a
//! function symbol. That is exactly the case recursion cannot use — the values
//! are produced step by step, not by a term — so the general form is derived
//! here. The argument is the same: `coll(f,a)` is `{b}`, single-valuedness
//! closing the forward inclusion and the pair itself the backward one, and `app`
//! strips the union off a singleton.

use kernel::{Env, Formula, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, mpd_const, singleton, syl, uncurry,
};

/// `⊢ ∀f ∀a ∀b. ((SingleValued(f) ∧ ⟨a,b⟩ ∈ f) → app(f,a) = b)`.
///
/// The bridge between the *graph* view of a function (a set of ordered pairs)
/// and the *application* view, in the direction the recursion theorem needs:
/// every step of the approximation argument establishes membership of a pair in
/// a graph and then has to talk about `app`.
///
/// [`crate::funcs::beta_conditional`] is the same bridge for the special case
/// of a graph built by [`crate::funcs::lambda`], where the value is given by a
/// function symbol. That is exactly the case recursion cannot use — the values
/// are produced step by step, not by a term — so the general form is derived
/// here. The argument is the same: `coll(f,a)` is `{b}`, single-valuedness
/// closing the forward inclusion and the pair itself the backward one, and
/// `app` strips the union off a singleton.
pub fn app_of_graph(env: &mut Env, ap: &crate::funcs::Apply) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (f, a, b, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tb, ty) = (Term::var(f), Term::var(a), Term::var(b), Term::var(y));

    let sv = crate::funspace::is_single_valued(env, &ap.sets, &tf);
    let mem_ab = Formula::mem(ap.sets.pair(ta.clone(), tb.clone()), tf.clone());
    let h = Formula::and(sv.clone(), mem_ab.clone());
    let h_sv = and_left(sv.clone(), mem_ab.clone());
    let h_ab = and_right(sv.clone(), mem_ab.clone());

    let coll_term = ap.coll_of(tf.clone(), ta.clone());
    let sing = singleton(ap.sets.up, tb.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let mem_ys = Formula::mem(ty.clone(), sing.clone());

    let coll_at = inst_all(&ap.coll_members, &[tf.clone(), ta.clone(), ty.clone()])?;
    let ms = inst_all(&ap.mem_sing, &[tb.clone(), ty.clone()])?;

    // Single-valuedness at `(a, y, b)`.
    let s1 = Thm::ax_inst(sv.clone(), ta.clone())?;
    let (_, s1b) = s1.concl().as_imp()?;
    let s2 = syl(&s1, &Thm::ax_inst(s1b, ty.clone())?)?;
    let (_, s2b) = s2.concl().as_imp()?;
    let sv_inst = syl(&s2, &Thm::ax_inst(s2b, tb.clone())?)?;

    // ── `H → (y ∈ coll(f,a) → y ∈ {b})` ─────────────────────────────────────
    let k = Formula::and(h.clone(), mem_yc.clone());
    let k_h = and_left(h.clone(), mem_yc.clone());
    let k_yc = and_right(h.clone(), mem_yc.clone());
    let k_ay = hyp_mp(&a1i(&iff_mp(&coll_at)?, k.clone()), &k_yc)?;
    let k_ab = syl(&k_h, &h_ab)?;
    let k_sv = syl(&k_h, &h_sv)?;
    let k_eq = hyp_mp(&syl(&k_sv, &sv_inst)?, &hyp_and(&k_ay, &k_ab)?)?;
    let h_fwd = uncurry(&syl(&k_eq, &iff_mpr(&ms)?)?)?;

    // ── `H → (y ∈ {b} → y ∈ coll(f,a))` ─────────────────────────────────────
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        tb.clone(),
        ty.clone(),
        hole,
        Formula::mem(ap.sets.pair(ta.clone(), Term::var(hole)), tf.clone()),
    );
    let pre = syl(&iff_mp(&ms)?, &eq_symm_imp(env, ty.clone(), tb.clone()))?;
    let h_step = syl(&h_ab, &com12(&leib)?)?;
    let h_to_pair = crate::separation::hyp_syl(&a1i(&pre, h.clone()), &h_step)?;
    let h_bwd = crate::separation::hyp_syl(&h_to_pair, &a1i(&iff_mpr(&coll_at)?, h.clone()))?;

    // ── Extensionality, then strip the union ────────────────────────────────
    let h_all = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(y, &hyp_and(&h_fwd, &h_bwd)?),
    )?;
    let h_coll_eq = syl(&h_all, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w1 = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(
            coll_term,
            sing,
            w1,
            Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w1))),
        ),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_term = ap.apply(tf.clone(), ta.clone());
    let app_def = inst_all(&ap.app_ax, &[tf.clone(), ta.clone()])?;
    let w2 = env.fresh_var();
    let carry = Thm::eq_leibniz(ucoll, using.clone(), w2, Formula::eq(app_term.clone(), Term::var(w2)));
    let h_app_using =
        hyp_mp(&hyp_mp(&a1i(&carry, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w3 = env.fresh_var();
    let carry2 = Thm::mp(
        &Thm::eq_leibniz(using, tb.clone(), w3, Formula::eq(app_term.clone(), Term::var(w3))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&tb))?,
    )?;
    let out = syl(&h_app_using, &carry2)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(app_term, tb)),
        "app_of_graph: unexpected shape"
    );
    Some(gen_all(&[f, a, b], &out))
}
