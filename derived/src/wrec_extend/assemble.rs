//! The three clauses assembled, and the point they were assembled for.
//!
//! # Interface
//!
//! ```text
//! extension(…)  ⟶  Extension { sv, in_pow, rec_cond, attempt, indom }
//! ```
//!
//! — **five separate theorems**, each of the form
//! `⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (K → …)` with `K` the induction step's hypothesis
//! ([`super::hypothesis`]); the hub header
//! ([`crate::wrec_extend`]) lists all five in full. There is no export of the
//! conjunction `G ∈ Att ∧ app(G,⟨a,f⟩) = v`: the value equation is internal,
//! proved by [`super::value::value_at_new_point`] and consumed here, and the
//! membership `G ∈ Att` is [`Extension::attempt`] on its own.
//!
//! Callers need none of the derivations in the sibling files.
//!
//! # What it is for
//!
//! **This is the induction step of totality.** [`crate::wrec_total`] proves that
//! the recursor is defined everywhere on the W-type by structural induction, and
//! the step is: given that every subterm is in the recursor's domain, put
//! `⟨a,f⟩` in as well. The only way to do that is to exhibit an *attempt*
//! containing it — attempts are what `wrec` is the union of — and the attempt is
//! `g` extended by one pair, which is this module.
//!
//! Everything else in [`crate::wrec_extend`] exists to discharge the three
//! clauses of the attempt condition for that one extra pair.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::wrec::indom;
use crate::wrec_total::Recursor;
use crate::wtype::Wtype;
use crate::{a1i, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mpr, inst_all, syl};

use super::shared::hyp_inst;
use super::terms::Cx;
use super::value::value_at_new_point;
use super::single_valued::extension_single_valued;
use super::product::extension_in_product;
use super::recursion::{agreement, extension_recursion_condition};

/// What [`extension`] derives, each statement generalised over all seven
/// parameters `A`, `B`, `u`, `T`, `e`, `a`, `f`, and each with the induction
/// step's hypothesis [`super::hypothesis`] as its antecedent.
pub struct Extension {
    /// `⊢ ∀…. (K → sv(G))`.
    pub sv: Thm,
    /// `⊢ ∀…. (K → G ∈ 𝒫(prod(W(A,B,u), T)))`.
    pub in_pow: Thm,
    /// `⊢ ∀…. (K → rec_cond(B,e,G))`.
    pub rec_cond: Thm,
    /// `⊢ ∀…. (K → G ∈ Att(A,B,u,T,e))`.
    pub attempt: Thm,
    /// `⊢ ∀…. (K → indom(wrec(A,B,u,T,e), ⟨a,f⟩))` — **the induction step**.
    pub indom: Thm,
}

/// **The one-point extension is an attempt, so `⟨a,f⟩` is in the recursor's
/// domain.**
///
/// The three clauses of [`crate::wrec::attempt_cond`] are
/// `extension_in_product`, `extension_single_valued` and
/// `extension_recursion_condition`; `Att`'s Separation condition then makes
/// `G` an attempt, and [`crate::wrec::attempt_indom_wrec`] moves `⟨a,f⟩ ∈ dom G`
/// — which holds because the new pair is in `G` — across to `dom wrec`.
///
/// All five statements are built in one pass because they share the context and
/// the two expensive lemmas `value_at_new_point` and `agreement`.
pub fn extension(env: &mut Env, wt: &Wtype, r: &Recursor) -> Option<Extension> {
    let vars: Vec<FreeVar> = (0..7).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let cx = Cx::new(env, wt, r, &ts[0..5], &ts[5], &ts[6])?;
    let s = &wt.sums;

    let at_new = value_at_new_point(env, wt, r, &cx)?;
    let sv = extension_single_valued(env, wt, r, &cx, &at_new)?;
    let in_pow = extension_in_product(env, wt, r, &cx)?;
    let agree = agreement(env, wt, r, &cx, &sv)?;
    let rc = extension_recursion_condition(env, wt, r, &cx, &sv, &agree)?;

    // The three clauses, through `Att`'s membership condition.
    let mut with_g = cx.ps.clone();
    with_g.push(cx.g.clone());
    let att = syl(
        &hyp_and(&in_pow, &hyp_and(&sv, &rc)?)?,
        &iff_mpr(&inst_all(&r.att_ax, &with_g)?)?,
    )?;

    // `⟨a,f⟩ ∈ dom G ⊆ dom wrec`.
    let yv = env.fresh_var();
    let in_dom_g = Thm::mp(
        &exists_intro_imp(
            yv,
            Formula::mem(s.ap.sets.pair(cx.w0.clone(), Term::var(yv)), cx.g.clone()),
            cx.v.clone(),
        )?,
        &cx.new_pair(s)?,
    )?;
    let in_dom = hyp_mp(
        &hyp_inst(
            &syl(&att, &inst_all(&r.mono, &with_g)?)?,
            std::slice::from_ref(&cx.w0),
        )?,
        &a1i(&in_dom_g, cx.k.clone()),
    )?;
    debug_assert_eq!(
        *in_dom.concl(),
        Formula::imp(cx.k.clone(), indom(env, &s.ap, &cx.rec_t, &cx.w0)),
        "extension: the induction step has the wrong shape"
    );

    Some(Extension {
        sv: gen_all(&vars, &sv),
        in_pow: gen_all(&vars, &in_pow),
        rec_cond: gen_all(&vars, &rc),
        attempt: gen_all(&vars, &att),
        indom: gen_all(&vars, &in_dom),
    })
}
