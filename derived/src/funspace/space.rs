//! The function space `fs(a,b) = a → b`.
//!
//! # Interface
//!
//! With the three clauses
//!
//! ```text
//! is_total(a,b,f)        :=  ∀x. (x ∈ a → ∃y. (y ∈ b ∧ ⟨x,y⟩ ∈ f))
//! is_single_valued(f)    :=  ∀x ∀y ∀y′. ((⟨x,y⟩ ∈ f ∧ ⟨x,y′⟩ ∈ f) → y = y′)
//! isfun(a,b,f)           :=  f ⊆ prod(a,b) ∧ (is_total(a,b,f) ∧ is_single_valued(f))
//! ```
//!
//! the last being [`is_function`], the exports are
//!
//! ```text
//! ⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(a,b,f))     [funspace, checked by funspace_members]
//! ⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))              [funspace_subset_pow_prod]
//! ```
//!
//! Both hold with **no antecedent**, for every `a` and `b` rather than only on
//! the diagonal. [`Funspace`] bundles the symbol with both. Callers need none of
//! the derivations below.
//!
//! # The antecedent that used to survive
//!
//! The function space *is* carved out of a power set by a condition, and `a → b`
//! really is empty when `a` is inhabited and `b` is not. For as long as
//! Separation needed its result inhabited, `fs(a,b)` had to be defined by the
//! same total-by-default trick [`crate::funcs::collection`] used —
//!
//! ```text
//! f ∈ fs(a,b)  ↔  isfun(f)  ∨  (¬∃g. isfun(g)  ∧  f ∈ 𝒫prod(a,b))
//! ```
//!
//! — with the intended condition recoverable only under `∃g. isfun(g)`,
//! dischargeable only on the diagonal via the identity function. `∅` removes all
//! of that: [`crate::funcs::separation_full`] produces the separated set whether
//! or not it is inhabited, so [`funspace`] defines the intended condition
//! outright.
//!
//! What [`funspace_members`] adds is the *check*: it rebuilds `isfun(f)` from
//! [`is_function`] independently and refuses unless the defining theorem
//! characterises `fs(a,b)` by precisely that. A symbol defined by some other
//! condition would give a true theorem about the wrong set, silently, and that
//! is what the comparison rules out.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{hyp_syl, Sets};
use crate::{
    a1i, and_left, and_right, define_by_membership, exists_mono, gen_all, hyp_and, hyp_iff_mp,
    hyp_iff_mpr, iff_mp, iff_mpr, inst_all, syl,
};
use super::cartesian::Product;

/// `∀x. (x ∈ a → ∃y. (y ∈ b ∧ ⟨x,y⟩ ∈ f))` — `f` is total on `a`, with values
/// in `b`.
pub fn is_total(env: &mut Env, sets: &Sets, a: &Term, b: &Term, f: &Term) -> Formula {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let body = Formula::and(
        Formula::mem(ty.clone(), b.clone()),
        Formula::mem(sets.pair(tx.clone(), ty), f.clone()),
    );
    Formula::forall(x, Formula::imp(Formula::mem(tx, a.clone()), Formula::exists(y, body)))
}

/// `∀x ∀y ∀y′. ((⟨x,y⟩ ∈ f ∧ ⟨x,y′⟩ ∈ f) → y = y′)` — `f` is single-valued.
pub fn is_single_valued(env: &mut Env, sets: &Sets, f: &Term) -> Formula {
    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));
    let hyp = Formula::and(
        Formula::mem(sets.pair(tx.clone(), ty.clone()), f.clone()),
        Formula::mem(sets.pair(tx, ty2.clone()), f.clone()),
    );
    Formula::forall(
        x,
        Formula::forall(y, Formula::forall(y2, Formula::imp(hyp, Formula::eq(ty, ty2)))),
    )
}

/// `f ⊆ prod(a,b) ∧ (f total on a ∧ f single-valued)` — "`f` is a function from
/// `a` to `b`", as a formula.
pub fn is_function(
    env: &mut Env,
    sets: &Sets,
    p: &Product,
    a: &Term,
    b: &Term,
    f: &Term,
) -> Formula {
    let sub = kernel::thm::subset(env, f.clone(), p.of(a.clone(), b.clone()));
    Formula::and(sub, graph_condition(env, sets, a, b, f))
}

/// `f total on a ∧ f single-valued` — the half of [`is_function`] that
/// Separation carves with.
fn graph_condition(env: &mut Env, sets: &Sets, a: &Term, b: &Term, f: &Term) -> Formula {
    Formula::and(is_total(env, sets, a, b, f), is_single_valued(env, sets, f))
}

/// The function space `fs(a,b) = a → b`.
#[derive(Clone)]
pub struct Funspace {
    /// The symbol itself.
    pub fs: FnSym,
    /// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))` — the defining axiom, which is
    /// now the intended condition and nothing else.
    pub fs_def: Thm,
    /// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))` — the same statement, with
    /// [`funspace_members`] having rebuilt `isfun` independently and checked it
    /// against the defining axiom.
    pub fs_ax: Thm,
    /// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))`.
    pub fs_sub: Thm,
}

impl Funspace {
    /// Introduce `fs` and prove both lemmas about it.
    ///
    /// `empty` must be a proof `⊢ ∀z. ¬(z ∈ e)` — [`crate::funspace::Space::empty_ax`] is one.
    /// It is consumed by Separation and appears in none of the results.
    pub fn new(
        env: &mut Env,
        sets: &Sets,
        pow: FnSym,
        pow_ax: &Thm,
        p: &Product,
        empty: &Thm,
    ) -> Option<Funspace> {
        let (fs, fs_def) = funspace(env, sets, pow, pow_ax, p, empty)?;
        let fs_ax = funspace_members(env, sets, p, fs, &fs_def)?;
        let fs_sub = funspace_subset_pow_prod(env, sets, pow, pow_ax, p, fs, &fs_def)?;
        Some(Funspace { fs, fs_def, fs_ax, fs_sub })
    }

    /// The term `fs(a,b)`.
    pub fn of(&self, a: Term, b: Term) -> Term { Term::apply(self.fs, vec![a, b]) }
}

/// Introduce `fs(a,b) = a → b`, with
/// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))`.
///
/// **The condition defined is the intended one.** The function space is carved
/// out of `𝒫(prod(a,b))` by a condition, and `a → b` really is empty when `a`
/// is inhabited and `b` is not — so for as long as Separation needed its result
/// to be inhabited, the symbol could only be made total by a default disjunct,
///
/// ```text
/// f ∈ fs(a,b)  ↔  isfun(f)  ∨  (¬∃g. isfun(g)  ∧  f ∈ 𝒫prod(a,b))
/// ```
///
/// with the intended condition recoverable only under the antecedent
/// `∃g. isfun(g)`. With `∅` in hand [`crate::funcs::separation_full`] produces
/// the set outright, empty or not, and the disjunct is gone.
///
/// The only work left is cosmetic: Separation carves by `f ∈ 𝒫prod(a,b) ∧ ψ`
/// and the lemma is stated with `f ⊆ prod(a,b) ∧ ψ`, so the two are swapped
/// inside the existential using the Power Set characterisation.
pub fn funspace(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    pow_ax: &Thm,
    p: &Product,
    empty: &Thm,
) -> Option<(FnSym, Thm)> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let prod_t = p.of(ta.clone(), tb.clone());
    let pp = Term::apply(pow, vec![prod_t.clone()]);
    let l = is_function(env, sets, p, &ta, &tb, &tf);

    let sub = kernel::thm::subset(env, tf.clone(), prod_t.clone());
    let psi = graph_condition(env, sets, &ta, &tb, &tf);
    debug_assert_eq!(l, Formula::and(sub.clone(), psi.clone()), "funspace: condition shape drift");

    let mem_pp = Formula::mem(tf.clone(), pp.clone());
    let sep_cond = Formula::and(mem_pp.clone(), psi.clone());

    // `f ∈ 𝒫prod(a,b) ↔ f ⊆ prod(a,b)`, the only difference between the shape
    // Separation produces and the shape the lemma is stated in.
    let pow_at_f = inst_all(pow_ax, &[prod_t, tf.clone()])?;
    let l_to_sep = hyp_and(
        &syl(&and_left(sub.clone(), psi.clone()), &iff_mpr(&pow_at_f)?)?,
        &and_right(sub, psi.clone()),
    )?;
    let sep_to_l = hyp_and(
        &syl(&and_left(mem_pp.clone(), psi.clone()), &iff_mp(&pow_at_f)?)?,
        &and_right(mem_pp, psi.clone()),
    )?;

    let sep = crate::funcs::separation_full(env, f, &psi, &pp, empty)?;

    // Swap the carved condition for `isfun` inside the existential.
    let sv = env.fresh_var();
    let mem_fs = Formula::mem(tf.clone(), Term::var(sv));
    let p_s = Formula::forall(f, Formula::iff(mem_fs.clone(), sep_cond));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(sv, p_s.clone()),
        "funspace: Separation has an unexpected shape"
    );

    let p_inst = Thm::ax_inst(p_s.clone(), tf.clone())?;
    let p_fwd = hyp_syl(&hyp_iff_mp(&p_inst)?, &a1i(&sep_to_l, p_s.clone()))?;
    let p_bwd = hyp_syl(&a1i(&l_to_sep, p_s.clone()), &hyp_iff_mpr(&p_inst)?)?;
    let p_q = Thm::mp(
        &Thm::ax_dist(f, p_s.clone(), Formula::iff(mem_fs, l.clone()))?,
        &Thm::gen(f, &hyp_and(&p_fwd, &p_bwd)?),
    )?;
    let existence = Thm::mp(&exists_mono(sv, &Thm::gen(sv, &p_q))?, &sep)?;

    define_by_membership(env, &[a, b], &existence, f, &l)
}

/// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))` — step 6 of the chain.
///
/// A member of `fs(a,b)` is a function, and a function is a subset of the
/// product, hence a member of its power set. (This was already unconditional
/// when `fs` carried a default disjunct — the default was chosen to be
/// `𝒫(prod(a,b))` precisely so that it would be. Now there is only one case.)
pub fn funspace_subset_pow_prod(
    env: &mut Env,
    sets: &Sets,
    pow: FnSym,
    pow_ax: &Thm,
    p: &Product,
    fs: FnSym,
    fs_def: &Thm,
) -> Option<Thm> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let prod_t = p.of(ta.clone(), tb.clone());
    let pp = Term::apply(pow, vec![prod_t.clone()]);
    let l = is_function(env, sets, p, &ta, &tb, &tf);

    let sub = kernel::thm::subset(env, tf.clone(), prod_t.clone());
    let psi = graph_condition(env, sets, &ta, &tb, &tf);
    debug_assert_eq!(l, Formula::and(sub.clone(), psi.clone()));

    let pow_at_f = inst_all(pow_ax, &[prod_t, tf.clone()])?;
    let l_mem = syl(&and_left(sub, psi), &iff_mpr(&pow_at_f)?)?;

    let fs_at_f = inst_all(fs_def, &[ta.clone(), tb.clone(), tf.clone()])?;
    let fs_t = Term::apply(fs, vec![ta.clone(), tb.clone()]);
    debug_assert_eq!(
        *fs_at_f.concl(),
        Formula::iff(Formula::mem(tf.clone(), fs_t.clone()), l),
        "funspace's defining axiom has an unexpected shape"
    );
    let out = Thm::gen(f, &syl(&iff_mp(&fs_at_f)?, &l_mem)?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, fs_t, pp),
        "funspace_subset_pow_prod: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

/// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))` — the members of the function space
/// are the functions, **unconditionally**.
///
/// This used to be conditional on `∃g. isfun(g)`, that being the hypothesis
/// under which [`funspace`]'s default disjunct was dead. There is no default
/// any more, so the statement is exactly the defining axiom — and what this
/// function adds is the *check*: it rebuilds `isfun(f)` from
/// [`is_function`] independently and refuses unless `fs_def` characterises
/// `fs(a,b)` by precisely that. A symbol defined by some other condition would
/// give a true theorem about the wrong set, silently, and that is what the
/// comparison rules out.
pub fn funspace_members(
    env: &mut Env,
    sets: &Sets,
    p: &Product,
    fs: FnSym,
    fs_def: &Thm,
) -> Option<Thm> {
    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let l = is_function(env, sets, p, &ta, &tb, &tf);
    let fs_t = Term::apply(fs, vec![ta.clone(), tb.clone()]);
    let expected = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(f, Formula::iff(Formula::mem(tf, fs_t), l)),
        ),
    );
    if *fs_def.concl() != expected {
        return None
    }
    Some(fs_def.clone())
}
