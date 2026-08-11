//! The Peano properties of `ω`.
//!
//! # Interface
//!
//! Writing `Trans(n)` for [`crate::empty::transitive`], the exports are
//!
//! ```text
//! ⊢ t ∈ succ(t)                                                  [mem_succ_self]
//! ⊢ ∀n. (n ∈ ω → Trans(n))                                       [omega_trans]
//! ⊢ ∀n. ¬(succ(n) = 0)                                    [succ_ne_zero_pair.0]
//! ⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))                                 [succ_ne_zero]
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (succ(m) = succ(n) → m = n))       [succ_inj]
//! ```
//!
//! and [`Peano`] bundles those with the induction principle, `0 ∈ ω`, closure
//! under `succ` and `⊢ ∀x. ¬(x ∈ x)` in one struct — [`Peano::with_sets`] is the
//! entry point, and no caller needs any of the derivations below.
//!
//! **Nothing is conditional and no axiom was added.** The `n ∈ ω` antecedent on
//! [`succ_ne_zero`] is not used — the statement holds for every set — but it is
//! the form the Peano axioms are stated in, so it is the form given.
//! [`Peano::succ_ne_zero_un`] is the *un*weakened theorem the same derivation
//! passes through, exported beside it because a term-level caller has no `∈ ω`
//! to spend; [`succ_ne_zero_pair`] says which caller and why.
//!
//! # Where the content is
//!
//! [`omega_trans`] is an induction gluing [`crate::recursion::trans_empty`] to
//! [`crate::recursion::trans_succ`]; the gluing is the part that needs `ω` to be
//! *least*, and it is exactly what a construction helping itself to "the
//! naturals are transitive" would be skipping. [`succ_inj`] is the one that
//! consumes it: from `succ(m) = succ(n)` the two memberships give `m ∈ n ∨ m = n`
//! and `n ∈ m ∨ n = m`, and the only case to close off is `m ∈ n` together with
//! `n ∈ m`, which transitivity turns into `m ∈ m` and Regularity refutes
//! ([`crate::empty::no_self_mem`]).

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::separation::or_intro_right;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, gen_all, hyp_and, hyp_mp, hyp_or_elim,
    iff_mp, iff_mpr, imp_refl, inst_all, mpd_const, syl, uncurry,
};
use super::succ::{trans_empty, trans_succ};
use super::naturals::OmegaCore;
use super::induction::{induction_principle, induction_scheme};

/// `⊢ t ∈ succ(t)` for a caller-supplied term — the right disjunct of the
/// successor's membership condition, discharged by reflexivity.
pub fn mem_succ_self(core: &OmegaCore, t: &Term) -> Option<Thm> {
    let at = inst_all(&core.succ_ax, &[t.clone(), t.clone()])?;
    let disj = Thm::mp(
        &or_intro_right(Formula::mem(t.clone(), t.clone()), Formula::eq(t.clone(), t.clone())),
        &Thm::eq_refl(t.clone()),
    )?;
    Thm::mp(&iff_mpr(&at)?, &disj)
}

/// `⊢ ∀n. (n ∈ ω → Trans(n))` — **every natural number is transitive**.
///
/// By induction, and stated explicitly rather than assumed: it is what
/// [`succ_inj`] runs on. The base case is [`trans_empty`] and the step is
/// [`trans_succ`], so the induction adds nothing beyond gluing them — but the
/// gluing is the part that needs `ω` to be least, and it is exactly what a
/// construction that helped itself to "the naturals are transitive" would be
/// skipping.
pub fn omega_trans(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let phi = crate::empty::transitive(env, &tx);
    let scheme = induction_scheme(env, core, x, &phi)?;

    let base = trans_empty(env, &core.empty_ax)?;
    let tsucc = trans_succ(env, core.succ, &core.succ_ax)?;
    let x_in_om = Formula::mem(tx.clone(), core.set());
    let step_body = syl(
        &and_right(x_in_om, phi.clone()),
        &inst_all(&tsucc, std::slice::from_ref(&tx))?,
    )?;
    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(x, &step_body)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, Formula::imp(Formula::mem(tx, core.set()), phi)),
        "omega_trans: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))` — zero is not a successor.
///
/// `n ∈ succ(n)`, so `succ(n) = ∅` would put `n` in `∅`. The `n ∈ ω`
/// antecedent is not used — the statement holds for every set — but it is the
/// form the Peano axioms are stated in, so it is the form given here.
///
/// [`succ_ne_zero_pair`] hands back the unguarded theorem beside it, and this
/// is the guarded projection of that one call.
pub fn succ_ne_zero(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    Some(succ_ne_zero_pair(env, core)?.1)
}

/// **Both spellings of "zero is not a successor", from one derivation**:
///
/// ```text
/// ⊢ ∀n. ¬(succ(n) = 0)                 unguarded   .0
/// ⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))       Peano form  .1
/// ```
///
/// # Why the unguarded form is stated rather than left to the caller
///
/// This module's header has said since it was written that the `n ∈ ω`
/// antecedent *"is not used — the statement holds for every set"*, and the
/// derivation below shows it: `ne` is the unguarded theorem and [`a1i`] is the
/// single step that weakens it. What is new is a **consumer that cannot spend
/// the antecedent**, and it is the same one
/// [`crate::levels::order::Order::max_ne_zero`] was made unconditional for:
/// `mini::interp::Interp::as_pi_at` settles an interpreted `Π`'s `ite0` guard
/// by reading the *term*, and a term-level walk has no `∈ ω` to spend. There
/// the guard `ℓ̂₂` is `succ(û₁)` — every `Π` whose codomain is a sort, because
/// `Sort u` inhabits `Sort (u+1)` — and the walk holds no level expression to
/// recover `û₁ ∈ ω` from.
///
/// So the pair, and **one derivation** rather than two: the two theorems differ
/// by [`a1i`] alone, and deriving them apart would be two chances to disagree about
/// which `succ` and which `∅` they are about. Returning both from one call is
/// also what keeps [`Peano::over`]'s `Env::fresh_var` count exactly what it
/// was, which matters because every later symbol is numbered off it.
pub fn succ_ne_zero_pair(env: &mut Env, core: &OmegaCore) -> Option<(Thm, Thm)> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let (zero, sn) = (core.zero(), core.succ_of(tn.clone()));

    let n_in_sn = mem_succ_self(core, &tn)?;
    let hole = env.fresh_var();
    let leib =
        Thm::eq_leibniz(sn.clone(), zero, hole, Formula::mem(tn.clone(), Term::var(hole)));
    let to_mem = mpd_const(&leib, &n_in_sn)?;
    let not_mem = inst_all(&core.empty_ax, std::slice::from_ref(&tn))?;
    let ne = syl(&to_mem, &not_mem)?;
    let un = Thm::gen(n, &ne);
    debug_assert_eq!(
        *un.concl(),
        Formula::forall(n, Formula::not(Formula::eq(sn.clone(), core.zero()))),
        "succ_ne_zero_pair: unexpected unguarded shape"
    );
    let out = Thm::gen(n, &a1i(&ne, Formula::mem(tn.clone(), core.set())));
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn, core.set()),
                Formula::not(Formula::eq(sn, core.zero()))
            )
        ),
        "succ_ne_zero: unexpected shape"
    );
    Some((un, out))
}

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (succ(m) = succ(n) → m = n))` — the successor
/// is injective on `ω`.
///
/// From `succ(m) = succ(n)`: `m ∈ succ(m)` carries over to `m ∈ succ(n)`, so
/// `m ∈ n` or `m = n`, and symmetrically `n ∈ m` or `n = m`. The only case to
/// close off is `m ∈ n` together with `n ∈ m`, and that is where transitivity
/// is needed: `Trans(m)` turns it into `m ∈ m`, which Regularity refutes
/// ([`crate::empty::no_self_mem`]). `om_trans` supplies the transitivity and
/// must be [`omega_trans`]'s theorem.
pub fn succ_inj(env: &mut Env, core: &OmegaCore, om_trans: &Thm, no_self: &Thm) -> Option<Thm> {
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = core.set();
    let (sm, sn) = (core.succ_of(tm.clone()), core.succ_of(tn.clone()));

    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w.clone());
    let h = Formula::and(m_om.clone(), n_om.clone());
    let e = Formula::eq(sm.clone(), sn.clone());
    let big = Formula::and(h.clone(), e.clone());
    let goal = Formula::eq(tm.clone(), tn.clone());

    let mem_mn = Formula::mem(tm.clone(), tn.clone());
    let mem_nm = Formula::mem(tn.clone(), tm.clone());

    // ── `W → (m ∈ n ∨ m = n)` and `W → (n ∈ m ∨ n = m)` ──────────────────────
    let m_in_sm = mem_succ_self(core, &tm)?;
    let hole1 = env.fresh_var();
    let leib1 =
        Thm::eq_leibniz(sm.clone(), sn.clone(), hole1, Formula::mem(tm.clone(), Term::var(hole1)));
    let e_m_in_sn = mpd_const(&leib1, &m_in_sm)?;
    let succ_nm = inst_all(&core.succ_ax, &[tn.clone(), tm.clone()])?;
    let w_disj1 = syl(
        &and_right(h.clone(), e.clone()),
        &syl(&e_m_in_sn, &iff_mp(&succ_nm)?)?,
    )?;

    let n_in_sn = mem_succ_self(core, &tn)?;
    let hole2 = env.fresh_var();
    let leib2 =
        Thm::eq_leibniz(sn.clone(), sm.clone(), hole2, Formula::mem(tn.clone(), Term::var(hole2)));
    let e_n_in_sm = syl(&eq_symm_imp(env, sm, sn), &mpd_const(&leib2, &n_in_sn)?)?;
    let succ_mn = inst_all(&core.succ_ax, &[tm.clone(), tn.clone()])?;
    let w_disj2 = syl(
        &and_right(h.clone(), e.clone()),
        &syl(&e_n_in_sm, &iff_mp(&succ_mn)?)?,
    )?;

    // ── `m ∈ n`, then a second split on `n ∈ m` versus `n = m` ───────────────
    let v = Formula::and(big.clone(), mem_mn.clone());
    let v_w = and_left(big.clone(), mem_mn.clone());
    let v_mn = and_right(big.clone(), mem_mn.clone());
    let v_disj2 = syl(&v_w, &w_disj2)?;
    let v_case_eq = a1i(&eq_symm_imp(env, tn.clone(), tm.clone()), v.clone());

    let v_m_om = syl(&v_w, &syl(&and_left(h.clone(), e.clone()), &and_left(m_om, n_om))?)?;
    let v_trans_m =
        hyp_mp(&a1i(&inst_all(om_trans, std::slice::from_ref(&tm))?, v.clone()), &v_m_om)?;
    let trans_m = crate::empty::transitive(env, &tm);
    let trans_n = Thm::ax_inst(trans_m.clone(), tn.clone())?;
    let (_, trans_n_body) = trans_n.concl().as_imp()?;
    let trans_nm = syl(&trans_n, &Thm::ax_inst(trans_n_body, tm.clone())?)?;
    let v_trans_imp = syl(&v_trans_m, &trans_nm)?;

    let u = Formula::and(v.clone(), mem_nm.clone());
    let u_v = and_left(v.clone(), mem_nm.clone());
    let u_nm = and_right(v.clone(), mem_nm.clone());
    let u_pair = hyp_and(&syl(&u_v, &v_mn)?, &u_nm)?;
    let u_mm = hyp_mp(&syl(&u_v, &v_trans_imp)?, &u_pair)?;
    let no_self_m = inst_all(no_self, std::slice::from_ref(&tm))?;
    let u_false = hyp_mp(&a1i(&no_self_m, u.clone()), &u_mm)?;
    let v_case_mem = uncurry(&syl(&u_false, &crate::ex_falso(goal.clone()))?)?;

    let v_goal = hyp_or_elim(&v_disj2, &v_case_mem, &v_case_eq)?;
    let case_mem = uncurry(&v_goal)?;
    let case_eq = a1i(&imp_refl(goal.clone()), big.clone());

    let w_goal = hyp_or_elim(&w_disj1, &case_mem, &case_eq)?;
    let out = uncurry(&w_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::imp(e, goal)),
        "succ_inj: unexpected shape"
    );
    Some(gen_all(&[m, n], &out))
}

/// `ω` with the Peano properties, assembled once.
///
/// Everything here comes from a single chain of definitional extensions — see
/// [`OmegaCore`] on why building it twice would not compose.
#[derive(Clone)]
pub struct Peano {
    /// The symbols and the raw minimality theorem.
    pub core: OmegaCore,
    /// `⊢ ∀S. ((0 ∈ S ∧ ∀n. ((n ∈ ω ∧ n ∈ S) → succ(n) ∈ S)) → ∀n. (n ∈ ω → n ∈ S))`.
    pub induction: Thm,
    /// `⊢ ∀n. (n ∈ ω → Trans(n))`.
    pub trans: Thm,
    /// `⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))`.
    pub succ_ne_zero: Thm,
    /// `⊢ ∀n. ¬(succ(n) = 0)` — the same fact with the vacuous antecedent left
    /// off, for a caller that reads a level *term* and holds no membership.
    /// See [`succ_ne_zero_pair`]; the two come out of one derivation.
    pub succ_ne_zero_un: Thm,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (succ(m) = succ(n) → m = n))`.
    pub succ_inj: Thm,
    /// `⊢ ∀x. ¬(x ∈ x)`, which the injectivity proof consumes and which is
    /// worth keeping to hand.
    pub no_self_mem: Thm,
}

impl Peano {
    /// Derive the lot, over a caller-supplied [`Sets`].
    pub fn with_sets(env: &mut Env, sets: Sets) -> Option<Peano> {
        let core = OmegaCore::with_sets(env, sets)?;
        Peano::over(env, core)
    }

    /// Derive the lot over an [`OmegaCore`] the caller already has — the route
    /// [`crate::recursion::Rec::new`] takes, because it needs the `ω` whose `0` is the `∅` that
    /// `app` returns off the domain.
    pub fn over(env: &mut Env, core: OmegaCore) -> Option<Peano> {
        let induction = induction_principle(env, &core)?;
        let trans = omega_trans(env, &core)?;
        let (succ_ne_zero_un, succ_ne_zero) = succ_ne_zero_pair(env, &core)?;
        let no_self_mem = crate::empty::no_self_mem(env, core.sets.up, &core.mem_sing).ok()?;
        let succ_inj = succ_inj(env, &core, &trans, &no_self_mem)?;
        Some(Peano {
            core,
            induction,
            trans,
            succ_ne_zero,
            succ_ne_zero_un,
            succ_inj,
            no_self_mem,
        })
    }

    /// The same, minting a fresh [`Sets`].
    pub fn new(env: &mut Env) -> Option<Peano> {
        let sets = Sets::new(env);
        Peano::with_sets(env, sets)
    }
}
