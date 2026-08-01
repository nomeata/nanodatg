//! **Step 1** — a universe contains the ordered pairs of its members.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → ⟨a,b⟩ ∈ u)   [universe_opair]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # What it costs
//!
//! `⟨a,b⟩` is the Kuratowski pair `{{a},{a,b}}`, so this is
//! [`crate::universe::universe_pairing`] three times over: once for `{a}`
//! (as `{a,a}`), once for `{a,b}`, and once for the pair of those two. Nothing
//! else is used, and in particular no closure under `⋃` or products — which is
//! the point, since neither is available.
//!
//! This is the lemma the rest of the chain reaches for whenever something has
//! to be put *into* a universe: [`super::subset`] uses it on each member of a
//! function's graph, and [`super::closure`] on `⟨a,f⟩` itself.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::universe::is_universe;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, inst_all, opair, singleton, syl};

/// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → ⟨a,b⟩ ∈ u)` — **every
/// universe is closed under the Kuratowski ordered pair**.
///
/// Three applications of [`crate::universe::universe_pairing`]: `{a}` is
/// `{a,a}`, `{a,b}` is a pair, and `⟨a,b⟩` is the pair of those two. This is
/// [`crate::universe::least_universe_opair`]'s argument, run at an arbitrary
/// universe rather than at `U(c)` — which is the form the function-space
/// argument below needs, since it works inside a universe `u` that is not
/// `U(c)`.
///
/// `pairing` must be [`crate::universe::universe_pairing`] for this very `up`;
/// the statement is rebuilt here and compared, so a mismatched theorem gets a
/// rejection rather than a conclusion.
pub fn universe_opair(env: &mut Env, up: FnSym, pairing: &Thm) -> Option<Thm> {
    if up.arity() != 2 {
        return None
    }
    let (uv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(uv), Term::var(av), Term::var(bv));

    let univ_u = is_universe(env, &tu);
    let a_in = Formula::mem(ta.clone(), tu.clone());
    let b_in = Formula::mem(tb.clone(), tu.clone());
    let both = Formula::and(a_in.clone(), b_in.clone());
    let h = Formula::and(univ_u.clone(), both.clone());

    let h_univ = and_left(univ_u.clone(), both.clone());
    let h_mems = and_right(univ_u.clone(), both.clone());
    let h_a = syl(&h_mems, &and_left(a_in.clone(), b_in.clone()))?;
    let h_b = syl(&h_mems, &and_right(a_in, b_in))?;

    let sing = singleton(up, ta.clone());
    let upair_ab = Term::apply(up, vec![ta.clone(), tb.clone()]);

    let step = |env: &mut Env, x: &Term, y: &Term, hx: &Thm, hy: &Thm| -> Option<Thm> {
        let inst = inst_all(pairing, &[tu.clone(), x.clone(), y.clone()])?;
        let want = Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(
                    Formula::mem(x.clone(), tu.clone()),
                    Formula::mem(y.clone(), tu.clone()),
                ),
            ),
            Formula::mem(Term::apply(up, vec![x.clone(), y.clone()]), tu.clone()),
        );
        if *inst.concl() != want {
            return None
        }
        hyp_mp(&a1i(&inst, h.clone()), &hyp_and(&h_univ, &hyp_and(hx, hy)?)?)
    };

    let h_sing = step(env, &ta, &ta, &h_a, &h_a)?;
    let h_pair = step(env, &ta, &tb, &h_a, &h_b)?;
    let out = step(env, &sing, &upair_ab, &h_sing, &h_pair)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(opair(up, ta, tb), tu)),
        "universe_opair: wrong shape"
    );
    Some(gen_all(&[uv, av, bv], &out))
}
