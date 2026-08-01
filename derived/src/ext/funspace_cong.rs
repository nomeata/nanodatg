//! Congruence for the function space, in the form the checker's `pi_cong`
//! wants.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))   [fs_cong]
//! ```
//!
//! # Why there is anything to do
//!
//! The non-dependent Π is `fs(a,b)`, whose arguments are the interpretations of
//! the domain and codomain — so unlike `dprod` and `lam`, the head symbol does
//! *not* depend on the body's shape and there is nothing to prove beyond
//! congruence. What is not immediate is only the *form*: [`crate::congr`]
//! consumes two proved equations and yields a proved equation, whereas `pi_cong`
//! needs the universally quantified implication, which a Hilbert system has to
//! assemble. This is the companion to [`crate::ext::dprod_ext`] for the case
//! where the Π-type's body does not depend on the bound variable.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funspace::Funspace;
use crate::{and_left, and_right, gen_all, uncurry};
use super::shared::{hyp_congr, hyp_eq_trans};

/// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → f(a,b) = f(a',b')))`, for any binary
/// function symbol.
fn congr2_imp(env: &mut Env, f: FnSym) -> Option<Thm> {
    if f.arity() != 2 {
        return None
    }
    let (a, a2, b, b2) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tb, tb2) = (Term::var(a), Term::var(a2), Term::var(b), Term::var(b2));

    let e1 = Formula::eq(ta.clone(), ta2.clone());
    let e2 = Formula::eq(tb.clone(), tb2.clone());
    let h_e1 = and_left(e1.clone(), e2.clone());
    let h_e2 = and_right(e1.clone(), e2.clone());

    let lhs = Term::apply(f, vec![ta.clone(), tb.clone()]);
    let mid = Term::apply(f, vec![ta2.clone(), tb.clone()]);
    let rhs = Term::apply(f, vec![ta2.clone(), tb2.clone()]);

    let w1 = env.fresh_var();
    let step1 = hyp_congr(&h_e1, w1, &lhs, &Term::apply(f, vec![Term::var(w1), tb.clone()]))?;
    let w2 = env.fresh_var();
    let step2 = hyp_congr(&h_e2, w2, &mid, &Term::apply(f, vec![ta2.clone(), Term::var(w2)]))?;

    let out = uncurry(&hyp_eq_trans(env, &step1, &step2)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(e1, Formula::imp(e2, Formula::eq(lhs, rhs))),
        "congr2_imp: unexpected shape"
    );
    Some(gen_all(&[a, a2, b, b2], &out))
}

/// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))` — the
/// non-dependent function space respects equality of its domain and codomain.
///
/// Two Leibniz steps and a transitivity, via [`congr2_imp`]. This is the
/// companion to [`crate::ext::dprod_ext`] for the case where the Π-type's body does not
/// depend on the bound variable and the checker's interpretation is a plain
/// `fs`.
pub fn fs_cong(env: &mut Env, fsp: &Funspace) -> Option<Thm> { congr2_imp(env, fsp.fs) }
