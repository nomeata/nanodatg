//! [`LevelPoly`] assembles over one tower chain, and `imax` stays in `ω`.

use derived::levels::apparatus::{level_poly, LevelPoly};
use derived::tower::Tower;
use kernel::{Env, Formula, Term};

fn setup(env: &mut Env) -> LevelPoly {
    let t = Tower::new(env).expect("Tower");
    level_poly(env, &t).expect("LevelPoly")
}

/// The closure lemma has the advertised shape, and cashes out at numerals:
/// discharging `∅ ∈ ω ∧ 1̄ ∈ ω` yields the closed
/// `⊢ ite0(1̄, ∅, ∅ ∪ 1̄) ∈ ω`.
#[test]
fn imax_stays_in_omega() {
    let mut env = Env::new();
    let lp = setup(&mut env);
    let omega = lp.omega();
    let zero = lp.zero();
    let one = lp.succ_of(zero.clone());

    // Shape pin against an independent rebuild.
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let (tu, tv) = (Term::var(u), Term::var(v));
    let h = Formula::and(
        Formula::mem(tu.clone(), omega.clone()),
        Formula::mem(tv.clone(), omega.clone()),
    );
    let concl = Formula::mem(lp.imax(tu.clone(), tv.clone()), omega.clone());
    let rebuilt = Formula::forall(u, Formula::forall(v, Formula::imp(h, concl)));
    assert!(lp.imax_in_omega.hyps().is_empty());
    assert_eq!(*lp.imax_in_omega.concl(), rebuilt);

    // Cash at `u := ∅`, `v := 1̄`.
    let zero_mem = lp.r.peano.core.zero_mem.clone();
    let one_mem = derived::inst_all(&lp.r.peano.core.succ_closed, std::slice::from_ref(&zero))
        .and_then(|t| kernel::Thm::mp(&t, &zero_mem))
        .expect("1 in omega");
    let at = derived::inst_all(&lp.imax_in_omega, &[zero.clone(), one.clone()]).expect("inst");
    let closed = kernel::Thm::mp(&at, &derived::and_intro(&zero_mem, &one_mem)).expect("mp");
    assert!(closed.hyps().is_empty());
    assert_eq!(
        *closed.concl(),
        Formula::mem(lp.imax(zero, one), omega),
        "the closed instance is not about the imax term"
    );
}
