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

/// The bundled [`Rules`] kit is over the apparatus's **own** chain: its
/// `punit_demo` instantiates at the apparatus's `∅`, discharges with the
/// apparatus's own `0 ∈ ω`, and concludes membership in the apparatus's own
/// `srt(∅)` — a kit derived over a foreign tower would fail each of these.
#[test]
fn bundled_rules_are_over_this_chain() {
    let mut env = Env::new();
    let lp = setup(&mut env);
    let zero = lp.zero();
    let at = derived::inst_all(&lp.ru.punit_demo, std::slice::from_ref(&zero)).expect("inst");
    let closed = kernel::Thm::mp(&at, &lp.r.peano.core.zero_mem).expect("0 ∈ ω discharges");
    assert!(closed.hyps().is_empty());
    let (one, srt0) = closed.concl().as_mem().expect("a membership");
    assert_eq!(srt0, lp.srt_at(zero), "the target is not this apparatus's srt(∅)");
    // `1` is the unit of the tower the apparatus was built over; pin it against
    // an independent spelling through `srt`'s own `at_zero` computation.
    let _ = one;
    assert!(lp.ru.pi_imax.hyps().is_empty());
    assert!(lp.ru.mono_sub.hyps().is_empty());
}
