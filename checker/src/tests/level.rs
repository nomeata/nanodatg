use crate::tests::util::test_ctx;
use rand::prelude::*;
use std::error::Error;

#[test]
fn leq_test0() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let m = ctx.max(s, s);
        assert!(ctx.leq(s, m));
        assert!(ctx.leq(m, s));
        assert!(ctx.eq_antisymm(s, m));
    })
}

#[test]
fn leq_test1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let im = ctx.imax(ss, z);
        assert!(ctx.leq(im, z));
        assert!(ctx.eq_antisymm(z, im));
    })
}

#[test]
fn leq_test2() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let a = ctx.param_quick("a");
        let b = ctx.param_quick("b");
        assert!(!ctx.leq(a, b));
        assert!(!ctx.leq(b, a));
    })
}

/// **`eq_antisymm` needs a pair where the order is strict — every other call
/// in this file asserts it *true*, and `true` does not need antisymmetry.**
///
/// `eq_antisymm` is `leq(l, r) && leq(r, l)` (`level.rs`). Before this test,
/// all five assertions about it in this file (`leq_test0`, `leq_test1`,
/// `leq_test_max_param`, `leq_test_succ`, and the `_many` case) asserted a pair
/// that is genuinely equal, so both conjuncts hold and the conjunction carries
/// no information about which conjuncts were consulted. **Measured: rewriting
/// the body as `self.leq(l, r) && self.leq(l, r)` — dropping antisymmetry
/// outright — leaves the whole `--no-default-features --lib` suite at 246/246.**
///
/// That is not a cosmetic loss. `eq_antisymm` decides sort defeq
/// (`tc.rs`, `Sort l` against `Sort r`) and constructor level agreement
/// (`inductive.rs`). Degenerated to `leq(l, r)` it accepts `Sort u ≡ Sort v`
/// whenever `u ≤ v` — an *acceptance* the checker is not entitled to, which is
/// the unsound direction.
///
/// **Both orientations, deliberately.** One witness catches only one of the two
/// ways the conjunction can degenerate: `!eq_antisymm(z, s)` goes red under
/// `leq(l, r) && leq(l, r)` and stays green under `leq(r, l) && leq(r, l)`, and
/// the reversed witness does the opposite. Each projection needs its own
/// witness, exactly as `LocalKey`'s three-local fixture does.
///
/// The equal pair is kept as the positive control, so that an `eq_antisymm`
/// rewritten to `false` — which would satisfy both negative assertions — is
/// caught here too rather than only in `leq_test0`.
#[test]
fn eq_antisymm_is_antisymmetric_and_a_strict_order_separates_it() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        // The order is strict: `0 ≤ 1` and not conversely.
        assert!(ctx.leq(z, s), "0 ≤ 1");
        assert!(!ctx.leq(s, z), "1 ≰ 0");
        // …so the two levels are not equal, in either argument order.
        assert!(!ctx.eq_antisymm(z, s), "0 and 1 are not the same level");
        assert!(!ctx.eq_antisymm(s, z), "…and that does not depend on the argument order");
        // The positive control: equal but not syntactically identical.
        let m = ctx.max(s, s);
        assert!(ctx.eq_antisymm(s, m), "`max 1 1` and `1` are the same level");
    })
}

#[test]
fn leq_test_imax_imax() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let a = ctx.param_quick("a");
        let b = ctx.param_quick("b");
        let imax_a_b = ctx.imax(a, b);
        let s_imax_a_b = ctx.succ(imax_a_b);
        let ss_imax_a_b = ctx.succ(s_imax_a_b);
        assert!(ctx.leq(imax_a_b, imax_a_b));
        assert!(ctx.leq(imax_a_b, s_imax_a_b));
        assert!(ctx.leq(imax_a_b, ss_imax_a_b));
        assert!(ctx.leq(s_imax_a_b, ss_imax_a_b));
        assert!(!ctx.leq(ss_imax_a_b, imax_a_b));
        assert!(!ctx.leq(ss_imax_a_b, s_imax_a_b));
    })
}

#[test]
fn leq_test3() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let a = ctx.param_quick("a");
        let b = ctx.param_quick("b");
        assert!(!ctx.leq(a, b));
        assert!(!ctx.leq(b, a));
    })
}

#[test]
fn leq_test4() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        for _ in 0..100 {
            let mut rng = thread_rng();
            let (small, large) = {
                let (x, y): (u8, u8) = rng.gen();
                (x.min(y), x.max(y))
            };

            let p = ctx.param_quick("p");
            let (a, b) = (ctx.level_n(p, small as u64), ctx.level_n(p, large as u64));
            assert!(ctx.leq(a, b));
        }
    })
}

#[test]
fn leq_test5() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
        let mut rng = thread_rng();
        for _ in 0..100 {
            let (small, large) = {
                let (x, y): (u8, u8) = rng.gen();
                (x.min(y) as u64, x.max(y) as u64)
            };
            let lhs = {
                let (p_small, q_small) = (ctx.level_n(p, small), ctx.level_n(q, small));
                let lhs = ctx.max(p_small, q_small);
                ctx.level_n(lhs, small)
            };
            let rhs = {
                let (p_large, q_large) = (ctx.level_n(p, large), ctx.level_n(q, large));
                let rhs = ctx.max(p_large, q_large);
                ctx.level_n(rhs, large)
            };

            assert!(ctx.leq(lhs, rhs));
        }
    })
}

#[test]
fn leq_test6() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
        let mut rng = thread_rng();
        for _ in 0..100 {
            let (small, large) = {
                let (x, y): (u8, u8) = rng.gen();
                (x.min(y) as u64, x.max(y) as u64)
            };
            let lhs = {
                let (p_small, q_small) = (ctx.level_n(p, small), ctx.level_n(q, small));
                let lhs = ctx.imax(p_small, q_small);
                ctx.level_n(lhs, small)
            };
            let rhs = {
                let (p_large, q_large) = (ctx.level_n(p, large), ctx.level_n(q, large));
                let rhs = ctx.imax(p_large, q_large);
                ctx.level_n(rhs, large)
            };

            assert!(ctx.leq(lhs, rhs));
        }
    })
}

#[test]
fn leq_test7() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
        let mut rng = thread_rng();
        for _ in 0..100 {
            let (u, v, w) = {
                let (u, v, w): (u8, u8, u8) = rng.gen();
                (u as u64, v as u64, w as u64)
            };
            let lhs = {
                let (p_, q_) = (ctx.level_n(p, u), ctx.level_n(q, v + 1));
                let lhs = ctx.imax(p_, q_);
                ctx.level_n(lhs, w)
            };
            let rhs = {
                let (p_, q_) = (ctx.level_n(p, u), ctx.level_n(q, v + 1));
                let rhs = ctx.max(p_, q_);
                ctx.level_n(rhs, w)
            };

            assert!(ctx.eq_antisymm(lhs, rhs));
        }
    })
}

#[test]
fn eq_test1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let m = ctx.max(s, s);
        let sm = ctx.succ(m);
        assert!(ctx.eq_antisymm(ss, sm));
    })
}

#[test]
fn eq_many_test1() -> Result<(), Box<dyn Error>> {
    // [2] == [max(1, 1) + 1]
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let m = ctx.max(s, s);
        let sm = ctx.succ(m);
        let ups1 = ctx.alloc_levels(std::sync::Arc::from([ss]));
        let ups2 = ctx.alloc_levels(std::sync::Arc::from([sm]));
        assert!(ctx.eq_antisymm_many(ups1, ups2));
    })
}

#[test]
fn debug_test0() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let ss = ctx.succ(s);
        let (z_, num) = ctx.level_succs(ss);
        assert_eq!(z_, z);
        assert_eq!(num, 2);
        assert_eq!("2", format!("{:?}", ctx.debug_print(ss)));
    })
}

#[test]
fn debug_test1() -> Result<(), Box<dyn Error>> {
    test_ctx(None, |ctx| {
        let z = ctx.zero();
        let s = ctx.succ(z);
        let m = ctx.max(s, s);
        let sm = ctx.succ(m);
        let (m_, num) = ctx.level_succs(sm);
        assert_eq!(m, m_);
        assert_eq!(num, 1);
        assert_eq!("max(1, 1) + 1", format!("{:?}", ctx.debug_print(sm)));
    })
}
