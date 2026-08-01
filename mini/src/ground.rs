//! The mini side of the level pre-pass (MINI-DESIGN.md §3, step 2).
//!
//! # Interface
//!
//! `checker::instantiations::Instantiations::compute` produces the schedule and
//! is reused verbatim; what mini adds is the ~30 lines that put a declaration
//! *into* one of its scheduled ground instantiations:
//!
//! * [`eval`] — a `Level` at a ground environment, as a numeral. It mirrors
//!   `checker::instantiations::eval` clause for clause: `max` is maximum,
//!   `imax(_, 0)` is `0`, `imax(a, b)` is `max(a, b)` otherwise, a parameter
//!   with no binding is `None`.
//! * [`ground_levels`] — a declaration's `Inst` as a list of `succ^{σᵢ}(zero)`.
//! * [`subst_ground`] — a declaration's expression at σ.
//!
//! Why per-σ at all: `⟦·⟧` is not defined at a declaration's own parameters,
//! because `Level::simplify` never simplifies `imax(l, r)` at a parameter `r`,
//! so a `Π` whose codomain sits in `Sort (imax u v)` is a proposition when
//! `v := 0` and a function space otherwise. At a ground σ every level is a
//! numeral and exactly one §6.2 clause applies. None of this is needed by step
//! (b) — the port checks a declaration once at its own symbolic parameters,
//! which is what mini-lean does and what acceptance fidelity is measured
//! against — so nothing here is on the (b) path.

use crate::expr::{Level, Name, E};
use std::collections::HashMap;

/// A ground `Level` at `env`, as a numeral. `None` when a parameter is unbound,
/// which on a well-formed export file cannot happen: `checkDeclarInfo`'s
/// nanoda counterpart asserts every parameter a declaration mentions is one of
/// its own.
pub fn eval(l: &Level, env: &HashMap<Name, u32>) -> Option<u32> {
    match l {
        Level::Zero => Some(0),
        Level::Succ(a) => Some(eval(a, env)? + 1),
        Level::Max(a, b) => Some(eval(a, env)?.max(eval(b, env)?)),
        Level::IMax(a, b) => {
            let rb = eval(b, env)?;
            if rb == 0 {
                Some(0)
            } else {
                Some(eval(a, env)?.max(rb))
            }
        }
        Level::Param(n) => env.get(n).copied(),
    }
}

/// `succ^n(zero)`.
pub fn numeral(n: u32) -> Level {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = l.succ();
    }
    l
}

/// A declaration's universe parameters bound to the numerals of `sigma`.
pub fn ground_env(uparams: &[Name], sigma: &[u32]) -> HashMap<Name, u32> {
    uparams.iter().cloned().zip(sigma.iter().copied()).collect()
}

/// The level arguments a declaration's own parameters stand for under σ.
pub fn ground_levels(sigma: &[u32]) -> Vec<Level> { sigma.iter().map(|n| numeral(*n)).collect() }

/// A declaration's expression at σ: every parameter replaced by its numeral.
pub fn subst_ground(e: &E, uparams: &[Name], sigma: &[u32]) -> E {
    let env = ground_env(uparams, sigma);
    crate::expr::subst_level(e, &|n: &Name| match env.get(n) {
        Some(k) => numeral(*k),
        // As in `instantiate_lparams`: should not happen.
        None => Level::Param(n.clone()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Level { Level::Param(Name::simple(s)) }

    /// The semantics `checker::instantiations`' module doc states, pinned here
    /// so that mini's substitution and nanoda's scheduling cannot drift apart
    /// silently: they must agree about what σ *means*, or mini would look up
    /// interpretations at keys the pre-pass never scheduled.
    #[test]
    fn eval_matches_the_documented_semantics() {
        let env = ground_env(&[Name::simple("u"), Name::simple("v")], &[3, 0]);
        assert_eq!(eval(&Level::Zero, &env), Some(0));
        assert_eq!(eval(&p("u"), &env), Some(3));
        assert_eq!(eval(&p("u").succ(), &env), Some(4));
        assert_eq!(eval(&Level::max(p("u"), p("v")), &env), Some(3));
        // imax at a zero right-hand side is zero, whatever the left is.
        assert_eq!(eval(&Level::imax(p("u"), p("v")), &env), Some(0));
        // and the maximum otherwise.
        assert_eq!(eval(&Level::imax(p("v"), p("u")), &env), Some(3));
        // an unbound parameter has no value.
        assert_eq!(eval(&p("w"), &env), None);
    }

    /// **A ground level is decided exactly, and it decides to its numeral.**
    ///
    /// This is the property the whole per-σ strategy rests on, and it is
    /// weaker than MINI-DESIGN.md §3 claims: the design says `simplify` "yields
    /// `succ^n zero` on both sides" at ground levels, and it does not —
    /// `mk_imax(a, succ b)` is `Max(a, succ b)` and `simplify` never collapses
    /// a `Max` of numerals. What *is* true, and is all that is needed, is that
    /// `Level::le` is exact on ground input, so `assertLevelEq` between a
    /// ground level and its numeral always succeeds. The interpretation must
    /// therefore evaluate levels with [`eval`] rather than pattern-match a
    /// simplified level for `succ^n zero`.
    #[test]
    fn grounding_decides_exactly() {
        let uparams = [Name::simple("u"), Name::simple("v")];
        let ls = [
            Level::imax(p("u"), p("v")),
            Level::max(p("u").succ(), p("v")),
            Level::imax(Level::max(p("u"), p("v")), p("v")).succ(),
            Level::max(Level::imax(p("u"), p("v")), p("u")),
        ];
        for a in 0..4u32 {
            for b in 0..4u32 {
                let env = ground_env(&uparams, &[a, b]);
                for l in &ls {
                    let g = crate::expr::sort(l.clone());
                    let g = subst_ground(&g, &uparams, &[a, b]);
                    let crate::expr::Expr::Sort(gl) = &*g else { unreachable!() };
                    let n = eval(l, &env).unwrap();
                    crate::kernel::assert_level_eq(gl, &numeral(n))
                        .unwrap_or_else(|e| panic!("{l} at [{a},{b}]: {e}"));
                    // …and distinct numerals stay distinct.
                    assert!(
                        crate::kernel::assert_level_eq(gl, &numeral(n + 1)).is_err(),
                        "{l} at [{a},{b}] should not equal {}",
                        n + 1
                    );
                }
            }
        }
    }
}
