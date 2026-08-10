//! Level instantiation: a declaration's expression and store key at a given
//! list of level arguments.
//!
//! # Interface
//!
//! A declaration is interpreted at an **instantiation** — one
//! [`crate::expr::Level`] per universe parameter, in the declaration's own
//! order. Nothing here requires those levels to be ground:
//!
//! * [`subst_levels`] — a declaration's expression at an instantiation.
//!   Lean's `instantiate_lparams`, nothing more.
//! * [`key_levels`] — the canonical spelling of an instantiation, which is
//!   what [`crate::interp::ConstKey`] is keyed on.
//! * [`as_numeral`] — a *closed* level as a `u32`, or `None` when it still
//!   mentions a parameter. It mirrors `checker::instantiations::eval` clause
//!   for clause: `max` is maximum, `imax(_, 0)` is `0`, `imax(a, b)` is
//!   `max(a, b)` otherwise, a parameter is `None`.
//! * [`numeral`] / [`ground_levels`] — the pre-pass boundary: a schedule entry
//!   `σ : Vec<u32>` as the instantiation `succ^{σᵢ}(zero)`.
//!
//! # Where the groundness assumption actually lives now
//!
//! It used to live in the *type*: an instantiation was a `Vec<u32>`, so a
//! declaration at its own parameters could not be named at all, and the ground
//! σ-schedule was a precondition of the interpretation rather than a choice
//! (`LEVELPOLY.md` §5.3 step 2). It now lives in [`as_numeral`], and only
//! there: every place that still needs a numeral asks for one and mints
//! [`crate::ev::Gap::SymbolicLevel`] when it does not get one. Those sites are
//! the remaining volume of the de-scheduling, and they are countable because
//! they all go through this one function.
//!
//! Why a numeral is wanted at all, where it is: `⟦·⟧` is not defined at a
//! declaration's own parameters by the ground clauses, because
//! `Level::simplify` never simplifies `imax(l, r)` at a parameter `r`, so a
//! `Π` whose codomain sits in `Sort (imax u v)` is a proposition when `v := 0`
//! and a function space otherwise. At a numeral every level is decided and
//! exactly one §6.2 clause applies. The level-polymorphic replacement is
//! `derived::levels` (`srt(ℓ̂)` and the `ite0` clause); none of it is consumed
//! here yet.
//!
//! None of this is needed by step (b) — the port checks a declaration once at
//! its own symbolic parameters, which is what mini-lean does and what
//! acceptance fidelity is measured against — so nothing here is on the (b)
//! path.

use crate::expr::{Level, LevelView, Name, E};
use std::collections::HashMap;

/// A **closed** `Level` as a numeral, or `None` when it still mentions a
/// universe parameter.
///
/// The `None` is the level-polymorphic frontier: it is what every
/// [`crate::ev::Gap::SymbolicLevel`] in the program is reporting.
pub fn as_numeral(l: &Level) -> Option<u32> {
    match l.view() {
        LevelView::Zero => Some(0),
        LevelView::Succ(a) => Some(as_numeral(&a)? + 1),
        LevelView::Max(a, b) => Some(as_numeral(&a)?.max(as_numeral(&b)?)),
        LevelView::IMax(a, b) => {
            let rb = as_numeral(&b)?;
            if rb == 0 {
                Some(0)
            } else {
                Some(as_numeral(&a)?.max(rb))
            }
        }
        LevelView::Param(_) => None,
    }
}

/// A `Level` at a ground environment, as a numeral. `None` when a parameter is
/// unbound, which on a well-formed export file cannot happen: `checkDeclarInfo`'s
/// nanoda counterpart asserts every parameter a declaration mentions is one of
/// its own.
pub fn eval(l: &Level, env: &HashMap<Name, u32>) -> Option<u32> {
    match l.view() {
        LevelView::Zero => Some(0),
        LevelView::Succ(a) => Some(eval(&a, env)? + 1),
        LevelView::Max(a, b) => Some(eval(&a, env)?.max(eval(&b, env)?)),
        LevelView::IMax(a, b) => {
            let rb = eval(&b, env)?;
            if rb == 0 {
                Some(0)
            } else {
                Some(eval(&a, env)?.max(rb))
            }
        }
        LevelView::Param(n) => env.get(&n).copied(),
    }
}

/// `succ^n(zero)`.
pub fn numeral(n: u32) -> Level {
    let mut l = Level::zero();
    for _ in 0..n {
        l = l.succ();
    }
    l
}

/// A declaration's universe parameters bound to the numerals of `sigma`.
pub fn ground_env(uparams: &[Name], sigma: &[u32]) -> HashMap<Name, u32> {
    uparams.iter().cloned().zip(sigma.iter().copied()).collect()
}

/// A schedule entry as an instantiation: the level arguments a declaration's
/// own parameters stand for under `sigma`.
///
/// **The pre-pass boundary, and the only place a `Vec<u32>` becomes an
/// instantiation.** `LEVELPOLY.md` §5.3 step 5 deletes the schedule; what
/// replaces this call is the declaration's own parameters, `Level::param`
/// rather than `numeral`, and every consumer already takes that.
pub fn ground_levels(sigma: &[u32]) -> Vec<Level> { sigma.iter().map(|n| numeral(*n)).collect() }

/// The canonical spelling of an instantiation — what [`crate::interp::ConstKey`]
/// is keyed on, so that two spellings of one instantiation are one entry.
///
/// `Level::simplify` is the checker's `canon_level` discipline: it is the
/// identity on the numerals a ground schedule produces, so widening the key
/// moved no existing entry.
pub fn key_levels(levels: &[Level]) -> Vec<Level> {
    levels.iter().map(|l| l.simplify()).collect()
}

/// How an instantiation is *spelled* in a label, a dump row or a blocker
/// draft: a closed level as its numeral, an open one as the level expression.
///
/// The numeral branch is not cosmetic. Before the key widened, an
/// instantiation *was* a `Vec<u32>` and every reader printed `1`;
/// `Level`'s own `Display` prints the ladder, `(0+1)`. Rendering a ground key
/// any other way than as its numeral would move every fixture that names a
/// pair, for no reason, and would say the interpretation had changed when only
/// the key's type had.
pub fn show_level(l: &Level) -> String {
    match as_numeral(l) {
        Some(n) => n.to_string(),
        None => l.to_string(),
    }
}

/// An instantiation as a whole, spelled the way the `Vec<u32>` it replaced
/// was by `{:?}`: `[0, 1]`, and `[u]` where a level is open.
pub fn show_levels(levels: &[Level]) -> String {
    let parts: Vec<String> = levels.iter().map(show_level).collect();
    format!("[{}]", parts.join(", "))
}

/// A total order on instantiations that agrees with the numeric order of the
/// `Vec<u32>` it replaced.
///
/// Ground first, ordered by value — *not* by [`show_level`], which would put
/// `10` before `2` — then the open levels, ordered by their spelling. The
/// `Vec<u32>` this replaces sorted numerically, and a dump whose rows silently
/// reordered would be a diff nobody could read.
pub fn level_sort_key(l: &Level) -> (u8, u32, String) {
    match as_numeral(l) {
        Some(n) => (0, n, String::new()),
        None => (1, 0, l.to_string()),
    }
}

/// A declaration's expression at an instantiation: every universe parameter
/// replaced by the level standing for it. Lean's `instantiate_lparams`.
pub fn subst_levels(e: &E, uparams: &[Name], levels: &[Level]) -> E {
    let env: HashMap<Name, Level> = uparams.iter().copied().zip(levels.iter().copied()).collect();
    crate::expr::subst_level(e, &|n: &Name| match env.get(n) {
        Some(l) => *l,
        // As in `instantiate_lparams`: should not happen.
        None => Level::param(*n),
    })
}

/// A declaration's expression at a ground σ.
pub fn subst_ground(e: &E, uparams: &[Name], sigma: &[u32]) -> E {
    subst_levels(e, uparams, &ground_levels(sigma))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Level { Level::param(Name::simple(s)) }

    /// The semantics `checker::instantiations`' module doc states, pinned here
    /// so that mini's substitution and nanoda's scheduling cannot drift apart
    /// silently: they must agree about what σ *means*, or mini would look up
    /// interpretations at keys the pre-pass never scheduled.
    #[test]
    fn eval_matches_the_documented_semantics() {
        let env = ground_env(&[Name::simple("u"), Name::simple("v")], &[3, 0]);
        assert_eq!(eval(&Level::zero(), &env), Some(0));
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

    /// [`as_numeral`] is [`eval`] at a closed level, and it is `None` at
    /// exactly the levels that still mention a parameter.
    ///
    /// Both halves are asserted, because the `None` half is the one the
    /// de-scheduling turns into a live population: it is what every
    /// `Gap::SymbolicLevel` in the program is reporting, and a version of this
    /// function that answered `Some(0)` at a parameter would silently
    /// interpret `Sort u` as `Prop`.
    #[test]
    fn as_numeral_is_eval_at_a_closed_level_and_none_at_an_open_one() {
        let uparams = [Name::simple("u"), Name::simple("v")];
        let ls = [
            Level::imax(p("u"), p("v")),
            Level::max(p("u").succ(), p("v")),
            Level::imax(Level::max(p("u"), p("v")), p("v")).succ(),
            Level::max(Level::imax(p("u"), p("v")), p("u")),
        ];
        for l in &ls {
            // Open: no numeral, at every arity of parameter occurrence.
            assert_eq!(as_numeral(l), None, "{l} is not closed");
            for a in 0..3u32 {
                for b in 0..3u32 {
                    let env = ground_env(&uparams, &[a, b]);
                    let closed = l.subst(&|n: &Name| {
                        numeral(*env.get(n).expect("both parameters are bound"))
                    });
                    assert_eq!(as_numeral(&closed), eval(l, &env), "{l} at [{a},{b}]");
                }
            }
        }
    }

    /// [`key_levels`] is the identity on the numerals a ground schedule
    /// produces, which is why widening [`crate::interp::ConstKey`] moved no
    /// existing entry — and it is *not* the identity on a spelling that
    /// canonicalises, which is why it is applied at all.
    #[test]
    fn key_levels_is_the_identity_on_a_ground_schedule_entry() {
        for sigma in [vec![], vec![0], vec![0, 3], vec![2, 0, 7]] {
            let ls = ground_levels(&sigma);
            assert_eq!(key_levels(&ls), ls, "σ={sigma:?}");
        }
        // Three atoms, so the test cannot pass by an accident of arity or
        // order: `imax(u, 0)` canonicalises to `0` and the other two do not
        // move, and the vector is the three of them in that order.
        let raw = vec![Level::imax(p("u"), Level::zero()), p("v"), numeral(2)];
        assert_eq!(key_levels(&raw), vec![Level::zero(), p("v"), numeral(2)]);
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
    /// therefore evaluate levels with [`as_numeral`] rather than pattern-match
    /// a simplified level for `succ^n zero`.
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
                    let g = crate::expr::sort(*l);
                    let g = subst_ground(&g, &uparams, &[a, b]);
                    let crate::expr::Expr::Sort(gl) = &g.view() else { unreachable!() };
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
