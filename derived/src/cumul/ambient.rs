//! **The chain over an ambient signature the caller already has.**
//!
//! # Interface
//!
//! ```text
//! Chain::over(env, tower, wt, bound) -> Option<Chain>
//! ```
//!
//! [`Chain::new`] mints its own [`Tower`] — its own `∅`, `ω`, `𝒫`, `U(·)`,
//! [`Sums`](crate::sums::Sums) and [`Wtype`] — and everything it proves is about
//! *those* symbols. A client that already has a signature therefore cannot use a
//! word of it: a theorem about one `W` says nothing about another, and the
//! failure is silent, showing up as a `None` from some lemma that looks
//! unrelated.
//!
//! This constructor is [`Chain::new`] with the minting removed. It takes
//!
//! * a [`Tower`] — for `ω`, for `U₁ = U(ω)`, and for the five `∀c` closure
//!   theorems the stages need;
//! * a [`Wtype`] and a [`Bound`] — the caller's, so that `W(A,B,U(c))` in the
//!   chain's conclusions is the caller's `W`;
//!
//! and clones what it needs out of them, which is why
//! [`Sums`](crate::sums::Sums), [`Wtype`], [`Bound`],
//! [`Space`](crate::funspace::in_universe::Space),
//! [`Peano`](crate::recursion::Peano) and
//! [`OmegaCore`](crate::recursion::OmegaCore) are `Clone`. Cloning one is a
//! handful of `Thm` and `Term` clones and copies **the same symbols** — the
//! point of the exercise, and the opposite of rebuilding.
//!
//! # The two guards
//!
//! Handing in a `Wtype` and a `Bound` from a *different* chain than the `Tower`
//! is exactly the mistake this file exists to make impossible, and it is not
//! detectable from the types. Two symbol comparisons catch it:
//!
//! * `wt.sums.ap.sets.up == tower.sums.ap.sets.up` — one pairing, hence one
//!   ordered pair, hence one `app`;
//! * `bound.lu == tower.space.lu` — one `U(·)`, hence `U₁` really is a universe
//!   the chain's conclusions can land in.
//!
//! They are necessary, not sufficient: the sufficient check is that the
//! conclusion of the theorem finally wanted is the formula the caller claims,
//! and [`super::NatMem::over`] makes it.

use kernel::Env;

use crate::bound::Bound;
use crate::funcs::Apply;
use crate::recursion::{app_of_graph, Rec};
use crate::tower::Tower;
use crate::wtype::Wtype;

use super::chain::{Chain, Closures};

impl Chain {
    /// Build the chain over a caller-supplied [`Tower`], [`Wtype`] and
    /// [`Bound`], so that its conclusions are about the caller's own symbols.
    ///
    /// `None` if the three did not come from one signature; see the module
    /// header for the two comparisons that decide it.
    pub fn over(env: &mut Env, tower: &Tower, wt: &Wtype, bound: &Bound) -> Option<Chain> {
        if wt.sums.ap.sets.up != tower.sums.ap.sets.up
            || wt.sums.pow != tower.space.pow
            || bound.lu != tower.space.lu
        {
            return None
        }

        let u1 = tower.at(1)?;
        let ap: Apply = tower.sums.ap.clone();
        let cl = Closures {
            pow_all: tower.pow.clone(),
            union_all: tower.union.clone(),
            bin_union_all: tower.bin_union.clone(),
            transitive_all: tower.transitive.clone(),
            sub_all: tower.sub.clone(),
        };

        let app_of_graph = app_of_graph(env, &ap)?;
        let r = Rec { ap, peano: tower.peano.clone(), app_of_graph };

        Chain::assemble(env, r, u1, tower.space.clone(), wt.clone(), bound.clone(), cl)
    }
}
