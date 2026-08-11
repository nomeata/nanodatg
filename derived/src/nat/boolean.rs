//! **The two-valued decode**: from `ω`'s `succ 0`/`0` to a caller-supplied pair.
//!
//! # Interface
//!
//! Writing `t` and `f` for two arbitrary sets the caller supplies:
//!
//! ```text
//! boolify(t,f,n) := app({⟨succ 0, t⟩, ⟨0, f⟩}, n)
//!
//! ⊢ ∀t ∀f. boolify(t,f,succ 0) = t                       [Boolean::boolify_one]
//! ⊢ ∀t ∀f. boolify(t,f,0)      = f                      [Boolean::boolify_zero]
//!
//! ── and the three comparisons, decoded ──────────────────────────────────
//! bleb(t,f,x,y) := boolify(t,f,ble(x,y))                 [Boolean::bleb_ax]
//! bltb(t,f,x,y) := boolify(t,f,blt(x,y))                 [Boolean::bltb_ax]
//! beqb(t,f,x,y) := boolify(t,f,beq(x,y))                 [Boolean::beqb_ax]
//! ```
//!
//! [`crate::nat::Eval::ble_bool`], [`blt_bool`](crate::nat::Eval::blt_bool) and
//! [`beq_bool`](crate::nat::Eval::beq_bool) evaluate those at numerals, over a
//! [`Decode`] — the bundle of this and the two values — and are the entry a
//! consumer actually calls. [`crate::nat::ble_uniqueness`] is what connects an
//! *imported* operation to `bleb` so that they say something about it.
//!
//! # What this exists for, measured
//!
//! [`crate::nat::Compare`] is **`ω`-valued**: `ble(x,y)` is `iszero(sub(x,y))`,
//! which is `succ 0` or `0`, because that is what lets every equation about it
//! be an equation between terms of `ω` and never a disjunction — see
//! [`compare`](crate::nat::compare)'s header, *Why there is no order relation
//! here, and no truth value*.
//!
//! A checker importing a two-valued type does not want `succ 0`. It wants the
//! two elements **its own** translation produced, and it cannot be told what
//! they are: `derived/` does not know what `Bool` is and must not learn. So the
//! decode takes them as arguments, and this file is the reason
//! `MEASUREMENTS.md`'s "Origin 2 is not the bignum bridge" could name a piece
//! of missing work rather than a piece of missing wiring — the comparison
//! evaluator existed and was complete, and there was no occurrence of the word
//! `Bool` anywhere in `derived/src/nat/` because there could not be one.
//!
//! # Why there is no recursion here, and no case split
//!
//! The obvious definition is `natrec(f, const t, n)`, and it is the wrong one
//! twice over: `natrec`'s step is applied as `app(app(g,n), r)`, so `const t`
//! has to be a *set* that is a function on two arguments, and the ι rule at
//! `succ` carries an `n ∈ ω` side condition the decode does not need. The
//! second obvious definition is by cases on `n = 0`, which is a classical split
//! and a discharge.
//!
//! Neither is necessary, because a decode of a **two**-valued input is a
//! function on two points, and [`crate::twopoint`] is exactly that:
//!
//! ```text
//! ⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app({⟨a,b⟩,⟨c,d⟩}, a) = b)
//! ⊢ ∀a ∀b ∀c ∀d. (¬(a = c) → app({⟨a,b⟩,⟨c,d⟩}, c) = d)
//! ```
//!
//! with **no** typing of `b` and `d` — the header of that file says so, and it
//! is the property this construction lives on, since `t` and `f` are sets about
//! which nothing whatever is known. Instantiating at `a := succ 0`, `c := 0`
//! makes the shared antecedent `¬(succ 0 = 0)`, which is
//! [`Nat::succ_ne_zero`](crate::nat::Nat::succ_ne_zero) at `0` — discharged
//! once, for both equations. That ordering is the only design choice in the
//! file and it is what removes a `¬`-symmetry step — **do not reverse it for
//! symmetry's sake**: `0` first reads more naturally and costs a `¬`-symmetry
//! derivation that this way round is simply absent.
//!
//! So both exports are **unconditional and O(1)**: no induction, no hypothesis,
//! and nothing proved about `ω` beyond `succ 0 ≠ 0`.
//!
//! # What it costs, measured
//!
//! The decode is **fifteen kernel inferences flat**, at every operand width —
//! `derived/tests/nat.rs` asserts that rather than printing it. So a decoded
//! comparison is `12·bits + 22`:
//!
//! | operands | `ble` | `ble_bool` |
//! |---|---:|---:|
//! | 4 bits | 55 | **70** |
//! | 64 bits | 775 | 790 |
//!
//! Four bits is the row that matters: `MEASUREMENTS.md`'s census of a whole
//! certifying run of `init-prelude` finds **612 of 643** accelerated
//! comparisons at four bits or fewer, and the 466 that block an ι rule are 55
//! distinct instances with every operand ≤ 12.
//!
//! # Non-vacuity
//!
//! `t` and `f` are universally quantified and the two equations have visibly
//! different right-hand sides, so neither is an instance of the other. That
//! they are not both provable of one `n` is `succ 0 ≠ 0` and nothing else.
//! `derived/tests/nat.rs` fires the pair at two fresh constants and reads both
//! values back off one graph.

use kernel::{Env, FnSym, Term, Thm};

use crate::err::DResult;
use crate::prim;
use crate::rules::{define_abbrev, inst_all};
use crate::twopoint::TwoPoint;

use super::apparatus::Nat;
use super::compare::Compare;
use super::glue::{gen_all, imported, Chain};

/// A [`Boolean`] together with the two values to decode onto.
///
/// They always travel together — every entry that needs the decode needs both
/// values, and a signature taking them apart hit clippy's argument limit at
/// [`Eval::ble_bool`](crate::nat::Eval::ble_bool), which was the right
/// complaint about the wrong thing: the fix is that this is one datum.
pub struct Decode<'a> {
    /// The decode's symbols and equations.
    pub bl: &'a Boolean,
    /// What `ble` decodes to when it holds.
    pub t: &'a Term,
    /// What it decodes to when it does not.
    pub f: &'a Term,
}

impl<'a> Decode<'a> {
    /// Pair a decode with the two values.
    pub fn new(bl: &'a Boolean, t: &'a Term, f: &'a Term) -> Decode<'a> { Decode { bl, t, f } }
}

/// The decode, and the three comparisons composed with it.
pub struct Boolean {
    /// The symbol `boolify(t,f,n)`.
    pub boolify: FnSym,
    /// `⊢ ∀t ∀f ∀n. boolify(t,f,n) = app({⟨succ 0, t⟩, ⟨0, f⟩}, n)`.
    pub boolify_ax: Thm,
    /// `⊢ ∀t ∀f. boolify(t,f,0) = f`.
    pub boolify_zero: Thm,
    /// `⊢ ∀t ∀f. boolify(t,f,succ 0) = t`.
    pub boolify_one: Thm,

    /// The symbol `bleb(t,f,x,y)`.
    pub bleb: FnSym,
    /// `⊢ ∀t ∀f ∀x ∀y. bleb(t,f,x,y) = boolify(t,f,ble(x,y))`.
    pub bleb_ax: Thm,
    /// The symbol `bltb(t,f,x,y)`.
    pub bltb: FnSym,
    /// `⊢ ∀t ∀f ∀x ∀y. bltb(t,f,x,y) = boolify(t,f,blt(x,y))`.
    pub bltb_ax: Thm,
    /// The symbol `beqb(t,f,x,y)`.
    pub beqb: FnSym,
    /// `⊢ ∀t ∀f ∀x ∀y. beqb(t,f,x,y) = boolify(t,f,beq(x,y))`.
    pub beqb_ax: Thm,
}

impl Boolean {
    /// The term `boolify(t,f,n)`.
    pub fn boolify_of(&self, t: Term, f: Term, n: Term) -> Term {
        Term::apply(self.boolify, vec![t, f, n])
    }

    /// The term `bleb(t,f,x,y)`.
    pub fn bleb_of(&self, t: Term, f: Term, x: Term, y: Term) -> Term {
        Term::apply(self.bleb, vec![t, f, x, y])
    }

    /// The term `bltb(t,f,x,y)`.
    pub fn bltb_of(&self, t: Term, f: Term, x: Term, y: Term) -> Term {
        Term::apply(self.bltb, vec![t, f, x, y])
    }

    /// The term `beqb(t,f,x,y)`.
    pub fn beqb_of(&self, t: Term, f: Term, x: Term, y: Term) -> Term {
        Term::apply(self.beqb, vec![t, f, x, y])
    }

    /// Define the four symbols and derive the two decode equations.
    pub fn new(env: &mut Env, nat: &Nat, cmp: &Compare) -> DResult<Boolean> {
        let ap = nat.rec.ap.clone();
        let tp = imported("crate::twopoint::TwoPoint::over", TwoPoint::over(env, &ap))?;

        let zero = nat.zero();
        let one = nat.succ_of(zero.clone());

        let (tv, fv, nv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tt, tf, tn) = (Term::var(tv), Term::var(fv), Term::var(nv));

        // ── the graph, and the symbol that applies it ────────────────────────
        //
        // `succ 0` first, `0` second: `TwoPoint`'s antecedent is `¬(a = c)`, so
        // this way round it is `¬(succ 0 = 0)` — exactly `succ_ne_zero`, with no
        // symmetry step between them.
        let graph = TwoPoint::of(&ap, one.clone(), tt.clone(), zero.clone(), tf.clone());
        let (boolify, boolify_ax) =
            define_abbrev(env, &[tv, fv, nv], &ap.apply(graph, tn.clone()))?;

        // ── the shared antecedent, discharged once ───────────────────────────
        let ne = prim::mp(
            &inst_all(nat.succ_ne_zero(), std::slice::from_ref(&zero))?,
            nat.zero_mem(),
        )?;
        let at = |thm: &Thm| -> DResult<Thm> {
            prim::mp(
                &inst_all(thm, &[one.clone(), tt.clone(), zero.clone(), tf.clone()])?,
                &ne,
            )
        };
        // `⊢ app(graph, succ 0) = t` and `⊢ app(graph, 0) = f`.
        let (at_one, at_zero) = (at(&tp.left)?, at(&tp.right)?);

        let decode = |env: &mut Env, arg: &Term, step: Thm| -> DResult<Thm> {
            let unfold = inst_all(&boolify_ax, &[tt.clone(), tf.clone(), arg.clone()])?;
            let out = Chain::from(unfold).then(step).done(env)?;
            gen_all(&[tv, fv], &out)
        };
        let boolify_one = decode(env, &one, at_one)?;
        let boolify_zero = decode(env, &zero, at_zero)?;

        // ── the three comparisons, composed with the decode ──────────────────
        let (xv, yv) = (env.fresh_var(), env.fresh_var());
        let (tx, ty) = (Term::var(xv), Term::var(yv));
        let composed = |env: &mut Env, inner: Term| {
            let body = Term::apply(boolify, vec![tt.clone(), tf.clone(), inner]);
            define_abbrev(env, &[tv, fv, xv, yv], &body)
        };
        let (bleb, bleb_ax) = composed(env, cmp.ble_of(tx.clone(), ty.clone()))?;
        let (bltb, bltb_ax) = composed(env, cmp.blt_of(tx.clone(), ty.clone()))?;
        let (beqb, beqb_ax) = composed(env, cmp.beq_of(tx, ty))?;

        Ok(Boolean {
            boolify,
            boolify_ax,
            boolify_zero,
            boolify_one,
            bleb,
            bleb_ax,
            bltb,
            bltb_ax,
            beqb,
            beqb_ax,
        })
    }
}
