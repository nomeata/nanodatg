//! The recursion theorem, and the symbol it licenses.
//!
//! # Interface
//!
//! [`recursion`] runs the whole approximation argument and returns
//!
//! ```text
//! ⊢ ∃!f. RecFn(f)                                        [Recursion::exists_unique]
//! ⊢ RecFn(iter(c))                                       [Recursion::iter_ax]
//! ⊢ app(iter(c), 0) = c                                  [Recursion::base]
//! ⊢ ∀n. (n ∈ ω → app(iter(c), succ n) = G(app(iter(c), n)))   [Recursion::step]
//! ```
//!
//! where `RecFn` is [`crate::recursion::rec_fn`]'s five conjuncts — `f` is a
//! single-valued set of pairs with domain exactly `ω`, `app(f,0) = c`, and `f`
//! steps by `G`.
//!
//! # What `params` is for
//!
//! `G` is a *function symbol* of the ambient extension, so it cannot be an
//! argument of the symbol being defined; `c` is a *term*, so it can. Passing
//! `params = [cv]` with `c = cv` a free variable makes `iter` unary and its
//! defining axiom `⊢ ∀c. RecFn(iter(c))`; passing `params = []` with a closed
//! `c` makes it a constant. Anything free in `c` must appear in `params`, or
//! [`kernel::thm::define`] refuses — see the soundness note there.
//!
//! # Why the `∃!` is not bookkeeping
//!
//! It is what licenses the symbol at all. Existence is
//! [`crate::recursion::Iter::property`], the end of the approximation argument;
//! uniqueness is [`crate::recursion::rec_unique`]. Without the second half
//! `define` would be Skolemisation, which this kernel does not offer and — as
//! [`kernel::thm::define`] records — could not offer soundly at arity ≥ 1 in the
//! presence of an unrestricted Replacement scheme.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{a1i, and_intro, gen_all, hyp_and, imp_refl, inst_all, syl};
use super::agree::{approx_agree, approx_subset, approx_unique, omega_is_transitive};
use super::approximation::approx_dom;
use super::existence::approx_exists;
use super::family::family;
use super::iterate::{iterate, rec_fn, Iter, RecFn};
use super::rec::Rec;
use super::unique::{rec_agree, rec_subset, rec_unique};

/// The recursion theorem, its witness, and the symbol it licenses.
pub struct Recursion {
    /// The graph, and everything proved about it on the way.
    pub it: Iter,
    /// `⊢ ∃!f. RecFn(f)`.
    pub exists_unique: Thm,
    /// The symbol `iter`, of arity `params.len()`.
    pub iter: FnSym,
    /// `⊢ RecFn(iter(params))`, instantiated back at the parameters.
    pub iter_ax: Thm,
    /// `⊢ app(iter(params), 0) = c`.
    pub base: Thm,
    /// `⊢ ∀n. (n ∈ ω → app(iter(params), succ n) = G(app(iter(params), n)))`.
    pub step: Thm,
    /// The specification `RecFn(iter(params))`, as a formula.
    pub spec: RecFn,
    /// The term `iter(params)`.
    pub term: Term,
}

impl Recursion {
    /// The term `iter(params)`.
    pub fn set(&self) -> Term { self.term.clone() }
}

/// Derive the recursion theorem for base `c` and unary step symbol `g`, and
/// define `iter`.
///
/// `params` must cover every free variable of `c`; see the module header.
pub fn recursion(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    params: &[FreeVar],
) -> Option<Recursion> {
    // ── The approximation argument ───────────────────────────────────────────
    let dom = approx_dom(env, r, g, c)?;
    let om_trans = omega_is_transitive(env, r)?;
    let agree = approx_agree(env, r, g, c)?;
    let subset = approx_subset(env, r, g, c, &agree, &om_trans)?;
    let unique = approx_unique(env, r, g, c, &subset)?;
    let exists = approx_exists(env, r, g, c, &dom, &om_trans)?;
    let fam = family(env, r, g, c, &exists, &unique, params)?;
    let it = iterate(env, r, g, c, fam, &unique, &exists, &agree)?;

    // ── Uniqueness, then `∃!` ────────────────────────────────────────────────
    let ragree = rec_agree(env, r, g, c)?;
    let rsubset = rec_subset(env, r, g, c, &ragree)?;
    let runique = rec_unique(env, r, g, c, &rsubset)?;

    let (f, f2) = (env.fresh_var(), env.fresh_var());
    let (tf, tf2) = (Term::var(f), Term::var(f2));
    let phi = rec_fn(env, r, g, c, &tf)?.formula();
    let phi2 = rec_fn(env, r, g, c, &tf2)?.formula();
    let gam = it.set();
    debug_assert_eq!(
        *it.property.concl(),
        phi.subst(f, &gam),
        "recursion: the existence half is about a different set"
    );

    let at = inst_all(&runique, &[tf2.clone(), gam.clone()])?;
    let only = syl(
        &hyp_and(&imp_refl(phi2.clone()), &a1i(&it.property, phi2.clone()))?,
        &at,
    )?;
    debug_assert_eq!(
        *only.concl(),
        Formula::imp(phi2.clone(), Formula::eq(tf2.clone(), gam.clone())),
        "recursion: the uniqueness half drifted"
    );

    let uniq_part = Formula::forall(
        f2,
        Formula::imp(phi.subst(f, &tf2), Formula::eq(tf2, tf)),
    );
    let eu_body = Formula::and(phi.clone(), uniq_part);
    let witness = and_intro(&it.property, &Thm::gen(f2, &only));
    let exists_unique = crate::exists_intro(f, eu_body, gam, &witness)?;
    debug_assert_eq!(
        *exists_unique.concl(),
        kernel::thm::exists_unique(env, f, &phi),
        "recursion: the ∃! obligation drifted"
    );

    // ── The symbol ───────────────────────────────────────────────────────────
    let (iter, closed) =
        kernel::thm::define(env, params, f, phi, &gen_all(params, &exists_unique))?;
    let args: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let term = Term::apply(iter, args.clone());
    let iter_ax = inst_all(&closed, &args)?;
    let spec = rec_fn(env, r, g, c, &term)?;
    debug_assert_eq!(*iter_ax.concl(), spec.formula(), "recursion: unexpected shape");

    let base = Thm::mp(&spec.proj(3)?, &iter_ax)?;
    let step = Thm::mp(&spec.proj(4)?, &iter_ax)?;
    Some(Recursion { it, exists_unique, iter, iter_ax, base, step, spec, term })
}

// ─────────────────────────────────────────────────────────────────────────────
// Closing note — 2026-07-31, the session that finished the recursion theorem.
//
// WHAT IS DONE. All six steps of the plan recorded in `crate::recursion`'s
// header are complete and pinned by tests in `derived/tests/recursion.rs`:
//
//   1. `Approx` — codomain-free, in `approximation`, plus `approx_dom`
//      ("an approximation holds no pair outside its domain"), which every
//      extension argument needs and which was missing;
//   2. `approx_one` and `approx_extend`, in `existence`;
//   3. `approx_exists` (induction) and `approx_unique` (via the two-domain
//      `approx_agree` and `approx_subset`);
//   4. `family` — Replacement over ω;
//   5. `iterate` — `⊢ RecFn(Γ)`;
//   6. `rec_unique`, then `recursion` above, then `omega_tower`.
//
// Three things were changed rather than added, and a reader of the old notes
// should know:
//
//   * `approx_agree` now has TWO domains. Its hypothesis is
//     `m₁ ∈ ω ∧ Approx(m₁,h₁) ∧ m₂ ∈ ω ∧ Approx(m₂,h₂) ∧ k ∈ m₁ ∧ k ∈ m₂`. The
//     proof is unchanged in substance — the domains are used only for
//     transitivity — but R5 of the final theorem cannot be proved without it,
//     because `app(f,succ n)` and `app(f,n)` are read off approximations with
//     *different* domains. `approx_subset` instantiates it at `m₁ = m₂`.
//   * The Replacement instance sends `n` to the PAIR `⟨n, app(hₙ,n)⟩`, not to
//     `hₙ`. The image is then the graph outright and no `⋃` is taken; step 5 of
//     the old plan ("`⋃` of that set is a function") does not exist. This is
//     what keeps single-valuedness of the result a one-domain statement.
//   * `family` and `recursion` take a `params: &[FreeVar]` list, because
//     `kernel::thm::define` rejects a definition whose condition has a free
//     variable outside the parameters. Pass `[cv]` with `c = Term::var(cv)` to
//     get a unary `iter`; pass `[]` with a closed `c` to get a constant.
//
// THE OLD CLOSING NOTE, AND WHY IT IS WRONG. This note used to read "WHAT IS
// NOT DONE, AND IS THE NEXT STEP. `W(A,B,u) ∈ u` is still open, and it is the
// whole reason this file exists." Both halves are false, and the record is kept
// because the corrections are more useful than the deletion would be.
//
// `W(A,B,u) ∈ u` is not open — it is **refutable** at the `u` this development
// uses. `crate::cumul` proves the point (`V_ω` is a universe, `A ∈ V_ω` makes
// every member of `U(A)` finite, and the deleted `wnat` made `W(A,B,U(A))`
// infinite); `crate::cumul::wmem` repeats it. The correct target is
// `W(A,B,U(A)) ∈ U(c)` for a universe `c` with `ω ∈ U(c)` — a size statement
// whose size content is `ω`.
//
// The three "next steps" the note listed were carried out in `crate::cumul`,
// and two of the three were the wrong shape. `cumul.rs`'s "WHAT THE PREVIOUS
// HANDOVER GOT WRONG" section is that analysis and is the thing to read:
//
//   * the stage function cannot be a unary `FnSym` built from Product/Funspace
//     (a `define_abbrev` symbol may mention no free variables outside its own
//     parameters), so the parametric data enters through the recursion's
//     **base** and the step is the closed `G(x) = x ∪ 𝒫x`;
//   * no second universe-relative copy of `omega_tower`'s Replacement instance
//     is needed — three `⋃`-closures and `C₂` place the union in `U(c)`;
//   * `W ⊆ ⋃ₙWₙ` is not an induction over `crate::wtype::rect`; plain
//     `w_induction` suffices, and the genuinely new content is `closed(A,B,T)`,
//     which is where finite branching enters.
//
// So this file's exports stand on their own (see the header), and nothing below
// is waiting on the items above.
//
// A WARNING ABOUT COST. Every lemma here was written one at a time, each with a
// test pinning its exact conclusion at fresh constants, and each was compiled
// and run before the next was started. Two of the three failures encountered all
// session were `Option::None` from a combinator guard with no message; both were
// localised in under a minute by inserting `eprintln!` checkpoints between the
// `let` bindings and re-running the single test. Do that rather than reading.
// The one shape error (`mpd_const` discharges the *inner* antecedent, not the
// outer one) would have cost an hour by inspection.
