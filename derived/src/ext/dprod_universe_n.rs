//! **Lean's `Π` typing rule at a parameter prefix** — the n-ary
//! `dprod_in_universe_pair`, with no antecedent left over.
//!
//! # Interface
//!
//! For a fibre symbol `b` of arity `k+1`, writing `U(c)` for
//! [`crate::universe::least_universe`], `img(q⃗,A) = { b(q⃗,x) : x ∈ A }` and
//! `dprod(q⃗,A) = Π(x:A). b(q⃗,x)`, the exports are
//!
//! ```text
//! ⊢ ∀q⃗ ∀A ∀c. ((A ∪ ⋃img(q⃗,A)) ∈ U(c) → dprod(q⃗,A) ∈ U(c))
//!                                                     [dprod_in_universe_of_n]
//! ⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(q⃗,x) ∈ U(c))) → dprod(q⃗,A) ∈ U(c))
//!                                                   [dprod_in_universe_pair_n]
//! ```
//!
//! The second is **the form the checker wants**: a base set in a universe, every
//! fibre in the same universe, and the dependent product in it too — with the
//! parameter prefix its skeleton decomposition gives it. Callers need none of
//! the derivation below, and [`DProdN`] plus
//! [`crate::universe::least_universe_replacement_n`] is the whole ingredient
//! list.
//!
//! # Why the prefix is the case that matters
//!
//! [`super::dprod_in_universe_pair`] is this statement for a **unary** fibre.
//! That is the rare shape: a dependent `Π` whose body mentions only its own
//! binder and nothing of the ambient context arises **11 times** on
//! `init-prelude` (`checker/src/tg.rs`, "The n-ary dependent product"), while
//! `ty_pi` has 5269 sites there of which 2903 are definitely into `Type`
//! (`MEASUREMENTS.md:1224`). `checker/src/tg.rs:6642` records the `Pi` clause as
//! a counted decline for exactly this reason — "needs `dprod_in_universe`, whose
//! n-ary port does not exist" — and this file is that port.
//!
//! **Wiring the `tg.rs` consumer is deliberately not part of this file.** What
//! is delivered is the rule; the clause that calls it is separate, later work,
//! and until it lands the measured population above is unblocked rather than
//! closed. See the honest accounting in the entry this was built from.
//!
//! # The derivation, and what each step costs
//!
//! Identical to the unary original, which is the point — the prefix rides in the
//! argument lists and is generalised at the end, and no step takes a fibre term
//! apart. Two halves:
//!
//! **The reduction** ([`dprod_in_universe_of_n`]). Everything above the base set
//! is already available and each step is one of the closure properties
//! [`crate::universe`] proves for `U(x)`:
//!
//! ```text
//! dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))     — `DProdN::dprod_sub`, unconditional
//! fs(a,b)    ⊆ 𝒫(prod(a,b))          — `funspace_subset_pow_prod`
//! prod(a,b)  ⊆ 𝒫𝒫(a ∪ b)             — `product_subset_pow_pow`
//! ```
//!
//! so [`crate::funspace::funspace_in_universe_of`] carries the middle two — and
//! it is `b`-independent, hence reused verbatim rather than ported — and one
//! more `C₂` adds the first. What is left is a single membership,
//! `(A ∪ ⋃img(q⃗,A)) ∈ U(c)`.
//!
//! **Discharging it** ([`dprod_in_universe_pair_n`]), in three closure steps:
//!
//! * Replacement, to put `img(q⃗,A)` in `U(c)` —
//!   [`crate::universe::least_universe_replacement_n`], the one ingredient that
//!   had to be ported, since it is the only one that mentions `b`;
//! * `⋃`-closure, to strip it to `⋃img(q⃗,A)` —
//!   [`crate::universe::least_universe_union`], fibre-independent, reused;
//! * binary union, to add the base set —
//!   [`crate::universe::least_universe_bin_union`], likewise.
//!
//! Until 2026-07-31 all three were *refutable*, not merely unproved: see the
//! countermodels at the end of [`crate::universe`] and the date note on
//! [`super::dprod_in_universe_of`]. They became available when the transitivity
//! clause was added to Tarski's Axiom A, and this file is the first construction
//! to spend all three at once at a prefixed fibre.
//!
//! # One universe, and what has to happen before this rule fires
//!
//! The rule types the base, the fibres and the product **at the same `U(c)`**.
//! Lean's does not: `Π (x : A), B x` has `A : Sort u`, `B x : Sort v` and the
//! product in `Sort max(u,v)`. So a consumer holds `⟦A⟧ ∈ U_u` and
//! `∀x ∈ ⟦A⟧. b(q⃗,x) ∈ U_v` and must raise both to `U_max(u,v)` first. That is
//! [`crate::tower::Cumul`] — `Cumul::raise` for the base and
//! `Cumul::fibres_mono` for the fibres, the latter being exactly this rule's
//! second conjunct under its binder. `Cumul` is a **named consumer-side
//! prerequisite, not a dependency of this file**: nothing below mentions the
//! tower, and the rule is stated at a quantified `c` so that any rung
//! instantiates it.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::{bin_union, Funspace};
use crate::universe::fibres_in_n;
use crate::{a1i, and_left, gen_all, hyp_and, hyp_mp, inst_all, syl};

use super::dprod_n::{base_of_n, sym_at, DProdN};

/// **One fibre family's stack**: the three symbols, and the two theorems about
/// them the `Π` rule spends.
///
/// The symbols-plus-proved-properties discipline `checker`'s `lam_in_dprod_n`
/// takes, as a named struct rather than a tuple. The symbols are built by
/// whoever owns the interpretation — [`DProdN::new`] here, `TgBackend::fibre` in
/// the checker — and the rules below rebuild every shape they need from `b`
/// alone and compare, so a stack that does not fit together is refused rather
/// than silently described. The defining axioms `img_ax` and `dprod_def` are
/// *not* carried: nothing here consumes them directly, and the two theorems that
/// are carried are the ones each rule actually checks. Whoever builds them has
/// already checked them against the axioms
/// ([`super::dprod_n::dprod_members_n`]).
pub struct Fibre<'a> {
    /// The fibre symbol `b(q⃗,x)`, of arity `k+1`. Every other arity here is
    /// read off this one.
    pub b: FnSym,
    /// The Replacement image `img(q⃗,A) = { b(q⃗,x) : x ∈ A }`.
    pub img: FnSym,
    /// The dependent product `dprod(q⃗,A) = Π(x:A). b(q⃗,x)`.
    pub dprod: FnSym,
    /// `⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))` —
    /// [`super::dprod_n::dprod_subset_funspace_n`].
    pub dprod_sub: &'a Thm,
    /// `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → img(q⃗,A) ∈ U(c))` —
    /// [`crate::universe::least_universe_replacement_n`]. The only ingredient
    /// that mentions `b`, and hence the only one that had to be ported.
    pub replacement: &'a Thm,
}

impl Fibre<'_> {
    /// The prefix length `k`, or `None` if the three symbols' arities disagree.
    fn arity(&self) -> Option<usize> {
        let k = (self.b.arity() as usize).checked_sub(1)?;
        (self.img.arity() as usize == k + 1 && self.dprod.arity() as usize == k + 1)
            .then_some(k)
    }
}

/// **The universe apparatus**, none of which mentions the fibre.
///
/// Grouped for the same reason [`crate::funspace::Space`] is: the five entries
/// are not independent — every theorem must be about the *same* `U(·)` symbol —
/// and passing them loose is how a caller ends up mixing two universe operators.
/// Each is rebuilt at the rule's own terms and compared, so a mismatch is `None`.
pub struct UniverseParts<'a> {
    /// The least-universe operator `U(·)`, of arity 1.
    pub lu: FnSym,
    /// `⊢ ∀x. C₂(U(x))` — [`crate::universe::least_universe_closed_sub`].
    pub c2: &'a Thm,
    /// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))` —
    /// [`crate::funspace::funspace_in_universe_of`].
    pub fs_in_u: &'a Thm,
    /// `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))` —
    /// [`crate::universe::least_universe_union`].
    pub union: &'a Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))` —
    /// [`crate::universe::least_universe_bin_union`].
    pub bin_union: &'a Thm,
}

impl DProdN {
    /// This dependent product as the [`Fibre`] stack the rules below take,
    /// given the Replacement lemma proved for its image.
    pub fn fibre<'a>(&'a self, replacement: &'a Thm) -> Fibre<'a> {
        Fibre {
            b: self.b,
            img: self.img,
            dprod: self.dprod,
            dprod_sub: &self.dprod_sub,
            replacement,
        }
    }
}

/// `⊢ ∀q⃗ ∀A ∀c. ((A ∪ ⋃img(q⃗,A)) ∈ U(c) → dprod(q⃗,A) ∈ U(c))` — the dependent
/// product lands in any universe its base set does.
///
/// `dprod(q⃗,A)` is a subset of `fs(A, ⋃img(q⃗,A))` outright
/// ([`DProdN::dprod_sub`], unconditional), so `C₂` carries it in as soon as the
/// function space is there, and that is
/// [`crate::funspace::funspace_in_universe_of`] verbatim — no port needed, since
/// it says nothing about `b`. **The antecedent is the same one that lemma
/// carries**; nothing is lost and nothing new is assumed.
///
/// `u.c2` and `u.fs_in_u` must be for the same `lu` and the same `fsp`, and
/// `fibre.dprod_sub` must be what
/// [`super::dprod_n::dprod_subset_funspace_n`] produced for this stack. All of
/// it is rebuilt at our own terms and compared.
pub fn dprod_in_universe_of_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    fibre: &Fibre<'_>,
    u: &UniverseParts<'_>,
) -> Option<Thm> {
    let (img, dprod, lu) = (fibre.img, fibre.dprod, u.lu);
    let k = fibre.arity()?;
    if lu.arity() != 1 {
        return None
    }
    let qs: Vec<_> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, cv) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(av), Term::var(cv));
    let w = Term::apply(lu, vec![tc.clone()]); // U(c)

    let base = base_of_n(ap, img, &qts, &ta); // ⋃img(q⃗,A)
    let un = bin_union(&ap.sets, ta.clone(), base.clone()); // A ∪ ⋃img(q⃗,A)
    let fs_t = fsp.of(ta.clone(), base.clone());
    let dp_t = sym_at(dprod, &qts, ta.clone());
    let h = Formula::mem(un, w.clone());

    // `H → fs(A,⋃img(q⃗,A)) ∈ U(c)`, the whole of the function-space chain.
    let fs_at = inst_all(u.fs_in_u, &[ta.clone(), base, tc.clone()])?;
    if *fs_at.concl() != Formula::imp(h.clone(), Formula::mem(fs_t.clone(), w.clone())) {
        return None
    }

    // `C₂(U(c))`, and the subset step it licenses.
    let c2_at = inst_all(u.c2, std::slice::from_ref(&tc))?;
    if *c2_at.concl() != crate::universe::closed_sub(env, &w) {
        return None
    }
    let sc = crate::funspace::sub_closed(&c2_at, &fs_t, &dp_t)?;

    let mut sargs = qts;
    sargs.push(ta);
    let sub = inst_all(fibre.dprod_sub, &sargs)?;
    if *sub.concl() != kernel::thm::subset(env, dp_t.clone(), fs_t) {
        return None
    }

    let out = hyp_mp(&syl(&fs_at, &sc)?, &a1i(&sub, h.clone()))?;
    // Not a `debug_assert`: this is the statement the caller relies on.
    if *out.concl() != Formula::imp(h, Formula::mem(dp_t, w)) {
        return None
    }
    let mut all = qs;
    all.push(av);
    all.push(cv);
    Some(gen_all(&all, &out))
}

/// `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(q⃗,x) ∈ U(c))) → dprod(q⃗,A) ∈ U(c))`
/// — **Lean's dependent `Π` typing rule at a parameter prefix**.
///
/// Three closure properties, in order: Replacement puts `img(q⃗,A)` in `U(c)`,
/// `⋃`-closure puts `⋃img(q⃗,A)` there, binary union puts `A ∪ ⋃img(q⃗,A)` there,
/// and [`dprod_in_universe_of_n`] finishes.
///
/// `fibre.replacement` must be what
/// [`crate::universe::least_universe_replacement_n`] produced for this `img` and
/// `b`; `u.union` and `u.bin_union` are the fibre-independent
/// [`crate::universe::least_universe_union`] and
/// [`crate::universe::least_universe_bin_union`], reused rather than ported;
/// `general` is [`dprod_in_universe_of_n`]'s output. Every argument is rebuilt
/// at our own terms and compared, so a stack that does not fit together — a
/// `union` for a different universe operator, a `replacement` for a different
/// fibre symbol, a `general` at the wrong prefix length — is refused rather than
/// silently described.
pub fn dprod_in_universe_pair_n(
    env: &mut Env,
    ap: &Apply,
    fibre: &Fibre<'_>,
    u: &UniverseParts<'_>,
    general: &Thm,
) -> Option<Thm> {
    let (b, img, dprod, lu) = (fibre.b, fibre.img, fibre.dprod, u.lu);
    let k = fibre.arity()?;
    if lu.arity() != 1 {
        return None
    }
    let qs: Vec<_> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (cv, av) = (env.fresh_var(), env.fresh_var());
    let (tc, ta) = (Term::var(cv), Term::var(av));
    let w = Term::apply(lu, vec![tc.clone()]);

    let img_a = sym_at(img, &qts, ta.clone());
    let u_img = base_of_n(ap, img, &qts, &ta); // ⋃img(q⃗,A)
    debug_assert_eq!(
        u_img,
        ap.sets.union_of(img_a.clone()),
        "⋃img(q⃗,A) is not the union of img(q⃗,A)"
    );
    let un = bin_union(&ap.sets, ta.clone(), u_img.clone());

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let fib = fibres_in_n(env, b, &qts, &ta, &w);
    let h = Formula::and(a_in_w.clone(), fib.clone());
    let h_a = and_left(a_in_w.clone(), fib);

    // Replacement, then `⋃`.
    let mut rargs = qts.clone();
    rargs.push(tc.clone());
    rargs.push(ta.clone());
    let lr = inst_all(fibre.replacement, &rargs)?;
    if *lr.concl() != Formula::imp(h.clone(), Formula::mem(img_a.clone(), w.clone())) {
        return None
    }
    let lun = inst_all(u.union, &[tc.clone(), img_a.clone()])?;
    if *lun.concl()
        != Formula::imp(
            Formula::mem(img_a, w.clone()),
            Formula::mem(u_img.clone(), w.clone()),
        )
    {
        return None
    }
    let h_uimg = syl(&lr, &lun)?;

    // Binary union with the base set.
    let lbu = inst_all(u.bin_union, &[tc.clone(), ta.clone(), u_img.clone()])?;
    if *lbu.concl()
        != Formula::imp(
            Formula::and(a_in_w, Formula::mem(u_img, w.clone())),
            Formula::mem(un.clone(), w.clone()),
        )
    {
        return None
    }
    let h_un = hyp_mp(&a1i(&lbu, h.clone()), &hyp_and(&h_a, &h_uimg)?)?;

    // And the reduction proved above.
    let mut gargs = qts.clone();
    gargs.push(ta.clone());
    gargs.push(tc);
    let g = inst_all(general, &gargs)?;
    let dp_t = sym_at(dprod, &qts, ta);
    if *g.concl() != Formula::imp(Formula::mem(un, w.clone()), Formula::mem(dp_t.clone(), w.clone()))
    {
        return None
    }
    let out = syl(&h_un, &g)?;
    // Not a `debug_assert`: this is the statement the caller relies on.
    if *out.concl() != Formula::imp(h, Formula::mem(dp_t, w)) {
        return None
    }
    let mut all = qs;
    all.push(cv);
    all.push(av);
    Some(gen_all(&all, &out))
}
