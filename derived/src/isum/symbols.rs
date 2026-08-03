//! **The `n`-ary sum and its injections, as real symbols** — `Sum_n(A₀ … A_{n-1})`
//! and `Inj_i(a)`, defined on demand, cached, and exposed by their properties
//! rather than by their construction.
//!
//! # Why symbols rather than a meta-level nest
//!
//! [`super::tags`] builds `A₀ + (A₁ + (… + (A_{n-1} + 0)))` and
//! `inj_i(a) = inr^i(inl(a))` as Rust term formers, so the whole nest is
//! **inlined at every mention**. That has two costs. The nest is `O(n)` nodes
//! deep wherever the tag set appears — and it appears in the carrier term, in
//! `closed`, and in every constructor's typing rule; the injections are worse,
//! `O(i)` each, and a constructor term mentions one every time it is written
//! down. This project holds that a kernel operation the checker performs should
//! be constant cost, and a meta-level nest makes formula size grow with the
//! declaration's arity.
//!
//! Behind symbols, `Sum_n(A₀ … A_{n-1})` is one node over `n` arguments and
//! `Inj_i(a)` is one node over one, at every depth. The second is a genuine
//! asymptotic win; the first trades `O(n)` depth for depth 1.
//!
//! It also **protects the encoding decision**. The trailing `+ 0` — which
//! [`super::tags`] argues for, and which is not gospel — is otherwise visible in
//! every downstream statement. Behind `Sum_n` it is one defining equation, so
//! changing it later costs one file.
//!
//! [`crate::sigma::dsum`] is the pattern this follows: a real symbol built by
//! Replacement and Separation, parameterised by the domain and fibre symbols,
//! exposing `intro`/`fst_mem`/`snd_mem`/`eta` with the construction hidden.
//!
//! # The cache keys, and why the injection's is just `i`
//!
//! ```text
//! Sum_n     cached by n
//! Inj_i     cached by i          — not by (n, i), and not by the summands
//! ```
//!
//! `inj_i(a) = inr^i(inl(a))` mentions neither `n` nor any `Aⱼ`, so **one symbol
//! per depth serves every arity at once**. That is a direct dividend of keeping
//! the trailing `+ 0`: without it the last injection would be `inr^{n-1}` with
//! no `inl`, so it *would* depend on `n` and the cache would be quadratic.
//! [`super::tags`]'s header argues for the trailing `0` on the grounds that it
//! makes the lemmas uniform; this is the second, independent reason.
//!
//! The properties divide the same way, and **every one of them is cached under
//! the key that indexes it** — a hit hands back the theorem, never a
//! re-derivation:
//!
//! | property | key |
//! |---|---|
//! | [`ISumSyms::sum_ax`] — `Sum_n(A⃗) = A₀ + (… + 0)` | `n` |
//! | [`ISumSyms::inj_ax`] — `Inj_i(a) = inr^i(inl a)` | `i` |
//! | [`ISumSyms::inj_mem`] — `a ∈ Aᵢ → Inj_i(a) ∈ Sum_n(A⃗)` | `(n, i)` |
//! | [`ISumSyms::inj_inj`] — `Inj_i(a) = Inj_i(b) → a = b` | `i` |
//! | [`ISumSyms::inj_distinct`] — `¬(Inj_i(a) = Inj_j(b))` | `(i, j)` |
//! | [`ISumSyms::no_junk`] — every element of `Sum_n(A⃗)` is some `Inj_i(a)` | `n` |
//! | [`ISumSyms::branch`] — the restriction `f|ᵢ` along `Inj_i` ([`super::restrict`]) | `i` |
//! | [`ISumSyms::branch_in_funspace`] — `f ∈ fs(Sum_n(A⃗),S) → f|ᵢ ∈ fs(Aᵢ,S)` | `(n, i)` |
//!
//! The first four are minted eagerly by [`ISumSyms::ensure`], because a
//! declaration needs all of them; the last two are derived on first request and
//! then cached, because they are keyed by a pair and by an expensive induction
//! respectively. Nothing is ever evicted.
//!
//! # Interface
//!
//! [`ISumSyms::ensure`] mints every symbol at arity `≤ n` — idempotent and
//! incremental, so a caller extends the cache by calling it again with a larger
//! `n`. Terms are [`ISumSyms::sum`], [`ISumSyms::inj`] and
//! [`ISumSyms::finord`]; the theorems are the six above.
//!
//! **One cache belongs to one [`Sums`], and a failed `ensure` caches nothing.**
//! Both are properties of `ensure`'s `Some`, and both are there so that
//! `Some(())` means what it says. A cache is bound to the first family it is
//! used with ([`ISumSyms::is_over`]) and refuses every accessor taking some
//! other one, because `Sum_n(A⃗) = A₀ + (… + 0)` is a statement about *that*
//! family's `+`; and a derivation that fails part-way rolls back its pushes, so
//! the `levels.len()`/`injs.len()` that `ensure` keys its progress on cannot
//! report an arity whose theorems were never obtained. Without either, a second
//! `ensure` could return `Some(())` for an arity it never derived and
//! [`ISumSyms::sum_ax`] hand back a theorem about another family's symbols.
//!
//! **The defining equations stay reachable on purpose.** This is a convenience
//! boundary, not a soundness one: [`crate::define_abbrev`] is a conservative
//! extension, so nothing here can be unsound, but a failed proof downstream
//! shows `Sum_3(…)` and has to be unfolded by hand. `sum_ax`/`inj_ax` are what
//! that is done with, and no caller should need them for anything else.
//!
//! # Non-vacuity
//!
//! A symbol with only an introduction rule says nothing: `Sum_n(A⃗) := V`
//! satisfies [`ISumSyms::inj_mem`] for every `i`, and `Sum_n(A⃗) := ∅` satisfies
//! [`ISumSyms::no_junk`]. The two together pin it from both sides, and
//! [`ISumSyms::inj_distinct`] separates the summands inside it.
//! `tests/isum.rs` cashes all three at `finord(3) = Sum_3(1,1,1)`, whose three
//! elements are pairwise provably distinct and provably exhaust it.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`] per arity and per depth, each naming a term
//! [`super::tags`] already builds out of [`crate::sums`]' existing `sum` symbol.
//! No new axiom, and no construction that was not already available.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::sums::Sums;
use crate::wrec::{hyp_congr, hyp_eq_trans};
use crate::{
    a1i, and_left, and_right, define_abbrev, disj_inject, disj_of, eq_symm, eq_trans, ex_falso,
    exists_elim_imp, exists_intro_imp, gen_all, hyp_and, hyp_mp, hyp_or_elim, imp_refl, inst_all,
    mpd_const, syl, uncurry,
};

use super::restrict::{branch_in_funspace, Branch};
use super::tags::{inj_distinct as nest_distinct, inj_injective, inj_mem_at, inj_of, isum_of};

/// One arity: the symbol `Sum_n`, its defining equation, and the `n`
/// memberships.
struct Level {
    sym: FnSym,
    /// `⊢ ∀A₀ … ∀A_{n-1}. Sum_n(A⃗) = A₀ + (… + (A_{n-1} + 0))`.
    ax: Thm,
    /// For each `i < n`: `⊢ ∀A⃗ ∀a. (a ∈ Aᵢ → Inj_i(a) ∈ Sum_n(A⃗))`.
    inj_mem: Vec<Thm>,
}

/// One depth: the symbol `Inj_i`, its defining equation, and its injectivity.
struct Injection {
    sym: FnSym,
    /// `⊢ ∀a. Inj_i(a) = inr^i(inl(a))`.
    ax: Thm,
    /// `⊢ ∀a ∀b. (Inj_i(a) = Inj_i(b) → a = b)`. `None` only *during* the
    /// derivation, which needs the symbol to be in the cache before it can
    /// state the theorem about it; an entry with `None` here is never visible
    /// outside [`ISumSyms::ensure`], which rolls the push back if the
    /// derivation fails.
    inj: Option<Thm>,
}

/// Which [`Sums`] a cache was built over: the `sum` symbol and the pairing,
/// which between them fix every term [`super::tags`] builds.
///
/// Two `Sums` in one `Env` are two *different* families — `Sums::new` mints a
/// fresh `upair` and a fresh `sum` — so a theorem derived over one says nothing
/// about the other's `A + B`. The cache records the family it was first used
/// with and refuses every later call over a different one.
type Family = (FnSym, FnSym);

fn family_of(s: &Sums) -> Family { (s.sum, s.ap.sets.up) }

/// The cache of `n`-ary sum symbols and injection symbols, with everything
/// derived about them.
///
/// `levels` and `injs` are `Vec`s rather than maps because
/// [`ISumSyms::ensure`] fills `0..=n` densely: a declaration with `n`
/// constructors needs every arity below `n` too, for the fibres of its
/// constructors. The two on-demand families are maps, keyed as the table in
/// the module header says.
///
/// **One cache serves one [`Sums`].** `family` is set by the first
/// [`ISumSyms::ensure`] that mints anything and compared by every entry point
/// that takes a `&Sums`; a call over a second family is refused rather than
/// answered out of the first family's cache. And every entry is *derived before
/// it is pushed*, in the sense that a failure anywhere rolls the cache back to
/// what it was when the call started — so `levels.len()`/`injs.len()`, which is
/// what progress is keyed on, can never count an arity whose theorems were
/// never obtained.
#[derive(Default)]
pub struct ISumSyms {
    family: Option<Family>,
    levels: Vec<Level>,
    injs: Vec<Injection>,
    distinct: RefCell<HashMap<(usize, usize), Thm>>,
    junk: RefCell<HashMap<usize, Thm>>,
    branches: RefCell<HashMap<usize, Rc<Branch>>>,
    branch_fs: RefCell<HashMap<(usize, usize), Thm>>,
}

impl ISumSyms {
    /// An empty cache. Nothing is minted until [`ISumSyms::ensure`].
    pub fn new() -> ISumSyms { ISumSyms::default() }

    /// The largest arity currently available — every one of whose theorems was
    /// actually derived, because a failed [`ISumSyms::ensure`] leaves no entry
    /// behind.
    pub fn arity(&self) -> usize { self.levels.len().saturating_sub(1) }

    /// `true` when this cache has been used with `s` — or has not been used at
    /// all, in which case `s` is the family it would adopt.
    ///
    /// Every accessor taking a `&Sums` refuses when this is `false`.
    pub fn is_over(&self, s: &Sums) -> bool {
        self.family.is_none_or(|f| f == family_of(s))
    }

    /// Mint `Sum_k` for every `k ≤ n` and `Inj_i` for every `i < n`, deriving
    /// their defining equations, memberships and injectivity.
    ///
    /// Idempotent and incremental: calling it again with a larger `n` extends
    /// the cache and re-derives nothing.
    ///
    /// **All or nothing.** `None` — because `s` is not the family this cache
    /// was built over, or because a derivation failed — leaves the cache
    /// exactly as it was, so `Some(())` means every arity up to `n` and every
    /// depth below it is present *with its theorems*, over the caller's own
    /// `Sums`. Reporting an arity as available when its derivation failed, or
    /// over a family the caller did not ask about, would let
    /// [`ISumSyms::sum_ax`] hand back a theorem about somebody else's symbols.
    pub fn ensure(&mut self, env: &mut Env, s: &Sums, n: usize) -> Option<()> {
        if !self.is_over(s) {
            return None
        }
        let (injs, levels) = (self.injs.len(), self.levels.len());
        match self.mint(env, s, n) {
            Some(()) => {
                self.family = Some(family_of(s));
                Some(())
            }
            None => {
                // Roll back whatever this call had pushed: a half-built `Level`
                // or `Injection` would otherwise be counted as derived by the
                // `while` conditions below and never repaired.
                self.injs.truncate(injs);
                self.levels.truncate(levels);
                None
            }
        }
    }

    /// [`ISumSyms::ensure`]'s body, which may leave the cache half-extended;
    /// its caller rolls that back.
    fn mint(&mut self, env: &mut Env, s: &Sums, n: usize) -> Option<()> {
        while self.injs.len() < n {
            let i = self.injs.len();
            let av = env.fresh_var();
            let (sym, ax) = define_abbrev(env, &[av], &inj_of(s, i, Term::var(av)))?;
            // Pushed without its injectivity theorem, which is derived
            // immediately below: `unfold_inj` needs the symbol to be in the
            // cache before it can mention it. `inj_inj(i)` refuses the entry
            // until the theorem is there, and a failure before then rolls the
            // push back, so no caller ever sees the gap.
            self.injs.push(Injection { sym, ax, inj: None });
            let (bv, cv) = (env.fresh_var(), env.fresh_var());
            let (tb, tc) = (Term::var(bv), Term::var(cv));
            let bridge = self.unfold_inj(env, i, i, &tb, &tc)?;
            let out = syl(&bridge, &inst_all(&inj_injective(env, s, i)?, &[tb.clone(), tc.clone()])?)?;
            debug_assert_eq!(
                *out.concl(),
                Formula::imp(
                    Formula::eq(self.inj(i, tb.clone())?, self.inj(i, tc.clone())?),
                    Formula::eq(tb, tc),
                ),
                "isum::symbols: inj_inj has the wrong shape"
            );
            // The claim is unconditional, and `Sums`' theorem fields are `pub`:
            // a hypothetical input would compose through `syl` and arrive here
            // with `Γ` intact and the same conclusion.
            if !out.hyps().is_empty() {
                return None
            }
            self.injs[i].inj = Some(gen_all(&[bv, cv], &out));
        }
        while self.levels.len() <= n {
            let k = self.levels.len();
            let vars: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
            let terms: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
            let (sym, ax) = define_abbrev(env, &vars, &isum_of(s, &terms))?;
            self.levels.push(Level { sym, ax, inj_mem: Vec::new() });

            let av = env.fresh_var();
            let ta = Term::var(av);
            let mut quant = vars.clone();
            quant.push(av);
            let mut mems = Vec::with_capacity(k);
            for i in 0..k {
                let nest = inj_mem_at(s, &terms, i, &ta)?;
                // `nest → Sum_k(A⃗)`, then `inj_i(a) → Inj_i(a)`.
                let to_sym = Thm::mp(
                    &{
                        let hole = env.fresh_var();
                        Thm::eq_leibniz(
                            isum_of(s, &terms),
                            self.sum(&terms)?,
                            hole,
                            Formula::mem(inj_of(s, i, ta.clone()), Term::var(hole)),
                        )
                    },
                    &eq_symm(env, &inst_all(self.sum_ax(k)?, &terms)?)?,
                )?;
                let to_inj = Thm::mp(
                    &{
                        let hole = env.fresh_var();
                        Thm::eq_leibniz(
                            inj_of(s, i, ta.clone()),
                            self.inj(i, ta.clone())?,
                            hole,
                            Formula::mem(Term::var(hole), self.sum(&terms)?),
                        )
                    },
                    &eq_symm(env, &inst_all(self.inj_ax(i)?, std::slice::from_ref(&ta))?)?,
                )?;
                let out = syl(&nest, &syl(&to_sym, &to_inj)?)?;
                debug_assert_eq!(
                    *out.concl(),
                    Formula::imp(
                        Formula::mem(ta.clone(), terms[i].clone()),
                        Formula::mem(self.inj(i, ta.clone())?, self.sum(&terms)?),
                    ),
                    "isum::symbols: inj_mem has the wrong shape"
                );
                if !out.hyps().is_empty() {
                    return None
                }
                mems.push(gen_all(&quant, &out));
            }
            self.levels[k].inj_mem = mems;
        }
        Some(())
    }

    // ── terms ───────────────────────────────────────────────────────────────

    /// The term `Sum_n(A₀ … A_{n-1})`, with `n = args.len()`. `None` if
    /// [`ISumSyms::ensure`] has not reached that arity.
    pub fn sum(&self, args: &[Term]) -> Option<Term> {
        Some(Term::apply(self.levels.get(args.len())?.sym, args.to_vec()))
    }

    /// The term `Inj_i(a)`. `None` if [`ISumSyms::ensure`] has not reached
    /// depth `i`.
    pub fn inj(&self, i: usize, a: Term) -> Option<Term> {
        Some(Term::apply(self.injs.get(i)?.sym, vec![a]))
    }

    /// The symbol `Sum_n` itself, for a client that has to check it is looking
    /// at *this* cache's sum rather than another's.
    pub fn sum_sym(&self, n: usize) -> Option<FnSym> { Some(self.levels.get(n)?.sym) }

    /// The symbol `Inj_i` itself, for the same reason. Never re-minted: once
    /// [`ISumSyms::ensure`] has returned, the symbol at a given depth is fixed
    /// for the life of the cache, so it is a stable identity to record.
    pub fn inj_sym(&self, i: usize) -> Option<FnSym> { Some(self.injs.get(i)?.sym) }

    /// The finite ordinal `m`, as `Sum_m(1, …, 1)` — the fibre a constructor
    /// with `m` recursive arguments gets (`thesis.txt:1800`).
    ///
    /// Note `finord(1)` is `Sum_1(1)`, which unfolds to `1 + 0` and is **not**
    /// the term `1`; see [`crate::recarg`] for what that costs.
    ///
    /// `None` — as everywhere here — when `s` is not the family this cache was
    /// built over.
    pub fn finord(&self, s: &Sums, m: usize) -> Option<Term> {
        if !self.is_over(s) {
            return None
        }
        self.sum(&vec![s.unit(); m])
    }

    // ── the defining equations, for unfolding by hand ───────────────────────

    /// `⊢ ∀A⃗. Sum_n(A⃗) = A₀ + (… + (A_{n-1} + 0))`.
    pub fn sum_ax(&self, n: usize) -> Option<&Thm> { Some(&self.levels.get(n)?.ax) }

    /// `⊢ ∀a. Inj_i(a) = inr^i(inl(a))`.
    pub fn inj_ax(&self, i: usize) -> Option<&Thm> { Some(&self.injs.get(i)?.ax) }

    /// `⊢ Inj_i(a) = Inj_j(b) → inj_i(a) = inj_j(b)` — the bridge into the
    /// construction that every equational property crosses.
    fn unfold_inj(&self, env: &mut Env, i: usize, j: usize, a: &Term, b: &Term) -> Option<Thm> {
        let ea = inst_all(self.inj_ax(i)?, std::slice::from_ref(a))?;
        let eb = inst_all(self.inj_ax(j)?, std::slice::from_ref(b))?;
        let h = Formula::eq(self.inj(i, a.clone())?, self.inj(j, b.clone())?);
        let back = a1i(&eq_symm(env, &ea)?, h.clone());
        let step = hyp_eq_trans(env, &back, &imp_refl(h.clone()))?;
        hyp_eq_trans(env, &step, &a1i(&eb, h))
    }

    /// `⊢ inr(Inj_d(a)) = Inj_{d+1}(a)` — climbing one injection.
    ///
    /// `inr(inj_d(a))` *is* `inj_{d+1}(a)` as a term, so the whole content is
    /// unfolding one symbol and folding the next.
    fn climb(&self, env: &mut Env, s: &Sums, d: usize, a: &Term) -> Option<Thm> {
        let down = inst_all(self.inj_ax(d)?, std::slice::from_ref(a))?;
        let lifted = {
            let hole = env.fresh_var();
            let lhs = s.inr(self.inj(d, a.clone())?);
            let leib = Thm::eq_leibniz(
                self.inj(d, a.clone())?,
                inj_of(s, d, a.clone()),
                hole,
                Formula::eq(lhs.clone(), s.inr(Term::var(hole))),
            );
            Thm::mp(&mpd_const(&leib, &Thm::eq_refl(lhs))?, &down)?
        };
        let up = eq_symm(env, &inst_all(self.inj_ax(d + 1)?, std::slice::from_ref(a))?)?;
        let out = eq_trans(env, &lifted, &up)?;
        debug_assert_eq!(
            *out.concl(),
            Formula::eq(s.inr(self.inj(d, a.clone())?), self.inj(d + 1, a.clone())?),
            "isum::symbols: climb has the wrong shape"
        );
        Some(out)
    }

    // ── the properties ──────────────────────────────────────────────────────

    /// `⊢ ∀A₀ … ∀A_{n-1} ∀a. (a ∈ Aᵢ → Inj_i(a) ∈ Sum_n(A⃗))`.
    pub fn inj_mem(&self, n: usize, i: usize) -> Option<&Thm> {
        self.levels.get(n)?.inj_mem.get(i)
    }

    /// `⊢ ∀a ∀b. (Inj_i(a) = Inj_i(b) → a = b)` — independent of the arity.
    pub fn inj_inj(&self, i: usize) -> Option<&Thm> { self.injs.get(i)?.inj.as_ref() }

    /// `⊢ ∀a ∀b. ¬(Inj_i(a) = Inj_j(b))`, for `i ≠ j` — **the injections have
    /// pairwise disjoint ranges**, and again independent of the arity.
    ///
    /// Derived on first request and cached under `(i, j)`.
    pub fn inj_distinct(&self, env: &mut Env, s: &Sums, i: usize, j: usize) -> Option<Thm> {
        if i == j || !self.is_over(s) {
            return None
        }
        if let Some(th) = self.distinct.borrow().get(&(i, j)) {
            return Some(th.clone())
        }
        let (av, bv) = (env.fresh_var(), env.fresh_var());
        let (ta, tb) = (Term::var(av), Term::var(bv));
        let bridge = self.unfold_inj(env, i, j, &ta, &tb)?;
        let out = syl(&bridge, &inst_all(&nest_distinct(env, s, i, j)?, &[ta.clone(), tb.clone()])?)?;
        debug_assert_eq!(
            *out.concl(),
            Formula::not(Formula::eq(self.inj(i, ta)?, self.inj(j, tb)?)),
            "isum::symbols: inj_distinct has the wrong shape"
        );
        let out = gen_all(&[av, bv], &out);
        self.distinct.borrow_mut().insert((i, j), out.clone());
        Some(out)
    }

    /// **No junk**: `⊢ ∀A⃗ ∀p. (p ∈ Sum_n(A⃗) → ⋁_{i<n} ∃a. (a ∈ Aᵢ ∧ p = Inj_i(a)))`,
    /// and at `n = 0` the emptiness statement `⊢ ∀p. ¬(p ∈ Sum_0())`.
    ///
    /// The exhaustiveness half of the interface: the one property that stops
    /// `Sum_n(A⃗)` from being allowed to hold anything besides the injections.
    ///
    /// Induction down the nest.
    /// [`Sums::sum_cases`](crate::sums::Sums::sum_cases) splits each link into
    /// "in the head summand", which is already the statement's first disjunct,
    /// or "`p = inr y` with `y` in the tail" — and then the tail's own statement
    /// is shifted up one injection by [`ISumSyms::climb`]. The base case is
    /// `¬(p ∈ 0)`, so the recursion bottoms out on the trailing `0` with no
    /// special case for the last constructor, exactly as the injections do.
    ///
    /// Derived on first request and cached under `n`. It is the one property
    /// here that is not a transport of an existing lemma, and much the most
    /// expensive.
    ///
    /// `None` when `s` is not this cache's family, or when
    /// [`ISumSyms::ensure`] has not reached arity `n` — like every other
    /// accessor here, and unlike the panic this used to be.
    pub fn no_junk(&self, env: &mut Env, s: &Sums, n: usize) -> Option<Thm> {
        if !self.is_over(s) {
            return None
        }
        if let Some(th) = self.junk.borrow().get(&n) {
            return Some(th.clone())
        }
        let out = self.derive_no_junk(env, s, n)?;
        self.junk.borrow_mut().insert(n, out.clone());
        Some(out)
    }

    /// **The restriction along `Injⱼ`** — [`super::Branch`] at depth `j`,
    /// minted on first request and cached under `j`.
    ///
    /// One symbol per depth serves every arity, for the same reason
    /// [`ISumSyms::inj_sym`] does: `Injⱼ(x)` mentions neither `n` nor any
    /// summand. Only [`ISumSyms::branch_in_funspace`] is keyed by the pair.
    ///
    /// `None` when `s` is not this cache's family or when [`ISumSyms::ensure`]
    /// has not reached depth `j`. Unlike `ensure`, a failure **after** the two
    /// symbols are minted leaves them in `env` — the same cost
    /// `crate::inductive::recursor` records for a refused `StepSym`, and the
    /// reason nothing is cached until the derivation has succeeded.
    pub fn branch(&self, env: &mut Env, s: &Sums, j: usize) -> Option<Rc<Branch>> {
        if !self.is_over(s) {
            return None
        }
        if let Some(b) = self.branches.borrow().get(&j) {
            return Some(b.clone())
        }
        let built = Rc::new(Branch::new(env, s, self.inj_sym(j)?, j)?);
        self.branches.borrow_mut().insert(j, built.clone());
        Some(built)
    }

    /// `⊢ ∀A⃗ ∀S ∀f. (f ∈ fs(Sum_n(A⃗), S) → restrⱼ(f, Aⱼ) ∈ fs(Aⱼ, S))`, the
    /// restriction's typing rule at the shape its consumers hold.
    ///
    /// `app_mem` must be [`crate::ext::funspace_app_mem`] over this `Sums` —
    /// checked, because it is `mp`-ed against. Derived on first request and
    /// cached under `(n, j)`.
    pub fn branch_in_funspace(
        &self,
        env: &mut Env,
        s: &Sums,
        app_mem: &Thm,
        n: usize,
        j: usize,
    ) -> Option<Thm> {
        if !self.is_over(s) {
            return None
        }
        if let Some(th) = self.branch_fs.borrow().get(&(n, j)) {
            return Some(th.clone())
        }
        let b = self.branch(env, s, j)?;
        let out = branch_in_funspace(env, s, self, &b, app_mem, n, j)?;
        self.branch_fs.borrow_mut().insert((n, j), out.clone());
        Some(out)
    }

    fn derive_no_junk(&self, env: &mut Env, s: &Sums, n: usize) -> Option<Thm> {
        // Every symbol the statement mentions has to be in the cache already:
        // `Sum_n` and, for the disjuncts, `Inj_0 … Inj_{n-1}`. This is what
        // makes the `expect` in `disjunct` below true rather than hopeful.
        if self.levels.len() <= n || self.injs.len() < n {
            return None
        }
        let vars: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
        let terms: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
        let pv = env.fresh_var();
        let tp = Term::var(pv);
        let bound: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();

        // `∃a. (a ∈ Aᵢ ∧ t = Inj_d(a))` — the `i`-th summand's witness, at the
        // injection depth the current tail gives it.
        let disjunct = |t: &Term, i: usize, d: usize| -> Formula {
            let a = Term::var(bound[i]);
            Formula::exists(
                bound[i],
                Formula::and(
                    Formula::mem(a.clone(), terms[i].clone()),
                    Formula::eq(t.clone(), self.inj(d, a).expect("cached by ensure")),
                ),
            )
        };
        let goal = |t: &Term, k: usize| -> Formula {
            let atoms: Vec<Formula> = (k..n).map(|i| disjunct(t, i, i - k)).collect();
            disj_of(&atoms).unwrap_or_else(Formula::false_)
        };

        // ── the base: nothing is in the trailing `0` ────────────────────────
        let mut claim = Thm::gen(
            pv,
            &syl(
                &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tp))?,
                &ex_falso(goal(&tp, n)),
            )?,
        );

        for k in (0..n).rev() {
            let head = terms[k].clone();
            let tail = isum_of(s, &terms[k + 1..]);
            let here = Formula::mem(tp.clone(), isum_of(s, &terms[k..]));
            let dk = goal(&tp, k);
            let atoms_k: Vec<Formula> = (k..n).map(|i| disjunct(&tp, i, i - k)).collect();

            // ── the head summand: `p = inl x`, which is `p = Inj_0(x)` ──────
            let xv = env.fresh_var();
            let tx = Term::var(xv);
            let left = {
                let raw = Formula::and(
                    Formula::mem(tx.clone(), head.clone()),
                    Formula::eq(tp.clone(), s.inl(tx.clone())),
                );
                let fold = {
                    let hole = env.fresh_var();
                    Thm::mp(
                        &Thm::eq_leibniz(
                            s.inl(tx.clone()),
                            self.inj(0, tx.clone())?,
                            hole,
                            Formula::and(
                                Formula::mem(tx.clone(), head.clone()),
                                Formula::eq(tp.clone(), Term::var(hole)),
                            ),
                        ),
                        &eq_symm(env, &inst_all(self.inj_ax(0)?, std::slice::from_ref(&tx))?)?,
                    )?
                };
                let intro = exists_intro_imp(
                    bound[k],
                    Formula::and(
                        Formula::mem(Term::var(bound[k]), head.clone()),
                        Formula::eq(tp.clone(), self.inj(0, Term::var(bound[k]))?),
                    ),
                    tx.clone(),
                )?;
                let body = syl(&syl(&fold, &intro)?, &disj_inject(&atoms_k, 0)?)?;
                debug_assert_eq!(
                    *body.concl(),
                    Formula::imp(raw.clone(), dk.clone()),
                    "isum::symbols: no_junk's head branch has the wrong shape"
                );
                exists_elim_imp(xv, &Thm::gen(xv, &body), &dk)?
            };

            // ── the tail: `p = inr y`, and `y`'s own statement shifted up ───
            let yv = env.fresh_var();
            let ty = Term::var(yv);
            let right = {
                let kf = Formula::and(
                    Formula::mem(ty.clone(), tail.clone()),
                    Formula::eq(tp.clone(), s.inr(ty.clone())),
                );
                let (in_tail, is_inr) = (
                    and_left(
                        Formula::mem(ty.clone(), tail.clone()),
                        Formula::eq(tp.clone(), s.inr(ty.clone())),
                    ),
                    and_right(
                        Formula::mem(ty.clone(), tail.clone()),
                        Formula::eq(tp.clone(), s.inr(ty.clone())),
                    ),
                );
                let have = syl(&in_tail, &inst_all(&claim, std::slice::from_ref(&ty))?)?;

                let body = if k + 1 == n {
                    // The tail is the trailing `0`, so `have` concludes `⊥`.
                    syl(&have, &ex_falso(dk.clone()))?
                } else {
                    let tail_atoms: Vec<Formula> =
                        (k + 1..n).map(|i| disjunct(&ty, i, i - k - 1)).collect();
                    // `⊢ K → (Eᵢ(y) → Dₖ(p))`, for one summand of the tail.
                    let shift = |env: &mut Env, i: usize| -> Option<Thm> {
                        let a = Term::var(bound[i]);
                        let phi = Formula::and(
                            Formula::mem(a.clone(), terms[i].clone()),
                            Formula::eq(ty.clone(), self.inj(i - k - 1, a.clone())?),
                        );
                        let (p_head, p_tail) = (
                            and_left(kf.clone(), phi.clone()),
                            and_right(kf.clone(), phi.clone()),
                        );
                        let (in_a, y_is) = (
                            syl(
                                &p_tail,
                                &and_left(
                                    Formula::mem(a.clone(), terms[i].clone()),
                                    Formula::eq(ty.clone(), self.inj(i - k - 1, a.clone())?),
                                ),
                            )?,
                            syl(
                                &p_tail,
                                &and_right(
                                    Formula::mem(a.clone(), terms[i].clone()),
                                    Formula::eq(ty.clone(), self.inj(i - k - 1, a.clone())?),
                                ),
                            )?,
                        );
                        // `p = inr y = inr(Inj_{i-k-1} a) = Inj_{i-k} a`.
                        let p_is_inr = syl(&p_head, &is_inr)?;
                        let lifted = hyp_congr(env, &y_is, |t| s.inr(t))?;
                        let step = hyp_eq_trans(env, &p_is_inr, &lifted)?;
                        let climbed = self.climb(env, s, i - k - 1, &a)?;
                        let both = Formula::and(kf.clone(), phi.clone());
                        let p_is = hyp_eq_trans(env, &step, &a1i(&climbed, both.clone()))?;

                        let placed = syl(
                            &syl(
                                &hyp_and(&in_a, &p_is)?,
                                &exists_intro_imp(
                                    bound[i],
                                    Formula::and(
                                        Formula::mem(a.clone(), terms[i].clone()),
                                        Formula::eq(tp.clone(), self.inj(i - k, a.clone())?),
                                    ),
                                    a,
                                )?,
                            )?,
                            &disj_inject(&atoms_k, i - k)?,
                        )?;
                        debug_assert_eq!(
                            *placed.concl(),
                            Formula::imp(both, dk.clone()),
                            "isum::symbols: no_junk's shift has the wrong shape"
                        );
                        // `⊢ (K ∧ φ) → Dₖ` becomes `⊢ K → ((∃a. φ) → Dₖ)`.
                        let swapped = crate::com12(&uncurry(&placed)?)?;
                        crate::com12(&exists_elim_imp(
                            bound[i],
                            &Thm::gen(bound[i], &swapped),
                            &Formula::imp(kf.clone(), dk.clone()),
                        )?)
                    };

                    // Fold the tail's disjunction, innermost summand first.
                    let mut acc = shift(env, n - 1)?;
                    for i in (k + 1..n - 1).rev() {
                        let rest = disj_of(&tail_atoms[i - k..])?;
                        let disj = Formula::or(tail_atoms[i - k - 1].clone(), rest);
                        let pick = and_left(kf.clone(), disj.clone());
                        let this = shift(env, i)?;
                        let elim = hyp_or_elim(
                            &and_right(kf.clone(), disj),
                            &syl(&pick, &this)?,
                            &syl(&pick, &acc)?,
                        )?;
                        acc = uncurry(&elim)?;
                    }
                    hyp_mp(&acc, &have)?
                };
                exists_elim_imp(yv, &Thm::gen(yv, &body), &dk)?
            };

            let cases = inst_all(&s.sum_cases, &[head, tail, tp.clone()])?;
            claim = Thm::gen(
                pv,
                &hyp_or_elim(&cases, &a1i(&left, here.clone()), &a1i(&right, here))?,
            );
        }

        // ── the nest becomes `Sum_n(A⃗)`; the injections are already symbols ─
        let at_p = inst_all(&claim, std::slice::from_ref(&tp))?;
        let hole = env.fresh_var();
        let out = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    isum_of(s, &terms),
                    self.sum(&terms)?,
                    hole,
                    Formula::imp(Formula::mem(tp.clone(), Term::var(hole)), goal(&tp, 0)),
                ),
                &eq_symm(env, &inst_all(self.sum_ax(n)?, &terms)?)?,
            )?,
            &at_p,
        )?;
        debug_assert_eq!(
            *out.concl(),
            Formula::imp(Formula::mem(tp.clone(), self.sum(&terms)?), goal(&tp, 0)),
            "isum::symbols: no_junk has the wrong shape"
        );
        let mut quant = vars;
        quant.push(pv);
        Some(gen_all(&quant, &out))
    }
}
