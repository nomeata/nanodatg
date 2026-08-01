//! The tower itself: the level terms, the step, and the closure properties at
//! a level.
//!
//! # Interface
//!
//! [`Tower::new`] builds the whole thing; the fields *are* the theorems, and
//! [`Tower::at`] pins them at one level. Read [`crate::tower`] for the
//! statements — this file is the implementation.
//!
//! # Why the seed is `ω` and not `U₀`
//!
//! See the module header of [`crate::tower`]. In one line: `V_ω` satisfies
//! every clause of [`crate::universe::is_universe`], so `U(x)` for a
//! hereditarily finite `x` — and `U₀ = {0,1}` is hereditarily finite — is
//! contained in `V_ω` and has no infinite member at all. `U(U₀)` is therefore
//! *refutably* too small, and the tower has to be seeded above `ω`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::anchor::falsity;
use crate::ext::{dprod_in_universe_of, dprod_in_universe_pair, DProd};
use crate::funcs::Apply;
use crate::funspace::{self as fsp, Funspace, Space};
use crate::recursion::{OmegaCore, Peano};
use crate::sums::Sums;
use crate::universe as uni;
use crate::{and_intro, ex_falso, inst_all, mpd_const, syl};

/// The universe tower `U₀, U₁, U₂, …`, together with every property the
/// interpretation assumes of it.
///
/// Built once. Every symbol below comes from a **single** chain of definitional
/// extensions — one pairing, one `∅`, one power set, one function space, one
/// `U(·)`, one `ω` — because two chains would mint two `⟨·,·⟩`s and no theorem
/// about one would say anything about the other. That is the same hazard
/// [`crate::funcs::Apply`] and [`crate::sums::Sums`] exist to avoid, and it is
/// why this struct carries the apparatus rather than rebuilding it on demand.
pub struct Tower {
    /// The unit type, the sums, the product, the function space and `app` —
    /// and, inside it, the one [`Apply`] everything is built over.
    pub sums: Sums,
    /// The power set, `U(·)` and the two clause transfers `C₂`, `C₃`.
    pub space: Space,
    /// `ω` with the Peano properties. What makes `⊢ ω ∈ Uₙ` a statement about
    /// the natural numbers rather than about an arbitrary constant.
    pub peano: Peano,

    // ── level 0 ──────────────────────────────────────────────────────────────
    /// `⊢ ∀p. (p ∈ U₀ ↔ (p = 0 ∨ p = 1))`.
    pub u0_members: Thm,
    /// `⊢ 0 ∈ U₀`.
    pub false_in_u0: Thm,
    /// `⊢ 1 ∈ U₀`.
    pub true_in_u0: Thm,
    /// `⊢ ¬(0 = 1)` — **non-vacuity of level 0**.
    pub u0_two_valued: Thm,
    /// `⊢ ∀p ∀x. ((p ∈ U₀ ∧ x ∈ p) → x = •)` — proof irrelevance.
    pub u0_subsingleton: Thm,

    // ── the step ─────────────────────────────────────────────────────────────
    /// `⊢ ∀x. x ∈ U(x)`.
    pub mem_u: Thm,
    /// `⊢ ∀x. C₁(U(x))`, i.e. `∀x ∀y. (y ∈ U(x) → ∀z. (z ∈ y → z ∈ U(x)))`.
    pub transitive: Thm,
    /// `⊢ ∀x ∀y. (y ∈ U(x) → ∀z. (z ⊆ y → z ∈ U(x)))` — `C₂` at `U(x)`.
    pub sub: Thm,
    /// `⊢ ∀c. ∅ ∈ U(c)`.
    pub empty_in: Thm,
    /// `⊢ ∀c. U₀ ∈ U(c)` — level 0 is a member of *every* level above it.
    pub u0_in: Thm,

    // ── closure, one `∀c` statement each ─────────────────────────────────────
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))`.
    pub pairing: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → ⟨a,b⟩ ∈ U(c))`.
    pub opair: Thm,
    /// `⊢ ∀c ∀y. (y ∈ U(c) → 𝒫y ∈ U(c))`.
    pub pow: Thm,
    /// `⊢ ∀c ∀s. (s ∈ U(c) → ⋃s ∈ U(c))`.
    pub union: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))`.
    pub bin_union: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c))`.
    pub product: Thm,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))`.
    pub funspace: Thm,
    /// `⊢ ∀c ∀f ∀x. (f ∈ U(c) → app(f,x) ∈ U(c))`.
    pub app: Thm,

    // ── carried so that [`Tower::family`] need not rebuild them ──────────────
    /// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))`.
    pub funspace_of: Thm,

    // ── non-vacuity ──────────────────────────────────────────────────────────
    /// `⊢ ∀x. ¬(x ∈ x)`, from Regularity. What makes `U₀ ∈ U₁` witness
    /// `U₀ ≠ U₁`.
    pub no_self_mem: Thm,
    /// `⊢ ¬(U₀ = U₁)` — **the tower does not collapse at the bottom**.
    pub u0_ne_u1: Thm,
    /// `⊢ fs(U₀,U₀) ∈ U₁` — a closure antecedent discharged at concrete terms.
    pub fs_u0_in_u1: Thm,
}

impl Tower {
    /// Build every symbol and derive every theorem, from the axioms up.
    ///
    /// The order matters: the [`Space`] is built over the [`Apply`] so that
    /// `app` and `fs` speak about the same ordered pair, the [`Sums`] over the
    /// `Space`'s power set so that `1` and `fs` do, and `ω` over the same
    /// pairing and the same `∅` so that `0 ∈ ω` is about the `∅` that is also
    /// `⟦False⟧`.
    pub fn new(env: &mut Env) -> Option<Tower> {
        let ap = Apply::new(env)?;
        let space = Space::with_apply(env, &ap)?;
        let prod = fsp::product(env, &space.sets)?;
        let fs =
            Funspace::new(env, &space.sets, space.pow, &space.pow_ax, &prod, &space.empty_ax)?;
        let sums = Sums::over(env, ap.clone(), space.pow, space.pow_ax.clone(), prod, fs)?;

        // `ω`, over *this* pairing and *this* `∅`.
        let core = OmegaCore::with_parts(
            env,
            space.sets.clone(),
            ap.mem_sing.clone(),
            ap.empty,
            ap.empty_ax.clone(),
        )?;
        let peano = Peano::over(env, core)?;

        // ── level 0 ─────────────────────────────────────────────────────────
        let (zero, one) = (sums.zero(), sums.unit());
        let u0 = falsity::truth_values(&sums);
        let u0_members = inst_all(&sums.ap.sets.up_ax, &[zero.clone(), one.clone()])?;
        let false_in_u0 = falsity::false_in_prop(&sums)?;
        let true_in_u0 = falsity::true_in_prop(&sums)?;
        let u0_two_valued = falsity::prop_two_valued(&sums)?;
        let u0_subsingleton = falsity::prop_subsingleton(env, &sums)?;

        // ── the step, and the closure chain ─────────────────────────────────
        let mem_u = space.mem_lu.clone();
        let transitive = uni::least_universe_transitive(env, space.lu, &space.lu_ax)?;
        let sub = space.c2.clone();

        let universe_pairing = uni::universe_pairing(
            env,
            space.sets.up,
            &space.sets.up_ax,
            space.empty,
            &space.empty_ax,
            space.pow,
            &space.pow_ax,
        )?;
        let mem_mem = uni::universe_mem_mem(env)?;
        let sub_mem = uni::universe_sub_mem(env)?;
        let two_cycle = crate::empty::no_two_cycle(env, space.sets.up, &space.sets.up_ax)?;
        let universe_union =
            uni::universe_union_closed(env, &space.sets, &space.empty_ax, &mem_mem, &two_cycle)?;

        let pairing =
            uni::least_universe_pairing(env, space.lu, &space.lu_ax, space.sets.up, &universe_pairing)?;
        let opair = uni::least_universe_opair(env, space.lu, space.sets.up, &pairing)?;
        let union =
            uni::least_universe_union(env, space.lu, &space.lu_ax, space.sets.un, &universe_union)?;
        let bin_union =
            uni::least_universe_bin_union(env, space.lu, &space.sets, &pairing, &union)?;
        let pow = power_closed_everywhere(env, &space)?;

        let up_sub = fsp::upair_subset(env, &space.sets)?;
        let pair_pp =
            fsp::pair_in_pow_pow(env, &space.sets, space.pow, &space.pow_ax, &up_sub)?;
        let (ml, mr) = fsp::mem_bin_union(env, &space.sets)?;
        let prod_sub = fsp::product_subset_pow_pow(
            env,
            &space.sets,
            space.pow,
            &sums.prod,
            &pair_pp,
            &ml,
            &mr,
        )?;
        let product_of = fsp::product_in_universe_of(env, &space, &sums.prod, &prod_sub)?;
        let funspace_of =
            fsp::funspace_in_universe_of(env, &space, &sums.prod, &prod_sub, &sums.fs)?;
        let product =
            fsp::product_in_universe(env, &space, &sums.prod, &product_of, &bin_union)?;
        let funspace =
            fsp::funspace_in_universe_pair(env, &space, &sums.fs, &funspace_of, &bin_union)?;

        let coll_closed = uni::universe_coll_closed(env, &sums.ap, &universe_union, &sub_mem)?;
        let app_closed =
            uni::universe_app_closed(env, &sums.ap, &universe_union, &coll_closed)?;
        let app = uni::least_universe_app(env, &sums.ap, space.lu, &space.lu_ax, &app_closed)?;

        // ── `∅` and `U₀` at every level ─────────────────────────────────────
        let empty_in = empty_everywhere(env, &space)?;
        let u0_in = u0_everywhere(env, &space, &sums, &empty_in, &pairing)?;

        // ── non-vacuity ─────────────────────────────────────────────────────
        let no_self_mem = crate::empty::no_self_mem(env, space.sets.up, &sums.ap.mem_sing)?;
        let omega = peano.core.set();
        let u1 = Term::apply(space.lu, vec![omega.clone()]);
        let u0_in_u1 = inst_all(&u0_in, std::slice::from_ref(&omega))?;
        let u0_ne_u1 = distinct(env, &no_self_mem, &u0_in_u1, &u0, &u1)?;
        let fs_u0_in_u1 = Thm::mp(
            &inst_all(&funspace, &[omega, u0.clone(), u0.clone()])?,
            &and_intro(&u0_in_u1, &u0_in_u1),
        )?;

        Some(Tower {
            sums,
            space,
            peano,
            u0_members,
            false_in_u0,
            true_in_u0,
            u0_two_valued,
            u0_subsingleton,
            mem_u,
            transitive,
            sub,
            empty_in,
            u0_in,
            pairing,
            opair,
            pow,
            union,
            bin_union,
            product,
            funspace,
            app,
            funspace_of,
            no_self_mem,
            u0_ne_u1,
            fs_u0_in_u1,
        })
    }

    // ── the level terms ─────────────────────────────────────────────────────

    /// `U₀ = {0, 1}`, the set of truth values. **Not a universe**; see the
    /// module header.
    pub fn u0(&self) -> Term { falsity::truth_values(&self.sums) }

    /// The term `ω`.
    pub fn omega(&self) -> Term { self.peano.core.set() }

    /// The **seed** of level `n ≥ 1`: the argument `U(·)` is applied to.
    ///
    /// `seed(1) = ω` and `seed(n+1) = Uₙ`. Level 1 is the one place the tower
    /// does not iterate on itself, and that is not a convenience — `U(U₀)` is
    /// refutably too small. See the module header.
    ///
    /// Panics for `n = 0`: level 0 is not of the form `U(·)`.
    pub fn seed(&self, n: usize) -> Term {
        assert!(n >= 1, "level 0 is not U(·) of anything");
        if n == 1 { self.omega() } else { self.level(n - 1) }
    }

    /// The term `Uₙ`: `U₀ = {0,1}`, `U₁ = U(ω)`, `U₍ₙ₊₁₎ = U(Uₙ)`.
    ///
    /// This is a **meta-level** iteration over `n: usize`, which is all Lean's
    /// levels ever need: `0`, `succ`, `max` and `imax` of closed levels all
    /// evaluate to a numeral at interpretation time, so no set-theoretic
    /// recursion and no recursion theorem is involved. Level *variables* stay
    /// opaque, exactly as they do in the thesis.
    pub fn level(&self, n: usize) -> Term {
        if n == 0 {
            self.u0()
        } else {
            Term::apply(self.space.lu, vec![self.seed(n)])
        }
    }

    /// `⊢ [φ] ∈ U₀` — every proposition's denotation is a truth value.
    ///
    /// A construction taking a *formula*, exactly as
    /// [`crate::prop::conditional_singleton`] is; `chi` must be that
    /// construction's characteristic theorem for the term `c = [φ]`. This
    /// delegates to [`crate::anchor::falsity::cond_in_prop`] rather than
    /// reproving it.
    pub fn cond_in_u0(
        &self,
        env: &mut Env,
        phi: &Formula,
        c: &Term,
        chi: &Thm,
    ) -> Option<Thm> {
        falsity::cond_in_prop(env, &self.sums, phi, c, chi)
    }

    /// Every property of level `n ≥ 1`, pinned at the term [`Tower::level`]
    /// hands back.
    ///
    /// Returns `None` for `n = 0`: `U₀` is not a universe and satisfies none of
    /// the closure clauses — `𝒫{0} = {0,1} = U₀ ∉ U₀`, for one.
    pub fn at(&self, n: usize) -> Option<Level> {
        if n == 0 {
            return None
        }
        let seed = self.seed(n);
        let set = self.level(n);
        let at_seed = |t: &Thm| inst_all(t, std::slice::from_ref(&seed));

        // `U_{n-1} ∈ Uₙ`: at level 1 the set below is `U₀`, which is not the
        // seed, so it needs [`Tower::u0_in`]; above that the seed *is* the set
        // below and `x ∈ U(x)` does it.
        let mem_below = if n == 1 {
            at_seed(&self.u0_in)?
        } else {
            at_seed(&self.mem_u)?
        };

        let transitive = at_seed(&self.transitive)?;
        let omega_mem = omega_at(self, n)?;

        let (u0_mem, empty_mem) = (at_seed(&self.u0_in)?, at_seed(&self.empty_in)?);
        let (sub, pairing, opair) =
            (at_seed(&self.sub)?, at_seed(&self.pairing)?, at_seed(&self.opair)?);
        let (pow, union, bin_union) =
            (at_seed(&self.pow)?, at_seed(&self.union)?, at_seed(&self.bin_union)?);
        let (product, funspace, app) =
            (at_seed(&self.product)?, at_seed(&self.funspace)?, at_seed(&self.app)?);

        Some(Level {
            n,
            seed,
            set,
            mem_below,
            omega_mem,
            u0_mem,
            empty_mem,
            transitive,
            sub,
            pairing,
            opair,
            pow,
            union,
            bin_union,
            product,
            funspace,
            app,
        })
    }

    /// Replacement and the dependent product, for a caller-supplied **fibre
    /// family** `b`.
    ///
    /// `Π(x:A). B x` is interpreted through a Replacement image along `b`, and
    /// `b` is a symbol of the ambient extension chosen by the *shape of the
    /// body* — so, exactly like [`crate::prop::conditional_singleton`]'s
    /// formula, it cannot be `∀`-quantified inside one theorem. Hand the symbol
    /// over and get the two statements back at it.
    pub fn family(&self, env: &mut Env, b: FnSym) -> Option<Family> {
        if b.arity() != 1 {
            return None
        }
        let dp = DProd::new(env, &self.sums.ap, &self.sums.fs, b)?;
        let universe_replacement =
            uni::universe_replacement(env, &self.space.empty_ax, dp.img, &dp.img_ax, b)?;
        let replacement = uni::least_universe_replacement(
            env,
            self.space.lu,
            &self.space.lu_ax,
            dp.img,
            b,
            &universe_replacement,
        )?;
        let general = dprod_in_universe_of(
            env,
            &self.sums.ap,
            &self.sums.fs,
            &dp,
            self.space.lu,
            &self.space.c2,
            &self.funspace_of,
        )?;
        let dprod = dprod_in_universe_pair(
            env,
            &self.sums.ap,
            &dp,
            self.space.lu,
            b,
            &replacement,
            &self.union,
            &self.bin_union,
            &general,
        )?;
        Some(Family { b, dp, replacement, dprod })
    }
}

/// The dependent-product half of the interface, at one fibre family.
///
/// See [`Tower::family`] for why this is parameterised rather than quantified.
pub struct Family {
    /// The fibre family symbol handed in.
    pub b: FnSym,
    /// `Π(x:A). b(x)`, and the Replacement image `img(A) = { b(x) : x ∈ A }`.
    pub dp: DProd,
    /// `⊢ ∀c ∀A. ((A ∈ U(c) ∧ ∀x ∈ A. b(x) ∈ U(c)) → img(A) ∈ U(c))`.
    pub replacement: Thm,
    /// `⊢ ∀c ∀A. ((A ∈ U(c) ∧ ∀x ∈ A. b(x) ∈ U(c)) → dprod(A) ∈ U(c))` —
    /// **Lean's `Π` rule**.
    pub dprod: Thm,
}

impl Family {
    /// Both statements at level `n ≥ 1`, with the `∀c` discharged.
    pub fn at(&self, t: &Tower, n: usize) -> Option<(Thm, Thm)> {
        if n == 0 {
            return None
        }
        let seed = t.seed(n);
        Some((
            inst_all(&self.replacement, std::slice::from_ref(&seed))?,
            inst_all(&self.dprod, std::slice::from_ref(&seed))?,
        ))
    }
}

/// One level of the tower, `n ≥ 1`, with every statement at the closed term
/// `Uₙ` rather than under a `∀`.
///
/// The fields are the whole contract; see [`crate::tower`] for the statements.
pub struct Level {
    /// Which level this is.
    pub n: usize,
    /// The seed, i.e. `Uₙ = U(seed)`.
    pub seed: Term,
    /// The term `Uₙ`.
    pub set: Term,
    /// `⊢ U₍ₙ₋₁₎ ∈ Uₙ`.
    pub mem_below: Thm,
    /// `⊢ ω ∈ Uₙ`.
    pub omega_mem: Thm,
    /// `⊢ U₀ ∈ Uₙ`.
    pub u0_mem: Thm,
    /// `⊢ ∅ ∈ Uₙ`.
    pub empty_mem: Thm,
    /// `⊢ ∀y. (y ∈ Uₙ → ∀z. (z ∈ y → z ∈ Uₙ))` — transitivity, hence
    /// `U₍ₙ₋₁₎ ⊆ Uₙ` at `y := U₍ₙ₋₁₎`.
    pub transitive: Thm,
    /// `⊢ ∀y. (y ∈ Uₙ → ∀z. (z ⊆ y → z ∈ Uₙ))`.
    pub sub: Thm,
    /// `⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → {a,b} ∈ Uₙ)`.
    pub pairing: Thm,
    /// `⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → ⟨a,b⟩ ∈ Uₙ)`.
    pub opair: Thm,
    /// `⊢ ∀y. (y ∈ Uₙ → 𝒫y ∈ Uₙ)`.
    pub pow: Thm,
    /// `⊢ ∀s. (s ∈ Uₙ → ⋃s ∈ Uₙ)`.
    pub union: Thm,
    /// `⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → (a ∪ b) ∈ Uₙ)`.
    pub bin_union: Thm,
    /// `⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → prod(a,b) ∈ Uₙ)`.
    pub product: Thm,
    /// `⊢ ∀a ∀b. ((a ∈ Uₙ ∧ b ∈ Uₙ) → fs(a,b) ∈ Uₙ)`.
    pub funspace: Thm,
    /// `⊢ ∀f ∀x. (f ∈ Uₙ → app(f,x) ∈ Uₙ)`.
    pub app: Thm,
}

// ─────────────────────────────────────────────────────────────────────────────
// The four derivations this module does itself. Everything else is assembled.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀c ∀y. (y ∈ U(c) → 𝒫y ∈ U(c))`.
///
/// [`crate::funspace::pow_closed`] at the *variable* universe `U(c)`, whose two
/// hypotheses are [`Space::c2`] and [`Space::c3`] instantiated at `c`, followed
/// by one generalisation. `C₃` alone gives only *some* member above every
/// subset of `y`; `C₂` is what pulls `𝒫y` itself back in.
fn power_closed_everywhere(env: &mut Env, space: &Space) -> Option<Thm> {
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let w = space.universe_of(tc.clone());
    let c2 = inst_all(&space.c2, std::slice::from_ref(&tc))?;
    let c3 = inst_all(&space.c3, std::slice::from_ref(&tc))?;
    let pc = fsp::pow_closed(env, space.pow, &space.pow_ax, &w, &c2, &c3)?;
    Some(Thm::gen(cv, &pc))
}

/// `⊢ ∀c. ∅ ∈ U(c)`.
///
/// `∅ ⊆ c` because nothing is a member of `∅`, `c ∈ U(c)` by
/// [`crate::universe::mem_least_universe`], and `C₂` at `U(c)` puts a subset of
/// a member back in.
///
/// This is the statement [`crate::enums::empty_in_least_universe`] proves. It
/// is re-derived rather than called because that function takes a
/// [`crate::wtype::Wtype`] and a [`crate::bound::Bound`], neither of which the
/// tower needs for anything else and both of which are large; the twelve lines
/// below are cheaper than the two apparatus.
fn empty_everywhere(env: &mut Env, space: &Space) -> Option<Thm> {
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let zero = Term::apply(space.empty, vec![]);

    // `⊢ ∅ ⊆ c`. Built with an explicit bound variable so that the result is
    // syntactically `kernel::thm::subset(∅, c)` — alpha-equivalent formulas are
    // syntactically equal here, so any fresh variable does.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let not_in = inst_all(&space.empty_ax, std::slice::from_ref(&tz))?;
    let body = syl(&not_in, &ex_falso(Formula::mem(tz.clone(), tc.clone())))?;
    let subset_thm = Thm::gen(zv, &body);
    debug_assert_eq!(
        *subset_thm.concl(),
        kernel::thm::subset(env, zero.clone(), tc.clone()),
        "empty_everywhere: the subset formula is not the kernel's"
    );

    let c2 = inst_all(&space.c2, std::slice::from_ref(&tc))?;
    let closed = fsp::sub_closed(&c2, &tc, &zero)?;
    let c_in = inst_all(&space.mem_lu, std::slice::from_ref(&tc))?;
    let out = Thm::mp(&Thm::mp(&closed, &c_in)?, &subset_thm)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(zero, space.universe_of(tc)),
        "empty_everywhere: unexpected shape"
    );
    Some(Thm::gen(cv, &out))
}

/// `⊢ ∀c. U₀ ∈ U(c)`.
///
/// `U₀ = {0, 1}` and `1 = {0, 0}`, so this is [`empty_everywhere`] followed by
/// [`crate::universe::least_universe_pairing`] twice — once to build `1` out of
/// `0`, once to pair the two. Nothing about `c` is used, which is why level 0
/// sits below *every* level of the tower and not only below level 1.
fn u0_everywhere(
    env: &mut Env,
    space: &Space,
    sums: &Sums,
    empty_in: &Thm,
    pairing: &Thm,
) -> Option<Thm> {
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let (zero, one) = (sums.zero(), sums.unit());

    let zero_in = inst_all(empty_in, std::slice::from_ref(&tc))?;
    // `1 = {0,0}`, so the pairing rule at `a = b = 0` produces it on the nose.
    let one_in = Thm::mp(
        &inst_all(pairing, &[tc.clone(), zero.clone(), zero.clone()])?,
        &and_intro(&zero_in, &zero_in),
    )?;
    let out = Thm::mp(
        &inst_all(pairing, &[tc.clone(), zero, one])?,
        &and_intro(&zero_in, &one_in),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(falsity::truth_values(sums), space.universe_of(tc)),
        "u0_everywhere: unexpected shape"
    );
    Some(Thm::gen(cv, &out))
}

/// `⊢ ¬(a = b)` from `⊢ ∀x. ¬(x ∈ x)` and `⊢ a ∈ b`.
///
/// If `b` were `a` then `a ∈ b` would be `a ∈ a`. This is the whole
/// non-degeneracy argument for `U₀ ≠ U₁`, and it needs no cardinality: one
/// membership and Regularity.
fn distinct(env: &mut Env, no_self_mem: &Thm, a_in_b: &Thm, a: &Term, b: &Term) -> Option<Thm> {
    let not_self = inst_all(no_self_mem, std::slice::from_ref(a))?;
    let w = env.fresh_var();
    // `⊢ b = a → (a ∈ b → a ∈ a)`.
    let leib =
        Thm::eq_leibniz(b.clone(), a.clone(), w, Formula::mem(a.clone(), Term::var(w)));
    let step = mpd_const(&leib, a_in_b)?; // `⊢ b = a → a ∈ a`
    let ne_ba = syl(&step, &not_self)?; // `⊢ ¬(b = a)`
    let out = syl(&crate::eq_symm_imp(env, a.clone(), b.clone()), &ne_ba)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(a.clone(), b.clone())),
        "distinct: unexpected shape"
    );
    Some(out)
}

/// `⊢ ω ∈ Uₙ`, by meta-level iteration on `n`.
///
/// The base is [`crate::universe::mem_least_universe`] at `ω`, which is the
/// whole reason level 1 is seeded there. The step is transitivity:
/// `ω ∈ U₍ₙ₋₁₎ ∈ Uₙ` and `C₁(Uₙ)`.
fn omega_at(t: &Tower, n: usize) -> Option<Thm> {
    let omega = t.omega();
    let mut out = inst_all(&t.mem_u, std::slice::from_ref(&omega))?;
    for k in 2..=n {
        let seed = t.seed(k); // `= U₍ₖ₋₁₎`
        let c1 = inst_all(&t.transitive, std::slice::from_ref(&seed))?;
        let at_y = inst_all(&c1, std::slice::from_ref(&seed))?;
        let below = inst_all(&t.mem_u, std::slice::from_ref(&seed))?;
        let all_z = Thm::mp(&at_y, &below)?;
        out = Thm::mp(&inst_all(&all_z, std::slice::from_ref(&omega))?, &out)?;
    }
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(omega, t.level(n)),
        "omega_at: unexpected shape"
    );
    Some(out)
}
