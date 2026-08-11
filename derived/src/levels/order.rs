//! The order theory of `ω`: trichotomy, the case principle, `⊆`-linearity,
//! and `max = ∪`.
//!
//! # Interface
//!
//! Over a caller-supplied [`Rec`] (one chain of definitional extensions, so
//! `∅`, `succ`, `ω`, the pairing and the union are *its* symbols), writing
//! `m ∪ n` for [`crate::funspace::bin_union`] — `⋃{m,n}` in the crate's one
//! spelling of the binary union — the exports are
//!
//! ```text
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n ∨ (m = n ∨ n ∈ m)))       [Order::trichotomy]
//! ⊢ ∀n. (n ∈ ω → (n = ∅ ∨ ∃m. (m ∈ ω ∧ n = succ(m))))          [Order::cases]
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n ↔ (m ∈ n ∨ m = n)))       [Order::sub_iff]
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∪ n) ∈ ω)                     [Order::max_in_omega]
//! ⊢ ∀m ∀n. (m ⊆ (m ∪ n) ∧ n ⊆ (m ∪ n))                         [Order::max_ub]
//! ⊢ ∀m ∀n. (¬(n = ∅) → ¬((m ∪ n) = ∅))                         [Order::max_ne_zero]
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → ((m ∪ n) = m ∨ (m ∪ n) = n))     [Order::max_absorb]
//! ⊢ ∀n. (n ∈ ω → (∅ ∈ n ∨ ∅ = n))                              [Order::zero_least]
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n → succ(m) ∈ succ(n)))     [Order::succ_mono_mem]
//! ⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))                    [Order::mem_bin_union_iff]
//! ```
//!
//! [`Order::max_ub`] holds for *all* sets, so it is stated without the `ω`
//! guard the design sketch carried — a caller with the guard in hand drops it
//! by weakening, never the other way round. [`Order::max_ne_zero`] is
//! unconditional for the same reason and for one more: its caller reads a level
//! *term* and has no membership to spend, so a guarded statement would be
//! unusable there rather than merely heavier. [`Order::max`] spells the term
//! `m ∪ n`, and [`Order::mem_bin_union_iff`] is the membership condition it
//! answers to ([`crate::sums::mem_bin_union_iff`], re-exported here because
//! every `max` fact above is cashed through it). [`order`] is the entry point;
//! callers need none of the derivations below.
//!
//! # Where the content is
//!
//! Trichotomy is the double-induction result; here it is one induction on `n`
//! in `φ(n) := ∀m. (m ∈ ω → (m ∈ n ∨ (m = n ∨ n ∈ m)))`, with the second
//! induction packed into the auxiliary [`succ_mono_raw`]
//! (`m ∈ n → succ(m) ∈ succ(n)`) and the base into [`zero_least_raw`]. In the
//! step, the case `n ∈ m` is sent through the auxiliary to `succ(n) ∈ succ(m)`
//! and split by the successor's membership condition; the other two cases land
//! in `m ∈ succ(n)` directly. `⊆`-linearity then falls out: `m ∈ n → m ⊆ n`
//! is transitivity of `n` ([`crate::recursion::Peano::trans`]), and the reverse
//! direction kills the third trichotomy disjunct with `n ∈ n` against
//! Regularity ([`crate::recursion::Peano::no_self_mem`]). The `max` facts are
//! trichotomy plus one Extensionality argument each way
//! ([`union_absorb_one`]: a `⊆`-comparable pair's union is the larger side).

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::funspace::bin_union;
use crate::recursion::{induction_scheme, mem_succ_self, OmegaCore, Peano, Rec};
use crate::separation::{or_intro_left, or_intro_right};
use crate::{
    a1i, and_intro, and_left, and_right, com12, contrapos, disj_inject, eq_symm_imp, ex_falso,
    exists_intro_imp, gen_all, hyp_and, hyp_iff_mpr, hyp_mp, hyp_or_elim, iff_mp, iff_mpr,
    imp_mono_r, imp_refl, inst_all, mpd_const, syl, uncurry,
};

/// The order theory of `ω`, assembled once over a caller-supplied [`Rec`].
pub struct Order {
    /// The pairing and union `max` is spelled with — [`Rec`]'s own.
    pub sets: Sets,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n ∨ (m = n ∨ n ∈ m)))`.
    pub trichotomy: Thm,
    /// `⊢ ∀n. (n ∈ ω → (n = ∅ ∨ ∃m. (m ∈ ω ∧ n = succ(m))))`.
    pub cases: Thm,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n ↔ (m ∈ n ∨ m = n)))`.
    pub sub_iff: Thm,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∪ n) ∈ ω)`.
    pub max_in_omega: Thm,
    /// `⊢ ∀m ∀n. (m ⊆ (m ∪ n) ∧ n ⊆ (m ∪ n))` — unconditional; see the module
    /// documentation.
    pub max_ub: Thm,
    /// `⊢ ∀m ∀n. (¬(n = ∅) → ¬((m ∪ n) = ∅))` — a `max` with a nonzero **right**
    /// operand is nonzero.
    ///
    /// Unconditional, like [`Order::max_ub`] it is cashed through, and that is
    /// the whole reason it is stated rather than left to the caller: the
    /// `ω`-guarded route through [`Order::sub_iff`] proves the same thing and
    /// makes every consumer produce `n ∈ ω` and `(m ∪ n) ∈ ω` first. The
    /// consumer here is `mini`'s binder collapse, which walks an interpreted
    /// `Π`'s guard as a *term* and has no level expression to read a
    /// membership off — see `mini::interp::Interp::level_guard_at`.
    ///
    /// **The right operand and not both**, because the one caller is `imax`:
    /// `imax(m,n)` is `ite0(n, ∅, m ∪ n)`, so the operand a settled guard is
    /// about is always the second. A left-hand twin is [`max_ub`]'s other
    /// conjunct and four lines, and is not written because nothing asks.
    pub max_ne_zero: Thm,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → ((m ∪ n) = m ∨ (m ∪ n) = n))`.
    pub max_absorb: Thm,
    /// `⊢ ∀n. (n ∈ ω → (∅ ∈ n ∨ ∅ = n))`.
    pub zero_least: Thm,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n → succ(m) ∈ succ(n)))`.
    pub succ_mono_mem: Thm,
    /// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))` — the membership condition
    /// `max` answers to ([`crate::sums::mem_bin_union_iff`], re-exported).
    pub mem_bin_union_iff: Thm,
}

impl Order {
    /// The term `m ∪ n` — `max` on von Neumann naturals, spelled the one way
    /// the crate spells the binary union (`⋃{m,n}`).
    pub fn max(&self, m: Term, n: Term) -> Term {
        bin_union(&self.sets, m, n)
    }
}

/// Derive the lot, over the `Rec`'s symbols.
pub fn order(env: &mut Env, r: &Rec) -> Option<Order> {
    let core = r.core().clone();
    let peano = &r.peano;
    let sets = r.ap.sets.clone();

    let zero_least = zero_least_raw(env, &core)?;
    let succ_mono = succ_mono_raw(env, &core)?;
    let trichotomy = trichotomy(env, &core, &zero_least, &succ_mono)?;
    let cases = cases(env, &core)?;
    let sub_iff = sub_iff(env, &core, peano, &trichotomy)?;

    let bin_iff = crate::sums::mem_bin_union_iff(env, &sets)?;
    let absorb_left = union_absorb_one(env, &sets, &bin_iff, true)?;
    let absorb_right = union_absorb_one(env, &sets, &bin_iff, false)?;
    let max_ub = max_ub(env, &sets, &bin_iff)?;
    let max_absorb =
        max_absorb(env, &core, &sets, &trichotomy, &sub_iff, &absorb_left, &absorb_right)?;
    let max_in_omega = max_in_omega(env, &core, &sets, &max_absorb)?;
    let succ_mono_mem = guard_succ_mono(env, &core, &succ_mono)?;
    let max_ne_zero = max_ne_zero(env, &core, &sets, &max_ub)?;

    Some(Order {
        sets,
        trichotomy,
        cases,
        sub_iff,
        max_in_omega,
        max_ub,
        max_ne_zero,
        max_absorb,
        zero_least,
        succ_mono_mem,
        mem_bin_union_iff: bin_iff,
    })
}

/// `⊢ z ∈ a → z ∈ succ(a)` for caller-supplied terms — the left disjunct of
/// the successor's membership condition.
fn widen(core: &OmegaCore, a: &Term, z: &Term) -> Option<Thm> {
    let at = inst_all(&core.succ_ax, &[a.clone(), z.clone()])?;
    syl(
        &or_intro_left(Formula::mem(z.clone(), a.clone()), Formula::eq(z.clone(), a.clone())),
        &iff_mpr(&at)?,
    )
}

/// `⊢ ∀n. (n ∈ ω → (∅ ∈ n ∨ ∅ = n))` — zero is below every natural.
///
/// Induction in `φ(n) := (∅ ∈ n ∨ ∅ = n)`: at `∅` the right disjunct is
/// reflexivity, and the step is the successor's membership condition read
/// backwards — its right-hand side at `z := ∅` *is* `φ(n)`.
fn zero_least_raw(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let (zero, w) = (core.zero(), core.set());
    let phi = Formula::or(
        Formula::mem(zero.clone(), tn.clone()),
        Formula::eq(zero.clone(), tn.clone()),
    );
    let scheme = induction_scheme(env, core, n, &phi)?;

    let base = Thm::mp(
        &or_intro_right(
            Formula::mem(zero.clone(), zero.clone()),
            Formula::eq(zero.clone(), zero.clone()),
        ),
        &Thm::eq_refl(zero.clone()),
    )?;

    let sn = core.succ_of(tn.clone());
    let into_succ = iff_mpr(&inst_all(&core.succ_ax, &[tn.clone(), zero.clone()])?)?;
    let inject = or_intro_left(
        Formula::mem(zero.clone(), sn.clone()),
        Formula::eq(zero.clone(), sn.clone()),
    );
    let n_om = Formula::mem(tn.clone(), w);
    let step_body = syl(&and_right(n_om.clone(), phi.clone()), &syl(&into_succ, &inject)?)?;

    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(n, &step_body)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(n, Formula::imp(n_om, phi)),
        "zero_least: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ n → succ(m) ∈ succ(n)))` — the successor is
/// monotone along `∈`, guarded on the **container** only.
///
/// Induction in `φ(n) := ∀m. (m ∈ n → succ(m) ∈ succ(n))`. The base is vacuous
/// (`m ∈ ∅` refutes itself); in the step `m ∈ succ(n)` splits: `m ∈ n` goes
/// through the induction hypothesis and one widening, `m = n` rewrites
/// `succ(n) ∈ succ(succ(n))` ([`mem_succ_self`]).
fn succ_mono_raw(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    let (n, m) = (env.fresh_var(), env.fresh_var());
    let (tn, tm) = (Term::var(n), Term::var(m));
    let w = core.set();
    let (sm, sn) = (core.succ_of(tm.clone()), core.succ_of(tn.clone()));
    let phi = Formula::forall(
        m,
        Formula::imp(Formula::mem(tm.clone(), tn.clone()), Formula::mem(sm.clone(), sn.clone())),
    );
    let scheme = induction_scheme(env, core, n, &phi)?;

    // ── base: vacuous at `∅` ─────────────────────────────────────────────────
    let zero = core.zero();
    let base_body = syl(
        &inst_all(&core.empty_ax, std::slice::from_ref(&tm))?,
        &ex_falso(Formula::mem(sm.clone(), core.succ_of(zero.clone()))),
    )?;
    let base = Thm::gen(m, &base_body);
    debug_assert_eq!(*base.concl(), phi.subst(n, &zero), "succ_mono_raw: base drifted");

    // ── step, under `K := n ∈ ω ∧ φ(n)`, then `L := K ∧ m ∈ succ(n)` ─────────
    let n_om = Formula::mem(tn.clone(), w);
    let k = Formula::and(n_om.clone(), phi.clone());
    let ssn = core.succ_of(sn.clone());
    let mem_msn = Formula::mem(tm.clone(), sn.clone());
    let goal_mem = Formula::mem(sm.clone(), ssn.clone());
    let l = Formula::and(k.clone(), mem_msn.clone());

    let l_k = and_left(k.clone(), mem_msn.clone());
    let l_disj = syl(
        &and_right(k.clone(), mem_msn.clone()),
        &iff_mp(&inst_all(&core.succ_ax, &[tn.clone(), tm.clone()])?)?,
    )?;

    // Case `m ∈ n`: the induction hypothesis, then one widening.
    let k_ih = syl(&and_right(n_om, phi.clone()), &Thm::ax_inst(phi.clone(), tm.clone())?)?;
    let up = widen(core, &sn, &sm)?;
    let k_case_mem = syl(&k_ih, &imp_mono_r(&up, Formula::mem(tm.clone(), tn.clone()))?)?;
    let l_case_mem = syl(&l_k, &k_case_mem)?;

    // Case `m = n`: rewrite `succ(n) ∈ succ(succ(n))` along the equation.
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        tn.clone(),
        tm.clone(),
        hole,
        Formula::mem(core.succ_of(Term::var(hole)), ssn.clone()),
    );
    let case_eq = syl(
        &eq_symm_imp(env, tm.clone(), tn.clone()),
        &mpd_const(&leib, &mem_succ_self(core, &sn)?)?,
    )?;
    let l_case_eq = a1i(&case_eq, l);

    let l_goal = hyp_or_elim(&l_disj, &l_case_mem, &l_case_eq)?;
    let step_body = uncurry(&l_goal)?;
    let k_all = Thm::mp(
        &Thm::ax_dist(m, k.clone(), Formula::imp(mem_msn, goal_mem))?,
        &Thm::gen(m, &step_body),
    )?;
    debug_assert_eq!(
        *k_all.concl(),
        Formula::imp(k, phi.subst(n, &sn)),
        "succ_mono_raw: step drifted"
    );

    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(n, &k_all)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(n, Formula::imp(Formula::mem(tn, core.set()), phi)),
        "succ_mono_raw: unexpected shape"
    );
    Some(out)
}

/// The inner formula of [`succ_mono_raw`] at a caller-supplied container:
/// `∀a. (a ∈ n → succ(a) ∈ succ(n))`.
fn succ_mono_inner(env: &mut Env, core: &OmegaCore, n: &Term) -> Formula {
    let a = env.fresh_var();
    let ta = Term::var(a);
    Formula::forall(
        a,
        Formula::imp(
            Formula::mem(ta.clone(), n.clone()),
            Formula::mem(core.succ_of(ta), core.succ_of(n.clone())),
        ),
    )
}

/// [`succ_mono_raw`] restated with the symmetric guard the interface promises:
/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n → succ(m) ∈ succ(n)))`.
fn guard_succ_mono(env: &mut Env, core: &OmegaCore, raw: &Thm) -> Option<Thm> {
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = core.set();
    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w.clone());

    let at_n = inst_all(raw, std::slice::from_ref(&tn))?;
    let inner = succ_mono_inner(env, core, &tn);
    let at_m = Thm::ax_inst(inner, tm.clone())?;
    let body = syl(&and_right(m_om.clone(), n_om.clone()), &syl(&at_n, &at_m)?)?;
    let out = gen_all(&[m, n], &body);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            m,
            Formula::forall(
                n,
                Formula::imp(
                    Formula::and(m_om, n_om),
                    Formula::imp(
                        Formula::mem(tm.clone(), tn.clone()),
                        Formula::mem(core.succ_of(tm), core.succ_of(tn))
                    )
                )
            )
        ),
        "guard_succ_mono: unexpected shape"
    );
    Some(out)
}

/// The trichotomy disjunction `x ∈ y ∨ (x = y ∨ y ∈ x)`, right-nested.
fn tri_disj(x: &Term, y: &Term) -> [Formula; 3] {
    [
        Formula::mem(x.clone(), y.clone()),
        Formula::eq(x.clone(), y.clone()),
        Formula::mem(y.clone(), x.clone()),
    ]
}

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n ∨ (m = n ∨ n ∈ m)))` — **trichotomy
/// on `ω`**.
///
/// One induction on `n` in `φ(n) := ∀m. (m ∈ ω → D(m,n))`; the second
/// induction of the textbook proof lives in `succ_mono` and the base in
/// `zero_least`. In the step, `D(m,n)` splits: `m ∈ n` and `m = n` both land
/// in `m ∈ succ(n)`; `n ∈ m` goes through `succ`-monotonicity to
/// `succ(n) ∈ succ(m)`, which the successor's membership condition splits into
/// the remaining two disjuncts.
fn trichotomy(env: &mut Env, core: &OmegaCore, zero_least: &Thm, succ_mono: &Thm) -> Option<Thm> {
    let (n, m) = (env.fresh_var(), env.fresh_var());
    let (tn, tm) = (Term::var(n), Term::var(m));
    let w = core.set();
    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w.clone());

    let d_n = crate::disj_of(&tri_disj(&tm, &tn))?;
    let phi = Formula::forall(m, Formula::imp(m_om.clone(), d_n.clone()));
    let scheme = induction_scheme(env, core, n, &phi)?;

    // ── base: `D(m, ∅)` from `zero_least` ────────────────────────────────────
    let zero = core.zero();
    let atoms0 = tri_disj(&tm, &zero);
    let case_zero_mem = disj_inject(&atoms0, 2)?;
    let case_zero_eq = syl(&eq_symm_imp(env, zero.clone(), tm.clone()), &disj_inject(&atoms0, 1)?)?;
    let zl_disj = Formula::or(
        Formula::mem(zero.clone(), tm.clone()),
        Formula::eq(zero.clone(), tm.clone()),
    );
    let bridge = hyp_or_elim(
        &imp_refl(zl_disj.clone()),
        &a1i(&case_zero_mem, zl_disj.clone()),
        &a1i(&case_zero_eq, zl_disj),
    )?;
    let base_body = syl(&inst_all(zero_least, std::slice::from_ref(&tm))?, &bridge)?;
    let base = Thm::gen(m, &base_body);
    debug_assert_eq!(*base.concl(), phi.subst(n, &zero), "trichotomy: base drifted");

    // ── step, under `K := n ∈ ω ∧ φ(n)`, then `J := K ∧ m ∈ ω` ───────────────
    let sn = core.succ_of(tn.clone());
    let k = Formula::and(n_om.clone(), phi.clone());
    let atoms_sn = tri_disj(&tm, &sn);
    let d_sn = crate::disj_of(&atoms_sn)?;

    let j = Formula::and(k.clone(), m_om.clone());
    let j_k = and_left(k.clone(), m_om.clone());
    let j_m = and_right(k.clone(), m_om.clone());
    let j_ih = hyp_mp(
        &syl(
            &j_k,
            &syl(&and_right(n_om.clone(), phi.clone()), &Thm::ax_inst(phi.clone(), tm.clone())?)?,
        )?,
        &j_m,
    )?;

    // Case `m ∈ n`: widen into `succ(n)`.
    let case_a = syl(&widen(core, &tn, &tm)?, &disj_inject(&atoms_sn, 0)?)?;
    // Case `m = n`: rewrite `n ∈ succ(n)` to `m ∈ succ(n)`.
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        tn.clone(),
        tm.clone(),
        hole,
        Formula::mem(Term::var(hole), sn.clone()),
    );
    let m_in_sn = syl(
        &eq_symm_imp(env, tm.clone(), tn.clone()),
        &mpd_const(&leib, &mem_succ_self(core, &tn)?)?,
    )?;
    let case_b = syl(&m_in_sn, &disj_inject(&atoms_sn, 0)?)?;
    // Case `n ∈ m`: monotonicity to `succ(n) ∈ succ(m)`, then split it.
    let c_f = Formula::mem(tn.clone(), tm.clone());
    let l = Formula::and(j.clone(), c_f.clone());
    let inner_m = succ_mono_inner(env, core, &tm);
    let mono_at = syl(
        &inst_all(succ_mono, std::slice::from_ref(&tm))?,
        &Thm::ax_inst(inner_m, tn.clone())?,
    )?;
    let l_j = and_left(j.clone(), c_f.clone());
    let l_mono = syl(&syl(&l_j, &j_m)?, &mono_at)?;
    let l_snsm = hyp_mp(&l_mono, &and_right(j.clone(), c_f.clone()))?;
    let l_split = syl(&l_snsm, &iff_mp(&inst_all(&core.succ_ax, &[tm.clone(), sn.clone()])?)?)?;
    let sub_mem = disj_inject(&atoms_sn, 2)?;
    let sub_eq = syl(&eq_symm_imp(env, sn.clone(), tm.clone()), &disj_inject(&atoms_sn, 1)?)?;
    let l_goal = hyp_or_elim(&l_split, &a1i(&sub_mem, l.clone()), &a1i(&sub_eq, l))?;
    let j_case_c = uncurry(&l_goal)?;

    // Assemble the three cases over `D(m, n)`.
    let b_f = Formula::eq(tm.clone(), tn.clone());
    let bc_f = Formula::or(b_f, c_f);
    let h2 = Formula::and(j.clone(), bc_f.clone());
    let h2_goal = hyp_or_elim(
        &and_right(j.clone(), bc_f.clone()),
        &a1i(&case_b, h2),
        &syl(&and_left(j.clone(), bc_f), &j_case_c)?,
    )?;
    let j_right = uncurry(&h2_goal)?;
    let j_goal = hyp_or_elim(&j_ih, &a1i(&case_a, j.clone()), &j_right)?;
    debug_assert_eq!(*j_goal.concl(), Formula::imp(j, d_sn.clone()), "trichotomy: step case split");

    let step_body = uncurry(&j_goal)?;
    let k_all = Thm::mp(
        &Thm::ax_dist(m, k.clone(), Formula::imp(m_om.clone(), d_sn))?,
        &Thm::gen(m, &step_body),
    )?;
    debug_assert_eq!(*k_all.concl(), Formula::imp(k, phi.subst(n, &sn)), "trichotomy: step drifted");
    let raw = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(n, &k_all)))?;

    // ── massage `∀n ∀m` with guards in sequence into `∀m ∀n` with `∧` ────────
    let j_mn = Formula::and(m_om.clone(), n_om.clone());
    let g1 = syl(&and_right(m_om.clone(), n_om.clone()), &inst_all(&raw, std::slice::from_ref(&tn))?)?;
    let g2 = syl(&g1, &Thm::ax_inst(phi, tm)?)?;
    let g3 = hyp_mp(&g2, &and_left(m_om, n_om))?;
    let out = gen_all(&[m, n], &g3);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(j_mn, d_n))),
        "trichotomy: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀n. (n ∈ ω → (n = ∅ ∨ ∃m. (m ∈ ω ∧ n = succ(m))))` — every natural is
/// zero or a successor of a natural.
///
/// Induction in the disjunction itself: at `∅` the left disjunct is
/// reflexivity, and at `succ(n)` the right disjunct is witnessed by `n`.
fn cases(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    let (n, mv) = (env.fresh_var(), env.fresh_var());
    let (tn, tmv) = (Term::var(n), Term::var(mv));
    let (zero, w) = (core.zero(), core.set());
    let ex_body = Formula::and(
        Formula::mem(tmv.clone(), w.clone()),
        Formula::eq(tn.clone(), core.succ_of(tmv)),
    );
    let phi = Formula::or(
        Formula::eq(tn.clone(), zero.clone()),
        Formula::exists(mv, ex_body.clone()),
    );
    let scheme = induction_scheme(env, core, n, &phi)?;

    let base = Thm::mp(
        &or_intro_left(
            Formula::eq(zero.clone(), zero.clone()),
            Formula::exists(mv, ex_body.subst(n, &zero)),
        ),
        &Thm::eq_refl(zero.clone()),
    )?;
    debug_assert_eq!(*base.concl(), phi.subst(n, &zero), "cases: base drifted");

    let sn = core.succ_of(tn.clone());
    let n_om = Formula::mem(tn.clone(), w);
    let ex_sn = ex_body.subst(n, &sn);
    let witness = hyp_and(&imp_refl(n_om.clone()), &a1i(&Thm::eq_refl(sn.clone()), n_om.clone()))?;
    debug_assert_eq!(
        *witness.concl(),
        Formula::imp(n_om.clone(), ex_sn.subst(mv, &tn)),
        "cases: the witness drifted"
    );
    let h_ex = syl(&witness, &exists_intro_imp(mv, ex_sn.clone(), tn.clone())?)?;
    let h_phi = syl(
        &h_ex,
        &or_intro_right(Formula::eq(sn, zero), Formula::exists(mv, ex_sn)),
    )?;
    let step_body = syl(&and_left(n_om.clone(), phi.clone()), &h_phi)?;

    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(n, &step_body)))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(n, Formula::imp(n_om, phi)),
        "cases: unexpected shape"
    );
    Some(out)
}

/// `⊢ Trans(n) → (m ∈ n → m ⊆ n)` for caller-supplied terms — a member of a
/// transitive set is a subset of it.
fn mem_to_sub(env: &mut Env, m: &Term, n: &Term) -> Option<Thm> {
    let trans = crate::empty::transitive(env, n);
    let z = env.fresh_var();
    let tz = Term::var(z);
    let t1 = Thm::ax_inst(trans.clone(), m.clone())?;
    let (_, t1_body) = t1.concl().as_imp()?;
    let t2 = syl(&t1, &Thm::ax_inst(t1_body, tz.clone())?)?;

    let mem_mn = Formula::mem(m.clone(), n.clone());
    let mem_zm = Formula::mem(tz.clone(), m.clone());
    let mem_zn = Formula::mem(tz, n.clone());
    let p = Formula::and(trans.clone(), mem_mn.clone());
    let q_p = and_left(p.clone(), mem_zm.clone());
    let q_pair = hyp_and(
        &and_right(p.clone(), mem_zm.clone()),
        &syl(&q_p, &and_right(trans.clone(), mem_mn.clone()))?,
    )?;
    let q_zn = hyp_mp(&syl(&q_p, &syl(&and_left(trans.clone(), mem_mn), &t2)?)?, &q_pair)?;
    let p_imp = uncurry(&q_zn)?;
    let p_sub = Thm::mp(
        &Thm::ax_dist(z, p, Formula::imp(mem_zm, mem_zn))?,
        &Thm::gen(z, &p_imp),
    )?;
    let out = uncurry(&p_sub)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            trans,
            Formula::imp(
                Formula::mem(m.clone(), n.clone()),
                kernel::thm::subset(env, m.clone(), n.clone())
            )
        ),
        "mem_to_sub: unexpected shape"
    );
    Some(out)
}

/// `⊢ a = b → a ⊆ b` for caller-supplied terms — reflexivity carried along
/// the equation by Leibniz.
fn eq_to_sub(env: &mut Env, a: &Term, b: &Term) -> Option<Thm> {
    let z = env.fresh_var();
    let tz = Term::var(z);
    let refl = Thm::gen(z, &imp_refl(Formula::mem(tz.clone(), a.clone())));
    let hole = env.fresh_var();
    let sub_hole = Formula::forall(
        z,
        Formula::imp(Formula::mem(tz.clone(), a.clone()), Formula::mem(tz, Term::var(hole))),
    );
    let leib = Thm::eq_leibniz(a.clone(), b.clone(), hole, sub_hole);
    let out = mpd_const(&leib, &refl)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::eq(a.clone(), b.clone()),
            kernel::thm::subset(env, a.clone(), b.clone())
        ),
        "eq_to_sub: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n ↔ (m ∈ n ∨ m = n)))` —
/// **`⊆`-linearity**: on `ω`, inclusion is exactly "member or equal".
///
/// Backward: `m ∈ n → m ⊆ n` is transitivity of `n`, and `m = n → m ⊆ n` is
/// Leibniz over reflexivity. Forward: trichotomy leaves only `n ∈ m` to kill,
/// and `m ⊆ n` sends it to `n ∈ n`, which Regularity refutes.
fn sub_iff(env: &mut Env, core: &OmegaCore, peano: &Peano, trichotomy: &Thm) -> Option<Thm> {
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = core.set();
    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w);
    let j = Formula::and(m_om.clone(), n_om.clone());
    let sub = kernel::thm::subset(env, tm.clone(), tn.clone());
    let a_f = Formula::mem(tm.clone(), tn.clone());
    let b_f = Formula::eq(tm.clone(), tn.clone());
    let c_f = Formula::mem(tn.clone(), tm.clone());
    let ab = Formula::or(a_f.clone(), b_f.clone());

    // ── forward: under `H := J ∧ m ⊆ n`, eliminate the third disjunct ────────
    let h = Formula::and(j.clone(), sub.clone());
    let h_d = syl(&and_left(j.clone(), sub.clone()), &inst_all(trichotomy, &[tm.clone(), tn.clone()])?)?;
    let case_a = or_intro_left(a_f, b_f.clone());
    let case_b = or_intro_right(Formula::mem(tm.clone(), tn.clone()), b_f.clone());
    let h3 = Formula::and(h.clone(), c_f.clone());
    let h3_sub = syl(&and_left(h.clone(), c_f.clone()), &and_right(j.clone(), sub.clone()))?;
    let h3_imp = syl(&h3_sub, &Thm::ax_inst(sub.clone(), tn.clone())?)?;
    let h3_nn = hyp_mp(&h3_imp, &and_right(h.clone(), c_f.clone()))?;
    let no_self_n = inst_all(&peano.no_self_mem, std::slice::from_ref(&tn))?;
    let h3_false = hyp_mp(&a1i(&no_self_n, h3), &h3_nn)?;
    let h_case_c = uncurry(&syl(&h3_false, &ex_falso(ab.clone()))?)?;
    let bc_f = Formula::or(b_f, c_f.clone());
    let h2 = Formula::and(h.clone(), bc_f.clone());
    let h2_goal = hyp_or_elim(
        &and_right(h.clone(), bc_f.clone()),
        &a1i(&case_b, h2),
        &syl(&and_left(h.clone(), bc_f), &h_case_c)?,
    )?;
    let h_goal = hyp_or_elim(&h_d, &a1i(&case_a, h), &uncurry(&h2_goal)?)?;
    let fwd = uncurry(&h_goal)?;

    // ── backward: transitivity for the member, Leibniz for the equal ─────────
    let from_mem = syl(
        &inst_all(&peano.trans, std::slice::from_ref(&tn))?,
        &mem_to_sub(env, &tm, &tn)?,
    )?;
    let g = Formula::and(j.clone(), ab.clone());
    let g_mem = syl(
        &syl(&and_left(j.clone(), ab.clone()), &and_right(m_om, n_om))?,
        &from_mem,
    )?;
    let g_eq = a1i(&eq_to_sub(env, &tm, &tn)?, g);
    let g_goal = hyp_or_elim(&and_right(j.clone(), ab.clone()), &g_mem, &g_eq)?;
    let bwd = uncurry(&g_goal)?;

    let out = gen_all(&[m, n], &hyp_and(&fwd, &bwd)?);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(j, Formula::iff(sub, ab)))),
        "sub_iff: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀a ∀b. (b ⊆ a → a ∪ b = a)` when `keep_left`, else
/// `⊢ ∀a ∀b. (a ⊆ b → a ∪ b = b)` — a `⊆`-comparable pair's union is the
/// larger side, by Extensionality over the membership condition.
///
/// `pub(crate)` for [`crate::levels::leq`], whose `imax_absorb` spends the
/// `keep_left = false` direction — one construction, not two.
pub(crate) fn union_absorb_one(env: &mut Env, sets: &Sets, bin_iff: &Thm, keep_left: bool) -> Option<Thm> {
    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let bu = bin_union(sets, ta.clone(), tb.clone());
    let (src, kept) = if keep_left { (tb.clone(), ta.clone()) } else { (ta.clone(), tb.clone()) };
    let sub = kernel::thm::subset(env, src, kept.clone());

    let mem_za = Formula::mem(tz.clone(), ta.clone());
    let mem_zb = Formula::mem(tz.clone(), tb.clone());
    let mem_zbu = Formula::mem(tz.clone(), bu.clone());
    let mem_zkept = Formula::mem(tz.clone(), kept.clone());
    let at = inst_all(bin_iff, &[ta, tb, tz.clone()])?;

    // Forward under `sub`: a member of the union lands in the kept side.
    let h2 = Formula::and(sub.clone(), mem_zbu.clone());
    let h2_disj = syl(&and_right(sub.clone(), mem_zbu.clone()), &iff_mp(&at)?)?;
    let via_sub = syl(&and_left(sub.clone(), mem_zbu.clone()), &Thm::ax_inst(sub.clone(), tz)?)?;
    let keep_id = a1i(&imp_refl(mem_zkept.clone()), h2);
    let (h2_l, h2_r) = if keep_left { (keep_id, via_sub) } else { (via_sub, keep_id) };
    let h_fwd = uncurry(&hyp_or_elim(&h2_disj, &h2_l, &h2_r)?)?;

    // Backward, unconditional: the kept side injects into the union.
    let intro = if keep_left {
        or_intro_left(mem_za, mem_zb)
    } else {
        or_intro_right(mem_za, mem_zb)
    };
    let bwd = syl(&intro, &iff_mpr(&at)?)?;

    let h_iff = hyp_and(&h_fwd, &a1i(&bwd, sub.clone()))?;
    let h_all = Thm::mp(
        &Thm::ax_dist(z, sub.clone(), Formula::iff(mem_zbu, mem_zkept))?,
        &Thm::gen(z, &h_iff),
    )?;
    let ext_at = inst_all(&Thm::ax_extensionality(env), &[bu.clone(), kept.clone()])?;
    let out = syl(&h_all, &ext_at)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(sub, Formula::eq(bu, kept)),
        "union_absorb_one: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

/// `⊢ ∀m ∀n. (m ⊆ (m ∪ n) ∧ n ⊆ (m ∪ n))` — the union bounds both sides.
/// Holds for all sets, so no `ω` guard.
fn max_ub(env: &mut Env, sets: &Sets, bin_iff: &Thm) -> Option<Thm> {
    let (m, n, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, tn, tz) = (Term::var(m), Term::var(n), Term::var(z));
    let bu = bin_union(sets, tm.clone(), tn.clone());
    let mem_zm = Formula::mem(tz.clone(), tm.clone());
    let mem_zn = Formula::mem(tz.clone(), tn.clone());
    let at = inst_all(bin_iff, &[tm.clone(), tn.clone(), tz])?;

    let left = syl(&or_intro_left(mem_zm.clone(), mem_zn.clone()), &iff_mpr(&at)?)?;
    let right = syl(&or_intro_right(mem_zm, mem_zn), &iff_mpr(&at)?)?;
    let out = gen_all(&[m, n], &and_intro(&Thm::gen(z, &left), &Thm::gen(z, &right)));
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            m,
            Formula::forall(
                n,
                Formula::and(
                    kernel::thm::subset(env, tm.clone(), bu.clone()),
                    kernel::thm::subset(env, tn, bu)
                )
            )
        ),
        "max_ub: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀x. (x ⊆ ∅ → x = ∅)` — a subset of the empty set is empty.
///
/// Extensionality one way and vacuity the other: the forward half of
/// `z ∈ x ↔ z ∈ ∅` *is* the subset hypothesis instantiated, and the backward
/// half is [`OmegaCore::empty_ax`] and `ex_falso`, which needs no hypothesis at
/// all. No `ω` anywhere — this is pure set theory, and stating it that way is
/// what keeps [`max_ne_zero`] unguarded.
fn sub_empty(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));
    let zero = core.zero();
    let sub = kernel::thm::subset(env, tx.clone(), zero.clone());
    let (mem_zx, mem_z0) = (Formula::mem(tz.clone(), tx.clone()), Formula::mem(tz.clone(), zero.clone()));

    // `x ⊆ ∅ → (z ∈ x → z ∈ ∅)`, which is the hypothesis opened at `z`, and
    // `x ⊆ ∅ → (z ∈ ∅ → z ∈ x)`, which ignores it.
    let fwd = crate::prim::ax_inst(sub.clone(), tz.clone()).ok()?;
    let bwd = a1i(
        &syl(&inst_all(&core.empty_ax, std::slice::from_ref(&tz))?, &ex_falso(mem_zx.clone()))?,
        sub.clone(),
    );
    let iff_at = hyp_and(&fwd, &bwd)?;
    let pointwise = Formula::iff(mem_zx, mem_z0);
    debug_assert_eq!(
        *iff_at.concl(),
        Formula::imp(sub.clone(), pointwise.clone()),
        "sub_empty: the pointwise biconditional drifted"
    );

    // `∀z` under the hypothesis, then Extensionality at `(x, ∅)`.
    let all = Thm::mp(
        &crate::prim::ax_dist(z, sub.clone(), pointwise).ok()?,
        &Thm::gen(z, &iff_at),
    )?;
    let ext_at = inst_all(&Thm::ax_extensionality(env), &[tx.clone(), zero.clone()])?;
    let out = syl(&all, &ext_at)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(sub, Formula::eq(tx, zero)),
        "sub_empty: unexpected shape"
    );
    Some(Thm::gen(x, &out))
}

/// `⊢ ∀m ∀n. (¬(n = ∅) → ¬((m ∪ n) = ∅))` — see [`Order::max_ne_zero`].
///
/// Contraposition of `(m ∪ n) = ∅ → n = ∅`: [`max_ub`]'s right conjunct is
/// `n ⊆ (m ∪ n)` unconditionally, the equation carries it to `n ⊆ ∅` in one
/// Leibniz step, and [`sub_empty`] finishes.
fn max_ne_zero(env: &mut Env, core: &OmegaCore, sets: &Sets, max_ub: &Thm) -> Option<Thm> {
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let zero = core.zero();
    let bu = bin_union(sets, tm.clone(), tn.clone());

    let ub = inst_all(max_ub, &[tm.clone(), tn.clone()])?;
    let n_sub_bu = Thm::mp(
        &and_right(
            kernel::thm::subset(env, tm, bu.clone()),
            kernel::thm::subset(env, tn.clone(), bu.clone()),
        ),
        &ub,
    )?;
    // `(m ∪ n) = ∅ → (n ⊆ (m ∪ n) → n ⊆ ∅)`, with the second premise in hand.
    let w = env.fresh_var();
    let carried = mpd_const(
        &Thm::eq_leibniz(
            bu.clone(),
            zero.clone(),
            w,
            kernel::thm::subset(env, tn.clone(), Term::var(w)),
        ),
        &n_sub_bu,
    )?;
    let to_empty = syl(&carried, &inst_all(&sub_empty(env, core)?, std::slice::from_ref(&tn))?)?;
    let out = contrapos(&to_empty)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::not(Formula::eq(tn, zero.clone())),
            Formula::not(Formula::eq(bu, zero))
        ),
        "max_ne_zero: unexpected shape"
    );
    Some(gen_all(&[m, n], &out))
}

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → ((m ∪ n) = m ∨ (m ∪ n) = n))` — on `ω` the
/// union of two elements **is** one of them.
///
/// Trichotomy splits the pair; `m ∈ n ∨ m = n` gives `m ⊆ n` through
/// [`sub_iff`] and absorbs rightward, `n ∈ m` gives `n ⊆ m` (the same
/// biconditional with the guard swapped) and absorbs leftward.
fn max_absorb(
    env: &mut Env,
    core: &OmegaCore,
    sets: &Sets,
    trichotomy: &Thm,
    sub_iff: &Thm,
    absorb_left: &Thm,
    absorb_right: &Thm,
) -> Option<Thm> {
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = core.set();
    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w);
    let j = Formula::and(m_om.clone(), n_om.clone());
    let bu = bin_union(sets, tm.clone(), tn.clone());
    let e1 = Formula::eq(bu.clone(), tm.clone());
    let e2 = Formula::eq(bu.clone(), tn.clone());
    let goal = Formula::or(e1.clone(), e2.clone());
    let a_f = Formula::mem(tm.clone(), tn.clone());
    let b_f = Formula::eq(tm.clone(), tn.clone());
    let c_f = Formula::mem(tn.clone(), tm.clone());
    let ab = Formula::or(a_f.clone(), b_f.clone());

    let tri_at = inst_all(trichotomy, &[tm.clone(), tn.clone()])?;

    // `m ∈ n ∨ m = n`: absorb rightward.
    let j_mpr = hyp_iff_mpr(&inst_all(sub_iff, &[tm.clone(), tn.clone()])?)?;
    let chain = syl(&inst_all(absorb_right, &[tm.clone(), tn.clone()])?, &or_intro_right(e1.clone(), e2.clone()))?;
    let case_ab = syl(&j_mpr, &imp_mono_r(&chain, ab)?)?;

    // `n ∈ m`: swap the guard, absorb leftward.
    let swap = hyp_and(&and_right(m_om.clone(), n_om.clone()), &and_left(m_om, n_om))?;
    let j_mpr_swapped = hyp_iff_mpr(&syl(&swap, &inst_all(sub_iff, &[tn.clone(), tm.clone()])?)?)?;
    let inj_c = or_intro_left(c_f.clone(), Formula::eq(tn.clone(), tm.clone()));
    let j_c_sub = com12(&syl(&inj_c, &com12(&j_mpr_swapped)?)?)?;
    let chain_c = syl(&inst_all(absorb_left, &[tm, tn])?, &or_intro_left(e1, e2))?;
    let case_c = syl(&j_c_sub, &imp_mono_r(&chain_c, c_f.clone())?)?;

    // Assemble over the trichotomy disjunction.
    let case_a = com12(&syl(&or_intro_left(a_f.clone(), b_f.clone()), &com12(&case_ab)?)?)?;
    let case_b = com12(&syl(&or_intro_right(a_f, b_f.clone()), &com12(&case_ab)?)?)?;
    let bc = Formula::or(b_f, c_f);
    let h_goal = hyp_or_elim(
        &and_right(j.clone(), bc.clone()),
        &syl(&and_left(j.clone(), bc.clone()), &case_b)?,
        &syl(&and_left(j.clone(), bc), &case_c)?,
    )?;
    let j_goal = hyp_or_elim(&tri_at, &case_a, &uncurry(&h_goal)?)?;
    let out = gen_all(&[m, n], &j_goal);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(j, goal))),
        "max_absorb: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∪ n) ∈ ω)` — `ω` is closed under `max`.
///
/// Immediate from [`max_absorb`]: whichever side the union is, that side's
/// membership in `ω` transports along the equation.
fn max_in_omega(env: &mut Env, core: &OmegaCore, sets: &Sets, max_absorb: &Thm) -> Option<Thm> {
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = core.set();
    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w.clone());
    let j = Formula::and(m_om.clone(), n_om.clone());
    let bu = bin_union(sets, tm.clone(), tn.clone());

    let absorb_at = inst_all(max_absorb, &[tm.clone(), tn.clone()])?;

    let hole = env.fresh_var();
    let leib_m = Thm::eq_leibniz(tm.clone(), bu.clone(), hole, Formula::mem(Term::var(hole), w.clone()));
    let pre_m = syl(&eq_symm_imp(env, bu.clone(), tm), &leib_m)?;
    let case_m = syl(&and_left(m_om.clone(), n_om.clone()), &com12(&pre_m)?)?;

    let hole2 = env.fresh_var();
    let leib_n = Thm::eq_leibniz(tn.clone(), bu.clone(), hole2, Formula::mem(Term::var(hole2), w.clone()));
    let pre_n = syl(&eq_symm_imp(env, bu.clone(), tn), &leib_n)?;
    let case_n = syl(&and_right(m_om, n_om), &com12(&pre_n)?)?;

    let j_goal = hyp_or_elim(&absorb_at, &case_m, &case_n)?;
    let out = gen_all(&[m, n], &j_goal);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(j, Formula::mem(bu, w)))),
        "max_in_omega: unexpected shape"
    );
    Some(out)
}
