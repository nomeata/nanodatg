//! **`⊢ enum(A) ∈ U₁`** — the enumeration types in the first universe.
//!
//! # Interface
//!
//! Writing `enum(A)` for `W(A, ∅, U(A))` — [`crate::enums`]' reading of a Lean
//! inductive all of whose constructors take no arguments — and `U₁` for `U(ω)`:
//!
//! ```text
//! ⊢ 0 ∈ U₁                                         [zero_in_u1]
//! ⊢ 1 ∈ U₁                                         [unit_in_u1]
//! ⊢ enum(A) ∈ U₁     given ⊢ A ∈ U₁                [enum_in_u1]
//! ```
//!
//! all at **closed terms** and with no hypothesis, so `enum(0)` (Lean's
//! `Empty`), `enum(1)` (`Unit`) and `enum(1+1)` (`Bool`) are members of
//! `⟦Type 0⟧`. The `1+1` case needs `⊢ (1+1) ∈ U₁`, which is
//! [`super::NatMem::tags_in_u1`] — the same tag set, the same theorem.
//!
//! Non-vacuity comes from [`crate::enums`] at the same terms:
//! `⊢ ⟨inl •,∅⟩ ∈ enum(1+1)`, `⊢ ⟨inr •,∅⟩ ∈ enum(1+1)` and
//! `⊢ ¬(⟨inl •,∅⟩ = ⟨inr •,∅⟩)`, so the membership is not about a singleton.
//!
//! # Why this is shorter than [`super::witness`], not merely different
//!
//! [`super::WMem::w_in_universe`] asks for the same four things whatever the
//! W-type, and three of the four are *cheaper* here than for `N`:
//!
//! | obligation | for `N` | for `enum(A)` |
//! |---|---|---|
//! | `A ⊆ S` | `S = A ∪ 1`, so the left introduction of `∪` | `S = A`, so reflexivity |
//! | `∀a ∈ A. (B(a) ⊆ S ∧ B(a) ∈ ω)` | a case analysis on `a ∈ 1+1`, `sum_cases` + `unit_eta` + two `rec₊` rules | `B = ∅`, so `⊢ ∀a. app(∅,a) = ∅` and **no case analysis at all** |
//! | `S ∈ U(A)` | `A ∈ U(A)`, `∅ ∈ U(A)`, pairing, binary union | `A ∈ U(A)` |
//! | `S ∈ U₁` | `(1+1) ∈ U₁` and `1 ∈ U₁`, then binary union | the caller's `A ∈ U₁` |
//!
//! The seed can be `A` itself precisely because the fibres are empty: `Fin`'s
//! second clause is about `B(a)`, and `∅ ⊆ A` holds for every `A`. `N` cannot
//! do this — its `succ` fibre is `1`, which is not a subset of `1+1`.
//!
//! So the closing note of [`crate::cumul`] was right that the ω-tower is what
//! `W ∈ u` needs, and its remark that the enumerations were bounded "at their
//! own tag set" is about the *bound* `U(A)`, not about the universe they live
//! in. `enum(A) ∈ U(A)` is refutable for the same reason `N ∈ U(1+1)` is; this
//! is the membership that is not.

use kernel::{Env, Formula, Term, Thm};

use crate::{and_intro, a1i, ex_falso, eq_symm, inst_all, syl};

use super::chain::Chain;
use super::stages::subset_refl;

/// `⊢ 0 ∈ U₁` — the empty tag set, i.e. `Empty`'s.
pub fn zero_in_u1(c: &Chain) -> Thm { c.u1.empty_mem.clone() }

/// `⊢ 1 ∈ U₁` — the one-point tag set, i.e. `Unit`'s.
///
/// `1` is the term `{∅,∅}`, so this is `U₁`'s pairing closure at `a = b = ∅`
/// and nothing else. The guard checks that the term produced really is `1`,
/// since "the unordered pair of `∅` with itself" being the same term as "the
/// unit type" is a fact about how [`crate::sums`] builds them rather than
/// something this file may assume.
pub fn unit_in_u1(c: &Chain) -> Option<Thm> {
    let s = &c.wt.sums;
    let zero = s.zero();
    let out = Thm::mp(
        &inst_all(&c.u1.pairing, &[zero.clone(), zero])?,
        &and_intro(&c.u1.empty_mem, &c.u1.empty_mem),
    )?;
    (*out.concl() == Formula::mem(s.unit(), c.u1.set.clone())).then_some(out)
}

/// `⊢ enum(A) ∈ U₁`, given `⊢ A ∈ U₁`.
///
/// `tags_in_u1` must be exactly that, unconditionally: it is checked before it
/// is used, and the result is checked to be the membership claimed before it is
/// returned. A theorem about some other set — or one resting on an assumption —
/// yields `None`, not a weaker conclusion.
pub fn enum_in_u1(env: &mut Env, c: &Chain, tags: &Term, tags_in_u1: &Thm) -> Option<Thm> {
    let wt = &c.wt;
    let s = &wt.sums;
    let z = wt.empty();
    let om = c.r.omega();
    let u = Term::apply(c.lu(), vec![tags.clone()]);
    let ty = wt.of(tags.clone(), z.clone(), u);

    if !tags_in_u1.hyps().is_empty()
        || *tags_in_u1.concl() != Formula::mem(tags.clone(), c.u1.set.clone())
    {
        return None
    }
    // The seed is the tag set itself; everything below is stated at it.
    let seed = tags.clone();

    // ── `A ⊆ S` ─────────────────────────────────────────────────────────────
    let tags_sub = inst_all(&subset_refl(env)?, std::slice::from_ref(&seed))?;

    // ── `∅ ⊆ S ∧ ∅ ∈ ω` ─────────────────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let empty_sub = Thm::gen(
        zv,
        &syl(
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?,
            &ex_falso(Formula::mem(tz.clone(), seed.clone())),
        )?,
    );
    if *empty_sub.concl() != kernel::thm::subset(env, s.zero(), seed.clone()) {
        return None
    }
    let empty_ok = and_intro(&empty_sub, &c.r.core().zero_mem);

    // ── `∀a. (a ∈ A → (app(∅,a) ⊆ S ∧ app(∅,a) ∈ ω))` ───────────────────────
    //
    // No case analysis: the fibre is `app(∅,a)`, which `Wtype::app_empty` says
    // is `∅` for *every* `a`, so the one fact above is moved along that equation
    // and generalised.
    let (av, wv) = (env.fresh_var(), env.fresh_var());
    let ta = Term::var(av);
    let fibre = wt.fibre(z.clone(), ta.clone());
    let goal = Formula::and(
        kernel::thm::subset(env, fibre.clone(), seed.clone()),
        Formula::mem(fibre.clone(), om.clone()),
    );
    let app_empty_at = inst_all(&wt.app_empty, std::slice::from_ref(&ta))?;
    if *app_empty_at.concl() != Formula::eq(fibre.clone(), s.zero()) {
        return None
    }
    let move_goal = Thm::eq_leibniz(
        s.zero(),
        fibre.clone(),
        wv,
        Formula::and(
            kernel::thm::subset(env, Term::var(wv), seed.clone()),
            Formula::mem(Term::var(wv), om.clone()),
        ),
    );
    let at_a = Thm::mp(&Thm::mp(&move_goal, &eq_symm(env, &app_empty_at)?)?, &empty_ok)?;
    if *at_a.concl() != goal {
        return None
    }
    let all = Thm::gen(av, &a1i(&at_a, Formula::mem(ta, tags.clone())));
    let fin = and_intro(&tags_sub, &all);

    // ── `S ∈ U(A)`, and step (f) at the concrete seed ───────────────────────
    let mem_lu = crate::universe::mem_least_universe(env, c.lu(), &c.bound.lu_ax)?;
    let seed_in_bound = inst_all(&mem_lu, std::slice::from_ref(&seed))?;

    let at_seed = Thm::gen(c.st.seed, &c.wmem.w_in_universe);
    let at = inst_all(&at_seed, &[seed, tags.clone(), z, tags.clone(), om])?;
    let out = Thm::mp(
        &at,
        &and_intro(
            &and_intro(&fin, &seed_in_bound),
            &and_intro(tags_in_u1, &c.u1.omega_mem),
        ),
    )?;
    (out.hyps().is_empty() && *out.concl() == Formula::mem(ty, c.u1.set.clone())).then_some(out)
}
