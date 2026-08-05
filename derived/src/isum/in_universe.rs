//! **`⊢ ∀c. finord(m) ∈ U(c)`** — the finite-ordinal fibre lives in every
//! universe, which is the carrier-side half of what
//! [`crate::cumul::bnd_finord`] does for the tower.
//!
//! # Interface
//!
//! Writing `Σ(m)` for `finord(m) = Sum_m(1,…,1)`:
//!
//! ```text
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a + b) ∈ U(c))     [SumClosure::sum]
//! ⊢ ∀c. ∅ ∈ U(c)                                            [SumClosure::empty]
//! ⊢ ∀c. 1 ∈ U(c)                                            [SumClosure::unit]
//! ⊢ ∀c. Σ(m) ∈ U(c)                                         [finord_in_universe]
//! ⊢ Sum_m(A⃗) ∈ U(c)   from  ⊢ Aⱼ ∈ U(c)                     [isum_in_universe]
//! ⊢ H → Sum_m(A⃗) ∈ U(c)  from  ⊢ H → Aⱼ ∈ U(c)              [isum_in_universe_under]
//! ```
//!
//! The last two are the export; neither has a **sequent hypothesis** and
//! neither has a side condition on `c`, for each concrete `m`. The optional
//! `H` of the second is carried in the *conclusion*, which is the discipline
//! [`crate::ctx`] states and the reason a parameterised declaration's placement
//! can still generalise over its parameters at the end. [`finords_in_universe`] is the same at a whole
//! declaration's recursive-argument counts, shaped exactly like
//! [`crate::cumul::bnd_finords`] so that the two are called the same way.
//!
//! [`isum_in_universe_under`] is the **general** form and the one a constructor
//! with a function-typed recursive argument needs: its fibre summand is
//! `Σ(z::γⱼ)` rather than `1`, so the value is an iterated sum of sets no arity
//! can name — and when `γⱼ` is one of the declaration's *parameters* the
//! summand's membership exists only under that parameter's typing, which is
//! what the optional `H` carries. `isum_in_universe` is that at `H` absent and
//! `finord_in_universe` is that at `Aⱼ := 1` with [`SumClosure::unit`]
//! supplying every input; all three share one fold — see [`one`].
//!
//! [`SumClosure`] is the apparatus the two share — the sum-closure lemma and
//! the two base memberships, derived **once** rather than per constructor. It
//! plays the role `Rec`/`Stages` play for `bnd_finords`.
//!
//! # Why this is nearly free, and where the one real step is
//!
//! `finord(m)` *is* an iterated binary sum, and [`crate::sums::sum_in_universe`]
//! is exactly closure under the binary one, so the induction on `m` is a fold:
//!
//! ```text
//! ∅ ∈ U(c)                                                   the base, `1 + (… + 0)`'s tail
//! 1 ∈ U(c)                                                   pairing at `{∅,∅}`
//! (1 ∈ U(c) ∧ tail ∈ U(c)) → (1 + tail) ∈ U(c)               sum_in_universe, m times
//! ```
//!
//! `1 ∈ U(c)` is not an extra assumption: `1` **is** `{∅}`, so one use of the
//! caller's pairing closure at `∅` supplies it — the same step
//! [`crate::sums::sum_in_universe`] already performs internally on the tags. The
//! only genuine input beyond the four closure lemmas is therefore `∅ ∈ U(c)`,
//! for the reason that file's header gives: it is not a closure property at all.
//!
//! **The one step that is not free is the unfolding.** The fold above proves
//! membership of the *nest* [`super::tags::isum_of`] builds, and `finord(m)` as
//! consumers know it is [`super::symbols::ISumSyms::finord`], the **symbol**
//! `Sum_m(1,…,1)`. The two are connected by
//! [`ISumSyms::sum_ax`](super::symbols::ISumSyms::sum_ax) and by nothing else,
//! so one Leibniz step at the end moves the membership onto the symbol. That
//! matters most at `m = 0`, where the nest is the term `∅` and `Sum_0()` is a
//! symbol that is not syntactically `∅` — without the unfolding the statement
//! there would be about the wrong term.
//!
//! Everything indexed by `m` happens in Rust, as in [`crate::cumul::finord`]:
//! `m` is a `usize` the translation knows at translation time, so there is no
//! induction in the object language and none is done.
//!
//! # What it is *not* needed for, today
//!
//! [`crate::inductive::carrier`] does **not** consume this. Its header records
//! `finord(m) ∈ U(A)` as the obstacle to seeding the bound at `c := A`, and it
//! sidesteps that by seeding at `c := {A, T}` instead, where transitivity of
//! `U(c)` discharges everything with no case analysis on the tag. This file
//! removes the obstacle rather than the workaround: a consumer that wants the
//! *tight* seed `c := A`, or that wants a fibre's universe membership without
//! carrying `T` around, can now have it. The workaround stays where it is.
//!
//! # Non-vacuity
//!
//! `Σ(m) ∈ U(c)` would be just as true of an empty `Σ(m)`, and `U(c)` is not a
//! set everything belongs to only because
//! [`crate::tower::Tower::no_self_mem`] says so. `tests/isum.rs` pins both: at
//! `m = 3` the three points `Inj_0(•)`, `Inj_1(•)`, `Inj_2(•)` are provably
//! members of `Σ(3)` and provably pairwise distinct
//! ([`ISumSyms::inj_distinct`](super::symbols::ISumSyms::inj_distinct)), so the
//! set placed in `U(c)` has at least three elements and has not collapsed; and
//! `U(ω) ∉ U(ω)`, so the ambient universe is not everything.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced and no theorem is assumed. Every ingredient is a
//! caller-supplied closure lemma, each of which is **checked at the terms this
//! file uses before it is used** and rejected — rather than described as proved
//! — if it does not fit. All four are additionally required to be
//! hypothesis-free, and so is every caller-supplied `mems[j]`: a theorem
//! carrying `Γ` would compose through `mp` with `Γ` intact and arrive at the
//! conclusion this module advertises without one, and `Thm::gen` over `c` — or,
//! at a declaration, over its parameters — would then generalise a variable a
//! hypothesis may mention. An optional `H` is *not* an exception to that: it
//! lives in the conclusion, where a comparison can see it.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::ctx::Ctx;
use crate::sums::{sum_in_universe, Sums};
use crate::{and_intro, eq_symm, gen_all, inst_all, singleton};

use super::symbols::ISumSyms;
use super::tags::isum_of;

/// Which [`Sums`] a [`SumClosure`] was built over: the `sum` symbol and the
/// pairing, which between them fix every term below.
///
/// The same identity [`ISumSyms`] records, and for the same reason — two
/// `Sums` in one `Env` are two different `+`, and a closure lemma about one
/// says nothing about the other's nests.
type Family = (FnSym, FnSym);

/// **The sum-closure apparatus**: `U(c)`'s closure under `+`, and the two base
/// memberships `∅ ∈ U(c)` and `1 ∈ U(c)`, derived once.
///
/// A declaration with `n` constructors needs `n` finite-ordinal fibres and the
/// three theorems here do not depend on the arity; re-deriving them per
/// constructor is the only thing that would make [`finords_in_universe`]
/// quadratic in the declaration. This is the same split
/// [`crate::cumul::bnd_finords`] makes over [`crate::cumul::finite`]'s three
/// lemmas.
pub struct SumClosure {
    family: Family,
    /// The universe operator `U(·)`, of arity 1.
    pub lu: FnSym,
    /// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a + b) ∈ U(c))`.
    pub sum: Thm,
    /// `⊢ ∀c. ∅ ∈ U(c)`.
    pub empty: Thm,
    /// `⊢ ∀c. 1 ∈ U(c)` — because `1` is `{∅}` and pairing is closed.
    pub unit: Thm,
}

impl SumClosure {
    /// Derive the three theorems from the caller's universe closure lemmas.
    ///
    /// `lu` is the universe operator and the four arguments are its closure
    /// properties, in the shape [`crate::tower::Tower`] stores them:
    ///
    /// ```text
    /// empty_in    ⊢ ∀c. ∅ ∈ U(c)
    /// pairing     ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))
    /// product     ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c))
    /// bin_union   ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))
    /// ```
    ///
    /// `None` when `lu` is not unary, when any of the four **carries a
    /// hypothesis**, when one of them is not about `s`'s operators at the terms
    /// used here, or when `1` is not `{∅}` over this `s` — every one of which
    /// is checked rather than assumed.
    pub fn new(
        env: &mut Env,
        s: &Sums,
        lu: FnSym,
        empty_in: &Thm,
        pairing: &Thm,
        product: &Thm,
        bin_union: &Thm,
    ) -> Option<SumClosure> {
        if lu.arity() != 1 {
            return None
        }
        // A hypothetical input composes through `mp` with `Γ` intact, and the
        // `Thm::gen` below would then bind a variable `Γ` may mention.
        if [empty_in, pairing, product, bin_union].iter().any(|t| !t.hyps().is_empty()) {
            return None
        }
        let up = s.ap.sets.up;
        let (zero, one) = (s.zero(), s.unit());
        // The whole derivation reads `1 ∈ U(c)` off the pairing closure, which
        // is only the unit type's membership if `1` really is `{∅}`.
        if one != singleton(up, zero.clone()) {
            return None
        }

        let sum = sum_in_universe(env, s, lu, empty_in, pairing, product, bin_union)?;

        let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
        let w = Term::apply(lu, vec![tc.clone()]);

        // `sum_in_universe` checks its own ingredients but pins its conclusion
        // only under `debug_assertions`; rebuild it here and insist.
        let want = Formula::forall(
            cv,
            Formula::forall(
                av,
                Formula::forall(
                    bv,
                    Formula::imp(
                        Formula::and(
                            Formula::mem(ta.clone(), w.clone()),
                            Formula::mem(tb.clone(), w.clone()),
                        ),
                        Formula::mem(s.sum_of(ta, tb), w.clone()),
                    ),
                ),
            ),
        );
        if !sum.hyps().is_empty() || *sum.concl() != want {
            return None
        }

        // ── `∅ ∈ U(c)`, and `1 = {∅}` above it ──────────────────────────────
        let z_at = inst_all(empty_in, std::slice::from_ref(&tc))?;
        let mem_z = Formula::mem(zero, w.clone());
        if *z_at.concl() != mem_z {
            return None
        }
        let pair_at = inst_all(pairing, &[tc, s.zero(), s.zero()])?;
        if *pair_at.concl()
            != Formula::imp(
                Formula::and(mem_z.clone(), mem_z),
                Formula::mem(one, w),
            )
        {
            return None
        }
        let one_at = Thm::mp(&pair_at, &and_intro(&z_at, &z_at))?;

        Some(SumClosure {
            family: (s.sum, up),
            lu,
            sum,
            empty: Thm::gen(cv, &z_at),
            unit: Thm::gen(cv, &one_at),
        })
    }

    /// Whether this apparatus was built over `s`.
    ///
    /// Every entry point taking a `&Sums` refuses when this is `false`: the
    /// closure lemma is a statement about *that* family's `+`, and a nest built
    /// out of another family's would not be the term it speaks about.
    pub fn is_over(&self, s: &Sums) -> bool { self.family == (s.sum, s.ap.sets.up) }
}

/// **`⊢ Sum_m(A⃗) ∈ U(c)`** — an iterated sum of summands that are themselves
/// in `U(c)`.
///
/// The general form of [`finord_in_universe`], and the one a constructor with a
/// **function-typed** recursive argument needs: §5.2's recursive-argument rule
/// gives such a slot the fibre summand `Σ(z::γⱼ)` rather than `1`
/// (`thesis.txt:1800`), so the value is `Sum_m(A⃗)` at summands no arity can
/// name.
///
/// `mems[j]` must be `⊢ Aⱼ ∈ U(c)` at `summands[j]` and at *this* `c`,
/// unconditional and with an empty hypothesis set; all three are checked. The
/// seed `c` is a **term** here rather than a generalised variable, because a
/// caller with a real summand has its membership at the rung it is placing the
/// declaration in and not `∀c`; [`finords_in_universe`] recovers the `∀c` form
/// by passing a fresh variable and generalising.
///
/// [`isum_in_universe_under`] is this under an optional antecedent; this is
/// that at `hyp = None`, and the two share one fold.
pub fn isum_in_universe(
    env: &mut Env,
    clo: &SumClosure,
    s: &Sums,
    syms: &ISumSyms,
    c: &Term,
    summands: &[Term],
    mems: &[Thm],
) -> Option<Thm> {
    isum_in_universe_under(env, clo, s, syms, c, None, summands, mems)
}

/// **`⊢ [H →] Sum_m(A⃗) ∈ U(c)`** — [`isum_in_universe`] under an optional
/// antecedent.
///
/// `mems[j]` must be `⊢ Aⱼ ∈ U(c)` when `hyp` is `None` and `⊢ H → Aⱼ ∈ U(c)`
/// when it is `Some(H)`, at `summands[j]` and at *this* `c`. The **empty
/// hypothesis set** is required either way and is checked: a `Γ ⊢` has the
/// conclusion the real theorem has, composes through `mp` with `Γ` intact, and
/// would arrive at a statement this module advertises without one. `H` is
/// carried in the *conclusion* for the reason [`crate::ctx`] gives — a caller
/// generalising over a declaration's parameters cannot do so past a `Γ` that
/// mentions them.
///
/// # Why the antecedent had to reach this far in
///
/// A Lean declaration is always closed, so a **parameterised** one's placement
/// theorem is `⊢ ∀p⃗. (H → ind(p⃗) ∈ Uₙ)` with `H` the conjunction of the
/// parameters' own typings. A constructor whose recursive argument's domain is
/// one of those parameters — `Tree α | node : (α → Tree α) → Tree α` — has the
/// fibre summand `Aⱼ = Σ(z::α)`, and `Aⱼ ∈ Uₙ` is then available under `H` and
/// under nothing weaker: `Tree α` for an `α` that is not small has no W-type in
/// `Uₙ` at all, so the antecedent is the statement's content rather than a
/// convenience. Requiring an unconditional `mems[j]` here was what refused that
/// declaration, one construction after the summand's membership had already
/// been derived.
///
/// **The mixed case is the ordinary one and costs nothing extra.** At `np ≥ 1`
/// a constructor may sum a summand that needs `H` beside one that does not
/// (`node : (B2 → T α) → (α → T α) → T α`); the caller states *every* row at
/// `ctx.under(…)`, lifting the unconditional ones, so the fold below sees one
/// uniform shape and no per-summand case analysis exists to get wrong.
#[allow(clippy::too_many_arguments)]
pub fn isum_in_universe_under(
    env: &mut Env,
    clo: &SumClosure,
    s: &Sums,
    syms: &ISumSyms,
    c: &Term,
    hyp: Option<&Formula>,
    summands: &[Term],
    mems: &[Thm],
) -> Option<Thm> {
    if !clo.is_over(s) || !syms.is_over(s) || summands.len() != mems.len() {
        return None
    }
    let ctx = Ctx(hyp.cloned());
    let w = Term::apply(clo.lu, vec![c.clone()]);
    let z_in = inst_all(&clo.empty, std::slice::from_ref(c))?;
    if *z_in.concl() != Formula::mem(s.zero(), w.clone()) {
        return None
    }
    for (j, m) in mems.iter().enumerate() {
        if !m.hyps().is_empty()
            || *m.concl() != ctx.under(Formula::mem(summands[j].clone(), w.clone()))
        {
            return None
        }
    }
    general(env, clo, s, syms, &ctx, c, summands, mems, &z_in, &w)
}

/// The fold and the unfolding, over inputs the two entry points have already
/// checked.
///
/// `z_in` is unconditional at every caller — `∅ ∈ U(c)` is a fact about the
/// universe and never about a declaration's parameters — so the fold lifts it
/// into `ctx` rather than asking for it there.
#[allow(clippy::too_many_arguments)]
fn general(
    env: &mut Env,
    clo: &SumClosure,
    s: &Sums,
    syms: &ISumSyms,
    ctx: &Ctx,
    c: &Term,
    summands: &[Term],
    mems: &[Thm],
    z_in: &Thm,
    w: &Term,
) -> Option<Thm> {
    let m = summands.len();
    let mut acc = ctx.lift(z_in);
    for j in (0..m).rev() {
        let tail = isum_of(s, &summands[j + 1..]);
        let at = inst_all(&clo.sum, &[c.clone(), summands[j].clone(), tail.clone()])?;
        let want = Formula::imp(
            Formula::and(
                Formula::mem(summands[j].clone(), w.clone()),
                Formula::mem(tail.clone(), w.clone()),
            ),
            Formula::mem(s.sum_of(summands[j].clone(), tail), w.clone()),
        );
        if *at.concl() != want {
            return None
        }
        acc = ctx.mp(&ctx.lift(&at), &ctx.and(&mems[j], &acc)?)?;
    }
    let nest = isum_of(s, summands);
    if *acc.concl() != ctx.under(Formula::mem(nest.clone(), w.clone())) {
        return None
    }

    // ── the nest becomes the symbol `Sum_m(A⃗)` ──────────────────────────────
    let sigma = syms.sum(summands)?;
    let ax = inst_all(syms.sum_ax(m)?, summands)?;
    if *ax.concl() != Formula::eq(sigma.clone(), nest.clone()) {
        return None
    }
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(nest, sigma.clone(), hole, Formula::mem(Term::var(hole), w.clone()));
    let out = ctx.syl(&acc, &Thm::mp(&leib, &eq_symm(env, &ax)?)?)?;

    (out.hyps().is_empty() && *out.concl() == ctx.under(Formula::mem(sigma, w.clone())))
        .then_some(out)
}

/// **`⊢ ∀c. finord(m) ∈ U(c)`** — the fibre a constructor with `m` recursive
/// arguments gets is a member of every universe.
///
/// `syms` must have been [`ISumSyms::ensure`]d to arity `m` over `s`, and `clo`
/// must have been built over the same `s`. Unconditional and generic in the
/// seed `c`, for each concrete `m` — including `m = 0`, where `finord(0)` is
/// the *symbol* `Sum_0()` and not the term `∅`, so the unfolding at the end is
/// doing work even there.
pub fn finord_in_universe(
    env: &mut Env,
    clo: &SumClosure,
    s: &Sums,
    syms: &ISumSyms,
    m: usize,
) -> Option<Thm> {
    Some(finords_in_universe(env, clo, s, syms, std::slice::from_ref(&m))?.remove(0))
}

/// [`finord_in_universe`] at every arity a declaration uses.
///
/// `counts[i]` is the `i`-th constructor's recursive-argument count, exactly as
/// [`crate::fibre::Fibre::new`] and [`crate::cumul::bnd_finords`] take it. The
/// two base memberships and the sum-closure lemma already sit on `clo`, so the
/// per-constructor cost here is `m` implications and one unfolding.
pub fn finords_in_universe(
    env: &mut Env,
    clo: &SumClosure,
    s: &Sums,
    syms: &ISumSyms,
    counts: &[usize],
) -> Option<Vec<Thm>> {
    if !clo.is_over(s) || !syms.is_over(s) {
        return None
    }
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let w = Term::apply(clo.lu, vec![tc.clone()]);

    let z_in = inst_all(&clo.empty, std::slice::from_ref(&tc))?;
    let one_in = inst_all(&clo.unit, std::slice::from_ref(&tc))?;
    if *z_in.concl() != Formula::mem(s.zero(), w.clone())
        || *one_in.concl() != Formula::mem(s.unit(), w.clone())
    {
        return None
    }

    counts
        .iter()
        .map(|&m| one(env, clo, s, syms, m, cv, &w, &z_in, &one_in))
        .collect()
}

/// One arity, over base memberships the caller already has.
///
/// The unit summand repeated `m` times, handed to [`general`] — so the `∀c`
/// entry point and the general one share **one** fold and one unfolding rather
/// than two spellings of the same induction. `cv` is the variable `w` — and
/// hence both memberships — is stated at; it is generalised at the end.
#[allow(clippy::too_many_arguments)]
fn one(
    env: &mut Env,
    clo: &SumClosure,
    s: &Sums,
    syms: &ISumSyms,
    m: usize,
    cv: kernel::FreeVar,
    w: &Term,
    z_in: &Thm,
    one_in: &Thm,
) -> Option<Thm> {
    let tc = Term::var(cv);
    let summands = vec![s.unit(); m];
    let mems = vec![one_in.clone(); m];
    let at = general(env, clo, s, syms, &Ctx(None), &tc, &summands, &mems, z_in, w)?;
    let out = gen_all(&[cv], &at);

    let sigma = syms.finord(s, m)?;
    let expected = Formula::forall(cv, Formula::mem(sigma, w.clone()));
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}
