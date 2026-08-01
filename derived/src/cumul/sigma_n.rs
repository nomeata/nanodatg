//! **`⊢ [H →] Aᵢ ∈ Uₙ` at a telescope of *any* depth** — the constructor
//! summand `Σy₀:β₀. Σy₁:β₁(y₀). … Σy_{k-1}:β_{k-1}(y⃗). 1` inside a universe,
//! by induction on telescope depth, **at any rung of the tower**.
//!
//! # Interface
//!
//! Fix a declaration, a constructor index `ci`, and write `k` for that
//! constructor's number of non-recursive arguments, `p⃗` for the declaration's
//! parameters, `Cᵢ` for [`crate::sigma::Telescope`]'s `i`-th level (so
//! `C₀(p⃗) = Aᵢ` is the summand and `C_k ≡ 1`), `Uₙ` for the [`Rung`] the caller
//! hands in, and
//!
//! ```text
//! Hⱼ   := yⱼ ∈ βⱼ(p⃗, y₀ … y_{j-1})
//! D₀   := H                      (the caller's optional antecedent, or nothing)
//! Dⱼ₊₁ := Dⱼ ∧ Hⱼ                (just Hⱼ when Dⱼ is absent)
//! ```
//!
//! Then
//!
//! ```text
//! given, for each j < k:
//!   ⊢ ∀y₀ … ∀y_{j-1}. (Dⱼ → βⱼ(p⃗, y₀ … y_{j-1}) ∈ Uₙ)     [arg_obligations_at()[j]]
//! ⊢ [H →] Aᵢ ∈ Uₙ                                            [summand_at]
//! ```
//!
//! [`arg_obligations_at`] hands the caller the `k` conclusions it must supply,
//! as formulas, so that they are built once and compared rather than guessed;
//! [`summand_at`] checks each supplied theorem against them **and** checks that
//! its hypothesis set is empty. [`arg_obligations`] and [`summand_in_u1`] are
//! the `n = 1` instances, one line each, so an existing caller changes nothing
//! and pays nothing.
//!
//! At `k = 1` the single obligation is `⊢ [H →] β₀(p⃗) ∈ Uₙ` — `D₀` is `H` and
//! there is no `∀` — which is exactly [`super::sigma::unary_summand_at`]'s
//! input, and `k = 0` degenerates to no obligation at all. Neither of those two
//! is routed through this file by anything that exists today: they keep their
//! own, cheaper derivations ([`super::sigma`], [`super::tags`]), and
//! `derived/tests/cumul_sigma_n.rs` pins that the answers agree on the nose.
//!
//! # Which rung to run at, and why there is only one entry point
//!
//! Running the induction at rung `n` costs **exactly** what running it at rung
//! 1 costs: every lemma it spends is a `∀c` statement
//! ([`crate::universe::least_universe_replacement_n`],
//! [`crate::cantor::image_in_universe`], the rung's own closure clauses)
//! instantiated at `rung.seed`, and a seed is a seed. What is *not* free is
//! running it **twice** for one declaration: each outer telescope level calls
//! [`crate::ext::image_symbol_n`], which mints a **fresh function symbol and a
//! fresh Replacement axiom instance** in the `Env`. Two runs of a `k`-field
//! constructor therefore leave `k−1` redundant symbols in the signature — not
//! merely duplicated work.
//!
//! Moving a *finished* membership up is free by comparison:
//! [`crate::tower::Cumul::raise`] is one `inst_all` and one `mp`, and mints
//! nothing. So the rule is
//!
//! > run this pipeline **exactly once**, at
//! > `n₀ := max(1, max over the fields of the rung that field's type lives in)`,
//! > and [`crate::tower::Cumul::raise`] the finished `A ∈ U_{n₀}` to whatever
//! > rung the declaration is placed at.
//!
//! A field membership available *below* `n₀` is raised individually first,
//! which is again one `mp`. For a declaration all of whose fields are small,
//! `n₀ = 1` and this is the old behaviour on the nose.
//!
//! That is why there is **one** generalised entry point rather than a `U₁` one
//! and a target-rung one: two entry points would offer only the binary choice
//! "`U₁`" versus "the rung the declaration is placed at", and the decision is
//! actually over `n₀`, which in general is neither. `Prod.{1,0}` (fields
//! `α ∈ U₂`, `β ∈ U₁`) has `n₀ = 2` while it may be placed at any rung ≥ 2, and
//! a field whose type is `Type 0` — i.e. the value `U₁`, whose membership
//! `U₁ ∈ U₂` is [`crate::tower::Rung::mem_below`] — cannot produce its
//! obligation at `U₁` at all, because raising only goes upward and there is
//! nothing to lower.
//!
//! # Why an induction, and where the `k = 1` argument survives inside it
//!
//! [`super::sigma`]'s header states the reduction this rests on, and it is
//! general at every `k`:
//!
//! ```text
//! Cᵢ(p⃗,y⃗) ∈ Uₙ   ⇐   βᵢ(p⃗,y⃗) ∈ Uₙ   and   imgᵢ(p⃗,y⃗) ∈ Uₙ
//! ```
//!
//! because [`crate::sigma::dsum`](fn@crate::sigma::dsum) carves `Cᵢ` out of
//! `βᵢ × ⋃imgᵢ` by Separation. What is not general is the second input, and the
//! two ways of supplying it split by *level*, not by `k`:
//!
//! * at the **innermost** `Σ`, `i = k-1`, the fibre is `C_k`, which `base_ax`
//!   says is the constant `1`. So `img_{k-1} ⊆ {1}` and `C₂` finishes with no
//!   Replacement instance. This is [`super::sigma::unary_image_is_a_point`]'s
//!   argument restated at the level's own argument list, and at `k = 1` it is
//!   the *whole* derivation — the `k = 1` fast path is not a special case this
//!   file replaces, it is this file's base level;
//! * at every **outer** level `i < k-1` the fibre `C_{i+1}(p⃗,y⃗,yᵢ)` genuinely
//!   varies with `yᵢ`, `imgᵢ` is a real Replacement image, and
//!   [`crate::universe::least_universe_replacement_n`] discharges it. That
//!   lemma's premise `∀x ∈ βᵢ. C_{i+1}(p⃗,y⃗,x) ∈ Uₙ` **is** the induction
//!   hypothesis, generalised over `yᵢ`; supplying it is the whole content of
//!   the induction.
//!
//! So the induction runs from level `k` downwards, and the Replacement lemma is
//! used `max(k-1, 0)` times per constructor.
//!
//! # One companion symbol per Replacement instance, and why
//!
//! [`crate::universe::least_universe_replacement_n`] is stated about the image
//! symbol [`crate::ext::image_symbol_n`] builds, which takes the *base set* as
//! its last argument: `img'(q⃗,A)`, arity `k+1`.
//! [`crate::sigma::dsum`](fn@crate::sigma::dsum)'s image bakes the base set in —
//! `imgᵢ(p⃗,y⃗) = { C_{i+1}(p⃗,y⃗,x) : x ∈ βᵢ(p⃗,y⃗) }`, arity `np+i` — so the
//! lemma cannot simply be instantiated at it, and this is the one place where
//! the composition is not immediate. The file therefore introduces one
//! arity-`np+i+1` companion image per outer level, proves Replacement about
//! *it*, and transfers by
//!
//! ```text
//! ⊢ imgᵢ(p⃗,y⃗) ⊆ img'(p⃗,y⃗, βᵢ(p⃗,y⃗))
//! ```
//!
//! plus `C₂`. That inclusion is one syllogism between the two defining axioms —
//! their existential bodies are the *same formula*, bound variables being de
//! Bruijn — so no extensionality is needed to relate the two sets, and no
//! second Replacement is spent on the transfer.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::ext::image_symbol_n`] per outer level, which is one Replacement
//! each, plus the theorems [`crate::sigma::dsum`](fn@crate::sigma::dsum) and
//! [`crate::sigma::Telescope`] already proved. No new axiom, and every
//! caller-supplied theorem is pinned on both its conclusion and its (empty)
//! hypothesis set.
//!
//! # Cost
//!
//! Each outer level pays one [`crate::cantor::image_in_universe`], which is the
//! longest derivation in [`crate::cantor`]. The count is per *level*, not per
//! declaration, and nothing is shared between levels because the fibre symbol
//! `C_{i+1}` differs at each: a `k`-field structure costs `k-1` of them.
//!
//! The count does **not** depend on the rung — but it is paid again, in full
//! and with fresh symbols, by every additional run. See the interface section
//! for the rule that follows.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::ext::image_symbol_n;
use crate::inductive::{Inductive, Machine};
use crate::sigma::Telescope;
use crate::sums::Sums;
use crate::tower::Rung;
use crate::universe::{fibres_in_n, least_universe_replacement_n, universe_replacement_n};
use crate::{
    all_unconditional, and_left, and_right, establishes, exists_elim_imp, iff_mp, iff_mpr,
    inst_all, singleton, syl, uncurry,
};

use super::apparatus::IndChain;
use super::opt::Ctx;

/// The pieces of one constructor's telescope this file reads, once the
/// structural checks have passed.
struct Levels<'a> {
    tel: &'a Telescope,
    /// The declaration's parameters, as terms.
    ps: Vec<Term>,
    /// `k` fresh telescope variables — the `y⃗` every statement below is stated
    /// at and generalised over.
    zs: Vec<FreeVar>,
}

impl Levels<'_> {
    /// The number of non-recursive arguments.
    fn k(&self) -> usize { self.tel.betas.len() }

    /// The argument list of level `i`: `p⃗, y₀ … y_{i-1}`.
    fn args(&self, i: usize) -> Vec<Term> {
        let mut a = self.ps.clone();
        a.extend(self.zs[..i].iter().map(|v| Term::var(*v)));
        a
    }

    /// `Cᵢ(p⃗, y₀ … y_{i-1})`.
    fn level(&self, i: usize) -> Term { Term::apply(self.tel.levels[i], self.args(i)) }

    /// `βᵢ(p⃗, y₀ … y_{i-1})`.
    fn beta(&self, i: usize) -> Term { Term::apply(self.tel.betas[i], self.args(i)) }

    /// `imgᵢ(p⃗, y₀ … y_{i-1})`, the image
    /// [`crate::sigma::dsum`](fn@crate::sigma::dsum) built.
    fn img(&self, i: usize) -> Term { Term::apply(self.tel.sums[i].img, self.args(i)) }

    /// `Hᵢ := yᵢ ∈ βᵢ(p⃗, y₀ … y_{i-1})`.
    fn guard(&self, i: usize) -> Formula {
        Formula::mem(Term::var(self.zs[i]), self.beta(i))
    }

    /// `D₀ … D_k`, the antecedent in force at each level.
    fn antecedents(&self, hyp: Option<&Formula>) -> Vec<Option<Formula>> {
        let mut out = vec![hyp.cloned()];
        for i in 0..self.k() {
            let next = match &out[i] {
                Some(d) => Formula::and(d.clone(), self.guard(i)),
                None => self.guard(i),
            };
            out.push(Some(next));
        }
        out
    }
}

/// `∀x₀ … ∀x_{n-1}. φ`, as a formula.
fn quantify(xs: &[FreeVar], phi: Formula) -> Formula {
    xs.iter().rev().fold(phi, |acc, x| Formula::forall(*x, acc))
}

/// From `⊢ D → φ` infer `⊢ D → ∀v. φ`, for `v` not free in `D`.
fn hyp_gen(v: FreeVar, t: &Thm) -> Option<Thm> {
    let (h, phi) = t.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h, phi)?, &Thm::gen(v, t))
}

/// The structural checks, and the telescope if they pass.
///
/// Every one of them is true by [`crate::sigma::Telescope::new`]'s
/// construction; none is assumed. The level/fibre/domain identifications in
/// particular are what make the recursion below speak about the same nest of
/// `Σ`s the summand actually is, rather than about some other telescope of the
/// same depth.
fn levels<'a>(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &'a Inductive,
    ci: usize,
) -> Option<Levels<'a>> {
    if !ic.is_over(mach) || !ind.is_over(mach) || ci >= ind.summands.len() {
        return None
    }
    let tel: &Telescope = &ind.telescopes[ci];
    let k = tel.betas.len();
    if ind.spec.ctors[ci].args.len() != k || tel.levels.len() != k + 1 || tel.sums.len() != k {
        return None
    }
    for (i, d) in tel.sums.iter().enumerate() {
        if d.sigma != tel.levels[i] || d.fib != tel.levels[i + 1] || d.dom != tel.betas[i] {
            return None
        }
    }
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    if Term::apply(tel.levels[0], ps.clone()) != ind.summands[ci] {
        return None
    }
    let zs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    Some(Levels { tel, ps, zs })
}

/// The handed-in [`Rung`] really is a rung of **this chain's own** tower, and
/// every field this file spends is a `⊢` with nothing on the left.
///
/// The same shape of check [`super::decl::DeclUniverse::over_at`] makes, on
/// *statements* rather than on symbols, and over the fields this file reads and
/// no others:
///
/// * `Uₙ` is this chain's `U(·)` applied to the rung's **own seed**. A `Rung`
///   from a second [`crate::tower::Tower`] in the same `Env` fails here — its
///   `set` is the *other* `U(·)` of something — and so does a `Rung` whose
///   `set` and `seed` have drifted apart. This is also the identification
///   [`replacement_at`] relies on when it instantiates
///   [`crate::universe::least_universe_replacement_n`] at `rung.seed`.
/// * `⊢ ∅ ∈ Uₙ` is about *this* [`Sums`]' `∅`, not about some other empty set.
/// * the four closure schemas the induction spends — `sub` (`C₂`), `pairing`,
///   `union` and `product` — rest on nothing, so nothing rides into the
///   unconditional statement this file advertises.
fn rung_ok(ic: &IndChain, s: &Sums, rung: &Rung) -> bool {
    Term::apply(ic.chain.lu(), vec![rung.seed.clone()]) == rung.set
        && establishes(&rung.empty_mem, &Formula::mem(s.zero(), rung.set.clone()))
        && all_unconditional(&[&rung.sub, &rung.pairing, &rung.union, &rung.product])
}

/// The `k` conclusions [`summand_in_u1`] requires of its `args_in_u1`, in
/// order — `⊢ ∀y₀ … ∀y_{j-1}. (Dⱼ → βⱼ(p⃗, y⃗) ∈ U₁)` for each `j < k`.
///
/// [`arg_obligations_at`] at `ic.chain.u1`, and nothing else.
pub fn arg_obligations(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    ci: usize,
    hyp: Option<&Formula>,
) -> Option<Vec<Formula>> {
    arg_obligations_at(env, ic, mach, ind, ci, hyp, &ic.chain.u1)
}

/// The `k` conclusions [`summand_at`] requires of its `args_in_un`, in order —
/// `⊢ ∀y₀ … ∀y_{j-1}. (Dⱼ → βⱼ(p⃗, y⃗) ∈ Uₙ)` for each `j < k`, at **any** rung.
///
/// Exposed so that a caller builds the obligation it has to discharge from the
/// same code that checks it, rather than reconstructing the guard chain by
/// hand. The bound variables are de Bruijn, so a formula returned here is
/// *equal* to a correctly-shaped one the caller derived with its own variables,
/// not merely alpha-equivalent.
///
/// `None` in exactly the cases [`summand_at`] returns `None` for a declaration
/// it cannot read, plus the ones [`rung_ok`] rejects.
pub fn arg_obligations_at(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    ci: usize,
    hyp: Option<&Formula>,
    rung: &Rung,
) -> Option<Vec<Formula>> {
    if !ic.is_over(mach) || !rung_ok(ic, &mach.wt.sums, rung) {
        return None
    }
    let l = levels(env, ic, mach, ind, ci)?;
    Some(obligations(&l, rung, hyp))
}

/// [`arg_obligations_at`], once the telescope has been read.
fn obligations(l: &Levels<'_>, rung: &Rung, hyp: Option<&Formula>) -> Vec<Formula> {
    let ds = l.antecedents(hyp);
    let un = rung.set.clone();
    (0..l.k())
        .map(|j| {
            let goal = Formula::mem(l.beta(j), un.clone());
            quantify(&l.zs[..j], Ctx(ds[j].clone()).wrap(goal))
        })
        .collect()
}

/// **`⊢ [H →] Aᵢ ∈ U₁`** for a constructor with any number `k` of non-recursive
/// arguments, given the `k` theorems [`arg_obligations`] describes.
///
/// [`summand_at`] at `ic.chain.u1`, and nothing else.
pub fn summand_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    ci: usize,
    hyp: Option<&Formula>,
    args_in_u1: &[Thm],
) -> Option<Thm> {
    summand_at(env, ic, mach, ind, ci, hyp, &ic.chain.u1, args_in_u1)
}

/// **`⊢ [H →] Aᵢ ∈ Uₙ`** for a constructor with any number `k` of non-recursive
/// arguments, at **any** rung, given the `k` theorems [`arg_obligations_at`]
/// describes.
///
/// The induction on telescope depth: see the module header for the statement,
/// and for which levels pay a Replacement instance. Each `args_in_un[j]` is
/// checked for its conclusion **and** for an empty hypothesis set, and every
/// theorem this reads out of the telescope is compared against one rebuilt
/// here, so a theorem from a different apparatus is refused rather than
/// silently used.
///
/// Running at rung `n` costs exactly what running at rung 1 costs — every
/// lemma the induction spends is a `∀c` statement instantiated at `rung.seed`.
/// What is *not* free is running it **twice** for one declaration; see the
/// module header for the rule that follows.
///
/// `None` when `ci` is out of range, when `args_in_un` has the wrong length or
/// any of its entries the wrong shape, when `mach` is not `ind`'s apparatus and
/// `ic`'s signature, or when `rung` is not a rung of this chain's own tower
/// ([`rung_ok`]).
#[allow(clippy::too_many_arguments)]
pub fn summand_at(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    ci: usize,
    hyp: Option<&Formula>,
    rung: &Rung,
    args_in_un: &[Thm],
) -> Option<Thm> {
    let l = levels(env, ic, mach, ind, ci)?;
    let k = l.k();
    if args_in_un.len() != k {
        return None
    }
    let ds = l.antecedents(hyp);
    let s = &mach.wt.sums;
    // `Uₙ` really is this chain's `U(seed)`, which is what the Replacement
    // lemma below is instantiated to produce, and the four closure schemas rest
    // on nothing.
    if !rung_ok(ic, s, rung) {
        return None
    }

    // Each argument's smallness, checked and then pinned at this file's own
    // telescope variables.
    let want = obligations(&l, rung, hyp);
    let mut betas: Vec<Thm> = Vec::with_capacity(k);
    for (j, th) in args_in_un.iter().enumerate() {
        if !th.hyps().is_empty() || *th.concl() != want[j] {
            return None
        }
        let zs: Vec<Term> = l.zs[..j].iter().map(|v| Term::var(*v)).collect();
        betas.push(inst_all(th, &zs)?);
    }

    // ── The base level: `C_k(p⃗,y⃗) = 1`, and `1 ∈ Uₙ` ───────────────────────
    let unit_in = one_in(rung, s)?;
    let base_at = inst_all(&l.tel.base_ax, &l.args(k))?;
    if *base_at.concl() != Formula::eq(l.level(k), s.unit()) {
        return None
    }
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        s.unit(),
        l.level(k),
        hole,
        Formula::mem(Term::var(hole), rung.set.clone()),
    );
    let mut cur = Ctx(ds[k].clone())
        .lift(&Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, &base_at)?)?, &unit_in)?);

    // ── and down the nest, one `Σ` at a time ────────────────────────────────
    let sing = singleton(s.ap.sets.up, s.unit());
    for i in (0..k).rev() {
        let ctx = Ctx(ds[i].clone());
        let img_in = if i + 1 == k {
            // The innermost fibre is the constant `1`; no Replacement.
            let sub = image_is_a_point(env, &l, s, i)?;
            let sing_in = ctx.lift(&singleton_in(rung, s, &unit_in)?);
            sub_in_rung(&ctx, rung, &sing_in, &sub, l.img(i), sing.clone())?
        } else {
            // The induction hypothesis, generalised over `yᵢ`, is exactly the
            // Replacement lemma's fibre condition.
            let fibres = if ds[i].is_some() {
                hyp_gen(l.zs[i], &uncurry(&cur)?)?
            } else {
                Thm::gen(l.zs[i], &cur)
            };
            let cond = fibres_in_n(env, l.tel.levels[i + 1], &l.args(i), &l.beta(i), &rung.set);
            if *fibres.concl() != ctx.wrap(cond.clone()) {
                return None
            }
            replacement_at(env, ic, rung, &l, &ctx, i, &betas[i], &fibres, &cond)?
        };
        cur = sigma_step(env, rung, mach, &l, &ctx, i, &betas[i], &img_in)?;
    }

    let out = cur;
    (out.hyps().is_empty()
        && *out.concl() == Ctx(hyp.cloned()).wrap(Formula::mem(l.level(0), rung.set.clone())))
    .then_some(out)
}

/// `⊢ 1 ∈ Uₙ` — `1 = {0,0}`, so one pairing over `⊢ ∅ ∈ Uₙ`.
fn one_in(rung: &Rung, s: &Sums) -> Option<Thm> {
    let out = Thm::mp(
        &inst_all(&rung.pairing, &[s.zero(), s.zero()])?,
        &crate::and_intro(&rung.empty_mem, &rung.empty_mem),
    )?;
    (*out.concl() == Formula::mem(s.unit(), rung.set.clone())).then_some(out)
}

/// `⊢ {1} ∈ Uₙ`.
fn singleton_in(rung: &Rung, s: &Sums, one_in: &Thm) -> Option<Thm> {
    let out = Thm::mp(
        &inst_all(&rung.pairing, &[s.unit(), s.unit()])?,
        &crate::and_intro(one_in, one_in),
    )?;
    (*out.concl() == Formula::mem(singleton(s.ap.sets.up, s.unit()), rung.set.clone()))
        .then_some(out)
}

/// `C₂` at `Uₙ`, carried under the optional antecedent: from `⊢ [D →] big ∈ Uₙ`
/// and `⊢ small ⊆ big` infer `⊢ [D →] small ∈ Uₙ`.
fn sub_in_rung(
    ctx: &Ctx,
    rung: &Rung,
    big_in: &Thm,
    sub: &Thm,
    small: Term,
    big: Term,
) -> Option<Thm> {
    let all_z = ctx.mp(&ctx.lift(&inst_all(&rung.sub, std::slice::from_ref(&big))?), big_in)?;
    ctx.mp(&ctx.inst(&all_z, small)?, &ctx.lift(sub))
}

/// `⊢ imgᵢ(p⃗,y⃗) ⊆ {1}` — the **innermost** level's image is a point.
///
/// [`super::sigma::unary_image_is_a_point`]'s argument at level `i = k-1` and
/// at that level's own argument list: `base_ax` says the fibre `C_k` is the
/// constant `1`, so every member of the image *is* `1`. One `∃`-elimination
/// and one Leibniz step, and no Replacement instance — which is the whole
/// reason the base level is free.
fn image_is_a_point(env: &mut Env, l: &Levels<'_>, s: &Sums, i: usize) -> Option<Thm> {
    let up = s.ap.sets.up;
    let (wv, xv) = (env.fresh_var(), env.fresh_var());
    let (tw, tx) = (Term::var(wv), Term::var(xv));

    let mut fib_args = l.args(i);
    fib_args.push(tx.clone());
    let fib_x = Term::apply(l.tel.levels[i + 1], fib_args.clone());

    let mut img_args = l.args(i);
    img_args.push(tw.clone());
    let img_at_w = inst_all(&l.tel.sums[i].img_ax, &img_args)?;

    let base_x = inst_all(&l.tel.base_ax, &fib_args)?;
    if *base_x.concl() != Formula::eq(fib_x.clone(), s.unit()) {
        return None
    }

    let hole = env.fresh_var();
    let to_one = Thm::mp(
        &Thm::eq_leibniz(fib_x.clone(), s.unit(), hole, Formula::eq(tw.clone(), Term::var(hole))),
        &base_x,
    )?;
    let into_sing = iff_mpr(&inst_all(&s.ap.mem_sing, &[s.unit(), tw.clone()])?)?;
    let in_sing = Formula::mem(tw.clone(), singleton(up, s.unit()));
    let case = syl(
        &and_right(Formula::mem(tx.clone(), l.beta(i)), Formula::eq(tw.clone(), fib_x)),
        &syl(&to_one, &into_sing)?,
    )?;
    let from_ex = exists_elim_imp(xv, &Thm::gen(xv, &case), &in_sing)?;
    let out = Thm::gen(wv, &syl(&iff_mp(&img_at_w)?, &from_ex)?);

    (out.hyps().is_empty()
        && *out.concl() == kernel::thm::subset(env, l.img(i), singleton(up, s.unit())))
    .then_some(out)
}

/// `⊢ [D →] imgᵢ(p⃗,y⃗) ∈ Uₙ` at an **outer** level, by Replacement.
///
/// One [`crate::ext::image_symbol_n`] introduces a companion image
/// `img'(q⃗,A) = { C_{i+1}(q⃗,x) : x ∈ A }` that carries the base set as an
/// argument, [`crate::universe::least_universe_replacement_n`] puts
/// `img'(p⃗y⃗, βᵢ)` into `Uₙ` from the fibre condition, and
/// `imgᵢ ⊆ img'(p⃗y⃗, βᵢ)` transfers that to the image the `Σ` was actually
/// built over, by `C₂`. See the module header for why the transfer is needed.
///
/// The rung enters in exactly one place: `least_universe_replacement_n` is
/// `⊢ ∀q⃗ ∀c ∀A. …`, and `rung.seed` is what goes in for `c`. So an outer level
/// costs the same at every rung — but it does mint a symbol, and that is what
/// makes running the pipeline twice for one declaration expensive.
#[allow(clippy::too_many_arguments)]
fn replacement_at(
    env: &mut Env,
    ic: &IndChain,
    rung: &Rung,
    l: &Levels<'_>,
    ctx: &Ctx,
    i: usize,
    beta_in: &Thm,
    fibres: &Thm,
    cond: &Formula,
) -> Option<Thm> {
    let b = l.tel.levels[i + 1];
    let (imgn, imgn_ax) = image_symbol_n(env, b)?;
    let ur = universe_replacement_n(env, &ic.chain.space.empty_ax, imgn, &imgn_ax, b)?;
    let lur =
        least_universe_replacement_n(env, ic.chain.lu(), &ic.chain.space.lu_ax, imgn, b, &ur)?;

    let beta_at = l.beta(i);
    let mut inst = l.args(i);
    inst.push(rung.seed.clone());
    inst.push(beta_at.clone());
    let rule = inst_all(&lur, &inst)?;

    let mut imgn_args = l.args(i);
    imgn_args.push(beta_at.clone());
    let imgn_at = Term::apply(imgn, imgn_args);
    if *rule.concl()
        != Formula::imp(
            Formula::and(Formula::mem(beta_at.clone(), rung.set.clone()), cond.clone()),
            Formula::mem(imgn_at.clone(), rung.set.clone()),
        )
    {
        return None
    }
    let imgn_in = ctx.mp(&ctx.lift(&rule), &ctx.and(beta_in, fibres)?)?;

    // `imgᵢ(p⃗,y⃗) ⊆ img'(p⃗,y⃗, βᵢ(p⃗,y⃗))`, unconditionally: the two defining
    // axioms have the same existential body.
    let wv = env.fresh_var();
    let tw = Term::var(wv);
    let mut a1 = l.args(i);
    a1.push(tw.clone());
    let fwd = iff_mp(&inst_all(&l.tel.sums[i].img_ax, &a1)?)?;
    let mut a2 = l.args(i);
    a2.push(beta_at);
    a2.push(tw);
    let bwd = iff_mpr(&inst_all(&imgn_ax, &a2)?)?;
    let sub = Thm::gen(wv, &syl(&fwd, &bwd)?);
    if *sub.concl() != kernel::thm::subset(env, l.img(i), imgn_at.clone()) {
        return None
    }
    sub_in_rung(ctx, rung, &imgn_in, &sub, l.img(i), imgn_at)
}

/// `⊢ [D →] Cᵢ(p⃗,y⃗) ∈ Uₙ` from `⊢ [D →] βᵢ ∈ Uₙ` and `⊢ [D →] imgᵢ ∈ Uₙ`.
///
/// The reduction [`super::sigma`]'s header states and
/// [`super::sigma::unary_summand_at`] performs at `i = 0`, `k = 1`: `Uₙ`'s
/// union and product closures put the Separation's carrier `βᵢ × ⋃imgᵢ` into
/// `Uₙ`, the defining axiom's forward half says `Cᵢ` is a subset of it, and
/// `C₂` finishes. Nothing here depends on the level or on the rung, which is
/// what "the reduction is general at every `k`" means concretely.
#[allow(clippy::too_many_arguments)]
fn sigma_step(
    env: &mut Env,
    rung: &Rung,
    mach: &Machine,
    l: &Levels<'_>,
    ctx: &Ctx,
    i: usize,
    beta_in: &Thm,
    img_in: &Thm,
) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let proj = &mach.proj;

    let beta_at = l.beta(i);
    let img_at = l.img(i);
    let uimg = ap.sets.union_of(img_at.clone());
    let prod_at = s.prod.of(beta_at.clone(), uimg.clone());
    let sigma_at = l.level(i);

    let uimg_in =
        ctx.mp(&ctx.lift(&inst_all(&rung.union, std::slice::from_ref(&img_at))?), img_in)?;
    let prod_in = ctx.mp(
        &ctx.lift(&inst_all(&rung.product, &[beta_at, uimg])?),
        &ctx.and(beta_in, &uimg_in)?,
    )?;

    // `Cᵢ(p⃗,y⃗) ⊆ βᵢ × ⋃imgᵢ`, read off the Separation.
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let mut sig_args = l.args(i);
    sig_args.push(tq.clone());
    let sig_at = inst_all(&l.tel.sums[i].sigma_ax, &sig_args)?;
    let psi = Formula::mem(proj.snd_of(ap, tq.clone()), {
        let mut a = l.args(i);
        a.push(proj.fst_of(ap, tq.clone()));
        Term::apply(l.tel.levels[i + 1], a)
    });
    let in_prod = Formula::mem(tq.clone(), prod_at.clone());
    let fwd = iff_mp(&sig_at)?;
    if *fwd.concl()
        != Formula::imp(
            Formula::mem(tq.clone(), sigma_at.clone()),
            Formula::and(in_prod.clone(), psi.clone()),
        )
    {
        return None
    }
    let sigma_sub = Thm::gen(qv, &syl(&fwd, &and_left(in_prod, psi))?);
    if *sigma_sub.concl() != kernel::thm::subset(env, sigma_at.clone(), prod_at.clone()) {
        return None
    }
    let out = sub_in_rung(ctx, rung, &prod_in, &sigma_sub, sigma_at.clone(), prod_at)?;
    (*out.concl() == ctx.wrap(Formula::mem(sigma_at, rung.set.clone()))).then_some(out)
}
