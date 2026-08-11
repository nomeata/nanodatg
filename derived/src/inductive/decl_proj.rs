//! **A projection out of a class-(T) structure, typed at an arbitrary carrier
//! element** — and the structure η rule that falls out of the same induction.
//!
//! # The fourth member of the ladder family
//!
//! [`super::family::le_prop_fields`], [`super::family::trunc_fields`] and
//! [`super::decl_fields`] all say "the fields are inhabited by the point",
//! differing only in which carrier supplies the major premise. This one is
//! their sibling at a **data** field, where the projection is a real term
//! rather than `•`, and the difference from [`super::decl_fields`] is exactly
//! one thing: **`φ` mentions `z`.**
//!
//! | module | `φ(z)` |
//! |---|---|
//! | [`super::decl_fields`] | `(⋀ⱼ Pⱼ → ⋀ⱼ Hⱼ)` — constant in `z` |
//! | **here** | `⋀ⱼ (πⱼ(z) ∈ βⱼ(p⃗, π⃗<ⱼ z))  ∧  (ctor₀(π⃗ z) = z)` |
//!
//! # The term is not the hard half
//!
//! Every layer of a class-(T) carrier element is a Kuratowski pair — `sup(a,f)`
//! **is** `⟨a,f⟩`, `Inj₀(x)` unfolds to `⟨∅,x⟩`, and
//! [`Telescope::tuple_of`](crate::sigma::Telescope::tuple_of) is a right-nested
//! chain — so
//!
//! ```text
//! πⱼ(z)  :=  compⱼ( π₂( π₁ z ) )  =  π₁(π₂ʲ(π₂(π₁ z)))       [proj_of]
//! ```
//!
//! reaches field `j` in `j + 3` projections, and `⊢ πⱼ(ctor₀(y⃗)) = yⱼ` is that
//! many instantiations of [`Proj::fst`]/[`Proj::snd`], unconditional. That rule
//! is [`computes`], and it lives **here**, beside the spine it is about.
//!
//! *This paragraph used to say "that rule is an argument here, not a
//! derivation", and named `mini`'s `proj_data::computes` as its owner. That was
//! right while `mini` was the only consumer; it stopped being right when
//! [`super::degen`] — which is in this crate and has no `mini` to ask — needed
//! the same equation. Two spellings in shipped code is what the sentence was
//! guarding against, so the derivation moved down rather than being copied up,
//! and `mini::proj_data::computes` now delegates.*
//!
//! [`DeclProj::over_declaration`] still takes the `k` rules as **arguments**
//! and still pins every one of them against [`proj_of`]. That is not vestigial:
//! [`DeclProj::build`] is the one-call entry that derives them with [`computes`]
//! and hands them over, and the pin is what keeps a caller who builds its own
//! — `derived/tests/decl_proj.rs` does, deliberately, so that a drift between
//! the two chains is a test failure rather than a silent agreement — from being
//! spoken for.
//!
//! **`π₂(π₁ z)`, not `π₁(π₁ z)`**, and the distinction survives no test with
//! fewer than three fields: `π₁(π₁ z)` is the *tag* `∅`, and at `k ≤ 2` an
//! off-by-one in either the `π₂(π₁ ·)` prefix or the `π₂ʲ` walk lands on a
//! component that happens to agree. The tests pin three.
//!
//! # Interface
//!
//! With `p⃗` the declaration's parameter variables and `z` the major premise:
//!
//! ```text
//! πⱼ(z)                                                          [proj_of]
//! ⊢ πⱼ(ctor₀(y⃗)) = yⱼ                                            [computes]
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → πⱼ(z) ∈ βⱼ(p⃗, π₀ z, …, π_{j-1} z) )  [DeclProj::typed]
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → ctor₀(π₀ z, …, π_{k-1} z) = z )        [DeclProj::eta]
//! ```
//!
//! All three unconditional; [`DeclProj::build`] is the whole bundle in one
//! call. `typed` is empty at `k = 0`; `eta` is **not** — at a fieldless
//! structure it says the carrier's one element is `ctor₀()`, which is true and
//! cheap.
//!
//! [`computes`] is stated at the caller's own `y⃗` and mentions **no
//! parameter**: `ctor₀(y⃗)` is `⟨Inj₀(tuple y⃗), f()⟩`, and at a declaration with
//! no recursive field none of those three layers takes `p⃗`. That is what lets
//! [`super::degen`] state a parameter-free ι rule.
//!
//! # η, and why it is here rather than on `rect`'s result
//!
//! [`super::rect`]'s own proof assembles `ctorᵢ(π⃗) = ⟨a,f⟩` as a local
//! (`k_eq`) and drops it — `MINI-HANDOFF.md` §2's discarded-evidence pattern at
//! its fifth position. It is **not** exportable from there: it is stated at the
//! existential witnesses `a`, `f` and `σᵢ` under the case analysis's own
//! context, and surfacing it means discharging those, which is re-running the
//! case analysis with η as the goal — which is precisely [`decl_rect`] at a `φ`
//! that mentions `z`. So the export costs nothing *here* (one more conjunct in
//! a `φ` this file already builds) and would cost the whole traversal there.
//!
//! Fen's test settles the placement: **does the consumer want it at the same
//! terms?** `105_structEta` wants `Prod.mk (fst x) (snd x) = x` at its own `x`,
//! which a `∀z` theorem gives by instantiation; `rect`'s local is at witnesses
//! no consumer can name. Storing it there would have stored the wrong terms.
//!
//! # One Separation for `k + 1` theorems
//!
//! `φ` is the conjunction of the `k` typings **and** η, so a single
//! [`crate::wtype::w_rect`] Separation covers all of them and [`conj_proj`]
//! reads them back. [`super::decl_fields`] uses the same trick on its ladder,
//! and for the same reason: the conjuncts are independent statements about one
//! induction, not stages of one statement.
//!
//! The single induction step is `∀y⃗. (⋀_q y_q ∈ β_q(p⃗,y⃗<q) → φ(ctor₀(y⃗)))`,
//! and each conjunct of `φ(ctor₀(y⃗))` is reached by rewriting with the supplied
//! computation rules: conjunct `j` of the antecedent after `j + 1` rewrites for
//! the `j`-th typing, and reflexivity after `k` for η.
//!
//! # Scope
//!
//! One constructor, no recursive field. At two constructors the statement is
//! **false** rather than merely unproved: `π₂(π₁ z)` is the packed tuple only
//! under `Inj₀`, and an element built by the second constructor has
//! `Inj₁(x) = ⟨{∅}, x⟩` there. The σ question answers "the same" — `Prod.fst`'s
//! field sort is a *successor*, `Sort (u+1)`, which by `SCOPING.md` §9's
//! sort-expression table never splits, unlike
//! [`super::decl_fields`]'s bare-parameter row.
//!
//! Neither refusal has a guard, and **which check owns which was instrumented,
//! not inferred** — the first draft of this paragraph named the wrong one:
//!
//! | input | first refuser |
//! |---|---|
//! | a computation rule about another spine | the [`crate::establishes`] against [`proj_of`] |
//! | two constructors | `parts.len() != 1` |
//! | a recursive field | [`Inductive::ctor_term`] returning `None` |
//!
//! The last is not the `rect_parts` comparison, which is what I assumed and
//! wrote before measuring. A recursive declaration's constructor term takes
//! `m` recursive arguments; this file builds `ctor₀(y⃗)` with **none**, because
//! that is the term the computation rules are about, so the shape a caller
//! would have to supply cannot be formed and the refusal happens before
//! anything is derived.
//!
//! [`super::family::trunc_fields`]'s header sets out why the measurement is
//! necessary and a mutation script is not sufficient: deleting any one of these
//! alone also fails no test, because the survivors plus the downstream
//! [`Thm::mp`] catch whatever the deleted one would have. An over-determined
//! net where each check owns one input is not a redundant layer.
//!
//! # Nothing here is an axiom
//!
//! One [`decl_rect`] — one Separation, for all `k + 1` theorems — and then
//! Leibniz steps only: `k(k+3)/2` of them, `j + 1` per typing and `k` for η.
//! [`computes`] adds no Separation at all: `j + 3` instantiations of the two
//! projection rules and the injection's defining equation, chained.
//!
//! [`Proj::fst`]: crate::proj::Proj
//! [`Proj::snd`]: crate::proj::Proj

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::err::{DResult, Operand};
use crate::funcs::Apply;
use crate::prim::Shape;
use crate::proj::Proj;
use crate::recarg::RecArg;
use crate::sigma::Telescope;
use crate::{assembly, conj_of, conj_proj, decline, eq_symm, establishes, gen_all, inst_all, syl};

use super::carrier::Inductive;
use super::machine::Machine;
use super::rec_shared::{hyp_conj, rewrite_under, under};
use super::rect::{decl_rect, rect_parts};

/// **`πⱼ(z) = compⱼ(π₂(π₁ z))`** — the `j`-th field read straight out of a
/// class-(T) carrier element.
///
/// The one spelling of the projection spine. A consumer builds it at its own
/// subject with this, and [`DeclProj::over_declaration`] compares every
/// computation rule it is handed against it, so the term in a checker and the
/// term in these theorems cannot be two different terms.
///
/// `π₁ z` is the tag-and-payload pair, `π₂` of that drops the `Inj₀` tag `∅`,
/// and `compⱼ` walks `j` steps down the packed tuple. Reading `π₁(π₁ z)`
/// instead lands on the tag itself, and no declaration with fewer than three
/// fields distinguishes the two.
pub fn proj_of(ap: &Apply, proj: &Proj, j: usize, z: Term) -> Term {
    Telescope::comp_of(ap, proj, j, proj.snd_of(ap, proj.fst_of(ap, z)))
}

/// `⊢ g(a) = g(b)` from `⊢ a = b`, for a term-former given as a closure.
///
/// [`crate::congr_arg`] does this for one argument of one `FnSym`; `π₁` and
/// `π₂` are *composites* (`π₁ p = ⋃⋂p`, `π₂ p = app({p}, π₁ p)`, and the second
/// mentions `p` twice), so a per-symbol congruence would need three steps and
/// the two occurrences would have to move together. One Leibniz over the hole
/// does both.
fn congr_of(env: &mut Env, g: &dyn Fn(Term) -> Term, ab: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().eq_parts()?;
    let x = env.fresh_var();
    let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(g(a.clone()), g(Term::var(x))));
    crate::prim::mp(&crate::prim::mp(&leib, ab)?, &Thm::eq_refl(g(a)))
}

/// **`⊢ πⱼ(ctor₀(y⃗)) = yⱼ`** — the projection spine's computation rule at the
/// declaration's own constructor, at caller-supplied field terms.
///
/// The one derivation of it; [`DeclProj::build`] and [`super::degen`] are its
/// consumers inside this crate, `mini::proj_data::computes` outside it.
///
/// ```text
/// π₁ ⟨Inj₀(tuple), f()⟩  = Inj₀(tuple)     Proj::fst
/// Inj₀(tuple)            = ⟨∅, tuple⟩      ISumSyms::inj_ax at depth 0
/// π₂ ⟨∅, tuple⟩          = tuple           Proj::snd      ← the `π₂(π₁ ·)`
/// π₂ ⟨y_q, rest⟩         = rest            Proj::snd, q < j
/// π₁ ⟨y_j, rest⟩         = y_j             Proj::fst
/// ```
///
/// **Unconditional, and free of `p⃗`** — every layer above is a literal
/// Kuratowski pair, so nothing here needs `z ∈ ind(p⃗)`, no Separation is
/// minted, and the parameters do not appear. That is what [`super::degen`]
/// spends.
///
/// Declines for a declaration without exactly one constructor, for `j` out of
/// range, and — through [`Inductive::ctor_term`] — for one whose constructor
/// takes a recursive argument: this states a rule about `ctor₀(y⃗)` with no
/// recursive arguments at all, which at `m > 0` is not a constructor
/// application and cannot be formed.
///
/// The conclusion is checked against `proj_of` and `yⱼ` on the nose, so a chain
/// that walked into the wrong component is an error and never an equation about
/// the wrong field.
pub fn computes(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    j: usize,
    ys: &[Term],
) -> DResult<Thm> {
    if ind.spec.ctors.len() != 1 {
        return Err(decline!("decl_proj::computes: not a one-constructor declaration"))
    }
    if j >= ys.len() {
        return Err(decline!("decl_proj::computes: the field index is out of range"))
    }
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let Some(ctor) = ind.ctor_term(mach, 0, ys, &[]) else {
        return Err(decline!(
            "decl_proj::computes: no fieldwise constructor term — a recursive field, a foreign \
             apparatus, or the wrong field count"
        ))
    };
    let tuple = Telescope::tuple_of(s, ys);
    let Some(tag) = mach.syms.inj(0, tuple.clone()) else {
        return Err(decline!("decl_proj::computes: this apparatus has no Inj₀"))
    };
    let recf = RecArg::of(s, &mach.cases, &[]);

    // ── the tag, out of the outer pair ──────────────────────────────────────
    let e_tag = crate::rules::inst_all(&mach.proj.fst, &[tag.clone(), recf])?;
    let want_tag = Formula::eq(mach.proj.fst_of(ap, ctor.clone()), tag.clone());
    if !establishes(&e_tag, &want_tag) {
        return Err(assembly!(
            "decl_proj::computes: π₁(ctor₀(y⃗)) is not the tag",
            Operand::thm("e_tag", &e_tag),
            Operand::formula("want", &want_tag),
        ))
    }

    // ── the payload, out of the tag: unfold `Inj₀`, then `π₂` ───────────────
    let Some(inj_ax) = mach.syms.inj_ax(0) else {
        return Err(decline!("decl_proj::computes: this apparatus has no Inj₀ defining equation"))
    };
    let unfold = crate::rules::inst_all(inj_ax, std::slice::from_ref(&tuple))?;
    let (_, inl) = unfold.concl().eq_parts()?;
    if inl != s.inl(tuple.clone()) {
        return Err(assembly!(
            "decl_proj::computes: Inj₀(x) did not unfold to inl(x) = ⟨∅,x⟩",
            Operand::thm("unfold", &unfold),
        ))
    }
    let snd = |t: Term| mach.proj.snd_of(ap, t);
    let e_pay = {
        let a = congr_of(env, &snd, &e_tag)?;
        let b = congr_of(env, &snd, &unfold)?;
        let via = crate::rules::eq_trans(env, &a, &b)?;
        let step = crate::rules::inst_all(&mach.proj.snd, &[s.zero(), tuple.clone()])?;
        crate::rules::eq_trans(env, &via, &step)?
    };

    // ── down the telescope: `j` tails, then one head ────────────────────────
    let mut cur = e_pay;
    for q in 0..j {
        let rest = Telescope::tuple_of(s, &ys[q + 1..]);
        let step = crate::rules::inst_all(&mach.proj.snd, &[ys[q].clone(), rest])?;
        let lift = congr_of(env, &snd, &cur)?;
        cur = crate::rules::eq_trans(env, &lift, &step)?;
    }
    let fst = |t: Term| mach.proj.fst_of(ap, t);
    let head = crate::rules::inst_all(
        &mach.proj.fst,
        &[ys[j].clone(), Telescope::tuple_of(s, &ys[j + 1..])],
    )?;
    let lift = congr_of(env, &fst, &cur)?;
    let out = crate::rules::eq_trans(env, &lift, &head)?;

    let want = Formula::eq(proj_of(ap, &mach.proj, j, ctor), ys[j].clone());
    if !establishes(&out, &want) {
        return Err(assembly!(
            "decl_proj::computes: the chain did not land on πⱼ(ctor₀(y⃗)) = yⱼ",
            Operand::thm("out", &out),
            Operand::formula("want", &want),
        ))
    }
    Ok(out)
}

/// A class-(T) structure's projections, typed, and its η rule.
pub struct DeclProj {
    /// The major-premise variable `z`, bound by the second `∀` of both
    /// theorems. Exported so a consumer can rebuild what it instantiates.
    pub major: FreeVar,
    /// `πⱼ(z)` at [`DeclProj::major`], one per field in declared order.
    pub proj: Vec<Term>,
    /// `⊢ ∀p⃗ ∀z. (z ∈ ind(p⃗) → πⱼ(z) ∈ βⱼ(p⃗, π₀ z, …, π_{j-1} z))`, one per
    /// field. Empty at `k = 0`.
    pub typed: Vec<Thm>,
    /// **`⊢ ∀p⃗ ∀z. (z ∈ ind(p⃗) → ctor₀(π₀ z, …, π_{k-1} z) = z)`** — the
    /// structure η rule, which [`super::rect`] assembles internally and drops.
    pub eta: Thm,
}

impl DeclProj {
    /// **The whole bundle in one call**: mint the `k` field variables, derive
    /// the `k` computation rules with [`computes`], and hand them to
    /// [`DeclProj::over_declaration`].
    ///
    /// The rules and the theorems are then about the *same* variables by
    /// construction rather than by check, which is the property a caller
    /// assembling the two halves itself has to arrange by hand.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call, so build this
    /// once per declaration and cache it.
    pub fn build(env: &mut Env, mach: &Machine, ind: &Inductive) -> DResult<DeclProj> {
        let Some(c) = ind.spec.ctors.first() else {
            return Err(decline!("DeclProj::build: a declaration with no constructors"))
        };
        if ind.spec.ctors.len() != 1 {
            return Err(decline!("DeclProj::build: not a one-constructor declaration"))
        }
        let k = c.args.len();
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let rules: Vec<Thm> =
            (0..k).map(|j| computes(env, mach, ind, j, &ys)).collect::<DResult<_>>()?;
        match DeclProj::over_declaration(env, mach, ind, &yvs, &rules) {
            Some(dp) => Ok(dp),
            None => Err(decline!("DeclProj::build: over_declaration refused this declaration")),
        }
    }

    /// Type the projections, and derive η, by one induction over the carrier.
    ///
    /// `yvs` are the caller's field variables and `computes[j]` must be
    /// `⊢ πⱼ(ctor₀(y⃗)) = yⱼ` at them, with `πⱼ` [`proj_of`]'s — **compared,
    /// not assumed**, which is what stops a consumer's projection term and
    /// this module's from drifting apart. Each must be unconditional: a
    /// hypothesis on one would ride into a conclusion documented `⊢`.
    ///
    /// `None` for a declaration without exactly one constructor, for one whose
    /// constructor has a recursive field, for a foreign apparatus, on a length
    /// mismatch, and on any internal shape check.
    ///
    /// One [`crate::wtype::w_rect`] Separation is minted per call, for all
    /// `k + 1` theorems, so build this once per declaration and cache it.
    pub fn over_declaration(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        yvs: &[FreeVar],
        computes: &[Thm],
    ) -> Option<DeclProj> {
        // The apparatus identity is the only guard: nothing below re-checks it.
        // The two refusals this module makes are statement comparisons, and the
        // header says which catches which.
        if !ind.is_over(mach) || ind.spec.ctors.is_empty() {
            return None
        }
        let c = &ind.spec.ctors[0];
        let k = c.args.len();
        if yvs.len() != k || computes.len() != k || !crate::all_unconditional(&[&ind.ty_ax]) {
            return None
        }
        if !crate::all_unconditional(&computes.iter().collect::<Vec<_>>()) {
            return None
        }

        let s = mach.wt.sums.clone();
        let ap = s.ap.clone();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();

        // ── the supplied computation rules, pinned against `proj_of` ────────
        let ctor = ind.ctor_term(mach, 0, &ys, &[])?;
        for (j, rule) in computes.iter().enumerate() {
            let want = Formula::eq(proj_of(&ap, &mach.proj, j, ctor.clone()), ys[j].clone());
            if !establishes(rule, &want) {
                return None
            }
        }

        // ── `φ(z)`: the `k` typings and η, conjoined ────────────────────────
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let pz: Vec<Term> = (0..k).map(|j| proj_of(&ap, &mach.proj, j, tz.clone())).collect();
        let atom_at = |subjs: &[Term], j: usize| -> Option<Formula> {
            let mut a = ps.clone();
            a.extend(subjs.get(..j)?.iter().cloned());
            Some(Formula::mem(subjs.get(j)?.clone(), Term::apply(c.args[j], a)))
        };
        let mut phis: Vec<Formula> =
            (0..k).map(|j| atom_at(&pz, j)).collect::<Option<_>>()?;
        phis.push(Formula::eq(ind.ctor_term(mach, 0, &pz, &[])?, tz.clone()));
        let phi = conj_of(&phis)?; // `k + 1 ≥ 1`, so never empty

        // ── the single induction step ───────────────────────────────────────
        let parts = rect_parts(env, mach, ind, zv, &phi)?;
        if parts.len() != 1 {
            return None
        }
        let ratoms: Vec<Formula> = (0..k).map(|j| atom_at(&ys, j)).collect::<Option<_>>()?;
        let hyp = conj_of(&ratoms);
        // `⊢ [H →] yᵢ = πᵢ(ctor₀(y⃗))`, the rules read backwards: the step's goal
        // is stated at the projections and its antecedent at the variables.
        let backs: Vec<Thm> = computes
            .iter()
            .map(|r| {
                let b = eq_symm(env, r)?;
                Some(match &hyp {
                    Some(h) => under(&b, h),
                    None => b,
                })
            })
            .collect::<Option<_>>()?;
        // `πᵢ(ctor₀(y⃗))`, the terms the step's conjuncts are actually about.
        let pc: Vec<Term> = (0..k).map(|j| proj_of(&ap, &mach.proj, j, ctor.clone())).collect();

        let mut conjs: Vec<Thm> = Vec::with_capacity(k + 1);
        for j in 0..k {
            // Start at conjunct `j` of the antecedent and walk `y` to `π(ctor)`
            // one position at a time — the `j` type arguments, then the
            // subject. `spine` records how far that has got, so the context
            // handed to Leibniz is the formula as it stands.
            let mut spine = ys.clone();
            let mut cur = match &hyp {
                Some(_) => conj_proj(&ratoms, j)?,
                None => return None, // `k > 0` here, so the antecedent exists
            };
            for i in 0..=j {
                let (pre, post) = (spine[..i].to_vec(), spine[i + 1..].to_vec());
                let (psc, sym) = (ps.clone(), c.args[j]);
                let subj_is_i = i == j;
                let spine_c = spine.clone();
                cur = rewrite_under(
                    env,
                    &backs[i],
                    move |t| {
                        let mut v = pre.clone();
                        v.push(t);
                        v.extend(post.iter().cloned());
                        let mut a = psc.clone();
                        a.extend(v[..j].iter().cloned());
                        let subj = if subj_is_i { v[j].clone() } else { spine_c[j].clone() };
                        Formula::mem(subj, Term::apply(sym, a))
                    },
                    &cur,
                )?;
                spine[i] = pc[i].clone();
            }
            if *cur.concl() != imp_opt(&hyp, atom_at(&pc, j)?) {
                return None
            }
            conjs.push(cur);
        }

        // η: reflexivity at the constructor, with each argument walked back.
        //
        // `ctor_term` cannot fail here — `is_over(mach)` is checked above and
        // the argument list is always `k` long — so the `expect` is the same
        // "one binder, one term" idiom `le.rs`'s `subst_all` uses.
        let mk = |v: &[Term]| {
            ind.ctor_term(mach, 0, v, &[]).expect("k plain fields over this machine")
        };
        let mut spine = ys.clone();
        let refl = Thm::eq_refl(ctor.clone());
        let mut cur = match &hyp {
            Some(h) => under(&refl, h),
            None => refl,
        };
        for i in 0..k {
            let (pre, post) = (spine[..i].to_vec(), spine[i + 1..].to_vec());
            let cc = ctor.clone();
            cur = rewrite_under(
                env,
                &backs[i],
                |t| {
                    let mut v = pre.clone();
                    v.push(t);
                    v.extend(post.iter().cloned());
                    Formula::eq(mk(&v), cc.clone())
                },
                &cur,
            )?;
            spine[i] = pc[i].clone();
        }
        if *cur.concl()
            != imp_opt(&hyp, Formula::eq(ind.ctor_term(mach, 0, &pc, &[])?, ctor.clone()))
        {
            return None
        }
        conjs.push(cur);

        let body = hyp_conj(&conjs).unwrap_or_else(|| conjs[0].clone());
        let step = gen_all(yvs, &body);
        if !establishes(&step, &parts[0]) {
            return None
        }

        // ── `⊢ ∀z. (z ∈ W → φ)`, then the carrier's own name for `W` ────────
        let all_w = Thm::mp(&decl_rect(env, mach, ind, zv, &phi)?, &step)?;
        let zv2 = env.fresh_var();
        let tz2 = Term::var(zv2);
        let at_z = inst_all(&all_w, std::slice::from_ref(&tz2))?;
        let to_w = inst_all(&ind.ty_ax, &ps)?;
        if *to_w.concl() != Formula::eq(ind.carrier.clone(), ind.wty.clone()) {
            return None
        }
        let hole = env.fresh_var();
        let phi_at2 = phi.subst(zv, &tz2);
        let at_ind = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    ind.wty.clone(),
                    ind.carrier.clone(),
                    hole,
                    Formula::imp(Formula::mem(tz2.clone(), Term::var(hole)), phi_at2.clone()),
                ),
                &eq_symm(env, &to_w)?,
            )?,
            &at_z,
        )?;

        // ── the conjuncts, read back ────────────────────────────────────────
        let mut quant = ind.params.clone();
        quant.push(zv2);
        let mem_z = Formula::mem(tz2.clone(), ind.carrier.clone());
        let parts2: Vec<Formula> = phis.iter().map(|f| f.subst(zv, &tz2)).collect();
        let out: Vec<Thm> = (0..=k)
            .map(|j| {
                let at = syl(&at_ind, &conj_proj(&parts2, j)?)?;
                establishes(&at, &Formula::imp(mem_z.clone(), parts2[j].clone()))
                    .then(|| gen_all(&quant, &at))
            })
            .collect::<Option<_>>()?;

        let dp = DeclProj {
            major: zv2,
            proj: (0..k).map(|j| proj_of(&ap, &mach.proj, j, tz2.clone())).collect(),
            typed: out[..k].to_vec(),
            eta: out[k].clone(),
        };
        crate::all_unconditional(
            &dp.typed.iter().chain(std::iter::once(&dp.eta)).collect::<Vec<_>>(),
        )
        .then_some(dp)
    }

    /// `πⱼ(z')` at a caller-supplied subject — [`proj_of`], with the field
    /// index range-checked against this declaration.
    ///
    /// A consumer holds its own `⟦s⟧` and instantiates
    /// [`DeclProj::typed`]`[j]` at it; this is the matching term, so the two
    /// come from one spelling.
    pub fn proj_at(&self, ap: &Apply, proj: &Proj, j: usize, z: Term) -> Option<Term> {
        (j < self.typed.len()).then(|| proj_of(ap, proj, j, z))
    }
}

/// `H → φ`, or bare `φ` when there is no antecedent.
fn imp_opt(hyp: &Option<Formula>, phi: Formula) -> Formula {
    match hyp {
        Some(h) => Formula::imp(h.clone(), phi),
        None => phi,
    }
}
