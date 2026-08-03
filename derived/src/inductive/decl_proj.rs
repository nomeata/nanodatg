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
//! many instantiations of [`Proj::fst`]/[`Proj::snd`], unconditional. **That
//! rule is an argument here, not a derivation.** It is built and tested by the
//! consumer (`mini`'s `proj_data::computes`), and rebuilding it would be a
//! second spelling of one convention. What this module does own is
//! [`proj_of`] — the spine itself — and every supplied rule is compared against
//! it before anything is derived, so a consumer whose term disagrees is refused
//! rather than spoken for.
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
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → πⱼ(z) ∈ βⱼ(p⃗, π₀ z, …, π_{j-1} z) )  [DeclProj::typed]
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → ctor₀(π₀ z, …, π_{k-1} z) = z )        [DeclProj::eta]
//! ```
//!
//! Both unconditional. `typed` is empty at `k = 0`; `eta` is **not** — at a
//! fieldless structure it says the carrier's one element is `ctor₀()`, which is
//! true and cheap.
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
//!
//! [`Proj::fst`]: crate::proj::Proj
//! [`Proj::snd`]: crate::proj::Proj

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::proj::Proj;
use crate::sigma::Telescope;
use crate::{conj_of, conj_proj, eq_symm, establishes, gen_all, inst_all, syl};

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
