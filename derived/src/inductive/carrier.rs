//! **The carrier of an inductive declaration** — §5.2's `A`, `B` and the
//! W-type they bound, assembled from a [`DeclSpec`](super::DeclSpec) alone.
//!
//! # What the thesis asks for
//!
//! `thesis.txt:1786–1801`. The `spec` judgment recurses over the constructor
//! list and, within each constructor, over its arguments, producing three terms
//! `A; B; G`. For a **non-indexed** declaration `G` is vacuous
//! (`INDUCTIVES.md:176`) and the translation
//!
//! ```text
//! Jµt : F. KK = λx :: α. { s : Wp : A. B p | recW (λp. G p) s x }
//! ```
//!
//! collapses to the W-type outright. What is left is
//!
//! ```text
//! Aᵢ      := Σy₀:β₀. … Σy_{k-1}:β_{k-1}. 1        [crate::sigma::Telescope]
//! A       := Sum_n(A₀ … A_{n-1})                  [crate::isum::symbols]
//! B       := rec₊(λ_. v₀, … rec₊(λ_. v_{n-1}, ∅))                  [crate::fibre]
//! carrier := W(A, B, u)
//! ```
//!
//! with `vᵢ = Sum_{mᵢ}(Σ(z::γ₀) … Σ(z::γ_{mᵢ-1}))` — [`fibre_values`], the
//! thesis's recursive-argument rule read off the spec. A constructor all of
//! whose `γⱼ` are empty has `vᵢ = finord(mᵢ)` **literally**, because `finord` is
//! `Sum_m` of `m` copies of `1`, so the plain case is not a branch in the rule
//! and no plain declaration's terms move.
//!
//! # A **function-typed** recursive argument
//!
//! One non-empty `γⱼ` and the constructor's recursive-argument function is
//! [`RecArg::general`]'s rather than [`RecArg::new`]'s, its `j`-th hypothesis is
//! `gⱼ ∈ fs(Σ(z::γⱼ), ind(p⃗))` rather than `rⱼ ∈ ind(p⃗)`, and its codomain is
//! built from the branches (`⋃ⱼ ran(gⱼ)`) rather than taken as a parameter. The
//! choice is made per constructor, off the spec, in [`Inductive::build`].
//!
//! **Two things are declined rather than derived, and both are named where they
//! live**: `ctor_injective` at such a constructor (see
//! [`super::distinct`]), and the whole recursor path
//! ([`Inductive::has_function_typed_recs`] is the guard). Everything else —
//! the carrier, the bound, the constructor typing rule and pairwise
//! distinctness — holds at every constructor.
//!
//! — one telescope per constructor, one summand per constructor, one `rec₊` per
//! constructor. Every one of those three is already a primitive; this file is
//! the assembly, the **bound**, and the definitional extension naming the
//! result.
//!
//! # The bound is seeded at `{A, T}`, and that is the whole of it
//!
//! [`crate::bound::least_universe_closed`] wants
//!
//! ```text
//! A ∈ U(c)      and      ∀a ∈ A. app(B,a) ∈ U(c)
//! ```
//!
//! for some seed `c`. `wnat.rs` and `wlist.rs` both take `c := A` and then
//! discharge the second obligation by **case analysis on the tag sum**, showing
//! each constructor's fibre — `0` or `1` there — separately lands in `U(A)`.
//! That does not generalise: the fibres here are `finord(mᵢ)`, and
//! `finord(m) ∈ U(A)` for arbitrary `m` would need `U` closed under binary
//! sums, which is a sequence of closure lemmas nobody has needed yet.
//!
//! Taking
//!
//! ```text
//! c := {A, T}          T = the fibre family's codomain, {finord(m₀)} ∪ (…)
//! ```
//!
//! removes the problem rather than solving it. `c ∈ U(c)` is
//! [`crate::universe::mem_least_universe`]; `A ∈ c` and `T ∈ c` are
//! [`crate::upair_members`]; and **transitivity** of `U(c)`
//! ([`crate::universe::least_universe_transitive`], the clause added to
//! `ax_tarski` on 2026-07-31) turns each of those into membership in `U(c)`.
//! The second obligation is then [`crate::fibre::Fibre::values_in_target`],
//! which is `∀a ∈ A. app(B,a) ∈ T`, followed by transitivity once more. So the
//! bound costs **four uses of one lemma and no case analysis at all** — and in
//! particular it never asks what `mᵢ` is, which is why it holds at every arity.
//!
//! `INDUCTIVES.md`'s note that "the transitivity clause removed the need for the
//! ω-tower" is what this depends on, and this is the first place the clause pays
//! for something the hand-written files could not do.
//!
//! **The seed was re-examined on 2026-08-01 and kept.**
//! [`crate::isum::finord_in_universe`] has since made `finord(m) ∈ U(A)`
//! available, so the *tight* seed `c := A` is now reachable and the sentence
//! above about "a sequence of closure lemmas nobody has needed yet" is no
//! longer the obstacle it was. It is still the right choice, for a reason that
//! only appears downstream: [`crate::cumul::DeclUniverse`] — the consumer that
//! turns this into `⊢ ⟦T⟧ ∈ U₁` — must produce `S ∈ U(c)` for its own tower
//! seed `S = A ∪ ⋃T`, hence both `A ∈ U(c)` and `T ∈ U(c)`. At `c = {A,T}`
//! both are one use of transitivity at a member of the seed and neither
//! mentions `mᵢ`; at `c = A` the second costs `finord_in_universe` plus `U(A)`'s
//! pairing and binary-union closures, `n + 1` steps that grow with the
//! declaration. So the seed is the cheaper of the two on the only path that
//! consumes it, not merely the one that was reachable first.
//!
//! # Interface
//!
//! [`Inductive::build`] takes a [`Machine`] and a [`DeclSpec`](super::DeclSpec)
//! and returns everything:
//!
//! ```text
//! ⊢ closed(A, B, U({A,T}))                              [Inductive::closed]
//! ⊢ ∀p⃗. ind(p⃗) = W(A, B, U({A,T}))                      [Inductive::ty_ax]
//! ⊢ ∀p⃗ ∀y⃗ ∀r⃗. (H → ctor_i(y⃗,r⃗) ∈ ind(p⃗))               [Ctor::mem]
//! ⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. (ctor_i(y⃗,r⃗) = ctor_i(y⃗′,r⃗′) → E)   [Ctor::inj]
//! ⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. ¬(ctor_i(y⃗,r⃗) = ctor_j(y⃗′,r⃗′))       [Inductive::distinct]
//! ```
//!
//! where `H` is the right-nested conjunction of `yⱼ ∈ βⱼ(p⃗, y₀…y_{j-1})` and
//! `rⱼ ∈ ind(p⃗)`, **absent entirely** when the constructor is nullary (see
//! [`crate::ctx`] for why that matters), and `E` is the **one flat
//! right-nested chain** of all `k + m` equations
//!
//! ```text
//! y₀ = y₀′ ∧ (y₁ = y₁′ ∧ (… ∧ (r₀ = r₀′ ∧ (… ∧ r_{m-1} = r_{m-1}′))))
//! ```
//!
//! — arguments then recursive arguments in declaration order, *not* grouped as
//! `(⋀ⱼ yⱼ = yⱼ′) ∧ (⋀ⱼ rⱼ = rⱼ′)`. At `k = 2, m = 1` it is
//! `y₀ = y₀′ ∧ (y₁ = y₁′ ∧ r₀ = r₀′)`. A caller who rebuilds the grouped form
//! and compares gets a rejection.
//!
//! # One `Inductive` belongs to one `Machine`
//!
//! Everything above is stated over the apparatus [`Inductive::build`] was
//! handed. The methods that take a `&Machine` afterwards —
//! [`Inductive::ctor_term`] and [`Inductive::distinct`] — check it is the same
//! one ([`Inductive::is_over`]) and return `None` otherwise, because a second
//! apparatus answers every internal step out of *its* `Inj`, `upair` and `rec₊`
//! and would hand back a true theorem about terms that are not these
//! constructors.
//!
//! # Non-vacuity
//!
//! Memberships alone would be satisfied by a one-element carrier, and
//! `Inductive::distinct` is what stops that: distinct constructors are provably
//! distinct sets, so an `n`-constructor enumeration has `n` provably different
//! elements. [`Ctor::inj`] does the same for the arguments — a constructor's
//! arguments come back out of it, so `List`'s carrier sees `α`'s elements and a
//! tree's carrier sees its subtrees. `tests/inductive.rs` cashes both at eight
//! declarations, including a three-constructor enumeration and a binary tree,
//! neither of which anything in `derived/` could express before.

use std::rc::Rc;

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::fibre::Fibre;
use crate::recarg::RecArg;
use crate::sigma::Telescope;
use crate::sums::Sums;
use crate::{and_intro, define_abbrev, eq_symm, inst_all, syl, upair_members};

use super::ctor::{ctor_typing, Ctor};
use super::distinct::ctors_distinct;
use super::machine::{Machine, MachineId};
use super::spec::DeclSpec;

/// A translated declaration: the carrier, and every constructor.
pub struct Inductive {
    /// The declaration this was built from.
    pub spec: DeclSpec,
    /// The `np` parameter variables, free in [`Inductive::carrier`].
    pub params: Vec<FreeVar>,
    /// One telescope per constructor — the `Σ` nest over its arguments. Shared
    /// with [`Machine`]'s cache, so two constructors with the same argument
    /// types are the *same* telescope.
    pub telescopes: Vec<Rc<Telescope>>,
    /// One telescope per **recursive slot** of each constructor — the `Σ` nest
    /// over `γⱼ`, whose type at `p⃗` is the slot's fibre summand `Aⱼ`, and
    /// `None` at a plain slot where `γⱼ` is empty.
    ///
    /// Kept because [`Inductive::minor_args`] needs the slot's *argument type*
    /// `β₀ⱼ(p⃗)` and not only its summand: the summand is a set of tuples and
    /// Lean's minor premise is a function on the argument type. The telescopes
    /// come from [`Machine::telescope`]'s cache, so these are the very ones
    /// `fibre_summands` built the summands from — not a second nest of the same
    /// shape, which no equation would relate to the carrier.
    pub rec_telescopes: Vec<Vec<Option<Rc<Telescope>>>>,
    /// One recursive-argument function per constructor.
    pub recargs: Vec<RecArg>,
    /// `A₀ … A_{n-1}`, the tag summands at the declaration's parameters.
    pub summands: Vec<Term>,
    /// `A = Sum_n(A₀ … A_{n-1})`.
    pub tags: Term,
    /// The fibre family `B`, and its codomain `T`.
    pub fibre: Fibre,
    /// `c = {A, T}`, the universe seed.
    pub seed: Term,
    /// `U({A,T})`, the bound the W-type is carved out of.
    pub bound: Term,
    /// `⊢ closed(A, B, U({A,T}))` — **unconditional**.
    pub closed: Thm,
    /// The type symbol `ind`, of arity `np`.
    pub ty: FnSym,
    /// `⊢ ∀p⃗. ind(p⃗) = W(A, B, U({A,T}))`.
    pub ty_ax: Thm,
    /// `ind(p⃗)`, at [`Inductive::params`].
    pub carrier: Term,
    /// `W(A, B, U({A,T}))` — the same set, before the abbreviation.
    pub wty: Term,
    /// The constructors, in declaration order.
    pub ctors: Vec<Ctor>,
    /// **Which [`Machine`] every term and theorem above is stated over.**
    ///
    /// Recorded so that the methods taking a `&Machine` — which cannot
    /// otherwise tell — can refuse a second apparatus. See
    /// [`Inductive::ctor_term`].
    pub machine: MachineId,
    /// `Inj_0 … Inj_{n-1}` as this declaration used them: the tag symbols the
    /// constructor terms are built from. Part of the same identity, and kept
    /// separately because the sum symbols live in a cache that keeps growing
    /// while the four in [`MachineId`] do not.
    pub inj_syms: Vec<FnSym>,
}

impl Inductive {
    /// Translate a declaration.
    ///
    /// Returns `None` when the spec is not
    /// [`well_formed`](DeclSpec::well_formed) — an argument type whose arity is
    /// not `np + i` would silently be applied to the wrong terms.
    pub fn build(env: &mut Env, mach: &mut Machine, spec: &DeclSpec) -> Option<Inductive> {
        if !spec.well_formed() {
            return None
        }
        let np = spec.params;
        let n = spec.ctors.len();

        // Every arity this declaration mentions: `n` for the tag set, and
        // `mᵢ` for each constructor's fibre. One `ensure` covers all of them.
        let widest = spec.ctors.iter().map(|c| c.recs).chain(std::iter::once(n)).max()?;
        let sums = mach.wt.sums.clone();
        mach.syms.ensure(env, &sums, widest)?;

        let params: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();

        // ── one telescope per constructor: §5.2's `∀y : β` rule, iterated ───
        let mut telescopes = Vec::with_capacity(n);
        let mut summands = Vec::with_capacity(n);
        for c in &spec.ctors {
            let tel = mach.telescope(env, np, &c.args)?;
            summands.push(tel.ty_of(ps.clone()));
            telescopes.push(tel);
        }
        // ── one telescope per recursive slot, from the same cache ───────────
        let mut rec_telescopes = Vec::with_capacity(n);
        for c in &spec.ctors {
            let mut per = Vec::with_capacity(c.recs);
            for j in 0..c.recs {
                let gamma = c.rec_dom(j);
                per.push(match gamma.is_empty() {
                    true => None,
                    false => Some(mach.telescope(env, np, gamma)?),
                });
            }
            rec_telescopes.push(per);
        }
        // ── the tag set and the fibre family ────────────────────────────────
        let fibre_lists = fibre_summands(env, mach, spec, &ps)?;
        let values: Vec<Term> =
            fibre_lists.iter().map(|f| mach.syms.sum(f)).collect::<Option<_>>()?;
        let s = &mach.wt.sums;
        let fibre = Fibre::new(
            env,
            s,
            &mach.cases,
            &mach.syms,
            &params,
            &summands,
            &values,
            &mach.wt.empty_fun,
            &mach.wt.app_pair,
        )?;
        let tags = fibre.tags.clone();
        let target = fibre.target.clone();

        // ── the bound, seeded at `{A, T}` ───────────────────────────────────
        let seed = Term::apply(s.ap.sets.up, vec![tags.clone(), target.clone()]);
        let bound = mach.bnd.universe_of(seed.clone());
        let seed_in_u = inst_all(&mach.mem_lu, std::slice::from_ref(&seed))?;
        let trans = {
            // `⊢ ∀y. (y ∈ U(c) → ∀z. (z ∈ y → z ∈ U(c)))` at this seed.
            inst_all(&mach.trans_lu, std::slice::from_ref(&seed))?
        };
        let members_of = |th: &Thm, y: &Term| -> Option<Thm> {
            Thm::mp(&inst_all(&trans, std::slice::from_ref(y))?, th)
        };
        let (a_in_seed, t_in_seed) = upair_members(&s.ap.sets.up_ax, &tags, &target)?;
        let a_in_u = Thm::mp(
            &inst_all(&members_of(&seed_in_u, &seed)?, std::slice::from_ref(&tags))?,
            &a_in_seed,
        )?;
        let t_in_u = Thm::mp(
            &inst_all(&members_of(&seed_in_u, &seed)?, std::slice::from_ref(&target))?,
            &t_in_seed,
        )?;

        // `∀a. (a ∈ A → app(B,a) ∈ U(c))`, with no case analysis on the tag.
        let av = env.fresh_var();
        let ta = Term::var(av);
        let fibres = {
            let in_target = inst_all(&fibre.values_in_target, std::slice::from_ref(&ta))?;
            let widen = inst_all(
                &members_of(&t_in_u, &target)?,
                std::slice::from_ref(&s.ap.apply(fibre.fam.clone(), ta.clone())),
            )?;
            Thm::gen(av, &syl(&in_target, &widen)?)
        };
        debug_assert_eq!(
            *fibres.concl(),
            crate::bound::fibres_in(env, s, &tags, &fibre.fam, &bound),
            "inductive: the family condition is not the one the W-type rules state"
        );

        let typing = and_intro(&a_in_u, &fibres);
        let closed = Thm::mp(
            &inst_all(
                &mach.bnd.least_universe_closed,
                &[seed.clone(), tags.clone(), fibre.fam.clone()],
            )?,
            &typing,
        )?;
        debug_assert_eq!(
            *closed.concl(),
            crate::wtype::closed(env, s, &tags, &fibre.fam, &bound),
            "inductive: closed has the wrong shape"
        );

        // ── the carrier, as a definitional extension ────────────────────────
        let wty = mach.wt.of(tags.clone(), fibre.fam.clone(), bound.clone());
        let (ty, ty_ax) = define_abbrev(env, &params, &wty)?;
        let carrier = Term::apply(ty, ps.clone());
        let to_ty = eq_symm(env, &inst_all(&ty_ax, &ps)?)?;

        // `sup`'s typing rule at this instance, with the bound discharged.
        let sup = Thm::mp(
            &inst_all(&mach.bnd.sup_mem, &[seed.clone(), tags.clone(), fibre.fam.clone()])?,
            &typing,
        )?;

        // ── the recursive-argument functions, one per constructor ──────────
        //
        // **The entry point is chosen by the spec, not by the arity.** A
        // constructor all of whose `γⱼ` are empty takes the degenerate
        // `RecArg::new`, whose codomain is `fin(r⃗)` — that is what keeps every
        // plain constructor's *term* unchanged. One non-empty `γⱼ` and the whole
        // constructor takes `RecArg::general`, over that constructor's own fibre
        // summands.
        let mut recargs = Vec::with_capacity(n);
        for (i, c) in spec.ctors.iter().enumerate() {
            recargs.push(if c.rec_doms.iter().any(|g| !g.is_empty()) {
                RecArg::general(
                    env,
                    s,
                    &mach.cases,
                    &mach.syms,
                    &mach.ran,
                    &mach.fin,
                    &mach.wt.fs_mono,
                    &mach.wt.empty_fun,
                    &fibre_lists[i],
                )?
            } else {
                RecArg::new(
                    env,
                    s,
                    &mach.cases,
                    &mach.syms,
                    &mach.pf,
                    &mach.fin,
                    &mach.wt.fs_mono,
                    &mach.wt.empty_fun,
                    c.recs,
                )?
            });
        }

        // ── the constructors ────────────────────────────────────────────────
        let frame = Frame {
            ps: &ps,
            params: &params,
            telescopes: &telescopes,
            summands: &summands,
            fibre: &fibre,
            recargs: &recargs,
            wty: &wty,
            carrier: &carrier,
            to_ty: &to_ty,
            sup: &sup,
        };
        let mut ctors = Vec::with_capacity(n);
        for i in 0..n {
            ctors.push(ctor_typing(env, mach, &frame, i)?);
        }

        let inj_syms: Vec<FnSym> = (0..n).map(|i| mach.syms.inj_sym(i)).collect::<Option<_>>()?;
        let out = Inductive {
            spec: spec.clone(),
            params,
            telescopes,
            rec_telescopes,
            recargs,
            summands,
            tags,
            fibre,
            seed,
            bound,
            closed,
            ty,
            ty_ax,
            carrier,
            wty,
            ctors,
            machine: mach.ident(),
            inj_syms,
        };
        // **The two spellings of the fibre summands agree at the declaration's
        // own parameters.** `fibre_summands` mints; `Inductive::fibre_summands_at`
        // reads `rec_telescopes` and is what a client instantiating at other
        // parameters gets. They are the same terms only because the telescopes
        // come from one cache, which is a property of `Machine` and not of
        // either function — so it is checked here rather than asserted in two
        // headers. A drift makes `carrier_at` name a fibre family that is not
        // this declaration's, and it returns *terms*.
        //
        // **Measured, and weaker than "nothing downstream could catch it".**
        // Two mutations of `fibre_summands_at` — the slot index clamped to
        // `min(j,1)`, and the per-constructor list reversed — were both caught
        // with this check *removed*: the first by one test
        // (`mini::rec_dep`'s function-typed dependent eliminator), the second by
        // eleven across six suites. So this converts a wrong-term outcome into
        // a clean decline three suites earlier rather than catching something
        // otherwise invisible; it is kept for that, and the claim is recorded
        // at its measured strength.
        if out.fibre_summands_at(s, &ps)? != fibre_lists {
            return None
        }
        Some(out)
    }

    /// Whether `mach` is the apparatus this declaration was translated over.
    ///
    /// Nothing else ties the two together: `mach` arrives as a bare `&Machine`,
    /// every step of every method below resolves against *it*, and a second
    /// apparatus with warm caches answers every one of them — with a true
    /// theorem about somebody else's `Inj`, `upair` and `rec₊`. This is the
    /// same shape as the historical `Chain::new` symbol mismatch, and the same
    /// answer: compare the symbols.
    pub fn is_over(&self, mach: &Machine) -> bool {
        self.machine == mach.ident()
            && (0..self.inj_syms.len()).all(|i| mach.syms.inj_sym(i) == Some(self.inj_syms[i]))
    }

    /// The term `ind(p⃗)` at caller-supplied parameters.
    pub fn ty_of(&self, args: Vec<Term>) -> Term { Term::apply(self.ty, args) }

    /// The term `ctor_i(y⃗, r⃗) = ⟨inj_i⟨y₀,…,•⟩, f(r⃗)⟩` at caller-supplied
    /// arguments — what a client builds to *state* something about a
    /// constructor application.
    ///
    /// `None` if `i` is out of range, if `args`/`recs` are not the constructor's
    /// own arities — a shorter tuple is a perfectly well-formed term that is
    /// *not* a constructor application, and a client could otherwise state an
    /// obligation about it — or if `mach` is not the apparatus this declaration
    /// was built over ([`Inductive::is_over`]).
    ///
    /// **The dispatcher is chosen per constructor, exactly as
    /// `super::ctor`'s own `ctor_typing` chooses it.** A constructor with a
    /// function-typed recursive argument gets [`RecArg::of_general`], whose
    /// codomain is `⋃ⱼ ran(gⱼ)`; the degenerate [`RecArg::of`] at the same
    /// arguments is a *different term* over `fin(g⃗)`, and one this declaration
    /// has no theorem about. Nothing downstream could catch that: the result is
    /// a term, so a client would state its obligation about a set that is not
    /// this constructor and the mislabelling would be invisible — the cost
    /// [`Inductive::is_over`]'s own comment puts at a session.
    pub fn ctor_term(
        &self,
        mach: &Machine,
        i: usize,
        args: &[Term],
        recs: &[Term],
    ) -> Option<Term> {
        self.ctor_term_at(mach, i, args, recs, &self.param_terms())
    }

    /// [`Inductive::ctor_term`] at **caller-supplied parameters**.
    ///
    /// The instantiable spelling, and the reason it has to exist is the same
    /// one [`Inductive::fibre_at`] exists for, one construction later. A
    /// constructor that takes [`RecArg::of_general`] dispatches over its own
    /// fibre summands `Σ(z::γⱼ(p⃗))`, so its term **mentions the declaration's
    /// parameters** even at parameter-free arguments — and a client stating
    /// something at other parameters (a checker's λ-nest binders, say) gets a
    /// term that is half at its own variables and half at the declaration's,
    /// which is not a constructor application of anything.
    ///
    /// At `ps = self.params` this is [`Inductive::ctor_term`] on the nose,
    /// because [`Inductive::build`] checks that
    /// [`Inductive::fibre_summands_at`] agrees there with the lists
    /// [`RecArg::general`] was handed. A plain constructor's term mentions no
    /// parameter at all and `ps` is inert.
    ///
    /// `None` in every case [`Inductive::ctor_term`] is `None`, plus a wrong
    /// parameter arity.
    pub fn ctor_term_at(
        &self,
        mach: &Machine,
        i: usize,
        args: &[Term],
        recs: &[Term],
        ps: &[Term],
    ) -> Option<Term> {
        if i >= self.ctors.len() || !self.is_over(mach) {
            return None
        }
        if args.len() != self.telescopes[i].betas.len() {
            return None
        }
        let s = &mach.wt.sums;
        let fun = self.recfun_of_at(mach, i, recs, ps)?;
        Some(mach.wt.sup(mach.syms.inj(i, Telescope::tuple_of(s, args))?, fun))
    }

    /// The declaration's own parameter variables, as terms.
    pub fn param_terms(&self) -> Vec<Term> {
        self.params.iter().map(|v| Term::var(*v)).collect()
    }

    /// The term `f(r⃗)` — the `i`-th constructor's **recursive-argument
    /// function** at caller-supplied arguments, and the one place the two
    /// dispatcher spellings are chosen.
    ///
    /// [`RecArg::of`], whose codomain is `fin(r⃗)`, at a constructor all of whose
    /// `γⱼ` are empty; [`RecArg::of_general`], whose codomain is `⋃ⱼ ran(gⱼ)`,
    /// at one with a function-typed recursive argument. **The two are different
    /// terms at the same arguments**, and a declaration has theorems about only
    /// the one its `Inductive::build` chose.
    ///
    /// [`Inductive::ctor_term`] and [`super::iota`] both read this rather than
    /// matching on `RecArg::hyp` themselves, which is what makes their agreement
    /// a consequence instead of a `debug_assert`. `4ba0904` fixed exactly this
    /// defect in the other direction — `ctor_term` built `RecArg::of` while
    /// `ctor_typing` had chosen `of_general`, so the public term-builder and
    /// `Ctor::term` named different sets.
    ///
    /// `None` on a bad index, a wrong `recs` arity, or a foreign machine.
    pub fn recfun_of(&self, mach: &Machine, i: usize, recs: &[Term]) -> Option<Term> {
        self.recfun_of_at(mach, i, recs, &self.param_terms())
    }

    /// [`Inductive::recfun_of`] at **caller-supplied parameters** — the one
    /// place `ps` is actually spent, since the summands are the only part of a
    /// constructor term that mentions the declaration's parameters.
    ///
    /// [`RecArg::summands`] is `Σ(z::γⱼ(p⃗))` at the declaration's own `p⃗`;
    /// [`Inductive::fibre_summands_at`] is the same list at any `p⃗`, off the
    /// telescope cache the summands were minted from. The degenerate branch
    /// reads neither — [`RecArg::of`] builds `m` copies of `1` itself — so a
    /// plain declaration's term is `ps`-independent by construction and not by
    /// a comparison.
    ///
    /// `None` on a bad index, a wrong `recs` arity, a foreign machine, or a
    /// wrong parameter arity.
    pub fn recfun_of_at(
        &self,
        mach: &Machine,
        i: usize,
        recs: &[Term],
        ps: &[Term],
    ) -> Option<Term> {
        let ra = self.recargs.get(i)?;
        if !self.is_over(mach) || recs.len() != ra.m {
            return None
        }
        let s = &mach.wt.sums;
        Some(match ra.hyp {
            None => RecArg::of(s, &mach.cases, recs),
            Some(_) => {
                let summands = self.fibre_summands_at(s, ps)?.into_iter().nth(i)?;
                RecArg::of_general(s, &mach.cases, &mach.ran, &summands, recs)
            }
        })
    }

    /// `⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. ¬(ctor_i(y⃗,r⃗) = ctor_j(y⃗′,r⃗′))`, for `i ≠ j`.
    ///
    /// Derived on demand, because it depends on the *pair* `(i,j)`. `None` when
    /// `i == j`, where the statement is false, when either index is out of
    /// range, or when `mach` is not the apparatus this declaration was built
    /// over ([`Inductive::is_over`]) — in which case every step would resolve
    /// against the *other* machine's symbols and the theorem returned would be
    /// true of terms that are not these constructors.
    /// Whether any constructor takes a **function-typed** recursive argument —
    /// a non-empty `γⱼ`, so that its recursive-argument function dispatches over
    /// `Sum_m(Σ(z::γ⃗))` rather than `finord(m)`.
    ///
    /// **Per declaration, and that is the wrong grain for three of its four
    /// former readers** — see [`Inductive::rec_slot_domains`].
    ///
    /// **Nothing guards on this any more, and nothing guards on
    /// [`Inductive::has_mixed_ctor`] either.**
    /// [`crate::inductive::recursor::GenRecursor`] stopped declining on this
    /// flag in `c4203c4` and [`crate::inductive::dep::DepRecursor`] in `79a65c6`,
    /// where it was replaced by the strictly narrower `has_mixed_ctor`; that
    /// door is now open too. Both flags are kept because they are true and
    /// cheap questions about a declaration — `has_mixed_ctor` is the question
    /// [`Inductive::minor_subs`] is a function of — but every reader that used
    /// either as a guard was asking one of the two *per-slot* questions
    /// instead: [`Inductive::rec_slot_domains`] or
    /// [`Inductive::ctor_slot_domains`].
    ///
    /// # What lifting the value recursor's guard cost, measured
    ///
    /// Not the substitution it looked like. Lean's minor premise for a
    /// function-typed field takes the field's **function** on `Aⱼ` and one
    /// induction hypothesis, also on `Aⱼ`; the ι rule can hand it the variable
    /// a constructor was applied to, and *that* is the sense in which "Lean
    /// hands you the function" and [`super::rect::recarg_eta`] is skipped. The
    /// **step** cannot: [`crate::wrec_total::step_typed`] quantifies over every
    /// `f ∈ fs(B(a), W)`, so `valᵢ(σ,f,r)` is defined at an arbitrary `f` and
    /// has to project the field back out of the pack. That projection is
    /// [`crate::isum::Branch`], `f|ⱼ = {⟨z, app(f,Injⱼ z)⟩ : z ∈ Aⱼ}`. All four
    /// steps have landed:
    ///
    /// * [`super::premise`] — `minor_typedᵢ`'s `tⱼ ∈ W` / `vⱼ ∈ T` became
    ///   `tⱼ ∈ fs(Aⱼ,W)` / `vⱼ ∈ fs(Aⱼ,T)` at a function-typed slot, through the
    ///   **additive** [`super::premise::minor_typed_at`], because
    ///   `checker/src/tg.rs` consumes the present signature;
    /// * [`super::step`] — `Rx::fibre(i)` is `recargs[i].domain`, which is
    ///   `finord(mᵢ)` *literally* in the plain case, and `Rx::fibre_apps`
    ///   chooses `app(f, Injⱼ(•))` or `f|ⱼ` **per recursive argument**;
    /// * [`super::typed`] — one `branch_in_funspace` where the plain slot spends
    ///   `app_mem`;
    /// * [`super::iota`] — the two identifications `recfun(g⃗)|ⱼ = gⱼ` and
    ///   `cmp|ⱼ = comp(grec, gⱼ, Aⱼ)`, each [`crate::ext::funspace_ext`] over
    ///   [`crate::isum::Branch`]'s computation rule, and the ih slot of the ι
    ///   rule's right-hand side is `comp(grec, tⱼ, Aⱼ)` and not
    ///   `app(grec, tⱼ)`.
    ///
    /// Two things the plan did not name, both found by measurement. `Machine`
    /// needed **no** `Branch` cache: [`crate::isum::ISumSyms`] has had one
    /// behind `&self` since `isum::restrict` landed. And a **mixed**
    /// constructor — `γ₀ = ∅`, `γ₁ = [Bool]` — takes [`RecArg::general`] as a
    /// whole, so *every* branch is a function and its plain slot's value is
    /// `app(tⱼ, •)` rather than `tⱼ`; that is the only shape at which
    /// `Rx::inj_pt_mem` over the constructor's own summands differs from one
    /// over `finord(mᵢ)`, and both mutations fail nothing without it.
    ///
    /// # What the dependent piece cost, measured
    ///
    /// [`super::dep::DepRecursor`] was a **second** and larger piece, and it is
    /// landed. The scope was right about the shape — the motive obligation
    /// `app(drec,tⱼ) ∈ app(C,tⱼ)` becomes `∀z ∈ Aⱼ. app(vⱼ,z) ∈ app(C,app(tⱼ,z))`,
    /// which is [`super::motive::ih_at_motive`], and it runs through
    /// [`super::guard`] and [`super::motive`] alike — and **wrong about two
    /// things, both found by measurement**:
    ///
    /// * `recarg_eta` at the general fibre needs a **third** ingredient the
    ///   note did not name. Dropping [`crate::sums::Sums::unit_eta`] and
    ///   spending [`crate::recarg::RecArg::app`]'s hypothesis is two of three;
    ///   the missing one is [`crate::isum::Branch`], because the `m` things the
    ///   dispatcher is rebuilt from are the **restrictions** `f|ⱼ` and not the
    ///   values `app(f, Injⱼ(•))` — at a general summand there is no single
    ///   value to read.
    /// * The guard was **not** the only thing stopping the dependent path.
    ///   With `has_function_typed_recs` removed from `dep.rs`'s door,
    ///   `decl_rect` and `GuardedMinors::build` both still returned `None` at
    ///   `RTree` — they fail closed on their own — while
    ///   [`super::rect::rect_step`] and [`super::motive::dep_minor`], which are
    ///   *statement* builders and cannot fail, went on producing a
    ///   well-formed, unprovable formula. That asymmetry is why the door needed
    ///   a guard at all.
    ///
    /// # What the mixed constructor cost, measured
    ///
    /// The same measurement at the *next* door said something different, and it
    /// is worth the two lines. With `has_mixed_ctor` removed and nothing else
    /// changed, [`super::rect::decl_rect`] **went through** — the induction
    /// principle was already wide enough, because it reads
    /// [`Inductive::ctor_slot_domains`] and a mixed constructor is a general
    /// dispatcher like any other. Only `GuardedMinors::build` stopped, at one
    /// `hyp_mp` in `minor_lands`, on two of `DEPᵢ`'s four antecedent atoms —
    /// both at the plain slot, both with the *subject* right and the *set*
    /// wrong. So the second door was one site and the first was three.
    pub fn has_function_typed_recs(&self) -> bool {
        self.spec.ctors.iter().any(|c| c.rec_doms.iter().any(|g| !g.is_empty()))
    }

    /// **Each constructor's fibre summands at caller-supplied parameters** —
    /// `Σ(z::γ₀(p⃗)) … Σ(z::γ_{m-1}(p⃗))`, the list [`fibre_values`] sums.
    ///
    /// The instantiable spelling of [`fibre_summands`], which mints and so
    /// needs `&mut Env` and `&mut Machine`. This one reads
    /// [`Inductive::rec_telescopes`], which by that field's own contract holds
    /// **the very telescopes** `fibre_summands` built the summands from — they
    /// come out of [`Machine::telescope`]'s cache — so at `ps = self.params`
    /// the two agree term for term, and [`Inductive::build`] checks that they
    /// do rather than leaving it to the comment.
    ///
    /// `None` at the wrong parameter arity.
    pub fn fibre_summands_at(&self, s: &Sums, ps: &[Term]) -> Option<Vec<Vec<Term>>> {
        if ps.len() != self.params.len() {
            return None
        }
        let unit = s.unit();
        Some(
            self.rec_telescopes
                .iter()
                .map(|per| {
                    per.iter()
                        .map(|t| match t {
                            None => unit.clone(),
                            Some(t) => t.ty_of(ps.to_vec()),
                        })
                        .collect()
                })
                .collect(),
        )
    }

    /// **The fibre values and their codomain at caller-supplied parameters** —
    /// `(v₀ … v_{n-1}, T)` where `vᵢ = Sum_{mᵢ}(Σ(z::γ⃗(p⃗)))` and
    /// `T = {v₀} ∪ (… ∪ ∅)`.
    ///
    /// The `Fibre`'s own [`values`](crate::fibre::Fibre::values) and
    /// [`target`](crate::fibre::Fibre::target) are these at the declaration's
    /// **own** parameter variables. A value may mention them — that is the
    /// whole content of the fibre taking a parameter telescope — so a client
    /// stating something at other parameters must re-state the codomain too,
    /// and [`carrier_at`](super::recursor::carrier_at) is the one that does.
    ///
    /// `None` at a foreign machine, at the wrong parameter arity, or if a sum
    /// symbol of the needed width is not minted.
    pub fn fibre_at(&self, mach: &Machine, ps: &[Term]) -> Option<(Vec<Term>, Term)> {
        if !self.is_over(mach) {
            return None
        }
        let s = &mach.wt.sums;
        let per = self.fibre_summands_at(s, ps)?;
        let values: Vec<Term> =
            per.iter().map(|f| mach.syms.sum(f)).collect::<Option<_>>()?;
        let target = crate::fibre::target_of(s, &values);
        Some((values, target))
    }

    /// **The stated set of each of constructor `i`'s recursive-argument
    /// slots** — `None` for a plain one and `Some(Aⱼ)` for a function-typed
    /// one.
    ///
    /// The single place the two spellings are chosen, so that
    /// [`super::premise`], [`super::step`], [`super::typed`] and
    /// [`super::iota`] cannot disagree about which slot is which. Empty when
    /// `i` is out of range, which is the plain spelling everywhere and
    /// therefore the safe answer.
    ///
    /// **Per recursive argument, not per constructor**, and the distinction is
    /// real: a constructor with `γ₀ = ∅` and `γ₁ = [Bool]` takes
    /// [`RecArg::general`] as a *whole* — that choice is per constructor, made
    /// in [`Inductive::build`] — while its first slot stays plain, because
    /// Lean's first field is still a plain recursive occurrence and its minor
    /// premise still takes an element of the carrier. The two `1`s involved are
    /// not interchangeable: `A₀ = 1` is the *fibre* summand and the slot's
    /// stated set is the carrier itself, not `fs(1, W)`.
    pub fn rec_slot_domains(&self, i: usize) -> Vec<Option<Term>> {
        let Some(c) = self.spec.ctors.get(i) else { return Vec::new() };
        (0..c.recs)
            .map(|j| {
                (!c.rec_dom(j).is_empty())
                    .then(|| self.recargs[i].summands.get(j).cloned())
                    .flatten()
            })
            .collect()
    }

    /// **The stated set of each of constructor `i`'s recursive-argument slots
    /// at the grain the *constructor term* takes them** — `None` at every slot
    /// of a plain constructor, `Some(Aⱼ)` at **every** slot of one that takes
    /// [`RecArg::general`].
    ///
    /// The second of the two grains, and the mixed constructor is what makes
    /// them two. [`Inductive::rec_slot_domains`] answers *"what does Lean's
    /// minor premise take at this slot"* — `None` at a plain slot, even inside
    /// a general constructor, because Lean's field there is still an element of
    /// the carrier. This one answers *"what does [`Inductive::ctor_term`]'s
    /// `j`-th recursive argument range over"*, and at that same slot the answer
    /// is `fs(1, W)`, because [`RecArg::general`] is chosen per **constructor**
    /// and dispatches over every summand alike.
    ///
    /// [`super::rect`] reads this one, because its `φ` is applied to
    /// `ctorᵢ(y⃗,t⃗)` itself and so quantifies the constructor's own arguments;
    /// [`super::premise`] and [`super::guard`] read the other. The ι rule is
    /// where the two meet: it quantifies at *this* grain and instantiates the
    /// minor premise at the *other*, which is why its plain slot of a mixed
    /// constructor is handed `app(tⱼ, •)`.
    ///
    /// Empty when `i` is out of range.
    pub fn ctor_slot_domains(&self, i: usize) -> Vec<Option<Term>> {
        let Some(ra) = self.recargs.get(i) else { return Vec::new() };
        match ra.hyp {
            None => vec![None; ra.m],
            Some(_) => ra.summands.iter().cloned().map(Some).collect(),
        }
    }

    /// Whether any constructor is **mixed** — carries both a plain recursive
    /// field and a function-typed one, so that
    /// [`Inductive::ctor_slot_domains`] and [`Inductive::rec_slot_domains`]
    /// disagree at one of its slots.
    ///
    /// The one shape at which "what the constructor term takes" and "what
    /// Lean's minor premise takes" are different questions with different
    /// answers, and therefore the one shape at which
    /// [`Inductive::minor_subs`] is not the identity. [`super::iota`] pays for
    /// it, and so does [`super::guard`]'s `minor_lands`, which is where
    /// [`crate::point_fun::PointFun`] reconciles the two grains — see
    /// [`super::dep`]'s header for what that cost.
    pub fn has_mixed_ctor(&self) -> bool {
        (0..self.spec.ctors.len()).any(|i| {
            let (c, r) = (self.ctor_slot_domains(i), self.rec_slot_domains(i));
            c.len() != r.len() || (0..c.len()).any(|j| c[j].is_some() != r[j].is_some())
        })
    }

    /// **What constructor `i`'s minor premise is handed at each recursive
    /// slot**, given the *constructor term's* own recursive arguments `t⃗`.
    ///
    /// The single place the two grains are reconciled, and the only place the
    /// mixed constructor's `app(tⱼ, •)` is written:
    ///
    /// | `ctor_slot_domains` | `rec_slot_domains` | value |
    /// |---|---|---|
    /// | `None` | `None` | `tⱼ` — a plain constructor |
    /// | `Some(1)` | `None` | `app(tⱼ, •)` — a **mixed** constructor's plain slot |
    /// | `Some(Aⱼ)` | `Some(Aⱼ)` | `tⱼ` — the field's own function |
    ///
    /// [`super::iota`] builds the ι rule's right-hand side from this and
    /// [`super::dep`] rebuilds the dependent one from it, so the two cannot
    /// disagree about what a minor premise receives. `None` if `mach` is not
    /// this declaration's apparatus, if `ts` has the wrong length, or if a
    /// mixed constructor's plain slot is not the one-point set — where `• ∈ Aⱼ`
    /// is not a fact and the application would be a term nothing is true of.
    pub fn minor_subs(&self, mach: &Machine, i: usize, ts: &[Term]) -> Option<Vec<Term>> {
        let (cd, rd) = (self.ctor_slot_domains(i), self.rec_slot_domains(i));
        if !self.is_over(mach) || ts.len() != cd.len() || rd.len() != cd.len() {
            return None
        }
        let s = &mach.wt.sums;
        (0..ts.len())
            .map(|j| match (&cd[j], &rd[j]) {
                (Some(a), None) => {
                    (*a == s.unit()).then(|| s.ap.apply(ts[j].clone(), s.point()))
                }
                _ => Some(ts[j].clone()),
            })
            .collect()
    }

    /// **What it is handed at each induction-hypothesis slot**, at a recursor
    /// term `rec` and the composite symbol.
    ///
    /// `app(rec, subⱼ)` at a slot Lean's minor premise takes an element of the
    /// carrier at — including a mixed constructor's plain one, where `subⱼ` is
    /// `app(tⱼ, •)` — and the **composite** `comp(rec, tⱼ, Aⱼ)` at a
    /// function-typed one, where `app(rec, tⱼ)` is not even well typed. Keyed
    /// off [`Inductive::rec_slot_domains`], the minor premise's own grain,
    /// because that is whose slot this fills.
    pub fn minor_ihs(
        &self,
        mach: &Machine,
        comp: kernel::FnSym,
        rec: &Term,
        i: usize,
        ts: &[Term],
    ) -> Option<Vec<Term>> {
        let subs = self.minor_subs(mach, i, ts)?;
        let rd = self.rec_slot_domains(i);
        let ap = &mach.wt.sums.ap;
        (0..ts.len())
            .map(|j| {
                Some(match rd.get(j)? {
                    None => ap.apply(rec.clone(), subs[j].clone()),
                    Some(a) => {
                        crate::wrec::comp_of(comp, rec.clone(), ts[j].clone(), a.clone())
                    }
                })
            })
            .collect()
    }

    /// **`β₀ⱼ(p⃗)`, the argument type of each function-typed recursive slot** —
    /// `None` at a plain slot, and `None` at a slot whose `γⱼ` has depth `≥ 2`.
    ///
    /// The companion of [`Inductive::rec_slot_domains`], and *not* a second
    /// spelling of it: that one answers "which set does Lean's minor premise
    /// bind this slot at, as `derived` states it" — `Aⱼ = Σ(z::γⱼ)`, a set of
    /// tuples — and this one answers "which set is Lean's own function on",
    /// which is the telescope's single argument type. The two are related by
    /// [`crate::sigma::push`] and by nothing else.
    ///
    /// **Depth one, and the `None` above is load-bearing.** At `k ≥ 2` the map
    /// between the two sets is a currying rather than a reindexing
    /// ([`crate::sigma::push`]'s own guard), so there is no `β₀ⱼ(p⃗)` to state
    /// anything at; [`Inductive::minor_args`] therefore fails closed and the
    /// dependent premises are not stated at all rather than stated falsely.
    pub fn rec_slot_betas(&self, i: usize) -> Vec<Option<Term>> {
        let Some(tels) = self.rec_telescopes.get(i) else { return Vec::new() };
        let ps: Vec<Term> = self.params.iter().map(|v| Term::var(*v)).collect();
        tels.iter()
            .map(|t| {
                t.as_ref()
                    .filter(|t| t.betas.len() == 1)
                    .map(|t| Term::apply(t.betas[0], ps.clone()))
            })
            .collect()
    }

    /// **What Lean's own minor premise is applied to**, given what `derived`
    /// hands its `j`-th slot: `push(xⱼ, β₀ⱼ(p⃗))` at a function-typed slot and
    /// `xⱼ` itself everywhere else.
    ///
    /// The single place the last of the three grains is written. `derived`
    /// binds a function-typed recursive slot at `fs(Aⱼ, W)` — a function on
    /// *tuples*, because that is what the carrier's `W`-encoding sums — and
    /// hands the induction hypothesis at that same grain, as a function on
    /// `Aⱼ`. **Lean's minor premise is a function on neither.** Its own field
    /// binder is `⟦γⱼ → T p⃗⟧` and its ih binder is `⟦∀z:γⱼ, C (f z)⟧`, both
    /// dependent products over `⟦γⱼ⟧ = β₀ⱼ(p⃗)`, and applying `Sᵢ` to an element
    /// of `fs(Aⱼ,W)` is applying a function to something outside its domain —
    /// so the premise stated that way is *false*, not merely unproved. `push`
    /// is the crossing, and applying it here is what makes `DEPᵢ` and the
    /// dependent ι rule statements an interpreted minor premise can meet.
    ///
    /// Used for both of the minor's argument families —
    /// [`Inductive::minor_subs`]'s and [`Inductive::minor_ihs`]'s — because
    /// both cross the same seam, and used by [`super::motive::dep_minor`],
    /// [`super::guard`] and [`super::dep`] alike so the statement and the two
    /// proofs cannot drift.
    ///
    /// `None` if `mach` is not this declaration's apparatus, if `xs` has the
    /// wrong length, if the `push` operator cannot be minted, or at a
    /// function-typed slot with no depth-one `β₀ⱼ(p⃗)`
    /// ([`Inductive::rec_slot_betas`]).
    pub fn minor_args(
        &self,
        env: &mut Env,
        mach: &Machine,
        i: usize,
        xs: &[Term],
    ) -> Option<Vec<Term>> {
        let rd = self.rec_slot_domains(i);
        if !self.is_over(mach) || xs.len() != rd.len() {
            return None
        }
        if rd.iter().all(Option::is_none) {
            return Some(xs.to_vec())
        }
        let betas = self.rec_slot_betas(i);
        if betas.len() != rd.len() {
            return None
        }
        let push = mach.push(env)?;
        (0..xs.len())
            .map(|j| match rd[j] {
                None => Some(xs[j].clone()),
                Some(_) => Some(push.of(xs[j].clone(), betas[j].clone()?)),
            })
            .collect()
    }

    pub fn distinct(&self, env: &mut Env, mach: &Machine, i: usize, j: usize) -> Option<Thm> {
        if !self.is_over(mach) {
            return None
        }
        ctors_distinct(env, mach, self, i, j)
    }
}

/// What a constructor's derivation needs from the carrier's. Private.
pub(super) struct Frame<'a> {
    pub(super) ps: &'a [Term],
    pub(super) params: &'a [FreeVar],
    pub(super) telescopes: &'a [Rc<Telescope>],
    pub(super) summands: &'a [Term],
    pub(super) fibre: &'a Fibre,
    pub(super) recargs: &'a [RecArg],
    /// `W(A, B, U({A,T}))`.
    pub(super) wty: &'a Term,
    /// `ind(p⃗)`.
    pub(super) carrier: &'a Term,
    /// `⊢ W(A,B,U({A,T})) = ind(p⃗)`.
    pub(super) to_ty: &'a Thm,
    /// `⊢ ∀a. (a ∈ A → ∀f. (f ∈ fs(app(B,a), W) → ⟨a,f⟩ ∈ W))`.
    pub(super) sup: &'a Thm,
}

/// The `j`-th argument's stated type, `βⱼ(p⃗, y₀ … y_{j-1})`.
pub(super) fn arg_type(tel: &Telescope, ps: &[Term], ys: &[Term], j: usize) -> Term {
    let mut a = ps.to_vec();
    a.extend(ys[..j].iter().cloned());
    Term::apply(tel.betas[j], a)
}

/// The right-nested list of a constructor's hypotheses: the `k` argument
/// typings, then the `m` recursive arguments' membership in `carrier`.
///
/// The plain form. A **function-typed** recursive argument is not in the
/// carrier — it is a function *into* it — so a constructor with a non-empty
/// `γⱼ` needs [`ctor_atoms_at`] instead.
pub(super) fn ctor_atoms(
    tel: &Telescope,
    ps: &[Term],
    ys: &[Term],
    rs: &[Term],
    carrier: &Term,
) -> Vec<Formula> {
    ctor_atoms_at(tel, ps, ys, rs, &vec![carrier.clone(); rs.len()])
}

/// The same list with the `j`-th recursive argument's **stated set** supplied
/// per argument: `carrier` for a plain one, `fs(Σ(z::γⱼ), carrier)` for a
/// function-typed one.
///
/// That is exactly [`RecArg::general`]'s hypothesis at `S := carrier`, which is
/// why the constructor's typing rule spends the conjunction unchanged.
pub(super) fn ctor_atoms_at(
    tel: &Telescope,
    ps: &[Term],
    ys: &[Term],
    rs: &[Term],
    rec_sets: &[Term],
) -> Vec<Formula> {
    let mut atoms: Vec<Formula> = (0..ys.len())
        .map(|j| Formula::mem(ys[j].clone(), arg_type(tel, ps, ys, j)))
        .collect();
    atoms.extend(rs.iter().zip(rec_sets).map(|(r, t)| Formula::mem(r.clone(), t.clone())));
    atoms
}

/// The set the `j`-th recursive argument is stated to be in, at a given
/// carrier: `carrier` when `ra` is [`RecArg::new`]'s, `fs(Aⱼ, carrier)` when it
/// is [`RecArg::general`]'s.
pub(super) fn rec_sets(s: &Sums, ra: &RecArg, carrier: &Term) -> Vec<Term> {
    match ra.hyp {
        None => vec![carrier.clone(); ra.m],
        Some(_) => ra
            .summands
            .iter()
            .map(|a| s.fs.of(a.clone(), carrier.clone()))
            .collect(),
    }
}

/// **Each constructor's fibre summands**, `Σ(z::γ₀) … Σ(z::γ_{m-1})` — the list
/// [`fibre_values`] sums and the list [`RecArg::general`] dispatches over.
///
/// Exposed separately because those two consumers want *different shapes of the
/// same computation*: the fibre family wants one term per constructor and the
/// recursive-argument function wants the summands. Recomputing them in the
/// second would be a second telescope per `γⱼ` and a second chance to disagree.
///
/// `None` when the spec is not [`DeclSpec::well_formed`] or a telescope refuses.
pub fn fibre_summands(
    env: &mut Env,
    mach: &mut Machine,
    spec: &DeclSpec,
    ps: &[Term],
) -> Option<Vec<Vec<Term>>> {
    if !spec.well_formed() || ps.len() != spec.params {
        return None
    }
    let unit = mach.wt.sums.unit();
    let mut out = Vec::with_capacity(spec.ctors.len());
    for c in &spec.ctors {
        let mut summands = Vec::with_capacity(c.recs);
        for j in 0..c.recs {
            let gamma = c.rec_dom(j);
            summands.push(if gamma.is_empty() {
                unit.clone()
            } else {
                mach.telescope(env, spec.params, gamma)?.ty_of(ps.to_vec())
            });
        }
        out.push(summands);
    }
    Some(out)
}

/// **The fibre value of each constructor** — `Sum_{mᵢ}(Σ(z::γ₀) … Σ(z::γ_{mᵢ-1}))`,
/// the thesis's recursive-argument rule read straight off the spec.
///
/// `Σ(z::γⱼ)` is [`Telescope`]'s type at the declaration's parameters, and at
/// `γⱼ = ∅` it is the **one-point set**, spelled `1` rather than as the
/// telescope symbol `T(p⃗)` that `Telescope` at `k = 0` would hand back. The two
/// are provably equal — [`Telescope`]'s own base axiom says so — and choosing
/// the normal form is what keeps a plain declaration's fibre *literally*
/// `finord(mᵢ)`, since [`ISumSyms::finord`](crate::isum::ISumSyms::finord) is
/// `Sum_m` of `m` copies of `1`. So the plain case is not a branch in the rule,
/// only a choice of spelling for one set, and every constructor term in the
/// project is unchanged.
///
/// Exposed because it is the whole of what [`CtorSpec::rec_doms`](super::CtorSpec) buys and a
/// caller should be able to see it without building a carrier. A declaration
/// with a non-empty `γ` **does** build one: [`Inductive::build`] takes
/// [`RecArg::general`] over these summands at such a constructor, and
/// [`Ctor::mem`](super::Ctor) concludes
/// `∀g. (g ∈ fs(Σ(z::γ), ind(p⃗)) → c(g) ∈ ind(p⃗))`. The recursor path takes it
/// too, at a value motive and at a dependent one alike, and since this round
/// at a [mixed](Inductive::has_mixed_ctor) constructor as well. No shape of
/// recursive argument is declined by either recursor.
///
/// `None` when the spec is not [`DeclSpec::well_formed`] or a telescope
/// refuses.
pub fn fibre_values(
    env: &mut Env,
    mach: &mut Machine,
    spec: &DeclSpec,
    ps: &[Term],
) -> Option<Vec<Term>> {
    let per_ctor = fibre_summands(env, mach, spec, ps)?;
    per_ctor.iter().map(|summands| mach.syms.sum(summands)).collect()
}
