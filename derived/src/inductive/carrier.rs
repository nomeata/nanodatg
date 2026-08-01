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
//! B       := rec₊(λ_. finord(m₀), … rec₊(λ_. finord(m_{n-1}), ∅))  [crate::fibre]
//! carrier := W(A, B, u)
//! ```
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
//! [`super::shared`] for why that matters), and `E` is the **one flat
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
        let s = &mach.wt.sums;

        // ── the tag set and the fibre family ────────────────────────────────
        let counts: Vec<usize> = spec.ctors.iter().map(|c| c.recs).collect();
        let fibre = Fibre::new(
            env,
            s,
            &mach.cases,
            &mach.syms,
            &summands,
            &counts,
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

        // ── the recursive-argument functions, one per distinct arity ────────
        let mut recargs = Vec::with_capacity(n);
        for c in &spec.ctors {
            recargs.push(RecArg::new(
                env,
                s,
                &mach.cases,
                &mach.syms,
                &mach.pf,
                &mach.fin,
                &mach.wt.fs_mono,
                &mach.wt.empty_fun,
                c.recs,
            )?);
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
        Some(Inductive {
            spec: spec.clone(),
            params,
            telescopes,
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
        })
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
    pub fn ctor_term(
        &self,
        mach: &Machine,
        i: usize,
        args: &[Term],
        recs: &[Term],
    ) -> Option<Term> {
        if i >= self.ctors.len() || !self.is_over(mach) {
            return None
        }
        if args.len() != self.telescopes[i].betas.len() || recs.len() != self.recargs[i].m {
            return None
        }
        let s = &mach.wt.sums;
        Some(mach.wt.sup(
            mach.syms.inj(i, Telescope::tuple_of(s, args))?,
            RecArg::of(s, &mach.cases, recs),
        ))
    }

    /// `⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. ¬(ctor_i(y⃗,r⃗) = ctor_j(y⃗′,r⃗′))`, for `i ≠ j`.
    ///
    /// Derived on demand, because it depends on the *pair* `(i,j)`. `None` when
    /// `i == j`, where the statement is false, when either index is out of
    /// range, or when `mach` is not the apparatus this declaration was built
    /// over ([`Inductive::is_over`]) — in which case every step would resolve
    /// against the *other* machine's symbols and the theorem returned would be
    /// true of terms that are not these constructors.
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
pub(super) fn ctor_atoms(
    tel: &Telescope,
    ps: &[Term],
    ys: &[Term],
    rs: &[Term],
    carrier: &Term,
) -> Vec<Formula> {
    let mut atoms: Vec<Formula> = (0..ys.len())
        .map(|j| Formula::mem(ys[j].clone(), arg_type(tel, ps, ys, j)))
        .collect();
    atoms.extend(rs.iter().map(|r| Formula::mem(r.clone(), carrier.clone())));
    atoms
}
