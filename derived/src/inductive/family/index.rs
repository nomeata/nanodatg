//! **The index space** `Idx(p⃗)` — one [`Telescope`] over the index types, and
//! the power set the `good` recursion lands in.
//!
//! # What it is
//!
//! `INDEXED-DESIGN.md` §3.2:
//!
//! ```text
//! Idx(p⃗) := Σx₀:ι₀. … Σx_{ni−1}:ι_{ni−1}. 1        tup(x⃗) := ⟨x₀,⟨x₁,…⟨x_{ni−1},•⟩…⟩⟩
//! ```
//!
//! — the thesis's `(z₁,…,(zₙ,()))` tuple convention exactly, and therefore
//! **the same construction the constructors' tag payloads already use**. There
//! is nothing new here: [`crate::sigma::Telescope`] at `(np, [ι₀ … ι_{ni−1}])`
//! supplies `intro`, `proj_mem` and `eta`, and the [`Machine`]'s telescope
//! cache is keyed by `(np, β⃗)` so an index space whose types coincide with some
//! constructor's argument types is *the same* `Σ` nest, with the same symbols.
//!
//! # The one thing the design did not say, and it costs a hypothesis
//!
//! `Idx(p⃗)` is a genuine typing obligation, not a formality. The index
//! *symbols* `eᵢₖ` are opaque — the whole point of the `FnSym` convention is
//! that the derived layer never looks inside them — so nothing here can prove
//! `tup(e⃗ᵢ(p⃗,y⃗)) ∈ Idx(p⃗)`. It has to be *assumed*, and
//! [`super::carrier`]'s membership rule therefore carries `ni` extra
//! antecedents beyond the ones `INDEXED-DESIGN.md` §4.2 lists:
//!
//! ```text
//! eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, eᵢ₀(p⃗,y⃗) … eᵢ_{k−1}(p⃗,y⃗))          for k < ni
//! ```
//!
//! For `RBTree.red` those are `Color.r ∈ Color` (closed) and `n ∈ N` (the
//! plain field's own typing, which the checker already holds), so the cost is
//! real but is paid where the Lean typing derivation lives. It could not be
//! avoided by dropping the `w ∈ Idx(p⃗)` conjunct from `Gᵢ`: that conjunct is
//! what makes `Gᵢ` a *subset of a set*, and hence what makes
//! [`super::goodstep`]'s `step_typed` unconditional.
//!
//! # `ni = 0` is a rung of this construction, not a hole in it
//!
//! A declaration with no indices has the **one-point** index space:
//! `Idx(p⃗) = Σ⟨nothing⟩. 1`, which [`crate::sigma::Telescope`] at `(np, [])`
//! already builds, and `tup() = •`. Every line of the interface below survives
//! verbatim — the empty conjunction makes [`IndexSpace::intro`] the
//! hypothesis-free `⊢ ∀p⃗. • ∈ Idx(p⃗)`, and [`IndexSpace::proj_mem`] has no
//! entries because there is no index to project. Nothing is special-cased; the
//! telescope's `k = 0` case, which its own header records as "not a special
//! case anywhere below", carries it.
//!
//! **This is not a reversal of `INDEXED-DESIGN.md` §7.2**, and the distinction
//! is by *eliminator class*, not by index count:
//!
//! * **Class (T)** — the `good` route ([`super::good`], [`super::carrier`]).
//!   [`super::IndexedInductive::build`] still declines `ni = 0`, and should:
//!   `Bool`, `N` and `List` have a perfectly good W-type carrier already, so
//!   `ind(p⃗) = {s ∈ W : • ∈ …}` would re-derive the zero-gap fragment through
//!   a vacuous Separation for no benefit. §7.2's argument is about *this*
//!   route and is untouched.
//! * **Class (S)** — the `acc` route ([`super::le`]). There **is no other
//!   path**: `And`, `PUnit` and `ProjDataIndex` are subsingletons, their
//!   carriers are conditional singletons rather than W-types, and declining
//!   `ni = 0` here left them with no clause at all. Which is what
//!   [`super::le_prop`] exists to cash: at `ni = 0` the carrier collapses to
//!   `{q ∈ 1 : ψ}`, one [`crate::prop::conditional_singleton`].
//!
//! So the guard belongs on the class-(T) entry point, where it still is, and
//! not on the index space, where it was.
//!
//! # Interface
//!
//! ```text
//! Idx(p⃗)                                            [IndexSpace::idx]
//! 𝒫(Idx(p⃗))                                         [IndexSpace::target]
//! ⊢ ∀p⃗ ∀x⃗. ((⋀ₖ xₖ ∈ ιₖ(p⃗,x⃗<ₖ)) → tup(x⃗) ∈ Idx(p⃗))   [IndexSpace::intro]
//! ⊢ ∀p⃗ ∀q. (q ∈ Idx(p⃗) → compₖ(q) ∈ ιₖ(…))          [IndexSpace::proj_mem]
//! ⊢ ∀p⃗. Idx(p⃗) = 1                (only when ni = 0) [IndexSpace::point]
//! ```
//!
//! all at the declaration's **own** parameter variables, which is what lets a
//! theorem here compose with one about the carrier.

use std::rc::Rc;

use kernel::{Env, Term};

use crate::inductive::machine::Machine;
use crate::sigma::Telescope;

use super::spec::IndexedDeclSpec;

/// The index space of an indexed declaration.
pub struct IndexSpace {
    /// The `Σ` nest over `ι₀ … ι_{ni−1}`, shared with the [`Machine`]'s cache.
    pub telescope: Rc<Telescope>,
    /// `Idx(p⃗)`, at the declaration's parameters.
    pub idx: Term,
    /// `𝒫(Idx(p⃗))` — the `good` recursion's target set, and the only target
    /// at which its `step_typed` holds.
    pub target: Term,
}

impl IndexSpace {
    /// Build (or look up) the index space of `spec` at the parameter terms
    /// `ps`.
    ///
    /// **`ni = 0` is accepted**, and gives the one-point index space
    /// `Idx(p⃗) = 1` — see the module header for why the guard that used to sit
    /// here belongs on the class-(T) entry point instead.
    ///
    /// `None` when the spec is not
    /// [`well_formed`](IndexedDeclSpec::well_formed) or `ps` is not the
    /// declaration's parameter list.
    pub fn build(
        env: &mut Env,
        mach: &mut Machine,
        spec: &IndexedDeclSpec,
        ps: &[Term],
    ) -> Option<IndexSpace> {
        if !spec.well_formed() || ps.len() != spec.params() {
            return None
        }
        let telescope = mach.telescope(env, spec.params(), &spec.indices)?;
        let idx = telescope.ty_of(ps.to_vec());
        let target = Term::apply(mach.wt.sums.pow, vec![idx.clone()]);
        Some(IndexSpace { telescope, idx, target })
    }

    /// `⊢ ∀p⃗ ∀x⃗. ((⋀ₖ xₖ ∈ ιₖ(p⃗, x₀…x_{k−1})) → tup(x⃗) ∈ Idx(p⃗))` —
    /// [`Telescope::intro`], renamed for what it means here.
    pub fn intro(&self) -> &kernel::Thm { &self.telescope.intro }

    /// `⊢ ∀p⃗ ∀q. (q ∈ Idx(p⃗) → compₖ(q) ∈ ιₖ(p⃗, comp₀q …))`.
    pub fn proj_mem(&self, k: usize) -> Option<&kernel::Thm> { self.telescope.proj_mem.get(k) }

    /// `⊢ ∀p⃗. Idx(p⃗) = 1` — **`Some` iff the declaration has no indices**.
    ///
    /// [`crate::sigma::Telescope`]'s `base_ax` at `k = 0`, where the innermost
    /// level *is* the whole nest, renamed for what it means here. It is what
    /// turns [`super::le`]'s Separation `{q ∈ Idx(p⃗) : φ}` into a
    /// [`crate::prop::conditional_singleton`]; [`super::le_prop`] spends it,
    /// and nothing else does.
    ///
    /// The index count is read off the **telescope**, not off the spec, so the
    /// answer is about the nest this `IndexSpace` actually holds.
    pub fn point(&self) -> Option<&kernel::Thm> {
        self.telescope.betas.is_empty().then_some(&self.telescope.base_ax)
    }

    /// The number of indices, read off the telescope.
    pub fn num_indices(&self) -> usize { self.telescope.betas.len() }
}
