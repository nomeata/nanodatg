//! The binary sum `A + B`, its two injections, and the apparatus [`Sums`] that
//! carries every symbol the development shares.
//!
//! # Interface
//!
//! [`Sums::new`] builds everything from the axioms up; [`Sums::over`] does the
//! same over a **caller-supplied** pairing, power set, product and function
//! space, which is what a client already holding those must use. Its fields are
//! the theorems, so a caller reads them off the struct and never calls the
//! functions below directly:
//!
//! ```text
//! ⊢ ∀A ∀B ∀z. (z ∈ A + B ↔ ((∃a. (a ∈ A ∧ z = inl(a))) ∨ (∃b. (b ∈ B ∧ z = inr(b)))))   [sum_ax]
//! ⊢ ∀A ∀B ∀a. (a ∈ A → inl(a) ∈ A + B)                                                  [inl_mem]
//! ⊢ ∀A ∀B ∀b. (b ∈ B → inr(b) ∈ A + B)                                                  [inr_mem]
//! ⊢ ∀A ∀B ∀p. (p ∈ A + B → (… ∨ …))                                                     [sum_cases]
//! ⊢ ∀a ∀b. ¬(inl(a) = inr(b))                                                           [disjoint]
//! ⊢ ∀a ∀a′. (inl(a) = inl(a′) → a = a′)                                                 [inl_inj]
//! ⊢ ∀b ∀b′. (inr(b) = inr(b′) → b = b′)                                                 [inr_inj]
//! ```
//!
//! plus the four unit-type facts from [`super::unit_type`] and
//! [`super::pair_in_product`], stored as fields so that one `Sums` answers
//! every question the eliminator in [`super::cases`] asks.
//!
//! Term constructors: [`Sums::zero`], [`Sums::point`], [`Sums::unit`],
//! [`Sums::inl`], [`Sums::inr`], [`Sums::sum_of`].
//!
//! # Nothing here is an axiom
//!
//! `0` and the point `•` are `∅`, `1` is `{∅}`, and `A + B` is
//! `({∅} × A) ∪ ({1} × B)`. The symbol `sum` is an **explicit** definitional
//! extension ([`sum_symbol`]), so it costs nothing: the thing being named is
//! already a term and [`crate::exists_unique_eq`] discharges the `∃!` premise
//! for free.
//!
//! # The master lemma
//!
//! All the work sits in [`sum_members`], which is three rewrites composed: the
//! defining equation moves `z ∈ A + B` to `z` in the union,
//! [`super::mem_bin_union_iff`] splits the union into a disjunction, and
//! [`super::tagged_copy_members`] identifies each half as a tagged copy — the
//! left at tag `∅`, the right at tag `1`.
//!
//! Once it is proved, the four requested facts about `A + B` are corollaries of
//! it and of the Kuratowski pair's injectivity: [`injection_mem`] chooses a
//! disjunct, [`sum_case_analysis`] reads one off, [`injection_inj`] and
//! [`sum_disjoint`] cancel or compare a tag. Disjointness is the only one that
//! reaches outside, to [`super::tags_distinct`].
//!
//! # Why `Sums` is threaded rather than rebuilt
//!
//! Building the apparatus twice would introduce two different `upair` symbols,
//! and then `⟨a,b⟩` would name two different terms and none of the theorems
//! would compose — which is why [`crate::funcs::Apply`] is threaded through
//! rather than rebuilt, and why [`Sums::over`] exists at all. It is the same
//! hazard [`Wtype::over`](crate::wtype::Wtype::over) and
//! [`Bound::over`](crate::bound::Bound::over) exist to avoid.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{or_intro_left, or_intro_right, Apply};
use crate::funspace::{self as fsp, Funspace, Product};
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm, exists_intro_imp, gen_all, hyp_and, iff_mp,
    iff_mpr, imp_refl, inst_all, opair, singleton, syl,
};

use super::membership::{mem_bin_union_iff, pair_in_product, tagged_copy_members};
use super::shared::{carry_mem, iff_trans, inl_of, inr_of, or_iff, sum_body, unit_of, zero_of};
use super::unit_type::{tags_distinct, unit_eta, unit_mem, zero_empty};

/// Everything the sum construction needs, built once so that all the symbols
/// come from a single definitional extension.
///
/// Building it twice would introduce two different `upair` symbols, and then
/// `⟨a,b⟩` would name two different terms and none of the theorems would
/// compose — which is why [`crate::funcs::Apply`] is threaded through rather
/// than rebuilt.
#[derive(Clone)]
pub struct Sums {
    /// Pairing, union, `∅`, `coll` and `app`.
    pub ap: Apply,
    /// The power set symbol.
    pub pow: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`.
    pub pow_ax: Thm,
    /// The Cartesian product.
    pub prod: Product,
    /// The function space.
    pub fs: Funspace,
    /// `⊢ • ∈ 1`, i.e. `⊢ ∅ ∈ {∅}`.
    pub unit_mem: Thm,
    /// `⊢ ∀x. (x ∈ 1 → x = •)` — `1` is a subsingleton.
    pub unit_eta: Thm,
    /// `⊢ ¬(∃x. x ∈ 0)` — `0` is empty. Reused from [`crate::empty::empty`].
    pub zero_empty: Thm,
    /// `⊢ ¬(∅ = 1)` — the two tags are different sets.
    pub tags_distinct: Thm,
    /// `sum(A,B) = A + B`.
    pub sum: FnSym,
    /// `⊢ ∀A ∀B. sum(A,B) = ({∅} × A) ∪ ({1} × B)` — the defining equation.
    pub sum_def: Thm,
    /// `⊢ ∀A ∀B ∀z. (z ∈ A + B ↔ ((∃a. (a ∈ A ∧ z = inl(a))) ∨ (∃b. (b ∈ B ∧ z = inr(b)))))`.
    pub sum_ax: Thm,
    /// `⊢ ∀A ∀B ∀a. (a ∈ A → inl(a) ∈ A + B)`.
    pub inl_mem: Thm,
    /// `⊢ ∀A ∀B ∀b. (b ∈ B → inr(b) ∈ A + B)`.
    pub inr_mem: Thm,
    /// `⊢ ∀a ∀b. ¬(inl(a) = inr(b))`.
    pub disjoint: Thm,
    /// `⊢ ∀a ∀a′. (inl(a) = inl(a′) → a = a′)`.
    pub inl_inj: Thm,
    /// `⊢ ∀b ∀b′. (inr(b) = inr(b′) → b = b′)`.
    pub inr_inj: Thm,
    /// `⊢ ∀A ∀B ∀p. (p ∈ A + B → ((∃a. (a ∈ A ∧ p = inl(a))) ∨ (∃b. (b ∈ B ∧ p = inr(b)))))`.
    pub sum_cases: Thm,
    /// `⊢ ∀A ∀T ∀u ∀v. (⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T))`.
    pub pair_in_prod: Thm,
}

impl Sums {
    /// Introduce every symbol and derive every theorem, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Sums> {
        let ap = Apply::new(env)?;
        let (pow, pow_ax) = crate::power(env);
        let prod = fsp::product(env, &ap.sets)?;
        let fs = Funspace::new(env, &ap.sets, pow, &pow_ax, &prod, &ap.empty_ax)?;
        Sums::over(env, ap, pow, pow_ax, prod, fs)
    }

    /// The same, over a **caller-supplied** pairing, power set, product and
    /// function space, so that a client already holding those gets a sum type
    /// whose terms compose with everything else built over them.
    ///
    /// Building them afresh instead would mint a *second* `⟨·,·⟩` and a second
    /// `fs`, and then no theorem here would speak of the same operators as the
    /// caller's — the same hazard [`Wtype::over`](crate::wtype::Wtype::over)
    /// and [`Bound::over`](crate::bound::Bound::over) exist to avoid.
    pub fn over(
        env: &mut Env,
        ap: Apply,
        pow: FnSym,
        pow_ax: Thm,
        prod: Product,
        fs: Funspace,
    ) -> Option<Sums> {
        let unit_mem = unit_mem(&ap)?;
        let unit_eta = unit_eta(env, &ap)?;
        let zero_empty = zero_empty(&ap);
        let tags_distinct = tags_distinct(env, &ap, &unit_mem)?;

        let (sum, sum_def) = sum_symbol(env, &ap, &prod)?;
        let tagged = tagged_copy_members(env, &ap.sets, &ap.mem_sing, &prod)?;
        let bin = mem_bin_union_iff(env, &ap.sets)?;
        let sum_ax = sum_members(env, &ap, &prod, sum, &sum_def, &tagged, &bin)?;

        let inl_mem = injection_mem(env, &ap, sum, &sum_ax, true)?;
        let inr_mem = injection_mem(env, &ap, sum, &sum_ax, false)?;
        let disjoint = sum_disjoint(env, &ap, &tags_distinct)?;
        let inl_inj = injection_inj(env, &ap, true)?;
        let inr_inj = injection_inj(env, &ap, false)?;
        let sum_cases = sum_case_analysis(env, sum, &sum_ax)?;
        let pair_in_prod = pair_in_product(env, &ap, &prod)?;

        Some(Sums {
            ap,
            pow,
            pow_ax,
            prod,
            fs,
            unit_mem,
            unit_eta,
            zero_empty,
            tags_distinct,
            sum,
            sum_def,
            sum_ax,
            inl_mem,
            inr_mem,
            disjoint,
            inl_inj,
            inr_inj,
            sum_cases,
            pair_in_prod,
        })
    }

    /// The term `∅`, which is both `0` and the point `•` of the unit type.
    pub fn zero(&self) -> Term { zero_of(&self.ap) }

    /// The point `• = ∅`, the sole inhabitant of `1`.
    pub fn point(&self) -> Term { self.zero() }

    /// The unit type `1 = {∅}`.
    pub fn unit(&self) -> Term { unit_of(&self.ap) }

    /// The left tag, `∅`.
    pub fn tag_l(&self) -> Term { self.zero() }

    /// The right tag, `1 = {∅}`.
    pub fn tag_r(&self) -> Term { self.unit() }

    /// `inl(a) = ⟨∅, a⟩`.
    pub fn inl(&self, a: Term) -> Term { inl_of(&self.ap, a) }

    /// `inr(b) = ⟨1, b⟩`.
    pub fn inr(&self, b: Term) -> Term { inr_of(&self.ap, b) }

    /// The term `A + B`.
    pub fn sum_of(&self, a: Term, b: Term) -> Term { Term::apply(self.sum, vec![a, b]) }

    /// `({∅} × A) ∪ ({1} × B)`, the term `A + B` abbreviates.
    pub fn sum_term(&self, a: Term, b: Term) -> Term { sum_body(&self.ap, &self.prod, a, b) }
}

/// Introduce `sum(A,B) = ({∅} × A) ∪ ({1} × B)`, with
/// `⊢ ∀A ∀B. sum(A,B) = ({∅} × A) ∪ ({1} × B)`.
///
/// An **explicit** definition, so it costs nothing: the thing being named is
/// already a term, and [`crate::exists_unique_eq`] discharges the `∃!` premise
/// for free. All the work sits in [`sum_members`], which unfolds it.
pub fn sum_symbol(env: &mut Env, ap: &Apply, p: &Product) -> Option<(FnSym, Thm)> {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let body = sum_body(ap, p, Term::var(a), Term::var(b));
    crate::define_abbrev(env, &[a, b], &body)
}

/// `⊢ ∀A ∀B ∀z. (z ∈ A + B ↔ ((∃a. (a ∈ A ∧ z = inl(a))) ∨ (∃b. (b ∈ B ∧ z = inr(b)))))`
/// — **the master lemma**; every other fact about `A + B` is a corollary.
///
/// Three rewrites composed: the defining equation moves `z ∈ A + B` to `z` in
/// the union, [`mem_bin_union_iff`] splits the union into a disjunction, and
/// [`tagged_copy_members`] identifies each half as a tagged copy — the left at
/// tag `∅`, the right at tag `1`.
pub fn sum_members(
    env: &mut Env,
    ap: &Apply,
    p: &Product,
    sum: FnSym,
    sum_def: &Thm,
    tagged: &Thm,
    bin: &Thm,
) -> Option<Thm> {
    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));

    let sum_t = Term::apply(sum, vec![ta.clone(), tb.clone()]);
    let body = sum_body(ap, p, ta.clone(), tb.clone());
    let left = p.of(singleton(ap.sets.up, zero_of(ap)), ta.clone());
    let right = p.of(singleton(ap.sets.up, unit_of(ap)), tb.clone());

    // ── z ∈ sum(A,B) ↔ z ∈ ({∅}×A) ∪ ({1}×B) ─────────────────────────────────
    let def_at = inst_all(sum_def, &[ta.clone(), tb.clone()])?;
    debug_assert_eq!(*def_at.concl(), Formula::eq(sum_t.clone(), body.clone()));
    let unfold = and_intro(
        &Thm::mp(&carry_mem(env, tz.clone(), sum_t.clone(), body.clone()), &def_at)?,
        &Thm::mp(&carry_mem(env, tz.clone(), body.clone(), sum_t.clone()), &eq_symm(env, &def_at)?)?,
    );

    // ── … ↔ (z ∈ {∅}×A ∨ z ∈ {1}×B) ──────────────────────────────────────────
    let split = inst_all(bin, &[left.clone(), right.clone(), tz.clone()])?;

    // ── … ↔ (∃a. (a ∈ A ∧ z = inl(a)) ∨ ∃b. (b ∈ B ∧ z = inr(b))) ────────────
    let l_iff = inst_all(tagged, &[zero_of(ap), ta.clone(), tz.clone()])?;
    let r_iff = inst_all(tagged, &[unit_of(ap), tb.clone(), tz.clone()])?;
    let sides = or_iff(&l_iff, &r_iff)?;

    let out = iff_trans(&unfold, &iff_trans(&split, &sides)?)?;

    // State the conclusion independently and insist the derivation matched it.
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let want = Formula::or(
        Formula::exists(
            av,
            Formula::and(
                Formula::mem(Term::var(av), ta.clone()),
                Formula::eq(tz.clone(), inl_of(ap, Term::var(av))),
            ),
        ),
        Formula::exists(
            bv,
            Formula::and(
                Formula::mem(Term::var(bv), tb.clone()),
                Formula::eq(tz.clone(), inr_of(ap, Term::var(bv))),
            ),
        ),
    );
    debug_assert_eq!(
        *out.concl(),
        Formula::iff(Formula::mem(tz, sum_t), want),
        "sum_members: unexpected shape"
    );
    Some(gen_all(&[a, b, z], &out))
}

/// `⊢ ∀A ∀B ∀a. (a ∈ A → inl(a) ∈ A + B)` when `left`, and the `inr` mirror
/// image otherwise.
///
/// The witness is the element itself and the equation is reflexivity, so all
/// that happens is choosing the correct disjunct of [`sum_members`].
pub fn injection_mem(
    env: &mut Env,
    ap: &Apply,
    sum: FnSym,
    sum_ax: &Thm,
    left: bool,
) -> Option<Thm> {
    let (a, b, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx) = (Term::var(a), Term::var(b), Term::var(x));
    let sum_t = Term::apply(sum, vec![ta.clone(), tb.clone()]);

    let inj = |t: Term| if left { inl_of(ap, t) } else { inr_of(ap, t) };
    let dom = if left { ta.clone() } else { tb.clone() };
    let h = Formula::mem(tx.clone(), dom.clone());
    let elem = inj(tx.clone());

    let at = inst_all(sum_ax, &[ta.clone(), tb.clone(), elem.clone()])?;
    // The two disjuncts, read off the master lemma rather than rebuilt, so that
    // the disjunct chosen below is provably the one it names.
    let (disj_l, disj_r) = {
        let (_, cond) = iff_mp(&at)?.concl().as_imp()?;
        let (nl, r) = cond.as_imp()?;
        (nl.as_imp()?.0, r)
    };

    // The witness variable must be fresh: binding `x` would abstract the `x` in
    // the fixed left-hand side `inl(x)` as well.
    let w = env.fresh_var();
    let tw = Term::var(w);
    let body = Formula::and(
        Formula::mem(tw.clone(), dom),
        Formula::eq(elem.clone(), inj(tw)),
    );
    let h_witness = hyp_and(&imp_refl(h.clone()), &a1i(&Thm::eq_refl(elem.clone()), h.clone()))?;
    let h_ex = syl(&h_witness, &exists_intro_imp(w, body, tx.clone())?)?;

    let h_disj = if left {
        syl(&h_ex, &or_intro_left(disj_l, disj_r))?
    } else {
        syl(&h_ex, &or_intro_right(disj_l, disj_r))?
    };
    let out = syl(&h_disj, &iff_mpr(&at)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(elem, sum_t)),
        "injection_mem: unexpected shape"
    );
    Some(gen_all(&[a, b, x], &out))
}

/// `⊢ ∀A ∀B ∀p. (p ∈ A + B → ((∃a. (a ∈ A ∧ p = inl(a))) ∨ (∃b. (b ∈ B ∧ p = inr(b)))))`
/// — case analysis, i.e. **no junk**: nothing is in `A + B` but the images of
/// the two injections.
pub fn sum_case_analysis(env: &mut Env, sum: FnSym, sum_ax: &Thm) -> Option<Thm> {
    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let at = inst_all(sum_ax, &[ta.clone(), tb.clone(), tz.clone()])?;
    let out = iff_mp(&at)?;
    debug_assert_eq!(
        out.concl().as_imp()?.0,
        Formula::mem(tz, Term::apply(sum, vec![ta, tb])),
        "sum_case_analysis: unexpected shape"
    );
    Some(gen_all(&[a, b, z], &out))
}

/// `⊢ ∀a ∀b. ¬(inl(a) = inr(b))` — the two injections are disjoint.
///
/// Injectivity of the Kuratowski pair reduces the equation to `∅ = 1`, which
/// [`tags_distinct`] refutes. This is the only place the choice of tags
/// matters, and it is why that lemma is proved rather than assumed.
pub fn sum_disjoint(env: &mut Env, ap: &Apply, tags: &Thm) -> Option<Thm> {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let (e, u) = (zero_of(ap), unit_of(ap));

    let inj = inst_all(&ap.pair_inj, &[e.clone(), ta.clone(), u.clone(), tb.clone()])?;
    let tags_eq = syl(&inj, &and_left(Formula::eq(e.clone(), u.clone()), Formula::eq(ta.clone(), tb.clone())))?;
    let out = syl(&tags_eq, tags)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(inl_of(ap, ta.clone()), inr_of(ap, tb.clone()))),
        "sum_disjoint: unexpected shape"
    );
    Some(gen_all(&[a, b], &out))
}

/// `⊢ ∀a ∀a′. (inl(a) = inl(a′) → a = a′)` when `left`, and the `inr` mirror
/// image otherwise — the injections are injective.
pub fn injection_inj(env: &mut Env, ap: &Apply, left: bool) -> Option<Thm> {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let tag = if left { zero_of(ap) } else { unit_of(ap) };

    let inj = inst_all(&ap.pair_inj, &[tag.clone(), tx.clone(), tag.clone(), ty.clone()])?;
    let out = syl(
        &inj,
        &and_right(Formula::eq(tag.clone(), tag.clone()), Formula::eq(tx.clone(), ty.clone())),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::eq(opair(ap.sets.up, tag.clone(), tx.clone()), opair(ap.sets.up, tag, ty.clone())),
            Formula::eq(tx, ty)
        ),
        "injection_inj: unexpected shape"
    );
    Some(gen_all(&[x, y], &out))
}
