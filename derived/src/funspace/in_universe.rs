//! The payoff: `fs(a,a) ∈ U(a)`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))   [funspace_in_universe_of]
//! ⊢ ∀a. fs(a,a) ∈ U(a)                            [funspace_in_universe]
//! ```
//!
//! The second is **unconditional**, and is what the tutorial's
//! `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` needs: `⟦Sort 0⟧` is a constant `P` and
//! `⟦Sort (u+1)⟧` is `U(⟦Sort u⟧)`, so the goal is `(P → P) ∈ U(P)`.
//!
//! [`Space`] is the ambient apparatus — pairing, union, power set and `U(x)`,
//! with the facts about `U(x)` the chain consumes — and [`Development`] is the
//! whole thing assembled once. Both exist because each piece is a *definitional
//! extension*: building one twice would introduce two different symbols and the
//! theorems would not compose. Callers need none of the derivations below.
//!
//! # The chain
//!
//! | step | lemma |
//! |---|---|
//! | `a ∈ U(a)` | [`crate::universe::mem_least_universe`] |
//! | `y ∈ U(x) → 𝒫y ∈ U(x)` | [`crate::funspace::pow_closed`] |
//! | `(y ∈ U(x) ∧ z ⊆ y) → z ∈ U(x)` | [`crate::funspace::sub_closed`] |
//! | `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` | [`crate::funspace::product_subset_pow_pow`] |
//! | `fs(a,b) ⊆ 𝒫(prod(a,b))` | [`crate::funspace::funspace_subset_pow_prod`] |
//! | `a ∪ a = a` | [`crate::union_singleton`] |
//!
//! # The two-argument case
//!
//! Everything above `a ∪ b` goes through, which is why
//! [`funspace_in_universe_of`] is stated in full with `(a ∪ b) ∈ U(c)` as its
//! antecedent. Discharging it from `a ∈ U(c)` and `b ∈ U(c)` is closure of
//! `U(c)` under binary unions, which is now
//! [`crate::universe::least_universe_bin_union`]; the discharge lives in
//! [`crate::funspace::pi_rule`], which is where the general
//! `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))` is proved. The
//! conditional form here is kept because `crate::ext` and `crate::checker`
//! consume it.
//!
//! At `b = c = a` the antecedent becomes `(a ∪ a) ∈ U(a)`, and `a ∪ a` is
//! `⋃{a,a}` — that is, `⋃{a}`, which [`crate::union_singleton`] equates with
//! `a`. So the binary union disappears rather than having to be closed over,
//! and [`funspace_in_universe`] is unconditional.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::{a1i, eq_symm, gen_all, hyp_mp, inst_all, singleton, syl};
use super::cartesian::{product, Product};
use super::pow_pow::{
    bin_union, mem_bin_union, pair_in_pow_pow, product_subset_pow_pow, upair_subset,
};
use super::space::Funspace;
use super::identity::{funspace_diagonal_members, identity_graph, identity_is_function};
use super::closure::{pow_closed, sub_closed};

/// The ambient apparatus: pairing, union, power set and the canonical universe
/// operator, with the facts about `U(x)` that the chain consumes.
///
/// Assembled once and passed around, because each piece is a *definitional
/// extension*: building it twice would introduce two different symbols and the
/// theorems would not compose.
#[derive(Clone)]
pub struct Space {
    /// Pairing and union.
    pub sets: Sets,
    /// The power set symbol.
    pub pow: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`.
    pub pow_ax: Thm,
    /// `⊢ ∀c. ⋃{c} = c` — what collapses `a ∪ a` to `a`.
    pub union_sing: Thm,
    /// `∅`, with no members; see [`crate::empty::empty`].
    pub empty: FnSym,
    /// `⊢ ∀z. ¬(z ∈ ∅)` — what makes Separation, and hence [`crate::funspace::funspace`],
    /// unconditional.
    pub empty_ax: Thm,
    /// `U(x)`, the least universe containing `x`.
    pub lu: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
    pub lu_ax: Thm,
    /// `⊢ ∀x. x ∈ U(x)`.
    pub mem_lu: Thm,
    /// `⊢ ∀x. C₂(U(x))`.
    pub c2: Thm,
    /// `⊢ ∀x. C₃(U(x))`.
    pub c3: Thm,
    /// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → (a = c ∧ b = d))`.
    pub pair_inj: Thm,
}

impl Space {
    /// Build everything, from the axioms up, over a **fresh** [`Sets`].
    ///
    /// Use [`Space::with_apply`] whenever an [`crate::funcs::Apply`] is also in
    /// play: this constructor mints its own pairing, and two pairings are two
    /// unrelated definitional extensions.
    pub fn new(env: &mut Env) -> Option<Space> {
        let sets = Sets::new(env);
        let (empty, empty_ax) = crate::empty::empty(env);
        Space::over(env, sets, empty, empty_ax)
    }

    /// Build everything over the pairing, empty set and ordered-pair facts an
    /// existing [`crate::funcs::Apply`] already has.
    ///
    /// **This is the constructor to use.** `Space::new` and `Apply::new` each
    /// mint their own [`Sets`], so a development that called both had *two*
    /// ordered-pair operations: `app`'s and `fs`'s. Nothing goes wrong while
    /// the two halves never meet, and everything goes wrong the moment a lemma
    /// mentions both — `f ∈ fs(a,b) → app(f,x) ∈ b` is exactly such a lemma.
    /// Assembling the `Space` by hand from `Apply`'s fields was the workaround;
    /// this is that workaround, done once and in the library, so that no client
    /// has to know which four fields to overwrite.
    ///
    /// The three shared theorems (`union_sing`, `empty_ax`, `pair_inj`) are
    /// taken from `ap` rather than re-derived, so they are literally the same
    /// theorems, about literally the same symbols.
    pub fn with_apply(env: &mut Env, ap: &crate::funcs::Apply) -> Option<Space> {
        let (pow, pow_ax) = crate::power(env);
        let (lu, lu_ax) = crate::universe::least_universe(env).ok()?;
        let mem_lu = crate::universe::mem_least_universe(env, lu, &lu_ax).ok()?;
        let c2 = crate::universe::least_universe_closed_sub(env, lu, &lu_ax).ok()?;
        let c3 = crate::universe::least_universe_closed_pow(env, lu, &lu_ax, pow, &pow_ax).ok()?;
        Some(Space {
            sets: ap.sets.clone(),
            pow,
            pow_ax,
            union_sing: ap.union_sing.clone(),
            empty: ap.empty,
            empty_ax: ap.empty_ax.clone(),
            lu,
            lu_ax,
            mem_lu,
            c2,
            c3,
            pair_inj: ap.pair_inj.clone(),
        })
    }

    /// The shared body of [`Space::new`]: everything that does not depend on
    /// where the pairing and the empty set came from.
    fn over(env: &mut Env, sets: Sets, empty: FnSym, empty_ax: Thm) -> Option<Space> {
        let (pow, pow_ax) = crate::power(env);
        let union_sing = crate::union_singleton(env, sets.up, &sets.up_ax, sets.un, &sets.un_ax)?;
        let (lu, lu_ax) = crate::universe::least_universe(env).ok()?;
        let mem_lu = crate::universe::mem_least_universe(env, lu, &lu_ax).ok()?;
        let c2 = crate::universe::least_universe_closed_sub(env, lu, &lu_ax).ok()?;
        let c3 = crate::universe::least_universe_closed_pow(env, lu, &lu_ax, pow, &pow_ax).ok()?;

        let mem_sing = crate::mem_singleton(env, sets.up, &sets.up_ax)?;
        let sing_inj = crate::singleton_inj(env, sets.up, &mem_sing)?;
        let fst = crate::opair_fst(env, sets.up, &sets.up_ax, &mem_sing, &sing_inj)?;
        let snd = crate::pairs::opair_snd(env, sets.up, &sets.up_ax, &mem_sing, &fst)?;
        let pair_inj = crate::pairs::opair_inj(env, sets.up, &fst, &snd)?;

        Some(Space { sets, pow, pow_ax, union_sing, empty, empty_ax, lu, lu_ax, mem_lu, c2, c3, pair_inj })
    }

    /// The term `U(x)`.
    pub fn universe_of(&self, x: Term) -> Term { Term::apply(self.lu, vec![x]) }
}

/// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))` — the general form, with the
/// one missing ingredient carried as an explicit antecedent.
///
/// Everything above `a ∪ b` is available: two power sets, the inclusion
/// [`product_subset_pow_pow`], one more power set, and
/// [`crate::funspace::funspace_subset_pow_prod`], each cashed in through [`pow_closed`] or
/// [`sub_closed`]. What is *not* available is `a ∪ b ∈ U(c)` from `a ∈ U(c)`
/// and `b ∈ U(c)`.
///
/// Before the transitivity clause was added to `ax_tarski` on 2026-07-31 that
/// was **false** — the countermodels at the end of `crate::universe` refuted
/// both the weakened antecedent and the weakened conclusion `fs(a,b) ∈ U(c)`.
/// It is now **proved**: `a ∪ b` is `⋃{a,b}`, pairing closure was already
/// available, and `⋃`-closure is
/// [`crate::universe::universe_union_closed`], so
/// [`crate::funspace::funspace_in_universe_pair`] discharges the antecedent.
/// This conditional form is kept because `crate::ext` and `crate::checker`
/// consume it, and because it is the sharpest statement of what the chain
/// above actually needs.
pub fn funspace_in_universe_of(
    env: &mut Env,
    s: &Space,
    p: &Product,
    prod_pp: &Thm,
    fs: &Funspace,
) -> Option<Thm> {
    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc) = (Term::var(a), Term::var(b), Term::var(c));
    let w = s.universe_of(tc.clone());

    let c2 = inst_all(&s.c2, std::slice::from_ref(&tc))?;
    let c3 = inst_all(&s.c3, std::slice::from_ref(&tc))?;
    let pc = pow_closed(env, s.pow, &s.pow_ax, &w, &c2, &c3)?;

    // `H := (a ∪ b) ∈ U(c)`, and two power sets above it.
    let un = bin_union(&s.sets, ta.clone(), tb.clone());
    let pu = Term::apply(s.pow, vec![un.clone()]);
    let ppu = Term::apply(s.pow, vec![pu.clone()]);
    let h_pu = inst_all(&pc, std::slice::from_ref(&un))?;
    let h = h_pu.concl().as_imp()?.0;
    debug_assert_eq!(h, Formula::mem(un, w.clone()));
    let h_ppu = syl(&h_pu, &inst_all(&pc, std::slice::from_ref(&pu))?)?;

    // `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` pulls the product in.
    let prod_t = p.of(ta.clone(), tb.clone());
    let prod_sub = inst_all(prod_pp, &[ta.clone(), tb.clone()])?;
    let h_prod = hyp_mp(
        &syl(&h_ppu, &sub_closed(&c2, &ppu, &prod_t)?)?,
        &a1i(&prod_sub, h.clone()),
    )?;

    // One more power set, then `fs(a,b) ⊆ 𝒫(prod(a,b))`.
    let pprod = Term::apply(s.pow, vec![prod_t.clone()]);
    let h_pprod = syl(&h_prod, &inst_all(&pc, std::slice::from_ref(&prod_t))?)?;
    let fs_t = fs.of(ta.clone(), tb.clone());
    let fs_sub = inst_all(&fs.fs_sub, &[ta.clone(), tb.clone()])?;
    let out = hyp_mp(
        &syl(&h_pprod, &sub_closed(&c2, &pprod, &fs_t)?)?,
        &a1i(&fs_sub, h.clone()),
    )?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(fs_t, w)),
        "funspace_in_universe_of: unexpected shape"
    );
    Some(gen_all(&[a, b, c], &out))
}

/// `⊢ ∀a. fs(a,a) ∈ U(a)` — **the payoff**: the function space `a → a` lands in
/// the least universe containing `a`.
///
/// This is what the tutorial's `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` needs: `⟦Sort 0⟧` is
/// a constant `P` and `⟦Sort (u+1)⟧` is `U(⟦Sort u⟧)`, so the goal is
/// `(P → P) ∈ U(P)`.
///
/// [`funspace_in_universe_of`] does the work; all that is left is to discharge
/// its antecedent at `b = c = a`, where it reads `(a ∪ a) ∈ U(a)`. And `a ∪ a`
/// is `⋃{a,a}` — that is, `⋃{a}` — which [`crate::union_singleton`] equates
/// with `a`, while `a ∈ U(a)` is [`crate::universe::mem_least_universe`]. The
/// binary union that blocks the general case simply disappears.
pub fn funspace_in_universe(
    env: &mut Env,
    s: &Space,
    fs: &Funspace,
    general: &Thm,
) -> Option<Thm> {
    let a = env.fresh_var();
    let ta = Term::var(a);
    let w = s.universe_of(ta.clone());

    let uaa = bin_union(&s.sets, ta.clone(), ta.clone());
    debug_assert_eq!(
        uaa,
        s.sets.union_of(singleton(s.sets.up, ta.clone())),
        "a ∪ a is not ⋃{{a}}"
    );
    let eq_uaa = inst_all(&s.union_sing, std::slice::from_ref(&ta))?;
    debug_assert_eq!(*eq_uaa.concl(), Formula::eq(uaa.clone(), ta.clone()));

    // `⋃{a} ∈ U(a)`, by moving `a ∈ U(a)` across the equation.
    let a_in = inst_all(&s.mem_lu, std::slice::from_ref(&ta))?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ta.clone(),
        uaa,
        hole,
        Formula::mem(Term::var(hole), w.clone()),
    );
    let un_in = Thm::mp(&Thm::mp(&leib, &eq_symm(env, &eq_uaa)?)?, &a_in)?;

    let inst = inst_all(general, &[ta.clone(), ta.clone(), ta.clone()])?;
    let out = Thm::mp(&inst, &un_in)?;
    // Checked at run time, not asserted: `fs` enters the derivation *nowhere
    // else*, so this comparison is the only thing that makes the returned
    // theorem a statement about the caller's function space rather than about
    // whatever `general`'s consequent happens to mention. Handing in
    // `product_in_universe_of`, whose antecedent has the same shape, otherwise
    // yields `⊢ ∀a. prod(a,a) ∈ U(a)` from a function whose header says
    // `fs(a,a)`.
    if !general.hyps().is_empty()
        || !out.hyps().is_empty()
        || *out.concl() != Formula::mem(fs.of(ta.clone(), ta), w)
    {
        return None
    }
    Some(Thm::gen(a, &out))
}

/// The whole development: every symbol, every theorem, and the payoff.
pub struct Development {
    /// Pairing, union, power set, `U(x)`.
    pub space: Space,
    /// The Cartesian product.
    pub product: Product,
    /// `⊢ ∀a ∀b. prod(a,b) ⊆ 𝒫𝒫(a ∪ b)`.
    pub prod_sub: Thm,
    /// The function space.
    pub funspace: Funspace,
    /// `id(a) = { ⟨x,x⟩ : x ∈ a }`.
    pub id: FnSym,
    /// `⊢ ∀a ∀z. (z ∈ id(a) ↔ ∃x. (x ∈ a ∧ z = ⟨x,x⟩))`.
    pub id_ax: Thm,
    /// `⊢ ∀a. isfun(id(a))`.
    pub id_fun: Thm,
    /// `⊢ ∀a ∀f. (f ∈ fs(a,a) ↔ isfun(f))` — the `b := a` instance of
    /// [`Funspace::fs_ax`], which is itself unconditional.
    pub diagonal_members: Thm,
    /// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))`.
    pub in_universe_of: Thm,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`.
    pub in_universe: Thm,
}

impl Development {
    /// Build it all, over a fresh [`Space`] — and hence a fresh [`Sets`].
    pub fn new(env: &mut Env) -> Option<Development> {
        let space = Space::new(env)?;
        Development::over(env, space)
    }

    /// Build it all over the pairing an existing [`crate::funcs::Apply`]
    /// already has, so that `app` and `fs` speak about the same ordered pair.
    ///
    /// [`Space::with_apply`] does the sharing; this is the same thing carried
    /// through the product, the function space and the universe chain.
    pub fn with_apply(env: &mut Env, ap: &crate::funcs::Apply) -> Option<Development> {
        let space = Space::with_apply(env, ap)?;
        Development::over(env, space)
    }

    /// Everything above the [`Space`], which is where the two constructors
    /// differ and the only place the choice of pairing is made.
    pub fn over(env: &mut Env, space: Space) -> Option<Development> {
        let product = product(env, &space.sets)?;
        let up_sub = upair_subset(env, &space.sets)?;
        let pair_pp = pair_in_pow_pow(env, &space.sets, space.pow, &space.pow_ax, &up_sub)?;
        let (ml, mr) = mem_bin_union(env, &space.sets)?;
        let prod_sub = product_subset_pow_pow(
            env,
            &space.sets,
            space.pow,
            &product,
            &pair_pp,
            &ml,
            &mr,
        )?;
        let funspace =
            Funspace::new(env, &space.sets, space.pow, &space.pow_ax, &product, &space.empty_ax)?;

        let (id, id_ax) = identity_graph(env, &space.sets)?;
        let id_fun =
            identity_is_function(env, &space.sets, &product, id, &id_ax, &space.pair_inj)?;
        let diagonal_members = funspace_diagonal_members(env, &funspace.fs_ax)?;

        let in_universe_of =
            funspace_in_universe_of(env, &space, &product, &prod_sub, &funspace)?;
        let in_universe = funspace_in_universe(env, &space, &funspace, &in_universe_of)?;
        Some(Development {
            space,
            product,
            prod_sub,
            funspace,
            id,
            id_ax,
            id_fun,
            diagonal_members,
            in_universe_of,
            in_universe,
        })
    }
}
