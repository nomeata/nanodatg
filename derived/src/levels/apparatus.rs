//! [`LevelPoly`] — the whole level-quantification apparatus, assembled over a
//! caller's [`Tower`] chain, plus the one closure lemma the pieces need
//! together: **`imax` stays in `ω`**.
//!
//! # Interface
//!
//! [`level_poly`] builds, over the tower's own `∅`/`succ`/`ω`/`U(·)`/pairing
//! symbols (nothing minted twice — the same one-chain rule every hub in this
//! crate follows):
//!
//! * [`crate::levels::ite0::Ite0`], [`crate::levels::order::Order`],
//!   [`crate::levels::utower::UTower`], [`crate::levels::srt::Srt`] — see each
//!   file's header; and
//!
//! ```text
//! ⊢ ∀u ∀v. ((u ∈ ω ∧ v ∈ ω) → ite0(v, ∅, u ∪ v) ∈ ω)   [LevelPoly::imax_in_omega]
//! ```
//!
//! — the interpretation of `imax` (`LEVELPOLY.md` §1.1) is a natural number
//! whenever its arguments are. With [`Order::max_in_omega`] and the `Peano`
//! base facts (`0 ∈ ω`, `succ`-closure) this closes the ω-membership of
//! **every** level expression's interpretation by structural recursion, which
//! is what a checker consuming this apparatus does per level (`LEVELPOLY.md`
//! §5.3 step 1).
//!
//! # Derivation of `imax_in_omega`
//!
//! Classical cases on `v = ∅`, the same Clavius-free route [`hyp_or_elim`]
//! affords once the disjunction is spelled: `or(P, ¬P)` unabbreviates to
//! `¬P → ¬P`, so excluded middle *is* [`imp_refl`]. Under `P` the term
//! computes to `∅` ([`crate::levels::ite0::Ite0::when_zero`]) and `0 ∈ ω` is
//! [`crate::recursion::OmegaCore::zero_mem`]; under `¬P` it computes to
//! `u ∪ v` and [`Order::max_in_omega`] finishes. Both transports are one
//! Leibniz step against the reversed equation.

use kernel::{Env, Formula, Term, Thm};

use crate::levels::ite0::{ite0, Ite0};
use crate::levels::order::{order, Order};
use crate::levels::srt::{srt, Srt};
use crate::levels::utower::{utower, UTower};
use crate::recursion::{app_of_graph, Rec};
use crate::separation::hyp_syl;
use crate::tower::Tower;
use crate::{a1i, com12, eq_symm_imp, gen_all, hyp_or_elim, imp_refl, inst_all, mpd_const, syl};

/// The assembled apparatus. See the module header.
pub struct LevelPoly {
    /// `ω`, `succ`, `app` and the Peano facts, over the tower's chain.
    pub r: Rec,
    /// The conditional term former.
    pub i: Ite0,
    /// Trichotomy, the case principle, and `max = ∪`.
    pub ord: Order,
    /// The internal universe ladder `lvl`.
    pub ut: UTower,
    /// `srt(n) = ite0(n, U₀, app(lvl, n))` and its laws.
    pub s: Srt,
    /// `⊢ ∀u ∀v. ((u ∈ ω ∧ v ∈ ω) → ite0(v, ∅, u ∪ v) ∈ ω)`.
    pub imax_in_omega: Thm,
}

impl LevelPoly {
    /// The term `ω`.
    pub fn omega(&self) -> Term { self.r.omega() }
    /// The term `∅`, which is also the level `0`.
    pub fn zero(&self) -> Term { self.r.zero() }
    /// The level `succ ℓ̂`.
    pub fn succ_of(&self, t: Term) -> Term { self.r.succ_of(t) }
    /// The level `max ℓ̂ ℓ̂'`, i.e. `ℓ̂ ∪ ℓ̂'`.
    pub fn max(&self, m: Term, n: Term) -> Term { self.ord.max(m, n) }
    /// The level `imax ℓ̂ ℓ̂'`, i.e. `ite0(ℓ̂', ∅, ℓ̂ ∪ ℓ̂')`.
    pub fn imax(&self, m: Term, n: Term) -> Term {
        self.i.at(n.clone(), self.zero(), self.max(m, n))
    }
    /// The sort `srt(ℓ̂)`.
    pub fn srt_at(&self, n: Term) -> Term { self.s.at(n) }
}

/// Assemble the apparatus over `tower`'s chain and derive
/// [`LevelPoly::imax_in_omega`].
pub fn level_poly(env: &mut Env, tower: &Tower) -> Option<LevelPoly> {
    let ap = tower.sums.ap.clone();
    let peano = tower.peano.clone();
    let aog = app_of_graph(env, &ap)?;
    let r = Rec { ap, peano, app_of_graph: aog };

    let i = ite0(env, &r.ap)?;
    let ord = order(env, &r)?;
    let ut = utower(env, &r, tower.space.lu, &tower.space.lu_ax, tower.space.pow, &tower.space.pow_ax)?;
    let s = srt(env, &r, &i, &ut, tower)?;

    let imax_in_omega = derive_imax_in_omega(env, &r, &i, &ord)?;

    Some(LevelPoly { r, i, ord, ut, s, imax_in_omega })
}

/// `⊢ ∀u ∀v. ((u ∈ ω ∧ v ∈ ω) → ite0(v, ∅, u ∪ v) ∈ ω)`.
fn derive_imax_in_omega(env: &mut Env, r: &Rec, i: &Ite0, ord: &Order) -> Option<Thm> {
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let (tu, tv) = (Term::var(u), Term::var(v));
    let omega = r.omega();
    let zero = r.zero();
    let muv = ord.max(tu.clone(), tv.clone());
    let t = i.at(tv.clone(), zero.clone(), muv.clone());

    let h = Formula::and(
        Formula::mem(tu.clone(), omega.clone()),
        Formula::mem(tv.clone(), omega.clone()),
    );
    let p = Formula::eq(tv.clone(), zero.clone());
    let np = Formula::not(p.clone());
    let goal = Formula::mem(t.clone(), omega.clone());

    // ── Case `P`: the term is `∅`, and `0 ∈ ω` ──────────────────────────────
    let wz = inst_all(&i.when_zero, &[tv.clone(), zero.clone(), muv.clone()])?;
    debug_assert_eq!(
        *wz.concl(),
        Formula::imp(p.clone(), Formula::eq(t.clone(), zero.clone())),
        "imax_in_omega: when_zero instantiated to an unexpected shape"
    );
    // `⊢ T = ∅ → (∅ ∈ ω → T ∈ ω)`, and `0 ∈ ω` closes the inner antecedent.
    let w = env.fresh_var();
    let leib_z = Thm::eq_leibniz(zero.clone(), t.clone(), w, Formula::mem(Term::var(w), omega.clone()));
    let sy = syl(&eq_symm_imp(env, t.clone(), zero.clone()), &leib_z)?;
    let t_eq_gives = mpd_const(&sy, &r.peano.core.zero_mem)?;
    let case_p = a1i(&syl(&wz, &t_eq_gives)?, h.clone());
    debug_assert_eq!(
        *case_p.concl(),
        Formula::imp(h.clone(), Formula::imp(p.clone(), goal.clone())),
        "imax_in_omega: the P-case has an unexpected shape"
    );

    // ── Case `¬P`: the term is `u ∪ v`, and `max_in_omega` finishes ─────────
    let wnz = inst_all(&i.when_nonzero, &[tv.clone(), zero, muv.clone()])?;
    debug_assert_eq!(
        *wnz.concl(),
        Formula::imp(np.clone(), Formula::eq(t.clone(), muv.clone())),
        "imax_in_omega: when_nonzero instantiated to an unexpected shape"
    );
    let h_muv = inst_all(&ord.max_in_omega, &[tu.clone(), tv.clone()])?;
    debug_assert_eq!(
        *h_muv.concl(),
        Formula::imp(h.clone(), Formula::mem(muv.clone(), omega.clone())),
        "imax_in_omega: max_in_omega instantiated to an unexpected shape"
    );
    let w2 = env.fresh_var();
    let leib_m = Thm::eq_leibniz(muv.clone(), t.clone(), w2, Formula::mem(Term::var(w2), omega.clone()));
    let sy2 = syl(&eq_symm_imp(env, t.clone(), muv), &leib_m)?;
    // `⊢ muv ∈ ω → (T = muv → T ∈ ω)`, then under `H`.
    let h_eq_gives = syl(&h_muv, &com12(&sy2)?)?;
    let case_np = hyp_syl(&a1i(&wnz, h.clone()), &h_eq_gives)?;
    debug_assert_eq!(
        *case_np.concl(),
        Formula::imp(h.clone(), Formula::imp(np.clone(), goal.clone())),
        "imax_in_omega: the ¬P-case has an unexpected shape"
    );

    // ── Excluded middle: `or(P, ¬P)` is `¬P → ¬P`, i.e. `imp_refl` ─────────
    let em = a1i(&imp_refl(np), h);
    debug_assert_eq!(
        em.concl().as_imp()?.1,
        Formula::or(p, Formula::not(Formula::eq(tv.clone(), r.zero()))),
        "imax_in_omega: excluded middle is not the or the case split eliminates"
    );
    let out = hyp_or_elim(&em, &case_p, &case_np)?;
    Some(gen_all(&[u, v], &out))
}
