//! **`⟦N⟧ ∈ U₁`** — step (g), the deliverable of [`crate::cumul`].
//!
//! # Interface
//!
//! Writing `A` for `1 + 1`, `B` for [`crate::wnat`]'s fibre family, `N` for
//! `W(A, B, U(A))` and `U₁` for `U(ω)`, [`NatUniverse`] carries
//!
//! ```text
//! ⊢ 1 = succ 0                                        [NatUniverse::one_is_succ_zero]
//! ⊢ 1 ∈ ω                                             [NatUniverse::one_in_omega]
//! ⊢ (1 + 1) ∈ U₁                                      [NatUniverse::tags_in_u1]
//! ⊢ S ∈ U(A)   and   ⊢ S ∈ U₁     for S := A ∪ 1      [NatUniverse::seed_in_bound, seed_in_u1]
//! ⊢ Fin(A,B)                                          [NatUniverse::fin]
//! ⊢ N ∈ U₁                                            [NatUniverse::nat_in_u1]
//! ```
//!
//! all at **closed terms**, with no hypothesis whatsoever, together with
//! [`crate::wnat::Nat`] itself — so `⊢ ⟨inl •,∅⟩ ∈ N`, `⊢ ∀n ∈ N. succ n ∈ N`
//! and `⊢ ∀n. ¬(zero = succ n)` are available at the same terms and the
//! membership is provably not about a set with fewer than two elements.
//!
//! "With no hypothesis whatsoever" is **checked, on the way in and on the way
//! out**: [`NatMem::over`] refuses a `Nat` whose fibre equations rest on an
//! assumption and refuses to return a `NatMem` any of whose theorems does
//! ([`NatMem::is_unconditional`]). A conclusion comparison cannot tell the two
//! apart, and this is the module the checker reads its `⊢ ⟦N⟧ ∈ U₁` from.
//!
//! # The seed is `A ∪ 1`, not `A ∪ ⋃⋃⋃B`
//!
//! The closing note of [`crate::cumul`] proposed the generic seed
//! `S := A ∪ ⋃⋃⋃B`, which works for any family given as a set of pairs. At a
//! concrete W-type it is unnecessary and more expensive: the two obligations
//! [`super::tower_closed`] actually carries are `A ⊆ S` and
//! `∀a ∈ A. B(a) ⊆ S`, and for `N` the fibres are `0 = ∅` and `1`, so
//!
//! ```text
//! S := (1 + 1) ∪ 1
//! ```
//! discharges both — `∅ ⊆ S` for free and `1 ⊆ S` by the right introduction of
//! the binary union. `⋃⋃⋃B` would additionally require `B` to be known as a
//! *set of pairs with `A` in its domain*, which is two more hypotheses of
//! exactly the kind the seed was meant to remove.
//!
//! # `1 ∈ ω` is one Extensionality, and it is the only one
//!
//! The fibre of `succ` is `1 = {∅}`, and `super::bounded` needs it to be a von
//! Neumann natural. `succ(n)` is `n ∪ {n}`, so `succ 0` is `∅ ∪ {∅}` and
//! `1 = {∅}`: two different terms for the same set, related by one use of
//! Extensionality (`z ∈ ∅` is absurd, so `z ∈ succ 0 ↔ z = ∅ ↔ z ∈ 1`). This is
//! the single equality-of-sets step in the whole chain, exactly as the closing
//! note predicted.
//!
//! # The two universes at their concrete values
//!
//! `⊢ N ∈ U₁` is [`super::WMem::w_in_universe`] at `c := A` and `d := ω`, and
//! the two are different for a reason a countermodel forces — see
//! [`super::wmem`]. What has to be produced here is `A ∈ U₁`, and the route is
//! the sum's *defining equation* rather than its membership condition:
//! `A + B` abbreviates `({∅} × A) ∪ ({1} × B)`, and `U₁` is closed under
//! products, binary unions and pairing, so `1 + 1 ∈ U₁` is five instantiations
//! and one rewrite. No Replacement instance and no case analysis.

use kernel::{Env, Formula, Term, Thm};

use crate::bound::Bound;
use crate::enums::empty_in_least_universe;
use crate::funspace::bin_union;
use crate::point_fun::PointFun;
use crate::sums::Cases;
use crate::wnat::Nat;
use crate::{
    a1i, and_intro, and_left, and_right, com12, eq_symm, eq_symm_imp, ex_falso, exists_elim_imp,
    hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all, singleton, syl,
};
use crate::separation::or_intro_right;

use super::chain::Chain;

/// [`crate::wnat`]'s `N`, and the proof that it is a member of `U₁`.
pub struct NatUniverse {
    /// The whole of [`crate::wnat`], over the chain's own symbols.
    pub nat: Nat,
    /// The seed `S = (1+1) ∪ 1`.
    pub seed: Term,
    /// `⊢ 1 = succ 0` — the one Extensionality.
    pub one_is_succ_zero: Thm,
    /// `⊢ 1 ∈ ω`.
    pub one_in_omega: Thm,
    /// `⊢ (1+1) ∈ U₁`.
    pub tags_in_u1: Thm,
    /// `⊢ S ∈ U(1+1)` — the seed is inside the *bound*.
    pub seed_in_bound: Thm,
    /// `⊢ S ∈ U₁` — and inside the universe `N` lives in.
    pub seed_in_u1: Thm,
    /// `⊢ (1+1) ⊆ S ∧ ∀a. (a ∈ 1+1 → (B(a) ⊆ S ∧ B(a) ∈ ω))` — the finite
    /// branching hypothesis, discharged.
    pub fin: Thm,
    /// **`⊢ N ∈ U₁`.**
    pub nat_in_u1: Thm,
}

/// Everything [`NatUniverse`] proves **about an `N` it was handed**, rather than
/// about one it built itself.
///
/// [`NatUniverse::new`] is this plus a freshly constructed [`Nat`]. The split
/// exists because a client that already has an `N` — the checker, whose
/// `⟦N⟧` is an abbreviation for one particular `W(1+1,B,U(1+1))` — must get the
/// theorem at *that* term: [`Cases::new`] mints a fresh `rec₊`, so a second
/// `Nat` would have a different fibre family and hence a different `W`.
pub struct NatMem {
    /// The seed `S = (1+1) ∪ 1`.
    pub seed: Term,
    /// `⊢ 1 = succ 0`.
    pub one_is_succ_zero: Thm,
    /// `⊢ 1 ∈ ω`.
    pub one_in_omega: Thm,
    /// `⊢ (1+1) ∈ U₁`.
    pub tags_in_u1: Thm,
    /// `⊢ S ∈ U(1+1)`.
    pub seed_in_bound: Thm,
    /// `⊢ S ∈ U₁`.
    pub seed_in_u1: Thm,
    /// `⊢ Fin(1+1, B)`.
    pub fin: Thm,
    /// **`⊢ N ∈ U₁`**, at the `N` the caller supplied.
    pub nat_in_u1: Thm,
}

impl NatMem {
    /// Whether every theorem here is what the struct's docs say it is: a
    /// closed `⊢`, with an empty hypothesis set.
    ///
    /// [`NatMem::over`] checks this before returning, so a `NatMem` in hand
    /// always satisfies it.
    pub fn is_unconditional(&self) -> bool {
        [
            &self.one_is_succ_zero,
            &self.one_in_omega,
            &self.tags_in_u1,
            &self.seed_in_bound,
            &self.seed_in_u1,
            &self.fin,
            &self.nat_in_u1,
        ]
        .iter()
        .all(|t| t.hyps().is_empty())
    }
}

impl NatUniverse {
    /// Build `N` over the chain and put it in `U₁`.
    pub fn new(env: &mut Env, c: &Chain) -> Option<NatUniverse> {
        let wt = &c.wt;
        let s = &wt.sums;
        let bnd: &Bound = &c.bound;

        let cases = Cases::new(env, s)?;
        let pf = PointFun::over(env, s, &wt.app_pair)?;
        let empty_u = empty_in_least_universe(env, wt, bnd)?;
        let nat = Nat::over(env, wt, bnd, &cases, &pf, &empty_u)?;

        let m = NatMem::over(env, c, &nat)?;
        Some(NatUniverse {
            nat,
            seed: m.seed,
            one_is_succ_zero: m.one_is_succ_zero,
            one_in_omega: m.one_in_omega,
            tags_in_u1: m.tags_in_u1,
            seed_in_bound: m.seed_in_bound,
            seed_in_u1: m.seed_in_u1,
            fin: m.fin,
            nat_in_u1: m.nat_in_u1,
        })
    }
}

impl NatMem {
    /// Put a **caller-supplied** `N` in `U₁`.
    ///
    /// `nat` must have been built over `c`'s own [`crate::wtype::Wtype`] and
    /// [`Bound`] — over any other, `nat.ty` names a `W` this chain's theorems do
    /// not speak of, and the final guard rejects the result rather than
    /// returning a theorem about the wrong set.
    ///
    /// **The two `Nat` theorems this consumes must be unconditional, and so
    /// must everything it returns.** `Nat`'s theorem fields are `pub`, so a
    /// caller can hand over a `⊢`-shaped conclusion resting on a hypothesis;
    /// [`crate::hyp_mp`] and `Thm::mp` union the hypothesis sets, so it would
    /// ride through `finite_branching` into `nat_in_u1` and be advertised as
    /// the unconditional `⊢ N ∈ U₁` this struct's documentation promises.
    /// Pinning the *conclusion* does not catch that — a hypothetical theorem
    /// has the same conclusion — which is why the checks below are on
    /// `hyps()` as well, as [`super::enums::enum_in_u1`] already does on both
    /// sides.
    pub fn over(env: &mut Env, c: &Chain, nat: &Nat) -> Option<NatMem> {
        if !nat.fibre_zero.hyps().is_empty() || !nat.fibre_succ.hyps().is_empty() {
            return None
        }
        let wt = &c.wt;
        let s = &wt.sums;
        let bnd: &Bound = &c.bound;
        let sets = s.ap.sets.clone();
        let lu = c.lu();

        // Re-derived rather than taken as an argument: it introduces no symbol,
        // only fresh variables, so the statement is the same one whichever
        // caller produced it.
        let empty_u = empty_in_least_universe(env, wt, bnd)?;

        let zero = s.zero();
        let one = s.unit();
        let om = c.r.omega();
        let tags = nat.tags.clone();
        let fam = nat.fam.clone();
        let seed = bin_union(&sets, tags.clone(), one.clone());

        // ── `1 = succ 0`, and hence `1 ∈ ω` ─────────────────────────────────
        let one_is_succ_zero = one_eq_succ_zero(env, c, &zero, &one)?;
        let succ_zero_in_om = Thm::mp(
            &inst_all(&c.r.core().succ_closed, std::slice::from_ref(&zero))?,
            &c.r.core().zero_mem,
        )?;
        let wv = env.fresh_var();
        let one_in_omega = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    c.r.succ_of(zero.clone()),
                    one.clone(),
                    wv,
                    Formula::mem(Term::var(wv), om.clone()),
                ),
                &eq_symm(env, &one_is_succ_zero)?,
            )?,
            &succ_zero_in_om,
        )?;

        // ── The seed's two inclusions ───────────────────────────────────────
        let (bu_left, bu_right) = crate::funspace::pow_pow::mem_bin_union(env, &sets)?;
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let tags_sub = Thm::gen(
            zv,
            &inst_all(&bu_left, &[tags.clone(), one.clone(), tz.clone()])?,
        );
        let one_sub = Thm::gen(
            zv,
            &inst_all(&bu_right, &[tags.clone(), one.clone(), tz.clone()])?,
        );
        let empty_sub = Thm::gen(
            zv,
            &syl(
                &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?,
                &ex_falso(Formula::mem(tz.clone(), seed.clone())),
            )?,
        );
        if *tags_sub.concl() != kernel::thm::subset(env, tags.clone(), seed.clone())
            || *one_sub.concl() != kernel::thm::subset(env, one.clone(), seed.clone())
            || *empty_sub.concl() != kernel::thm::subset(env, zero.clone(), seed.clone())
        {
            return None
        }

        // ── `Fin(A,B)`: the fibre obligations, by case analysis on `1 + 1` ──
        let fin = finite_branching(
            env,
            c,
            nat,
            &seed,
            &and_intro(&empty_sub, &c.r.core().zero_mem),
            &and_intro(&one_sub, &one_in_omega),
            &tags_sub,
        )?;

        // ── `A ∈ U₁`, from the sum's defining equation ──────────────────────
        let u1 = &c.u1;
        let one_in_u1 = Thm::mp(
            &inst_all(&u1.pairing, &[zero.clone(), zero.clone()])?,
            &and_intro(&u1.empty_mem, &u1.empty_mem),
        )?;
        let sing_one = singleton(sets.up, one.clone());
        let sing_one_in_u1 = Thm::mp(
            &inst_all(&u1.pairing, &[one.clone(), one.clone()])?,
            &and_intro(&one_in_u1, &one_in_u1),
        )?;
        let p_left = s.prod.of(singleton(sets.up, zero.clone()), one.clone());
        let p_right = s.prod.of(sing_one.clone(), one.clone());
        let p_left_u1 = Thm::mp(
            &inst_all(&u1.product, &[singleton(sets.up, zero.clone()), one.clone()])?,
            &and_intro(&one_in_u1, &one_in_u1),
        )?;
        let p_right_u1 = Thm::mp(
            &inst_all(&u1.product, &[sing_one, one.clone()])?,
            &and_intro(&sing_one_in_u1, &one_in_u1),
        )?;
        let body_u1 = Thm::mp(
            &inst_all(&u1.bin_union, &[p_left.clone(), p_right.clone()])?,
            &and_intro(&p_left_u1, &p_right_u1),
        )?;
        let sum_def_at = inst_all(&s.sum_def, &[one.clone(), one.clone()])?;
        if *sum_def_at.concl()
            != Formula::eq(tags.clone(), bin_union(&sets, p_left.clone(), p_right.clone()))
        {
            return None
        }
        let tags_in_u1 = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    bin_union(&sets, p_left, p_right),
                    tags.clone(),
                    wv,
                    Formula::mem(Term::var(wv), u1.set.clone()),
                ),
                &eq_symm(env, &sum_def_at)?,
            )?,
            &body_u1,
        )?;
        let seed_in_u1 = Thm::mp(
            &inst_all(&u1.bin_union, &[tags.clone(), one.clone()])?,
            &and_intro(&tags_in_u1, &one_in_u1),
        )?;

        // ── `S ∈ U(A)`, the bound side ──────────────────────────────────────
        let mem_lu = crate::universe::mem_least_universe(env, lu, &bnd.lu_ax)?;
        let tags_in_bound = inst_all(&mem_lu, std::slice::from_ref(&tags))?;
        let empty_in_bound = inst_all(&empty_u, std::slice::from_ref(&tags))?;
        let one_in_bound = Thm::mp(
            &inst_all(&bnd.least_pairing, &[tags.clone(), zero.clone(), zero.clone()])?,
            &and_intro(&empty_in_bound, &empty_in_bound),
        )?;
        let seed_in_bound = Thm::mp(
            &inst_all(&c.bin_union_all, &[tags.clone(), tags.clone(), one.clone()])?,
            &and_intro(&tags_in_bound, &one_in_bound),
        )?;

        // ── Step (f) at the concrete seed, tags, family and two universes ───
        let at_seed = Thm::gen(c.st.seed, &c.wmem.w_in_universe);
        let at = inst_all(
            &at_seed,
            &[seed.clone(), tags.clone(), fam.clone(), tags.clone(), om.clone()],
        )?;
        let nat_in_u1 = Thm::mp(
            &at,
            &and_intro(
                &and_intro(&fin, &seed_in_bound),
                &and_intro(&seed_in_u1, &u1.omega_mem),
            ),
        )?;
        if *nat_in_u1.concl() != Formula::mem(nat.ty.clone(), u1.set.clone()) {
            return None
        }

        let out = NatMem {
            seed,
            one_is_succ_zero,
            one_in_omega,
            tags_in_u1,
            seed_in_bound,
            seed_in_u1,
            fin,
            nat_in_u1,
        };
        // Every field is advertised as a `⊢` with nothing on the left. Checked
        // rather than argued: it is one line, and it is the only thing standing
        // between a hypothesis anywhere upstream and a checker-facing statement
        // that does not mention it.
        out.is_unconditional().then_some(out)
    }
}

/// `⊢ 1 = succ 0`, i.e. `{∅} = ∅ ∪ {∅}` — one Extensionality.
fn one_eq_succ_zero(env: &mut Env, c: &Chain, zero: &Term, one: &Term) -> Option<Thm> {
    let core = c.r.core();
    let sz = c.r.succ_of(zero.clone());
    let ext = Thm::ax_extensionality(env);
    let zv = env.fresh_var();
    let tz = Term::var(zv);

    let ms = inst_all(&core.mem_sing, &[zero.clone(), tz.clone()])?;
    let sa = inst_all(&core.succ_ax, &[zero.clone(), tz.clone()])?;
    let in_zero = Formula::mem(tz.clone(), zero.clone());
    let eq_zero = Formula::eq(tz.clone(), zero.clone());
    let disj = Formula::or(in_zero.clone(), eq_zero.clone());

    // `z ∈ 1 → z = 0 → (z ∈ 0 ∨ z = 0) → z ∈ succ 0`.
    let fwd = syl(
        &iff_mp(&ms)?,
        &syl(&or_intro_right(in_zero.clone(), eq_zero.clone()), &iff_mpr(&sa)?)?,
    )?;
    // `(z ∈ 0 ∨ z = 0) → z = 0`, since `z ∈ ∅` is absurd.
    let collapse = Thm::mp(
        &com12(&imp_refl(disj))?,
        &inst_all(&c.r.ap.empty_ax, std::slice::from_ref(&tz))?,
    )?;
    let bwd = syl(&iff_mp(&sa)?, &syl(&collapse, &iff_mpr(&ms)?)?)?;

    let same = Thm::gen(zv, &and_intro(&fwd, &bwd));
    let out = Thm::mp(&inst_all(&ext, &[one.clone(), sz.clone()])?, &same)?;
    if *out.concl() != Formula::eq(one.clone(), sz) {
        return None
    }
    Some(out)
}

/// `⊢ (1+1) ⊆ S ∧ ∀a. (a ∈ 1+1 → (B(a) ⊆ S ∧ B(a) ∈ ω))`.
///
/// The `∀a` half is the case analysis: `a ∈ 1 + 1` is `a = inl x` or
/// `a = inr y` with `x, y ∈ 1`, `1` is a subsingleton, and the two `rec₊`
/// computation rules then name the fibre.
fn finite_branching(
    env: &mut Env,
    c: &Chain,
    nat: &Nat,
    seed: &Term,
    zero_ok: &Thm,
    one_ok: &Thm,
    tags_sub: &Thm,
) -> Option<Thm> {
    let s = &c.wt.sums;
    let om = c.r.omega();
    let point = s.point();
    let (av, xv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(av), Term::var(xv));

    let fibre = c.wt.fibre(nat.fam.clone(), ta.clone());
    let goal = Formula::and(
        kernel::thm::subset(env, fibre.clone(), seed.clone()),
        Formula::mem(fibre.clone(), om),
    );

    // One branch: from `x ∈ 1 ∧ a = inj(x)` and `⊢ app(B, inj •) = f`, and
    // `⊢ f ⊆ S ∧ f ∈ ω`, conclude the goal.
    let mut branch = |inj: &dyn Fn(Term) -> Term, fibre_eq: &Thm, ok: &Thm| -> Option<Thm> {
        let x_in_one = Formula::mem(tx.clone(), s.unit());
        let a_eq = Formula::eq(ta.clone(), inj(tx.clone()));
        let e = Formula::and(x_in_one.clone(), a_eq.clone());
        let e_x = and_left(x_in_one.clone(), a_eq.clone());
        let e_eq = and_right(x_in_one, a_eq);

        // `x = •`, so `a = inj •`.
        let e_pt = syl(&e_x, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;
        let to_point = Thm::eq_leibniz(
            tx.clone(),
            point.clone(),
            wv,
            Formula::eq(ta.clone(), inj(Term::var(wv))),
        );
        let e_a = hyp_mp(&syl(&e_pt, &to_point)?, &e_eq)?;
        let e_a_sym = syl(&e_a, &eq_symm_imp(env, ta.clone(), inj(point.clone())))?;

        // Move the fibre equation along it, then the goal back along that.
        let (_, f) = fibre_eq.concl().as_eq()?;
        let move_fibre = Thm::eq_leibniz(
            inj(point.clone()),
            ta.clone(),
            wv,
            Formula::eq(c.wt.fibre(nat.fam.clone(), Term::var(wv)), f.clone()),
        );
        let e_fibre = hyp_mp(&syl(&e_a_sym, &move_fibre)?, &a1i(fibre_eq, e.clone()))?;
        let e_fibre_sym = syl(&e_fibre, &eq_symm_imp(env, fibre.clone(), f.clone()))?;
        let move_goal = Thm::eq_leibniz(
            f,
            fibre.clone(),
            wv,
            Formula::and(
                kernel::thm::subset(env, Term::var(wv), seed.clone()),
                Formula::mem(Term::var(wv), c.r.omega()),
            ),
        );
        let out = hyp_mp(&syl(&e_fibre_sym, &move_goal)?, &a1i(ok, e.clone()))?;
        if *out.concl() != Formula::imp(e.clone(), goal.clone()) {
            return None
        }
        exists_elim_imp(xv, &Thm::gen(xv, &out), &goal)
    };

    let left = branch(&|t| s.inl(t), &nat.fibre_zero, zero_ok)?;
    let right = branch(&|t| s.inr(t), &nat.fibre_succ, one_ok)?;

    let a_in = Formula::mem(ta.clone(), nat.tags.clone());
    let cases = inst_all(&s.sum_cases, &[s.unit(), s.unit(), ta.clone()])?;
    if cases.concl().as_imp()?.0 != a_in {
        return None
    }
    let body = hyp_or_elim(&cases, &a1i(&left, a_in.clone()), &a1i(&right, a_in.clone()))?;
    let all = Thm::gen(av, &body);
    Some(and_intro(tags_sub, &all))
}
