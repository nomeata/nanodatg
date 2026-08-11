//! **`Nat.rec`'s ι rule at a use site** — the certificate `whnf`'s recursor arm
//! needs when the eliminator is `Nat.rec` and its major premise has reached a
//! constructor.
//!
//! # Interface
//!
//! ```text
//! iota_nat::fire(checker, Nat.rec, rec_ty, ⟦Nat.rec⟧, args, ⟦args⟧, ctor, ctor_args, rhs)
//!   -> Result<(Thm, Term), Gap>
//! ```
//!
//! One composed equation
//!
//! ```text
//! Γ ⊢ app(…app(⟦Nat.rec⟧, ⟦C⟧)…, ⟦major⟧) = ⟦rhs⟧
//! ```
//!
//! together with `⟦rhs⟧` — the same contract [`crate::iota_dep::fire`],
//! [`crate::iota_model::fire`] and [`crate::rec_acc_iota::fire`] have, at the
//! same call site in [`crate::kernel::Checker::whnf_conv`], and a **sibling** of
//! all three rather than a widening of any.
//!
//! # Why a sibling
//!
//! `iota_dep` builds its equation out of
//! [`derived::inductive::DepRecursor::iota`] over a class-(T) carrier, and
//! `Nat` **has no class-(T) carrier**: it takes
//! [`crate::direct::Clause::Nat`], so no W-type skeleton is ever built for it.
//! The split is made on the clause at the dispatch, exactly as `Acc`'s is, so
//! that neither module has to decline for the other.
//!
//! **This module was missing for one commit and the cost is on the record.**
//! With `⟦Nat⟧ = ω` in and this absent, `mini/tests/fixtures/nat_char_equations`
//! fell from `constEv 38/38` to `13/38` with 46 gapped conversions, every one
//! of them labelled `recursor(Nat.rec: iota: the declaration has no class-(T)
//! carrier)` — `iota_dep` correctly reporting that a carrier it never built has
//! no rule. The tutorial corpus did not catch it: its two `Nat` exports reduce
//! `Nat.rec` but never demand a *certificate* for the ι step.
//!
//! # What the equation is made of
//!
//! Four rewrites, and the two ι rules are one of them:
//!
//! ```text
//! app⁴(⟦Nat.rec⟧, C,cz,cs, ⟦major⟧) = natrec(⟦cz⟧,⟦cs⟧,⟦major⟧)   beta_spine
//!             natrec(…, app(⟦Nat.succ⟧,k)) = natrec(…, succ k)    congruence on beta_spine
//!             natrec(…, succ k) = app(app(cs,k), natrec(…,k))     Nat::iota_succ
//!                          natrec(…,k) = app⁴(⟦Nat.rec⟧, …, k)    beta_spine, backwards
//! ```
//!
//! The last one is the one that is easy to forget: `derived` states the rule
//! about `natrec` and Lean's right-hand side names the *recursor applied
//! again*, so the recursive call has to be put back on the spine it came from
//! or the two sides never meet.
//!
//! At zero it is two: `beta_spine`, then [`Nat::iota_zero`](derived::nat::Nat),
//! and `⟦major⟧` is already `0` because the clause that interprets `Nat.zero`
//! is this clause.
//!
//! # `u = 0` is not here, and that is deliberate
//!
//! At a `Prop` motive both sides of the equation interpret to `•` — §6.2 sends
//! a proof-valued application there — so the rule is reflexivity and
//! [`Checker::proof_point_leg`](crate::kernel) already supplies it, at no cost
//! and without this module running. Declining is the correct answer rather than
//! a gap: see [`PROP`]. `crate::rec_acc_iota` makes the same call for the same
//! reason.

use kernel::{Formula, Term, Thm};

use crate::ev::{Cause, Gap};
use crate::expr::{Name, E};
use crate::kernel::Checker;

/// `C`, `cz`, `cs`, `t`.
const DEPTH: usize = 4;

/// The dispatch sent a recursor whose declaration does not take this clause.
const CLAUSE: &str = "nat: iota: the declaration does not take the Nat clause";
/// The redex does not have `Nat.rec`'s arity.
const SHAPE: &str = "nat: iota: the redex is not Nat.rec at four arguments";
/// A `Prop`-motive ι, which is reflexivity and is not this module's.
const PROP: &str = "nat: iota: a Prop motive's rule is proof irrelevance";
/// The major premise is not one of Lean's two constructors at its own arity.
const MAJOR: &str = "nat: iota: the major premise is not Nat.zero or Nat.succ k";
/// A rewrite in the chain did not meet the next one.
const COMPOSE: &str = "nat: iota: the rule did not compose onto the redex";

/// Whether the ι rule at this eliminator is this module's.
pub(crate) fn selects(c: &Checker<'_, '_>, rec: &Name) -> bool {
    c.environment().owner(rec).and_then(crate::direct::clause_for)
        == Some(crate::direct::Clause::Nat)
}

/// The composed equation, and the reduct's interpretation.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fire(
    c: &mut Checker<'_, '_>,
    rec: &Name,
    rec_ty: &E,
    head_tm: &Term,
    args: &[E],
    arg_tms: &[Term],
    ctor: &Name,
    ctor_args: &[E],
    rhs: &E,
) -> Result<(Thm, Term), Gap> {
    let ind_name = c
        .environment()
        .owner(rec)
        .cloned()
        .ok_or(Gap::NoInterpretation(*rec))?;
    let bad = |w: &'static str| Gap::Recursor(ind_name, w, Cause::Threading);
    if crate::direct::clause_for(&ind_name) != Some(crate::direct::Clause::Nat) {
        return Err(bad(CLAUSE))
    }
    if args.len() != DEPTH || arg_tms.len() != DEPTH {
        return Err(bad(SHAPE))
    }
    // Read off the recursor's own motive binder, as everywhere else.
    let u1 = crate::rec_dep::motive_level(rec_ty, 0, 0).ok_or_else(|| bad(SHAPE))?;
    if u1 == 0 {
        return Err(bad(PROP))
    }

    // `⟦rhs⟧` first: everything after this holds the `Interp` mutably, and
    // inference is the checker's.
    let want = c.infer_type(rhs).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;

    let nat_n = Name::simple("Nat");
    let is_zero = *ctor == Name::str(&nat_n, "zero");
    let is_succ = *ctor == Name::str(&nat_n, "succ");
    if !(is_zero && ctor_args.is_empty() || is_succ && ctor_args.len() == 1) {
        return Err(bad(MAJOR))
    }

    // The arguments' memberships, and — at a successor — the field's, which is
    // the premise both `beta_spine`s and `iota_succ` consume.
    let mems = c.nest_arg_mems(head_tm, rec_ty, args, arg_tms)?;
    let field = if is_succ {
        let t = c.infer_type(&ctor_args[0]).map_err(|_| Gap::Classifier)?;
        let tm = t.tm.clone().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?;
        let mem = t.ev.thm().cloned().ok_or_else(|| t.ev.reason(Gap::NoEndpoint))?;
        Some((tm, mem))
    } else {
        None
    };
    let succ_former = if is_succ {
        Some(
            c.stored_term(&Name::str(&nat_n, "succ"), &[])
                .ok_or_else(|| bad(MAJOR))?,
        )
    } else {
        None
    };

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let nc = ip.nat_clause().ok_or_else(|| bad(CLAUSE))?;
    let (cz, cs) = (arg_tms[1].clone(), arg_tms[2].clone());

    // ── `app⁴(⟦Nat.rec⟧, …) = natrec(⟦cz⟧, ⟦cs⟧, ⟦major⟧)` ──────────────────
    let (_, beta) = ip.beta_spine(head_tm, arg_tms, &mems).ok_or_else(|| bad(COMPOSE))?;

    let chain = if is_zero {
        // `⟦Nat.zero⟧` *is* `0`, so the rule applies with no rewrite in front
        // of it — which is a property of the clause and not a coincidence.
        let rule = derived::inst_all(&nc.nat.iota_zero, &[cz.clone(), cs.clone()])
            .ok_or_else(|| bad(COMPOSE))?;
        derived::eq_trans(&mut ip.env_mut(), &beta, &rule).ok_or_else(|| bad(COMPOSE))?
    } else {
        let (k_tm, k_mem) = field.ok_or_else(|| bad(MAJOR))?;
        let former = succ_former.ok_or_else(|| bad(MAJOR))?;
        // `app(⟦Nat.succ⟧, k) = succ k`, then under `natrec(cz,cs,·)`.
        let (_, sbeta) = ip
            .beta_spine(&former, std::slice::from_ref(&k_tm), std::slice::from_ref(&k_mem))
            .ok_or_else(|| bad(COMPOSE))?;
        let cong = natrec_cong(ip, &nc, &cz, &cs, &sbeta).ok_or_else(|| bad(COMPOSE))?;
        let step = derived::eq_trans(&mut ip.env_mut(), &beta, &cong).ok_or_else(|| bad(COMPOSE))?;
        // The ι rule itself, whose side condition is `k ∈ ω`.
        let rule = derived::inst_all(&nc.nat.iota_succ, &[cz.clone(), cs.clone(), k_tm.clone()])
            .ok_or_else(|| bad(COMPOSE))?;
        let iota = Thm::mp(&rule, &k_mem).ok_or_else(|| bad(COMPOSE))?;
        let step = derived::eq_trans(&mut ip.env_mut(), &step, &iota).ok_or_else(|| bad(COMPOSE))?;
        // **The recursive call goes back on the spine it came from.** `derived`
        // names it `natrec(cz,cs,k)`; Lean's right-hand side names
        // `Nat.rec C cz cs k`, whose interpretation is the four-deep
        // application. Without this the two sides never meet.
        let mut inner_tms = arg_tms.to_vec();
        inner_tms[3] = k_tm;
        let mut inner_mems = mems.clone();
        inner_mems[3] = k_mem;
        let (_, ibeta) =
            ip.beta_spine(head_tm, &inner_tms, &inner_mems).ok_or_else(|| bad(COMPOSE))?;
        let back = derived::eq_symm(&mut ip.env_mut(), &ibeta).ok_or_else(|| bad(COMPOSE))?;
        let cong2 = minor_cong(ip, &cs, &inner_tms[3], &back).ok_or_else(|| bad(COMPOSE))?;
        derived::eq_trans(&mut ip.env_mut(), &step, &cong2).ok_or_else(|| bad(COMPOSE))?
    };

    // The chain must land on the interpretation the *export's* right-hand side
    // has, compared and not assumed.
    let (_, got) = chain.concl().as_eq().ok_or_else(|| bad(COMPOSE))?;
    if got != want {
        return Err(bad(COMPOSE))
    }
    Ok((chain, want))
}

/// `⊢ natrec(cz,cs,a) = natrec(cz,cs,b)` from `⊢ a = b`.
fn natrec_cong(
    ip: &mut crate::interp::Interp,
    nc: &crate::nat_clause::NatClause,
    cz: &Term,
    cs: &Term,
    eq: &Thm,
) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let (a, b) = (a.clone(), b.clone());
    let y = ip.fresh_var();
    let lhs = ip.mk(nc.nat.natrec, vec![cz.clone(), cs.clone(), a.clone()]);
    let tmpl = ip.mk(nc.nat.natrec, vec![cz.clone(), cs.clone(), Term::var(y)]);
    let leib = Thm::eq_leibniz(a, b, y, Formula::eq(lhs.clone(), tmpl));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}

/// `⊢ app(app(cs,k), a) = app(app(cs,k), b)` from `⊢ a = b`.
fn minor_cong(
    ip: &mut crate::interp::Interp,
    cs: &Term,
    k: &Term,
    eq: &Thm,
) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let (a, b) = (a.clone(), b.clone());
    let head = ip.app(cs.clone(), k.clone());
    let y = ip.fresh_var();
    let lhs = ip.app(head.clone(), a.clone());
    let tmpl = ip.app(head, Term::var(y));
    let leib = Thm::eq_leibniz(a, b, y, Formula::eq(lhs.clone(), tmpl));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}
