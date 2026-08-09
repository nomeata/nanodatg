//! **`Nat.rec`** — the eliminator of the one declaration whose carrier is `ω`.
//!
//! # Interface
//!
//! ```text
//! rec_nat::ensure(checker, Nat, σ_Nat, Nat.rec, σ_rec) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::recursor::ensure`] on the declaration
//! [`crate::direct::Clause::Nat`] names, and from nowhere else. On success
//! `⟦Nat.rec.{σ}⟧` and its typing are in the store.
//!
//! # Two rules, and §6.2's own split decides which
//!
//! ```text
//! Nat.rec.{u} : ∀ (C : Nat → Sort u) (cz : C Nat.zero)
//!                 (cs : ∀ n, C n → C n.succ) (t : Nat), C t
//! ```
//!
//! | `u` | interpretation | what carries the bottom |
//! |---|---|---|
//! | `0` | `•` | [`derived::nat::induct`] at `φ(z) := • ∈ app(⟦C⟧,z)` |
//! | `≥ 1` | `natrec(⟦cz⟧, ⟦cs⟧, ⟦t⟧)` | [`derived::nat::natrec_mem`] |
//!
//! `u` is read off the recursor's **own motive binder** by
//! [`crate::rec_dep::motive_level`], not off the σ list, and it is then
//! required to agree with what the nest's codomain says — so a recursor whose
//! motive is not a family of sorts is declined rather than mis-routed.
//!
//! # The step premise is built by opening binders, not by instantiating
//!
//! `derived` states the step universally; the nest hands in `⟦cs⟧` as a
//! *member of a dependent product*. Those are two shapes of one fact and the
//! bridge is the scope stack, exactly as in [`crate::rec_dep::minor_at`]: open
//! a binder, apply the minor to it, discharge — and
//! [`Closed::discharge`](crate::scope::Closed::discharge) *is* `∀x. (x ∈ A → …)`
//! by construction. Nothing is instantiated and nothing is searched for.
//!
//! **The one rewrite in the walk** is at the end of it. The second application
//! lands in `app(⟦C⟧, app(⟦Nat.succ⟧, x))`, because the minor's declared
//! codomain is `C n.succ` and `⟦Nat.succ n⟧` is an application of the *stored
//! nest*; `derived` states the step at `app(⟦C⟧, succ x)`, `succ` being the
//! symbol. One [`Interp::beta_spine`](crate::interp::Interp::beta_spine) closes
//! it — the same call [`crate::direct`]'s constructor bottom makes to put a
//! membership back on its declared codomain, and the reason `⟦Nat.succ⟧` has to
//! be *this* clause's is that no other nest β-reduces to `succ`.
//!
//! # Why the two branches do not share a derivation
//!
//! It would be tidier if both called [`derived::nat::natrec_mem`] and the
//! `Prop` one then moved `natrec(…) = •` across by proof irrelevance. It
//! cannot. At `u = 0` every `Π` in the minor is a **conditional singleton**, so
//! the application rule is [`Interp::cond_app`](crate::interp::Interp::cond_app),
//! and what that concludes is `• ∈ codomain` — a statement about `•` and never
//! about `app(app(⟦cs⟧,x),v)`, which is what `natrec_mem`'s premise is about.
//! The value branch's inner binder is a **scope** (`∀v. (v ∈ app(C,x) → …)`);
//! the `Prop` branch's is an **assumption** (`φ(x) → φ(succ x)`), because there
//! is no `v` for it to be about. They share their shape, not their proof —
//! which is also true of [`crate::rec_dep`] and [`crate::rec_acc`].

use kernel::{FreeVar, Formula, Term, Thm};

use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape};
use crate::kernel::{Checker, Typing, R};
use crate::nat_clause::NatClause;
use crate::scope::Scopes;

/// `C`, `cz`, `cs`, `t` — one motive, two minors, one major, no parameters and
/// no indices.
const DEPTH: usize = 4;

/// The export's `Nat.rec` does not have Lean's arity.
const SHAPE: &str = "nat: Nat.rec is not (0 params, 2 minors, 0 indices)";
/// The motive binder is not a family of sorts, or disagrees with the codomain.
const MOTIVE: &str = "nat: Nat.rec's motive is not a family of sorts";
/// The recursor's type does not have the four binders its arity promises.
const ARITY: &str = "nat: Nat.rec's type does not decompose to its own arity";
/// A minor premise's interpretation is not the `Π` shape the clause walks.
const MINOR: &str = "nat: a minor premise's interpretation is not a Π over the carrier";
/// The apparatus, or a binder's typing, was not the one this clause models.
const APPARATUS: &str = "nat: the ω apparatus or a binder's typing is not the clause's";
/// The induction ran but did not land on the codomain the nest reached.
const LANDING: &str = "nat: the recursor's value does not land in the motive's fibre at the major";

/// Make `⟦Nat.rec.{σ}⟧` available, or say which step refused.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    };
    if (*num_params, *num_minors, *num_indices) != (0, 2, 0) {
        return Err(bad(SHAPE))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*rec_name, rec_inst.to_vec()))
    }
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let u1 = crate::rec_dep::motive_level(&rec_ty, 0, 0).ok_or_else(|| bad(MOTIVE))?;
    let codomain = crate::zoneb::peel(&rec_ty, DEPTH).ok_or_else(|| bad(ARITY))?;
    let site = Site { ind: *ind_name, inst: ind_inst.to_vec(), codomain, u1 };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(bottom_at(c, &site)) };
    let t = c.lam_nest(&rec_ty, DEPTH, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// Which declaration's eliminator, and what the nest reached.
struct Site {
    ind: Name,
    inst: Vec<u32>,
    codomain: E,
    /// The motive's resultant sort, read off the recursor's own motive binder.
    u1: u32,
}

/// Everything the two branches read, gathered once.
struct At {
    c_tm: Term,
    c_mem: Thm,
    cz_tm: Term,
    cz_mem: Thm,
    cs_tm: Term,
    cs_mem: Thm,
    t_tm: Term,
    t_mem: Thm,
    /// The stored `⟦Nat.succ⟧` nest — the one β-step the walk owes.
    succ_former: Term,
}

/// The bottom of `⟦Nat.rec.{u}⟧`'s nest.
fn bottom_at(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);

    let Some((xs, mems)) = c.binders(DEPTH) else { return gap(Gap::NoEndpoint) };
    if xs.len() != DEPTH || mems.len() != DEPTH {
        return gap(Gap::NoEndpoint)
    }

    // §6.2's split, taken twice and required to agree: once from the motive's
    // declared sort in `ensure`, once from the codomain the nest reached.
    let prop = match c.is_prop(&site.codomain) {
        Ok(p) => p,
        Err(_) => return gap(Gap::Classifier),
    };
    if prop != (site.u1 == 0) {
        return gap(bad(MOTIVE))
    }

    let succ_name = Name::str(&Name::simple("Nat"), "succ");
    let Some(succ_former) = c.stored_term(&succ_name, &site.inst) else {
        return gap(Gap::NoEndpoint)
    };
    let at = At {
        c_tm: xs[0].clone(),
        c_mem: mems[0].clone(),
        cz_tm: xs[1].clone(),
        cz_mem: mems[1].clone(),
        cs_tm: xs[2].clone(),
        cs_mem: mems[2].clone(),
        t_tm: xs[3].clone(),
        t_mem: mems[3].clone(),
        succ_former,
    };

    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(nc) = ip.nat_clause() else { return gap(bad(APPARATUS)) };

    // The major premise's own scope typing must be membership in *this* `ω`.
    // If the clause had not taken over the carrier, this is the line that says
    // so, rather than a wrong theorem being built on top of it.
    if *at.t_mem.concl() != Formula::mem(at.t_tm.clone(), nc.nat.omega()) {
        return gap(bad(APPARATUS))
    }

    let built = if prop { prop_bottom(ip, &nc, &at) } else { value_bottom(ip, &nc, &at) };
    match built {
        Some((tm, mem)) => {
            let want = ip.app(at.c_tm.clone(), at.t_tm.clone());
            if *mem.concl() != Formula::mem(tm.clone(), want) {
                return gap(bad(LANDING))
            }
            Typing { ty, tm: Some(tm), ev: Ev::Proved(mem) }
        }
        None => gap(bad(MINOR)),
    }
}

// ───────────────────────────────────────────────────────── shared walk ──

/// Open `x` at `ω` and apply the succ minor to it, returning the scope, the
/// binder and `⊢ app(⟦cs⟧, x) ∈ ⟦C x → C x.succ⟧`.
///
/// The first half of both branches, and the only part of the walk that is
/// literally the same derivation either way: the outer `Π` of the minor is
/// over the *carrier*, which is not a `Prop` at either motive level.
fn open_index(
    ip: &mut Interp,
    nc: &NatClause,
    scopes: &mut Scopes,
    at: &At,
) -> Option<(crate::scope::ScopeToken, Term, Thm, Thm)> {
    let omega = nc.nat.omega();
    let tok = scopes.open(&mut ip.env_mut(), omega.clone());
    let (x_tm, x_mem) = {
        let s = scopes.get(0)?;
        (s.term(), s.assumption().clone())
    };
    let set1 = at.cs_mem.concl().as_mem()?.1.clone();
    let shape1 = ip.as_pi(&set1)?;
    // The minor's first domain must be the carrier itself: `∀ n : Nat`.
    if shape1.dom() != omega {
        return None
    }
    let applied = match &shape1 {
        PiShape::Dep { site, dom } => {
            ip.dprod_app(site, dom, &at.cs_tm, &x_tm, &at.cs_mem, &x_mem)
        }
        PiShape::Prop { site, dom } => ip.cond_app(site, dom, &at.cs_mem, &x_tm, &x_mem),
    }?;
    Some((tok, x_tm, x_mem, applied))
}

/// `⊢ app(⟦C⟧, a) = app(⟦C⟧, b)` from `⊢ a = b` — one Leibniz instance at the
/// motive's argument slot.
fn motive_cong(ip: &mut Interp, c_tm: &Term, eq: &Thm) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let (a, b) = (a.clone(), b.clone());
    let y = ip.fresh_var();
    let lhs = ip.app(c_tm.clone(), a.clone());
    let tmpl = ip.app(c_tm.clone(), Term::var(y));
    let leib = Thm::eq_leibniz(a, b, y, Formula::eq(lhs.clone(), tmpl));
    let step = Thm::mp(&leib, eq)?;
    Thm::mp(&step, &Thm::eq_refl(lhs))
}

/// Move a membership from `app(⟦C⟧, app(⟦Nat.succ⟧, x))` onto
/// `app(⟦C⟧, succ x)`, which is where `derived` states the step.
fn onto_succ(ip: &mut Interp, at: &At, x_tm: &Term, x_mem: &Thm, mem: &Thm) -> Option<Thm> {
    let (_, succ_eq) = ip.beta_spine(&at.succ_former, std::slice::from_ref(x_tm), std::slice::from_ref(x_mem))?;
    let cod_eq = motive_cong(ip, &at.c_tm, &succ_eq)?;
    ip.retarget_set(mem, &cod_eq)
}

// ───────────────────────────────────────────────────────── u ≥ 1 ──

/// `u ≥ 1`: the eliminator is `natrec(⟦cz⟧, ⟦cs⟧, ⟦t⟧)`.
fn value_bottom(ip: &mut Interp, nc: &NatClause, at: &At) -> Option<(Term, Thm)> {
    // The base premise is the zero minor's own scope typing. Its declared type
    // is `C Nat.zero`, which interprets to `app(⟦C⟧, 0)` **because
    // `⟦Nat.zero⟧` is `0`** — compared and not assumed, so if the clause had
    // not taken over the constructor this is where it would stop.
    let base_want = Formula::mem(at.cz_tm.clone(), ip.app(at.c_tm.clone(), nc.nat.zero()));
    if *at.cz_mem.concl() != base_want {
        return None
    }

    let mut scopes = Scopes::new();
    let (tok_x, x_tm, x_mem, applied1) = open_index(ip, nc, &mut scopes, at)?;

    // ── `v : app(⟦C⟧, x)`, a real binder: the step is `∀v` at a value motive ─
    let (mid_tm, set2) = {
        let (a, b) = applied1.concl().as_mem()?;
        (a.clone(), b.clone())
    };
    let shape2 = ip.as_pi(&set2)?;
    let fibre_x = ip.app(at.c_tm.clone(), x_tm.clone());
    if shape2.dom() != fibre_x {
        return None
    }
    let tok_v = scopes.open(&mut ip.env_mut(), fibre_x);
    let (v_tm, v_mem) = {
        let s = scopes.get(0)?;
        (s.term(), s.assumption().clone())
    };
    let applied2 = match &shape2 {
        PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &mid_tm, &v_tm, &applied1, &v_mem),
        // A value motive whose second `Π` is `Prop`-valued is not this shape.
        PiShape::Prop { .. } => None,
    }?;
    let moved = onto_succ(ip, at, &x_tm, &x_mem, &applied2)?;

    let inner = scopes.close(tok_v).discharge(&moved).ok()?;
    let step = scopes.close(tok_x).discharge(&inner).ok()?;

    let rule = derived::nat::natrec_mem(&mut ip.env_mut(), &nc.nat, &at.c_tm, &at.cz_tm, &at.cs_tm)
        .ok()?;
    let fired = Thm::mp(&rule, &derived::and_intro(&at.cz_mem, &step))?;
    let at_t = derived::inst_all(&fired, std::slice::from_ref(&at.t_tm))?;
    let mem = Thm::mp(&at_t, &at.t_mem)?;
    // Through `Interp::mk`, as the λ clause above once required of any value
    // mentioning its binders. See `crate::direct`'s `Nat.succ` arm.
    let value = ip.mk(
        nc.nat.natrec,
        vec![at.cz_tm.clone(), at.cs_tm.clone(), at.t_tm.clone()],
    );
    Some((value, mem))
}

// ───────────────────────────────────────────────────────── u = 0 ──

/// `u = 0`: the eliminator is `•`, and the obligation is that `app(⟦C⟧,⟦t⟧)` is
/// inhabited by it.
fn prop_bottom(ip: &mut Interp, nc: &NatClause, at: &At) -> Option<(Term, Thm)> {
    let point = ip.point();
    let z = ip.fresh_var();
    // `φ(z) := • ∈ app(⟦C⟧, z)`.
    let phi = Formula::mem(point.clone(), ip.app(at.c_tm.clone(), Term::var(z)));

    // ── the base ────────────────────────────────────────────────────────────
    //
    // The zero minor's typing is about the *binder*; `φ(0)` is about `•`. They
    // are the same by proof irrelevance, and the premise irrelevance wants is
    // that the fibre is a `Prop` — which is the motive's own typing applied at
    // `0`, not an assumption about it.
    let zero = nc.nat.zero();
    let fibre0_mem = fibre_is_prop(ip, at, &zero, nc.nat.zero_mem())?;
    let is_point = ip.point_of_proof(&fibre0_mem, &at.cz_mem)?;
    let base = subject_to_point(ip, &at.cz_mem, &is_point)?;
    if *base.concl() != phi.subst(z, &zero) {
        return None
    }

    // ── the step, as `φ(x) → φ(succ x)` under `x ∈ ω` ───────────────────────
    let mut scopes = Scopes::new();
    let (tok_x, x_tm, x_mem, applied1) = open_index(ip, nc, &mut scopes, at)?;
    let set2 = applied1.concl().as_mem()?.1.clone();
    let shape2 = ip.as_pi(&set2)?;
    let fibre_x = ip.app(at.c_tm.clone(), x_tm.clone());
    if shape2.dom() != fibre_x {
        return None
    }
    // **An assumption, not a binder.** `cond_app` reports about `•`, so there
    // is no `v` for the step to be universally quantified over; what the
    // induction wants at this level is the implication `φ(x) → φ(succ x)`.
    let ih = Formula::mem(point.clone(), fibre_x);
    let (tok_ih, ih_thm) = scopes.assume(ih);
    let applied2 = match &shape2 {
        PiShape::Prop { site, dom } => ip.cond_app(site, dom, &applied1, &point, &ih_thm),
        // A `Prop` motive whose second `Π` is a dependent product is not this
        // shape, and applying it at `•` would be applying it off its domain.
        PiShape::Dep { .. } => None,
    }?;
    let moved = onto_succ(ip, at, &x_tm, &x_mem, &applied2)?;
    let implied = scopes.discharge_assumption(tok_ih, &moved);
    let curried = scopes.close(tok_x).discharge(&implied).ok()?;

    // `∀x. (x ∈ ω → (φ(x) → φ(succ x)))` is what the walk produced;
    // `induct` states its premise over the conjunction, and `induct_step`
    // assembles that from a natural-deduction proof — which is one
    // instantiation and two modus ponens.
    let step = derived::nat::induct_step(nc.nat.core(), z, &phi, |z_om, phi_z| {
        let at_z = derived::rules::inst_all(&curried, &[Term::var(z)])?;
        let under = derived::prim::mp(&at_z, z_om)?;
        derived::prim::mp(&under, phi_z)
    })
    .ok()?;

    let all = derived::nat::induct(&mut ip.env_mut(), nc.nat.core(), z, &phi, &base, &step).ok()?;
    let at_t = derived::inst_all(&all, std::slice::from_ref(&at.t_tm))?;
    let mem = Thm::mp(&at_t, &at.t_mem)?;
    Some((point, mem))
}

/// `⊢ app(⟦C⟧, a) ∈ U₀` — the motive's own typing, applied at `a`.
///
/// The premise proof irrelevance needs, and it is *derived* from the motive
/// binder rather than assumed of it: a `Nat.rec` whose motive is not a family
/// of propositions cannot produce it.
fn fibre_is_prop(ip: &mut Interp, at: &At, a: &Term, a_mem: &Thm) -> Option<Thm> {
    let set = at.c_mem.concl().as_mem()?.1.clone();
    let shape = ip.as_pi(&set)?;
    match &shape {
        PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &at.c_tm, a, &at.c_mem, a_mem),
        PiShape::Prop { .. } => None,
    }
}

/// `⊢ • ∈ S` from `⊢ e ∈ S` and `⊢ e = •`.
fn subject_to_point(ip: &mut Interp, mem: &Thm, eq: &Thm) -> Option<Thm> {
    let (e, s) = mem.concl().as_mem()?;
    let (s, e) = (s.clone(), e.clone());
    let (l, r) = eq.concl().as_eq()?;
    if l != e {
        return None
    }
    let r = r.clone();
    let y: FreeVar = ip.fresh_var();
    let leib = Thm::eq_leibniz(e, r, y, Formula::mem(Term::var(y), s));
    let step = Thm::mp(&leib, eq)?;
    Thm::mp(&step, mem)
}
