//! **Function η's certificate** — `⊢ ⟦λx:A. f x⟧ = ⟦f⟧`.
//!
//! # Interface
//!
//! ```text
//! fun_eta::certify(checker, f_expr, lam_tm, f_tm) -> Result<Thm, Gap>
//! Interp::eta()                                   -> Option<Rc<derived::ext::Eta>>
//! ```
//!
//! Called from [`crate::mini::kernel::Checker::def_eq_ev`] after `try_fun_eta` has
//! *decided*, exactly as [`crate::mini::proj_data::structure_eta`] is called after
//! `try_structure_eta`: the probe accepts or rejects, this only certifies, and
//! its failure is a gap rather than a rejection so acceptance cannot move when
//! a certificate becomes available.
//!
//! # The shortcut, and why the note's threading is not needed
//!
//! The site's own comment read *"the pointwise family is discharged from a
//! scope the recursion above opens with no endpoints; wiring
//! `conv::fun_eta_leg` needs that recursion threaded first."* `try_fun_eta`
//! does call the **`bool`** `is_def_eq` and throw its conversions away, so
//! threading it is real work — but it is work for a *general* body, and η's own
//! theorem does not need it:
//!
//! ```text
//! ⊢ ∀A ∀B ∀f. (f ∈ fs(A,B) → f = graph(f,A))          derived::ext::Eta::eta
//! ```
//!
//! `graph(f,A)` is [`derived::funcs::lambda_n`]'s graph over the body symbol
//! `app` — and `⟦λx:A. f x⟧` is *also* a `lambda_n` graph, over this
//! occurrence's own body symbol `t(h⃗,x)`. Two `lambda_n` graphs whose body
//! symbols agree pointwise are equal by `lam_ext_n`, and here they agree by the
//! site's **own defining axiom**: `t_ax` says `t(h⃗,x) = app(f̄,x)` at every `x`,
//! which is the whole pointwise family with no derivation at all.
//!
//! So the route is `t_ax` → `lam_ext_n` → `Eta::eta`, and the recursion is not
//! threaded. What that costs is *generality of one kind*: a body merely
//! **def-eq** to `f x` rather than syntactically it declines here by name, and
//! that is the case the note's threading would buy. No corpus export has it —
//! both `106_funEta` and `107_funEtaDep` have the body literally `f x`, which
//! is what η is about — and a decline is a reported gap, not a rejection.
//!
//! # One bridge, not two
//!
//! `Eta::eta` is stated over **`fs`** and mini's `Π` is always a `dprod`
//! (`MINI-HANDOFF.md` §18 item 9). §20 item 4 predicted this would need
//! `dprod_const_fibre_n` for the non-dependent pair and something else for the
//! dependent one. It needs neither: [`derived::ext::DProdN::dprod_sub`] —
//! `⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))`, unconditional and with no
//! constant-fibre hypothesis — puts `f̄` into a function space at
//! `B := ⋃img(h⃗,A)` whatever the fibre is. **The dependent and non-dependent
//! pairs take the same route**, and the prediction was one bridge too many.
//!
//! That is worth stating because §18 item 9's two-uses-of-`dprod_const_fibre_n`
//! finding is real and this is *not* a second instance of it: `Quot.lift`
//! needed the function space at a **named** codomain `B` because
//! `lift_in_funspace` mentions it, and η does not care what the codomain is.
//! **The bridge is chosen by whether the consumer names the codomain.**

use std::rc::Rc;

use kernel::{Formula, Term, Thm};

use crate::mini::ev::Gap;
use crate::mini::expr::E;
use crate::mini::interp::{Interp, PiShape};
use crate::mini::kernel::Checker;

/// **`Γ ⊢ ⟦λx:A. f x⟧ = ⟦f⟧`**, or the reason it could not be derived.
///
/// `lam_tm` and `f_tm` are the two interpretations the caller already holds;
/// `f_e` is the *function* side's expression, re-inferred here for its typing
/// because `def_eq_ev` holds terms and not memberships.
///
/// Every step is checked: that the lambda's interpretation really is a graph,
/// that its body symbol really unfolds to `app(f̄,x)`, that the two domains
/// coincide, and that the composite lands on the two endpoints the caller
/// named. A mismatch is `Gap::FunEta`, never a wrong equation.
pub(crate) fn certify(
    c: &mut Checker<'_, '_>,
    f_e: &E,
    lam_tm: &Term,
    f_tm: &Term,
) -> Result<Thm, Gap> {
    // The function's own typing. `def_eq_ev` carries interpretations and not
    // memberships, so this is re-inferred rather than threaded — the same
    // choice `crate::mini::proj_data::structure_eta` makes, and for the same reason.
    let ft = c.infer_type(f_e).map_err(|_| Gap::Classifier)?;
    let (_, _, ft) = c.whnf_typing(ft).map_err(|_| Gap::Classifier)?;
    let f_mem = ft.ev.thm().cloned().ok_or(Gap::FunEta)?;
    if ft.tm.as_ref() != Some(f_tm) {
        return Err(Gap::FunEta)
    }

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let eta = ip.eta().ok_or(Gap::FunEta)?;
    let p = ip.prelude.clone();
    let ap = p.ap.clone();

    // `⟦λx:A. f x⟧ = lam(h⃗, ⟦A⟧)`, and `⟦f⟧ ∈ dprod(q⃗, ⟦A⟧)`.
    let (site, dom) = ip.as_lam(lam_tm).ok_or(Gap::FunEta)?;
    let f_set = f_mem.concl().as_mem().ok_or(Gap::FunEta)?.1;
    let PiShape::Dep { site: fsite, dom: fdom } = ip.as_pi(&f_set).ok_or(Gap::FunEta)? else {
        return Err(Gap::FunEta)
    };
    if fdom != dom {
        return Err(Gap::FunEta)
    }

    // ── the pointwise family, which is the body symbol's own axiom ──────────
    let xv = ip.fresh_var();
    let x = Term::var(xv);
    let body_eq = ip
        .symbol_at(site.t, &site.t_ax, &site.holes, &x)
        .ok_or(Gap::FunEta)?;
    let want_body = ip.app(f_tm.clone(), x.clone());
    if body_eq.concl().as_eq().map(|(_, r)| r) != Some(want_body) {
        // The body is not syntactically `f x`. That is the case the site's own
        // note would buy with a threaded recursion; declined by name.
        return Err(Gap::FunEta)
    }
    let family = crate::mini::rec_dep::gen_all_checked(
        &[xv],
        &derived::a1i(&body_eq, Formula::mem(x, dom.clone())),
    )
    .ok_or(Gap::FunEta)?;

    // ── the two graphs are equal ────────────────────────────────────────────
    let rule = derived::ext::lam_ext_n(
        &mut ip.env_mut(),
        &ap,
        site.t,
        site.lam,
        &site.lam_ax,
        ap.app,
        eta.graph,
        &eta.graph_ax,
    )
    .ok_or(Gap::FunEta)?;
    let mut args = site.holes.clone();
    args.push(f_tm.clone());
    args.push(dom.clone());
    args.push(dom.clone());
    let inst = derived::inst_all(&rule, &args).ok_or(Gap::FunEta)?;
    let graphs = Thm::mp(&inst, &Thm::eq_refl(dom.clone()))
        .and_then(|t| Thm::mp(&t, &family))
        .ok_or(Gap::FunEta)?;

    // ── `f̄` into a function space, at whatever codomain the fibres reach ────
    //
    // `dprod_sub` and not `dprod_const_fibre_n`: η does not name the codomain,
    // so the union of the image serves at a dependent fibre as well as at a
    // constant one. See the header.
    let mut sargs = fsite.holes.clone();
    sargs.push(dom.clone());
    let sub = derived::inst_all(&fsite.dp.dprod_sub, &sargs).ok_or(Gap::FunEta)?;
    let at_f = derived::inst_all(&sub, std::slice::from_ref(f_tm)).ok_or(Gap::FunEta)?;
    let f_in_fs = Thm::mp(&at_f, &f_mem).ok_or(Gap::FunEta)?;
    let img = Term::apply(fsite.dp.img, sargs);
    let cod = ap.sets.union_of(img);
    if *f_in_fs.concl() != Formula::mem(f_tm.clone(), p.fs.of(dom.clone(), cod.clone())) {
        return Err(Gap::FunEta)
    }

    // ── η itself, and the chain ─────────────────────────────────────────────
    let eta_at =
        derived::inst_all(&eta.eta, &[dom.clone(), cod, f_tm.clone()]).ok_or(Gap::FunEta)?;
    let f_is_graph = Thm::mp(&eta_at, &f_in_fs).ok_or(Gap::FunEta)?;
    let back = derived::eq_symm(&mut ip.env_mut(), &f_is_graph).ok_or(Gap::FunEta)?;
    let out = derived::eq_trans(&mut ip.env_mut(), &graphs, &back).ok_or(Gap::FunEta)?;
    if *out.concl() != Formula::eq(lam_tm.clone(), f_tm.clone()) {
        return Err(Gap::FunEta)
    }
    Ok(out)
}

impl Interp {
    /// [`derived::ext::Eta`] over **this** `Interp`'s own application and
    /// function space, built on first use and then shared.
    ///
    /// Identity rather than memoisation, for the reason every apparatus here is:
    /// `graph(f,A)` must be **one** symbol across every η in a file, or two
    /// occurrences would be related by nothing. Lazy because it carves a
    /// `lambda_n` graph and derives four theorems, and an export with no η
    /// should not pay for them.
    pub fn eta(&mut self) -> Option<Rc<derived::ext::Eta>> {
        if self.eta.is_none() && !self.eta_failed {
            let p = self.prelude.clone();
            self.eta = (|| {
                let app_pair = derived::ext::app_of_pair(&mut self.env_mut(), &p.ap)?;
                let fun_ext =
                    derived::ext::funspace_ext(&mut self.env_mut(), &p.ap, &p.prod, &p.fs, &app_pair)?;
                derived::ext::Eta::new(
                    &mut self.env_mut(),
                    &p.ap,
                    &p.prod,
                    &p.fs,
                    &fun_ext,
                    &p.fs_app_mem,
                )
            })()
            .map(Rc::new);
            self.eta_failed = self.eta.is_none();
        }
        self.eta.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The apparatus builds and η's own equation is unconditional — a
    /// `Γ`-carrying one would ride into a conversion this module documents as
    /// closed.
    #[test]
    fn the_eta_apparatus_builds_and_is_unconditional() {
        let mut ip = Interp::new();
        let e = ip.eta().expect("the Eta apparatus builds over the prelude");
        assert!(e.eta.hyps().is_empty(), "the eta equation is unconditional");
        assert!(e.graph_ax.hyps().is_empty(), "the graph's axiom is unconditional");
    }

    /// **One `graph`, not one per call.** Two η conversions in one file must
    /// name the same symbol or they would be related by nothing.
    #[test]
    fn the_apparatus_is_identity_not_a_cache() {
        let mut ip = Interp::new();
        assert_eq!(
            ip.eta().expect("builds").graph,
            ip.eta().expect("builds").graph,
            "two η conversions must name one graph"
        );
    }
}
