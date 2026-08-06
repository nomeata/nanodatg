//! The kernel's fallible primitives, with the site and the operands attached.
//!
//! # Interface
//!
//! ```text
//! mp(imp, arg)                  -> DResult<Thm>              // Thm::mp
//! ax_inst(phi, t)               -> DResult<Thm>              // Thm::ax_inst
//! ax_dist(x, phi, psi)          -> DResult<Thm>              // Thm::ax_dist
//! gen(x, thm)                   -> DResult<Thm>              // Thm::gen_checked
//! ax_replacement(env, x, y, phi)-> DResult<Thm>              // Thm::ax_replacement
//! define(env, xs, y, phi, witness) -> DResult<(FnSym, Thm)>  // kernel::thm::define
//!
//! phi.imp_parts()               -> DResult<(Formula, Formula)>  // Formula::as_imp
//! phi.eq_parts()                -> DResult<(Term, Term)>        // Formula::as_eq
//! phi.mem_parts()               -> DResult<(Term, Term)>        // Formula::as_mem
//! ```
//!
//! # Why these exist, and why they are *here*
//!
//! Nine kernel entry points return `Option`, and each `None` means the same
//! thing: **this call was passed data it cannot accept**. Until now that `None`
//! travelled up through a dozen frames as an anonymous `None`, and the caller
//! that finally saw it knew neither which primitive refused nor with what.
//!
//! The fix does not belong in `kernel/`. The kernel is the entire trusted base
//! and every line of it has to be re-read adversarially; adding diagnostics
//! there would inflate the thing whose whole design goal is to stay small, and
//! it would put a `&'static str` and a `Vec<Operand>` inside the crate that is
//! forbidden I/O and formatting. So the shims live at `derived/`'s boundary
//! instead. Each is `#[track_caller]`, calls the kernel version verbatim, and
//! on `None` records the *caller's* `file:line` together with the operands the
//! primitive rejected. **The kernel is unchanged and the TCB is unchanged.**
//!
//! Every failure here is [`DerErr::Assembly`], never a decline. These
//! primitives fail only on malformed input — `mp` whose antecedent is not the
//! argument's conclusion, an instantiation of a formula that is not a `∀`, a
//! destructuring of a formula that is not the connective asked for. In each
//! case the *derivation that built the operands* is wrong. There is no correct
//! program that reaches one of these on purpose, which is why the split is
//! mechanical here and only needs judgement at the explicit refusals in the
//! rest of the crate.
//!
//! # `gen` is the panicking rule, made fallible
//!
//! [`kernel::Thm::gen`] **panics** when the generalised variable is free in a
//! hypothesis; `Thm::gen_checked` is the same rule reporting instead. R6′-I3
//! bans the panicking form in `checker/` but explicitly does *not* apply it to
//! `derived/`, which has ~700 `gen` call sites and relied on I1 — "`derived/`
//! never assumes" — to keep the panic unreachable. That argument no longer
//! holds on its own: `crate::discharge` introduces hypotheses inside this
//! crate. [`gen`] here is `gen_checked` with a site attached, so a derivation
//! that generalises over a variable of its own assumption gets a counted
//! `Assembly` rather than aborting a corpus run in which declines are normal.

use crate::err::{DResult, DerErr, Operand, Site};
use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

/// Modus ponens. `Assembly` when `imp`'s conclusion is not an implication whose
/// antecedent is `arg`'s conclusion.
#[track_caller]
pub fn mp(imp: &Thm, arg: &Thm) -> DResult<Thm> {
    match Thm::mp(imp, arg) {
        Some(t) => Ok(t),
        None => Err(DerErr::assembly(Site::caller(), "Thm::mp", vec![Operand::thm("imp", imp), Operand::thm("arg", arg)])),
    }
}

/// Universal instantiation `(∀x. φ) → φ[t/x]`. `Assembly` when `phi` is not
/// universally quantified.
#[track_caller]
pub fn ax_inst(phi: Formula, t: Term) -> DResult<Thm> {
    match Thm::ax_inst(phi.clone(), t.clone()) {
        Some(x) => Ok(x),
        None => Err(DerErr::assembly(Site::caller(), "Thm::ax_inst", vec![Operand::formula("phi", &phi), Operand::term("t", &t)])),
    }
}

/// Distribution `(∀x. (φ → ψ)) → (φ → ∀x. ψ)`. `Assembly` when `x` occurs free
/// in `phi`, which is the side condition the rule genuinely has to check.
#[track_caller]
pub fn ax_dist(x: FreeVar, phi: Formula, psi: Formula) -> DResult<Thm> {
    match Thm::ax_dist(x, phi.clone(), psi.clone()) {
        Some(t) => Ok(t),
        None =>
            Err(DerErr::assembly(Site::caller(), "Thm::ax_dist", vec![
                Operand::var("x", x),
                Operand::formula("phi", &phi),
                Operand::formula("psi", &psi),
            ])),
    }
}

/// Generalisation, with the side condition reported rather than raised.
/// `Assembly` when `x` is free in a hypothesis of `thm`.
///
/// This is [`kernel::Thm::gen_checked`]; use it in preference to
/// [`kernel::Thm::gen`], which panics on the same input.
#[track_caller]
pub fn gen(x: FreeVar, thm: &Thm) -> DResult<Thm> {
    match Thm::gen_checked(x, thm) {
        Some(t) => Ok(t),
        None => Err(DerErr::assembly(Site::caller(), "Thm::gen_checked", vec![Operand::var("x", x), Operand::thm("thm", thm)])),
    }
}

/// Replacement, as a scheme. `Assembly` when `x` and `y` are not distinct, or
/// collide with the variables the scheme generates for itself.
#[track_caller]
pub fn ax_replacement(env: &mut Env, x: FreeVar, y: FreeVar, phi: Formula) -> DResult<Thm> {
    match Thm::ax_replacement(env, x, y, phi.clone()) {
        Some(t) => Ok(t),
        None => Err(DerErr::assembly(
            Site::caller(),
            "Thm::ax_replacement",
            vec![Operand::var("x", x), Operand::var("y", y), Operand::formula("phi", &phi)],
        )),
    }
}

/// Definitional extension. `Assembly` when the witness does not prove exactly
/// `∀x⃗. ∃!y. φ`, **or when it proves it only under hypotheses**.
///
/// The second case is this project's second soundness bug, caught in the
/// kernel: `define` returns an axiom carrying no hypotheses, so a witness with
/// a non-empty `Γ` would have it silently dropped. The kernel rejects; the
/// operands here are what makes the rejection diagnosable, because the two
/// causes are indistinguishable in a bare `None`.
#[track_caller]
pub fn define(
    env: &mut Env,
    xs: &[FreeVar],
    y: FreeVar,
    phi: Formula,
    witness: &Thm,
) -> DResult<(FnSym, Thm)> {
    match kernel::thm::define(env, xs, y, phi.clone(), witness) {
        Some(p) => Ok(p),
        None => Err(DerErr::assembly(Site::caller(), "kernel::thm::define", vec![
            Operand::var("y", y),
            Operand::formula("phi", &phi),
            Operand::thm("witness", witness),
        ])),
    }
}

/// The kernel's three formula destructors, as `DResult`.
///
/// They are an extension trait rather than free functions so that the ~750
/// existing `phi.as_imp()?` call sites become `phi.imp_parts()?` — a rename, not
/// a re-shaping of the expression. The names differ from the kernel's `as_imp`
/// / `as_eq` / `as_mem` because an inherent method wins over a trait method, so
/// a same-named trait method would silently never be called.
pub trait Shape {
    /// The two sides of an implication. `Assembly` when the formula is not one.
    #[track_caller]
    fn imp_parts(&self) -> DResult<(Formula, Formula)>;
    /// The two sides of an equation. `Assembly` when the formula is not one.
    #[track_caller]
    fn eq_parts(&self) -> DResult<(Term, Term)>;
    /// The two sides of a membership. `Assembly` when the formula is not one.
    #[track_caller]
    fn mem_parts(&self) -> DResult<(Term, Term)>;
}

impl Shape for Formula {
    #[track_caller]
    fn imp_parts(&self) -> DResult<(Formula, Formula)> {
        let phi = self;
        match self.as_imp() {
            Some(p) => Ok(p),
            None =>
                Err(DerErr::assembly(Site::caller(), "Formula::as_imp", vec![Operand::formula("phi", phi)])),
        }
    }

    #[track_caller]
    fn eq_parts(&self) -> DResult<(Term, Term)> {
        let phi = self;
        match self.as_eq() {
            Some(p) => Ok(p),
            None => Err(DerErr::assembly(Site::caller(), "Formula::as_eq", vec![Operand::formula("phi", phi)])),
        }
    }

    #[track_caller]
    fn mem_parts(&self) -> DResult<(Term, Term)> {
        let phi = self;
        match self.as_mem() {
            Some(p) => Ok(p),
            None =>
                Err(DerErr::assembly(Site::caller(), "Formula::as_mem", vec![Operand::formula("phi", phi)])),
        }
    }
}
