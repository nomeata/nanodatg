//! The failure channel: [`derived::DerErr`], and the `#[track_caller]` shims in
//! `derived::prim` that attach a site and the rejected operands to a kernel
//! primitive's `None`.
//!
//! What these pin, and why each pin exists:
//!
//! * **the shim agrees with the kernel** — on good input the shim's `Ok` is the
//!   kernel's `Some`, value for value. A shim that quietly re-derived would be a
//!   second implementation of a rule inside an untrusted crate, and nothing else
//!   would catch it.
//! * **the site is the *caller's* line, not the shim's.** This is the whole
//!   point of `#[track_caller]` and it is the thing that silently regresses if
//!   somebody adds a wrapper layer without the attribute. Pinned by taking the
//!   line number of the call and comparing.
//! * **the operands survive.** "`mp` failed" without them is the `None` this
//!   machinery replaces, so the count and the labels are pinned.
//! * **a decline is not an assembly failure.** The two variants are the reason
//!   the type exists; a consumer that treats them alike (panicking on a decline,
//!   or logging an assembly failure as routine) is the failure mode, so
//!   `is_decline`/`is_assembly` are pinned to be exclusive.

use derived::err::{DResult, DerErr, Operand, Shown, Site};
use derived::prim::{self, Shape};
use kernel::{Env, Formula, Term, Thm};

/// `⊢ ∀x. x = x`, a formula that is genuinely a `∀`, to instantiate.
fn forall_refl(env: &mut Env) -> (Formula, Thm) {
    let x = env.fresh_var();
    let t = Thm::gen(x, &Thm::eq_refl(Term::var(x)));
    (t.concl().clone(), t)
}

#[test]
fn shim_agrees_with_the_kernel_on_good_input() {
    let mut env = Env::new();
    let (phi, _) = forall_refl(&mut env);
    let a = env.fresh_var();
    // ax_inst
    let want = Thm::ax_inst(phi.clone(), Term::var(a)).expect("the formula is a forall");
    let got = prim::ax_inst(phi.clone(), Term::var(a)).expect("so the shim accepts it too");
    assert_eq!(want, got);

    // mp, on `⊢ φ → φ` against `⊢ φ`
    let p = Formula::eq(Term::var(a), Term::var(a));
    let imp = derived::imp_refl(p.clone());
    let arg = Thm::eq_refl(Term::var(a));
    assert_eq!(Thm::mp(&imp, &arg).expect("shapes line up"), prim::mp(&imp, &arg).expect("ditto"));

    // gen, on a theorem with no hypotheses
    assert_eq!(Thm::gen(a, &arg), prim::gen(a, &arg).expect("no hypotheses, so no side condition"));

    // the destructors
    assert_eq!(p.as_eq().expect("an equation"), p.eq_parts().expect("an equation"));
    assert_eq!(imp.concl().as_imp().expect("an implication"), imp.concl().imp_parts().expect("ditto"));
}

#[test]
fn mp_on_a_mismatched_antecedent_is_an_assembly_failure_with_both_operands() {
    let mut env = Env::new();
    let a = env.fresh_var();
    let b = env.fresh_var();
    let imp = derived::imp_refl(Formula::eq(Term::var(a), Term::var(a)));
    let arg = Thm::eq_refl(Term::var(b)); // `⊢ b = b`, not the antecedent
    let line = line!() + 1;
    let e = prim::mp(&imp, &arg).expect_err("the antecedent is `a = a`, the argument is `b = b`");

    assert!(e.is_assembly(), "a mismatched antecedent is a bug in the caller, not a refusal");
    assert!(!e.is_decline());
    assert_eq!(e.reason(), "Thm::mp");
    // The site is *this* file and *this* line — the `#[track_caller]` property.
    assert_eq!(e.site().line(), line, "the site must be the call, not the shim");
    assert!(e.site().file().ends_with("err.rs"), "got {}", e.site().file());

    let ops = e.operands();
    assert_eq!(ops.len(), 2, "both premises are needed to see why they do not line up");
    assert_eq!(ops[0].label, "imp");
    assert_eq!(ops[1].label, "arg");
    match (&ops[0].value, &ops[1].value) {
        (Shown::Thm(i), Shown::Thm(g)) => {
            assert_eq!(i, &imp);
            assert_eq!(g, &arg);
        }
        _ => panic!("mp's operands are the two theorems it was handed"),
    }
    // And it renders with them.
    let s = format!("{e}");
    assert!(s.contains("Thm::mp was passed bad data"), "{s}");
    assert!(s.contains("imp = "), "{s}");
    assert!(s.contains("arg = "), "{s}");
}

#[test]
fn each_primitive_names_itself() {
    let mut env = Env::new();
    let a = env.fresh_var();
    let b = env.fresh_var();
    let not_forall = Formula::eq(Term::var(a), Term::var(a));

    let e = prim::ax_inst(not_forall.clone(), Term::var(a)).expect_err("not universally quantified");
    assert_eq!(e.reason(), "Thm::ax_inst");
    assert_eq!(e.operands().len(), 2);

    // ax_dist's side condition: `x` must not occur free in `phi`.
    let e = prim::ax_dist(a, not_forall.clone(), not_forall.clone())
        .expect_err("`a` occurs free in phi");
    assert_eq!(e.reason(), "Thm::ax_dist");
    assert_eq!(e.operands().len(), 3);

    // ax_replacement rejects `x == y`, which would make the scheme unsound.
    let e = prim::ax_replacement(&mut env, a, a, not_forall.clone())
        .expect_err("the two designated variables must be distinct");
    assert_eq!(e.reason(), "Thm::ax_replacement");

    // The destructors, each on a formula of the wrong shape.
    let e = not_forall.imp_parts().expect_err("an equation is not an implication");
    assert_eq!(e.reason(), "Formula::as_imp");
    assert_eq!(e.operands().len(), 1);
    assert_eq!(e.operands()[0].label, "phi");
    let mem = Formula::mem(Term::var(a), Term::var(b));
    assert_eq!(mem.eq_parts().expect_err("a membership is not an equation").reason(), "Formula::as_eq");
    assert_eq!(not_forall.mem_parts().expect_err("an equation is not a membership").reason(), "Formula::as_mem");
}

/// The side condition on generalisation is the one that *panics* in
/// `Thm::gen`. `prim::gen` reports it, which is what lets a corpus run count a
/// gap rather than abort.
#[test]
fn generalising_over_a_hypothesis_variable_reports_rather_than_panics() {
    let mut env = Env::new();
    let a = env.fresh_var();
    let b = env.fresh_var();
    // `{a ∈ b} ⊢ a ∈ b` — hypothetical, with `a` free in the hypothesis.
    let h = derived::discharge::assuming(Formula::mem(Term::var(a), Term::var(b)));
    assert!(!h.hyps().is_empty());

    let e = prim::gen(a, &h).expect_err("`a` is free in the hypothesis");
    assert!(e.is_assembly());
    assert_eq!(e.reason(), "Thm::gen_checked");
    assert_eq!(e.operands().len(), 2);
    assert_eq!(e.operands()[0].label, "x");
    assert_eq!(e.operands()[1].label, "thm");

    // `b` is free in the hypothesis too, but generalising over a variable that
    // is *not* is fine, and the shim passes it through.
    let c = env.fresh_var();
    assert!(prim::gen(c, &h).is_ok());
}

#[test]
fn a_decline_is_not_an_assembly_failure_and_carries_no_operands() {
    fn refuse() -> DResult<Thm> { Err(derived::decline!("a fixture that always refuses")) }
    let e = refuse().expect_err("it always refuses");
    assert!(e.is_decline());
    assert!(!e.is_assembly());
    assert_eq!(e.reason(), "a fixture that always refuses");
    assert!(e.operands().is_empty(), "a decline is on the hot path and allocates nothing");
    assert_eq!(format!("{e}"), format!("{}: declined: a fixture that always refuses", e.site()));
    assert!(e.site().file().ends_with("err.rs"));
}

/// A self-check is on the **assembly** side, and keeps its operands.
///
/// Most refusals in `derived/` are the code checking its own work rather than
/// a kernel primitive refusing, so they cannot come from `prim`. They are bugs
/// in exactly the same way, and the thing that regresses silently is a guard
/// drifting to `decline!` — at which point a mis-assembled derivation reads as
/// routine traffic in a log, which is the `None` this machinery replaces.
#[test]
fn a_self_check_is_an_assembly_failure_and_keeps_its_operands() {
    let mut env = Env::new();
    let a = env.fresh_var();
    let phi = Formula::eq(Term::var(a), Term::var(a));
    let e = derived::assembly!("a fixture: the shape it built", Operand::formula("phi", &phi));
    assert!(e.is_assembly());
    assert!(!e.is_decline(), "a self-check is a bug, not the contract working");
    assert_eq!(e.reason(), "a fixture: the shape it built");
    assert_eq!(e.operands().len(), 1);
    assert_eq!(e.operands()[0].label, "phi");
    assert!(matches!(e.operands()[0].value, Shown::Formula(_)));
    assert!(e.site().file().ends_with("err.rs"));
}

/// An unmigrated `Option` reports as an assembly failure at the **caller's**
/// line, naming the construction that refused.
///
/// The migration to `DResult` runs module by module, so a migrated module keeps
/// calling unmigrated ones and their reason was thrown away at the boundary.
/// Naming the path is the honest amount of information left; the site has to be
/// the caller's, or the report would point at `err.rs` for every one of them —
/// the same collapse `#[track_caller]` exists to prevent in `prim`.
#[test]
fn an_unmigrated_option_reports_at_the_caller_naming_what_refused() {
    let line = line!() + 1;
    let e = derived::err::imported::<Thm>("crate::fixture::never", None).expect_err("None");
    assert!(e.is_assembly());
    assert_eq!(e.reason(), "crate::fixture::never");
    assert_eq!(e.site().line(), line, "the site is the caller's line, not err.rs's");
    assert!(e.site().file().ends_with("err.rs"));
    assert!(e.operands().is_empty(), "the operands were lost at the Option boundary");
    assert_eq!(derived::err::imported("crate::fixture::always", Some(7)).ok(), Some(7));
}

/// `?` propagates the *first* reason unchanged through intermediate frames —
/// §0.4's rule, obtained from the type rather than from a discipline.
#[test]
fn the_reason_survives_the_frames_it_passes_through() {
    fn inner(env: &mut Env) -> DResult<Thm> {
        let a = env.fresh_var();
        prim::ax_inst(Formula::eq(Term::var(a), Term::var(a)), Term::var(a))
    }
    fn middle(env: &mut Env) -> DResult<(Formula, Formula)> {
        let t = inner(env)?;
        t.concl().imp_parts()
    }
    fn outer(env: &mut Env) -> DResult<Formula> { Ok(middle(env)?.0) }

    let mut env = Env::new();
    let e = outer(&mut env).expect_err("inner stops it");
    assert_eq!(e.reason(), "Thm::ax_inst", "the outermost frame reports the innermost cause");
    assert!(e.site().file().ends_with("err.rs"));
}

/// A hand-built `Site`/`Operand` pair renders the way the shims' do, so a
/// consumer can format any `DerErr` uniformly.
#[test]
fn rendering_is_uniform() {
    let mut env = Env::new();
    let a = env.fresh_var();
    let phi = Formula::eq(Term::var(a), Term::var(a));
    let e = DerErr::assembly(
        Site::new("derived/src/somewhere.rs", 17),
        "Thm::mp",
        vec![Operand::formula("phi", &phi)],
    );
    let s = format!("{e}");
    assert!(s.starts_with("derived/src/somewhere.rs:17: Thm::mp was passed bad data"), "{s}");
    assert!(s.contains("\n    phi = "), "{s}");
}
