//! **A unit-like structure's two elements are equal** — `⊢ ⟦e₁⟧ = ⟦e₂⟧` at a
//! declaration Lean's `isDefEq` accepts by η for unit-likes.
//!
//! # Interface
//!
//! ```text
//! unit_like::certify(checker, t1, t2) -> Result<Thm, Gap>
//! ```
//!
//! Called from [`crate::kernel::Checker::proof_irrel_ev`]'s non-`Prop` branch,
//! which is where Lean's unit-like η lands after `is_prop_or_unit_ev` has
//! *decided*. The probe accepts; this only certifies, and its failure is a gap
//! rather than a rejection — the same split
//! [`crate::proj_data::structure_eta`] and [`crate::fun_eta`] make.
//!
//! # The theorem was built and the row was filed against the wrong crate
//!
//! The site's own comment read *"it needs the structure's subsingleton lemma,
//! which §9 zone B has not reached"*, and `MINI-HANDOFF.md` §20 item 5 reported
//! a search of `derived/` that found nothing. Both were wrong, and §21 records
//! how: [`derived::inductive::family::LeProp`] carries
//!
//! ```text
//! ⊢ ∀x ∀y. ((x ∈ A_φ(p⃗) ∧ y ∈ A_φ(p⃗)) → x = y)      [LeProp::subsingleton]
//! ```
//!
//! and [`crate::class_s`] **already builds a `LeProp` for every class-(S)
//! declaration**. Nothing is owed by `derived/`; this is wiring, which makes it
//! the second of `ev.rs`'s four `Cause::Library` gaps that was never library
//! debt.
//!
//! # Why a unit-like structure is class (S) at every `σ`
//!
//! `PUnit.{u}`'s resultant sort is `Sort (Param u)`, so `provably_nonzero`
//! answers **false** — it reads the declaration's own level *expression*, not
//! the ground instantiation (`QUOT-MODEL.md` §4.2, and it is the same
//! per-declaration rule Lean's eliminator trichotomy runs on). So the
//! trichotomy sends it down the class-(S) route at `u = 1` exactly as at
//! `u = 0`, and `LeProp` is available wherever the probe fires.
//!
//! # What is general here and what declines
//!
//! The parameters are taken off the *whnf'd type's own spine* and their
//! interpretations inferred, so a parameterised unit-like structure is handled
//! rather than assumed away; `LeProp::subsingleton` is stated open in `p⃗` and
//! is generalised and re-instantiated at them. What declines by name is a
//! declaration whose class-(S) translation is not available — an indexed one,
//! for instance, whose carrier is `LeIndex`'s and not `LeProp`'s.

use kernel::{Formula, Term, Thm};

use crate::env::ConstantInfo;
use crate::ev::Gap;
use crate::ground;
use crate::kernel::{Checker, Typing};

/// **`Γ ⊢ ⟦e₁⟧ = ⟦e₂⟧`** for two elements of one unit-like structure.
///
/// `t1` and `t2` are the two sides' `Typing`s, already inferred by the caller;
/// their `ev`s are the memberships `LeProp::subsingleton` consumes, and nothing
/// is re-derived. The declaration is read off `t1`'s **type**, whnf'd, so a
/// definitional abbreviation for the structure resolves to the structure.
pub(crate) fn certify(
    c: &mut Checker<'_, '_>,
    t1: &Typing,
    t2: &Typing,
) -> Result<Thm, Gap> {
    let (t1, t2) = (t1.clone(), t2.clone());
    // **The memberships are transported, not read off.** A structure reached
    // through a definitional abbreviation — `Unit`, whose value is `PUnit.{1}`
    // — has an interpretation of its *own*: `⟦Unit.{}⟧` is a fresh symbol with
    // δ's equation to `⟦PUnit.{1}⟧` beside it, so `t1.ev` states membership in
    // the abbreviation while `LeProp::subsingleton` is about `A_φ(p⃗)`.
    // [`Checker::whnf_typing`] carries both memberships along that equation,
    // which is the general move and not a `Unit` special case: `103_unitEta2`
    // names `PUnit.{1}` directly and needs no transport, `102_unitEta1` names
    // `Unit` and does.
    let (tw, _, t1) = c.whnf_typing(t1.clone()).map_err(|_| Gap::Classifier)?;
    let (_, _, t2) = c.whnf_typing(t2.clone()).map_err(|_| Gap::Classifier)?;
    let (Some(x), Some(y)) = (t1.tm.clone(), t2.tm.clone()) else {
        return Err(Gap::NoEndpoint)
    };
    let x_mem = t1.ev.thm().cloned().ok_or(Gap::NoEndpoint)?;
    let y_mem = t2.ev.thm().cloned().ok_or(Gap::NoEndpoint)?;

    // Which declaration, at which ground levels, with which parameters.
    let (head, args) = crate::expr::get_app(&tw);
    let crate::expr::Expr::Const(name, ls) = &*head else { return Err(Gap::NoEndpoint) };
    let name = *name;
    let empty = std::collections::HashMap::new();
    let inst: Vec<u32> = ls
        .iter()
        .map(|l| ground::eval(l, &empty))
        .collect::<Option<_>>()
        .ok_or(Gap::SymbolicLevel)?;
    let bad = || Gap::UnitLike(name);
    let Some(ConstantInfo::Inductive { num_params, .. }) = c.environment().get(&name) else {
        return Err(bad())
    };
    let np = *num_params as usize;
    if args.len() < np {
        return Err(bad())
    }
    // The parameters' interpretations, by inference on the type's own spine.
    let ps: Vec<Term> = args[..np]
        .iter()
        .map(|a| c.infer_type(a).ok().and_then(|t| t.tm).ok_or_else(bad))
        .collect::<Result<_, _>>()?;

    let cs = crate::class_s::of(c, &name, &inst).ok_or_else(bad)?;
    if cs.params.len() != np {
        return Err(bad())
    }
    // `LeProp::subsingleton` is stated **open** in `p⃗`, so it is generalised
    // and re-instantiated at the spine's own parameters. At `np = 0` — `PUnit`,
    // and every unit-like in this corpus — both steps are the identity.
    let gen = crate::rec_dep::gen_all_checked(&cs.params, &cs.lp.subsingleton).ok_or_else(bad)?;
    let at_ps = derived::inst_all(&gen, &ps).ok_or_else(bad)?;
    let at_xy = derived::inst_all(&at_ps, &[x.clone(), y.clone()]).ok_or_else(bad)?;
    let out = Thm::mp(&at_xy, &derived::and_intro(&x_mem, &y_mem)).ok_or_else(bad)?;
    if *out.concl() != Formula::eq(x, y) {
        return Err(bad())
    }
    Ok(out)
}
