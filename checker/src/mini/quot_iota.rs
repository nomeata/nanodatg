//! **`Quot.lift`'s computation rule at `u ≥ 1`** — the ι certificate
//! `⟦Quot.lift α r β f h (Quot.mk α r a)⟧ = ⟦f a⟧`.
//!
//! # Interface
//!
//! ```text
//! quot_iota::fire(checker, inst, head_tm, args, arg_tms, ctor_args) -> Result<(Thm, Term), Gap>
//! ```
//!
//! Called from [`crate::mini::kernel::Checker::whnf`]'s recursor arm, beside
//! [`crate::mini::iota_dep::fire`] and for the same reason: `Quot.lift` is a
//! `ConstantInfo::Recursor` — `add_quot`'s own classification — so it reaches
//! that site and finds no route. `Checker::nest_iota` is gated on
//! [`crate::mini::direct::clause_for`] applied to the *owner*, which is `Quot` and has
//! no direct clause; `iota_dep::fire` is about an inductive declaration's
//! `DepRecursor::iota`. Neither is this one.
//!
//! # The equation, and where each piece comes from
//!
//! ```text
//! app⁶(⟦Quot.lift.{u,v}⟧, A, r̄, B, f̄, ⟦h⟧, ⟦q⟧)
//!   = app(lift(A,R̄,f̄), ⟦q⟧)              β down the eliminator's nest, lifted
//!   = app(lift(A,R̄,f̄), class(A,R̄,ā))     β down ⟦Quot.mk.{u}⟧'s nest, lifted
//!   = app(f̄, ā)                           lift_beta
//! ```
//!
//! **Two β chains and two congruences, and `QUOT-MODEL.md` §6 finding 4 names
//! neither.** The note says `lift_beta`'s two antecedents — `compat(A,R̄,f̄)` and
//! `ā ∈ A` — are dischargeable at the redex, and they are; what it does not say
//! is that the redex is not in `lift_beta`'s shape until both nests have been
//! walked. That is `SCOPING.md` §1's sixth category, upward half, twice more.
//!
//! The nest is **five** deep and the spine is six long — `⟦Quot.lift α r β f h⟧`
//! is the clause and the major is applied to it — so [`Interp::beta_spine`]
//! runs on the first five and the major is lifted over by one `congr`. That is
//! also why this returns **one** equation about the whole spine: `whnf`'s
//! `step!` lifts a leg over the arguments still on the stack, so a per-level leg
//! would have to be composed anyway and composing after the fact is
//! `Gap::ConvCompose`. `iota_dep` emits one `step!` for the same reason.
//!
//! # `compat` is re-derived here, and that is the right call
//!
//! [`crate::mini::quot_classes::lift_at`] derives `compat(A,R̄,f̄)` and spends it,
//! which reads like `MINI-HANDOFF.md` §2's register — a value computed at a site
//! that outlives nothing. It is not, and the discriminator is *does the consumer
//! want it at the same terms?* It does not: `lift_at` derives it at the
//! eliminator nest's own binder variables, under that nest's open scopes, so its
//! `Γ` cannot be discharged there; here the terms are the redex's own arguments.
//! **Share the derivation, not the result** —
//! [`crate::mini::quot_classes::compat_at`] is `pub(crate)` for exactly this, and
//! storing the theorem would store one about the wrong terms.

use kernel::{Formula, Term, Thm};

use crate::mini::ev::{Cause, Gap};
use crate::mini::expr::{Name, E};
use crate::mini::kernel::Checker;

const SHAPE: &str = "quotient iota: the redex's arity or its levels disagree";
const ARG: &str = "quotient iota: an argument has no interpretation or no typing";
const STORE: &str = "quotient iota: a Quot primitive is not in the store at this level";
const NEST: &str = "quotient iota: the beta chain down the eliminator's nest";
const MAJOR: &str = "quotient iota: the major is not Quot.mk at the eliminator's own parameters";
const COMPAT: &str = "quotient iota: Lean's h does not yield compat at the redex";
const RULE: &str = "quotient iota: lift_beta does not instantiate here";

/// The ι certificate at one `Quot.lift` use site, and the reduct's
/// interpretation.
///
/// `args`/`arg_tms` are the six arguments up to and including the major, with
/// their interpretations; `ctor_args` is the major's own spine `α r a`.
///
/// Every shape is **checked** rather than assumed — the levels, the two arities,
/// that the major's β chain lands on the term the spine's last argument already
/// is, and the final endpoints. A mismatch is a `Gap` with its own reason, never
/// a wrong equation.
pub(crate) fn fire(
    c: &mut Checker<'_, '_>,
    inst: &[u32],
    head_tm: &Term,
    args: &[E],
    arg_tms: &[Term],
    ctor_args: &[E],
) -> Result<(Thm, Term), Gap> {
    let bad = |w: &'static str| Gap::Recursor(Name::str(&Name::simple("Quot"), "lift"), w, Cause::Threading);
    let (&u, &v) = match (inst.first(), inst.get(1)) {
        (Some(u), Some(v)) => (u, v),
        _ => return Err(bad(SHAPE)),
    };
    // `u = 0` is the identity clause's ι and `v = 0` makes the whole redex a
    // proof; both are `crate::mini::quot`'s and both already derive.
    if u == 0 || v == 0 {
        return Err(bad(SHAPE))
    }
    if args.len() != 6 || arg_tms.len() != 6 || ctor_args.len() != 3 {
        return Err(bad(SHAPE))
    }

    // ── the arguments' typings, by inference on the arguments themselves ────
    let mems = typings(c, args)?;
    let c_tms_mems = typings(c, ctor_args)?;
    let c_tms: Vec<Term> = ctor_args
        .iter()
        .map(|e| c.infer_type(e).ok().and_then(|t| t.tm).ok_or_else(|| bad(ARG)))
        .collect::<Result<_, _>>()?;

    let mk_former = c
        .stored_term(&Name::str(&Name::simple("Quot"), "mk"), &[u])
        .ok_or_else(|| bad(STORE))?;
    let eq_former = c.stored_term(&Name::simple("Eq"), &[v]).ok_or_else(|| bad(STORE))?;

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let q = ip.quotient().ok_or(Gap::Quotient(u, crate::mini::quot::Prim::Lift))?;
    let ap = ip.prelude.tower.sums.ap.clone();
    let ap_sym = ap.app;
    let (a, r, b_ty, f) =
        (arg_tms[0].clone(), arg_tms[1].clone(), arg_tms[2].clone(), arg_tms[3].clone());
    let graph = q.graph(ip, &a, &r);
    let major = arg_tms[5].clone();

    // ── step 1: down the eliminator's own nest, then over the major ─────────
    //
    // Five, not six: `⟦Quot.lift α r β f h⟧` is the clause and the major is
    // applied to it. The `congr` is what makes the result one equation about
    // the whole spine, which is the shape `step!` wants.
    let (bot, beta) = ip
        .beta_spine(head_tm, &arg_tms[..5], &mems[..5])
        .ok_or_else(|| bad(NEST))?;
    let want_bot = ip.mk(q.q.lift, vec![a.clone(), graph.clone(), f.clone()]);
    if bot != want_bot {
        return Err(bad(NEST))
    }
    let step1 = derived::congr(&mut ip.env_mut(), ap_sym, &[beta, Thm::eq_refl(major.clone())])
        .ok_or_else(|| bad(NEST))?;

    // ── step 2: the major, down `⟦Quot.mk.{u}⟧`'s nest ──────────────────────
    // The bottom of `⟦Quot.mk.{u}⟧`'s nest — the class term — is deliberately
    // not compared here, and it is not unchecked either: step 3 is `lift_beta`
    // at `[a, graph, f, x]`, whose left endpoint is `app(lift(A,R̄,f),
    // class(A,R̄,x))`, so `eq_trans` composes step 2 with it only if this
    // bottom *is* `class(a,graph,x)` syntactically. Naming it and comparing it
    // would restate the chain's own requirement in a second spelling; what is
    // checked instead is the thing a reader can verify, that the β chain's left
    // endpoint is the major the caller already holds.
    let (_klass, mk_beta) =
        ip.beta_spine(&mk_former, &c_tms, &c_tms_mems).ok_or_else(|| bad(MAJOR))?;
    if mk_beta.concl().as_eq().map(|(l, _)| l) != Some(major) {
        return Err(bad(MAJOR))
    }
    let step2 = derived::congr(&mut ip.env_mut(), ap_sym, &[Thm::eq_refl(bot.clone()), mk_beta])
        .ok_or_else(|| bad(MAJOR))?;

    // ── step 3: `lift_beta`, whose two antecedents the redex supplies ───────
    let compat = crate::mini::quot_classes::compat_at(
        &q, ip, &eq_former, &a, &r, &b_ty, &mems[2], &f, &mems[3], &mems[4],
    )
    .ok_or_else(|| bad(COMPAT))?;
    let x = c_tms[2].clone();
    let x_mem = c_tms_mems[2].clone();
    let rule = derived::inst_all(&q.q.lift_beta, &[a, graph, f.clone(), x.clone()])
        .ok_or_else(|| bad(RULE))?;
    let step3 = Thm::mp(&rule, &derived::and_intro(&compat, &x_mem)).ok_or_else(|| bad(RULE))?;

    // ── the chain, and the reduct ───────────────────────────────────────────
    let to_tm = ip.app(f, x);
    // Two statements, not a chain: the first `env_mut()` guard is a
    // statement-long temporary, and the closure's own `env_mut()` would be a
    // re-entrant borrow of the shared core.
    let chain12 = derived::eq_trans(&mut ip.env_mut(), &step1, &step2);
    let chain = chain12
        .and_then(|t| derived::eq_trans(&mut ip.env_mut(), &t, &step3))
        .ok_or_else(|| bad(RULE))?;
    let lhs = arg_tms.iter().fold(head_tm.clone(), |acc, t| ap.apply(acc, t.clone()));
    if *chain.concl() != Formula::eq(lhs, to_tm.clone()) {
        return Err(bad(RULE))
    }
    Ok((chain, to_tm))
}

/// Each expression's typing, by inference. The interpretation is not returned:
/// `whnf` already holds the terms, and re-deriving them here would risk two
/// spellings of one argument.
fn typings(c: &mut Checker<'_, '_>, es: &[E]) -> Result<Vec<Thm>, Gap> {
    let bad = Gap::Recursor(Name::str(&Name::simple("Quot"), "lift"), ARG, Cause::Threading);
    es.iter()
        .map(|e| {
            c.infer_type(e)
                .ok()
                .and_then(|t| t.ev.thm().cloned())
                .ok_or_else(|| bad.clone())
        })
        .collect()
}
