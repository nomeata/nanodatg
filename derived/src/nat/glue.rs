//! Equational and inductive glue for the arithmetic on `ω`.
//!
//! # Interface
//!
//! ```text
//! Chain::start(t) / Chain::from(⊢ a = b)   a running equation
//! Chain::then(⊢ b = c)                     extends it on the right
//! Chain::then_rev(⊢ c = b)                 the same, step read backwards
//! Chain::done(env)                         folds the links into one theorem
//! congr1(env, f, ⊢ a = b)                  `⊢ f(a) = f(b)`
//! congr2_l / congr2_r                      the same at a binary symbol
//! congr_tmpl(env, x, t(x), ⊢ a = b)        `⊢ t(a) = t(b)`, at any position
//! induct(env, core, x, φ, base, step)      `⊢ ∀x. (x ∈ ω → φ(x))`
//! induct_step(core, x, φ, body)            its step premise, natural-deduction style
//! gen_all(&[x⃗], ⊢ φ)                       `⊢ ∀x⃗. φ`, side condition reported
//! imported("f", f(..))                     an `Option` from the unmigrated crate
//! ```
//!
//! # Why this file exists
//!
//! Every arithmetic lemma below is a chain of rewrites assembled under an
//! induction hypothesis. The kernel *has* hypotheses ([`Thm::assume`] /
//! [`Thm::implies_intr`]), and every derived rule this file calls propagates
//! them through [`Thm::mp`]'s union, so the natural-deduction shape is
//! available and there is no need for the combinator gymnastics
//! [`crate::recursion::hyp`] needs. What is missing is only the bookkeeping:
//! a chain of `eq_trans` calls written out by hand is unreadable at ten links,
//! and the induction scheme wants its two premises assembled in one particular
//! shape. Both are mechanical, and both are here so that no arithmetic file
//! repeats them.
//!
//! Nothing here is trusted and nothing here builds a `Thm` other than through
//! the kernel's own rules.
//!
//! # Why `gen_all` is shadowed here
//!
//! [`crate::gen_all`] folds [`kernel::Thm::gen`], which **panics** when the
//! generalised variable is free in a hypothesis. Everywhere else in `derived/`
//! that is unreachable, because nothing else assumes; [`crate::nat`] is the one
//! module that does — [`crate::discharge`]'s only importers are its seven files
//! — so it is the one module where a mis-ordered `discharge`/`gen_all` pair is a
//! live way to abort a run in which declines are normal traffic. The [`gen_all`]
//! below is the same fold over [`crate::prim::gen`], so the side condition
//! arrives as an [`crate::err::DerErr::Assembly`] naming the variable and the
//! theorem.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::discharge::{assuming, discharge};

use crate::err::{DResult, DerErr, Site};
use crate::prim::{self, Shape};
use crate::recursion::induction::induction_scheme;
use crate::recursion::naturals::OmegaCore;
use crate::rules::{congr_arg, eq_symm, eq_trans};
use crate::{and_intro, decline};

/// A running equation `Γ ⊢ a = b`, extended on the right.
///
/// The point of the wrapper is that the *left* end never changes, so a
/// ten-link chain reads as ten steps rather than as ten nested `eq_trans`
/// calls whose intermediate terms have to be spelled out.
///
/// The links are **collected and folded at the end** rather than composed as
/// they arrive. That is not a performance choice: `eq_trans` needs a fresh
/// variable and therefore `&mut Env`, and a builder that took the environment
/// on every link could not have its links *computed* inline — every step of
/// every chain below is itself a congruence needing the same `&mut Env`, and
/// the borrow checker refuses the two at once. Deferring the folds to
/// [`Chain::done`] makes the natural spelling compile.
pub struct Chain {
    head: Thm,
    links: Vec<(Thm, bool)>,
}

impl Chain {
    /// Start at `⊢ t = t`.
    pub fn start(t: Term) -> Chain { Chain::from(Thm::eq_refl(t)) }

    /// Start from an equation already in hand.
    pub fn from(thm: Thm) -> Chain { Chain { head: thm, links: Vec::new() } }

    /// Extend `Γ ⊢ a = b` by `Δ ⊢ b = c`.
    pub fn then(mut self, step: Thm) -> Chain {
        self.links.push((step, false));
        self
    }

    /// Extend `Γ ⊢ a = b` by `Δ ⊢ c = b`, read backwards.
    pub fn then_rev(mut self, step: Thm) -> Chain {
        self.links.push((step, true));
        self
    }

    /// Fold the links into one equation.
    pub fn done(self, env: &mut Env) -> DResult<Thm> {
        let mut acc = self.head;
        for (step, rev) in self.links {
            let s = if rev { eq_symm(env, &step)? } else { step };
            acc = eq_trans(env, &acc, &s)?;
        }
        Ok(acc)
    }
}

/// From `Γ ⊢ a = b` and a **template** `t(x)` infer `Γ ⊢ t(a) = t(b)`.
///
/// [`crate::congr_arg`] rewrites one argument of one symbol; this rewrites at
/// an arbitrary position, named by putting a fresh variable there. The kernel
/// exposes no way to take a `Term` apart — `TermData` is `pub(crate)` — so a
/// context has to be *built* with its hole rather than found in a finished
/// term, which is the right discipline anyway: the caller says which occurrence
/// it means instead of hoping there is only one.
///
/// `x` must not occur in `a` or `b`. The environment is taken and unused: the
/// hole variable is supplied by the caller, who has to build the template with
/// it anyway, and every other rule in this file needs one — a signature that
/// did not would read as a different kind of rule.
pub fn congr_tmpl(_env: &mut Env, x: FreeVar, tmpl: &Term, ab: &Thm) -> DResult<Thm> {
    let (a, b) = ab.concl().eq_parts()?;
    if a.occurs_free(x) || b.occurs_free(x) {
        return Err(decline!("the template's hole variable occurs in the equation being rewritten"))
    }
    let lhs = crate::subst_term(tmpl, &[(x, a.clone())]);
    let phi = Formula::eq(lhs.clone(), tmpl.clone());
    let leib = Thm::eq_leibniz(a, b, x, phi);
    let step = prim::mp(&leib, ab)?;
    prim::mp(&step, &Thm::eq_refl(lhs))
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ f(a) = f(b)`, at a unary symbol.
pub fn congr1(env: &mut Env, f: FnSym, ab: &Thm) -> DResult<Thm> {
    let (a, _) = ab.concl().eq_parts()?;
    congr_arg(env, f, &[a], 0, ab)
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ f(a, r) = f(b, r)`.
pub fn congr2_l(env: &mut Env, f: FnSym, ab: &Thm, r: &Term) -> DResult<Thm> {
    let (a, _) = ab.concl().eq_parts()?;
    congr_arg(env, f, &[a, r.clone()], 0, ab)
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ f(l, a) = f(l, b)`.
pub fn congr2_r(env: &mut Env, f: FnSym, l: &Term, ab: &Thm) -> DResult<Thm> {
    let (a, _) = ab.concl().eq_parts()?;
    congr_arg(env, f, &[l.clone(), a], 1, ab)
}

/// `⊢ ∀x. (x ∈ ω → φ(x))` from `⊢ φ(0)` and `⊢ ∀x. ((x ∈ ω ∧ φ(x)) → φ(succ x))`.
///
/// A thin assembly over [`induction_scheme`]: it is that theorem's antecedent
/// that has to be built in exactly the right shape, and getting it wrong used to
/// be a bare `None` from `mp` a hundred lines from the mistake — which is what
/// [`crate::prim::mp`] now reports, with both theorems attached.
pub fn induct(
    env: &mut Env,
    core: &OmegaCore,
    x: FreeVar,
    phi: &Formula,
    base: &Thm,
    step: &Thm,
) -> DResult<Thm> {
    let scheme = imported(
        "crate::recursion::induction_scheme",
        induction_scheme(env, core, x, phi),
    )?;
    prim::mp(&scheme, &and_intro(base, step))
}

/// Assemble the step premise of [`induct`] from a natural-deduction proof.
///
/// `body` is handed `⊢ x ∈ ω` and `⊢ φ(x)` — both under the hypothesis
/// `x ∈ ω ∧ φ(x)`, which this function then discharges — and must return
/// `φ(succ x)`.
pub fn induct_step<F>(
    core: &OmegaCore,
    x: FreeVar,
    phi: &Formula,
    body: F,
) -> DResult<Thm>
where
    F: FnOnce(&Thm, &Thm) -> DResult<Thm>,
{
    let tx = Term::var(x);
    let x_om = Formula::mem(tx, core.set());
    let h = Formula::and(x_om, phi.clone());
    let assumed = assuming(h.clone());
    let x_om_thm = crate::rules::and_elim_left(&assumed)?;
    let phi_thm = crate::rules::and_elim_right(&assumed)?;
    let out = body(&x_om_thm, &phi_thm)?;
    let discharged = discharge(&h, &out);
    prim::gen(x, &discharged)
}

/// `⊢ ∀x⃗. φ`, outermost first — [`crate::gen_all`] with the side condition
/// **reported** rather than raised.
///
/// The two differ in exactly one way: `crate::gen_all` folds
/// [`kernel::Thm::gen`], which panics when the generalised variable is free in a
/// hypothesis of `thm`, and this folds [`crate::prim::gen`], which is
/// `Thm::gen_checked` with the site attached. Every export of this module is
/// closed by this function after a [`crate::discharge::discharge`], so a
/// mis-ordered pair — generalising before discharging — is the one mistake that
/// would otherwise abort a run rather than be counted.
pub fn gen_all(xs: &[FreeVar], thm: &Thm) -> DResult<Thm> {
    let mut acc = thm.clone();
    for x in xs.iter().rev() {
        acc = prim::gen(*x, &acc)?;
    }
    Ok(acc)
}

/// Adapt a construction from the part of `derived/` that still returns
/// `Option`.
///
/// `crate::recursion`, `crate::tower`, `crate::proj`, `crate::point_fun` and
/// `crate::ext` have not been migrated to [`crate::err::DResult`], and this
/// module may not edit them. A `None` from one of them means *the construction
/// this module is built on refused*, and its reason was thrown away at the
/// boundary — so it is reported as an [`crate::err::DerErr::Assembly`] naming
/// that construction, with no operands, which is the honest amount of
/// information available. It is deliberately **not** a decline: none of these
/// refuse as part of a contract, and one arriving on a corpus run is a finding.
///
/// `#[track_caller]` puts the *call site* in the report, so the site names the
/// line in `nat/` that asked rather than this line.
#[track_caller]
pub fn imported<T>(from: &'static str, r: Option<T>) -> DResult<T> {
    match r {
        Some(t) => Ok(t),
        None => Err(DerErr::assembly(Site::caller(), from, Vec::new())),
    }
}
