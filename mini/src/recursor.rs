//! **The eliminator** — `⟦T.rec.{ℓ⃗}⟧` (MINI-DESIGN.md §9, zone B's last step).
//!
//! # Interface
//!
//! ```text
//! recursor::ensure(checker, T, σ_T, T.rec, σ_rec) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::zoneb::ensure`] once the declaration's carrier and
//! constructors are in the store, and from nowhere else. On success
//! `⟦T.rec.{σ_rec}⟧` and its typing are in the store under the **recursor's
//! own** instantiation, which is one level longer than the declaration's: the
//! motive's `u₁` is prepended to `T`'s parameters, so the two keys differ and
//! must not be confused.
//!
//! # The obligation, and why it is not the ι rule
//!
//! What a `(declaration, σ)` pair asks for is `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧`, so for a
//! recursor it is
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : T p⃗ → Sort u₁) (s⃗ : minors) (t : T p⃗). C t⟧
//! ```
//!
//! and the innermost factor of that is a **dependent** product: the motive `C`
//! is a bound variable, and the eliminator has to land in `app(C,t)` at every
//! `t` of the carrier. That is a different obligation from the one
//! `checker/src/tg.rs` discharges, which is the ι *equation* at a use site
//! where `C` has already been instantiated — and it is why
//! `RECURSOR-DESIGN.md` §11.1's dependent-motive census could close at zero on
//! `init-prelude` while the census *here* is the opposite. See §5.1 of that
//! note: the corpus's recursor files η-expand the eliminator itself
//! (`def boolRec := fun motive f t b => Bool.rec motive f t b`), so the motive
//! is never a constant.
//!
//! # What each declaration's eliminator waits on
//!
//! This is the register the [`Gap::Recursor`] detail strings index. It is
//! deliberately a statement about `derived/`, because the wiring reaches every
//! recursor the corpus mentions and is not what is missing.
//!
//! | route | detail | what is missing |
//! |---|---|---|
//! | `Eq` — the thesis's own clause | — | nothing; [`eq_rec`] is it |
//! | class (T), `n ≥ 1` | [`DEPENDENT_MOTIVE`] | a dependent eliminator |
//! | class (T), `n = 0` | [`NO_CONSTRUCTORS`] | `⟦T⟧ = ∅`, then any function |
//! | class (S), `ni = 0` | [`CLASS_S`] | one premise of `LePropRecursor`; see below |
//!
//! ## The class-(S) row is one premise short, and the premise is `derived`'s
//!
//! This row used to read "the general class-(S) eliminator", meaning
//! `LeRecursor::build` declines `ni = 0`. That is no longer what is missing:
//! [`derived::inductive::family::LePropRecursor`] is the `ni = 0` rule, it is
//! built, and its ι is Lean-shaped. Measured against what a nest for
//!
//! ```text
//! And.rec.{w} : ∀ (a b : Prop) (C : And a b → Sort w)
//!                 (m : ∀ (l : a) (r : b), C (And.intro l r)) (t : And a b), C t
//! ```
//!
//! actually holds, the shortfall is one hypothesis. `rec_typed` is
//! `⊢ ∀m ∀T. (minor(m,•⃗) ∈ T → rec(m) ∈ fs(1,T))`, and at `T := app(C,•)` its
//! premise is `app(app(m,•),•) ∈ app(C,•)` — the minor applied to `k` copies of
//! the point. Mini has the application rules that would produce it
//! ([`Interp::cond_app`](crate::interp::Interp::cond_app),
//! [`dprod_app`](crate::interp::Interp::dprod_app),
//! [`fs_app`](crate::interp::Interp::fs_app)), and each demands a membership
//! for the argument. So the obligation is
//!
//! ```text
//! ⊢ • ∈ ⟦a⟧      and      ⊢ • ∈ ⟦b⟧
//! ```
//!
//! — **each field type is inhabited** — and that is not `⟦a⟧ ⊆ 1`, which the
//! parameter's own typing gives. It follows only from the major premise:
//! `t ∈ A_φ(a,b)` gives `LeProp::elim`'s
//! `ψ = ∃y₀ ∃y₁. (y₀ ∈ ⟦a⟧ ∧ (y₁ ∈ ⟦b⟧ ∧ • = •))`, whose witnesses collapse to
//! `•` by `⊆ 1`. Opening that existential is the missing step, and `derived`
//! exports nothing that does it: `LeProp::elim` hands ψ back unopened, and the
//! disjunct/witness eliminators `hyp_disj_elim` and `hyp_ex_branch` are
//! `pub(crate)` in `derived::inductive::rec_shared`. The construction that
//! closes the row is one theorem beside `LePropRecursor`:
//!
//! ```text
//! ⊢ ∀p⃗. (• ∈ A_φ(p⃗) → (⋀ⱼ βⱼ(p⃗,•⃗<ⱼ) ⊆ 1 → ⋀ⱼ • ∈ βⱼ(p⃗,•⃗<ⱼ)))
//! ```
//!
//! — the antecedent `G` of `iota_at_point` and `erase`, *derived* rather than
//! assumed, at the one constructor `LePropRecursor::build` already requires.
//! Assembling it on this side instead would put a disjunction-of-existentials
//! elimination in the checker, which is the boundary this project keeps; it is
//! also why the wiring is not attempted here rather than attempted and gapped
//! halfway through.
//!
//! **The `k = 0` sub-case is not blocked**, and saying so is the actionable
//! half. At `PUnit.unit`/`True.intro` there are no fields, `minor(m,•⃗)` *is*
//! `m`, and `rec_typed`'s premise is the minor binder's own scope typing —
//! nothing has to be opened. It is deliberately **not** wired ahead of the
//! rest, and the reason is not tidiness: `G` is empty at `k = 0`
//! (`LeCarrier::intro_is_conditional(spec, 0)` is `Some(false)`), so the
//! general implementation *is* the `k = 0` implementation with one extra
//! discharge. Landing the special case now would be a nest, a term and a
//! typing chain written to be deleted the day the theorem above exists. The
//! 2 pairs it would move (`PUnit`) are the same 2 that move for free then.
//!
//! ## The dependent-motive row is the substantive one
//!
//! [`derived::inductive::GenRecursor`] is **simply typed**: `grec(p⃗,s⃗,T)` is
//! `wrec` at one target *set* `T`, and its (S3)/(S4) carry `HYP`, the
//! conjunction of `∀y⃗ ∀t⃗ ∀v⃗. (… ∧ vⱼ ∈ T) → sᵢ⟪y⃗,t⃗⟫v⃗ ∈ T`. Neither of the
//! two candidate targets works at a variable motive, and the reason is not
//! arity but the *direction* the weakening runs in:
//!
//! * `T := app(C, c₀)` at some closed constructor — RECURSOR-DESIGN.md §5.2's
//!   policy 2 — makes `grec(t) ∈ app(C,c₀)`, which is the goal `app(C,t)` only
//!   when `C` is constant.
//! * `T := ⋃{app(C,w) : w ∈ ⟦T p⃗⟧}` makes the *conclusion* of each
//!   `minor_typedᵢ` free — Lean's minor gives `sᵢ(…) ∈ app(C, ctorᵢ(y⃗,t⃗))`,
//!   and that set is one of the union's members. But it also weakens each
//!   `vⱼ ∈ T` **hypothesis**, and `vⱼ ∈ ⋃img(C)` does not give `vⱼ ∈ app(C,tⱼ)`,
//!   which is what Lean's minor demands of the induction hypotheses. So `HYP`
//!   is dischargeable exactly when the declaration has **no recursive
//!   arguments** — and even then, turning `grec ∈ fs(W,T)` into
//!   `∀t ∈ W. grec(t) ∈ app(C,t)` needs one `wtype::w_rect` over a carrier
//!   inversion (`no_junk`, telescope η, `RecArg` η) that no `derived/` export
//!   assembles today.
//!
//! Both halves are model-level, so both belong in `derived/src/inductive/`
//! beside `GenRecursor`, not here: RECURSOR-DESIGN.md §5.3's Σ-target variant
//! is the design that closes the recursive case and the non-recursive one at
//! once. Until it exists the pair is a **library** gap with that name on it,
//! not an interpretation-scope gap — the carrier is built, the constructors are
//! built, the nest is walked, and a named construction is absent.
//!
//! # Nothing here searches
//!
//! The route is chosen by [`crate::direct::clause_for`] on the declaration's
//! name — one hash comparison on the name [`crate::zoneb::ensure`] was already
//! keyed on — and, as in [`crate::direct`], **the name selects and the
//! derivation verifies**. [`eq_rec`] rebuilds the two sets it reasons about
//! from the nest's own binders and refuses unless the scope's minor typing and
//! the declared codomain are literally those terms, so a declaration called
//! `Eq` whose recursor is some other rule is declined with a reason rather than
//! given a typing.

use kernel::{Formula, Term, Thm};

use crate::direct::Clause;
use crate::env::ConstantInfo;
use crate::ev::{Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::kernel::{Checker, Typing, R};

/// A class-(T) declaration with constructors: the eliminator's typing is
/// dependent and [`derived::inductive::GenRecursor`] is simply typed.
pub const DEPENDENT_MOTIVE: &str = "dependent motive";

/// A class-(T) declaration with no constructors (`Empty`).
/// [`derived::inductive::GenRecursor::build`] returns `None` for it by design —
/// its step is `∅` and it has no ι rule to state — so its eliminator needs the
/// separate argument its header names: `⟦Empty⟧ = ∅` by `wtype::w_rect` at a
/// refutable `φ`, after which any function is a section of any fibre.
pub const NO_CONSTRUCTORS: &str = "no constructors";

/// A class-(S) declaration — one [`crate::class_s`] built a carrier for. Its
/// eliminator is §5.3's subsingleton rule at `ni = 0`, which is
/// [`derived::inductive::family::LePropRecursor`], and **that construction
/// exists**. What is missing is one premise of it, and the missing thing is
/// named in the module header's register: see "the class-(S) row is one
/// premise short" below.
pub const CLASS_S: &str = "class (S) eliminator";

/// Make `⟦T.rec.{σ_rec}⟧` available, or say which construction it waits on.
///
/// The declaration is already translated when this runs — `zoneb::ensure`
/// builds it first and returns before reaching here if it could not — so the
/// route below is a statement about `T`, never a retry of the carrier.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    if let Some(Clause::Eq) = crate::direct::clause_for(ind_name) {
        return eq_rec(c, ind_name, ind_inst, rec_name, rec_inst)
    }
    // A class-(S) declaration is the one the *carrier* route already
    // identified: `crate::class_s::of` is a store read on the key this call
    // was handed, not a second classification, so the two cannot disagree.
    if crate::class_s::of(c, ind_name, ind_inst).is_some() {
        return Err(Gap::Recursor(ind_name.clone(), CLASS_S))
    }
    let empty = matches!(
        c.environment().get(ind_name),
        Some(ConstantInfo::Inductive { ctors, .. }) if ctors.is_empty()
    );
    Err(Gap::Recursor(ind_name.clone(), if empty { NO_CONSTRUCTORS } else { DEPENDENT_MOTIVE }))
}

/// **`Eq`'s eliminator**, the thesis's own clause `⟦rec₌ e b h⟧ = ⟦e⟧`
/// (`INDEXED-DESIGN.md` §2.2, Carneiro §6.2).
///
/// `Eq.rec.{u₁,u} : Π (α : Sort u) (a : α) (C : Π b, Eq α a b → Sort u₁)
/// (r : C a (Eq.refl α a)) (b : α) (t : Eq α a b). C b t`, so the nest is
/// `2 + 1 + 1 + 1 + 1 = 6` deep and its bottom is the minor `r` itself. The
/// derivation is two Leibniz steps on the *one* thing `t ∈ eq_set(a,b)` says:
/// `a = b`, and `t = •` because the conditional singleton is a subset of `1`.
///
/// The nest's depth is read off the export's own
/// [`ConstantInfo::Recursor`] counts rather than hardcoded, and the two are
/// compared: a `Eq.rec` with a different number of minors or indices is a
/// different rule, and the closed form below is not about it.
fn eq_rec(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(ind_name.clone(), w);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    };
    if (*num_params, *num_minors, *num_indices) != (2, 1, 1) {
        return Err(bad("Eq.rec: recursor shape"))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(rec_name.clone(), rec_inst.to_vec()))
    }
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let codomain =
        crate::zoneb::peel(&rec_ty, EQ_DEPTH).ok_or_else(|| bad("Eq.rec: recursor arity"))?;
    let site = EqSite { ind: ind_name.clone(), inst: ind_inst.to_vec(), codomain };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(eq_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, EQ_DEPTH, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// `α, a, C, r, b, t` — `num_params + 1 + num_minors + num_indices + 1` at
/// `Eq`'s `(2, 1, 1)`.
const EQ_DEPTH: usize = 6;

/// Which declaration `Eq.rec`'s nest is being built for, and the codomain read
/// off its type.
struct EqSite {
    ind: Name,
    inst: Vec<u32>,
    codomain: E,
}

/// The bottom of `Eq.rec`'s nest: the minor `r`, and its membership in
/// `⟦C b t⟧`.
///
/// Everything the derivation needs is already in the scope stack or in
/// [`crate::direct::Direct`]; the three things read off rather than assumed are
///
/// * `⟦C a (Eq.refl α a)⟧`, which is the *minor binder's own* scope typing;
/// * `⟦C b t⟧`, which is [`Checker::infer_type`] on the declared codomain;
/// * `⟦Eq α a b⟧`, which is `⟦Eq⟧`'s nest β-reduced at the major premise's own
///   three arguments by [`crate::interp::Interp::beta_spine`].
///
/// Each is then compared against the term this clause expects, and a mismatch
/// is a decline. That is the whole shape check: there is no separate syntactic
/// audit of `Eq.rec`, because a rule that is not `Eq.rec` cannot make these
/// three agree.
fn eq_bottom(c: &mut Checker<'_, '_>, site: &EqSite) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::Gap(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w);

    // `⟦C b t⟧`, by inference on the declared codomain.
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(EQ_DEPTH) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
    let sums = ip.prelude.tower.sums.clone();
    let point = sums.point();
    let (alpha, a, motive) = (xs[0].clone(), xs[1].clone(), xs[2].clone());
    let (refl, b, t) = (xs[3].clone(), xs[4].clone(), xs[5].clone());

    // The two motive instances, rebuilt from the binders. `⟦Eq.refl α a⟧` is
    // `•` by §6.2's proof clause, which is what puts `point` in the first.
    let at_refl = {
        let m = ip.app(motive.clone(), a.clone());
        ip.app(m, point.clone())
    };
    let at_t = {
        let m = ip.app(motive.clone(), b.clone());
        ip.app(m, t.clone())
    };
    if mems[3].concl().as_mem().map(|(_, s)| s) != Some(at_refl.clone()) {
        return gap(bad("Eq.rec: minor is not the motive at reflexivity"))
    }
    if goal != at_t {
        return gap(bad("Eq.rec: codomain is not the motive at the major premise"))
    }

    // `⟦Eq α a b⟧`, β-reduced to `eq_set(⟦a⟧,⟦b⟧)`, and the major premise's own
    // typing carried onto it. The premises `beta_spine` consumes are the three
    // arguments' scope typings, which is where a recursor whose major premise
    // is at other arguments is refused.
    let Some((carrier, spine_eq)) = ip.beta_spine(
        &former,
        &[alpha, a.clone(), b.clone()],
        &[mems[0].clone(), mems[1].clone(), mems[4].clone()],
    ) else {
        return gap(bad("Eq.rec: type former spine"))
    };
    if carrier != ip.mk(d.eq, vec![a.clone(), b.clone()]) {
        return gap(bad("Eq.rec: spine bottom"))
    }
    let Some(t_mem) = ip.retarget_set(&mems[5], &spine_eq) else {
        return gap(Gap::ConvCompose("eq-rec-major"))
    };

    // `t ∈ eq_set(a,b) → (t ∈ 1 ∧ a = b)` — the conditional singleton's own
    // defining axiom, at these very terms.
    let both = derived::inst_all(&d.eq_ax, &[a.clone(), b.clone(), t.clone()])
        .and_then(|chi| derived::iff_mp(&chi))
        .and_then(|fwd| Thm::mp(&fwd, &t_mem));
    let Some(both) = both else { return gap(Gap::ConvCompose("eq-rec-elim")) };
    let (Some(t_in_1), Some(a_eq_b)) =
        (derived::and_elim_left(&both), derived::and_elim_right(&both))
    else {
        return gap(Gap::ConvCompose("eq-rec-conjuncts"))
    };
    // `• = t`: the subset of `1` has `•` for its only element.
    let pt_eq_t = derived::inst_all(&sums.unit_eta, std::slice::from_ref(&t))
        .and_then(|r| Thm::mp(&r, &t_in_1))
        .and_then(|t_pt| derived::eq_symm(&mut ip.env, &t_pt));
    let Some(pt_eq_t) = pt_eq_t else { return gap(Gap::ConvCompose("eq-rec-unit-eta")) };

    // Two Leibniz steps, in the order the two facts arrive: `a ↦ b` in the
    // motive's first argument, then `• ↦ t` in its second.
    let x = ip.env.fresh_var();
    let phi_a = Formula::mem(refl.clone(), {
        let m = ip.app(motive.clone(), Term::var(x));
        ip.app(m, point.clone())
    });
    let at_b = Thm::mp(&Thm::eq_leibniz(a, b.clone(), x, phi_a), &a_eq_b)
        .and_then(|i| Thm::mp(&i, &mems[3]));
    let Some(at_b) = at_b else { return gap(Gap::ConvCompose("eq-rec-motive-index")) };

    let y = ip.env.fresh_var();
    let phi_pt = Formula::mem(refl.clone(), {
        let m = ip.app(motive, b);
        ip.app(m, Term::var(y))
    });
    let out = Thm::mp(&Thm::eq_leibniz(point, t, y, phi_pt), &pt_eq_t)
        .and_then(|i| Thm::mp(&i, &at_b));
    let Some(out) = out else { return gap(Gap::ConvCompose("eq-rec-proof-index")) };

    if *out.concl() != Formula::mem(refl.clone(), goal) {
        return gap(bad("Eq.rec: the minor is not about the codomain"))
    }
    Typing { ty, tm: Some(refl), ev: Ev::Proved(out) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Expr, Level};
    use crate::interp::Interp;
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }

    fn level(n: u32) -> Level {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = l.succ();
        }
        l
    }

    /// `Eq`, as the exports declare it. `Eq.rec` is **generated** by
    /// [`crate::kernel::add`], exactly as it is on the corpus, so this test
    /// reads the same recursor type the tutorial files do rather than a
    /// hand-written imitation of it.
    fn eq_env() -> (Environment, Name, Name) {
        let (e, refl) = (nm("Eq"), Name::str(&nm("Eq"), "refl"));
        let u: Level = Level::Param(nm("u"));
        let us: Rc<[Level]> = vec![u.clone()].into();
        let ty = forall(sort(u.clone()), forall(bvar(0), forall(bvar(1), sort(Level::Zero))));
        let at = |f: E, x: E, y: E, z: E| app(app(app(f, x), y), z);
        let cty =
            forall(sort(u), forall(bvar(0), at(konst(e.clone(), us), bvar(1), bvar(0), bvar(0))));
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e.clone(),
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(refl, cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, e.clone(), Name::str(&e, "rec"))
    }

    /// Replace the body under `depth` `Π` binders.
    fn with_codomain(ty: &E, depth: usize, cod: E) -> E {
        if depth == 0 {
            return cod
        }
        let Expr::Forall { ty: d, body } = &**ty else { panic!("fewer than {depth} binders") };
        forall(d.clone(), with_codomain(body, depth - 1, cod))
    }

    /// **`⟦Eq.rec⟧` is interpreted with its typing**, at a `Type`-valued motive
    /// and at a `Prop`-valued one — the two branches the `λ` clause takes, the
    /// second of which is what `094_ruleK` exercises.
    ///
    /// Non-vacuity: the typing has to be about `⟦Eq.rec⟧` *itself* and to have
    /// no hypotheses, and the interpretation has to be a six-deep nest rather
    /// than the opaque symbol a decline would leave.
    #[test]
    fn eq_rec_is_interpreted_with_its_typing() {
        let (env, _, rec) = eq_env();
        for sigma in [[1u32, 1], [0, 0]] {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let at: Rc<[Level]> = sigma.iter().map(|n| level(*n)).collect::<Vec<_>>().into();
            let t = c.infer_type(&konst(rec.clone(), at)).expect("infer ⟦Eq.rec⟧");
            let m = t
                .ev
                .thm()
                .unwrap_or_else(|| panic!("⟦Eq.rec.{sigma:?}⟧ has no typing: {:?}", t.ev))
                .clone();
            assert!(m.hyps().is_empty(), "a stored typing is unconditional");
            let (subj, _) = m.concl().as_mem().expect("a membership");
            assert_eq!(
                Some(subj),
                t.tm,
                "the typing must be about ⟦Eq.rec⟧ itself, not some other term"
            );
            // Non-vacuity, and it differs by branch because the *clause*
            // differs. A `Type`-valued motive makes `⟦Eq.rec⟧` a six-deep
            // λ-graph, and every level of it has to come apart again; a
            // `Prop`-valued one makes the whole eliminator a **proof**, so
            // §6.2 gives it `•` and its type is a conditional singleton. That
            // second branch is the one `094_ruleK` takes, and asserting the
            // first there would have pinned the wrong clause.
            if sigma[0] == 0 {
                assert_eq!(
                    t.tm,
                    Some(c.interp().expect("threaded").point()),
                    "a Prop-valued motive makes Eq.rec a proof, which denotes •"
                );
            } else {
                let mut cur = t.tm.clone().expect("interpreted");
                let ip = c.interp().expect("threaded");
                for lv in 0..EQ_DEPTH {
                    let (site, _) = ip
                        .as_lam(&cur)
                        .unwrap_or_else(|| panic!("⟦Eq.rec⟧ is not a λ at level {lv}"));
                    let (skel, holes) = (site.skel.clone(), site.holes.clone());
                    let x = Term::var(ip.env.fresh_var());
                    cur = ip.rebuild(&skel, &holes, &x);
                }
            }
        }
    }

    /// **The name is not the evidence.** A declaration called `Eq` whose
    /// recursor concludes at the *reflexivity* index rather than at the major
    /// premise's — `C a (Eq.refl α a)` where Lean writes `C b t` — is a
    /// well-typed six-binder `Π` and is still declined, because the set the
    /// minor's scope typing is about and the set the codomain interprets to no
    /// longer agree.
    ///
    /// The codomain is *inferred*, so nothing about the name is trusted; this
    /// is [`crate::direct`]'s discipline at the eliminator.
    #[test]
    fn a_recursor_at_the_wrong_index_is_declined_not_believed() {
        let (mut env, e, rec) = eq_env();
        let us: Rc<[Level]> = vec![Level::Param(nm("u"))].into();
        // `C a (Eq.refl α a)`, at binders `α a C r b t` = `#5 … #0`.
        let cod = app(
            app(bvar(3), bvar(4)),
            app(app(konst(Name::str(&e, "refl"), us), bvar(5)), bvar(4)),
        );
        let Some(ConstantInfo::Recursor { ty, .. }) = env.consts.get_mut(&rec) else {
            panic!("the recursor was generated")
        };
        *ty = with_codomain(&ty.clone(), EQ_DEPTH, cod);

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: Rc<[Level]> = vec![level(1), level(1)].into();
        let t = c.infer_type(&konst(rec, at)).expect("infer");
        assert_eq!(
            t.ev.gap(),
            Some(&Gap::Recursor(e, "Eq.rec: codomain is not the motive at the major premise")),
            "a recursor named Eq.rec that is not Eq's rule must be declined, with a reason \
             naming what was refused"
        );
    }

    /// The register is a register: a class-(T) declaration's eliminator waits
    /// on a named `derived/` construction, and **which** one is decided by
    /// whether it has constructors — not by its arity, which is why the
    /// positive case here has three constructors of three different arities.
    #[test]
    fn the_class_t_route_names_which_construction_it_waits_on() {
        let mut env = Environment::empty();
        let t = nm("T");
        let ty = konst(t.clone(), Vec::new().into());
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero.succ()),
                ctors: vec![
                    (Name::str(&t, "c0"), ty.clone()),
                    (Name::str(&t, "c1"), forall(ty.clone(), ty.clone())),
                    (Name::str(&t, "c2"), forall(ty.clone(), forall(ty.clone(), ty))),
                ],
            },
        )
        .expect("accepted");
        let empty = nm("E");
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: empty.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero.succ()),
                ctors: vec![],
            },
        )
        .expect("accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        assert_eq!(
            ensure(&mut c, &t, &[], &Name::str(&t, "rec"), &[0]).err(),
            Some(Gap::Recursor(t, DEPENDENT_MOTIVE))
        );
        assert_eq!(
            ensure(&mut c, &empty, &[], &Name::str(&empty, "rec"), &[0]).err(),
            Some(Gap::Recursor(empty, NO_CONSTRUCTORS))
        );
    }
}
