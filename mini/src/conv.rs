//! **Conversions**: `Γ ⊢ ⟦e⟧ = ⟦e'⟧`, and the certificate legs `whnf` composes
//! along a reduction (MINI-DESIGN.md §6.4).
//!
//! # Interface
//!
//! ```text
//! Conv { to: Expr, ev: Ev }              // ev : Γ ⊢ ⟦from⟧ = ⟦to⟧
//!
//! Conv::refl(to, tm)                     // ⟦e⟧ = ⟦e⟧
//! c1.then(ip, c2)                        // trans
//! c.flip(ip, from_tm)                    // symm
//! app_cong(ip, cf, ca)                   // congruence over `app`
//!
//! delta_leg(interp_of_c, to)             // a constant's defining equation
//! beta_leg(ip, lam_site, dom, arg_tm, arg_mem, to)
//! zeta_leg(to)                           // reflexivity, by construction
//! ```
//!
//! The endpoints are carried by the caller, as §5 says: a `Conv` records where
//! it went and the evidence that it did, and the *left* endpoint is whatever
//! the caller had. Composing with a `Gap` yields that `Gap` and never a
//! silently-weakened certificate.
//!
//! # Zeta is reflexivity, and natLit unfolding is too
//!
//! Not an optimisation — a consequence of §7's interpretation choices.
//! `⟦let x := v in b⟧` is *defined* as `⟦b[v]⟧`, so the zeta step's two sides
//! are the same `Term` and its certificate is `eq_refl`. Likewise
//! `⟦natLit n⟧ := ⟦Nat.succ (…)⟧`. Both are cases where a reduction that costs
//! nanoda a derivation costs mini nothing, because the interpretation was
//! chosen to make the equation hold on the nose.
//!
//! # `local_premises` has no counterpart here, and that is the point
//!
//! Beta is the interesting leg, and it is where nanoda is at its worst. To
//! contract `(λ x:A. b) a` the certificate needs `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧` — the
//! argument's typing. nanoda's `TgBackend::local_premises` **guesses** that
//! context: it scans the argument expression for `Local` nodes, even under open
//! binders, and reconstructs a hypothesis set from what it finds. That is a
//! heuristic reconstruction of information the checker had exactly a moment
//! earlier and discarded.
//!
//! Mini's [`crate::scope::Scopes`] *is* that information. For a `bvar`-headed
//! argument — the case that is 5 186 of nanoda's `has_type` misses, "a local at
//! the top level" — the premise is `scopes.get(i).assumption()`, which is one
//! vector index and no derivation at all. For a compound argument it is a
//! recursive `infer_type`, which is inference and not search: deterministic,
//! total on well-typed input, and producing its evidence as it goes.
//!
//! **So mini needs no `local_premises`, no `domain_obligation`, and no
//! `has_type_local`.** [`beta_leg`] takes the membership as an argument, which
//! is the whole design: a function that needs a fact takes it, rather than
//! going to look for it.

use crate::ev::{Ev, Gap};
use crate::expr::E;
use crate::interp::{Interp, LamSite};
use kernel::{Formula, Term, Thm};

/// A conversion to `to`, with `Γ ⊢ ⟦from⟧ = ⟦to⟧` or a named absence.
///
/// `from` is the caller's — a `Conv` that carried both endpoints would invite
/// the endpoint-drift bug nanoda's `certify_reduct` has a guard for, and mini
/// has no cache for the two to drift apart in.
#[derive(Debug, Clone)]
pub struct Conv {
    pub to: E,
    pub ev: Ev,
}

impl Conv {
    /// `⟦e⟧ = ⟦e⟧`. The identity of [`Conv::then`].
    pub fn refl(to: E, tm: &Term) -> Conv { Conv { to, ev: Ev::Proved(Thm::eq_refl(tm.clone())) } }

    /// A step that reached `to` but could not certify it.
    pub fn gap(to: E, g: Gap) -> Conv { Conv { to, ev: Ev::Gap(g) } }

    pub fn is_proved(&self) -> bool { self.ev.is_proved() }

    /// Compose: `⟦a⟧ = ⟦b⟧` then `⟦b⟧ = ⟦c⟧` gives `⟦a⟧ = ⟦c⟧`. `Γ` is the
    /// union, which is what makes a reduction under binders cost one merge per
    /// step instead of a re-proof.
    pub fn then(self, ip: &mut Interp, next: Conv) -> Conv {
        let to = next.to;
        let ev = self.ev.zip(next.ev, |a, b| match derived::eq_trans(&mut ip.env, &a, &b) {
            Some(t) => Ev::Proved(t),
            None => Ev::Gap(Gap::ConvCompose),
        });
        Conv { to, ev }
    }

    /// Reverse the conversion. `from_tm` is the left endpoint the caller holds,
    /// and becomes the new `to`'s interpretation.
    pub fn flip(self, ip: &mut Interp, from: E) -> Conv {
        let ev = self.ev.and_then(|t| match derived::eq_symm(&mut ip.env, &t) {
            Some(t) => Ev::Proved(t),
            None => Ev::Gap(Gap::ConvCompose),
        });
        Conv { to: from, ev }
    }
}

/// Congruence over application: from `⟦f⟧ = ⟦f'⟧` and `⟦a⟧ = ⟦a'⟧` infer
/// `⟦f a⟧ = ⟦f' a'⟧`.
///
/// One `derived::congr` over the `app` symbol. Note both halves are
/// *composed*, never dropped: `try_eta_expansion_aux`'s silently-discarded
/// recursive half is structurally impossible here, because the only way to
/// obtain a `Conv` is to compose one.
pub fn app_cong(ip: &mut Interp, f: &Ev, a: &Ev) -> Ev {
    let ap = ip.prelude.ap.app;
    f.clone().zip(a.clone(), |ef, ea| match derived::congr(&mut ip.env, ap, &[ef, ea]) {
        Some(t) => Ev::Proved(t),
        None => Ev::Gap(Gap::ConvCompose),
    })
}

/// **Delta**: a transparent constant's defining equation, `⊢ ⟦c.{σ}⟧ = ⟦val⟧`.
///
/// Mini-lean's `whnf` is eagerly delta-unfolding with no lazy-delta heuristic,
/// so nanoda's `lazy_delta_step`/`recall_eq` machinery has no counterpart and
/// the certificate is the stored axiom itself — one per unfold, already
/// proved, `Sealed`, and hypothesis-free, so weakening it into `Γ` is free.
pub fn delta_leg(defeq: Option<&crate::ev::Sealed>, to: E, name: &crate::expr::Name) -> Conv {
    match defeq {
        Some(s) => Conv { to, ev: Ev::Proved(s.thm().clone()) },
        None => Conv::gap(to, Gap::NoDefiningEquation(name.clone())),
    }
}

/// **Zeta**, and the `natLit` unfolding: reflexivity.
///
/// `⟦let x := v in b⟧` is *defined* as `⟦b[v]⟧` (§7), so the two sides are the
/// same `Term`. The step still exists — the expression changed — but its
/// certificate is free.
pub fn zeta_leg(to: E, tm: &Term) -> Conv { Conv::refl(to, tm) }

/// **Beta**: one head contraction, `Γ ⊢ ⟦(λ x:A. b) a⟧ = ⟦b[a]⟧`.
///
/// `arg_mem` must be `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧`. It is an *argument* rather than
/// something this function goes and finds, which is the whole of the design:
/// see the module header on `local_premises`.
///
/// The conclusion is checked against the statement claimed, so a mismatched
/// lambda site — a `LamSite` for a different body shape, or a domain that is
/// not the one the membership speaks of — is a gap rather than a theorem about
/// the wrong redex.
pub fn beta_leg(
    ip: &mut Interp,
    site: &LamSite,
    dom: Term,
    arg_tm: Term,
    arg_mem: &Ev,
    to: E,
) -> Conv {
    let p = ip.prelude.clone();
    let Some(beta) =
        derived::funcs::beta_conditional_n(&mut ip.env, &p.ap, site.t, site.lam, &site.lam_ax)
    else {
        return Conv::gap(to, Gap::ConvCompose)
    };
    let mut args = site.holes.clone();
    args.push(dom.clone());
    args.push(arg_tm.clone());
    let Some(inst) = derived::inst_all(&beta, &args) else { return Conv::gap(to, Gap::ConvCompose) };
    let ev = arg_mem.clone().and_then(|mem| {
        let Some(out) = Thm::mp(&inst, &mem) else { return Ev::Gap(Gap::ConvCompose) };
        // `app(lam(h⃗, ⟦A⟧), ⟦a⟧) = t(h⃗, ⟦a⟧)` — the redex and its contractum.
        let lam_t = ip.lam_term(site, dom.clone());
        let redex = ip.app(lam_t, arg_tm.clone());
        let mut targs = site.holes.clone();
        targs.push(arg_tm.clone());
        let contractum = ip.mk(site.t, targs);
        if *out.concl() == Formula::eq(redex, contractum) {
            Ev::Proved(out)
        } else {
            Ev::Gap(Gap::ConvCompose)
        }
    });
    Conv { to, ev }
}

/// **`tryFunEta`**: two set-functions of the same space that agree pointwise
/// are equal — `Γ ⊢ ⟦e₁⟧ = ⟦e₂⟧`.
///
/// This is the consumer MINI-DESIGN.md §10 predicted for the function-eta
/// lemma, and it is the *pointwise* form rather than the eta equation. That
/// matters and the design got it wrong: §6.5 asked for
/// `⊢ ⟦e₂⟧ = ⟦λA. e₂·x⟧`, i.e. graph extensionality at a particular graph
/// symbol. Mini's two sides are `lam(h⃗, ⟦A⟧)` for *its own* skeleton and
/// whatever `⟦e₂⟧` is, and neither of them need be the symbol the eta equation
/// names — so given only the eta form, the conversion would have to be bridged
/// through `lam_ext` first. The pointwise form applies directly.
///
/// The three premises are exactly what the checker already holds at this
/// point, which is why nothing is searched for:
///
/// * `f_mem`/`g_mem` — `Γ ⊢ ⟦eᵢ⟧ ∈ fs(⟦A⟧, C)`, the two typings
///   `assert_def_eq` is handed (§6.5 takes both typings for precisely this
///   branch);
/// * `pointwise` — `Γ ⊢ ∀x. (x ∈ ⟦A⟧ → app(⟦e₁⟧,x) = app(⟦e₂⟧,x))`, which is
///   what [`crate::scope::Closed::discharge`] produces from the recursive
///   `Conv` under the opened binder. That recursive half is *composed*, not
///   discarded — the half nanoda drops with no ledger entry.
#[allow(clippy::too_many_arguments)]
pub fn fun_eta_leg(
    ip: &mut Interp,
    dom: Term,
    cod: Term,
    f: Term,
    g: Term,
    f_mem: &Ev,
    g_mem: &Ev,
    pointwise: &Ev,
    to: E,
) -> Conv {
    let p = ip.prelude.clone();
    let Some(app_pair) = derived::ext::app_of_pair(&mut ip.env, &p.ap) else {
        return Conv::gap(to, Gap::ConvCompose)
    };
    let Some(rule) =
        derived::ext::funspace_ext(&mut ip.env, &p.ap, &p.prod, &p.fs, &app_pair)
    else {
        return Conv::gap(to, Gap::FunEta)
    };
    let Some(inst) = derived::inst_all(&rule, &[dom, cod, f.clone(), g.clone()]) else {
        return Conv::gap(to, Gap::ConvCompose)
    };
    // The hypothesis is right-nested: `f ∈ fs ∧ (g ∈ fs ∧ pointwise)`.
    let ev = f_mem.clone().zip(g_mem.clone(), |fm, gm| {
        pointwise.clone().and_then(|pw| {
            let inner = derived::and_intro(&gm, &pw);
            let Some(out) = Thm::mp(&inst, &derived::and_intro(&fm, &inner)) else {
                return Ev::Gap(Gap::ConvCompose)
            };
            if *out.concl() == Formula::eq(f.clone(), g.clone()) {
                Ev::Proved(out)
            } else {
                Ev::Gap(Gap::ConvCompose)
            }
        })
    });
    Conv { to, ev }
}

/// The typing of a `bvar`, straight out of the scope stack.
///
/// Kept here rather than in [`crate::scope`] so that the one function beta
/// needs and the one nanoda reconstructs sit side by side. It is a vector
/// index; there is nothing else to it, and that is the finding.
pub fn bvar_typing(scopes: &crate::scope::Scopes, idx: u32) -> Ev { scopes.typing_of_bvar(idx) }

/// The signature a threaded `whnf` has, stated here before the loop is
/// rewritten around it: the reduct, and the certificate that reached it.
///
/// **No typing input.** MINI-DESIGN.md §6.4 argued for this and the argument
/// survived contact: enumerating every `whnf` site, *zero* consume a typing
/// for the equality itself. Subject reduction is a composition at the caller
/// (`whnf_typing`, one Leibniz), and beta's premise is [`beta_leg`]'s
/// argument. A typing threaded *into* `whnf` would be carried past every site
/// that does not want it.
pub type WhnfResult = (E, Conv);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{bvar, sort, Level};
    use crate::scope::Scopes;

    /// **The beta leg, with a `bvar`-headed argument.**
    ///
    /// `(λ x:Prop. x) a` where `a` is a bound variable of the enclosing
    /// context. The premise beta needs — `Γ ⊢ ⟦a⟧ ∈ ⟦Prop⟧` — is the scope's
    /// stored assumption: one vector index, no derivation, no search. This is
    /// the case that is 5 186 of nanoda's `has_type` misses and the one
    /// `local_premises` reconstructs by scanning for `Local` nodes.
    #[test]
    fn beta_takes_its_premise_from_the_scope_at_zero_cost() {
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let prop = ip.sort(0);

        // The enclosing context: `a : Prop`.
        let outer = sc.open(&mut ip.env, prop.clone());
        let a = sc.get(0).unwrap().term();
        // …and the λ, whose own binder is a *different* scope.
        let inner = sc.open(&mut ip.env, prop.clone());
        let x = sc.get(0).unwrap().var();
        let site = ip.lam_site(&Term::var(x), x).expect("lam site");
        let _ = sc.close(inner);

        // The premise. `bvar 0` is now `a` again, and its typing is free.
        let arg_mem = bvar_typing(&sc, 0);
        assert!(arg_mem.is_proved());
        assert_eq!(
            arg_mem.thm().unwrap().concl(),
            &Formula::mem(a.clone(), prop.clone()),
            "the scope already holds exactly the premise beta needs"
        );

        let conv =
            beta_leg(&mut ip, &site, prop.clone(), a.clone(), &arg_mem, bvar(0));
        let thm = conv.ev.thm().expect("beta certificate").clone();
        // `Γ ⊢ app(lam(⟦Prop⟧), a) = t(a)`.
        let lam_t = ip.lam_term(&site, prop.clone());
        let redex = ip.app(lam_t, a.clone());
        let contractum = ip.mk(site.t, vec![a]);
        assert_eq!(*thm.concl(), Formula::eq(redex, contractum));
        assert_eq!(thm.hyps().len(), 1, "Γ is carried, not discarded");
        let _ = sc.close(outer);
    }

    /// A gap composes to a gap and never to a weaker certificate — and the
    /// **left** one wins, so the reported reason is the first thing missing.
    #[test]
    fn conversions_compose_and_gaps_propagate() {
        let mut ip = Interp::new();
        let t0 = ip.sort(0);
        let a = Conv::refl(sort(Level::Zero), &t0);
        let b = Conv::refl(sort(Level::Zero), &t0);
        let ab = a.clone().then(&mut ip, b);
        assert!(ab.is_proved());
        assert_eq!(*ab.ev.thm().unwrap().concl(), Formula::eq(t0.clone(), t0.clone()));

        let g = Conv::gap(sort(Level::Zero), Gap::FunEta);
        assert_eq!(a.clone().then(&mut ip, g.clone()).ev.gap(), Some(&Gap::FunEta));
        assert_eq!(
            g.then(&mut ip, Conv::gap(sort(Level::Zero), Gap::StrLit)).ev.gap(),
            Some(&Gap::FunEta),
            "the left gap wins"
        );
        // `symm` of a reflexivity is still a certificate.
        assert!(a.flip(&mut ip, sort(Level::Zero)).is_proved());
    }

    /// Congruence over `app` composes **both** halves. nanoda's
    /// `try_eta_expansion_aux` drops its recursive half with no ledger entry;
    /// here the only way to a `Conv` is to compose one, so the drop is
    /// unrepresentable.
    #[test]
    fn app_congruence_composes_both_halves() {
        let mut ip = Interp::new();
        let f = ip.sort(0);
        let a = ip.sort(1);
        let ef = Ev::Proved(Thm::eq_refl(f.clone()));
        let ea = Ev::Proved(Thm::eq_refl(a.clone()));
        let out = app_cong(&mut ip, &ef, &ea);
        let lhs = ip.app(f.clone(), a.clone());
        assert_eq!(*out.thm().unwrap().concl(), Formula::eq(lhs.clone(), lhs));
        // One gap on either side is a gap overall.
        assert!(app_cong(&mut ip, &Ev::Gap(Gap::FunEta), &ea).gap().is_some());
        assert!(app_cong(&mut ip, &ef, &Ev::Gap(Gap::FunEta)).gap().is_some());
    }

    /// **`tryFunEta` end to end**: the identity graph on `Prop` and itself,
    /// shown equal by pointwise agreement rather than by reflexivity.
    ///
    /// A weak version of this test would feed it two syntactically identical
    /// terms and pass on `eq_refl` alone. This one goes through
    /// `funspace_ext`: the premises are the two memberships and a discharged
    /// pointwise family, and the conclusion is checked to be the equation
    /// claimed. That is the path `assert_def_eq`'s eta branch will take.
    #[test]
    fn fun_eta_proves_equality_from_pointwise_agreement() {
        use crate::scope::Scopes;
        let mut ip = Interp::new();
        let mut sc = Scopes::new();
        let prop = ip.sort(0);

        // `f := ⟦λ x:Prop. x⟧`, and `g` the same graph.
        let tok = sc.open(&mut ip.env, prop.clone());
        let x = sc.get(0).unwrap().var();
        let site = ip.lam_site(&Term::var(x), x).expect("lam site");
        // `Γ ⊢ t(x) ∈ ⟦Prop⟧`, then discharge to the λ typing's premise.
        let mem = sc.get(0).unwrap().assumption().clone();
        let mem = ip.to_body_symbol(&site, x, &mem).expect("to t");
        let closed = sc.close_checked(tok, &mem);
        let family = closed.discharge(&mem).expect("discharge");
        let f_mem = ip
            .lam_typing_fs(&site, prop.clone(), prop.clone(), &family)
            .expect("λ typing");
        let f = ip.lam_term(&site, prop.clone());

        // Pointwise agreement of `f` with itself, over a fresh scope.
        let tok = sc.open(&mut ip.env, prop.clone());
        let y = sc.get(0).unwrap().var();
        let refl = Thm::eq_refl(ip.app(f.clone(), Term::var(y)));
        let closed = sc.close_checked(tok, &refl);
        let pw = closed.discharge(&refl).expect("discharge pointwise");

        let conv = fun_eta_leg(
            &mut ip,
            prop.clone(),
            prop,
            f.clone(),
            f.clone(),
            &Ev::Proved(f_mem.clone()),
            &Ev::Proved(f_mem),
            &Ev::Proved(pw),
            sort(Level::Zero),
        );
        let thm = conv.ev.thm().expect("fun eta certificate");
        assert_eq!(*thm.concl(), Formula::eq(f.clone(), f));
        assert!(thm.hyps().is_empty());
    }

    /// Zeta costs nothing: the interpretation was chosen to make the two sides
    /// the same `Term`.
    #[test]
    fn zeta_is_reflexivity_by_construction() {
        let ip = Interp::new();
        let t = ip.sort(2);
        let c = zeta_leg(sort(Level::Zero), &t);
        assert_eq!(*c.ev.thm().unwrap().concl(), Formula::eq(t.clone(), t));
    }
}
