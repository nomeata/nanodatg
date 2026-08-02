//! **A declaration with no constructors** — `Empty`, its carrier, and its
//! eliminator.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a. ¬(a ∈ A)                                        [EmptyDecl::no_tags]
//! ⊢ closed(A, B, ∅)                                     [EmptyDecl::closed_zero]
//! ⊢ ∀p⃗ ∀z. ¬(z ∈ ind(p⃗))                                [EmptyDecl::empty]
//! ⊢ ∀p⃗. ind(p⃗) = 0                                      [EmptyDecl::is_zero]
//! ⊢ ∀p⃗ ∀f ∀g ∀z. (z ∈ ind(p⃗) → app(f,z) ∈ app(g,z))     [EmptyDecl::rec_typed]
//! ⊢ ∀p⃗ ∀T. ∅ ∈ fs(ind(p⃗), T)                            [EmptyDecl::rec_in_funspace]
//! ⊢ ∀p⃗ ∀z. (z ∈ ind(p⃗) → φ(z))    for any caller's φ    [EmptyDecl::anything]
//! ```
//!
//! **There are no ι rules, and that is a statement rather than an omission.** A
//! ι rule is an equation `app(rec, ctorᵢ(…)) = …`, one per constructor; a
//! declaration with no constructors has none to state, and a wiring that goes
//! looking for one is looking for something that does not exist. Nothing in this
//! file is conditional on a minor premise either, for the same reason: there are
//! no minors.
//!
//! # `rec_typed` is quantified over the eliminator, deliberately
//!
//! `Empty.rec`'s value is never demanded, because demanding it needs an
//! inhabitant of `⟦Empty⟧` and there is none. So rather than pick a term for the
//! eliminator and prove that one well typed, [`EmptyDecl::rec_typed`] is
//! universally quantified over **both** the eliminator `f` and the motive `g`: a
//! wiring may interpret `Empty.rec` as whatever its uniform path produces — the
//! `grec(p⃗, s⃗, T)` shape, `∅`, or a nest it built for another reason — and the
//! typing obligation is discharged either way, at no extra cost and with no
//! obligation to agree with this file about the choice.
//!
//! It does still fix the *shape* of the obligation — `app(f,z) ∈ app(g,z)` is
//! what a **dependent** motive produces, and a non-dependent one asks for
//! `app(f,z) ∈ T`. [`EmptyDecl::anything`] is the scheme both are instances of:
//! at an empty carrier *every* obligation guarded by `z ∈ ind(p⃗)` is one
//! `ex_falso`, so the caller names its own formula rather than choosing from a
//! menu this file guessed at.
//!
//! That generality is also what stops the statement being a tautology, which
//! matters more here than usual because the conclusion is vacuously true. `∀f ∀g
//! ∀z. (z ∈ C → app(f,z) ∈ app(g,z))` is **equivalent to `C = ∅`**: if `C` had a
//! member `z₀`, take `g := ∅`, whose value at every argument is `∅`
//! ([`crate::wtype::app_of_empty`]), and the conclusion would put `app(f,z₀)`
//! into the empty set. So the theorem is not satisfied by a construction whose
//! carrier is `1` and whose motive happens to be constant — the direction a
//! vacuous theorem usually escapes in. `derived/tests/empty_decl.rs` derives
//! that converse rather than asserting it.
//!
//! # Why the carrier is empty, and why it is not one line
//!
//! `A = Sum_0()` has no members ([`ISumSyms::no_junk`](crate::isum::ISumSyms::no_junk)
//! at zero summands), so `closed(A,B,∅)` holds with nothing to check, and W2
//! ([`crate::wtype::w_induction`]) — `W` is the *least* closed subset of the
//! bound — puts the whole carrier inside `∅`. `∅ ⊆ u` is the other half of W2's
//! antecedent and is free. Extensionality then turns "no members" into the
//! **equation** `ind(p⃗) = 0`, which is the form the non-vacuity argument needs:
//! a membership statement about a subset of `{•}` survives the carrier being
//! either `0` or `1`, and an equation does not.
//!
//! # Why this is not [`GenRecursor`](super::GenRecursor) with a relaxed guard
//!
//! `GenRecursor::build` declines `n = 0`, and the decline is **load-bearing in
//! three independent places**, none of which is a guard:
//!
//! * `HYP` is a [`Formula`], built by `conj_of` over the `n` minor typings.
//!   At `n = 0` there is no formula for it to be, and the field would have to
//!   become an `Option`, through `step_typed_at` and `iota_at` and every
//!   consumer;
//! * [`step_cases`](super::members) case-splits the tag through `disj_of` over
//!   the `n` summands. `disj_of` of nothing is not a formula either, so
//!   [`step_single_valued`](super::values) cannot run;
//! * `step_typed_at` splits the same way, and additionally compares `no_junk`'s
//!   statement against `mem(a, A) → ⋁ᵢ …`. At `n = 0`, `no_junk` states
//!   `¬(a ∈ A)`, which is a *different shape*, so even the guard would refuse.
//!
//! The last is the tell: at `n = 0` the mathematics is not the general argument
//! with an empty loop, it is a shorter and different argument — the step is `∅`,
//! single-valuedness is immediate rather than `n²` branch comparisons, and the
//! typing is vacuous rather than a case analysis. So this is a genuine gap, and
//! a cheap one, and it belongs beside the general recursor rather than inside
//! it.
//!
//! # The class-(P) hole is the same hole
//!
//! [`TruncRecursor`](super::family::TruncRecursor) also declines `n = 0`, and
//! for the *same* underlying reason: its conclusion is vacuous there and its
//! `decl_rect` has no induction to state. The two want one construction and not
//! two, and it is this one — [`EmptyDecl::empty`] is the whole content. Given a
//! class-(P) declaration with no constructors, `‖ind(p⃗)‖ = 0` is
//! [`TruncCarrier::empty_at`](super::family::TruncCarrier::empty_at) at
//! [`EmptyDecl::empty`], and the class-(P) rule's conclusion follows from it by
//! ex falso exactly as [`EmptyDecl::rec_typed`] does here.
//!
//! What is *not* done is relaxing `TruncCarrier::over_declaration`'s own
//! `n = 0` guard, which — unlike `GenRecursor`'s — is not forced by anything in
//! its machinery: every field it builds is a [`Trunc`](crate::prop::Trunc)
//! instantiation independent of the constructor list, and the per-constructor
//! loop is simply empty. There is no corpus witness for a class-(P) declaration
//! with no constructors (`False` is class (S), and `Empty` is `Sort 1`-valued
//! and so class (T)), so the guard stays and this paragraph is the record of
//! what to do if one appears.
//!
//! # Nothing here is an axiom
//!
//! One Extensionality, for the equation. Everything else is an instance of
//! `no_junk`, W2, or `ex_falso`.

use kernel::{Env, Formula, Term, Thm};

use crate::{and_intro, ex_falso, gen_all, inst_all, syl};

use super::carrier::Inductive;
use super::machine::Machine;

/// A declaration with no constructors: its carrier is empty, and its eliminator
/// is typed by that alone.
pub struct EmptyDecl {
    /// `⊢ ∀a. ¬(a ∈ A)` — the tag set `Sum_0()` has no members.
    pub no_tags: Thm,
    /// `⊢ closed(A, B, ∅)` — vacuously, there being no tag to close under.
    pub closed_zero: Thm,
    /// **`⊢ ∀p⃗ ∀z. ¬(z ∈ ind(p⃗))`** — the carrier is empty. Everything else in
    /// this file, and the class-(P) statement the header discusses, is a
    /// corollary of this one.
    pub empty: Thm,
    /// **`⊢ ∀p⃗. ind(p⃗) = 0`** — the same fact as an *equation at a concrete
    /// set*, which is the form non-vacuity needs.
    pub is_zero: Thm,
    /// **`⊢ ∀p⃗ ∀f ∀g ∀z. (z ∈ ind(p⃗) → app(f,z) ∈ app(g,z))`** — the
    /// eliminator's typing, at *any* eliminator and *any* motive. See the
    /// header for why it is quantified rather than pinned, and why that is what
    /// stops it being a tautology.
    pub rec_typed: Thm,
    /// `⊢ ∀p⃗ ∀T. ∅ ∈ fs(ind(p⃗), T)` — and the empty function really is one, so
    /// a wiring that types `⟦Empty.rec⟧` as a function into the target has it
    /// without going through [`EmptyDecl::rec_typed`] at all.
    pub rec_in_funspace: Thm,
}

impl EmptyDecl {
    /// The carrier and the eliminator of a declaration with **no
    /// constructors**.
    ///
    /// `None` unless `ind` was translated over `mach` ([`Inductive::is_over`])
    /// and has an empty constructor list — a declaration with constructors has
    /// a non-empty carrier and every theorem below would be false of it, so
    /// this is a refusal and not a fast path.
    pub fn over_declaration(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
    ) -> Option<EmptyDecl> {
        if !ind.spec.ctors.is_empty() || !ind.is_over(mach) {
            return None
        }
        let s = &mach.wt.sums;
        let ap = &s.ap;
        let zero = s.zero();
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

        // ── nothing is a tag ────────────────────────────────────────────────
        let no_tags = mach.syms.no_junk(env, s, 0)?;
        let av = env.fresh_var();
        let ta = Term::var(av);
        let ma = Formula::mem(ta.clone(), ind.tags.clone());
        let not_a = inst_all(&no_tags, std::slice::from_ref(&ta))?;
        if !crate::establishes(&not_a, &Formula::not(ma.clone())) {
            return None
        }

        // ── `closed(A, B, ∅)`, with nothing to close under ──────────────────
        let fv = env.fresh_var();
        let tf = Term::var(fv);
        let inner = Formula::forall(
            fv,
            Formula::imp(
                Formula::mem(
                    tf.clone(),
                    s.fs.of(ap.apply(ind.fibre.fam.clone(), ta.clone()), zero.clone()),
                ),
                Formula::mem(crate::opair(ap.sets.up, ta.clone(), tf.clone()), zero.clone()),
            ),
        );
        let closed_zero = Thm::gen(av, &syl(&not_a, &ex_falso(inner))?);
        if *closed_zero.concl()
            != crate::wtype::closed(env, s, &ind.tags, &ind.fibre.fam, &zero)
        {
            return None
        }

        // ── `∅ ⊆ u`, and W2 ─────────────────────────────────────────────────
        let sv = env.fresh_var();
        let ts = Term::var(sv);
        let sub = Thm::gen(
            sv,
            &syl(
                &inst_all(&ap.empty_ax, std::slice::from_ref(&ts))?,
                &ex_falso(Formula::mem(ts.clone(), ind.bound.clone())),
            )?,
        );
        if *sub.concl() != kernel::thm::subset(env, zero.clone(), ind.bound.clone()) {
            return None
        }
        let w2 = crate::wtype::w_induction(env, s, mach.wt.w, &mach.wt.w_ax)?;
        let at = inst_all(
            &w2,
            &[
                ind.tags.clone(),
                ind.fibre.fam.clone(),
                ind.bound.clone(),
                zero.clone(),
            ],
        )?;
        let into_zero = Thm::mp(&at, &and_intro(&sub, &closed_zero))?;

        // ── the carrier is empty, at the declaration's own symbol ───────────
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let mem_ind = Formula::mem(tz.clone(), ind.carrier.clone());
        let mem_zero = Formula::mem(tz.clone(), zero.clone());
        let not_in_zero = inst_all(&ap.empty_ax, std::slice::from_ref(&tz))?;
        let not_in_w = syl(&inst_all(&into_zero, std::slice::from_ref(&tz))?, &not_in_zero)?;
        // `ind(p⃗)` *is* `W`, one Leibniz along the carrier's defining equation.
        let to_ty = crate::eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?;
        let hole = env.fresh_var();
        let not_in_ind = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    ind.wty.clone(),
                    ind.carrier.clone(),
                    hole,
                    Formula::not(Formula::mem(tz.clone(), Term::var(hole))),
                ),
                &to_ty,
            )?,
            &not_in_w,
        )?;
        if !crate::establishes(&not_in_ind, &Formula::not(mem_ind.clone())) {
            return None
        }
        let empty = gen_all(&ps_vars(ind), &Thm::gen(zv, &not_in_ind));

        // ── the equation, by Extensionality ─────────────────────────────────
        let same = and_intro(
            &syl(&not_in_ind, &ex_falso(mem_zero.clone()))?,
            &syl(&not_in_zero, &ex_falso(mem_ind.clone()))?,
        );
        if *same.concl() != Formula::iff(mem_ind, mem_zero) {
            return None
        }
        let ext = inst_all(
            &Thm::ax_extensionality(env),
            &[ind.carrier.clone(), zero.clone()],
        )?;
        let eq_body = Thm::mp(&ext, &Thm::gen(zv, &same))?;
        if !crate::establishes(&eq_body, &Formula::eq(ind.carrier.clone(), zero.clone())) {
            return None
        }
        let is_zero = gen_all(&ps_vars(ind), &eq_body);

        // ── the eliminator, at any term and any motive ──────────────────────
        let (ev, gv) = (env.fresh_var(), env.fresh_var());
        let (te, tg) = (Term::var(ev), Term::var(gv));
        let rec_body = syl(
            &not_in_ind,
            &ex_falso(Formula::mem(
                ap.apply(te.clone(), tz.clone()),
                ap.apply(tg.clone(), tz.clone()),
            )),
        )?;
        let mut rq = ps_vars(ind);
        rq.extend([ev, gv, zv]);
        let rec_typed = gen_all(&rq, &rec_body);

        // ── and the empty function is a function out of it ──────────────────
        let tv = env.fresh_var();
        let tt = Term::var(tv);
        let is_fun = inst_all(&crate::wtype::empty_is_a_function(env, s)?, std::slice::from_ref(&tt))?;
        if !crate::establishes(&is_fun, &Formula::mem(zero.clone(), s.fs.of(zero.clone(), tt.clone())))
        {
            return None
        }
        let back = crate::eq_symm(env, &eq_body)?;
        let hole2 = env.fresh_var();
        let (fs, tt_c, zero_c) = (s.fs.clone(), tt.clone(), zero.clone());
        let in_fs = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    zero.clone(),
                    ind.carrier.clone(),
                    hole2,
                    Formula::mem(zero_c.clone(), fs.of(Term::var(hole2), tt_c.clone())),
                ),
                &back,
            )?,
            &is_fun,
        )?;
        let mut fq = ps_vars(ind);
        fq.push(tv);
        let rec_in_funspace = gen_all(&fq, &in_fs);

        let out = EmptyDecl {
            no_tags,
            closed_zero,
            empty,
            is_zero,
            rec_typed,
            rec_in_funspace,
        };
        out.rests_on_nothing().then_some(out)
    }

    /// **`⊢ ∀p⃗ ∀z. (z ∈ ind(p⃗) → φ(z))` for any formula `φ` the caller
    /// names** — ex falso at the empty carrier, as a scheme.
    ///
    /// [`EmptyDecl::rec_typed`] is this at
    /// `φ := app(f,z) ∈ app(g,z)`, which is the obligation a *dependent* motive
    /// produces; a non-dependent one asks for `app(f,z) ∈ T` instead, and a
    /// wiring that states its typing some third way asks for something else
    /// again. Rather than guess which, or offer a menu, this takes the caller's
    /// own formula: at an empty carrier every obligation of that shape is one
    /// `ex_falso`, and the caller is the only one who knows what it has to
    /// discharge.
    ///
    /// `zv` is the variable `phi` speaks about. `None` if `zv` is one of the
    /// declaration's parameters — the final generalisation would capture — or
    /// if `ind` is not the declaration this was built over, which is caught by
    /// rebuilding the membership at `ind`'s own carrier and comparing.
    pub fn anything(&self, ind: &Inductive, zv: kernel::FreeVar, phi: &Formula) -> Option<Thm> {
        if ind.params.contains(&zv) {
            return None
        }
        let mut args: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        args.push(Term::var(zv));
        let not_in = inst_all(&self.empty, &args)?;
        if !crate::establishes(
            &not_in,
            &Formula::not(Formula::mem(Term::var(zv), ind.carrier.clone())),
        ) {
            return None
        }
        let mut quant = ind.params.clone();
        quant.push(zv);
        Some(gen_all(&quant, &syl(&not_in, &ex_falso(phi.clone()))?))
    }

    /// Whether every theorem this holds is a `⊢` with nothing on the left.
    ///
    /// Checked before [`EmptyDecl::over_declaration`] returns. Every field is
    /// documented `⊢ …` and none of them carries an antecedent — there are no
    /// minors and no `HYP` — so a sequent hypothesis here would be invisible to
    /// the conclusion comparisons above and would make the final `Thm::gen`
    /// over the parameters unsound.
    pub fn rests_on_nothing(&self) -> bool {
        crate::all_unconditional(&[
            &self.no_tags,
            &self.closed_zero,
            &self.empty,
            &self.is_zero,
            &self.rec_typed,
            &self.rec_in_funspace,
        ])
    }
}

/// The declaration's parameter variables.
fn ps_vars(ind: &Inductive) -> Vec<kernel::FreeVar> { ind.params.clone() }
