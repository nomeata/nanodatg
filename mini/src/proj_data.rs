//! **A projection out of a class-(T) structure at a *data* field** — the term
//! (`MINI-HANDOFF.md` §11's row 4, `SCOPING.md` §9's construction 3).
//!
//! # Interface
//!
//! ```text
//! proj_data::term(mach, j, z)                  -> Term        ⟦proj[T,j] s⟧
//! proj_data::computes(env, mach, ind, j, y⃗)    -> Option<Thm> ⊢ πⱼ(ctor₀(y⃗)) = yⱼ
//! ```
//!
//! Nothing consumes either yet, and that is deliberate — see *What is missing*
//! below, and `MINI-HANDOFF.md` §2's two counter-examples for why a value with
//! a named future consumer is kept rather than re-derived.
//!
//! # Route (b), and the term it produces
//!
//! `Prod.fst := fun α β self => proj[Prod,0] self` projects at a **variable**,
//! so `whnf`'s proj-of-ctor step never fires and `⟦projⱼ x⟧` has to be a real
//! term. Two routes were scoped and route (b) — the carrier's own structure —
//! was chosen on an invariant: route (a), via the eliminator, would make
//! `whnf`'s `Expr::Proj` arm rewrite a `Proj` node into a `rec` application,
//! changing `cur` into an expression that is **not a subterm of its input**,
//! which every other arm preserves.
//!
//! Route (b) is a pure composite of term-formers `derived` already has, and it
//! is shorter than the scope suggests because *every layer of a class-(T)
//! carrier element is a Kuratowski pair*:
//!
//! ```text
//! ctor₀(y⃗)  =  sup( Inj₀(tuple(y⃗)), f(∅) )       Inductive::ctor_term
//!           =  ⟨ ⟨∅, ⟨y₀, ⟨y₁, … ⟨y_{k-1}, •⟩…⟩⟩⟩ , f(∅) ⟩
//! ```
//!
//! — `sup(a,f)` is `⟨a,f⟩`, `Inj₀(x)` unfolds to `inl(x) = ⟨∅,x⟩`, and
//! `Telescope::tuple_of` is the right-nested pair chain. So
//!
//! ```text
//! πⱼ(z)  :=  compⱼ( π₂( π₁ z ) )  =  π₁(π₂ʲ(π₂(π₁ z)))
//! ```
//!
//! reaches field `j` in `j + 3` projections, and its computation rule is `j + 3`
//! instantiations of [`Proj::fst`](derived::proj::Proj) /
//! [`Proj::snd`](derived::proj::Proj) plus the injection's defining equation —
//! **all unconditional**, no Separation, no induction, and no hypothesis about
//! `z` at all. [`computes`] is that chain and `tests` cashes it.
//!
//! # What is missing, and it is **not** a term — the scope said it was
//!
//! *(`SCOPING.md` §9's construction 3 and `MINI-HANDOFF.md` §11's row 4 both
//! record this row as owing "a **term** — the only one that does", against
//! three sibling rows owing only a certificate. The term is above and it is
//! the small half. What the row also owes, and neither note says, is a
//! **theorem**, and it is `derived/`'s by every criterion the other three rows
//! were split on.)*
//!
//! The constant's obligation is `⊢ ⟦Prod.fst.{σ}⟧ ∈ ⟦ty[σ]⟧`, and mini's λ
//! clause reduces it to the nest bottom's
//!
//! ```text
//! Γ, self ∈ ind(⟦α⟧,⟦β⟧)  ⊢  πⱼ(self) ∈ βⱼ(⟦α⟧,⟦β⟧, π₀(self), …, π_{j-1}(self))
//! ```
//!
//! and **nothing in `derived/` states that.** [`computes`] is about a
//! constructor term; this is about an arbitrary carrier element, and getting
//! from one to the other is exactly the inversion the non-indexed carrier does
//! not have ([`Ctor`](derived::inductive::Ctor) has `mem` and `inj` only).
//! Composing `Telescope::proj_mem[j]` with `ISumSyms::no_junk` and
//! `bound::w_inversion_at` would do it and costs two existential eliminations;
//! the cheaper route is the one its three siblings already take:
//!
//! ```text
//! decl_rect at   φ(z) := πⱼ(z) ∈ βⱼ(p⃗, π₀(z), …, π_{j-1}(z))
//!
//! ⊢ ∀p⃗ ∀z. ( z ∈ ind(p⃗) → πⱼ(z) ∈ βⱼ(p⃗, π₀ z, …, π_{j-1} z) )
//! ```
//!
//! whose single induction step is `∀y⃗. (⋀ yq ∈ βq(p⃗,y⃗<q) → φ(ctor₀(y⃗)))`, and
//! `φ(ctor₀(y⃗))` is `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` — conjunct `j` of its own antecedent —
//! after `j + 1` rewrites by [`computes`]. So it is `decl_rect` at a φ that is
//! *not* constant in `z`, which is the only structural difference from
//! [`DeclFields`](derived::inductive::DeclFields), and it is the **fourth
//! member of the same family**:
//!
//! | class | major premise | φ | where |
//! |---|---|---|---|
//! | (S) | `• ∈ A_φ(p⃗)` | constant | `family::le_prop_fields` |
//! | (P) | `• ∈ ‖ind(p⃗)‖` | constant | `family::trunc_fields` |
//! | (T), `Prop` fields | `z ∈ ind(p⃗)` | constant | `decl_fields` |
//! | **(T), data fields** | `z ∈ ind(p⃗)` | **`πⱼ(z) ∈ βⱼ(…)`** | **unbuilt** |
//!
//! **Why `derived/` and not here**, on the same three grounds row 2 was split
//! on: it mentions no Lean syntax and no `Expr` at all; it is the fourth member
//! of a family whose other three live in `derived/src/inductive/`; and its
//! step wants `inductive::rec_shared`'s `rewrite_under`, which is private to
//! that module. Mini's side is then a fourth branch in [`crate::proj_prop`]
//! plus [`term`] above, and the routing already keys on which store holds the
//! declaration.
//!
//! **The σ question answers "the same" here**, unlike on row 2: `Prod.fst`'s
//! field sort is `Sort (u+1)`, a successor, so it is data at *every* σ. What
//! this route would close is `Prod` at both σ **and** the `{1,1}` halves of
//! `PProd`/`PSigma` that row 2 declines — one theorem, 16 pairs.
//!
//! # Nothing here searches
//!
//! [`computes`] rebuilds the constructor term from
//! [`Inductive::ctor_term`](derived::inductive::Inductive) and checks its own
//! conclusion against `yⱼ` on the nose, so a chain that walked into the wrong
//! component is a `None` and never an equation about the wrong field.

// **Stored ahead of its consumer, deliberately.** `MINI-HANDOFF.md` §2's rule
// is that a value computed where its inputs are live must be kept rather than
// re-derived, and its two counter-examples — `zoneb::IndexAx` and
// `class_s_ix::of` — were both kept this way with the consumer named, and both
// were consumed in the next commit. What is named here is the fourth branch of
// `crate::proj_prop`, which is one theorem away and cannot be written until
// that theorem exists. The alternative is to delete a chain that has been
// checked at three indices and write it again from the same header.
#![allow(dead_code)]

use kernel::{Env, Formula, Term, Thm};

use derived::inductive::{Inductive, Machine};
use derived::sigma::Telescope;

/// `⊢ g(a) = g(b)` from `⊢ a = b`, for a term-former `g` given as a closure.
///
/// [`derived::congr_arg`] does this for one argument of one `FnSym`; `π₁` and
/// `π₂` are *composites* (`π₁ p = ⋃⋂p`, `π₂ p = app({p}, π₁ p)`, and the second
/// mentions `p` twice), so a per-symbol congruence would need three steps and
/// the two occurrences would have to move together. One Leibniz over the hole
/// does both.
fn congr_of(env: &mut Env, g: &dyn Fn(Term) -> Term, ab: &Thm) -> Option<Thm> {
    let (a, b) = ab.concl().as_eq()?;
    let x = env.fresh_var();
    let phi = Formula::eq(g(a.clone()), g(Term::var(x)));
    let leib = Thm::eq_leibniz(a.clone(), b, x, phi);
    Thm::mp(&Thm::mp(&leib, ab)?, &Thm::eq_refl(g(a)))
}

/// The tag component's payload, `π₂(π₁ z)` — the constructor's packed
/// telescope element, for a **one-constructor** declaration.
///
/// `π₂` and not an injection inverse: `Inj₀(x)` is `inl(x) = ⟨∅,x⟩`, so the
/// payload is literally the pair's second component and no inverse symbol is
/// needed. At a declaration with more than one constructor the *same* term
/// would still be the payload of whichever `Injᵢ` the element carries, which is
/// precisely why the tag has to be identified before this is meaningful — and
/// why every consumer of this file must be single-constructor.
pub(crate) fn payload(mach: &Machine, z: Term) -> Term {
    let ap = &mach.wt.sums.ap;
    mach.proj.snd_of(ap, mach.proj.fst_of(ap, z))
}

/// `⟦proj[T,j] s⟧ = πⱼ(⟦s⟧) = compⱼ(π₂(π₁ ⟦s⟧))`.
pub(crate) fn term(mach: &Machine, j: usize, z: Term) -> Term {
    let ap = &mach.wt.sums.ap;
    Telescope::comp_of(ap, &mach.proj, j, payload(mach, z))
}

/// `⊢ πⱼ(ctor₀(y⃗)) = yⱼ` — **unconditional**, and the whole computation rule
/// route (b) needs.
///
/// `ind` must have exactly one constructor with no recursive field; `ys` are
/// its `k` fields. The chain, in the order it is built:
///
/// ```text
/// π₁ ⟨Inj₀(tuple), f(∅)⟩  = Inj₀(tuple)        Proj::fst
/// Inj₀(tuple)             = ⟨∅, tuple⟩         ISumSyms::inj_ax at depth 0
/// π₂ ⟨∅, tuple⟩           = tuple              Proj::snd
/// π₂ ⟨y_q, rest⟩          = rest               Proj::snd, q < j
/// π₁ ⟨y_j, rest⟩          = y_j                Proj::fst
/// ```
///
/// with one [`congr_of`] between consecutive steps, because each rewrites a
/// *subterm* of the next one's subject.
pub(crate) fn computes(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    j: usize,
    ys: &[Term],
) -> Option<Thm> {
    if ind.spec.ctors.len() != 1 || j >= ys.len() {
        return None
    }
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let ctor = ind.ctor_term(mach, 0, ys, &[])?;
    let tuple = Telescope::tuple_of(s, ys);
    let tag = mach.syms.inj(0, tuple.clone())?;
    let recf = derived::recarg::RecArg::of(s, &mach.cases, &[]);

    // ── the tag, out of the outer pair ──────────────────────────────────────
    let e_tag = derived::inst_all(&mach.proj.fst, &[tag.clone(), recf])?;
    if e_tag.concl().as_eq()? != (mach.proj.fst_of(ap, ctor.clone()), tag.clone()) {
        return None
    }

    // ── the payload, out of the tag: unfold `Inj₀`, then `π₂` ──────────────
    let unfold = derived::inst_all(mach.syms.inj_ax(0)?, std::slice::from_ref(&tuple))?;
    let (_, inl) = unfold.concl().as_eq()?;
    if inl != s.inl(tuple.clone()) {
        return None
    }
    let snd = |t: Term| mach.proj.snd_of(ap, t);
    let e_pay = {
        let a = congr_of(env, &snd, &e_tag)?;
        let b = congr_of(env, &snd, &unfold)?;
        let via = derived::eq_trans(env, &a, &b)?;
        let step = derived::inst_all(&mach.proj.snd, &[s.zero(), tuple.clone()])?;
        derived::eq_trans(env, &via, &step)?
    };
    if e_pay.concl().as_eq()? != (payload(mach, ctor.clone()), tuple.clone()) {
        return None
    }

    // ── down the telescope: `j` tails, then one head ────────────────────────
    let mut cur = e_pay;
    for q in 0..j {
        let rest = Telescope::tuple_of(s, &ys[q + 1..]);
        let step = derived::inst_all(&mach.proj.snd, &[ys[q].clone(), rest])?;
        let lift = congr_of(env, &snd, &cur)?;
        cur = derived::eq_trans(env, &lift, &step)?;
    }
    let fst = |t: Term| mach.proj.fst_of(ap, t);
    let head = derived::inst_all(
        &mach.proj.fst,
        &[ys[j].clone(), Telescope::tuple_of(s, &ys[j + 1..])],
    )?;
    let lift = congr_of(env, &fst, &cur)?;
    let out = derived::eq_trans(env, &lift, &head)?;

    // The conclusion is checked against `yⱼ` and against the term-former this
    // module hands out, so a chain that walked into the wrong component — or a
    // `term` that stopped counting somewhere else — is a `None`.
    if out.concl().as_eq()? != (term(mach, j, ctor), ys[j].clone()) {
        return None
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use derived::inductive::{CtorSpec, DeclSpec};
    use kernel::FreeVar;

    /// An opaque field type of arity `np + j` whose body is its `which`-th
    /// argument — `derived/tests/decl_fields.rs`'s fixture, and opaque for the
    /// same reason: the *symbol application* is what appears in every term
    /// below and nothing here unfolds it.
    fn field(env: &mut Env, np: usize, j: usize, which: usize) -> kernel::FnSym {
        let vars: Vec<FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
        let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
        let t = args[which].clone();
        derived::define_abbrev(env, &vars, &t).expect("an abbreviation").0
    }

    /// **Route (b)'s computation rule, at three fields.**
    ///
    /// Three and not two, because the claim under test is that
    /// `πⱼ = π₁ ∘ π₂ʲ ∘ π₂ ∘ π₁` counts the *right* number of tails: at two
    /// fields an off-by-one in either the `π₂(π₁ ·)` prefix or the `π₂ʲ` walk
    /// still lands on a component of the tuple and the equation still has two
    /// visibly different sides, so a wrong index passes. At three, `j = 1`'s
    /// answer is distinct from both neighbours. (`MEMORY`: two atoms cannot
    /// distinguish.)
    ///
    /// The declaration is `T (a b c : Type 0) : Type 0 | mk : a → b → c → T`
    /// with **no recursive field**, which is the shape route (b) is about, and
    /// the three field types are three *different* parameters so a chain that
    /// returned the wrong one is caught by the statement rather than by luck.
    #[test]
    fn the_projection_chain_reaches_the_field_it_names() {
        let mut env = Env::new();
        let mut mach = Machine::new(&mut env).expect("the apparatus");
        // Three parameters, three plain fields, `βq(p⃗,y⃗<q) = pq`.
        let betas: Vec<kernel::FnSym> = (0..3).map(|q| field(&mut env, 3, q, q)).collect();
        let spec = DeclSpec::new(3, vec![CtorSpec::new(betas.clone(), 0)]);
        let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the carrier");
        let ys: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();

        for j in 0..3 {
            let thm = computes(&mut env, &mach, &ind, j, &ys)
                .unwrap_or_else(|| panic!("j = {j}: the chain did not compute"));
            let (lhs, rhs) = thm.concl().as_eq().expect("an equation");
            assert_eq!(rhs, ys[j], "j = {j}: the chain reached the wrong field");
            assert_eq!(
                lhs,
                term(&mach, j, ind.ctor_term(&mach, 0, &ys, &[]).expect("the ctor term")),
                "j = {j}: the equation is not about this module's own term"
            );
            assert!(thm.hyps().is_empty(), "j = {j}: the computation rule is unconditional");
            // …and it is not the *same* equation at two indices, which a chain
            // that ignored `j` would make it.
            assert_ne!(rhs, ys[(j + 1) % 3], "j = {j}: the fields are not distinguished");
        }
    }
}
