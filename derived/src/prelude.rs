//! The **ambient signature** an interpretation of type theory is built in: the
//! universe tower, set-theoretic application, the function space, and the
//! handful of facts about them that no single construction owns.
//!
//! # Interface
//!
//! ```text
//! prelude()               -> Rc<Prelude>     // built once per thread, then replayed
//! fast_forward(env, &p)   -> ()              // advance a fresh Env past the ids it used
//! ```
//!
//! [`Prelude`] is a bundle of symbols and theorems, all of them public fields;
//! [`Prelude::u0`], [`Prelude::u1`], [`Prelude::point`] and
//! [`Prelude::fs_sym`] are the four shorthands worth having. The theorems it
//! carries are, in full:
//!
//! ```text
//! ⊢ ∀x. x ∈ U(x)                                                   [mem_u]
//! ⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))     [lu_ax]
//! ⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)                                       [pow_ax]
//! ⊢ ∀a. fs(a,a) ∈ U(a)                                             [fs_in_u]
//! ⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))       [fs_cong]
//! ⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)            [fs_app_mem]
//! ⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ ∀x ∈ a. app(f,x) ∈ c) → f ∈ fs(a,c))
//!                                                                  [fs_retarget]
//! ⊢ U₀ ∈ U₁                                                        [u0_in_u1]
//! ⊢ fs(U₀,U₀) ∈ U₁                                                 [fs_u0_in_u1]
//! ```
//!
//! **Nothing here is an axiom of the target theory.** Every symbol is a
//! definitional extension or a signature extension, and every theorem is
//! derived; the whole thing is assembled by ordinary calls to the constructions
//! in this crate.
//!
//! # Why it is built once per thread
//!
//! [`crate::funcs::Apply::new`] and the least-universe operator are the same
//! derivation every time — they take no input beyond a fresh [`Env`] — but
//! together they cost on the order of ten milliseconds, and a caller that
//! creates one interpretation per declaration would pay that per declaration.
//! Building them once per thread and replaying the result is therefore worth
//! it.
//!
//! Replaying is sound because an [`Env`] is *only* a pair of counters: it
//! records no signature, so a theorem proved against one `Env` is a theorem,
//! full stop. All that must be arranged is that a fresh `Env` never re-issues a
//! symbol or variable the prelude already used, which [`fast_forward`] does by
//! burning the same number of ids. `FnSym::id`/`FreeVar::id` make the counts
//! observable, and [`Prelude::n_syms`]/[`Prelude::n_vars`] record them.
//!
//! # One pairing operation, not two
//!
//! [`crate::funcs::Apply::new`] and `funspace::Development::new` each build
//! their *own* [`crate::funcs::Sets`], so a version of this that called both
//! had two unrelated ordered pairs: `app`'s and `fs`'s. That costs nothing
//! while the two halves never meet — `lam`/`app` use one, `fs` the other, and
//! no lemma mentions both. The `Π` bridge is exactly a lemma that mentions both
//! (`f ∈ fs(A,B) → app(f,x) ∈ B`), so the development here is assembled by hand
//! over `ap.sets`: the product, the function space and the universe facts are
//! built from the same pairing `app` is built from, and
//! [`crate::ext::dprod_const_fibre`]'s stack checks would refuse anything else.
//!
//! # The universe tower is part of it
//!
//! Every symbol below comes out of [`crate::tower::Tower::new`], which
//! assembles exactly this stack — one `Apply`, one [`crate::funspace::Space`]
//! over it, one product, one function space, one [`crate::sums::Sums`] and one
//! `ω` — and then derives the closure properties of `Uₙ` on top. Building it
//! here rather than alongside is not an economy: `⟦Sort 0⟧` is `Tower::u0`,
//! which is `{0,1}` over the tower's *own* `Sums`, and a second `Sums` would
//! mint a second `∅` about which none of [`crate::anchor`]'s theorems say
//! anything. Any construction that needs a `Sums` should take this one rather
//! than build its own.

use std::rc::Rc;

use kernel::{Env, FnSym, Term, Thm};

use crate::funcs::Apply;
use crate::funspace as fsp;

/// The once-per-thread part of an interpretation's machinery.
///
/// See the module header for what is in it and why it is shared.
pub struct Prelude {
    /// The universe tower `U₀, U₁, U₂, …` and every closure property of it.
    /// Everything else in this struct is one of its components, or derived from
    /// one.
    pub tower: Rc<crate::tower::Tower>,
    /// Set-theoretic application, and everything it is built from.
    pub ap: Apply,
    /// The least-universe operator `U`.
    pub u_sym: FnSym,
    /// `⊢ ∀x. x ∈ U(x)`.
    pub mem_u: Thm,
    /// `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))` — `U`'s
    /// defining equation. Only an inductive-carrier construction needs it, but
    /// it has to come from the same `U` everything else speaks of, so it is
    /// carried here rather than rebuilt.
    pub lu_ax: Thm,
    /// The power set, likewise: [`crate::sums::Sums::over`] needs one, and it
    /// must be the one `fs` was carved out of.
    pub pow: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`.
    pub pow_ax: Thm,
    /// The Cartesian product `fs` was carved out of. Needed by
    /// [`crate::ext::lam_in_funspace_n`], which shows a graph is a *subset* of
    /// it.
    pub prod: fsp::Product,
    /// The function space `fs(a,b) = b^a`, over `ap.sets` and the Cartesian
    /// product carved from it.
    pub fs: fsp::Funspace,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`.
    pub fs_in_u: Thm,
    /// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))`.
    pub fs_cong: Thm,
    /// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)`.
    pub fs_app_mem: Thm,
    /// `⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ ∀x ∈ a. app(f,x) ∈ c) → f ∈ fs(a,c))`.
    pub fs_retarget: Thm,
    /// `⊢ U₀ ∈ U₁` — i.e. `⊢ ⟦Prop⟧ ∈ ⟦Type 0⟧`.
    ///
    /// `⟦Sort (u+1)⟧` is `U(⟦Sort u⟧)` for every `u` **except** `u = 0`, where
    /// the tower is seeded at `ω` instead (`U(U₀)` has no infinite member at
    /// all; see [`crate::tower`]). So the one instance of `⊢ ∀x. x ∈ U(x)`
    /// that used to carry `⟦Sort 0⟧ ∈ ⟦Sort 1⟧` no longer applies to it, and
    /// this is the theorem that does. Taken from [`crate::tower::Level`],
    /// which proves it from `⊢ ∀c. U₀ ∈ U(c)`.
    pub u0_in_u1: Thm,
    /// `⊢ fs(U₀,U₀) ∈ U₁` — i.e. `⊢ ⟦Prop → Prop⟧ ∈ ⟦Type 0⟧`.
    ///
    /// The same story as [`Prelude::u0_in_u1`], one operator along.
    /// `⊢ ∀a. fs(a,a) ∈ U(a)` used to carry this at `a := ⟦Prop⟧`, because
    /// `⟦Type 0⟧` was literally `U(⟦Prop⟧)`; with the tower seeded at `ω` it is
    /// not, and this is [`crate::tower::Tower::fs_u0_in_u1`], which the tower
    /// derives from its own function-space closure at level 1 and `U₀ ∈ U₁`.
    pub fs_u0_in_u1: Thm,
    /// How many function symbols the above consumed. See [`fast_forward`].
    pub n_syms: u32,
    /// How many free variables the above consumed. See [`fast_forward`].
    pub n_vars: u32,
}

impl Prelude {
    /// The function-space symbol.
    pub fn fs_sym(&self) -> FnSym { self.fs.fs }
    /// `⟦Sort 0⟧`, i.e. `Prop`, i.e. the tower's `U₀ = {0,1}`.
    pub fn u0(&self) -> Term { self.tower.u0() }
    /// `⟦Sort 1⟧`, i.e. `Type 0`, i.e. `U(ω)`.
    pub fn u1(&self) -> Term { self.tower.level(1) }
    /// **`•`, the proof object** — Carneiro §6.2's interpretation of every
    /// *proof*.
    ///
    /// The left-hand column of §6.2 sends `λx:α. e` and `e₁ e₂` to `•`
    /// whenever the term is a proof, and `⟦Prop⟧ = U₀ = {0,1}` is where the
    /// subsets of `{•}` those proofs inhabit live.
    pub fn point(&self) -> Term { self.tower.sums.point() }
}

thread_local! {
    static PRELUDE: std::cell::RefCell<Option<Rc<Prelude>>> =
        const { std::cell::RefCell::new(None) };
}

/// The ambient signature for this thread, built on first call and replayed
/// thereafter.
///
/// Panics if any step of the assembly fails. That is deliberate: every one of
/// them is a closed derivation with no input, so a failure is a bug in this
/// crate rather than anything a caller could have caused or could recover
/// from.
pub fn prelude() -> Rc<Prelude> {
    PRELUDE.with(|slot| {
        if let Some(p) = slot.borrow().as_ref() {
            return p.clone()
        }
        let mut env = Env::new();
        // **The whole ambient signature, in one chain.** `Tower::new` builds the
        // `Apply`, the `Space` over it, the product, the function space, the
        // `Sums` and `ω` — the exact stack this function used to assemble by
        // hand, in the same order and with the same "one pairing operation"
        // discipline — and then derives `Uₙ`'s closure properties on top. What
        // is left below is only what the tower has no use for and an
        // interpretation does: the *diagonal* function-space fact, congruence,
        // and the two halves of the `Π` bridge.
        let tower = Rc::new(crate::tower::Tower::new(&mut env).expect("TG prelude: the universe tower"));
        let ap = tower.sums.ap.clone();
        let space = &tower.space;
        let (u_sym, mem_u) = (space.lu, space.mem_lu.clone());
        let (lu_ax, pow, pow_ax) = (space.lu_ax.clone(), space.pow, space.pow_ax.clone());
        let (prod, fs) = (tower.sums.prod.clone(), tower.sums.fs.clone());

        // `⊢ U₀ ∈ U₁`. Level 1 is `U(ω)`, not `U(U₀)`, so `⊢ ∀x. x ∈ U(x)` does
        // not give `⟦Prop⟧ ∈ ⟦Type 0⟧` and this does.
        let u0_in_u1 = tower.at(1).expect("TG prelude: level 1 of the tower").u0_mem;
        let fs_u0_in_u1 = tower.fs_u0_in_u1.clone();

        let up_sub = fsp::upair_subset(&mut env, &space.sets).expect("TG prelude: unordered pairs are small");
        let pair_pp = fsp::pair_in_pow_pow(&mut env, &space.sets, space.pow, &space.pow_ax, &up_sub)
            .expect("TG prelude: ordered pairs are small");
        let (ml, mr) = fsp::mem_bin_union(&mut env, &space.sets).expect("TG prelude: binary union");
        let prod_sub = fsp::product_subset_pow_pow(&mut env, &space.sets, space.pow, &prod, &pair_pp, &ml, &mr)
            .expect("TG prelude: the product is small");
        let in_u_of = fsp::funspace_in_universe_of(&mut env, space, &prod, &prod_sub, &fs)
            .expect("TG prelude: the function space is small");
        let fs_in_u = fsp::funspace_in_universe(&mut env, space, &fs, &in_u_of)
            .expect("TG prelude: the diagonal function space is in the universe");

        let fs_cong = crate::ext::fs_cong(&mut env, &fs).expect("TG prelude: function-space congruence");
        // The two `b`-independent halves of the `Π` bridge, derived once rather
        // than inside every call to `dprod_const_fibre_n`.
        let app_pair = crate::ext::app_of_pair(&mut env, &ap).expect("TG prelude: application at a pair");
        let fs_app_mem = crate::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair)
            .expect("TG prelude: a function's values lie in its codomain");
        let fs_retarget = crate::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair)
            .expect("TG prelude: the codomain may be retargeted");
        // One extra of each, purely to read the counters back out.
        let n_syms = env.declare(0).id() + 1;
        let n_vars = env.fresh_var().id() + 1;
        let p = Rc::new(Prelude {
            tower,
            ap,
            u_sym,
            mem_u,
            lu_ax,
            pow,
            pow_ax,
            prod,
            fs,
            fs_in_u,
            fs_cong,
            fs_app_mem,
            fs_retarget,
            u0_in_u1,
            fs_u0_in_u1,
            n_syms,
            n_vars,
        });
        *slot.borrow_mut() = Some(p.clone());
        p
    })
}

/// Advance a fresh `Env` past every id the prelude used.
///
/// This is what makes replaying [`prelude`] sound: an `Env` is only a pair of
/// counters, so the single thing that must not happen is a fresh `Env`
/// re-issuing a symbol or variable the prelude already holds a theorem about.
pub fn fast_forward(env: &mut Env, p: &Prelude) {
    for _ in 0..p.n_syms {
        env.declare(0);
    }
    for _ in 0..p.n_vars {
        env.fresh_var();
    }
}
