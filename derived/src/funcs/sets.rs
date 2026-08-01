//! [`Sets`]: pairing and union bundled, with the two lemmas everything about
//! `app` starts from.
//!
//! # Interface
//!
//! [`Sets`] carries `upair` and `union` with their characteristic theorems:
//!
//! ```text
//! ⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))
//! ⊢ ∀x ∀z. (z ∈ union(x) ↔ ∃y. (y ∈ x ∧ z ∈ y))
//! ```
//!
//! and the two derived lemmas are
//!
//! ```text
//! ⊢ (v ∈ s ∧ u ∈ v) → u ∈ ⋃s         [union_intro]
//! ⊢ ∀f ∀a ∀y. (⟨a,y⟩ ∈ f → y ∈ ⋃⋃f)  [snd_in_union2]
//! ```
//!
//! [`union_intro`] is the backward half of the Union axiom with the existential
//! already witnessed — supplying `v` for `y` is all that separates the axiom
//! from the form every use actually wants. [`snd_in_union2`] is the superset
//! lemma that makes `{ y : ⟨a,y⟩ ∈ f }` a legitimate instance of Separation: two
//! applications of [`union_intro`] along `y ∈ {a,y} ∈ ⟨a,y⟩ ∈ f`.
//!
//! # Clone, deliberately
//!
//! A [`Sets`] is a pair of symbols plus two theorems about them, so copying it
//! copies *the same* definitional extension — unlike calling [`Sets::new`]
//! twice, which mints two unrelated pairing operations whose terms do not
//! compose. Sharing is what [`crate::funcs::Apply::with_sets`] and
//! [`crate::funspace::Space::with_apply`] exist for; `Clone` is what lets them
//! hand the one `Sets` on.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, exists_intro_imp, gen_all, hyp_and, iff_mpr, imp_refl, inst_all, opair, singleton, syl,
    upair_members,
};

/// The pairing and union symbols with their characteristic theorems.
///
/// Bundled rather than passed one at a time: every lemma below needs all four,
/// and threading them individually makes the signatures unreadable.
///
/// **Clone, deliberately.** A `Sets` is a pair of symbols plus two theorems
/// about them, so copying it copies *the same* definitional extension —
/// unlike calling [`Sets::new`] twice, which mints two unrelated pairing
/// operations whose terms do not compose. Sharing is what
/// [`crate::funcs::Apply::with_sets`] and [`crate::funspace::Space::with_apply`] exist for;
/// `Clone` is what lets them hand the one `Sets` on.
#[derive(Clone)]
pub struct Sets {
    /// `upair`, with `⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))`.
    pub up: FnSym,
    /// The characteristic theorem of [`Sets::up`].
    pub up_ax: Thm,
    /// `union`, with `⊢ ∀x ∀z. (z ∈ union(x) ↔ ∃y. (y ∈ x ∧ z ∈ y))`.
    pub un: FnSym,
    /// The characteristic theorem of [`Sets::un`].
    pub un_ax: Thm,
}

impl Sets {
    /// Introduce both symbols and prove their characteristic theorems.
    pub fn new(env: &mut Env) -> Sets {
        let (up, up_ax) = crate::upair(env);
        let (un, un_ax) = crate::union(env);
        Sets { up, up_ax, un, un_ax }
    }

    /// The term `⋃s`.
    pub fn union_of(&self, s: Term) -> Term { Term::apply(self.un, vec![s]) }

    /// The term `⟨a, b⟩`.
    pub fn pair(&self, a: Term, b: Term) -> Term { opair(self.up, a, b) }
}

/// `⊢ (v ∈ s ∧ u ∈ v) → u ∈ ⋃s` — the backward half of the Union axiom, with
/// the existential already witnessed.
///
/// The union axiom characterises `u ∈ ⋃s` as `∃y. (y ∈ s ∧ u ∈ y)`; supplying
/// `v` for `y` is all that separates it from the form every use actually wants.
pub fn union_intro(env: &mut Env, sets: &Sets, s: Term, v: Term, u: Term) -> Option<Thm> {
    let un_inst = inst_all(&sets.un_ax, &[s.clone(), u.clone()])?;
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let body = Formula::and(Formula::mem(ty.clone(), s.clone()), Formula::mem(u.clone(), ty));
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(u.clone(), sets.union_of(s.clone())), Formula::exists(yv, body.clone())),
        "union_intro: the Union axiom has an unexpected shape"
    );
    let intro = exists_intro_imp(yv, body, v)?;
    syl(&intro, &iff_mpr(&un_inst)?)
}

/// `⊢ ∀f ∀a ∀y. (⟨a,y⟩ ∈ f → y ∈ ⋃⋃f)`.
///
/// The superset lemma that makes `{ y : ⟨a,y⟩ ∈ f }` a legitimate instance of
/// Separation. Two applications of [`union_intro`] along the chain
/// `y ∈ {a,y} ∈ ⟨a,y⟩ ∈ f`: the middle set is a member of the pair, which is a
/// member of `f`, so it is in `⋃f`, and `y` is in it, so `y` is in `⋃⋃f`.
pub fn snd_in_union2(env: &mut Env, sets: &Sets) -> Option<Thm> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));

    let ay = Term::apply(sets.up, vec![ta.clone(), ty.clone()]); // {a,y}
    let pair = sets.pair(ta.clone(), ty.clone()); // ⟨a,y⟩ = {{a},{a,y}}
    let uf = sets.union_of(tf.clone()); // ⋃f
    let uuf = sets.union_of(uf.clone()); // ⋃⋃f

    let h = Formula::mem(pair.clone(), tf.clone());

    // ⊢ {a,y} ∈ ⟨a,y⟩ and ⊢ y ∈ {a,y}, both from the Pairing characterisation.
    let (_, ay_in_pair) = upair_members(&sets.up_ax, &singleton(sets.up, ta.clone()), &ay)?;
    let (_, y_in_ay) = upair_members(&sets.up_ax, &ta, &ty)?;

    // ⊢ H → {a,y} ∈ ⋃f
    let step1 = union_intro(env, sets, tf.clone(), pair, ay.clone())?;
    let h_ay_in_uf = syl(&hyp_and(&imp_refl(h.clone()), &a1i(&ay_in_pair, h.clone()))?, &step1)?;

    // ⊢ H → y ∈ ⋃⋃f
    let step2 = union_intro(env, sets, uf, ay, ty.clone())?;
    let out = syl(&hyp_and(&h_ay_in_uf, &a1i(&y_in_ay, h.clone()))?, &step2)?;

    debug_assert_eq!(*out.concl(), Formula::imp(h, Formula::mem(ty, uuf)), "snd_in_union2: unexpected shape");
    Some(gen_all(&[f, a, y], &out))
}
