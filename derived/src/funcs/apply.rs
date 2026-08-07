//! Application: `app(f,a) = ⋃ coll(f,a)`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀f ∀a ∀w. (w ∈ app(f,a) ↔ ∃y. (⟨a,y⟩ ∈ f ∧ w ∈ y))   [app_members]
//! ⊢ ∀f ∀a. ((¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅)             [app_off_domain]
//! ```
//!
//! Both **unconditional**. [`Apply`] is the whole apparatus — pairing, union,
//! `∅`, `coll` and `app` with every characteristic theorem — assembled once;
//! [`Apply::with_sets`] is the entry point when a [`crate::funcs::Sets`] already
//! exists, and it must be used rather than building a second one, because each
//! piece is a *definitional extension* and building it twice would introduce two
//! different symbols whose theorems do not compose.
//!
//! Callers need neither derivation. [`app_members`] unfolds membership through
//! the Union axiom and then through `Apply::coll_members`; the inhabitation
//! antecedent it used to carry was inherited from `coll`, which no longer has
//! one.
//!
//! [`app_off_domain`] was **previously unstatable**: `app(f,a)` returned
//! whatever [`crate::funcs::collection`]'s default happened to give, and there
//! was no `∅` to compare it against anyway. Both obstacles are gone, and the
//! argument is short — off the domain nothing is collected, so `coll(f,a)` has
//! no members; a union over a set with no members has no members either; and `∅`
//! has no members, so Extensionality closes it. It is the complement of the
//! membership antecedent [`crate::funcs::beta_conditional`] carries.
//!
//! # How this fails
//!
//! **Nothing here declines.** Neither derivation takes a theorem of its own:
//! both are handed an [`Apply`], whose theorems this file built, so every guard
//! they could want is already a comparison against work done here — which is
//! what the `debug_assert_eq!`s are. What a caller can see is therefore either a
//! refusal from [`crate::rules`] underneath (an [`crate::rules::inst_all`]
//! decline when one of the apparatus' theorems has fewer leading quantifiers
//! than the terms fed to it, a [`crate::rules::syl`] or
//! [`crate::rules::hyp_syl`] decline when two implications do not compose) or an
//! [`crate::err::DerErr::Assembly`] from [`crate::prim`].
//!
//! [`Apply::with_sets`] is the exception, and only in the bookkeeping sense: it
//! reaches two constructions that still return `Option`,
//! `crate::pairs::opair_snd` and `crate::pairs::opair_inj`, whose reasons were
//! discarded at that boundary, so it reports them through
//! [`crate::err::imported`] — an assembly failure naming the construction to
//! migrate next. `crate::empty::empty` is infallible and needs no such wrapper.
//!
//! Nothing in this file is `#[track_caller]`. [`Apply::with_sets`] is a dozen
//! constructions in sequence and the two theorems below are derivations; for all
//! three, *which* internal step stopped is precisely what a reader needs, and
//! moving the site to the caller would throw it away.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::err::{imported, DResult};
use crate::prim;
use crate::rules::{
    com12, contrapos, define_abbrev, eq_symm, exists_elim_imp, exists_intro_imp, exists_mono,
    hyp_and, hyp_syl, iff_mp, iff_mpr, inst_all, mem_singleton, opair_fst, singleton_inj, syl,
    union_singleton,
};
use crate::{a1i, and_intro, and_left, and_right, gen_all};
use super::sets::{snd_in_union2, Sets};
use super::coll::{collection, collection_conditional, value_collection};

/// The whole application apparatus: the symbols and the characteristic
/// theorems every rule below consumes.
///
/// Assembling it once and passing it around is not just convenience — each
/// piece is a *definitional extension*, so building it twice would introduce
/// two different symbols and the theorems would not compose.
#[derive(Clone)]
pub struct Apply {
    /// Pairing and union.
    pub sets: Sets,
    /// `∅`, with no members; see [`crate::empty::empty`].
    pub empty: FnSym,
    /// `⊢ ∀z. ¬(z ∈ ∅)`.
    pub empty_ax: Thm,
    /// `coll(f,a) = { y : ⟨a,y⟩ ∈ f }`; see [`collection`].
    pub coll: FnSym,
    /// `⊢ ∀f ∀a ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f)` — **unconditional**.
    pub coll_members: Thm,
    /// `⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f))` — the
    /// weakening of [`Apply::coll_members`] that the beta derivations match on.
    pub coll_ax: Thm,
    /// `app(f,a) = ⋃ coll(f,a)`.
    pub app: FnSym,
    /// `⊢ ∀f ∀a. app(f,a) = ⋃ coll(f,a)`.
    pub app_ax: Thm,
    /// `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)`.
    pub mem_sing: Thm,
    /// `⊢ ∀c. ⋃{c} = c`.
    pub union_sing: Thm,
    /// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → (a = c ∧ b = d))`.
    pub pair_inj: Thm,
}

impl Apply {
    /// Introduce every symbol and derive every theorem, from the axioms up.
    ///
    /// Mints a fresh [`Sets`]. When the pairing has to be *shared* with a
    /// [`crate::funspace::Space`] — which is the normal case, because the `Π`
    /// bridge mentions both `app` and `fs` — build the `Apply` first and hand
    /// it to [`crate::funspace::Space::with_apply`], or start from an existing
    /// `Sets` with [`Apply::with_sets`].
    pub fn new(env: &mut Env) -> DResult<Apply> {
        let sets = Sets::new(env);
        Apply::with_sets(env, sets)
    }

    /// The same, over a **caller-supplied** [`Sets`].
    ///
    /// Every ordered pair in the resulting `Apply` is built from `sets.up`, so
    /// a client that already has a pairing operation gets an application
    /// apparatus whose terms compose with everything else built over it. That
    /// is the whole difference between this and [`Apply::new`]: two `Sets` are
    /// two unrelated definitional extensions, and a theorem about one says
    /// nothing about the other.
    pub fn with_sets(env: &mut Env, sets: Sets) -> DResult<Apply> {
        let mem_sing = mem_singleton(env, sets.up, &sets.up_ax)?;
        let sing_inj = singleton_inj(env, sets.up, &mem_sing)?;
        let fst = opair_fst(env, sets.up, &sets.up_ax, &mem_sing, &sing_inj)?;
        let snd = imported(
            "crate::pairs::opair_snd",
            crate::pairs::opair_snd(env, sets.up, &sets.up_ax, &mem_sing, &fst),
        )?;
        let pair_inj =
            imported("crate::pairs::opair_inj", crate::pairs::opair_inj(env, sets.up, &fst, &snd))?;
        let union_sing = union_singleton(env, sets.up, &sets.up_ax, sets.un, &sets.un_ax)?;

        let (empty, empty_ax) = crate::empty::empty(env);
        let sni = snd_in_union2(env, &sets)?;
        let vc = value_collection(env, &sets, &sni, &empty_ax)?;
        let (coll, coll_members) = collection(env, &sets, &vc)?;
        let coll_ax = collection_conditional(env, &sets, coll, &coll_members)?;

        // `app` is an *explicit* definition, so it costs nothing: the work all
        // sits in `coll`, and stripping the outer union is a term composition.
        let (f, a) = (env.fresh_var(), env.fresh_var());
        let body = sets.union_of(Term::apply(coll, vec![Term::var(f), Term::var(a)]));
        let (app, app_ax) = define_abbrev(env, &[f, a], &body)?;

        Ok(Apply {
            sets,
            empty,
            empty_ax,
            coll,
            coll_members,
            coll_ax,
            app,
            app_ax,
            mem_sing,
            union_sing,
            pair_inj,
        })
    }

    /// The term `app(f, a)`.
    pub fn apply(&self, f: Term, a: Term) -> Term { Term::apply(self.app, vec![f, a]) }

    /// The term `coll(f, a)`.
    pub fn coll_of(&self, f: Term, a: Term) -> Term { Term::apply(self.coll, vec![f, a]) }
}

/// `⊢ ∀f ∀a ∀w. (w ∈ app(f,a) ↔ ∃y. (⟨a,y⟩ ∈ f ∧ w ∈ y))` — the characteristic
/// property of application, **unconditional**.
///
/// `app(f,a)` is `⋃ coll(f,a)`, so membership unfolds through the Union axiom
/// and then through [`Apply::coll_members`]. The inhabitation antecedent this
/// used to carry was inherited from `coll`, and `coll` no longer has one, so
/// all that is left is swapping `y ∈ coll(f,a)` for `⟨a,y⟩ ∈ f` under the
/// existential — one [`crate::rules::exists_mono`] in each direction.
pub fn app_members(env: &mut Env, ap: &Apply) -> DResult<Thm> {
    let (f, a, w, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tw, ty) = (Term::var(f), Term::var(a), Term::var(w), Term::var(y));

    let coll_term = ap.coll_of(tf.clone(), ta.clone());
    let app_term = ap.apply(tf.clone(), ta.clone());
    let ucoll = ap.sets.union_of(coll_term.clone());

    let l = Formula::mem(ap.sets.pair(ta.clone(), ty.clone()), tf.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let mem_wy = Formula::mem(tw.clone(), ty.clone());
    let src = Formula::and(mem_yc.clone(), mem_wy.clone());
    let tgt = Formula::and(l.clone(), mem_wy.clone());

    // `w ∈ app(f,a) ↔ w ∈ ⋃coll(f,a)`, by Leibniz on the defining equation.
    let app_def = inst_all(&ap.app_ax, &[tf.clone(), ta.clone()])?;
    let (v1, v2) = (env.fresh_var(), env.fresh_var());
    let a2u = prim::mp(
        &Thm::eq_leibniz(app_term.clone(), ucoll.clone(), v1, Formula::mem(tw.clone(), Term::var(v1))),
        &app_def,
    )?;
    let u2a = prim::mp(
        &Thm::eq_leibniz(ucoll.clone(), app_term.clone(), v2, Formula::mem(tw.clone(), Term::var(v2))),
        &eq_symm(env, &app_def)?,
    )?;
    let un_inst = inst_all(&ap.sets.un_ax, &[coll_term, tw.clone()])?;
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(tw.clone(), ucoll), Formula::exists(y, src.clone())),
        "app_members: the Union axiom has an unexpected shape"
    );
    let coll_at = inst_all(&ap.coll_members, &[tf, ta, ty.clone()])?;
    debug_assert_eq!(
        *coll_at.concl(),
        Formula::iff(mem_yc.clone(), l.clone()),
        "app_members: the collection's characteristic theorem has an unexpected shape"
    );

    // Swap `y ∈ coll` for `⟨a,y⟩ ∈ f` under the existential, both ways.
    let src_tgt = hyp_and(
        &syl(&and_left(mem_yc.clone(), mem_wy.clone()), &iff_mp(&coll_at)?)?,
        &and_right(mem_yc.clone(), mem_wy.clone()),
    )?;
    let tgt_src = hyp_and(
        &syl(&and_left(l.clone(), mem_wy.clone()), &iff_mpr(&coll_at)?)?,
        &and_right(l, mem_wy),
    )?;
    let fwd_ex = exists_mono(y, &Thm::gen(y, &src_tgt))?;
    let bwd_ex = exists_mono(y, &Thm::gen(y, &tgt_src))?;

    let fwd = syl(&syl(&a2u, &iff_mp(&un_inst)?)?, &fwd_ex)?;
    let bwd = syl(&bwd_ex, &syl(&iff_mpr(&un_inst)?, &u2a)?)?;
    let out = and_intro(&fwd, &bwd);
    debug_assert_eq!(
        *out.concl(),
        Formula::iff(Formula::mem(tw, app_term), Formula::exists(y, tgt)),
        "app_members: unexpected shape"
    );
    Ok(gen_all(&[f, a, w], &out))
}

/// `⊢ ∀f ∀a. ((¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅)` — application off the domain.
///
/// Previously unstatable: `app(f,a)` returned whatever [`collection`]'s default
/// happened to give, and there was no `∅` to compare it against anyway. Both
/// obstacles are gone, and the argument is short. Off the domain nothing is
/// collected, so `coll(f,a)` has no members; a union over a set with no members
/// has no members either; and `∅` has no members. Extensionality closes it.
///
/// This is the companion to [`crate::funcs::beta_conditional`], whose membership antecedent
/// is exactly what this covers the complement of.
pub fn app_off_domain(env: &mut Env, ap: &Apply) -> DResult<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (f, a, w, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tw, ty) = (Term::var(f), Term::var(a), Term::var(w), Term::var(y));

    let coll_term = ap.coll_of(tf.clone(), ta.clone());
    let app_term = ap.apply(tf.clone(), ta.clone());
    let ucoll = ap.sets.union_of(coll_term.clone());
    let emp = Term::apply(ap.empty, vec![]);

    let l = Formula::mem(ap.sets.pair(ta.clone(), ty.clone()), tf.clone());
    let h = Formula::not(Formula::exists(y, l.clone())); // ¬∃y. ⟨a,y⟩ ∈ f

    // ── H → ¬(y ∈ coll(f,a)) ─────────────────────────────────────────────────
    // `⊢ ⟨a,y⟩ ∈ f → ∃y. ⟨a,y⟩ ∈ f` contraposes to `⊢ H → ¬(⟨a,y⟩ ∈ f)`, and
    // the collection's characteristic theorem — unconditional, which is the
    // whole point — carries that back to membership in `coll(f,a)`.
    let h_not_l = contrapos(&exists_intro_imp(y, l.clone(), ty.clone())?)?;
    let coll_at = inst_all(&ap.coll_members, &[tf.clone(), ta.clone(), ty.clone()])?;
    debug_assert_eq!(
        *coll_at.concl(),
        Formula::iff(Formula::mem(ty.clone(), coll_term.clone()), l),
        "app_off_domain: the collection's characteristic theorem has an unexpected shape"
    );
    let h_not_yc = hyp_syl(&a1i(&iff_mp(&coll_at)?, h.clone()), &h_not_l)?;

    // ── H → ¬(w ∈ ⋃coll(f,a)) ────────────────────────────────────────────────
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let mem_wy = Formula::mem(tw.clone(), ty.clone());
    let body = Formula::and(mem_yc.clone(), mem_wy.clone());
    let h_body_false = hyp_syl(&a1i(&and_left(mem_yc, mem_wy), h.clone()), &h_not_yc)?;
    // Discharge the witness; `y` is bound in `H`, so `¬H` is a legal target.
    let h_ex_false = com12(&exists_elim_imp(
        y,
        &Thm::gen(y, &com12(&h_body_false)?),
        &Formula::not(h.clone()),
    )?)?;

    let un_inst = inst_all(&ap.sets.un_ax, &[coll_term, tw.clone()])?;
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(tw.clone(), ucoll.clone()), Formula::exists(y, body)),
        "app_off_domain: the Union axiom has an unexpected shape"
    );
    let h_not_ucoll = hyp_syl(&a1i(&iff_mp(&un_inst)?, h.clone()), &h_ex_false)?;

    // ── H → ¬(w ∈ app(f,a)), across the defining equation ────────────────────
    let app_def = inst_all(&ap.app_ax, &[tf, ta])?;
    let v = env.fresh_var();
    let a2u = prim::mp(
        &Thm::eq_leibniz(app_term.clone(), ucoll, v, Formula::mem(tw.clone(), Term::var(v))),
        &app_def,
    )?;
    let h_not_app = hyp_syl(&a1i(&a2u, h.clone()), &h_not_ucoll)?;

    // ── Both sides are refutable, so they have the same members ──────────────
    let mem_app = Formula::mem(tw.clone(), app_term.clone());
    let mem_e = Formula::mem(tw.clone(), emp.clone());
    let h_fwd = crate::separation::hyp_ex_falso(&h_not_app, mem_e.clone())?;
    let not_e = inst_all(&ap.empty_ax, std::slice::from_ref(&tw))?;
    let h_bwd = crate::separation::hyp_ex_falso(&a1i(&not_e, h.clone()), mem_app.clone())?;

    let h_all = prim::mp(
        &prim::ax_dist(w, h.clone(), Formula::iff(mem_app, mem_e))?,
        &Thm::gen(w, &hyp_and(&h_fwd, &h_bwd)?),
    )?;
    let out = syl(&h_all, &inst_all(&ext, &[app_term.clone(), emp.clone()])?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(app_term, emp)),
        "app_off_domain: unexpected shape"
    );
    Ok(gen_all(&[f, a], &out))
}
