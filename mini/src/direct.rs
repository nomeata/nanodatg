//! **`Eq`'s interpretation clause** — the one declaration whose denotation is
//! *named* rather than translated (`INDEXED-DESIGN.md` §2.2, Carneiro §6.2).
//!
//! # Interface
//!
//! ```text
//! direct::clause_for(name)                -> Option<Clause>
//! direct::build(checker, clause, name, σ) -> Result<(), Gap>
//! direct::Direct::build(env, sums)        -> Option<Direct>   (the apparatus)
//! ```
//!
//! [`build`] is called from [`crate::zoneb::build`] **before** the eliminator
//! trichotomy, on the declaration [`clause_for`] names, and it stores `⟦T.{σ}⟧`
//! and `⟦T.ctor.{σ}⟧` exactly as the general path does — the same
//! [`Checker::lam_nest`](crate::kernel::Checker::lam_nest), the same store, the
//! same `Gap` vocabulary.
//!
//! # Why `Eq` is interpreted and not translated
//!
//! Carneiro's §5.3 gives a class-(S) declaration the carrier
//!
//! ```text
//! ⟦T p⃗ x⃗⟧ = [ tup(x⃗) ∈ acc(A_φ(p⃗), R(p⃗)) ]
//! ```
//!
//! and for a **non-recursive** declaration `R` is provably empty, so `acc` is
//! the identity and the carrier collapses to a single conditional singleton
//! `[φ]` over the constructors' field existentials. `Eq`'s collapse has a closed
//! form:
//!
//! | declaration | class | §5.3's `[φ]` collapses to | as a term |
//! |---|---|---|---|
//! | `Eq.{u} {α} (a : α) : α → Prop` | (S) | `[ b ∈ ⟦α⟧ ∧ b = a ]` | `eq_set(a,b) = [a = b]` |
//!
//! **and that is not why the row is here.** `Eq` is a member of Carneiro's
//! eight-item menagerie and §6.2 gives it its own interpretation clause —
//! `⟦a = b⟧ = [⟦a⟧ = ⟦b⟧]`, `⟦refl a⟧ = •`, `⟦rec₌ e b h⟧ = ⟦e⟧` (all three are
//! implemented, the last in [`crate::recursor`]). Interpreting it directly is
//! following the thesis, not shortcutting it, and the same will hold of `Acc`
//! when its clause (`derived::rec_acc::pack`) is wired.
//!
//! # The table had three rows and now has one
//!
//! `And` and `PUnit` were the other two, with closed forms `and_set(a,b)` and
//! `1` and a **delete-by** attached: they are ordinary declarations — a
//! two-field `Prop` structure and a one-constructor subsingleton — that happen
//! to collapse the same way, and nothing distinguished them from
//! `ProjDataIndex` and `True`, which no closed form covered. The condition was
//! that `derived` grow the general non-indexed class-(S) carrier, and it did
//! (`IndexSpace::build` at `ni = 0`, then
//! [`LeProp`](derived::inductive::family::LeProp)). Both rows are gone and both
//! declarations now go through [`crate::class_s`], which is where the general
//! clause and its reasoning live.
//!
//! The table takes **no fourth row**, and this is the standing rule rather than
//! a note about the past: a declaration that seems to want one is evidence that
//! the general clause is missing a case, and belongs in the ledger as a gap
//! naming that construction. `Eq` is not a fourth row because it is not a
//! collapse that happens to be convenient — it is §6.2's own clause, and it is
//! indexed, which the general route is not.
//!
//! # Keyed by name, verified by derivation
//!
//! [`clause_for`] is a table on the declaration's **name**, which is one hash
//! comparison on the name `ensure` was asked about — the same key the store is
//! keyed on, so MINI-DESIGN.md §0's claim is untouched: nothing is looked up by
//! shape and nothing is tried and retried.
//!
//! A name is not evidence, though, and this module never treats it as such.
//! The clause states its bottom against the type the **export** gives:
//!
//! * the type former's bottom must conclude `⊢ ⟦T⟧ ∈ ⟦Sort ℓ⟧` at the
//!   declaration's own resultant sort, which is read off, not assumed;
//! * a constructor's bottom must conclude `⊢ ⟦T.ctor⟧ ∈ ⟦its declared
//!   codomain⟧`, and that codomain is decomposed, its arguments *inferred*, and
//!   the type former's nest beta-reduced at those arguments by
//!   [`Interp::beta_spine`](crate::interp::Interp::beta_spine).
//!
//! So a declaration that is called `Eq` and is not Lean's `Eq` produces a
//! membership in the wrong set, the final shape check refuses it, and the
//! declaration is **declined with a reason** rather than given an interpretation
//! that a use site would then silently trust. That is the same discipline the
//! general paths apply at [`crate::zoneb::ctor_bottom`] and
//! [`crate::class_s`], and it is the reason the shape checks here are
//! deliberately thin: the derivation is the check.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::prop::{cond_intro, conditional_singleton};
use derived::sums::Sums;
use derived::{gen_all, inst_all};

use crate::env::ConstantInfo;
use crate::ev::{Ev, Gap};
use crate::expr::{Expr, Level, Name, E};
use crate::ground;
use crate::interp::Interp;
use crate::kernel::{Checker, Typing, R};

/// The symbol the direct clause denotes with, over **the prelude's own**
/// [`Sums`] so that its `1` and `•` are the ones every other clause speaks of.
///
/// This is [`derived::prop::Props`] restricted to what the clause needs.
/// `Props::new` mints a *fresh* `Sums`, hence a second `1`, so it cannot be the
/// thing an interpretation store already committed to a unit set uses; the
/// construction below is the same one its constructor performs, at the unit
/// set this `Interp` already has.
pub struct Direct {
    /// `eq_set(a,b) = [a = b]`.
    pub eq: FnSym,
    /// `⊢ ∀a ∀b ∀z. (z ∈ eq_set(a,b) ↔ (z ∈ 1 ∧ a = b))`.
    pub eq_ax: Thm,
    /// `⊢ ∀a. • ∈ eq_set(a,a)` — the typing of `Eq.refl`.
    pub eq_refl: Thm,
}

impl Direct {
    /// Introduce the conditional singleton and derive reflexivity's typing.
    pub fn build(env: &mut Env, sums: &Sums) -> Option<Direct> {
        let (a, b) = (env.fresh_var(), env.fresh_var());
        let (ta, tb) = (Term::var(a), Term::var(b));
        let (eq, eq_ax) = conditional_singleton(env, sums, &[a, b], &Formula::eq(ta.clone(), tb))?;
        // Reflexivity is the same introduction rule at `b := a`, where the
        // condition is a theorem rather than a hypothesis.
        let refl_phi = Formula::eq(ta.clone(), ta.clone());
        let c_aa = Term::apply(eq, vec![ta.clone(), ta.clone()]);
        let chi_aa = inst_all(&eq_ax, &[ta.clone(), ta.clone()])?;
        let intro = cond_intro(sums, &refl_phi, &c_aa, &chi_aa)?;
        let eq_refl = gen_all(&[a], &Thm::mp(&intro, &Thm::eq_refl(ta))?);

        Some(Direct { eq, eq_ax, eq_refl })
    }
}

/// Why `⟦Acc.intro⟧`'s *typing* is not yet derived — see [`ctor_bottom`]'s
/// `Clause::Acc` arm, which states the transport that is missing.
pub const ACC_INTRO: &str = "acc: Acc.intro's step hypothesis is not transported to preds_in";

/// Which direct clause a declaration takes, if any.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Clause {
    /// `Eq.{u} {α : Sort u} (a : α) : α → Prop`.
    Eq,
    /// `Acc.{u} {α : Sort u} (r : α → α → Prop) : α → Prop`.
    ///
    /// The second member of §6.2's menagerie to be wired, and the one the
    /// module header above predicted. It is **not** a fourth row of the
    /// retired closed-form table: `⟦Acc α r x⟧ = [x̄ ∈ acc(⟦α⟧,R̄)]` is
    /// thesis.txt:2126's own clause, `acc` is a construction the general
    /// class-(S) route does not have, and the general route cannot reach it
    /// anyway — `Acc.intro`'s recursive field is function-typed, which is the
    /// `Gap::FunTypedRecArg` the corpus rows wait on.
    Acc,
}

impl Clause {
    /// `(num_params, num_indices, number of constructors)`, as the export must
    /// state them. Checked before anything is built, so a same-named
    /// declaration of a different shape is declined rather than half-built.
    fn arity(self) -> (u32, u32, usize) {
        match self {
            Clause::Eq => (2, 1, 1),
            // `α` and `r` are the parameters, the subject is the index, and
            // `Acc.intro` is the one constructor — the same three numbers as
            // `Eq`, at a different declaration.
            Clause::Acc => (2, 1, 1),
        }
    }
}

/// The table. One comparison on the name [`crate::zoneb::ensure`] was asked
/// about — never a scan, and never a shape match.
pub fn clause_for(n: &Name) -> Option<Clause> {
    let Name::Str(pre, s) = n else { return None };
    if **pre != Name::Anon {
        return None
    }
    match &**s {
        "Eq" => Some(Clause::Eq),
        "Acc" => Some(Clause::Acc),
        _ => None,
    }
}

/// `⟦T.{σ}⟧` and `⟦T.ctor.{σ}⟧` for one direct declaration.
///
/// The shape of the walk is [`crate::zoneb::build`]'s: the declaration's own
/// data, the type former as a `np + ni`-deep λ-nest, then one nest per
/// constructor. What differs is only the bottom of each nest.
pub fn build(c: &mut Checker<'_, '_>, cl: Clause, name: &Name, inst: &[u32]) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(name.clone(), w);
    let env = c.environment();
    let Some(ConstantInfo::Inductive { lparams, ty, num_params, num_indices, ctors, .. }) =
        env.get(name)
    else {
        return Err(Gap::NoInterpretation(name.clone(), inst.to_vec()))
    };
    let (np, ni, nc) = cl.arity();
    if (*num_params, *num_indices, ctors.len()) != (np, ni, nc) {
        return Err(bad("direct clause: declaration shape"))
    }
    if inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(name.clone(), inst.to_vec()))
    }
    let depth = (np + ni) as usize;
    let lean_ty = ground::subst_ground(ty, lparams, inst);
    // The resultant sort, as a ground numeral: the universe the former's
    // bottom must land in, read off the declaration rather than assumed.
    let own = crate::zoneb::peel(&lean_ty, depth).ok_or_else(|| bad("type shape"))?;
    let Expr::Sort(l) = &*own else { return Err(bad("resultant sort")) };
    let level = ground::eval(l, &Default::default()).ok_or_else(|| bad("level"))?;
    let ctor_tys: Vec<(Name, E)> = ctors
        .iter()
        .map(|n| {
            env.get(n)
                .map(|ci| (n.clone(), ground::subst_ground(ci.ty(), lparams, inst)))
                .ok_or_else(|| bad("ctor type"))
        })
        .collect::<Result<_, _>>()?;

    // ── the type former ───────────────────────────────────────────────────
    let nm = name.clone();
    let mut bottom =
        move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(former_bottom(c, cl, &nm, depth, level)) };
    let t = c.lam_nest(&lean_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, name, inst, t)?;

    // ── the constructors ──────────────────────────────────────────────────
    for (cname, cty) in &ctor_tys {
        let cdepth = arity_of(cty);
        let codomain = crate::zoneb::peel(cty, cdepth).ok_or_else(|| bad("ctor arity"))?;
        let site = CtorSite {
            ind: name.clone(),
            inst: inst.to_vec(),
            clause: cl,
            codomain,
        };
        let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
        let t = c.lam_nest(cty, cdepth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
        crate::zoneb::store(c, cname, inst, t)?;
    }
    Ok(())
}

/// How many `Π` binders a constructor's type has. All of them: a direct
/// clause's constructors take their parameters and their fields and nothing
/// else, and the codomain check below is what confirms it.
fn arity_of(ty: &E) -> usize {
    let mut n = 0;
    let mut cur = ty.clone();
    while let Expr::Forall { body, .. } = &*cur.clone() {
        n += 1;
        cur = body.clone();
    }
    n
}

/// The bottom of the type former's nest: the denoting term, and its membership
/// in `⟦Sort ℓ⟧` at the declaration's **own** resultant level.
fn former_bottom(
    c: &mut Checker<'_, '_>,
    cl: Clause,
    name: &Name,
    depth: usize,
    level: u32,
) -> Typing {
    let ty = crate::expr::sort(level_of(level));
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let Some((xs, _)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
    let tower = ip.prelude.tower.clone();

    // The term, and the formula it is the conditional singleton of.
    let (term, phi, chi) = match cl {
        // `⟦Eq α a b⟧ = eq_set(⟦a⟧, ⟦b⟧)`: the parameters are `α` and `a`, and
        // the single index is `b`, so the *first* binder is dropped and the
        // other two are the equation's sides, in that order.
        Clause::Eq => {
            let (a, b) = (xs[1].clone(), xs[2].clone());
            let t = ip.mk(d.eq, vec![a.clone(), b.clone()]);
            let phi = Formula::eq(a.clone(), b.clone());
            let Some(chi) = inst_all(&d.eq_ax, &[a, b]) else {
                return gap(Gap::IndSpec(name.clone(), "eq instance"))
            };
            (t, phi, chi)
        }
        // `⟦Acc α r x⟧ = acc_set(⟦α⟧,⟦r⟧,x̄) = [x̄ ∈ acc(⟦α⟧, rel_graph(⟦α⟧,⟦r⟧))]`
        // — thesis.txt:2126, with the graph bridge the thesis's notation hides.
        // The parameters are `α` and `r` and the single index is the subject,
        // so all three binders are consumed, in order. See [`crate::acc`].
        Clause::Acc => {
            let (a, r, x) = (xs[0].clone(), xs[1].clone(), xs[2].clone());
            let Some(ac) = ip.acc() else { return gap(Gap::IndApparatus) };
            let t = ip.mk(ac.acc_set, vec![a.clone(), r.clone(), x.clone()]);
            let phi = ac.phi(&a, &r, &x);
            let Some(chi) = inst_all(&ac.acc_set_ax, &[a, r, x]) else {
                return gap(Gap::IndSpec(name.clone(), "acc instance"))
            };
            (t, phi, chi)
        }
    };

    // `⊢ term ∈ U₀`, then raised to the declaration's own level. `[φ] ∈ U₀` is a
    // closed theorem of the tower; the raise is the cumulativity table, and it
    // is what would make a `Sort u`-valued clause land in `⟦Sort u⟧` rather
    // than only in `⟦Prop⟧`.
    let in_u0 = tower.cond_in_u0(&mut ip.env, &phi, &term, &chi);
    let Some(in_u0) = in_u0 else { return gap(Gap::IndSpec(name.clone(), "denotation typing")) };
    let raised = if level == 0 {
        Some(in_u0)
    } else {
        ip.raise_in_gamma(0, level as usize, &in_u0)
    };
    match raised {
        Some(t) if *t.concl() == Formula::mem(term.clone(), ip.sort(level)) => {
            Typing { ty, tm: Some(term), ev: Ev::Proved(t) }
        }
        _ => gap(Gap::IndUniverseHeight(name.clone(), level)),
    }
}

/// `Sort ℓ` at a ground numeral.
fn level_of(n: u32) -> Level {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = l.succ();
    }
    l
}

/// One direct constructor: which declaration, which clause, and the codomain
/// read off its Lean type.
struct CtorSite {
    ind: Name,
    inst: Vec<u32>,
    clause: Clause,
    codomain: E,
}

/// The bottom of a direct constructor's nest.
///
/// **A direct constructor's interpretation is `•`**, because the declaration
/// denotes a subset of `1`; what the clause supplies is the derivation that puts
/// `•` in the right one. The codomain is decomposed and its arguments are
/// *inferred* — not assumed to be the binders in order — so the membership is
/// established about the set the export says the constructor lands in.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { ind, inst, clause, codomain } = site;
    let ty = codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    // The codomain must be this declaration, applied to something.
    let (head, args) = crate::expr::get_app(codomain);
    match &*head {
        Expr::Const(n, _) if n == ind => {}
        _ => return gap(Gap::IndSpec(ind.clone(), "ctor codomain")),
    }
    // …and each argument's interpretation and typing, by inference on the
    // argument itself. This is the step that refuses a constructor whose result
    // indices are not the ones the clause's closed form is about.
    let mut arg_tms = Vec::with_capacity(args.len());
    let mut arg_mems = Vec::with_capacity(args.len());
    for a in &args {
        let Ok(t) = c.infer_type(a) else { return gap(Gap::Classifier) };
        let (Some(tm), Ev::Proved(m)) = (t.tm, t.ev) else {
            return gap(Gap::IndSpec(ind.clone(), "ctor codomain argument"))
        };
        arg_tms.push(tm);
        arg_mems.push(m);
    }
    let Some(store_ty) = c.stored_term(ind, inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
    let point = ip.point();

    // `⟦T⟧` applied to the codomain's own arguments, beta-reduced to the set the
    // clause denotes. The premise each level consumes is the argument's typing,
    // which the loop above inferred.
    let Some((carrier, spine_eq)) = ip.beta_spine(&store_ty, &arg_tms, &arg_mems) else {
        return gap(Gap::IndSpec(ind.clone(), "type former spine"))
    };

    // **A decline that still hands back `•`.** A direct declaration's
    // constructor denotes `•` whatever its typing does, because the declaration
    // is a subset of `1` and §6.2's proof clause is what says so; what a clause
    // supplies is the derivation that puts `•` in the *right* subset. Returning
    // `tm: None` here would take the type former down with it — `zoneb::store`
    // reads a missing term as a decline of the whole declaration, and `ensure`
    // then records it against the declaration's own key.
    let undecided = |g: Gap| Typing { ty: ty.clone(), tm: Some(point.clone()), ev: Ev::missing(g) };

    // `⊢ • ∈ carrier`, per clause.
    let mem = match clause {
        // `Eq.refl a : Eq α a a` — reflexivity at the *second* codomain
        // argument. If the export's codomain were `Eq α a b` this concludes a
        // membership in `eq_set(a,a)` and the check below refuses it.
        Clause::Eq => match arg_tms.get(1).and_then(|a| inst_all(&d.eq_refl, std::slice::from_ref(a))) {
            Some(t) => t,
            None => return gap(Gap::IndSpec(ind.clone(), "refl instance")),
        },
        // `Acc.intro α r x (h : ∀ y, r y x → Acc α r y) : Acc α r x`.
        //
        // **The type former lands and the constructor's typing does not yet.**
        // `derived::acc::acc_intro` is the rule and it is unconditional; what is
        // missing is one transport, and it is named rather than guessed at:
        // `acc_intro`'s second premise is
        // `∀y. (y ∈ A → (⟨y,x⟩ ∈ R̄ → y ∈ acc(A,R̄)))`, while what the nest holds
        // is the scope typing of the `h` binder — `• ∈ ⟦∀ y:α, r y x → Acc α r y⟧`,
        // a *conditional singleton* over the same statement spelled in Lean's
        // terms: `• ∈ app(app(r̄,y),x̄)` where `acc_intro` wants `⟨y,x̄⟩ ∈ R̄`
        // ([`AccClause::graph_pair`](crate::acc::AccClause::graph_pair) is that
        // step), and `• ∈ ⟦Acc α r y⟧` — a **redex** over this very nest — where
        // it wants `y ∈ acc(A,R̄)`, which is one `beta_spine` and one
        // conditional-singleton elimination.
        //
        // Nothing here is owed by `derived/`; it is the transport that is
        // unwritten, and it is stated in this comment so the next build knows
        // what it is doing rather than discovering it.
        Clause::Acc => return undecided(Gap::IndSpec(ind.clone(), ACC_INTRO)),
    };
    if *mem.concl() != Formula::mem(point.clone(), carrier) {
        return gap(Gap::IndSpec(ind.clone(), "ctor is not about its own codomain"))
    }
    // …and back onto the applied spine, which is what the Lean codomain
    // interprets to.
    let back = match derived::eq_symm(&mut ip.env, &spine_eq) {
        Some(t) => t,
        None => return gap(Gap::ConvCompose("direct-spine-symm")),
    };
    match ip.retarget_set(&mem, &back) {
        Some(t) => Typing { ty, tm: Some(point), ev: Ev::Proved(t) },
        None => gap(Gap::ConvCompose("direct-codomain")),
    }
}

impl Interp {
    /// The direct-clause apparatus, over **this** `Interp`'s own unit set.
    ///
    /// Built on first use and then shared: two uses of `Eq` at different `σ`
    /// must name **one** `eq_set`, or their definitional equality would need a
    /// theorem where reflexivity should do — the same identity requirement
    /// `Interp::lam_site` and `IndApparatus::decls` have.
    pub fn direct(&mut self) -> Option<std::rc::Rc<Direct>> {
        if self.direct.is_none() && !self.direct_failed {
            let sums = self.prelude.tower.sums.clone();
            self.direct = Direct::build(&mut self.env, &sums).map(std::rc::Rc::new);
            self.direct_failed = self.direct.is_none();
        }
        self.direct.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{bvar, forall, konst, sort};

    fn nm(s: &str) -> Name { Name::simple(s) }

    /// The table is a table: it answers on the one name it knows and on nothing
    /// else, and in particular not on a *qualified* name that happens to end in
    /// it, and not on the two names it used to know.
    #[test]
    fn the_clause_table_is_keyed_on_the_whole_name() {
        assert_eq!(clause_for(&nm("Eq")), Some(Clause::Eq));
        assert_eq!(clause_for(&nm("List")), None);
        // The two retired rows. `And` and `PUnit` are ordinary class-(S)
        // declarations and go through [`crate::class_s`]; a table entry here
        // would take them off the general route silently.
        assert_eq!(clause_for(&nm("And")), None, "And is not a direct clause");
        assert_eq!(clause_for(&nm("PUnit")), None, "PUnit is not a direct clause");
        assert_eq!(clause_for(&Name::str(&nm("Foo"), "Eq")), None, "Foo.Eq is not Eq");
        assert_eq!(clause_for(&Name::str(&nm("Eq"), "refl")), None, "a constructor is not the type");
    }

    /// `Eq`, as the exports declare it, translated end to end: `⟦Eq.{0}⟧` is a
    /// three-deep nest whose typing is about `⟦Prop⟧`, and `⟦Eq.refl.{0}⟧` is a
    /// two-deep nest whose typing is about `⟦Eq α a a⟧`.
    fn eq_env(l: Level) -> (Environment, Name, Name) {
        let (e, r) = (nm("Eq"), Name::str(&nm("Eq"), "refl"));
        let us: std::rc::Rc<[Level]> = vec![l.clone()].into();
        // `Eq : ∀ (α : Sort l) (a : α), α → Prop`
        let ty = forall(
            sort(l.clone()),
            forall(bvar(0), forall(bvar(1), sort(Level::Zero))),
        );
        // `Eq.refl : ∀ (α : Sort l) (a : α), Eq α a a`
        let cty = forall(
            sort(l),
            forall(
                bvar(0),
                crate::expr::app(
                    crate::expr::app(
                        crate::expr::app(konst(e.clone(), us), bvar(1)),
                        bvar(0),
                    ),
                    bvar(0),
                ),
            ),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e.clone(),
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(r.clone(), cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, e, r)
    }

    #[test]
    fn eq_and_its_constructor_are_interpreted_with_their_typings() {
        let (env, e, r) = eq_env(Level::Param(nm("u")));
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let us: std::rc::Rc<[Level]> = vec![Level::Zero].into();

        let t = c.infer_type(&konst(e.clone(), us.clone())).expect("infer ⟦Eq⟧");
        let m = t.ev.thm().unwrap_or_else(|| panic!("⟦Eq⟧ has no typing: {:?}", t.ev)).clone();
        assert!(m.hyps().is_empty(), "a closed declaration's typing is unconditional");
        assert!(t.tm.is_some(), "⟦Eq⟧ must interpret");

        let ct = c.infer_type(&konst(r.clone(), us)).expect("infer ⟦Eq.refl⟧");
        let cm = ct.ev.thm().unwrap_or_else(|| panic!("⟦Eq.refl⟧ has no typing: {:?}", ct.ev)).clone();
        assert!(cm.hyps().is_empty());
        let (subj, _) = cm.concl().as_mem().expect("a membership");
        assert_eq!(subj, ct.tm.clone().unwrap(), "the typing must be about ⟦Eq.refl⟧ itself");
        assert_eq!(subj, c.interp().unwrap().point(), "a proof denotes •");
    }

    /// **The name is not the evidence.** A declaration called `Eq` whose
    /// constructor lands at a *different* index — `Eq α a a` replaced by
    /// `Eq α a x` for a third bound variable — is declined, because the
    /// membership `Eq.refl`'s clause derives is about `eq_set(a,a)` and the
    /// codomain interprets to `eq_set(a,x)`.
    #[test]
    fn a_misshapen_declaration_named_eq_is_declined_not_believed() {
        let (e, r) = (nm("Eq"), Name::str(&nm("Eq"), "refl"));
        let us: std::rc::Rc<[Level]> = vec![Level::Param(nm("u"))].into();
        let ty = forall(
            sort(Level::Param(nm("u"))),
            forall(bvar(0), forall(bvar(1), sort(Level::Zero))),
        );
        // `Eq.refl : ∀ (α : Sort u) (a x : α), Eq α a x` — same name, wrong law.
        let cty = forall(
            sort(Level::Param(nm("u"))),
            forall(
                bvar(0),
                forall(
                    bvar(1),
                    crate::expr::app(
                        crate::expr::app(
                            crate::expr::app(konst(e.clone(), us), bvar(2)),
                            bvar(1),
                        ),
                        bvar(0),
                    ),
                ),
            ),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: e.clone(),
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(r.clone(), cty)],
            },
        )
        .expect("accepted");
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: std::rc::Rc<[Level]> = vec![Level::Zero].into();
        let ct = c.infer_type(&konst(r, at)).expect("infer");
        // Its *interpretation* is still `•`: §6.2's proof clause gives every
        // proof that denotation whatever its type, and proof irrelevance is not
        // in question here. What must not exist is the **typing**.
        assert_eq!(ct.tm, Some(c.interp().unwrap().point()));
        assert_eq!(
            ct.ev.gap(),
            Some(&Gap::IndSpec(e, "ctor is not about its own codomain")),
            "a declaration named Eq whose constructor is not reflexivity must be declined, \
             with a reason naming what was refused"
        );
    }
}
