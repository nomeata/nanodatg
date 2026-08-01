//! **The direct interpretation clauses** — the declarations whose denotation is
//! *named* rather than translated (`INDEXED-DESIGN.md` §2.2).
//!
//! # Interface
//!
//! ```text
//! direct::clause_for(name)                -> Option<Clause>
//! direct::build(checker, clause, name, σ) -> Result<(), Gap>
//! direct::Direct::build(env, sums)        -> Option<Direct>   (the apparatus)
//! ```
//!
//! [`build`] is called from [`crate::zoneb::build`] **before** the class-(T)
//! walk, on the declarations [`clause_for`] names, and it stores `⟦T.{σ}⟧` and
//! `⟦T.ctor.{σ}⟧` exactly as the general path does — the same
//! [`Checker::lam_nest`](crate::kernel::Checker::lam_nest), the same store, the
//! same `Gap` vocabulary.
//!
//! # Why three declarations are interpreted and not translated
//!
//! `INDEXED-DESIGN.md` §2.2 settles it for `Eq`, and the argument generalises to
//! the other two. Carneiro's §5.3 gives a class-(S) declaration the carrier
//!
//! ```text
//! ⟦T p⃗ x⃗⟧ = [ tup(x⃗) ∈ acc(A_φ(p⃗), R(p⃗)) ]
//! ```
//!
//! and for a **non-recursive** declaration `R` is provably empty, so `acc` is
//! the identity and the carrier collapses to a single conditional singleton
//! `[φ]` over the constructors' field existentials. The three declarations below
//! are exactly the collapses that have a closed form:
//!
//! | declaration | class | §5.3's `[φ]` collapses to | as a term |
//! |---|---|---|---|
//! | `Eq.{u} {α} (a : α) : α → Prop` | (S) | `[ b ∈ ⟦α⟧ ∧ b = a ]` | `eq_set(a,b) = [a = b]` |
//! | `And (a b : Prop) : Prop` | (S) | `[ ∃l∃r. (l ∈ a ∧ r ∈ b) ]` | `and_set(a,b) = [• ∈ a ∧ • ∈ b]` |
//! | `PUnit.{u} : Sort u` | (S) | `[ ⊤ ]` | `1` |
//!
//! # One of these three rows is permanent; two are stopgaps with a delete-by
//!
//! **`Eq` is principled.** It is a member of Carneiro's eight-item menagerie
//! and §6.2 gives it its own interpretation clause — `⟦a = b⟧ = [⟦a⟧ = ⟦b⟧]`,
//! `⟦refl a⟧ = •`, `⟦rec₌ e b h⟧ = ⟦e⟧` (all three are implemented, the last in
//! [`crate::recursor`]). Interpreting it directly is following the thesis, not
//! shortcutting it, and the same will hold of `Acc` when its clause
//! (`derived::rec_acc::pack`) is wired.
//!
//! **`And` and `PUnit` are not.** They are ordinary declarations — a two-field
//! `Prop` structure and a one-constructor subsingleton — that happen to collapse
//! the same way and happen to have closed forms in [`derived::prop`]. Nothing
//! distinguishes them from `ProjDataIndex` and `SortElimProp`, which the general
//! class-(S) clause below would also close. So:
//!
//! > **Delete-by.** When
//! > [`IndexSpace::build`](derived::inductive::family::IndexSpace) gains its
//! > non-indexed case and [`LeCarrier`](derived::inductive::family::LeCarrier)
//! > becomes reachable for a non-indexed class-(S) declaration,
//! > [`Clause::And`] and [`Clause::Unit`] are to be **deleted** and `And` and
//! > `PUnit` routed through that clause. [`Clause::Eq`] stays.
//!
//! The condition is written down because this project has the precedent:
//! `enums`/`wnat`/`wlist` were stopgaps with good headers and were still
//! carrying the corpus days after the general machine existed. A stopgap that
//! explains itself well is exactly the kind that survives. For the same reason
//! the table takes **no fourth row**: a declaration that seems to want one is
//! evidence that the general clause is missing a case, and belongs in the
//! ledger as a gap naming that construction.
//!
//! The `b ∈ ⟦α⟧` and the `∃`-to-`•` steps are the two places a collapse is not
//! syntactic, and both are *already discharged in `derived`*:
//! [`derived::prop`] builds `eq_set` and `and_set` as the interpretations of
//! Lean's `Eq` and `And` and proves the typings of `Eq.refl` and `And.intro`
//! about them, and `1`'s only element is `•` by
//! [`Sums::unit_eta`](derived::sums::Sums). Going the long way round — an
//! [`IndexedDeclSpec`](derived::inductive::family::IndexedDeclSpec), an
//! `A_φ`, an `acc`, and `acc_empty_relation` — would arrive at a *provably
//! equal* set by a route with strictly more moving parts, which is the trade
//! `INDEXED-DESIGN.md` §2.2 already declined for `Eq`.
//!
//! # Keyed by name, verified by derivation
//!
//! [`clause_for`] is a table on the declaration's **name**, which is one hash
//! comparison on the name `ensure` was asked about — the same key the store is
//! keyed on, so MINI-DESIGN.md §0's claim is untouched: nothing is looked up by
//! shape and nothing is tried and retried.
//!
//! A name is not evidence, though, and this module never treats it as such.
//! Every clause states its bottom against the type the **export** gives:
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
//! general path applies at [`crate::zoneb::ctor_bottom`], and it is the reason
//! the shape checks here are deliberately thin: the derivation is the check.
//!
//! # What is deliberately *not* here
//!
//! The general class-(S) clause — `[⋁ᵢ ∃y⃗ᵢ. ⋀ⱼ yⱼ ∈ βᵢⱼ]` for an arbitrary
//! non-recursive subsingleton, which would subsume all three rows above and add
//! `ProjDataIndex` and `SortElimProp`. It needs a `derived`-side entry point:
//! [`LeCarrier`](derived::inductive::family::LeCarrier) is that construction,
//! but it is stated over an
//! [`IndexedDeclSpec`](derived::inductive::family::IndexedDeclSpec) and
//! `IndexSpace::build` has no non-indexed case. Assembling the disjunction of
//! existentials on the mini side instead would put a model-level derivation in
//! the checker, which is the boundary this project keeps.

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

/// The three symbols the direct clauses denote with, over **the prelude's own**
/// [`Sums`] so that their `1` and `•` are the ones every other clause speaks of.
///
/// This is [`derived::prop::Props`] restricted to what the clauses need.
/// `Props::new` mints a *fresh* `Sums`, hence a second `1`, so it cannot be the
/// thing an interpretation store already committed to a unit set uses; the two
/// constructions below are the same ones its constructor performs, at the unit
/// set this `Interp` already has.
pub struct Direct {
    /// `eq_set(a,b) = [a = b]`.
    pub eq: FnSym,
    /// `⊢ ∀a ∀b ∀z. (z ∈ eq_set(a,b) ↔ (z ∈ 1 ∧ a = b))`.
    pub eq_ax: Thm,
    /// `⊢ ∀a. • ∈ eq_set(a,a)` — the typing of `Eq.refl`.
    pub eq_refl: Thm,
    /// `and_set(p,q) = [• ∈ p ∧ • ∈ q]`.
    pub and: FnSym,
    /// `⊢ ∀p ∀q ∀z. (z ∈ and_set(p,q) ↔ (z ∈ 1 ∧ (• ∈ p ∧ • ∈ q)))`.
    pub and_ax: Thm,
    /// `⊢ ∀p ∀q. ((• ∈ p ∧ • ∈ q) → • ∈ and_set(p,q))` — `And.intro`'s typing.
    pub and_intro: Thm,
}

impl Direct {
    /// Introduce both conditional singletons and derive the two typings.
    pub fn build(env: &mut Env, sums: &Sums) -> Option<Direct> {
        // ── Eq ───────────────────────────────────────────────────────────
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

        // ── And ──────────────────────────────────────────────────────────
        let (p, q) = (env.fresh_var(), env.fresh_var());
        let (tp, tq) = (Term::var(p), Term::var(q));
        let pt = sums.point();
        let and_phi = Formula::and(
            Formula::mem(pt.clone(), tp.clone()),
            Formula::mem(pt, tq.clone()),
        );
        let (and, and_ax) = conditional_singleton(env, sums, &[p, q], &and_phi)?;
        let c_pq = Term::apply(and, vec![tp.clone(), tq.clone()]);
        let chi_pq = inst_all(&and_ax, &[tp, tq])?;
        let and_intro = gen_all(&[p, q], &cond_intro(sums, &and_phi, &c_pq, &chi_pq)?);

        Some(Direct { eq, eq_ax, eq_refl, and, and_ax, and_intro })
    }
}

/// Which direct clause a declaration takes, if any.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Clause {
    /// `Eq.{u} {α : Sort u} (a : α) : α → Prop`.
    Eq,
    /// `And (a b : Prop) : Prop`.
    And,
    /// `PUnit.{u} : Sort u`.
    Unit,
}

impl Clause {
    /// `(num_params, num_indices, number of constructors)`, as the export must
    /// state them. Checked before anything is built, so a same-named
    /// declaration of a different shape is declined rather than half-built.
    fn arity(self) -> (u32, u32, usize) {
        match self {
            Clause::Eq => (2, 1, 1),
            Clause::And => (2, 0, 1),
            Clause::Unit => (0, 0, 1),
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
        "And" => Some(Clause::And),
        "PUnit" => Some(Clause::Unit),
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
            depth: cdepth,
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
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::Gap(g) };
    let Some((xs, _)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
    let sums = ip.prelude.tower.sums.clone();
    let tower = ip.prelude.tower.clone();

    // The term, and the formula it is the conditional singleton of. `PUnit`'s
    // is the unit set itself, which is not of that form and is typed directly.
    let (term, phi_chi) = match cl {
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
            (t, Some((phi, chi)))
        }
        // `⟦And p q⟧ = and_set(⟦p⟧, ⟦q⟧)`.
        Clause::And => {
            let (p, q) = (xs[0].clone(), xs[1].clone());
            let t = ip.mk(d.and, vec![p.clone(), q.clone()]);
            let pt = sums.point();
            let phi = Formula::and(
                Formula::mem(pt.clone(), p.clone()),
                Formula::mem(pt, q.clone()),
            );
            let Some(chi) = inst_all(&d.and_ax, &[p, q]) else {
                return gap(Gap::IndSpec(name.clone(), "and instance"))
            };
            (t, Some((phi, chi)))
        }
        // `⟦PUnit.{u}⟧ = 1`, at every `u`.
        Clause::Unit => (sums.unit(), None),
    };

    // `⊢ term ∈ U₀`, then raised to the declaration's own level. Both `[φ] ∈ U₀`
    // and `1 ∈ U₀` are closed theorems of the tower; the raise is the
    // cumulativity table, and it is what makes `PUnit.{u}` land in `⟦Sort u⟧`
    // rather than only in `⟦Prop⟧`.
    let in_u0 = match &phi_chi {
        Some((phi, chi)) => tower.cond_in_u0(&mut ip.env, phi, &term, chi),
        None => Some(tower.true_in_u0.clone()),
    };
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
    depth: usize,
}

/// The bottom of a direct constructor's nest.
///
/// **Every direct constructor's interpretation is `•`**, because all three
/// declarations denote subsets of `1`; what differs is the derivation that puts
/// `•` in the right one. The codomain is decomposed and its arguments are
/// *inferred* — not assumed to be the binders in order — so the membership is
/// established about the set the export says the constructor lands in.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { ind, inst, clause, codomain, depth } = site;
    let ty = codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::Gap(g) };
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
    // The field typings the antecedent of `And.intro` is discharged from: the
    // nest's own scope assumptions, which is one vector read each.
    let Some((_, field_mems)) = c.binders(*depth) else { return gap(Gap::NoEndpoint) };

    let Some(store_ty) = c.stored_term(ind, inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
    let sums = ip.prelude.tower.sums.clone();
    let point = sums.point();

    // `⟦T⟧` applied to the codomain's own arguments, beta-reduced to the set the
    // clause denotes. The premise each level consumes is the argument's typing,
    // which the loop above inferred.
    let Some((carrier, spine_eq)) = ip.beta_spine(&store_ty, &arg_tms, &arg_mems) else {
        return gap(Gap::IndSpec(ind.clone(), "type former spine"))
    };

    // `⊢ • ∈ carrier`, per clause.
    let mem = match clause {
        // `Eq.refl a : Eq α a a` — reflexivity at the *second* codomain
        // argument. If the export's codomain were `Eq α a b` this concludes a
        // membership in `eq_set(a,a)` and the check below refuses it.
        Clause::Eq => match arg_tms.get(1).and_then(|a| inst_all(&d.eq_refl, std::slice::from_ref(a))) {
            Some(t) => t,
            None => return gap(Gap::IndSpec(ind.clone(), "refl instance")),
        },
        // `And.intro : a → b → And a b`. Its two fields are *proofs*, so their
        // scope typings are `⟦l⟧ ∈ ⟦a⟧` and `⟦r⟧ ∈ ⟦b⟧` while `and_intro`'s
        // antecedent is about `•`; proof irrelevance moves each one, and the
        // premise it needs — `⟦a⟧ ∈ U₀` — is the *codomain argument's* own
        // typing, already in hand.
        Clause::And => {
            if arg_mems.len() != 2 || field_mems.len() != 4 {
                return gap(Gap::IndSpec(ind.clone(), "intro arity"));
            }
            let mut atoms = Vec::with_capacity(2);
            for k in 0..2 {
                let Some(pf) = ip.point_of_proof(&arg_mems[k], &field_mems[2 + k]) else {
                    return gap(Gap::IndSpec(ind.clone(), "intro field is not a proof"))
                };
                // `point_of_proof` concludes `⟦field⟧ = •`, and the subject
                // being *replaced* is the one on the equation's right, so the
                // equation travels the other way round.
                let Some(pf) = derived::eq_symm(&mut ip.env, &pf) else {
                    return gap(Gap::ConvCompose("direct-intro-symm"))
                };
                match ip.retarget_subject(&field_mems[2 + k], &pf) {
                    Some(t) => atoms.push(t),
                    None => return gap(Gap::ConvCompose("direct-intro-field")),
                }
            }
            let Some(at) = inst_all(&d.and_intro, &[arg_tms[0].clone(), arg_tms[1].clone()]) else {
                return gap(Gap::IndSpec(ind.clone(), "and_intro instance"))
            };
            match Thm::mp(&at, &derived::and_intro(&atoms[0], &atoms[1])) {
                Some(t) => t,
                None => return gap(Gap::IndSpec(ind.clone(), "intro antecedent")),
            }
        }
        // `PUnit.unit : PUnit` — `⊢ • ∈ 1`, with nothing to discharge.
        Clause::Unit => sums.unit_mem.clone(),
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

    /// The table is a table: it answers on the three names it knows and on
    /// nothing else, and in particular not on a *qualified* name that happens to
    /// end in one of them.
    #[test]
    fn the_clause_table_is_keyed_on_the_whole_name() {
        assert_eq!(clause_for(&nm("Eq")), Some(Clause::Eq));
        assert_eq!(clause_for(&nm("And")), Some(Clause::And));
        assert_eq!(clause_for(&nm("PUnit")), Some(Clause::Unit));
        assert_eq!(clause_for(&nm("List")), None);
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
