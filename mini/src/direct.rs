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
use crate::expr::{Expr, Level, Name, E, NameView};
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
    /// `⊢ ∀a ∀b. (a = b → • ∈ eq_set(a,b))` — [`Direct::eq_refl`]'s rule with
    /// the equation still to be supplied.
    ///
    /// `Eq.refl` is this at `b := a` with `Thm::eq_refl` for the antecedent,
    /// and that is how it is built below. It is carried separately because a
    /// codomain whose two sides are *different* terms is not reflexivity and
    /// still has to be inhabited: `Quot.sound` at `u ≥ 1` is the occupant, and
    /// there the equation is `derived::quot::q_sound`'s.
    pub eq_intro: Thm,
}

impl Direct {
    /// Introduce the conditional singleton and derive reflexivity's typing.
    pub fn build(env: &mut Env, sums: &Sums) -> Option<Direct> {
        let (a, b) = (env.fresh_var(), env.fresh_var());
        let (ta, tb) = (Term::var(a), Term::var(b));
        let tb2 = tb.clone();
        let (eq, eq_ax) = conditional_singleton(env, sums, &[a, b], &Formula::eq(ta.clone(), tb))?;
        // Reflexivity is the same introduction rule at `b := a`, where the
        // condition is a theorem rather than a hypothesis.
        let refl_phi = Formula::eq(ta.clone(), ta.clone());
        let c_aa = Term::apply(eq, vec![ta.clone(), ta.clone()]);
        let chi_aa = inst_all(&eq_ax, &[ta.clone(), ta.clone()])?;
        let intro = cond_intro(sums, &refl_phi, &c_aa, &chi_aa)?;
        let eq_refl = gen_all(&[a], &Thm::mp(&intro, &Thm::eq_refl(ta.clone()))?);

        // …and the same introduction at two arbitrary sides, with the equation
        // left as an antecedent.
        let phi_ab = Formula::eq(ta.clone(), tb2.clone());
        let c_ab = Term::apply(eq, vec![ta.clone(), tb2.clone()]);
        let chi_ab = inst_all(&eq_ax, &[ta, tb2])?;
        let eq_intro = gen_all(&[a, b], &cond_intro(sums, &phi_ab, &c_ab, &chi_ab)?);

        Some(Direct { eq, eq_ax, eq_refl, eq_intro })
    }
}

/// Why `⟦Acc.intro⟧`'s *typing* was declined — the transport
/// [`crate::acc::intro_mem`] performs did not run to the end at this instance.
///
/// It is **built** now (`117_accRecType`'s `σ = [1,1]` was the one pair waiting
/// on it, under a `waiting:` row labelled for the eliminator). The reason is
/// kept, at its original spelling, because the transport is still fallible by
/// design: every step of it compares a shape rather than trusting a name, and a
/// declaration named `Acc` whose constructor is not `Acc.intro` must reach a
/// decline with a reason and not a wrong theorem.
pub const ACC_INTRO: &str = "acc: Acc.intro's step hypothesis is not transported to preds_in";

/// A declaration named `Nat` whose constructors are not Lean's two.
///
/// Reached when the name and the arity disagree — a `zero` that takes a field,
/// a `succ` that takes none, or a constructor called neither. It is a decline
/// with a reason and never a wrong theorem: the alternative is handing `⊢ 0 ∈ ω`
/// to something that is not zero.
pub const NAT_CTOR: &str = "nat: a constructor is not Nat.zero at arity 0 or Nat.succ at arity 1";

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
    /// anyway — `Acc.intro`'s recursive field is `∀y. r y x → Acc r y`, a
    /// function-typed recursive argument at telescope depth **2** on an
    /// *indexed* declaration, and `zoneb::ctor_spec` declines both of those.
    /// *(That sentence used to name `Gap::FunTypedRecArg` and call it "the
    /// reason the corpus rows wait on". Neither half survives: `Acc` has taken
    /// this clause since well before the walk would look, so no `Acc` pair has
    /// waited on that reason for several rounds, and the variant now has no
    /// mint site at all — the walk expresses depth-1 telescopes and declines
    /// the rest as `Gap::IndSpec` with the step that refused them.)*
    Acc,
    /// `Nat : Type 0`, with `Nat.zero` and `Nat.succ`.
    ///
    /// **The third row, and the first that is not `Prop`-valued.** Everything
    /// above denotes a subset of `1`, so its former's bottom is a conditional
    /// singleton and each of its constructors' is `•`; `⟦Nat⟧ = ω` is neither,
    /// and both bottoms below therefore grew a second route.
    ///
    /// It is not a fourth row of the retired closed-form table either, and the
    /// standing rule this module states is not violated by it. That rule is
    /// against a *collapse that happens to be convenient* — a declaration the
    /// general clause already covers, hardcoded because a closed form was
    /// noticed. The general clause covers `Nat` perfectly well and produces a
    /// **W-type carrier**; what it cannot produce is a carrier a *binary
    /// numeral* is a term of, and that is the whole reason this row exists.
    /// `⟦natLit n⟧` is `num(n)` — 66 nodes at `2⁶⁴` against 2⁶⁴ of anything —
    /// and `num` is built from `double`/`double1` on `ω`, which are symbols
    /// no W-type has. So the row is `Acc`'s kind: a construction the general
    /// route does not have and cannot be made to reach.
    ///
    /// The cost of *not* taking it was measured before it was taken: with the
    /// literal guard lifted and the general carrier kept, `init-prelude`
    /// expanding one 55296-deep successor tower peaked at 166 MB and produced
    /// no verdict in 600 s (`NAT-REPRESENTATION.md` §1.3.2).
    Nat,
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
            // No parameters, no indices, `zero` and `succ`.
            Clause::Nat => (0, 0, 2),
        }
    }
}

/// The table. One comparison on the name [`crate::zoneb::ensure`] was asked
/// about — never a scan, and never a shape match.
///
/// **Through `monomorph`'s root prefix.** The key is a name, and `monomorph`
/// (`MONOMORPH.md` §1.1) is entitled to rewrite one: `Acc.{u}` at `[0]` reaches
/// here as `_at.1.0.Acc`, the row did not fire, the general walk met
/// `Acc.intro`'s depth-2 recursive telescope and declined it. `Eq` and `Nat`
/// survived only because they are *carried built-ins* (`MONOMORPH.md` §3) and
/// keep their names, which is an accident of that list and not a property of
/// this table. [`crate::mono_name::strip`] is the identity on an unprefixed
/// name, so the unmonomorphized case is unchanged and there is no branch.
///
/// Stripping is safe here for the reason the module header already gives: a
/// name is not evidence. A declaration that reaches a row it is not is refused
/// by the arity check and by the derivation's own shape checks, and that
/// argument does not care how the name was spelled.
pub fn clause_for(n: &Name) -> Option<Clause> {
    let NameView::Str(pre, s) = crate::mono_name::strip(n).view() else { return None };
    if !pre.is_anon() {
        return None
    }
    match &*s {
        "Eq" => Some(Clause::Eq),
        "Acc" => Some(Clause::Acc),
        "Nat" => Some(Clause::Nat),
        _ => None,
    }
}

/// `⟦T.{σ}⟧` and `⟦T.ctor.{σ}⟧` for one direct declaration.
///
/// The shape of the walk is [`crate::zoneb::build`]'s: the declaration's own
/// data, the type former as a `np + ni`-deep λ-nest, then one nest per
/// constructor. What differs is only the bottom of each nest.
pub fn build(c: &mut Checker<'_, '_>, cl: Clause, name: &Name, inst: &[u32]) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(*name, w);
    let env = c.environment();
    let Some(ConstantInfo::Inductive { lparams, ty, num_params, num_indices, ctors, .. }) =
        env.get(name)
    else {
        return Err(Gap::NoInterpretation(*name, inst.to_vec()))
    };
    let (np, ni, nc) = cl.arity();
    if (*num_params, *num_indices, ctors.len()) != (np, ni, nc) {
        return Err(bad("direct clause: declaration shape"))
    }
    if inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*name, inst.to_vec()))
    }
    let depth = (np + ni) as usize;
    let lean_ty = ground::subst_ground(ty, lparams, inst);
    // The resultant sort, as a ground numeral: the universe the former's
    // bottom must land in, read off the declaration rather than assumed.
    let own = crate::zoneb::peel(&lean_ty, depth).ok_or_else(|| bad("type shape"))?;
    let Expr::Sort(l) = &own.view() else { return Err(bad("resultant sort")) };
    let level = ground::as_numeral(l).ok_or_else(|| bad("level"))?;
    let ctor_tys: Vec<(Name, E)> = ctors
        .iter()
        .map(|n| {
            env.get(n)
                .map(|ci| (*n, ground::subst_ground(ci.ty(), lparams, inst)))
                .ok_or_else(|| bad("ctor type"))
        })
        .collect::<Result<_, _>>()?;

    // ── the type former ───────────────────────────────────────────────────
    let nm = *name;
    let mut bottom =
        move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(former_bottom(c, cl, &nm, depth, level)) };
    let t = c.lam_nest(&lean_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, name, inst, t)?;

    // ── the constructors ──────────────────────────────────────────────────
    for (cname, cty) in &ctor_tys {
        let cdepth = arity_of(cty);
        let codomain = crate::zoneb::peel(cty, cdepth).ok_or_else(|| bad("ctor arity"))?;
        let site = CtorSite {
            ind: *name,
            ctor: *cname,
            inst: inst.to_vec(),
            clause: cl,
            codomain,
            eq: None,
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
    let mut cur = *ty;
    while let Expr::Forall { body, .. } = &cur.clone().view() {
        n += 1;
        cur = *body;
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
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let Some((xs, _)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };

    // **`⟦Nat⟧ = ω`, and its typing is not a conditional singleton's.** Every
    // other row reaches `tower.cond_in_u0` below, because every other row
    // denotes a subset of `1`. This one denotes the carrier itself and the
    // membership is already a closed theorem of the apparatus — so the route
    // is not "the same derivation at a different `φ`", it is a different
    // derivation, and it returns before the `[φ]` machinery is touched.
    //
    // The level is **read off the export** and required to be `1`, exactly as
    // the general route reads it: `Nat : Type 0` is `Sort 1`, and a
    // declaration named `Nat` that claims any other resultant sort is not the
    // one `ω` models and is declined by height rather than given `ω` anyway.
    if cl == Clause::Nat {
        if level != 1 {
            return gap(Gap::IndUniverseHeight(*name, level))
        }
        let Some(nc) = ip.nat_clause() else { return gap(Gap::IndApparatus) };
        let term = nc.nat.omega();
        let mem = nc.nat.omega_mem().clone();
        // `⊢ ω ∈ U₁` **is** `⊢ ω ∈ ⟦Sort 1⟧` — the same term, not one that
        // prints the same — because the apparatus was built over this
        // `Interp`'s own tower. If it were not, this comparison is what would
        // fail, and that is why it is a comparison and not an assumption.
        return if *mem.concl() == Formula::mem(term.clone(), ip.sort(1)) {
            Typing { ty, tm: Some(term), ev: Ev::Proved(mem) }
        } else {
            gap(Gap::IndSpec(*name, "denotation typing"))
        }
    }

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
                return gap(Gap::IndSpec(*name, "eq instance"))
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
                return gap(Gap::IndSpec(*name, "acc instance"))
            };
            (t, phi, chi)
        }
        // Returned above: `ω` is not a conditional singleton and this match is
        // only about the rows that are.
        Clause::Nat => return gap(Gap::IndSpec(*name, "nat: reached the conditional-singleton route")),
    };

    // `⊢ term ∈ U₀`, then raised to the declaration's own level. `[φ] ∈ U₀` is a
    // closed theorem of the tower; the raise is the cumulativity table, and it
    // is what would make a `Sort u`-valued clause land in `⟦Sort u⟧` rather
    // than only in `⟦Prop⟧`.
    let in_u0 = tower.cond_in_u0(&mut ip.env_mut(), &phi, &term, &chi);
    let Some(in_u0) = in_u0 else { return gap(Gap::IndSpec(*name, "denotation typing")) };
    let raised = if level == 0 {
        Some(in_u0)
    } else {
        ip.raise_in_gamma(0, level as usize, &in_u0)
    };
    match raised {
        Some(t) if *t.concl() == Formula::mem(term.clone(), ip.sort(level)) => {
            Typing { ty, tm: Some(term), ev: Ev::Proved(t) }
        }
        _ => gap(Gap::IndUniverseHeight(*name, level)),
    }
}

/// `Sort ℓ` at a ground numeral.
fn level_of(n: u32) -> Level {
    let mut l = Level::zero();
    for _ in 0..n {
        l = l.succ();
    }
    l
}

/// **`⊢ • ∈ ⟦Eq α a b⟧` at a codomain that is not a constructor's.**
///
/// [`ctor_bottom`] does not consult which *declaration* it is the bottom of: it
/// decomposes the codomain it was handed, infers that codomain's own arguments,
/// β-reduces the stored `⟦Eq.{0}⟧` at them and applies `Direct::eq_refl` at the
/// second — so it is already the derivation for any nest whose codomain is an
/// equation between two terms the interpretation makes equal.
///
/// The one occupant is `Quot.sound`, whose codomain is
/// `Eq (Quot α r) (mk a) (mk b)` with both sides `•` at `u = 0`
/// (`QUOT-MODEL.md` §2.3's T8). It reaches this through [`crate::axiom`] and
/// not through a constructor path, which is why the entry point is here rather
/// than inlined: re-deriving reflexivity at a second `eq_set` would mint
/// nothing but would state the membership about a set no `Interp` committed to.
///
/// The check that the equation's two sides really are the same term is
/// [`ctor_bottom`]'s own final comparison, unchanged — a codomain whose sides
/// differ yields `• ∈ eq_set(a,a)` against a carrier `eq_set(a,b)` and is
/// declined with a reason.
pub(crate) fn eq_bottom(
    c: &mut Checker<'_, '_>,
    codomain: &E,
    inst: Vec<u32>,
    eq: Option<Thm>,
) -> Typing {
    let site = CtorSite {
        ind: Name::simple("Eq"),
        ctor: Name::str(&Name::simple("Eq"), "refl"),
        inst,
        clause: Clause::Eq,
        codomain: *codomain,
        eq,
    };
    ctor_bottom(c, &site)
}

/// One direct constructor: which declaration, which clause, and the codomain
/// read off its Lean type.
struct CtorSite {
    ind: Name,
    /// The **constructor's** own name. `Eq` and `Acc` have one constructor
    /// each and never read it; `Nat` has two whose bottoms are different terms
    /// — `0` and `succ(x)` — and picking between them by position in the
    /// export's list would hand `⟦Nat.zero⟧ = 0` to whichever constructor
    /// happened to be listed first. The arity check below is the derivation
    /// that confirms the name.
    ctor: Name,
    inst: Vec<u32>,
    clause: Clause,
    codomain: E,
    /// A proof of `arg₁ = arg₂` for an `Eq` codomain whose two sides differ.
    /// `None` is reflexivity, which is every constructor's own case.
    eq: Option<Thm>,
}

/// The bottom of a direct constructor's nest.
///
/// **A direct constructor's interpretation is `•`**, because the declaration
/// denotes a subset of `1`; what the clause supplies is the derivation that puts
/// `•` in the right one. The codomain is decomposed and its arguments are
/// *inferred* — not assumed to be the binders in order — so the membership is
/// established about the set the export says the constructor lands in.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { ind, ctor, inst, clause, codomain, eq } = site;
    let ty = *codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    // The codomain must be this declaration, applied to something.
    let (head, args) = crate::expr::get_app(codomain);
    match &head.view() {
        Expr::Const(n, _) if n == ind => {}
        _ => return gap(Gap::IndSpec(*ind, "ctor codomain")),
    }
    // …and each argument's interpretation and typing, by inference on the
    // argument itself. This is the step that refuses a constructor whose result
    // indices are not the ones the clause's closed form is about.
    let mut arg_tms = Vec::with_capacity(args.len());
    let mut arg_mems = Vec::with_capacity(args.len());
    for a in &args {
        let Ok(t) = c.infer_type(a) else { return gap(Gap::Classifier) };
        let (Some(tm), Ev::Proved(m)) = (t.tm, t.ev) else {
            return gap(Gap::IndSpec(*ind, "ctor codomain argument"))
        };
        arg_tms.push(tm);
        arg_mems.push(m);
    }
    // **`Acc.intro`'s last binder is its premise**, and the nest already holds
    // its typing. Read here, at one vector index, because it is the *checker*
    // that holds the scope stack and the interpretation borrow below outlives
    // the match — the same ordering [`crate::zoneb`]'s bottoms use.
    let step_hyp = match clause {
        Clause::Acc => c.binder(0).map(|(_, m)| m),
        Clause::Eq | Clause::Nat => None,
    };
    // **`Nat.succ`'s only binder is its field**, and the bottom needs the
    // *term* as well as the typing: `⟦Nat.succ x⟧` is `succ(⟦x⟧)`, not `•`.
    // `Nat.zero` has no binder and this is `None`, which is the arity check
    // that tells the two constructors apart.
    let field = if *clause == Clause::Nat { c.binder(0) } else { None };
    let Some(store_ty) = c.stored_term(ind, inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let point = ip.point();

    // `⟦T⟧` applied to the codomain's own arguments, beta-reduced to the set the
    // clause denotes. The premise each level consumes is the argument's typing,
    // which the loop above inferred.
    let Some((carrier, spine_eq)) = ip.beta_spine(&store_ty, &arg_tms, &arg_mems) else {
        return gap(Gap::IndSpec(*ind, "type former spine"))
    };

    // **A decline that still hands back `•`.** A direct declaration's
    // constructor denotes `•` whatever its typing does, because the declaration
    // is a subset of `1` and §6.2's proof clause is what says so; what a clause
    // supplies is the derivation that puts `•` in the *right* subset. Returning
    // `tm: None` here would take the type former down with it — `zoneb::store`
    // reads a missing term as a decline of the whole declaration, and `ensure`
    // then records it against the declaration's own key.
    let undecided = |g: Gap| Typing { ty, tm: Some(point.clone()), ev: Ev::missing(g) };

    // **What the constructor denotes.** `•` for the two `Prop` rows, whose
    // declarations are subsets of `1`; `Nat`'s two constructors denote `0` and
    // `succ(⟦x⟧)`, which is the whole difference between this row and those.
    let mut value = point.clone();

    // `⊢ value ∈ carrier`, per clause.
    let mem = match clause {
        // `Eq.refl a : Eq α a a` — reflexivity at the *second* codomain
        // argument. If the export's codomain were `Eq α a b` this concludes a
        // membership in `eq_set(a,a)` and the check below refuses it.
        // **Reflexivity unless the caller supplied the equation.** A
        // constructor's codomain is `Eq α a a` and `eq_refl` is the whole of
        // it; a codomain whose two sides are different terms — `Quot.sound` at
        // `u ≥ 1`, where they are two *classes* — is not reflexivity and hands
        // its own proof in. The equation is checked against the arguments this
        // walk **inferred**, so a proof about some other pair is refused here
        // rather than believed.
        Clause::Eq => {
            let Some(d) = ip.direct() else { return gap(Gap::IndApparatus) };
            let (Some(l), Some(r)) = (arg_tms.get(1), arg_tms.get(2)) else {
                return gap(Gap::IndSpec(*ind, "refl instance"))
            };
            let got = match eq {
                None => inst_all(&d.eq_refl, std::slice::from_ref(l)),
                Some(t) if *t.concl() == Formula::eq(l.clone(), r.clone()) => {
                    inst_all(&d.eq_intro, &[l.clone(), r.clone()])
                        .and_then(|rule| Thm::mp(&rule, t))
                }
                Some(_) => None,
            };
            match got {
                Some(t) => t,
                None => return gap(Gap::IndSpec(*ind, "refl instance")),
            }
        }
        // `Acc.intro α r x (h : ∀ y, r y x → Acc α r y) : Acc α r x` — A1 over
        // the transport, which is [`crate::acc::intro_mem`] and is stated there.
        // The four things it needs are the codomain's own three arguments with
        // their typings and the `h` binder's scope typing; every one of them is
        // read off, and a missing one is this arm's decline rather than the
        // transport's.
        Clause::Acc => {
            let Some(ac) = ip.acc() else { return undecided(Gap::IndApparatus) };
            let (Some(h_mem), 3) = (&step_hyp, arg_tms.len()) else {
                return undecided(Gap::IndSpec(*ind, ACC_INTRO))
            };
            let got = crate::acc::intro_mem(
                ip,
                &ac,
                &store_ty,
                &arg_tms[0],
                &arg_mems[0],
                &arg_tms[1],
                &arg_mems[1],
                &arg_tms[2],
                &arg_mems[2],
                h_mem,
            );
            match got {
                Some(t) => t,
                None => return undecided(Gap::IndSpec(*ind, ACC_INTRO)),
            }
        }
        // `Nat.zero : Nat` and `Nat.succ (n : Nat) : Nat` — `0` and `succ(⟦n⟧)`
        // in `ω`, with the apparatus's own two closed theorems.
        //
        // **Keyed by name and checked by arity, and both are needed.** The name
        // alone would give `⟦Nat.zero⟧ = 0` to a nullary constructor called
        // `zero` of a two-nullary-constructor declaration named `Nat`, which is
        // `Bool` and is not this type; the arity alone would give it to
        // whichever constructor the export happened to list without a field.
        // Together they say: the constructor called `zero` takes no field and
        // the one called `succ` takes exactly one, of the type the nest already
        // typed as `⟦x⟧ ∈ ω`.
        Clause::Nat => {
            let Some(nc) = ip.nat_clause() else { return gap(Gap::IndApparatus) };
            let nat_n = Name::simple("Nat");
            if !args.is_empty() {
                return gap(Gap::IndSpec(*ind, "nat: the carrier takes no arguments"))
            }
            match (&field, *ctor == Name::str(&nat_n, "zero"), *ctor == Name::str(&nat_n, "succ")) {
                (None, true, _) => {
                    value = nc.nat.zero();
                    nc.nat.zero_mem().clone()
                }
                (Some((x, x_mem)), _, true) => {
                    // Through `Interp::mk` rather than `Nat::succ_of`, and the
                    // two are now the same `Term::apply`. They were not always
                    // equivalent: `Interp::skeleton` used to answer `None` on
                    // any subterm mentioning the binder that had not been
                    // entered in a side table only `Interp::mk` wrote to, a
                    // `succ(x)` built directly by `derived` was such a subterm,
                    // and the whole declaration declined with `Gap::Skeleton`.
                    value = ip.mk(nc.nat.core().succ, vec![x.clone()]);
                    match nc.nat.succ_mem_at(x_mem) {
                        Ok(t) => t,
                        Err(_) => return gap(Gap::IndSpec(*ind, NAT_CTOR)),
                    }
                }
                _ => return gap(Gap::IndSpec(*ind, NAT_CTOR)),
            }
        }
    };
    if *mem.concl() != Formula::mem(value.clone(), carrier) {
        return gap(Gap::IndSpec(*ind, "ctor is not about its own codomain"))
    }
    // …and back onto the applied spine, which is what the Lean codomain
    // interprets to.
    let back = match derived::eq_symm(&mut ip.env_mut(), &spine_eq) {
        Some(t) => t,
        None => return gap(Gap::ConvCompose("direct-spine-symm")),
    };
    match ip.retarget_set(&mem, &back) {
        Some(t) => Typing { ty, tm: Some(value), ev: Ev::Proved(t) },
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
            let built = Direct::build(&mut self.env_mut(), &sums).map(std::rc::Rc::new);
            self.direct = built;
            self.direct_failed = self.direct.is_none();
        }
        self.direct.clone()
    }
}

#[cfg(test)]
pub(crate) mod tests {
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
        let us: std::rc::Rc<[Level]> = vec![l].into();
        // `Eq : ∀ (α : Sort l) (a : α), α → Prop`
        let ty = forall(
            sort(l),
            forall(bvar(0), forall(bvar(1), sort(Level::zero()))),
        );
        // `Eq.refl : ∀ (α : Sort l) (a : α), Eq α a a`
        let cty = forall(
            sort(l),
            forall(
                bvar(0),
                crate::expr::app(
                    crate::expr::app(
                        crate::expr::app(konst(e, us), bvar(1)),
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
                name: e,
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(r, cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, e, r)
    }

    #[test]
    fn eq_and_its_constructor_are_interpreted_with_their_typings() {
        let (env, e, r) = eq_env(Level::param(nm("u")));
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let us: std::rc::Rc<[Level]> = vec![Level::zero()].into();

        let t = c.infer_type(&konst(e, us.clone())).expect("infer ⟦Eq⟧");
        let m = t.ev.thm().unwrap_or_else(|| panic!("⟦Eq⟧ has no typing: {:?}", t.ev)).clone();
        assert!(m.hyps().is_empty(), "a closed declaration's typing is unconditional");
        assert!(t.tm.is_some(), "⟦Eq⟧ must interpret");

        let ct = c.infer_type(&konst(r, us)).expect("infer ⟦Eq.refl⟧");
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
        let us: std::rc::Rc<[Level]> = vec![Level::param(nm("u"))].into();
        let ty = forall(
            sort(Level::param(nm("u"))),
            forall(bvar(0), forall(bvar(1), sort(Level::zero()))),
        );
        // `Eq.refl : ∀ (α : Sort u) (a x : α), Eq α a x` — same name, wrong law.
        let cty = forall(
            sort(Level::param(nm("u"))),
            forall(
                bvar(0),
                forall(
                    bvar(1),
                    crate::expr::app(
                        crate::expr::app(
                            crate::expr::app(konst(e, us), bvar(2)),
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
                name: e,
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(r, cty)],
            },
        )
        .expect("accepted");
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let at: std::rc::Rc<[Level]> = vec![Level::zero()].into();
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

    /// `Acc` and `Acc.intro`, as the exports declare them, with the step
    /// hypothesis's relation applied in the order `swapped` asks for.
    ///
    /// `swapped = false` is Lean's own `Acc.intro`; `swapped = true` states the
    /// premise about `r x y` instead of `r y x`, which is the same declaration
    /// with well-foundedness pointing the other way.
    pub(crate) fn acc_env(swapped: bool) -> (Environment, Name, Name) {
        let (a, i) = (nm("Acc"), Name::str(&nm("Acc"), "intro"));
        let u = Level::param(nm("u"));
        let us: std::rc::Rc<[Level]> = vec![u].into();
        // `Acc : ∀ (α : Sort u) (r : α → α → Prop), α → Prop`
        let rel = forall(bvar(0), forall(bvar(1), sort(Level::zero())));
        let ty = forall(sort(u), forall(rel, forall(bvar(1), sort(Level::zero()))));
        // `Acc α r y`, under `α r x y _`.
        let acc_at = |d_a: u32, d_r: u32, d_x: u32| {
            crate::expr::app(
                crate::expr::app(
                    crate::expr::app(konst(a, us.clone()), bvar(d_a)),
                    bvar(d_r),
                ),
                bvar(d_x),
            )
        };
        // `r y x` (or `r x y`) under `α r x y`: `α = #3, r = #2, x = #1, y = #0`.
        let (first, second) = if swapped { (1, 0) } else { (0, 1) };
        let holds = crate::expr::app(crate::expr::app(bvar(2), bvar(first)), bvar(second));
        // `Acc.intro : ∀ (α) (r) (x : α), (∀ y : α, r y x → Acc α r y) → Acc α r x`
        let step = forall(bvar(2), forall(holds, acc_at(4, 3, 1)));
        let cty = forall(
            sort(u),
            forall(rel, forall(bvar(1), forall(step, acc_at(3, 2, 1)))),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: a,
                lparams: vec![nm("u")],
                num_params: 2,
                ty,
                ctors: vec![(i, cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, a, i)
    }

    /// **`Acc.intro`'s typing, end to end.** The corpus reaches this only at the
    /// two σ `117_accRecType` schedules, and only as a constant *occurrence*
    /// inside another declaration's type; this is the same derivation with
    /// nothing else in the file.
    #[test]
    fn acc_and_its_constructor_are_interpreted_with_their_typings() {
        let (env, a, i) = acc_env(false);
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let us: std::rc::Rc<[Level]> = vec![Level::zero()].into();

        let t = c.infer_type(&konst(a, us.clone())).expect("infer ⟦Acc⟧");
        assert!(t.ev.thm().is_some(), "⟦Acc⟧ has no typing: {:?}", t.ev);
        assert!(t.tm.is_some(), "⟦Acc⟧ must interpret");

        let ct = c.infer_type(&konst(i, us)).expect("infer ⟦Acc.intro⟧");
        let cm = ct.ev.thm().unwrap_or_else(|| panic!("⟦Acc.intro⟧ has no typing: {:?}", ct.ev));
        assert!(cm.hyps().is_empty(), "a closed declaration's typing is unconditional");
        let (subj, _) = cm.concl().as_mem().expect("a membership");
        assert_eq!(subj, ct.tm.clone().unwrap(), "the typing must be about ⟦Acc.intro⟧ itself");
    }

    /// **The name is not the evidence, at `Acc`.** A declaration called `Acc`
    /// whose step hypothesis is `r x y` rather than `r y x` is the accessibility
    /// predicate of the *converse* relation, and `derived::acc::acc_intro`'s
    /// `⟨y,x⟩ ∈ R̄` is not what [`crate::acc::AccClause::graph_pair`] hands back
    /// at this instance.
    ///
    /// The interesting half is **which** check refuses. The codomain is
    /// unchanged, so [`ctor_bottom`]'s own final comparison cannot see it and
    /// neither can the arity table: the only thing that can is the transport, so
    /// the gap is pinned by name rather than merely asserted to exist.
    #[test]
    fn a_declaration_named_acc_with_the_relation_reversed_is_declined() {
        let (env, a, i) = acc_env(true);
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let us: std::rc::Rc<[Level]> = vec![Level::zero()].into();
        // The type former still lands — the clause is about `Acc α r x` and the
        // step hypothesis is nowhere in it.
        let t = c.infer_type(&konst(a, us.clone())).expect("infer ⟦Acc⟧");
        assert!(t.ev.thm().is_some(), "the formation clause is untouched by the constructor");

        let ct = c.infer_type(&konst(i, us)).expect("infer ⟦Acc.intro⟧");
        assert_eq!(ct.tm, Some(c.interp().unwrap().point()), "a proof still denotes •");
        assert_eq!(
            ct.ev.gap(),
            Some(&Gap::IndSpec(a, ACC_INTRO)),
            "the reversed relation must be declined by the transport, not by a shape check"
        );
    }
}
