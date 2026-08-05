//! **One indexed minor premise, transported** — the walk both indexed
//! class-(T) eliminators share (`INDEXED-DESIGN.md` §5.1/§5.3).
//!
//! # Interface
//!
//! ```text
//! minor_ix::transport(checker, Site, At, i, src, mvars, Clause)          -> Transported
//! minor_ix::transport_at(checker, Site, At, i, Source, src, mvars, Clause)
//! ```
//!
//! Called from [`crate::rec_ix_prop`], [`crate::rec_ix_dep`] and
//! [`crate::rec_trunc_ix`]. It produces `⊢ MINORᵢ(⟦C⟧)` or `⊢ IDEPᵢ(⟦C⟧,⟦Sᵢ⟧)`
//! at the recursor nest's own terms, plus the binder terms and the substitution
//! the caller needs to compare that against the statement `derived` rebuilds.
//!
//! [`transport`] is the eliminator nest's spelling and reads its Lean-syntax
//! frame off the checker telescope; [`transport_at`] takes that frame as a
//! [`Source`]. The split is the same one [`crate::zoneb::ind_spine`] /
//! [`crate::zoneb::ind_spine_at`] makes one level down, and for the same
//! reason — see [`Source`].
//!
//! # Why one module and not one per clause
//!
//! The two rules differ in three places and agree everywhere else, and
//! `derived` made the agreement structural rather than incidental:
//! `IDEPᵢ`'s antecedent **is**
//! [`minor_atoms_at`](derived::inductive::family::minor_atoms_at), the same
//! builder [`IndexedPropRecursor`](derived::inductive::family::IndexedPropRecursor)
//! uses, at the bound `vⱼ` instead of at `•`. Two thirds of the antecedent is
//! literally the other rule's. Writing that twice is the drift this project has
//! paid for four times, so [`Clause`] is the whole of the difference:
//!
//! | | `Prop` motive | value motive |
//! |---|---|---|
//! | what the rule quantifies | `k + m` fields | `k + m` fields **and** the `m` `vⱼ` |
//! | the induction-hypothesis argument | `•` — the IH is an *atom*, not a binder | the binder itself |
//! | the conclusion's subject | `•`, by proof irrelevance | `Sᵢ⟪f⃗⟫v⃗`, as the walk left it |
//!
//! Everything else — the checker-telescope walk, the three set-swaps, the
//! close-time domain rewrite, the prenexing — is one piece of code.
//!
//! # The walk opens *checker* binders, and that is the whole design
//!
//! [`crate::rec_dep::minor_at`] walks a minor's Π-interpretation with a private
//! [`Scopes`](crate::scope::Scopes) and never touches the Lean type. That
//! cannot work at `ni > 0`, and the reason is one atom:
//!
//! ```text
//! rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))         the atom `minor_atoms_at` states
//! rⱼ ∈ ⟦T p⃗ d⃗⟧                   the domain the binder was opened at
//! ```
//!
//! The two sets differ by one β down the type former's own λ-nest, and β
//! consumes **one membership per level** — `⟦dₖ⟧ ∈ ⟦Iₖ⟧`, per index of the
//! recursive argument. Nothing hands those over: `d⃗ᵢⱼ`'s defining axioms give
//! the *terms* and not the memberships, and the recursive argument's index
//! expressions live inside the minor's Lean type, where no interpretation walk
//! can infer anything.
//!
//! So the walk opens the minor's Lean binders on the **checker's own**
//! telescope, with
//! [`Checker::push_interpreted`](crate::kernel::Checker::push_interpreted) at
//! the domain the Π-interpretation already recorded. Everything
//! [`crate::ctor_ix`] does at the bottom of a constructor's nest is then
//! available one level up and unchanged:
//! [`crate::zoneb::ind_spine_at`] reads the index expressions off the binder's
//! type and [`crate::ctor_ix::infer_indices`] *infers* them, which is the only
//! place `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` exists.
//!
//! **That reason is about Lean syntax, not about a telescope.** It says the
//! minor's *type* must be in hand and that binders must be open where inference
//! can run — neither of which requires the type to have been read off the
//! eliminator's own nest, nor the parameters to be pinned `BVar`s. [`Source`]
//! is that separation, and it is what lets a ι rule at a use site share this
//! walk instead of growing a second copy of it.
//!
//! # The domain swap happens at each binder's close, not afterwards
//!
//! `rec_dep`'s conversion of the interleaved `∀w. (w ∈ D → …)` family into the
//! prenex `∀f⃗. (⋀A → …)` needs, per level, an implication `⋀A → (w ∈ D)`, and
//! it builds that from an **unconditional** equation between the two spellings
//! of `D`. Here the equation is a β step and carries the very hypotheses the
//! scopes introduced, so a `Γ`-carrying implication would survive to the final
//! `gen_all_checked` and be refused there: the bound variable is free in a
//! remaining hypothesis, which is exactly the discipline I2 exists to enforce.
//!
//! [`domain_swap`] moves the equation to where its `Γ` is still legal. Each
//! scope discharges to `∀w. (w ∈ ⟦D⟧ → φ)` and is *then* rewritten, by one
//! Leibniz, into `∀w. (w ∈ D_derived → φ)` — innermost first, while every outer
//! scope is still open, so the hypotheses the equation carries (which mention
//! only strictly earlier binders) are discharged by the closes above it. What
//! comes out has no `Γ` beyond the recursor nest's own, the antecedents are
//! `minor_atoms_at`'s on the nose, and the prenexing loop is `conj_proj` with
//! no retargeting left to do.
//!
//! It is the same move `zoneb`'s summand-leg close makes, at the same shape.
//!
//! # The atom list is Lean-positional, so level `l` answers atom `l`
//!
//! D7 quantifies in the constructor's **declared** field order and states the
//! atoms in that order, then the `mᵢ` induction hypotheses; D8 keeps both, and
//! says so as a contract rather than as a coincidence. A minor's
//! Π-interpretation unfolds in exactly that order. So there is no permutation
//! in this module at all — no `order_index`, no mask read — and the `Slot` mask
//! is consulted only to decide *which kind* of equation a level needs.
//!
//! # Three moves between a set the interpretation names and one `derived` names
//!
//! | level | the atom | the binder's domain | the equation |
//! |---|---|---|---|
//! | `Slot::Plain` | `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` | `⟦βⱼ⟧` | `field_abbrev`, instantiated |
//! | `Slot::Rec` | `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` | `⟦T p⃗ d⃗⟧` | `index_congr`, then β |
//! | IH | `vⱼ ∈ app(m,d⃗ᵢⱼ,rⱼ)` | `⟦C d⃗ rⱼ⟧` | `motive_congr_of` |
//!
//! and the conclusion travels the same way — `⟦C e⃗ᵢ (T.ctorᵢ p⃗ y⃗ r⃗)⟧` onto
//! `app(m, e⃗ᵢ, ctorᵢ(y⃗,r⃗))`, which is *two* positions of one spine moving at
//! once and is why
//! [`motive_congr`](derived::inductive::family::motive_congr) covers the
//! subject as well: the constructor term sits inside an **argument** of the
//! membership, so a subject retarget cannot reach it. That equation carries the
//! constructor nest's own `Γ`, which `motive_congr_of` takes.
//!
//! # Nothing here searches
//!
//! The index expressions come from the checker's own telescope and are
//! inferred; every equation is a defining axiom this declaration's translation
//! kept; and each finished premise is compared **by the caller** against what
//! `derived` states, rebuilt at these very terms.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::motive_congr_of;
use derived::inductive::Slot;

use crate::ev::{Cause, Gap};
use crate::expr::{Expr, Name, E};
use crate::interp::{Interp, PiShape};
use crate::kernel::Checker;
use crate::rec_dep::{gen_all_checked, hyp_inst, subst_f};
use crate::scope::Closed;
use crate::zoneb::IndexedTranslation;

const DISAGREE: &str = "indexed minor: the recursor and the carrier disagree";
const SCOPES: &str = "indexed minor: a binder did not close";
const SORTS: &str = "indexed minor: the conclusion is not a Prop at a Prop motive";

/// Which of §6.2's two clauses is being transported — the whole difference
/// between the `Prop`-motive rule and the value one; see the module header.
#[derive(Clone, Copy)]
pub(crate) struct Clause {
    /// How many variables the rule quantifies: `k + m` at a `Prop` motive,
    /// `k + 2m` at a value one, and `k` — the **plain** fields alone — at the
    /// class-(P) rule, where a recursive field is a proof and contributes an
    /// atom rather than a binder.
    pub nvars: usize,
    /// Whether the conclusion's subject must be moved onto `•`.
    pub proof: bool,
    /// The rule's own motive variable, which `src` is stated at.
    pub motive: FreeVar,
    /// **The class-(P) rule**, whose three differences from the `Prop`-motive
    /// class-(T) one are all consequences of the same fact — a recursive
    /// argument of a `Prop`-valued family is a *proof*, so it is `•`:
    ///
    /// | | class (T), `Prop` motive | class (P) |
    /// |---|---|---|
    /// | which levels the rule binds | the first `k + m` | the `Slot::Plain` ones |
    /// | a `Slot::Rec` level's atom | `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` | `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖` |
    /// | the conclusion's third argument | `ctorᵢ(y⃗,r⃗)` | `•` |
    ///
    /// The bound levels are no longer a *prefix*, which is why this is a flag
    /// on the clause and not a count: at an interleaved mask
    /// (`Plain, Rec, Plain, Rec`) levels 0 and 2 are bound and 1 and 3 are not.
    pub trunc: bool,
}

/// Which translation the walk reads its symbols and axioms out of.
///
/// The two indexed carriers are different objects with the same *interface* to
/// this walk — a spec, the declaration's parameter variables, the index
/// abbreviations' axioms, the field abbreviations, and one `FnSym` for the
/// carrier at `p⃗ ++ x⃗`. Everything below is stated against that interface, and
/// the three places where class (P) genuinely diverges are marked with
/// [`Clause::trunc`] rather than by holding two copies of the walk.
#[derive(Clone)]
pub(crate) enum Fam {
    /// [`crate::zoneb::build_indexed`]'s — the §5.2 carrier itself.
    ClassT(Rc<IndexedTranslation>),
    /// [`crate::class_p_ix`]'s — the truncation of it.
    ClassP(Rc<crate::class_p_ix::ClassPIx>),
}

impl Fam {
    pub(crate) fn spec(&self) -> &derived::inductive::family::IndexedDeclSpec {
        match self {
            Fam::ClassT(t) => &t.ii.spec,
            Fam::ClassP(p) => &p.walk.spec,
        }
    }

    pub(crate) fn params(&self) -> &[FreeVar] {
        match self {
            Fam::ClassT(t) => &t.base.params,
            Fam::ClassP(p) => &p.params,
        }
    }

    fn ax(&self) -> &crate::zoneb::IndexAx {
        match self {
            Fam::ClassT(t) => &t.ax,
            Fam::ClassP(p) => &p.walk.ax,
        }
    }

    fn field_abbrev(&self) -> &[Vec<Thm>] {
        match self {
            Fam::ClassT(t) => &t.field_abbrev,
            Fam::ClassP(p) => &p.walk.field_abbrev,
        }
    }

    /// The class-(T) translation, for the two callers that need more of it than
    /// this walk does — `rec_ix_dep` reads the skeleton's `wty`, and both read
    /// the memoised rule off the `IndexedInductive`.
    pub(crate) fn class_t(&self) -> Option<&Rc<IndexedTranslation>> {
        match self {
            Fam::ClassT(t) => Some(t),
            Fam::ClassP(_) => None,
        }
    }

    /// The class-(P) translation, for the eliminator that needs the truncation
    /// and its abbreviation as well as what this walk reads.
    pub(crate) fn class_p(&self) -> Option<&Rc<crate::class_p_ix::ClassPIx>> {
        match self {
            Fam::ClassT(_) => None,
            Fam::ClassP(p) => Some(p),
        }
    }
}

impl Clause {
    /// **Whether level `l` of the minor's Lean telescope is a binder the rule
    /// quantifies**, or one it instantiates at `•`.
    ///
    /// At class (T) the bound levels are a *prefix* — the `k + m` fields at a
    /// `Prop` motive, those and the `m` `vⱼ` at a value one — so a count says
    /// it. At class (P) they are the `Slot::Plain` positions, which an
    /// interleaved mask (`Plain, Rec, Plain, Rec`) makes non-contiguous, so a
    /// count cannot. `mvars` is consumed in this predicate's order.
    fn binds(&self, cs: &derived::inductive::CtorSpec, l: usize) -> bool {
        if self.trunc {
            cs.order.get(l).map(|s| *s == Slot::Plain).unwrap_or(false)
        } else {
            l < self.nvars
        }
    }
}

/// The level of the `j`-th `Slot::Rec` in the declared mask.
fn rec_level(cs: &derived::inductive::CtorSpec, j: usize) -> Option<usize> {
    let mut seen = 0;
    for (q, sl) in cs.order.iter().enumerate() {
        if *sl == Slot::Rec {
            if seen == j {
                return Some(q)
            }
            seen += 1;
        }
    }
    None
}

/// Which eliminator is being built, and everything read before a binder opens.
pub(crate) struct Site {
    pub ind: Name,
    pub inst: Vec<u32>,
    /// The eliminator's own name and instantiation — the key
    /// [`IndApparatus::dep_elims`](crate::interp::IndApparatus) stores the nest
    /// bottom's abbreviation under. Unused by the walk; carried because the
    /// bottom is the only place that has it and the only place that mints.
    pub rec: Name,
    pub rec_inst: Vec<u32>,
    /// The constructors' names, in declaration order.
    pub ctors: Vec<Name>,
    pub np: usize,
    pub n: usize,
    pub ni: usize,
    /// `np + 1 + n + ni + 1` — parameters, motive, minors, indices, major.
    pub depth: usize,
    pub codomain: E,
    pub fam: Fam,
    /// The reason **this clause** reports when a minor does not transport. The
    /// two eliminators are two rows of the ledger and must stay two, so the
    /// shared code takes the string rather than minting a shared one.
    pub minor_gap: &'static str,
}

/// What the nest's own scopes hold at the bottom, plus the store reads.
pub(crate) struct At {
    /// `⟦p⃗⟧`.
    pub ps: Vec<Term>,
    /// Their scope typings.
    pub param_mems: Vec<Thm>,
    /// `⟦C⟧`.
    pub c_tm: Term,
    /// `⟦S⃗⟧` and their scope typings.
    pub s_tms: Vec<Term>,
    pub s_mems: Vec<Thm>,
    /// `⟦x⃗⟧`, the index binders, with their typings.
    pub xs: Vec<Term>,
    pub x_mems: Vec<Thm>,
    /// `⟦t⟧` and `⟦t⟧ ∈ ⟦T p⃗ x⃗⟧`.
    pub t_tm: Term,
    pub t_mem: Thm,
    /// `⟦T⟧` and each `⟦T.ctorᵢ⟧`, as the store holds them.
    pub former: Term,
    pub ctor_formers: Vec<Term>,
    /// `⟦C x⃗ t⟧`, the set the bottom's membership must be about.
    pub goal: Term,
    /// The nest's own kernel variables, for naming the eliminator's term.
    pub vars: Vec<FreeVar>,
    /// `⟦p⃗⟧, ⟦C⟧, ⟦S⃗⟧, ⟦x⃗⟧, ⟦t⟧`, outermost first — the same list.
    pub all: Vec<Term>,
}

/// **Where the minor's Lean telescope is read from, and what the declaration's
/// parameters look like inside it.**
///
/// The walk needs two things out of Lean syntax and nothing else: the minor's
/// own type, and — at a `Slot::Rec` level — a way to recognise the recursive
/// field's type as *this declaration applied to these parameters*, so that the
/// index expressions after them can be read off and inferred
/// ([`crate::zoneb::ind_spine_at`]).
///
/// At the eliminator's own nest both come from the checker's telescope and the
/// parameters are pinned `BVar`s at a known depth; [`from_telescope`] is that
/// case, and it is the only one the three eliminator routes present. A **use**
/// site — a ι rule firing at arbitrary arguments — has the same two things in a
/// different frame: the minor's type is the recursor's declared binder with the
/// actual arguments substituted, and the parameters are arbitrary expressions.
/// Making them a parameter is what separates the walk's *reason* for opening
/// checker binders (the index expressions live in Lean syntax and nowhere else)
/// from the nest-shaped implementation of it, which is incidental.
///
/// **Frame contract.** `mty` and `params` are stated in the context the walk
/// *starts* in — the checker's telescope with no binder of this minor open yet.
/// The walk shifts `params` itself as it descends.
pub(crate) struct Source {
    /// The minor's Lean type.
    pub mty: E,
    /// `p⃗` as they occur inside `mty`, outermost first. Length must be
    /// [`Site::np`].
    pub params: Vec<E>,
}

impl Source {
    /// The eliminator nest's own reading: the minor binder's type off the
    /// checker telescope, and the parameters as the pinned `BVar`s the nest
    /// opened them at.
    ///
    /// The type is read **before** any of the minor's own binders is open, so
    /// that `local_type` does the de Bruijn shift and this module does none.
    fn from_telescope(c: &Checker<'_, '_>, site: &Site, i: usize) -> Option<Source> {
        let idx = u32::try_from(site.depth.checked_sub(1 + site.np + 1 + i)?).ok()?;
        let mty = c.local_type(idx).ok()?;
        // The nest is `site.depth` deep and the parameters are its outermost,
        // so they sit at `BVar(site.depth-1) … BVar(site.depth-np)`.
        let np = u32::try_from(site.np).ok()?;
        let d = u32::try_from(site.depth.checked_sub(site.np)?).ok()?;
        Some(Source { mty, params: crate::expr::bvars(np, d) })
    }
}

/// One transported minor premise, and what the caller needs to check it.
pub(crate) struct Transported {
    /// `⊢ MINORᵢ` / `⊢ IDEPᵢ` at the nest's own terms.
    pub thm: Thm,
    /// The `k + 2m` binder terms, in Lean order. Read by a caller that needs
    /// the fields after the fact; the value clause does not.
    #[allow(dead_code)]
    pub ws: Vec<Term>,
    /// The substitution the caller's comparison is under: the declaration's
    /// parameters at `⟦p⃗⟧`, the motive at `⟦C⟧`, and each of `mvars` at its
    /// binder.
    pub sub: Vec<(FreeVar, Term)>,
}

/// What the walk leaves behind at the bottom of one minor's telescope.
struct Walked {
    ws: Vec<Term>,
    wvs: Vec<FreeVar>,
    /// Per level, `⊢ Dᵈᵉʳⁱᵛᵉᵈ = ⟦D⟧` — the equation [`domain_swap`] closes with.
    eqs: Vec<Thm>,
    /// `Γ ⊢ subject ∈ app(m, e⃗ᵢ, ctorᵢ(y⃗,r⃗))`, at `derived`'s spelling.
    concl: Thm,
    /// The atom list at this call's own terms.
    atoms: Vec<Formula>,
    sub: Vec<(FreeVar, Term)>,
}

/// `⊢ MINORᵢ` / `⊢ IDEPᵢ` at mini's own terms, from the minor binder's scope
/// typing.
///
/// `src` is the rule's own atom list, at the rule's own variables; `mvars` the
/// variables it quantifies, position for position with the constructor's Lean
/// binders. The caller supplies both because only it knows which rule it is
/// discharging — and then compares the result against that rule's own
/// statement, which is what pins the quantifier prefix and the atom order.
pub(crate) fn transport(
    c: &mut Checker<'_, '_>,
    site: &Site,
    at: &At,
    i: usize,
    src: &[Formula],
    mvars: &[FreeVar],
    clause: Clause,
) -> Result<Transported, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let from = Source::from_telescope(c, site, i).ok_or_else(|| bad(site.minor_gap))?;
    transport_at(c, site, at, i, &from, src, mvars, clause)
}

/// [`transport`], with the Lean-syntax frame supplied rather than read off the
/// eliminator nest's telescope — see [`Source`].
#[allow(clippy::too_many_arguments)]
pub(crate) fn transport_at(
    c: &mut Checker<'_, '_>,
    site: &Site,
    at: &At,
    i: usize,
    from: &Source,
    src: &[Formula],
    mvars: &[FreeVar],
    clause: Clause,
) -> Result<Transported, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let cs = site.fam.spec().base.ctors.get(i).ok_or_else(|| bad(DISAGREE))?.clone();
    let (k, m) = (cs.args.len(), cs.recs);
    let nlev = k + 2 * m;
    if src.len() != nlev || mvars.len() != clause.nvars || clause.nvars > nlev {
        return Err(bad(DISAGREE))
    }
    // **What this guard owns, and it is a diagnosis and not a soundness
    // claim.** A wrong-length `params` is caught by `ind_spine_at` at the first
    // `Slot::Rec` level — and *only* there, because nothing else in the walk
    // reads the parameters. So at a constructor with no recursive field a bad
    // frame is invisible, and the transport that fails is the next
    // constructor's. This makes it the first one's.
    if from.params.len() != site.np {
        return Err(bad(DISAGREE))
    }

    // The walk leaves `nlev` checker binders open whether it succeeds or not,
    // and they must come off the telescope either way.
    let mut opened = 0usize;
    let walked = walk(c, site, at, i, &cs, from, src, mvars, clause, &mut opened);
    let mut closed: Vec<Closed> = Vec::with_capacity(opened);
    for _ in 0..opened {
        match c.close_one() {
            Some(cl) => closed.push(cl),
            None => return Err(bad(SCOPES)),
        }
    }
    let w = walked?;
    if closed.len() != nlev {
        return Err(bad(SCOPES))
    }

    // ── discharge, innermost first, swapping each domain as it closes ───────
    let mut chain = w.concl;
    for (l, cl) in closed.iter().enumerate() {
        let level = nlev - 1 - l;
        let Some(ip) = c.interp() else { return Err(Gap::SymbolicLevel) };
        chain = domain_swap(ip, cl, &w.eqs[level], &chain).ok_or_else(|| bad(site.minor_gap))?;
    }

    // ── prenex: re-instantiate and discharge each atom from the conjunction ──
    //
    // Level `l` answers atom `l`; the atom list is Lean-positional, so there is
    // no permutation. A `Prop` rule's induction-hypothesis levels are
    // instantiated at `•` rather than at their own binder, because there the
    // hypothesis is an atom of `Aᵢ` and not something `MINORᵢ` quantifies.
    let point = {
        let Some(ip) = c.interp() else { return Err(Gap::SymbolicLevel) };
        ip.point()
    };
    let hyp = derived::conj_of(&w.atoms);
    let mut cur = match &hyp {
        None => chain,
        Some(h) => derived::a1i(&chain, h.clone()),
    };
    for l in 0..nlev {
        let arg = if clause.binds(&cs, l) { w.ws[l].clone() } else { point.clone() };
        cur = hyp_inst(&cur, &arg).ok_or_else(|| bad(site.minor_gap))?;
        let ante = cur
            .concl()
            .as_imp()
            .and_then(|(_, r)| r.as_imp())
            .map(|(a, _)| a)
            .ok_or_else(|| bad(site.minor_gap))?;
        if ante != w.atoms[l] {
            return Err(bad(site.minor_gap))
        }
        let step = derived::conj_proj(&w.atoms, l).ok_or_else(|| bad(site.minor_gap))?;
        cur = derived::hyp_mp(&cur, &step).ok_or_else(|| bad(site.minor_gap))?;
    }
    // **The `∀y⃗` prefix is the bound levels', not a prefix of the levels.** At
    // class (T) the two coincide and slicing said it; at class (P) with an
    // interleaved mask (`Plain, Rec, Plain, Rec`) the bound levels are 0 and 2,
    // and `wvs[..nvars]` would generalise over the *recursive* binder at level
    // 1 and leave the second plain field free. `Pe` in
    // `crate::class_p_ix::tests::cells` is the shortest declaration that can
    // tell the two apart, and it is the only thing in the repository that does.
    let bound: Vec<FreeVar> =
        (0..nlev).filter(|l| clause.binds(&cs, *l)).map(|l| w.wvs[l]).collect();
    if bound.len() != clause.nvars {
        return Err(bad(DISAGREE))
    }
    let thm = gen_all_checked(&bound, &cur).ok_or_else(|| bad(site.minor_gap))?;
    Ok(Transported { thm, ws: w.ws, sub: w.sub })
}

/// Open every binder of one minor's Lean telescope, applying the minor as it
/// goes, and stop at the conclusion.
#[allow(clippy::too_many_arguments)]
fn walk(
    c: &mut Checker<'_, '_>,
    site: &Site,
    at: &At,
    i: usize,
    cs: &derived::inductive::CtorSpec,
    from: &Source,
    src: &[Formula],
    mvars: &[FreeVar],
    clause: Clause,
    opened: &mut usize,
) -> Result<Walked, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let fail = || bad(site.minor_gap);
    let ni = site.ni;
    let (k, m) = (cs.args.len(), cs.recs);
    let nlev = k + 2 * m;

    let mut sub: Vec<(FreeVar, Term)> =
        site.fam.params().iter().copied().zip(at.ps.iter().cloned()).collect();
    sub.push((clause.motive, at.c_tm.clone()));

    let mut ws: Vec<Term> = Vec::with_capacity(nlev);
    let mut wvs: Vec<FreeVar> = Vec::with_capacity(nlev);
    let mut wmems: Vec<Thm> = Vec::with_capacity(nlev);
    let mut eqs: Vec<Thm> = Vec::with_capacity(nlev);
    // `⟦d⃗ᵢⱼ⟧` with their typings, per recursive slot, as the walk infers them.
    let mut childs: Vec<Vec<(Term, Thm)>> = Vec::with_capacity(m);
    // `⊢ ⟦T p⃗ d⃗⟧ ∈ ⟦Sort 0⟧` per recursive slot — class (P) only, and read at
    // the `Slot::Rec` level where that binder's Lean type is in hand.
    let mut rec_tys: Vec<Thm> = Vec::with_capacity(m);
    let mut ys: Vec<Term> = Vec::with_capacity(k);

    let mut f_mem = at.s_mems[i].clone();
    let mut cur = from.mty.clone();
    let (mut plains, mut recs, mut bound) = (0usize, 0usize, 0usize);
    for (l, atom) in src.iter().enumerate().take(nlev) {
        let Expr::Forall { ty: dom_e, body } = &*cur.clone() else { return Err(fail()) };
        let (dom_e, body) = (dom_e.clone(), body.clone());

        // The set the interpretation opened this binder at, and the one the
        // rule states the level's atom in. The rule's set mentions only
        // *earlier* fields, so the partial substitution is complete for it.
        let f_set = f_mem.concl().as_mem().ok_or_else(fail)?.1;
        let shape = {
            let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
            ip.as_pi(&f_set).ok_or_else(fail)?
        };
        let idom = shape.dom();
        let ddom = subst_f(atom, &sub).as_mem().ok_or_else(fail)?.1;

        // The equation between the two, by the level's kind.
        let eq = if l < k + m {
            match cs.order[l] {
                Slot::Plain => {
                    let mut a = at.ps.clone();
                    a.extend(ys.iter().cloned());
                    let ax = site
                        .fam
                        .field_abbrev()
                        .get(i)
                        .and_then(|r| r.get(plains))
                        .ok_or_else(fail)?;
                    derived::inst_all(ax, &a).ok_or_else(fail)?
                }
                Slot::Rec => {
                    // The recursive argument's index expressions come off its
                    // own binder type and are **inferred** here — the only
                    // place `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` exists.
                    //
                    // **The de Bruijn step.** `from.params` is stated in the
                    // frame the walk started in, and `dom_e` is read under the
                    // `l` binders opened since, so the parameters must be
                    // shifted past them before they can be compared. At the
                    // eliminator's own nest they are `BVar(site.depth-1-q)` and
                    // this reproduces the old `d = site.depth + l - np`
                    // arithmetic exactly; at a use site they are arbitrary
                    // expressions and the shift is the only thing that changes.
                    let lifted: Vec<E> = from
                        .params
                        .iter()
                        .map(|p| crate::expr::shift(p, 0, u32::try_from(l).unwrap_or(u32::MAX)))
                        .collect();
                    let ds_e = crate::zoneb::ind_spine_at(&site.ind, &dom_e, &lifted, ni)
                        .ok_or_else(fail)?;
                    let ds = crate::ctor_ix::infer_indices(c, &ds_e).ok_or_else(fail)?;
                    let before =
                        site.fam.spec().plains_before(i, recs).ok_or_else(fail)?;
                    let mut a = at.ps.clone();
                    a.extend(ys.get(..before).ok_or_else(fail)?.iter().cloned());
                    let axs = site
                        .fam
                        .ax()
                        .ctors
                        .get(i)
                        .and_then(|cx| cx.rec_args.get(recs))
                        .ok_or_else(fail)?;
                    // **A recursive field of a `Prop` family is a proof of the
                    // truncation**, so the binder's own typing is kept here for
                    // the induction hypothesis below, which has to move that
                    // proof onto `•` before it can name the atom.
                    if clause.trunc {
                        let dt = c.infer_type(&dom_e).map_err(|_| Gap::Classifier)?;
                        rec_tys.push(dt.ev.thm().cloned().ok_or_else(fail)?);
                    }
                    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
                    let eq = match &site.fam {
                        // `ind(p⃗,d⃗ᵢⱼ) = ⟦T p⃗ d⃗⟧`: one congruence over the
                        // carrier symbol, then β back down the former's nest.
                        Fam::ClassT(t) => {
                            let cong = crate::ctor_ix::index_congr(
                                ip,
                                t.ii.carrier.ty,
                                &at.ps,
                                &ds,
                                axs,
                                &a,
                            )
                            .ok_or_else(fail)?;
                            let mut sa = at.ps.clone();
                            sa.extend(ds.iter().map(|(t, _)| t.clone()));
                            let mut sm = at.param_mems.clone();
                            sm.extend(ds.iter().map(|(_, t)| t.clone()));
                            let (_, beta) =
                                ip.beta_spine(&at.former, &sa, &sm).ok_or_else(fail)?;
                            let back = derived::eq_symm(&mut ip.env, &beta).ok_or_else(fail)?;
                            derived::eq_trans(&mut ip.env, &cong, &back).ok_or_else(fail)?
                        }
                        // `‖ind(p⃗,d⃗ᵢⱼ)‖ = ⟦T p⃗ d⃗⟧`: the same two steps and one
                        // more, since `⟦T p⃗ d⃗⟧` is the *truncation*. The
                        // composite is `class_p_ix::carrier_eq`, stated there
                        // because the constructor's codomain travels on it too,
                        // and taken the other way round here.
                        Fam::ClassP(p) => {
                            let fwd = crate::class_p_ix::carrier_eq(
                                ip,
                                p,
                                &at.former,
                                &at.ps,
                                &at.param_mems,
                                &ds,
                                axs,
                                &a,
                            )
                            .ok_or_else(fail)?;
                            derived::eq_symm(&mut ip.env, &fwd).ok_or_else(fail)?
                        }
                    };
                    // The drift check, and it is the same one at both routes:
                    // the equation's right-hand side must be the very set this
                    // binder was opened at. It is made below, against `idom`,
                    // for every level.
                    childs.push(ds);
                    eq
                }
            }
        } else {
            // An induction hypothesis: the motive's spine at the child's own
            // indices, and only the indices move.
            let j = l - (k + m);
            let ds = childs.get(j).ok_or_else(fail)?.clone();
            let before = site.fam.spec().plains_before(i, j).ok_or_else(fail)?;
            let mut a = at.ps.clone();
            a.extend(ys.get(..before).ok_or_else(fail)?.iter().cloned());
            let axs = site
                .fam
                .ax()
                .ctors
                .get(i)
                .and_then(|cx| cx.rec_args.get(j))
                .ok_or_else(fail)?;
            if axs.len() != ni || ds.len() != ni {
                return Err(fail())
            }
            let child = child_term(cs, &ws, j).ok_or_else(fail)?;
            // **The third argument of the motive spine.** At class (T) the
            // induction hypothesis is about the recursive *binder* `rⱼ` and the
            // argument does not move. At class (P) that binder is a proof, and
            // the rule states the hypothesis at `•` — so the last equation is
            // proof irrelevance, `⊢ rⱼ = •`, out of the binder's own typing
            // (kept at the `Slot::Rec` level above, where its Lean type was in
            // hand) and the membership the scope holds.
            let child_mem = if clause.trunc {
                let q = rec_level(cs, j).ok_or_else(fail)?;
                Some((rec_tys.get(j).cloned().ok_or_else(fail)?, wmems.get(q).cloned().ok_or_else(fail)?))
            } else {
                None
            };
            let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
            let s = ip.prelude.tower.sums.clone();
            let mut ceqs: Vec<Thm> = Vec::with_capacity(ni + 1);
            for (q, ax) in axs.iter().enumerate() {
                let step = derived::inst_all(ax, &a).ok_or_else(fail)?;
                if step.concl().as_eq().ok_or_else(fail)?.1 != ds[q].0 {
                    return Err(fail())
                }
                ceqs.push(step);
            }
            match child_mem {
                None => ceqs.push(Thm::eq_refl(child)),
                Some((ty_mem, mem)) => {
                    let pt = ip.point_of_proof(&ty_mem, &mem).ok_or_else(fail)?;
                    ceqs.push(derived::eq_symm(&mut ip.env, &pt).ok_or_else(fail)?);
                }
            }
            motive_congr_of(&mut ip.env, &s, &at.c_tm, &ceqs).ok_or_else(fail)?
        };
        if eq.concl().as_eq() != Some((ddom, idom.clone())) {
            return Err(fail())
        }
        eqs.push(eq);

        // Open the binder on the checker's own telescope, at the domain the
        // interpretation recorded, so that inference under it is Lean's.
        c.push_interpreted(dom_e, idom);
        *opened += 1;
        let (wt, wm) = c.binder(0).ok_or_else(fail)?;
        let wv = c.scope_vars(1).and_then(|v| v.first().copied()).ok_or_else(fail)?;

        let f_tm = f_mem.concl().as_mem().ok_or_else(fail)?.0;
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let out = match &shape {
            PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, &wt, &f_mem, &wm),
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &f_mem, &wt, &wm),
        }
        .ok_or_else(fail)?;
        f_mem = out;

        if clause.binds(cs, l) {
            sub.push((*mvars.get(bound).ok_or_else(fail)?, wt.clone()));
            bound += 1;
        }
        if l < k + m {
            match cs.order[l] {
                Slot::Plain => {
                    ys.push(wt.clone());
                    plains += 1
                }
                Slot::Rec => recs += 1,
            }
        }
        ws.push(wt);
        wvs.push(wv);
        wmems.push(wm);
        cur = body;
    }
    if plains != k || recs != m {
        return Err(bad(DISAGREE))
    }

    // ── the conclusion ──────────────────────────────────────────────────────
    //
    // At a `Prop` motive a field-free constructor's minor is a proof
    // *variable*: no application rule fired, so the subject is still the minor
    // binder's own scope variable and §6.2 gives it `•` by proof irrelevance.
    // Where a rule did fire it is `cond_app`, whose subject is `•` already, and
    // this step is skipped. At a value motive the subject is `Sᵢ⟪f⃗⟫v⃗` and
    // stays as it is.
    let concl_ev = c.infer_type(&cur).map_err(|_| Gap::Classifier)?;
    let point = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        ip.point()
    };
    let (subj, cset) = f_mem.concl().as_mem().ok_or_else(fail)?;
    if clause.proof && subj != point {
        let ty_mem = concl_ev.ev.thm().cloned().ok_or_else(fail)?;
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        if *ty_mem.concl() != Formula::mem(cset.clone(), ip.sort(0)) {
            return Err(bad(SORTS))
        }
        let pt = ip.point_of_proof(&ty_mem, &f_mem).ok_or_else(fail)?;
        let back = derived::eq_symm(&mut ip.env, &pt).ok_or_else(fail)?;
        f_mem = ip.retarget_subject(&f_mem, &back).ok_or_else(fail)?;
    }

    // `⟦C e⃗ᵢ (T.ctorᵢ p⃗ y⃗ r⃗)⟧` onto `app(m, e⃗ᵢ(p⃗,y⃗), ctorᵢ(y⃗,r⃗))`: `ni`
    // index equations and the subject, all in one spine.
    let fields: Vec<Term> = ws[..k + m].to_vec();
    let mut e_args = at.ps.clone();
    e_args.extend(ys.iter().cloned());
    let e_axs = site.fam.ax().ctors.get(i).map(|cx| &cx.result).ok_or_else(fail)?;
    if e_axs.len() != ni {
        return Err(bad(DISAGREE))
    }
    let mut sp_args = at.ps.clone();
    sp_args.extend(fields.iter().cloned());
    let mut sp_mems = at.param_mems.clone();
    sp_mems.extend(wmems[..k + m].iter().cloned());

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let mut ceqs: Vec<Thm> = Vec::with_capacity(ni + 1);
    for ax in e_axs {
        let fwd = derived::inst_all(ax, &e_args).ok_or_else(fail)?;
        ceqs.push(derived::eq_symm(&mut ip.env, &fwd).ok_or_else(fail)?);
    }
    // **The conclusion's third argument.** At class (T) it is the constructor
    // term, and getting from `⟦T.ctorᵢ p⃗ y⃗ r⃗⟧` to `ctorᵢ(y⃗,r⃗)` is β down the
    // constructor's own nest and then the abbreviation `ctor_ix` minted. At
    // class (P) the constructor **is** `•` — its codomain is a `Prop`, so the
    // whole constant is a proof and `zoneb::trunc_ctor_bottom`'s bottom term is
    // the point — and the rule's argument is `•` too, so the argument does not
    // move and there is no constructor abbreviation to mint or to keep.
    let last = match site.fam.class_t() {
        Some(t) => {
            let (_, cbeta) =
                ip.beta_spine(&at.ctor_formers[i], &sp_args, &sp_mems).ok_or_else(fail)?;
            // Over `p⃗ ++ f⃗`, which is `sp_args` — see `ctor_ix::ctor_abbrevs`.
            let cax = derived::inst_all(&t.ctor_abbrev[i].1, &sp_args).ok_or_else(fail)?;
            derived::eq_trans(&mut ip.env, &cbeta, &cax).ok_or_else(fail)?
        }
        None => Thm::eq_refl(ip.point()),
    };
    ceqs.push(last);
    let s = ip.prelude.tower.sums.clone();
    let move_eq = motive_congr_of(&mut ip.env, &s, &at.c_tm, &ceqs).ok_or_else(fail)?;
    let concl = ip.retarget_set(&f_mem, &move_eq).ok_or_else(fail)?;

    let atoms: Vec<Formula> = src.iter().map(|f| subst_f(f, &sub)).collect();
    Ok(Walked { ws, wvs, eqs, concl, atoms, sub })
}

/// The `j`-th recursive field's own binder term, found by counting `Slot::Rec`
/// down the declared mask — the induction hypothesis at level `k + m + j`
/// speaks of *that* binder, not of level `j`.
pub(crate) fn child_term(
    cs: &derived::inductive::CtorSpec,
    ws: &[Term],
    j: usize,
) -> Option<Term> {
    let mut seen = 0;
    for (q, sl) in cs.order.iter().enumerate() {
        if *sl == Slot::Rec {
            if seen == j {
                return ws.get(q).cloned()
            }
            seen += 1;
        }
    }
    None
}

/// `Γ ⊢ ∀w. (w ∈ Dᵈᵉʳⁱᵛᵉᵈ → φ)` from `Γ ∪ {w ∈ ⟦D⟧} ⊢ φ` and
/// `Γ ⊢ Dᵈᵉʳⁱᵛᵉᵈ = ⟦D⟧`.
///
/// The discharge and the domain rewrite in one step, because the two must
/// happen at the same moment: see the module header. `eq` may carry `Γ` — it
/// is a β step for a recursive field — and that `Γ` mentions only strictly
/// earlier binders, which the closes above this one discharge.
pub(crate) fn domain_swap(
    ip: &mut Interp,
    closed: &Closed,
    eq: &Thm,
    inner: &Thm,
) -> Option<Thm> {
    let idom = closed.domain().clone();
    let (ddom, rhs) = eq.concl().as_eq()?;
    if rhs != idom {
        return None
    }
    let w = closed.var();
    let phi = inner.concl().clone();
    let discharged = closed.discharge(inner).ok()?;
    let x = ip.env.fresh_var();
    let at = Formula::forall(w, Formula::imp(Formula::mem(Term::var(w), Term::var(x)), phi));
    let back = derived::eq_symm(&mut ip.env, eq)?;
    let leib = Thm::eq_leibniz(idom, ddom, x, at);
    Thm::mp(&Thm::mp(&leib, &back)?, &discharged)
}
