//! **The translation procedure for inductive declarations**, instantiated at
//! eight shapes with the *same* code — §5.2's `spec` judgment, driven by
//! declaration data.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** Membership theorems alone are satisfied
//! by a one-element carrier and refuted by none, so every shape below is also
//! made to exhibit *distinct* elements: `Bool` two, `RGB` three, `N` three (and
//! hence infinitely many), `Tree` an element with two different subtrees. A
//! translation that produced `∅` for everything would fail every one of those.
//!
//! The eight shapes, and what each is here to show:
//!
//! | declaration | what it exercises |
//! |---|---|
//! | `Empty` | 0 constructors — the tag set is `0` and there is nothing to type |
//! | `Unit` | 1 constructor — a closed, unconditional membership |
//! | `Bool` | 2 nullary constructors — what `enums.rs` caps out at |
//! | `RGB` | **3** nullary constructors — beyond `enums.rs`'s cap |
//! | `N` | a recursive argument |
//! | `List α` | a parameter, used as an argument type |
//! | `Tree` | **two** recursive arguments in one constructor |
//! | `Dep` | **two dependent** non-recursive arguments |

use kernel::{Env, Formula, FnSym, Term, Thm};

use derived::inductive::{Ctor, CtorSpec, DeclSpec, Inductive, Machine};

use derived::sigma::Telescope;
use derived::{and_intro, define_abbrev, inst_all, singleton};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// The statement `Ctor::mem` should have: `∀p⃗ ∀y⃗ ∀r⃗. (H → ctor ∈ ind(p⃗))`,
/// with the implication absent when the constructor takes nothing.
fn ctor_statement(ind: &Inductive, c: &Ctor) -> Formula {
    let concl = Formula::mem(c.term.clone(), ind.carrier.clone());
    let body = match &c.hyp {
        Some(h) => Formula::imp(h.clone(), concl),
        None => concl,
    };
    let mut quant = ind.params.clone();
    quant.extend(c.args.iter().copied());
    quant.extend(c.recs.iter().copied());
    // Rebuilt directly, rather than through `gen_all`, so the expected formula
    // does not depend on the helper being right.
    quant.iter().rev().fold(body, |acc, v| Formula::forall(*v, acc))
}

/// From `⊢ a = b` and `⊢ x ∈ a` infer `⊢ x ∈ b`.
fn transport(env: &mut Env, eq: &Thm, mem: &Thm) -> Thm {
    let (a, b) = eq.concl().as_eq().expect("an equation");
    let (x, _) = mem.concl().as_mem().expect("a membership");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, hole, Formula::mem(x, Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), mem).expect("mp")
}

/// Every declaration below is translated over one apparatus.
fn machine(env: &mut Env) -> Machine {
    Machine::new(env).expect("the translation apparatus")
}

// ─────────────────────────────────────────────────────────────────────────────
// The degenerate ends.
// ─────────────────────────────────────────────────────────────────────────────

/// `inductive Empty`. Zero constructors: the tag set is `0`, the fibre family
/// is `∅`, and the bound obligation is still discharged — so the construction
/// does not need a constructor to exist in order to be well-formed.
#[test]
fn empty_has_no_constructors_and_still_has_a_bound() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, vec![])).expect("Empty");

    let s = &mach.wt.sums;
    assert!(ind.ctors.is_empty());
    assert_eq!(ind.tags, mach.syms.sum(&[]).expect("Sum_0"));
    assert_eq!(
        *mach.syms.sum_ax(0).expect("Sum_0's defining equation").concl(),
        Formula::eq(ind.tags.clone(), s.zero()),
        "no constructors means the tag set unfolds to 0"
    );
    assert_eq!(ind.fibre.fam, s.zero(), "and the fibre family is the empty function");
    assert_eq!(
        *ind.closed.concl(),
        derived::wtype::closed(&mut env, s, &ind.tags, &ind.fibre.fam, &ind.bound),
    );
    assert!(closed(ind.closed.concl()), "the bound is discharged unconditionally");
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_none());
}

/// `inductive Unit | star`. One constructor, no arguments: the membership is a
/// **closed** theorem with no antecedent — which is the property
/// `INDUCTIVES.md`'s `Bool` measurement turns on.
#[test]
fn unit_has_one_element_and_the_membership_is_closed() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, vec![CtorSpec::nullary()]))
        .expect("Unit");

    let s = &mach.wt.sums;
    let c = &ind.ctors[0];
    assert!(c.hyp.is_none(), "a nullary constructor carries no hypothesis");
    assert_eq!(c.term, mach.wt.sup(mach.syms.inj(0, s.point()).expect("Inj_0"), s.zero()));
    assert_eq!(*c.mem.concl(), Formula::mem(c.term.clone(), ind.carrier.clone()));
    assert!(closed(c.mem.concl()), "⊢ star ∈ Unit is closed and unconditional");
    assert!(c.inj.is_none(), "there is nothing to be injective in");
}

// ─────────────────────────────────────────────────────────────────────────────
// Enumerations, past the cap.
// ─────────────────────────────────────────────────────────────────────────────

/// `inductive Bool | false | true`. Two nullary constructors — what
/// `derived/src/enums.rs` does by hand.
#[test]
fn bool_has_two_provably_distinct_elements() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = Inductive::build(
        &mut env,
        &mut mach,
        &DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]),
    )
    .expect("Bool");

    for c in &ind.ctors {
        assert_eq!(*c.mem.concl(), Formula::mem(c.term.clone(), ind.carrier.clone()));
        assert!(closed(c.mem.concl()));
    }
    let apart = ind.distinct(&mut env, &mach, 0, 1).expect("the two are distinct");
    assert_eq!(
        *apart.concl(),
        Formula::not(Formula::eq(ind.ctors[0].term.clone(), ind.ctors[1].term.clone()))
    );
    assert!(closed(apart.concl()));
    assert_ne!(ind.ctors[0].term, ind.ctors[1].term);
}

/// `inductive RGB | red | green | blue`. **Three** nullary constructors —
/// exactly the shape `enums.rs` cannot express, translated by the same code
/// that did `Bool`, with all three pairwise distinctness statements available.
#[test]
fn a_three_constructor_enumeration() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = Inductive::build(
        &mut env,
        &mut mach,
        &DeclSpec::new(0, vec![CtorSpec::nullary(); 3]),
    )
    .expect("RGB");

    assert_eq!(ind.ctors.len(), 3);
    for c in &ind.ctors {
        assert!(closed(c.mem.concl()));
        assert_eq!(*c.mem.concl(), Formula::mem(c.term.clone(), ind.carrier.clone()));
    }
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        let apart = ind.distinct(&mut env, &mach, i, j).expect("distinct");
        assert_eq!(
            *apart.concl(),
            Formula::not(Formula::eq(ind.ctors[i].term.clone(), ind.ctors[j].term.clone()))
        );
        assert!(closed(apart.concl()));
    }
    // Three constructors, three provably different elements, one carrier.
    assert_ne!(ind.ctors[0].term, ind.ctors[2].term);
}

// ─────────────────────────────────────────────────────────────────────────────
// Recursion.
// ─────────────────────────────────────────────────────────────────────────────

fn nat(env: &mut Env, mach: &mut Machine) -> Inductive {
    Inductive::build(
        env,
        mach,
        &DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 1)]),
    )
    .expect("N")
}

/// `inductive N | zero | succ : N → N`. The recursive constructor's rule
/// carries exactly one hypothesis, `r ∈ N`, and its fibre is `finord(1)`.
#[test]
fn nat_zero_and_succ() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = nat(&mut env, &mut mach);
    let s = &mach.wt.sums;

    let fin = |m| mach.syms.finord(s, m).expect("finord");
    assert_eq!(ind.fibre.values, vec![fin(0), fin(1)]);
    assert!(closed(ind.ctors[0].mem.concl()), "zero is a closed term");

    let succ = &ind.ctors[1];
    let r = Term::var(succ.recs[0]);
    assert_eq!(succ.hyp, Some(Formula::mem(r.clone(), ind.carrier.clone())));
    assert_eq!(*succ.mem.concl(), ctor_statement(&ind, succ));

    // `succ` is injective — one equation, no conjunction.
    let inj = succ.inj.as_ref().expect("succ is injective");
    let other = Term::var(env.fresh_var());
    let at = inst_all(inj, &[r.clone(), other.clone()]).expect("instantiate");
    let succ_of = |t: Term| {
        ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&t)).expect("succ")
    };
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::eq(succ_of(r.clone()), succ_of(other.clone())),
            Formula::eq(r, other),
        )
    );
}

/// Three different natural numbers, all in the carrier and pairwise distinct.
/// This is what says `N` is not a two-element set: `succ` applied twice leaves
/// the range of anything already there.
#[test]
fn nat_has_three_distinct_elements() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = nat(&mut env, &mut mach);

    let zero = ind.ctors[0].term.clone();
    let succ_of =
        |t: &Term| ind.ctor_term(&mach, 1, &[], std::slice::from_ref(t)).expect("succ");
    let one = succ_of(&zero);
    let two = succ_of(&one);

    // All three are in the carrier, unconditionally.
    let zero_in = ind.ctors[0].mem.clone();
    let succ_rule = &ind.ctors[1].mem;
    let one_in = Thm::mp(
        &inst_all(succ_rule, std::slice::from_ref(&zero)).expect("instantiate"),
        &zero_in,
    )
    .expect("succ zero ∈ N");
    let two_in = Thm::mp(
        &inst_all(succ_rule, std::slice::from_ref(&one)).expect("instantiate"),
        &one_in,
    )
    .expect("succ (succ zero) ∈ N");
    for (t, th) in [(&zero, &zero_in), (&one, &one_in), (&two, &two_in)] {
        assert_eq!(*th.concl(), Formula::mem(t.clone(), ind.carrier.clone()));
        assert!(closed(th.concl()));
    }

    // And pairwise distinct.
    let tags_apart = ind.distinct(&mut env, &mach, 0, 1).expect("zero ≠ succ _");
    let zero_ne_one = inst_all(&tags_apart, std::slice::from_ref(&zero)).expect("instantiate");
    assert_eq!(*zero_ne_one.concl(), Formula::not(Formula::eq(zero.clone(), one.clone())));
    let zero_ne_two = inst_all(&tags_apart, std::slice::from_ref(&one)).expect("instantiate");
    assert_eq!(*zero_ne_two.concl(), Formula::not(Formula::eq(zero.clone(), two.clone())));

    // `succ 0 ≠ succ 1` because `0 ≠ 1`, through injectivity.
    let inj = ind.ctors[1].inj.as_ref().expect("injective");
    let at = inst_all(inj, &[zero.clone(), one.clone()]).expect("instantiate");
    let one_ne_two = derived::syl(&at, &zero_ne_one).expect("chain");
    assert_eq!(*one_ne_two.concl(), Formula::not(Formula::eq(one, two)));
    assert!(closed(one_ne_two.concl()));
}

/// `inductive Tree | leaf | node : Tree → Tree → Tree`. **Two** recursive
/// arguments in one constructor — nothing in `derived/` could express this
/// before, because a one-point graph has one point.
#[test]
fn a_binary_tree_is_injective_in_both_subtrees() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let ind = Inductive::build(
        &mut env,
        &mut mach,
        &DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 2)]),
    )
    .expect("Tree");
    let s = &mach.wt.sums;

    assert_eq!(ind.fibre.values[1], mach.syms.finord(s, 2).expect("finord"), "node branches twice");
    let node = &ind.ctors[1];
    let (r0, r1) = (Term::var(node.recs[0]), Term::var(node.recs[1]));
    assert_eq!(
        node.hyp,
        Some(Formula::and(
            Formula::mem(r0.clone(), ind.carrier.clone()),
            Formula::mem(r1.clone(), ind.carrier.clone()),
        ))
    );
    assert_eq!(*node.mem.concl(), ctor_statement(&ind, node));

    // `node a b ∈ Tree` at two concrete subtrees.
    let leaf = ind.ctors[0].term.clone();
    let node_of = |a: &Term, b: &Term| {
        ind.ctor_term(&mach, 1, &[], &[a.clone(), b.clone()]).expect("node")
    };
    let leaf_in = ind.ctors[0].mem.clone();
    let nll = Thm::mp(
        &inst_all(&node.mem, &[leaf.clone(), leaf.clone()]).expect("instantiate"),
        &and_intro(&leaf_in, &leaf_in),
    )
    .expect("node leaf leaf ∈ Tree");
    assert_eq!(
        *nll.concl(),
        Formula::mem(node_of(&leaf, &leaf), ind.carrier.clone())
    );
    assert!(closed(nll.concl()));

    // Injective in **both** arguments, as a conjunction of two equations.
    let inj = node.inj.as_ref().expect("node is injective");
    let (a, b) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let at = inst_all(inj, &[r0.clone(), r1.clone(), a.clone(), b.clone()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::eq(node_of(&r0, &r1), node_of(&a, &b)),
            Formula::and(Formula::eq(r0, a), Formula::eq(r1, b)),
        )
    );

    // The two subtrees really are separated: `node leaf t ≠ node t leaf` would
    // follow, and concretely `node leaf leaf ≠ leaf`.
    let apart = ind.distinct(&mut env, &mach, 1, 0).expect("node ≠ leaf");
    let at = inst_all(&apart, &[leaf.clone(), leaf.clone()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::not(Formula::eq(node_of(&leaf, &leaf), leaf))
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Parameters, and dependent arguments.
// ─────────────────────────────────────────────────────────────────────────────

/// `inductive List (α) | nil | cons : α → List α → List α`. One parameter, used
/// as `cons`'s first argument type — which is the identity symbol `β₀(p) = p`,
/// the cheapest possible instance of the `FnSym` convention.
///
/// Every statement is **unconditional in `α`**, matching what
/// `derived/src/wlist.rs` found by hand: no hypothesis about `α`'s own type
/// appears anywhere.
#[test]
fn list_is_unconditional_in_its_parameter() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let pv = env.fresh_var();
    let (id, _) = define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let ind = Inductive::build(
        &mut env,
        &mut mach,
        &DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]),
    )
    .expect("List");

    let alpha = Term::var(ind.params[0]);
    assert_eq!(ind.carrier, ind.ty_of(vec![alpha.clone()]));
    // The bound is derived with `α` free and with **no** hypothesis.
    let mut free = Vec::new();
    ind.closed.concl().free_vars(&mut free);
    assert_eq!(free, vec![ind.params[0]], "the only free variable is the parameter");
    assert!(ind.closed.concl().as_imp().is_none(), "and there is no antecedent");

    // `nil` needs nothing.
    let nil = &ind.ctors[0];
    assert!(nil.hyp.is_none());
    assert_eq!(
        *nil.mem.concl(),
        Formula::forall(ind.params[0], Formula::mem(nil.term.clone(), ind.carrier.clone()))
    );

    // `cons` needs exactly `h ∈ α` and `t ∈ List α` — Lean's own signature.
    let cons = &ind.ctors[1];
    let (h, t) = (Term::var(cons.args[0]), Term::var(cons.recs[0]));
    assert_eq!(
        cons.hyp,
        Some(Formula::and(
            Formula::mem(h.clone(), Term::apply(id, vec![alpha.clone()])),
            Formula::mem(t.clone(), ind.carrier.clone()),
        ))
    );
    assert_eq!(*cons.mem.concl(), ctor_statement(&ind, cons));

    // `cons` is injective in **both** components, so `α`'s elements stay
    // visible inside the list and `List α` does not collapse to `N`.
    let inj = cons.inj.as_ref().expect("cons is injective");
    let (h2, t2) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let at = inst_all(inj, &[h.clone(), t.clone(), h2.clone(), t2.clone()]).expect("instantiate");
    let cons_of = |x: &Term, y: &Term| {
        ind.ctor_term(&mach, 1, std::slice::from_ref(x), std::slice::from_ref(y))
            .expect("cons")
    };
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::eq(cons_of(&h, &t), cons_of(&h2, &t2)),
            Formula::and(Formula::eq(h, h2), Formula::eq(t, t2)),
        )
    );

    // `nil ≠ cons h t`, whatever `h` and `t` are.
    let apart = ind.distinct(&mut env, &mach, 0, 1).expect("nil ≠ cons");
    assert!(closed(apart.concl()), "distinctness does not mention the parameter");
}

/// A constructor with **two dependent** non-recursive arguments:
/// `mk : (y₀ : 1) → (y₁ : {y₀}) → Dep`. The second argument's stated type
/// mentions the first, which is the whole content of §5.2's `Σy' : β. A[y'/y]`
/// and the reason the argument types have to be function symbols.
#[test]
fn a_dependent_two_argument_telescope() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let s = mach.wt.sums.clone();
    let (b0, b0_ax) = define_abbrev(&mut env, &[], &s.unit()).expect("β₀ = 1");
    let yv = env.fresh_var();
    let sing = singleton(s.ap.sets.up, Term::var(yv));
    let (b1, b1_ax) = define_abbrev(&mut env, &[yv], &sing).expect("β₁(y) = {y}");

    let ind = Inductive::build(
        &mut env,
        &mut mach,
        &DeclSpec::new(0, vec![CtorSpec::new(vec![b0, b1], 0)]),
    )
    .expect("Dep");

    let c = &ind.ctors[0];
    let (y0, y1) = (Term::var(c.args[0]), Term::var(c.args[1]));
    assert_eq!(
        c.hyp,
        Some(Formula::and(
            Formula::mem(y0.clone(), Term::apply(b0, vec![])),
            // **the second type mentions the first argument**
            Formula::mem(y1.clone(), Term::apply(b1, vec![y0.clone()])),
        )),
        "the telescope is genuinely dependent"
    );
    assert_eq!(*c.mem.concl(), ctor_statement(&ind, c));
    let packed = Telescope::tuple_of(&s, &[y0.clone(), y1.clone()]);
    assert_eq!(
        c.term,
        mach.wt.sup(mach.syms.inj(0, packed).expect("Inj_0"), s.zero())
    );

    // Both arguments come back out.
    let inj = c.inj.as_ref().expect("injective");
    let (z0, z1) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let at = inst_all(inj, &[y0.clone(), y1.clone(), z0.clone(), z1.clone()]).expect("instantiate");
    let mk = |a: &Term, b: &Term| {
        ind.ctor_term(&mach, 0, &[a.clone(), b.clone()], &[]).expect("mk")
    };
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::eq(mk(&y0, &y1), mk(&z0, &z1)),
            Formula::and(Formula::eq(y0, z0), Formula::eq(y1, z1)),
        )
    );

    // **Non-vacuity**: the constructor is inhabited, at `y₀ := •`, `y₁ := •`,
    // since `• ∈ 1 = β₀()` and `• ∈ {•} = β₁(•)`.
    let point = s.point();
    let in_b0 = {
        let back = derived::eq_symm(&mut env, &b0_ax).expect("1 = β₀()");
        transport(&mut env, &back, &s.unit_mem)
    };
    let in_b1 = {
        let at = inst_all(&b1_ax, std::slice::from_ref(&point)).expect("β₁(•) = {•}");
        let back = derived::eq_symm(&mut env, &at).expect("{•} = β₁(•)");
        let in_sing = Thm::mp(
            &derived::iff_mpr(
                &inst_all(&s.ap.mem_sing, &[point.clone(), point.clone()]).expect("instantiate"),
            )
            .expect("mpr"),
            &Thm::eq_refl(point.clone()),
        )
        .expect("• ∈ {•}");
        transport(&mut env, &back, &in_sing)
    };
    let witness = Thm::mp(
        &inst_all(&c.mem, &[point.clone(), point.clone()]).expect("instantiate"),
        &and_intro(&in_b0, &in_b1),
    )
    .expect("mk • • ∈ Dep");
    assert_eq!(
        *witness.concl(),
        Formula::mem(mk(&point, &point), ind.carrier.clone())
    );
    assert!(closed(witness.concl()), "the carrier is provably inhabited");
}

// ─────────────────────────────────────────────────────────────────────────────
// What the spec refuses.
// ─────────────────────────────────────────────────────────────────────────────

/// An argument type of the wrong arity is refused rather than silently applied
/// to the wrong terms. `βᵢ` must have arity `np + i`.
#[test]
fn a_malformed_spec_is_declined() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let unit = mach.wt.sums.unit();
    let (nullary, _) = define_abbrev(&mut env, &[], &unit).expect("a constant type");
    let bad: FnSym = nullary; // arity 0, but it is the *second* argument
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![nullary, bad], 0)]);
    assert!(!spec.well_formed());
    assert!(Inductive::build(&mut env, &mut mach, &spec).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// The caches.
// ─────────────────────────────────────────────────────────────────────────────

/// **The telescope cache is keyed by `(np, β⃗)`, not by the arity.** Two
/// constructors with the *same* argument types share one `Σ` nest — the same
/// symbols and the same theorems — while two with the same arity and different
/// types get their own.
#[test]
fn the_telescope_cache_is_keyed_by_the_argument_types() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let unit = mach.wt.sums.unit();
    let (b0, _) = define_abbrev(&mut env, &[], &unit).expect("β = 1");
    let zero = mach.wt.sums.zero();
    let (b1, _) = define_abbrev(&mut env, &[], &zero).expect("β′ = 0");

    let same = mach.telescope(&mut env, 0, &[b0]).expect("telescope");
    let hit = mach.telescope(&mut env, 0, &[b0]).expect("telescope again");
    assert!(std::rc::Rc::ptr_eq(&same, &hit), "the same argument types share one Σ nest");
    assert_eq!(*same.intro.concl(), *hit.intro.concl(), "and the same theorems");

    let other = mach.telescope(&mut env, 0, &[b1]).expect("a different type");
    assert!(!std::rc::Rc::ptr_eq(&same, &other), "different types do not");
    assert_ne!(same.levels[0], other.levels[0], "and get different Σ symbols");

    // The arity alone is not the key: `[b0]` and `[b1]` are both unary.
    assert_eq!(same.betas.len(), other.betas.len());

    // A declaration whose two constructors have identical argument types
    // therefore builds one telescope, not two.
    let ind = Inductive::build(
        &mut env,
        &mut mach,
        &DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0), CtorSpec::new(vec![b0], 1)]),
    )
    .expect("two constructors, one argument type");
    assert!(std::rc::Rc::ptr_eq(&ind.telescopes[0], &ind.telescopes[1]));
    assert_eq!(ind.summands[0], ind.summands[1], "so both tag summands are the same set");
    // …and the two constructors are still provably distinct, because the *tags*
    // differ even when the summands do not.
    assert!(ind.distinct(&mut env, &mach, 0, 1).is_some());
}

/// The sum-symbol cache is incremental: a second, wider declaration extends it
/// and re-derives nothing already present.
#[test]
fn the_sum_symbol_cache_is_incremental() {
    let mut env = Env::new();
    let mut mach = machine(&mut env);
    let narrow =
        Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, vec![CtorSpec::nullary(); 2]))
            .expect("two constructors");
    let sum2 = mach.syms.sum(&narrow.summands).expect("Sum_2");
    let inj1 = mach.syms.inj(1, mach.wt.sums.point()).expect("Inj_1");

    let wide =
        Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, vec![CtorSpec::nullary(); 5]))
            .expect("five constructors");
    assert_eq!(wide.ctors.len(), 5);
    // The narrow declaration's terms are untouched by the widening.
    assert_eq!(mach.syms.sum(&narrow.summands).expect("Sum_2"), sum2);
    assert_eq!(mach.syms.inj(1, mach.wt.sums.point()).expect("Inj_1"), inj1);
    // And the wider one reuses `Inj_1` rather than minting a second.
    assert_eq!(wide.ctors[1].tag, inj1);
}
