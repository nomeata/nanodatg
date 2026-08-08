//! **Step 3 of the nested arc: the generated model, put into the run, and the
//! keying that makes it the declaration's interpretation.**
//!
//! # Interface
//!
//! ```text
//! nested_splice::splice(env, decls, schedule) -> Spliced
//! ```
//!
//! [`Spliced`] is the file's declaration list with each nested declaration's
//! model — [`crate::nested_ev::iso`]'s output — inserted **immediately before
//! the declaration it models**, the environment those constants were checked
//! into, the σ they have to be interpreted at, and [`Spliced::model_of`]: the
//! side table that says which model constant carries `⟦T⟧`, `⟦T.ctorᵢ⟧` and
//! `⟦T.rec_k⟧`.
//!
//! It is [`crate::mutual_aux::expand`]'s shape and it runs at the same point in
//! [`crate::run::check_file`], immediately before it — a nested model contains
//! a `mutual … end` block of its own, and `expand` is what turns that into
//! declarations the interpretation pass can take.
//!
//! # Why this is a *substitution* there and an *alias* here
//!
//! `mutual_aux::expand` needs no side table: its encoding defines `Tᵢ`,
//! `Tᵢ.ctorⱼ` and `Tᵢ.rec` **under the block's own names**, so `⟦Tᵢ.{σ}⟧` lands
//! in the store at exactly the key every use site reads and there is nothing to
//! key afterwards.
//!
//! A nested declaration cannot be substituted that way, and the reason is on
//! the *acceptance* axis. `T` is installed by [`crate::nested::add`] as a
//! primitive `ConstantInfo::Inductive` and `T.rec_k` as a primitive
//! `ConstantInfo::Recursor` whose rules the kernel fires; the model's `rec_k` is
//! a `def` whose rules are **theorems**. Replacing the primitives by the model
//! would take away the ι reductions the file's own declarations are checked
//! with — `nested_iota.lean` is fourteen of them — and turn an accepted file
//! into a rejected one. So the primitives stay, the model is a parallel
//! development beside them, and the two are joined by
//! [`Spliced::model_of`] rather than by a name.
//!
//! # The keying is a table and not a convention, and that is the whole point
//!
//! `⟦T⟧ := ⟦T._model.self⟧` could be spelled as a name rule: take the
//! declaration's name, append `_model.self`, look it up. **It must not be.**
//! A name rule answers for a constant that exists for some other reason —
//! a file that declares its own `Tree._model.self` gets its interpretation
//! silently substituted for the model's — and the counters would report a
//! working model. This project has paid for that once already, at
//! `_auxCarrier`, and `mini/tests/fixtures/nested_keying.lean`'s `UTree` is the
//! same input at this site: two nested declarations of one shape, and the file
//! itself has taken the name one of their models wants.
//!
//! So the table is filled **only** from a model this module built, checked and
//! spliced in, and it is keyed on the constant's own [`ModelKey`] — the σ
//! included, because a recursor's motive level is part of what is being keyed.
//! A constant with no entry **declines**, by name, in
//! [`crate::zoneb::ensure`]; it never falls through to the class-(T) walk and
//! never falls back to a name.
//!
//! # Where the model goes, and the one shape that decides it
//!
//! Immediately **before** the nested declaration. The model mentions no part of
//! `T` — [`crate::nested_ev`]'s header says why its carrier has to be fresh —
//! so nothing stops it going first, and going first is what makes the alias
//! possible at all: [`crate::ledger::fill_declaration`] resolves `⟦T⟧` when it
//! reaches `T`, and it can only read `⟦T._model.self⟧` out of the store if the
//! model's own declarations have already been interpreted.
//!
//! That is a constraint on the *file*, not on this module, and it is checked
//! rather than assumed: every constant the model mentions must be declared
//! before `T`. The one that can fail is `Eq` — the round trips and the ι rules
//! are equations, and the exporter puts `Eq` wherever the file needed it, which
//! for a `mutual` block is routinely *after*
//! ([`crate::mutual_aux::expand`]'s header records three such files). A file
//! that declares its `Eq` after its nested type gets no model and a named
//! decline, which is the honest answer: the model would be unreadable at the
//! moment the alias needs it.
//!
//! # What the ι dispatch arm turns on, and what it costs
//!
//! Three things, and they were all measured from here rather than guessed:
//!
//! 1. **The seed.** The ι theorems are the one part of the model this module
//!    deliberately does not splice; the site below says why, with the number.
//!    Turning them on is `for (k, _, thm) in &iso.iotas { seeds.entry(thm) …
//!    applied[rec_name(name, k)] }`, three lines beside the recursor seeding.
//! 2. **A second table beside [`Spliced::model_of`]**, and it should be built
//!    at the same moment from the same source: [`crate::nested_ev::Iso::iotas`]
//!    is `(member k, the export's constructor, the theorem)`, so
//!    `((T.rec_k, σ), ctor) -> theorem` is the key a dispatch site holds — it
//!    has the recursor and the major's head constructor and nothing else. It is
//!    not built here because a table pointing at declarations this module did
//!    not splice would be a key with nothing behind it.
//! 3. **Where the arm attaches.** `iota_dep::fire`'s *first* check is
//!    `args.len() != np + 1 + n + 1`, and a nested recursor fails it before
//!    anything else: `Tree.rec` binds **two** motives and **four** minors, so a
//!    redex has seven arguments where that arity expects four. Every one of
//!    `nested_iota`'s fourteen waits on exactly that —
//!    `recursor(T.rec_k: iota: the recursor's arity or its declaration
//!    disagree)` — and `mini/tests/nested.rs`'s
//!    `what_is_left_after_the_keying_is_the_iota_dispatch_arm` pins the set. So
//!    the arm is a *sibling* of `iota_dep::fire`, chosen on the same
//!    `model_of` membership this module fills, and its body is
//!    [`crate::eq_cash::cash`] applied to the rule theorem at the redex's own
//!    arguments — not a repair of the arity check.
//!
//! # What the tests kill, measured
//!
//! Eight mutations of this module and of [`crate::zoneb::ensure`]'s keying
//! site, against the two fast tests in `mini/tests/nested.rs`
//! (`nested_keying` at 9 s and `nested_shapes` at 1m40; the executed test count
//! is read out of the harness's own summary, because `cargo test` prints
//! `error: test failed` at line start and a `^error:` classifier would read
//! every kill as a compile error):
//!
//! ```text
//! KILLED   a missing `model_of` entry falls through to the class-(T) walk
//! KILLED   key on the name `T._model.self` instead of on the table
//! KILLED   never recognise a nested declaration, so nothing is keyed
//! KILLED   splice the model *after* the declaration it models
//! KILLED   let `fill_declaration` use its own name list, losing `T.rec_1`
//! KILLED   drop the σ from a recursor's key
//! SURVIVED carry the model's defining equation onto the export's constant
//! SURVIVED drop the dependency-order check
//! ```
//!
//! The first is the one that matters: a discriminator whose missing case falls
//! back is decorative, and this says it does not.
//!
//! **Both survivors are reported rather than excused.** Carrying `defeq` is
//! unreachable by construction — `T` is a primitive inductive and `T.rec_k` a
//! primitive recursor, so the Lean checker never takes a δ step on either and
//! the equation is never consulted; `None` is kept because handing it on would
//! be *claiming* a reduction that does not exist, which is a statement about
//! the code and not about any run. The order check has no occupant in the
//! fixture set — every nested fixture declares its `Eq` first — and dropping it
//! costs correctness nothing (the alias would decline with
//! `nested model not interpreted`) but would leave the foreign-demand loop's
//! safety argument below claiming something nothing checks.
//!
//! # The boundary
//!
//! This module names no `Term`, `Thm`, `Ev` or `Interp`. It moves
//! `mini::Expr`s, calls [`crate::nested::plan`] and [`crate::nested_ev::iso`],
//! and produces a table of `(Name, σ)` pairs. Everything that reads a
//! certificate is on the other side of [`Spliced::model_of`].

use std::collections::{HashMap, HashSet};

use crate::env::{Declaration, Environment, IndType};
use crate::expr::{Expr, Name, E};

/// A constant at a ground instantiation — the pair `crate::interp`'s `ConstKey`
/// is, spelled out rather than imported.
///
/// The two are the same type and the alias is deliberately *not* the one on the
/// interpretation side: `ci/check-mutual-blackbox.sh` scans this file for the
/// word `interp::`, and a module that produces a table the evidence layer
/// consumes has no business naming the store to do it. What crosses the
/// boundary is a `(Name, Vec<u32>) -> Name` map of syntax.
pub type ModelKey = (Name, Vec<u32>);

/// One nested declaration's outcome, whether or not it got a model.
#[derive(Clone, Debug)]
pub struct NestedRecord {
    /// The shape that stopped the model, as [`crate::nested_ev::Reason::label`]
    /// spells it, or `None` when one was built and keyed.
    ///
    /// A `Some` here is what [`crate::zoneb::ensure`] reports instead of
    /// walking the declaration's constructor spec — which would answer
    /// `nested occurrence`, the true but least informative of the reasons.
    pub why: Option<&'static str>,
    /// The export constants the model is responsible for, in fill order: the
    /// type former, its constructors, then **every** recursor the declaration
    /// owns.
    ///
    /// `T.rec_1` and `T.rec_2` are the reason this list exists.
    /// [`crate::ledger::fill_declaration`]'s own list is `T`, its constructors
    /// and `T.rec`, which is every recursor an *ordinary* declaration has; a
    /// nested one has one per specialised member, and the ones past the first
    /// would otherwise be reached only by the lazy-fill path.
    pub constants: Vec<Name>,
}

/// A declaration list with every nested declaration's model spliced in.
pub struct Spliced {
    /// The environment the pass must run against: the caller's, with each
    /// model's constants added.
    pub env: Environment,
    /// The declaration list, in file order, each model before the declaration
    /// it models.
    pub decls: Vec<Declaration>,
    /// The schedule, with the σ each model needs added.
    pub schedule: HashMap<Name, Vec<Vec<u32>>>,
    /// **The keying.** `⟦export constant.{σ}⟧` is `⟦model constant.{σ}⟧`, for
    /// exactly the pairs a model was built and spliced for.
    pub model_of: HashMap<ModelKey, Name>,
    /// **The rules.** `((T.rec_k, σ), the export's constructor) ↦ the model's ι
    /// theorem`, for exactly the rules this pass seeded.
    ///
    /// The key is what a dispatch site holds: [`crate::iota_model::fire`] has
    /// the recursor it is reducing, the σ it is reducing at, and the major's
    /// head constructor, and nothing else. A rule with no entry **declines**
    /// there, by name; there is no name rule and no fall-through, for
    /// [`Spliced::model_of`]'s reason.
    ///
    /// Populated only for the rules [`refl_proved`] admits — see the seeding
    /// site, which carries the measurement.
    pub model_iota: HashMap<(ModelKey, Name), Name>,
    /// Every nested declaration this pass saw, by its own name.
    pub nested: HashMap<Name, NestedRecord>,
    /// Nested declarations seen, and models built. `modelled ≤ seen`, and the
    /// difference is the [`NestedRecord::why`] population.
    pub seen: usize,
    pub modelled: usize,
}

/// **Splice each nested declaration's model into the run, and key it.**
///
/// A declaration that is not nested is passed through untouched, and so is one
/// whose model could not be built — with its reason recorded in
/// [`Spliced::nested`] so that the decline downstream names a shape.
pub fn splice(
    env: &Environment,
    decls: &[Declaration],
    schedule: &HashMap<Name, Vec<Vec<u32>>>,
) -> Spliced {
    let mut out = Spliced {
        env: env.clone(),
        decls: Vec::with_capacity(decls.len()),
        schedule: schedule.clone(),
        model_of: HashMap::new(),
        model_iota: HashMap::new(),
        nested: HashMap::new(),
        seen: 0,
        modelled: 0,
    };
    // Which declaration in the list owns each name, by position. Read to check
    // that a model's dependencies are all *behind* the declaration it models —
    // see the header.
    let pos = positions(env, decls);
    // What the file's own declarations name, and at which ground σ — the
    // pre-pass's demand walk without its default padding. See the recursor
    // seeding below, which is the only reader.
    let applied = applied_at(decls, schedule);
    for (i, d) in decls.iter().enumerate() {
        let Declaration::Inductive { name, lparams, num_params, ty, ctors } = d else {
            out.decls.push(d.clone());
            continue
        };
        let types =
            vec![IndType { name: name.clone(), ty: ty.clone(), ctors: ctors.clone() }];
        // **`nested::plan` answers "is this nested", and nothing else does.**
        // Not the export's `is_nested` flag, which `convert::load` has already
        // consumed at the parser gate, and not a name: the question here is
        // whether a constructor field mentions the declaration under a foreign
        // inductive, which is the same question the specialisation asks.
        let plan = match crate::nested::plan(&out.env, lparams, *num_params, &types) {
            Ok(Some(p)) => p,
            // `Ok(None)` is an ordinary declaration. `Err` is a nested one the
            // specialiser cannot express — the file would not have been
            // accepted, so it cannot arise here, and passing it through leaves
            // the existing decline exactly where it was.
            _ => {
                out.decls.push(d.clone());
                continue
            }
        };
        out.seen += 1;
        let iso = match crate::nested_ev::iso(&out.env, lparams, *num_params, &types, &plan) {
            Ok(iso) => iso,
            Err(r) => {
                out.decline(name, d, r.label(), ctors, &plan);
                continue
            }
        };
        // Every name the development brought into being, by difference against
        // the environment it was checked over. Read off the environment rather
        // than rebuilt from the declaration list, because a block's recursors
        // are minted by `kernel::add` and are not in it.
        let mine: HashSet<Name> =
            iso.env.consts.keys().filter(|k| out.env.get(k).is_none()).cloned().collect();
        // **The model has to be readable where the alias reads it.** See the
        // header: `fill_declaration` resolves `⟦T⟧` at `T`'s own position, so
        // everything the model mentions must be declared before it.
        if mentioned_after(&iso, &mine, &pos, i).is_some() {
            out.decline(name, d, "nested model over a later declaration", ctors, &plan);
            continue
        }
        out.modelled += 1;
        // ── the keying ───────────────────────────────────────────────────
        //
        // One entry per `(export constant, σ)`, and the σ are the export's own:
        // the model's counterpart carries the same universe parameters, because
        // its statement is the export's with the names rewritten
        // (`nested_ev::Gen::rec_decl`). A σ the export's pre-pass did not
        // schedule gets no entry and declines, which is the direction that
        // fails closed.
        let mut seeds: HashMap<Name, Vec<Vec<u32>>> = out.schedule.clone();
        // The type former and the constructors have no universe parameters of
        // their own — `nested_ev::Reason::Polymorphic` refuses a declaration
        // that has any — so `σ = []` is the whole population and is keyed
        // whether or not the file's pre-pass happened to mention them.
        let mut pairs: Vec<(Name, Name)> = vec![(name.clone(), iso.self_name.clone())];
        pairs.extend(iso.ctors.iter().cloned());
        for (export, model) in &pairs {
            out.model_of.insert((export.clone(), Vec::new()), model.clone());
            seeds.entry(model.clone()).or_default().push(Vec::new());
        }
        // **A recursor is keyed at the σ the file *applies* it at, and at no
        // other** — `applied`, not the schedule.
        //
        // The two differ, and the difference is the whole cost of this module.
        // `checker::instantiations` closes its demand and then **defaults**:
        // "a declaration nothing demands is still checked, once per entry of
        // `DEFAULT_LEVELS`". So `T.rec` is scheduled at `[0]` and `[1]` in
        // every file that declares a nested type, whether or not anything
        // eliminates one — and seeding the model from that pulls in `pack`,
        // `unpack`, both round trips, both recursors, the congruences and every
        // ι theorem, twice. Measured on `nested_keying`, whose two `def`s never
        // mention a recursor: the whole file is **68 000** conversions in nine
        // seconds with the recursor half unkeyed, and with it keyed off the
        // padded schedule it was past 950 000 and out of 4 GB after nine
        // minutes.
        //
        // The padding is right for the pre-pass and wrong here. It exists so
        // that a declaration nothing reaches is still *checked*; a model exists
        // so that a use site can read it, and a σ no use site names is a model
        // nobody will read. So the σ are read off the file's own declarations,
        // which is the same walk the pre-pass does before it pads.
        for (k, r) in iso.recs.iter().enumerate() {
            let export = crate::nested::Plan::rec_name(name, k);
            let sigmas = applied.get(&export).cloned().unwrap_or_default();
            for s in &sigmas {
                out.model_of.insert((export.clone(), s.clone()), r.clone());
            }
            seeds.entry(r.clone()).or_default().extend(sigmas);
            pairs.push((export, r.clone()));
        }
        // **The ι theorems, seeded and keyed — but only the ones whose proof is
        // reflexivity, and that is a measurement and not a taste.**
        //
        // [`crate::nested_ev::Iso::iotas`] is `(member, the export's
        // constructor, the theorem)` for every rule of every `rec_k`, and
        // nothing in the *file* mentions one — a rule theorem is used by
        // nothing, exactly as `mutual_aux::expand`'s are, so the fixpoint below
        // cannot reach them and only this seed does.
        //
        // Seeding **all** of them was measured from here: `nested_iota` — the
        // one fixture that applies a nested recursor — reached **43.7 million
        // conversions and 6 GB after fifteen minutes** and was still at
        // declaration 65 of about 80, where without them the same file is 6.0
        // million and 2m18s. Inside `Tree`'s four rules the split is sharp: the
        // two the encoding leaves definitional cost about 150 000 each, and the
        // two that transport cost 5.0 million and 13.7 million and are where
        // `gapped` goes 0 → 30 → 109.
        //
        // **The expensive conversions are the ones that fail**, and they buy
        // nothing even when paid for: the two transporting rules cannot be
        // cashed either way. Their proofs go through `#90(b)` — a transport
        // that must be reduced rather than compared, whose small witness is
        // `mini/tests/fixtures/transport_through_eq_rec.lean` at 21 509
        // conversions — so their own constant typings are `no-endpoint`, and
        // [`crate::eq_cash::cash`] has nothing to read. `eq_cash`'s
        // `MODEL_IOTA` table is that fact on the hand-written model, asserted:
        // `iotaLeaf` and `iota1Nil` cash and `iotaNode` and `iota1Cons` do not.
        // So the rules left out here are exactly the rules the arm could not
        // fire, and leaving them out costs no conversion that would have
        // certified.
        //
        // [`refl_proved`] is the discriminator, read off the declaration this
        // module built rather than off a name or a shape: `Rule::value` starts
        // at `Eq.refl` and wraps one `Eq.rec` per **moving** field, so a proof
        // that is still `Eq.refl` under its binders is a rule with no
        // transport. When `#90(b)` lands the guard is the line to widen, and
        // the number to re-measure is the 5.0/13.7 million above.
        //
        // A rule that is not seeded is a rule with **no `model_iota` entry**,
        // and [`crate::iota_model::fire`] declines by name for it. It is not a
        // fall-back: a wrong model would be reported as success by the counters
        // and that is the error this whole table exists to refuse.
        let refl: HashSet<Name> = iso
            .decls
            .iter()
            .filter(|d| refl_proved(d))
            .map(|d| d.name())
            .collect();
        for (k, ctor, thm) in &iso.iotas {
            if !refl.contains(thm) {
                continue
            }
            let export = crate::nested::Plan::rec_name(name, *k);
            // The σ the recursor itself was keyed at, and no other: a rule at a
            // σ the recursor has no interpretation at is a rule about a redex
            // this run cannot name.
            let Some(sigmas) = applied.get(&export) else { continue };
            for s in sigmas {
                out.model_iota
                    .insert(((export.clone(), s.clone()), ctor.clone()), thm.clone());
            }
            seeds.entry(thm.clone()).or_default().extend(sigmas.iter().cloned());
        }

        let demanded = crate::mutual_aux::demand_over(&iso.env, &mine, &seeds);
        // **The model is spliced as far as it is demanded and no further**, and
        // that is a cost decision with a measurement behind it.
        //
        // `Ledger::run` opens a pair for **every** `Def` in the list, schedule
        // entry or not, so a declaration that is spliced is a declaration that
        // is interpreted. The whole model of one `Tree` is 950 000 conversions
        // and does not fit in 4 GB; the part a file that never applies a nested
        // recursor actually uses — the block, the carrier and the constructors
        // — is 27 000. The two round trips alone are 190 000 of the difference,
        // and they are reachable only through `rec_k`.
        //
        // The set is [`crate::mutual_aux::demand_over`]'s own fixpoint, which is
        // dependency-closed by construction, so what is kept is still in
        // dependency order and still complete. A file that *does* apply the
        // recursor seeds it above and gets the whole tower.
        let first_new = out.decls.len();
        for d in iso.decls {
            if declares(&d).iter().any(|n| demanded.contains_key(n)) {
                for n in declares(&d) {
                    if let Some(v) = iso.env.consts.get(&n) {
                        out.env.consts.insert(n.clone(), v.clone());
                    }
                    if let Some(o) = iso.env.owners.get(&n) {
                        out.env.owners.insert(n.clone(), o.clone());
                    }
                }
                out.decls.push(d);
            }
        }
        for (n, ss) in demanded {
            out.schedule.entry(n).or_default().extend(ss);
        }
        // **Everything spliced is scheduled, including what nothing demands.**
        //
        // `Ledger::run` interprets a `Def` with no schedule entry at the
        // all-zero σ anyway, so an unscheduled spliced declaration is not an
        // uninterpreted one — it is an interpretation at a key nothing
        // predicted, which is a `lazyFills` and is the counter this project
        // pins at zero. The occupants are the block's own recursors: the
        // walk above reaches them only through `rec_k`, and
        // `mutual_aux::expand` emits a `def` for each whether or not it does.
        // Measured before this loop existed as two lazy fills per model, both
        // inside the block's encoding — `_auxTag.rec` and `_auxCarrier.rec`, at
        // the σ `Tree._model.k.rec`'s own default reaches them at.
        for d in &out.decls[first_new..] {
            for n in declares(d) {
                let nl = iso.env.get(&n).map(|ci| ci.lparams().len()).unwrap_or(0);
                out.schedule.entry(n).or_insert_with(|| vec![vec![0; nl]]);
            }
        }
        // **…and so is what the model demands of the *file*.**
        //
        // `mutual_aux::demand`'s rule is that a constant from the surrounding
        // file "is already scheduled by the file's own pre-pass", so following
        // it would be that module deciding something the pre-pass owns. The
        // rule does not survive here, and the witness is one lazy fill on
        // `nested_iota`: `Eq.rec.{0,1}`. `Gen::rec_decl`'s transport is an
        // `Eq.rec` at the *motive* level over the *occurrence's* level, and no
        // declaration of the file uses that pair — the pre-pass could not have
        // predicted it, because the term that needs it did not exist when the
        // pre-pass ran.
        //
        // Safe because of the check above: `mentioned_after` has already
        // established that every constant the model names is settled strictly
        // before the declaration it models, so a σ added here is discharged at
        // that constant's own declaration, ahead of the model. That is the
        // *timing* half of `mutual_aux`'s own residue, and it is the half a
        // schedule entry alone does not buy.
        let mut foreign: Vec<(Name, Vec<u32>)> = Vec::new();
        for d in &out.decls[first_new..] {
            let Some((lparams, bodies)) = interpretable(d) else { continue };
            let Some(sigmas) = out.schedule.get(&d.name()) else { continue };
            for sigma in sigmas {
                let map = crate::ground::ground_env(lparams, sigma);
                for b in &bodies {
                    consts_at(b, &map, &mut foreign);
                }
            }
        }
        for (n, s) in foreign {
            if mine.contains(&n) {
                continue
            }
            let e = out.schedule.entry(n).or_default();
            if !e.contains(&s) {
                e.push(s);
            }
        }
        out.nested.insert(
            name.clone(),
            NestedRecord { why: None, constants: pairs.into_iter().map(|(e, _)| e).collect() },
        );
        out.decls.push(d.clone());
    }
    for v in out.schedule.values_mut() {
        v.sort();
        v.dedup();
    }
    out
}

impl Spliced {
    /// Record a nested declaration with no model: the declaration itself
    /// unchanged, and the shape that stopped it under every constant the model
    /// would have keyed.
    fn decline(
        &mut self,
        name: &Name,
        d: &Declaration,
        why: &'static str,
        ctors: &[(Name, E)],
        plan: &crate::nested::Plan,
    ) {
        let mut constants = vec![name.clone()];
        constants.extend(ctors.iter().map(|(c, _)| c.clone()));
        constants.extend(
            (0..plan.types.len()).map(|k| crate::nested::Plan::rec_name(name, k)),
        );
        self.nested.insert(name.clone(), NestedRecord { why: Some(why), constants });
        self.decls.push(d.clone());
    }
}

/// **Every constant the file's own declarations name, at every ground σ they
/// name it at** — one sweep, not a fixpoint.
///
/// `checker::instantiations::compute` runs the same sweep and then closes it
/// and pads it, and both of those are wrong for the question here. *Closing* it
/// would follow a mention through a declaration that is itself only there
/// because of the padding; *padding* it invents a σ for a constant nothing
/// mentions. What this asks is narrower and is the honest reading of "the file
/// applies `T.rec_k`": some declaration of the file has `T.rec_k.{ℓ⃗}` in its
/// type or its value, and `ℓ⃗` evaluates under a σ that declaration is
/// interpreted at.
///
/// An occurrence whose levels do not evaluate — a symbolic one — is skipped,
/// exactly as the pre-pass skips it.
fn applied_at(
    decls: &[Declaration],
    schedule: &HashMap<Name, Vec<Vec<u32>>>,
) -> HashMap<Name, Vec<Vec<u32>>> {
    let mut out: HashMap<Name, Vec<Vec<u32>>> = HashMap::new();
    for d in decls {
        let Some((lparams, bodies)) = interpretable(d) else { continue };
        let default = vec![vec![0u32; lparams.len()]];
        let sigmas = schedule.get(&d.name()).filter(|v| !v.is_empty()).unwrap_or(&default);
        for sigma in sigmas {
            let map = crate::ground::ground_env(lparams, sigma);
            for b in &bodies {
                let mut found = Vec::new();
                consts_at(b, &map, &mut found);
                for (n, s) in found {
                    let e = out.entry(n).or_default();
                    if !e.contains(&s) {
                        e.push(s);
                    }
                }
            }
        }
    }
    out
}

/// A declaration's universe parameters and the expressions the interpretation
/// pass will walk — its type, its value, and an inductive's constructor types.
///
/// The one place this file decides what "the body of a declaration" is. Both
/// [`applied_at`] and the foreign-demand walk in [`splice`] read it, and the
/// two must agree or a σ predicted by one would be missed by the other.
fn interpretable(d: &Declaration) -> Option<(&[Name], Vec<&E>)> {
    Some(match d {
        Declaration::Axiom { lparams, ty, .. } => (&lparams[..], vec![ty]),
        Declaration::Def { lparams, ty, value, .. } => (&lparams[..], vec![ty, value]),
        Declaration::Inductive { lparams, ty, ctors, .. } => {
            (&lparams[..], std::iter::once(ty).chain(ctors.iter().map(|(_, t)| t)).collect())
        }
        Declaration::Mutual { lparams, types, .. } => (
            &lparams[..],
            types
                .iter()
                .flat_map(|t| std::iter::once(&t.ty).chain(t.ctors.iter().map(|(_, c)| c)))
                .collect(),
        ),
        Declaration::Quot => return None,
    })
}

/// Every `Const` occurrence in `e` whose levels evaluate under `map`.
fn consts_at(e: &E, map: &HashMap<Name, u32>, out: &mut Vec<(Name, Vec<u32>)>) {
    match &**e {
        Expr::Const(n, ls) => {
            if let Some(s) = ls.iter().map(|l| crate::ground::eval(l, map)).collect() {
                out.push((n.clone(), s));
            }
        }
        Expr::App(f, x) => {
            consts_at(f, map, out);
            consts_at(x, map, out);
        }
        Expr::Forall { ty, body } | Expr::Lam { ty, body } => {
            consts_at(ty, map, out);
            consts_at(body, map, out);
        }
        Expr::Let { ty, val, body } => {
            consts_at(ty, map, out);
            consts_at(val, map, out);
            consts_at(body, map, out);
        }
        Expr::Proj { s, .. } => consts_at(s, map, out),
        _ => {}
    }
}

/// Every name a generated declaration brings into being — its own, and, for an
/// inductive or a block, each constructor and the recursor `kernel::add` mints
/// beside it.
///
/// [`crate::mutual_aux::Encoding::declares`] over one declaration rather than a
/// list, and it is written here for the same reason that one is written there:
/// a block's recursors are not in the declaration and are exactly what a
/// consumer reading the environment needs.
fn declares(d: &Declaration) -> Vec<Name> {
    let mut out = vec![d.name()];
    match d {
        Declaration::Inductive { name, ctors, .. } => {
            out.extend(ctors.iter().map(|(c, _)| c.clone()));
            out.push(Name::str(name, "rec"));
        }
        Declaration::Mutual { types, .. } => {
            for t in types {
                out.push(t.name.clone());
                out.extend(t.ctors.iter().map(|(c, _)| c.clone()));
                out.push(Name::str(&t.name, "rec"));
            }
        }
        _ => {}
    }
    out
}

/// **Is this generated declaration's proof reflexivity?** — the whole of the
/// ι seeding policy above, as one syntactic question.
///
/// [`crate::nested_ev`]'s `Rule::value` is `Eq.refl` at the rule's own
/// statement wrapped in **one `Eq.rec` per field the pack/unpack fold moves**,
/// so a proof still headed by `Eq.refl` under its binders is a rule with no
/// transport in it — and a transport is exactly what `#90(b)` cannot thread.
/// The same split is asserted on the hand-written model by
/// `mini/tests/nested.rs`'s
/// `two_of_the_four_model_iota_rules_are_definitional_and_two_are_not` and by
/// `eq_cash`'s own `MODEL_IOTA`.
///
/// Read off the **value** and not off the name: `iota_k_j` says which rule it
/// is and nothing about whether it transports, and a name rule here would be
/// the error [`Spliced::model_of`]'s note is about, one table along.
fn refl_proved(d: &Declaration) -> bool {
    let Declaration::Def { value, kind: crate::env::DefKind::Theorem, .. } = d else {
        return false
    };
    let mut cur = value.clone();
    while let Expr::Lam { body, .. } = &*cur.clone() {
        cur = body.clone();
    }
    let (head, _) = crate::expr::get_app(&cur);
    let refl = Name::str(&Name::simple("Eq"), "refl");
    matches!(&*head, Expr::Const(n, _) if *n == refl)
}

/// Which position in the declaration list each name is settled by: a
/// declaration's own name, and — for an inductive or a block — every
/// constructor and recursor the environment says it owns.
fn positions(env: &Environment, decls: &[Declaration]) -> HashMap<Name, usize> {
    let mut owner_pos: HashMap<Name, usize> = HashMap::new();
    for (i, d) in decls.iter().enumerate() {
        owner_pos.insert(d.name(), i);
        if let Declaration::Mutual { types, .. } = d {
            for t in types {
                owner_pos.insert(t.name.clone(), i);
            }
        }
    }
    let mut out = owner_pos.clone();
    for (n, o) in &env.owners {
        if let Some(i) = owner_pos.get(o) {
            out.insert(n.clone(), *i);
        }
    }
    out
}

/// The first constant a model mentions that is **not** its own and is not
/// settled strictly before position `i`.
///
/// `None` is what lets the model be spliced in; a `Some` is a file whose
/// declaration order the alias cannot be read in, and the caller turns it into
/// a named decline rather than into a model nobody can look up.
fn mentioned_after(
    iso: &crate::nested_ev::Iso,
    mine: &HashSet<Name>,
    pos: &HashMap<Name, usize>,
    i: usize,
) -> Option<Name> {
    let mut found: Vec<Name> = Vec::new();
    for d in &iso.decls {
        match d {
            Declaration::Axiom { ty, .. } => names_in(ty, &mut found),
            Declaration::Def { ty, value, .. } => {
                names_in(ty, &mut found);
                names_in(value, &mut found);
            }
            Declaration::Inductive { ty, ctors, .. } => {
                names_in(ty, &mut found);
                for (_, c) in ctors {
                    names_in(c, &mut found);
                }
            }
            Declaration::Mutual { types, .. } => {
                for t in types {
                    names_in(&t.ty, &mut found);
                    for (_, c) in &t.ctors {
                        names_in(c, &mut found);
                    }
                }
            }
            Declaration::Quot => {}
        }
    }
    found.into_iter().find(|n| !mine.contains(n) && pos.get(n).is_none_or(|j| *j >= i))
}

/// Every `Const` name occurring in `e`.
fn names_in(e: &E, out: &mut Vec<Name>) {
    match &**e {
        Expr::Const(n, _) => out.push(n.clone()),
        Expr::App(f, x) => {
            names_in(f, out);
            names_in(x, out);
        }
        Expr::Forall { ty, body } | Expr::Lam { ty, body } => {
            names_in(ty, out);
            names_in(body, out);
        }
        Expr::Let { ty, val, body } => {
            names_in(ty, out);
            names_in(val, out);
            names_in(body, out);
        }
        Expr::Proj { s, .. } => names_in(s, out),
        _ => {}
    }
}
