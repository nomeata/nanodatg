//! **Step 3 of the nested arc: the model the *export* already carries,
//! recognised, and the keying that makes it the declaration's interpretation.**
//!
//! # Interface
//!
//! ```text
//! nested_splice::recognise(env, decls, schedule) -> Recognised
//! ```
//!
//! [`Recognised`] is the schedule with the σ each model constant needs added,
//! and [`Recognised::model_of`]: the side table that says which model constant
//! carries `⟦T⟧`, `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧`, together with
//! [`Recognised::model_iota`], which says which theorem is `T.rec_k`'s rule on
//! a given constructor.
//!
//! # What changed, and why the module no longer splices
//!
//! *This module used to **generate** the model — `mini/src/nested_ev.rs`,
//! 2117 lines of Rust that built the specialised block, `pack`/`unpack`, the
//! round trips, the recursors and every ι rule as Lean terms and handed each to
//! [`crate::kernel::add`] — and then inserted the accepted declarations into
//! the run. `modelgen/` does that now, as an **export filter**: it reads the
//! `.ndjson`, splices the model in before each nested inductive, and writes the
//! `.ndjson` back out. `MODELGEN.md` §1 is the contract. Three things follow,
//! and each is a deletion here:*
//!
//! 1. *the model is **in the file**, so nothing is inserted;*
//! 2. *its declarations are the file's own, so they are scheduled, checked and
//!    interpreted by the ordinary pass — no seeding, no demand fixpoint, no
//!    dependency-order check;*
//! 3. *`⟦Eq.rec.{0,1}⟧` and the other constants the generated proofs reached
//!    for are named by declarations the pre-pass can see, so the foreign-demand
//!    walk that used to add them goes too.*
//!
//! What is left is the part that was always the point: **deciding whether a
//! model is there, and keying the export's names onto it.**
//!
//! # Why this is a *table* and not a name rule, still
//!
//! `⟦T⟧ := ⟦T._model.self⟧` could be spelled as a name rule: take the
//! declaration's name, append `_model.self`, look it up. **It must not be**, and
//! the argument is *stronger* now that the model arrives in the file rather
//! than being built here. A name rule answers for a constant that exists for
//! some other reason — a file that declares its own `Tree._model.self` gets its
//! interpretation silently substituted for the model's — and the counters would
//! report a working model. This project has paid for that once already, at
//! `_auxCarrier`, and `mini/tests/fixtures/nested_keying.lean`'s `UTree` is the
//! same input at this site: two nested declarations of one shape, and the file
//! itself has taken the name one of their models wants. `modelgen` declines
//! `UTree` for exactly that reason (`MODELGEN.md` §1.3) and this module must
//! reach the same verdict from the other side.
//!
//! So the table is filled only from declarations whose **statements** were
//! checked against the export's own, by [`shape`] below, and it is keyed on the
//! constant's own [`ModelKey`] — the σ included, because a recursor's motive
//! level is part of what is being keyed. A constant with no entry **declines**,
//! by name, in [`crate::zoneb::ensure`]; it never falls through to the class-(T)
//! walk and never falls back to a name.
//!
//! # The shape check is a **diagnostic**, and saying so is the point
//!
//! [`shape`] rebuilds each model declaration's statement from the export's own
//! — `MODELGEN.md` §1.1's property 1, read from the consumer's side — and
//! declines by name when it does not match. That is **not** what makes a
//! conclusion trustworthy. What makes it trustworthy is the certificate: every
//! model declaration is an ordinary declaration of the file, checked by mini's
//! kernel on the acceptance axis and carrying a derived typing on the evidence
//! axis, and a rule that fires does so through [`crate::eq_cash`] against a
//! theorem the file proved. A `_model` tower with the wrong statements produces
//! no certificate whatever this module does.
//!
//! What the check buys is the **reason string**. Without it a file whose
//! `Tree._model.rec_0` is not `Tree.rec`'s statement stops somewhere downstream
//! — `eq-cash-retarget`, or `iota: the model rule is not about the redex this
//! run is reducing` — naming where a value stopped rather than why. With it the
//! decline says `nested model recursor 0 does not state T.rec`, at the
//! declaration that owns the problem. This project has spent a great deal on
//! that distinction; the check is here to pay it back and for nothing else.
//!
//! It also fails **closed**, which is a second-order property and not the
//! argument: a mismatch declines rather than keying, so a wrong tower is
//! reported as "no model" rather than as a model whose conclusions never
//! arrive.
//!
//! # The instantiations, and the trap in them
//!
//! **Any instantiation of a modelled declaration is an instantiation of the
//! model.** If the file applies `T.rec.{3}` then `⟦T.rec.{3}⟧` is
//! `⟦T._model.rec_0.{3}⟧`, and nothing in `checker::instantiations` knows that
//! — it sees `T._model.rec_0` mentioned only by `T._model.iota_0_j`, which
//! nothing mentions at all. So the propagation is made here, at
//! [`Recognised::schedule`], from the σ the pre-pass gave the **export**
//! constant onto the model constant.
//!
//! The trap, paid for once on this arc and recorded so it is not paid again:
//! `checker::instantiations` closes its demand and then **defaults** — "a
//! declaration nothing demands is still checked, once per entry of
//! `DEFAULT_LEVELS`" — so `T.rec` is scheduled at `[0]` and `[1]` in every file
//! that declares a nested type, whether or not anything eliminates one. When
//! the model was *spliced* by this module, propagating off that padded schedule
//! pulled in `pack`, `unpack`, both round trips, both recursors, the
//! congruences and every ι theorem, twice: measured on `nested_keying`, 68 000
//! conversions in nine seconds became past 950 000 and out of 4 GB after nine
//! minutes.
//!
//! **That trap is not reachable in this design, and it is worth writing down
//! why rather than repeating the guard that used to avoid it.** The model's
//! declarations are the file's own, so the pre-pass has already scheduled every
//! one of them on its own account; a σ added here can only be one the export
//! constant was already going to be interpreted at. The old
//! `applied_at` sweep — "read the σ off the file's own declarations rather than
//! off the padded schedule" — existed because seeding a model *the file did not
//! contain* at a σ nothing applies is pure cost. Seeding one it does contain at
//! a σ it is already checked at is free.
//!
//! What is **not** free is that the model's recursors and ι theorems are
//! interpreted at **two** σ rather than one. That is real. The obvious reading
//! of it — "the defaulting applies to the model's own declarations, so teach
//! `checker::instantiations` this module's naming convention" — was written
//! here, and it is **wrong**; it is corrected in place rather than appended to
//! because a seat was briefed off it.
//!
//! Measured on `nested_keying` by counting the `(name, σ)` pairs the pre-pass
//! schedules, without changing any behaviour:
//!
//! * **`T._model.rec_k` is not "mentioned by nothing".** `T._model.iota_k_j`
//!   mentions it, so it is *demanded* at `[0]` and `[1]` — not defaulted there.
//!   Suppressing the default for it changes nothing.
//! * **`T._model.iota_k_j` is** defaulted; nothing mentions it. But
//!   [`Recognised::key`] then demands it at exactly the σ it keys `T.rec_k` at,
//!   and `T.rec` / `T.rec_1` are themselves at `[0]` and `[1]` **by the same
//!   default** — a file that declares a nested type need not eliminate one, and
//!   this one does not. The σ set is therefore unchanged, and suppressing the
//!   default for the ι theorems is *also* a no-op.
//!
//! So the doubling traces to the default on `T.rec_k`, an **ordinary**
//! declaration where the default is doing the job it exists for — not to the
//! model's names, and not to anything a convention exported to the other crate
//! could reach. `post == pre` for every one of this fixture's 48 scheduled
//! names: the propagation above is entirely subsumed by the pre-pass here.
//!
//! **And the doubling is the small half of the cost.** Of the 23 model-tower
//! names, 15 are monomorphic and already scheduled once; the tower is 31
//! scheduled pairs against the 23 it would be at one σ apiece, and the whole
//! file is 65 against 48. Truncating *every* declaration to a single σ — an
//! unreachable optimum, since it also drops genuinely demanded instantiations —
//! takes `nested_keying` from 9 775 526 conversions in 5m22 to 4 101 470 in
//! 2m17, and costs `constEv` 43 → 23 with `lazyFills` 0 → 71. **2.38× is the
//! ceiling on every scheduling-side fix together**; the `342×` this fixture is
//! quoted at (`MEASUREMENTS.md`) is the model being *in the file* at all.
//!
//! The standing fix is `MONOMORPH.md` §8, which deletes the schedule rather
//! than narrowing it — and §2.2's `--default 0` emits one copy of a
//! never-demanded group, which is this doubling, gone. Run **mono before
//! `modelgen`** and no convention is needed anywhere: the export is already
//! monomorphic, each `T` appears once per instantiation, and `modelgen` emits
//! one model per copy. Run mono *second* and the model's declarations are still
//! unreferenced — this module finds them by name — so mono would have to guess
//! their σ and this same defect reappears one layer along.
//!
//! # The boundary
//!
//! This module names no `Term`, `Thm`, `Ev` or `Interp`. It reads
//! `mini::Expr`s out of an [`Environment`], calls [`crate::nested::plan`], and
//! produces a table of `(Name, σ) -> Name` pairs of syntax. Everything that
//! reads a certificate is on the other side of [`Recognised::model_of`].

use std::collections::HashMap;

use crate::env::{ConstantInfo, Declaration, Environment, IndType};
use crate::expr::{get_app, Expr, Name, E};

/// A constant at an instantiation — the pair `crate::interp`'s `ConstKey`
/// is, spelled out rather than imported.
///
/// The two are the same type and the alias is deliberately *not* the one on the
/// interpretation side: `ci/check-mutual-blackbox.sh` scans this file for the
/// word `interp::`, and a module that produces a table the evidence layer
/// consumes has no business naming the store to do it. What crosses the
/// boundary is a `(Name, Vec<Level>) -> Name` map of syntax.
///
/// It widened with `ConstKey` (`LEVELPOLY.md` §5.3 step 2) and must stay
/// spelled out: the two are checked to agree by the compiler at every
/// assignment in `crate::run`, which is the only place they meet.
pub type ModelKey = (Name, Vec<crate::expr::Level>);

/// One nested declaration's outcome, whether or not a model was found for it.
#[derive(Clone, Debug)]
pub struct NestedRecord {
    /// The shape that stopped the model, as [`Missing::label`] spells it, or
    /// `None` when one was recognised and keyed.
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

/// Why a nested declaration got no model. Every variant is a **diagnostic**:
/// see the module header on what the check is and is not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Missing {
    /// No `T._model.self` in the environment. `MODELGEN.md` §1.3: the absence
    /// of the carrier is "no model", not an error — the filter declined the
    /// declaration and said which shape stopped it.
    ///
    /// This label says **where** the lookup stopped and not **why** the model
    /// is absent; the why is the filter's, and it is on the filter's stderr,
    /// which [`crate::convert`] writes through to the user (`nested model
    /// without funext`, say). Do not reach for a richer label here — this side
    /// does not know the reason and would have to guess one.
    NoCarrier,
    /// A model constant is declared at or after the declaration it models, so
    /// [`crate::ledger::fill_declaration`] cannot read it when it resolves
    /// `⟦T⟧`.
    Later,
    /// `T._model.self` is not a `def`, or is not `T`'s own type.
    Carrier,
    /// A `T._model.ctor_j` is absent or is not the `j`-th constructor's
    /// statement.
    Ctor,
    /// A `T._model.rec_k` is absent or is not `T.rec_k`'s statement.
    Rec,
    /// A `T._model.iota_k_j` is absent, or its statement is not an equation
    /// about `T._model.rec_k` applied to a constructor.
    Iota,
    /// The export declares a recursor rule on a constructor no ι theorem is
    /// about. Distinct from [`Missing::Iota`]: the theorem is there and states
    /// something, and it is not this rule.
    IotaRule,
}

impl Missing {
    pub fn label(self) -> &'static str {
        match self {
            Missing::NoCarrier => "no nested model in the export",
            Missing::Later => "nested model over a later declaration",
            Missing::Carrier => "nested model carrier does not state the declaration's type",
            Missing::Ctor => "nested model constructor does not state the export's",
            Missing::Rec => "nested model recursor does not state the export's",
            Missing::Iota => "nested model iota rule is not an equation about the model recursor",
            Missing::IotaRule => "nested model has no iota rule for a constructor the export's recursor reduces on",
        }
    }
}

/// The keying of a file's nested declarations onto the models the export
/// carries.
pub struct Recognised {
    /// The caller's schedule, with the σ each model constant needs added — see
    /// the module header's "the instantiations, and the trap in them".
    pub schedule: HashMap<Name, Vec<Vec<u32>>>,
    /// **The keying.** `⟦export constant.{σ}⟧` is `⟦model constant.{σ}⟧`, for
    /// exactly the pairs a model was recognised for.
    pub model_of: HashMap<ModelKey, Name>,
    /// **The rules.** `((T.rec_k, σ), the export's constructor) ↦ the model's ι
    /// theorem`, for exactly the rules this pass recognised.
    ///
    /// The key is what a dispatch site holds: [`crate::iota_model::fire`] has
    /// the recursor it is reducing, the σ it is reducing at, and the major's
    /// head constructor, and nothing else. A rule with no entry **declines**
    /// there, by name; there is no name rule and no fall-through, for
    /// [`Recognised::model_of`]'s reason.
    pub model_iota: HashMap<(ModelKey, Name), Name>,
    /// Every nested declaration this pass saw, by its own name.
    pub nested: HashMap<Name, NestedRecord>,
    /// Nested declarations seen, and models recognised. `modelled ≤ seen`, and
    /// the difference is the [`NestedRecord::why`] population.
    pub seen: usize,
    pub modelled: usize,
}

/// `T._model` — the prefix every name in `MODELGEN.md` §1 hangs off.
fn model_prefix(t: &Name) -> Name { Name::str(t, "_model") }

/// `T._model.self`, the carrier.
pub fn carrier_name(t: &Name) -> Name { Name::str(&model_prefix(t), "self") }

/// `T._model.ctor_j`.
fn ctor_name(t: &Name, j: usize) -> Name { Name::str(&model_prefix(t), &format!("ctor_{j}")) }

/// `T._model.rec_k`. **The model's index is the member index uniformly**, so
/// the export's `T.rec` is `T._model.rec_0` — `MODELGEN.md` §1.
fn rec_name(t: &Name, k: usize) -> Name { Name::str(&model_prefix(t), &format!("rec_{k}")) }

/// `T._model.iota_k_j`.
fn iota_name(t: &Name, k: usize, j: usize) -> Name {
    Name::str(&model_prefix(t), &format!("iota_{k}_{j}"))
}

/// **Recognise each nested declaration's model, and key it.**
///
/// A declaration that is not nested is ignored, and so is one whose model is
/// absent or does not state what the export states — with its reason recorded
/// in [`Recognised::nested`] so that the decline downstream names a shape.
pub fn recognise(
    env: &Environment,
    decls: &[Declaration],
    schedule: &HashMap<Name, Vec<Vec<u32>>>,
) -> Recognised {
    let mut out = Recognised {
        schedule: schedule.clone(),
        model_of: HashMap::new(),
        model_iota: HashMap::new(),
        nested: HashMap::new(),
        seen: 0,
        modelled: 0,
    };
    // Which declaration in the list settles each name, by position. Read to
    // check that the model is *behind* the declaration it models — see the
    // header, and [`Missing::Later`].
    let pos = positions(env, decls);
    // What the file's own declarations name, and at which ground σ. The
    // pre-pass's schedule is the other half; a recursor is keyed at the union,
    // for the reason the header gives.
    let applied = applied_at(decls, schedule);
    for (i, d) in decls.iter().enumerate() {
        let Declaration::Inductive { name, lparams, num_params, ty, ctors } = d else { continue };
        let types =
            vec![IndType { name: *name, ty: *ty, ctors: ctors.clone() }];
        // **`nested::plan` answers "is this nested", and nothing else does.**
        // Not the export's `is_nested` flag, which `convert::load` has already
        // consumed at the parser gate, and not a name: the question here is
        // whether a constructor field mentions the declaration under a foreign
        // inductive, which is the same question the specialisation asks.
        match crate::nested::plan(env, lparams, *num_params, &types) {
            Ok(Some(_)) => {}
            // `Ok(None)` is an ordinary declaration. `Err` is a nested one the
            // specialiser cannot express — the file would not have been
            // accepted, so it cannot arise here.
            _ => continue,
        }
        out.seen += 1;
        match shape(env, name, ctors, &pos, i) {
            Ok(m) => {
                out.modelled += 1;
                out.key(env, name, &m, &applied);
            }
            Err(why) => out.decline(env, name, ctors, why),
        }
    }
    for v in out.schedule.values_mut() {
        v.sort();
        v.dedup();
    }
    out
}

/// A recognised model: the export constant beside the model constant that
/// carries its interpretation, and the rules.
struct Model {
    /// `(export constant, model constant)` for the type former and each
    /// constructor, keyed at `σ = []`.
    ///
    /// **The declaration's own level parameters are compared but not keyed
    /// over**, and that is a limitation rather than a claim: `modelgen` grew
    /// universe-polymorphic support after this was written, so the statements
    /// are checked at the export's own `ℓ⃗` (see [`at_export_levels`]) while
    /// the store key here is the empty σ. Every nested fixture mini has is
    /// monomorphic, so the two coincide; a polymorphic one would need the σ
    /// the pre-pass scheduled `T` at, exactly as a recursor does below.
    mono: Vec<(Name, Name)>,
    /// `(export recursor, model recursor)`, in member order.
    recs: Vec<(Name, Name)>,
    /// `(export recursor, the rule's constructor, the model's ι theorem)`.
    iotas: Vec<(Name, Name, Name)>,
}

impl Recognised {
    /// Fill the tables for one recognised model, and propagate its σ.
    fn key(
        &mut self,
        env: &Environment,
        name: &Name,
        m: &Model,
        applied: &HashMap<Name, Vec<Vec<u32>>>,
    ) {
        let mut constants: Vec<Name> = Vec::new();
        // The type former and the constructors have no universe parameters of
        // their own, so `σ = []` is the whole population.
        for (export, model) in &m.mono {
            self.model_of.insert((*export, Vec::new()), *model);
            self.demand(model, &[Vec::new()]);
            constants.push(*export);
        }
        // **A recursor is keyed at every σ the run will ask for it at**, and
        // the same σ are propagated onto the model — the header's "any
        // instantiation of a modelled declaration is an instantiation of the
        // model". The union of the pre-pass's schedule and the file's own
        // applications: the first is what `Ledger::run` will interpret the
        // export's recursor at, the second is what a use site inside an
        // already-scheduled declaration reaches for.
        let mut sigmas_of: HashMap<Name, Vec<Vec<u32>>> = HashMap::new();
        for (export, model) in &m.recs {
            let mut sigmas: Vec<Vec<u32>> = self.schedule.get(export).cloned().unwrap_or_default();
            for s in applied.get(export).into_iter().flatten() {
                if !sigmas.contains(s) {
                    sigmas.push(s.clone());
                }
            }
            for s in &sigmas {
                self.model_of.insert((*export, crate::ground::ground_levels(s)), *model);
            }
            self.demand(model, &sigmas);
            sigmas_of.insert(*export, sigmas);
            constants.push(*export);
        }
        // A rule is keyed at the σ its recursor was keyed at, and at no other:
        // a rule at a σ the recursor has no interpretation at is a rule about a
        // redex this run cannot name.
        for (export, ctor, thm) in &m.iotas {
            let Some(sigmas) = sigmas_of.get(export) else { continue };
            for s in sigmas {
                self.model_iota
                    .insert(((*export, crate::ground::ground_levels(s)), *ctor), *thm);
            }
            self.demand(thm, sigmas);
        }
        let _ = env;
        self.nested.insert(*name, NestedRecord { why: None, constants });
    }

    /// Add σ to a model constant's schedule entry. **Never a default**: a
    /// constant reached with an empty σ list keeps whatever the pre-pass gave
    /// it, and a σ that is not propagated is a σ the keying above did not
    /// record either, so the two cannot disagree.
    fn demand(&mut self, n: &Name, sigmas: &[Vec<u32>]) {
        if sigmas.is_empty() {
            return
        }
        let e = self.schedule.entry(*n).or_default();
        for s in sigmas {
            if !e.contains(s) {
                e.push(s.clone());
            }
        }
    }

    /// Record a nested declaration with no model: the shape that stopped it,
    /// filed under every constant the model would have keyed.
    fn decline(&mut self, env: &Environment, name: &Name, ctors: &[(Name, E)], why: Missing) {
        let mut constants = vec![*name];
        constants.extend(ctors.iter().map(|(c, _)| *c));
        constants.extend(export_recs(env, name).into_iter().map(|(n, _)| n));
        self.nested
            .insert(*name, NestedRecord { why: Some(why.label()), constants });
    }
}

/// **Every recursor the export declares for `T`, in member order** — `T.rec`,
/// `T.rec_1`, `T.rec_2`, … — with its [`ConstantInfo`].
///
/// Read off the environment and not off a [`crate::nested::Plan`]: the plan's
/// member count is a *prediction* of how many recursors the declaration owns,
/// and the environment is what it actually owns. `env.owner` is checked as well
/// as the name, so a file's own `T.rec_1` that belongs to something else stops
/// the walk instead of being taken for a member.
fn export_recs<'e>(env: &'e Environment, t: &Name) -> Vec<(Name, &'e ConstantInfo)> {
    let mut out = Vec::new();
    for k in 0.. {
        let n = crate::nested::Plan::rec_name(t, k);
        let Some(ci @ ConstantInfo::Recursor { .. }) = env.get(&n) else { break };
        if env.owner(&n) != Some(t) {
            break
        }
        out.push((n, ci));
    }
    out
}

/// **The model, read out of the environment and checked against the export's
/// own statements.**
///
/// `MODELGEN.md` §1.1's property 1 from the consumer's side: take the export's
/// declared type, rewrite `T ↦ T._model.self`, `T.ctorⱼ ↦ T._model.ctor_j`,
/// `T.rec_m ↦ T._model.rec_m`, and the result must be the model declaration's
/// declared type **on the nose**. Property 2 is read the other way round: the
/// ι theorem's own left-hand side says which constructor it is about, and that
/// is compared against the rule the export's recursor carries at that index.
///
/// See the module header: this is a diagnostic. It fails closed, and it is not
/// what makes a conclusion trustworthy.
fn shape(
    env: &Environment,
    t: &Name,
    ctors: &[(Name, E)],
    pos: &HashMap<Name, usize>,
    i: usize,
) -> Result<Model, Missing> {
    let self_n = carrier_name(t);
    let recs = export_recs(env, t);

    // The rewriting, built before anything is compared. Its *keys* are the
    // export's names and its values the model's; a value that does not exist
    // is caught at the lookup that needs it, with the reason that names which
    // part of the tower is missing, rather than in one sweep that would report
    // every absence as the same thing.
    let mut rho: HashMap<Name, Name> = HashMap::new();
    rho.insert(*t, self_n);
    for (j, (c, _)) in ctors.iter().enumerate() {
        rho.insert(*c, ctor_name(t, j));
    }
    for (k, (r, _)) in recs.iter().enumerate() {
        rho.insert(*r, rec_name(t, k));
    }

    // ── the carrier ─────────────────────────────────────────────────────────
    //
    // `∀p⃗, Sort u`, which is `T`'s own type: `modelgen` declines a declaration
    // with indices (`MODELGEN.md` §5), so there is nothing else it could be.
    //
    // **The absence of the carrier is `NoCarrier` and not an error**
    // (`MODELGEN.md` §1.3): the filter declined the declaration and said which
    // shape stopped it, and a consumer that treated that as a failure would
    // turn every unsupported nested shape into a broken file.
    let Some(carrier) = env.get(&self_n) else { return Err(Missing::NoCarrier) };
    settled(pos, &self_n, i)?;
    let ConstantInfo::Def { .. } = carrier else { return Err(Missing::Carrier) };
    let Some(t_ci @ ConstantInfo::Inductive { .. }) = env.get(t) else {
        return Err(Missing::Carrier)
    };
    if at_export_levels(carrier, t_ci).ok_or(Missing::Carrier)? != *t_ci.ty() {
        return Err(Missing::Carrier)
    }

    let mut mono: Vec<(Name, Name)> = vec![(*t, self_n)];
    for (j, (c, c_ty)) in ctors.iter().enumerate() {
        let m = ctor_name(t, j);
        let Some(ci) = env.get(&m) else { return Err(Missing::Ctor) };
        settled(pos, &m, i)?;
        // At the *declaration's* level parameters, for [`at_export_levels`]'s
        // reason: `MODELGEN.md` §1 says every generated constant carries `ℓ⃗`,
        // and the export's constructor carries the declaration's own.
        let at = crate::env::instantiate_lparams(
            ci.ty(),
            ci.lparams(),
            &t_ci.lparams().iter().map(|n| crate::expr::Level::param(*n)).collect::<Vec<_>>(),
        );
        if ci.lparams().len() != t_ci.lparams().len()
            || at.ok().as_ref() != Some(&rename(&rho, c_ty))
        {
            return Err(Missing::Ctor)
        }
        mono.push((*c, m));
    }

    // ρ read backwards, for [`iota_key`]: an ι theorem's major is written in
    // the *model's* names at the root — `T._model.ctor_j`, because
    // `MODELGEN.md` §1.1's rewriting reaches into the rule's own statement —
    // and in the container's at a mimic, where `List.cons` is nobody's model
    // and is left alone. So the head read off the statement is mapped back
    // through ρ when it is a model constant and taken as it stands when it is
    // not.
    let back: HashMap<Name, Name> =
        rho.iter().map(|(e, m)| (*m, *e)).collect();

    let mut out_recs: Vec<(Name, Name)> = Vec::new();
    let mut iotas: Vec<(Name, Name, Name)> = Vec::new();
    for (k, (r, r_ci)) in recs.iter().enumerate() {
        let m = rec_name(t, k);
        let Some(ci) = env.get(&m) else { return Err(Missing::Rec) };
        settled(pos, &m, i)?;
        if at_export_levels(ci, r_ci).ok_or(Missing::Rec)? != rename(&rho, r_ci.ty()) {
            return Err(Missing::Rec)
        }
        // The rules, by index. `MODELGEN.md` §1.1's property 2 says a consumer
        // may line ι theorems up with rules by index and check the key by name
        // — so that is what this does, and the key it checks is read off the
        // theorem's **own left-hand side** rather than trusted from the index.
        let ConstantInfo::Recursor { rules, .. } = r_ci else { return Err(Missing::Rec) };
        for (j, (rule_ctor, _)) in rules.iter().enumerate() {
            let thm = iota_name(t, k, j);
            let Some(thm_ci) = env.get(&thm) else { return Err(Missing::Iota) };
            settled(pos, &thm, i)?;
            if thm_ci.lparams().len() != r_ci.lparams().len() {
                return Err(Missing::Iota)
            }
            let Some(about) = iota_key(thm_ci.ty(), &m, &back) else { return Err(Missing::Iota) };
            if about != *rule_ctor {
                return Err(Missing::IotaRule)
            }
            iotas.push((*r, *rule_ctor, thm));
        }
        out_recs.push((*r, m));
    }
    Ok(Model { mono, recs: out_recs, iotas })
}

/// The model constant is settled strictly before position `i`, where
/// [`crate::ledger::fill_declaration`] will read it.
///
/// `⟦T⟧` is resolved at `T`'s own position out of `⟦T._model.self⟧`, so a
/// model declared level with — or after — the declaration it models is one the
/// alias cannot look up. `modelgen` splices the model *before* the nested
/// inductive, so this holds for anything it wrote; it is checked because a
/// `_model` name in the file is not necessarily one it wrote.
fn settled(pos: &HashMap<Name, usize>, n: &Name, i: usize) -> Result<(), Missing> {
    match pos.get(n) {
        Some(j) if *j < i => Ok(()),
        _ => Err(Missing::Later),
    }
}

/// **The model recursor's declared type, at the export recursor's own universe
/// parameters** — `None` when the two do not bind the same number of them.
///
/// Positional and not by name, and that is a **correction to `MODELGEN.md`
/// §1.1's property 3**, which says the model "carries `T.rec_k`'s single
/// motive-universe parameter, under the same name". It carries the name the
/// *export file* wrote, and mini does not use the export's recursor: it
/// generates its own in `kernel::add_block`, whose motive parameter is
/// `fresh_level_name`'s `v` where every export in the corpus writes `u`. The
/// names are an artefact of two generators and the *position* is the contract,
/// which is also what every consumer of the table needs — `zoneb`'s
/// `model_alias` and [`crate::iota_model::fire`] both carry the redex's σ
/// across positionally and neither has a name to carry.
fn at_export_levels(model: &ConstantInfo, export: &ConstantInfo) -> Option<E> {
    if model.lparams().len() != export.lparams().len() {
        return None
    }
    let us: Vec<crate::expr::Level> =
        export.lparams().iter().map(|n| crate::expr::Level::param(*n)).collect();
    crate::env::instantiate_lparams(model.ty(), model.lparams(), &us).ok()
}

/// **Which constructor an ι theorem is about, read off its own statement.**
///
/// The statement is `∀p⃗ M⃗ S⃗ f⃗, Eq α (rec_k p⃗ M⃗ S⃗ (c f⃗)) rhs`. This peels the
/// ∀-nest, checks the body is an `Eq` of three arguments whose left-hand side
/// is an application of `rec` — the model recursor the caller is asking about,
/// by name, because that is the identity the whole table turns on — and returns
/// the head constant of that application's **last** argument, which is the
/// major premise.
///
/// `None` is "this is not an equation about that recursor at a constructor",
/// which is [`Missing::Iota`]. It is deliberately not "the theorem is about
/// some other recursor": a theorem naming a *different* model recursor on its
/// left is exactly as unusable here, and splitting the two would be a reason
/// string with no input behind it.
fn iota_key(ty: &E, rec: &Name, back: &HashMap<Name, Name>) -> Option<Name> {
    let mut body = *ty;
    while let Expr::Forall { body: b, .. } = body.view() {
        body = b;
    }
    let (head, args) = get_app(&body);
    let Expr::Const(eq, _) = &head.view() else { return None };
    if *eq != Name::simple("Eq") || args.len() != 3 {
        return None
    }
    let (lhs_head, lhs_args) = get_app(&args[1]);
    let Expr::Const(r, _) = &lhs_head.view() else { return None };
    if r != rec {
        return None
    }
    let major = lhs_args.last()?;
    match get_app(major).0.view() {
        Expr::Const(c, _) => Some(*back.get(&c).unwrap_or(&c)),
        _ => None,
    }
}

/// Rewrite every `Const` head named in `rho`, keeping its level list.
fn rename(rho: &HashMap<Name, Name>, e: &E) -> E {
    match &e.view() {
        Expr::Const(n, ls) => match rho.get(n) {
            Some(m) => crate::expr::konst(*m, ls.clone()),
            None => *e,
        },
        Expr::App(f, x) => crate::expr::app(rename(rho, f), rename(rho, x)),
        Expr::Forall { ty, body } => crate::expr::forall(rename(rho, ty), rename(rho, body)),
        Expr::Lam { ty, body } => crate::expr::lam(rename(rho, ty), rename(rho, body)),
        Expr::Let { ty, val, body } => crate::expr::let_(rename(rho, ty), rename(rho, val), rename(rho, body)),
        Expr::Proj { ind, idx, s } => crate::expr::proj(*ind, *idx, rename(rho, s)),
        _ => *e,
    }
}

/// **Every constant the file's own declarations name, at every ground σ they
/// name it at** — one sweep, not a fixpoint.
///
/// `checker::instantiations::compute` runs the same sweep and then closes it
/// and pads it. What this asks is narrower and is the honest reading of "the
/// file applies `T.rec_k`": some declaration of the file has `T.rec_k.{ℓ⃗}` in
/// its type or its value, and `ℓ⃗` evaluates under a σ that declaration is
/// interpreted at. An occurrence whose levels do not evaluate — a symbolic one
/// — is skipped, exactly as the pre-pass skips it.
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
    match &e.view() {
        Expr::Const(n, ls) => {
            if let Some(s) = ls.iter().map(|l| crate::ground::eval(l, map)).collect() {
                out.push((*n, s));
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

/// Which position in the declaration list each name is settled by: a
/// declaration's own name, and — for an inductive or a block — every
/// constructor and recursor the environment says it owns.
fn positions(env: &Environment, decls: &[Declaration]) -> HashMap<Name, usize> {
    let mut owner_pos: HashMap<Name, usize> = HashMap::new();
    for (i, d) in decls.iter().enumerate() {
        owner_pos.insert(d.name(), i);
        if let Declaration::Mutual { types, .. } = d {
            for t in types {
                owner_pos.insert(t.name, i);
            }
        }
    }
    let mut out = owner_pos.clone();
    for (n, o) in &env.owners {
        if let Some(i) = owner_pos.get(o) {
            out.insert(*n, *i);
        }
    }
    out
}
