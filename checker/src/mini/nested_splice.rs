//! **Step 3 of the nested arc: the model the *export* already carries,
//! recognised, and the keying that makes it the declaration's interpretation.**
//!
//! # Interface
//!
//! ```text
//! nested_splice::Recogniser         one declaration at a time
//! nested_splice::recognise(env, decls, schedule) -> Recognised
//! ```
//!
//! [`Recognised`] is the schedule with the σ each model constant needs added,
//! and [`Recognised::model_of`]: the side table that says which model constant
//! carries `⟦T⟧`, `⟦T.ctorᵢ⟧` and `⟦T.rec_k⟧`, together with
//! [`Recognised::model_iota`], which says which theorem is `T.rec_k`'s rule on
//! a given constructor.
//!
//! [`Recogniser`] is the same thing as a loop body, which is what
//! [`crate::mini::decl_pass`] drives; [`recognise`] is it over a whole file, and is
//! what `mini/tests/nested.rs` asks directly. **The per-declaration form needs
//! nothing the whole-file form has**, and the reason is [`settled`]: a model at
//! or after the declaration it models is [`Missing::Later`] whatever the
//! environment holds, so every lookup either resolves in the prefix or is a
//! decline in both forms.
//!
//! # What changed, and why the module no longer splices
//!
//! *This module used to **generate** the model — `mini/src/nested_ev.rs`,
//! 2117 lines of Rust that built the specialised block, `pack`/`unpack`, the
//! round trips, the recursors and every ι rule as Lean terms and handed each to
//! [`crate::mini::kernel::add`] — and then inserted the accepted declarations into
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
//! # Two producers, and the difference is the **key** rather than the spelling
//!
//! There are two filters that write a model tower, and this module reads both
//! — [`Scheme`] is which. They do not share a single name, and reading the
//! difference as a rename undersells it.
//!
//! | | carrier | constructor `j` of `T`, named `c` | recursor `k`, named `r` | rule `j` of `r` |
//! | --- | --- | --- | --- | --- |
//! | [`Scheme::Legacy`] (`modelgen/`) | `T._model.self` | `T._model.ctor_j` | `T._model.rec_k` | `T._model.iota_k_j` |
//! | [`Scheme::Tool`] (`lean-inductive-models`) | `T._model` | `c._model` | `r._model` | `r._model.iota_j` |
//!
//! **Legacy makes `_model` a namespace under the type former** and names every
//! leaf by a role word plus a position, so `T`'s name is the only input the
//! scheme takes and everything below it is an index. **The tool has one
//! name-forming operation, `modelName n = n._model`
//! (`vendor/lean-inductive-models/src/InductiveModels/Naming.lean:77`), applied
//! to the exact declaration being modelled** — the type former, each
//! constructor and each recursor alike. An index survives in exactly one place
//! here, and it is the place where the modelled thing has no declaration of its
//! own: a recursor *rule* is a field of the recursor, so it is `iota_j` under
//! `r._model`.
//!
//! Three consequences that are not spelling:
//!
//! 1. **Constructor order leaves the contract.** `T._model.ctor_j` couples the
//!    table to the order of the export's `ctors` array; `c._model` couples it to
//!    nothing. Same for the recursors.
//! 2. **A declaration that does not live below `T` is nameable.** `Naming.lean`
//!    is emphatic that a private constructor need not be in its inductive's
//!    namespace, so prefix substitution "is not a naming model". Legacy has no
//!    way to say that; the tool needs no way, because it never leaves the
//!    declaration's own name.
//! 3. **The tool has slots this module has no table for**: `T._model.proj_i`
//!    and `T._model.proj_i.iota` for an intrinsic structure projection — which
//!    models no source constant at all and is therefore indexed off the type
//!    former — and the metadata theorems `T._model.eta`, `T._model.unitlike`
//!    and `r._model.ruleK`. None is a *nested* declaration's business and none
//!    is read here; they are what generalising past nesting has to grow.
//!
//! The private bookkeeping moved too and is not this module's concern either
//! way: `modelgen` put `pack_0`/`unpack_0` in the same namespace as the public
//! API, the tool roots it at `T._model._impl.*` and its README says it is not
//! API. Nothing here looks at it.
//!
//! [`Scheme::Legacy`] is transitional and goes when `modelgen/` does. It is
//! still read because `modelgen/` is still what makes `init-prelude` accept.
//!
//! # Why this is a *table* and not a name rule, still
//!
//! `⟦T⟧ := ⟦T._model⟧` could be spelled as a name rule: take the declaration's
//! name, append `_model`, look it up. **It must not be**, and the argument is
//! *stronger* now that the model arrives in the file rather than being built
//! here, and stronger again under the tool's scheme — where `c._model` sits in
//! a namespace an ordinary file legitimately owns, which `T._model.self` never
//! did. A name rule answers for a constant that exists for some other reason —
//! a file that declares its own `Tree._model` gets its interpretation silently
//! substituted for the model's — and the counters would report a working model.
//! This project has paid for that once already, at `_auxCarrier`.
//!
//! So the table is filled only from declarations whose **statements** were
//! checked against the export's own, by [`shape`] below, and it is keyed on the
//! constant's own [`ModelKey`] — the σ included, because a recursor's motive
//! level is part of what is being keyed. A constant with no entry **declines**,
//! by name, in [`crate::mini::zoneb::ensure`]; it never falls through to the class-(T)
//! walk and never falls back to a name.
//!
//! **`nested_keying`'s `UTree` is still the input that says so, and the rename
//! moved which half of the guard it exercises.** The file declares its own
//! `UTree._model.self`. Under legacy that is the carrier's name, and what
//! stopped it was the *position* check in [`model_const`] — the squatter is
//! declared after `UTree` — because `def UTree._model.self : Type := N` has
//! exactly `UTree`'s declared type and passes the statement check. Under the
//! tool's scheme it is an unrelated definition, `UTree` models normally, and
//! the guard that now carries the weight is the statement check on
//! `UTree._model`. Both are pinned:
//! `mini_nested::the_recognition_reads_the_external_tools_names` asserts what
//! `⟦UTree⟧` is keyed *to*, and
//! `mini_nested::a_tool_carrier_that_states_something_else_is_not_adopted`
//! deletes the statement check and is the only test that notices.
//!
//! The producer guards the same boundary from its side and by a different
//! mechanism, which is worth knowing and worth not relying on:
//! `Naming.Table.collisionCensus` refuses to generate a family any of whose
//! required public names is already taken in the input, and
//! `Table.originalName?` is "a table lookup, not an attempt to parse `_model`
//! from `model`". That is the producer's business. Ours is the certificate;
//! see the next section.
//!
//! # The shape check is a **diagnostic**, and saying so is the point
//!
//! [`shape`] rebuilds each model declaration's statement from the export's own
//! — `MODELGEN.md` §1.1's property 1, read from the consumer's side — and
//! declines by name when it does not match. That is **not** what makes a
//! conclusion trustworthy. What makes it trustworthy is the certificate: every
//! model declaration is an ordinary declaration of the file, checked by mini's
//! kernel on the acceptance axis and carrying a derived typing on the evidence
//! axis, and a rule that fires does so through [`crate::mini::eq_cash`] against a
//! theorem the file proved. A `_model` tower with the wrong statements produces
//! no certificate whatever this module does.
//!
//! What the check buys is the **reason string**. Without it a file whose
//! `Tree.rec._model` is not `Tree.rec`'s statement stops somewhere downstream
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
//! `⟦T.rec._model.{3}⟧`, and nothing in `checker::instantiations` knows that
//! — it sees `T.rec._model` mentioned only by `T.rec._model.iota_j`, which
//! nothing mentions at all. So the propagation is made here, at
//! [`Recognised::schedule`], from the σ the pre-pass gave the **export**
//! constant onto the model constant.
//!
//! **The rename does not move this, and the reason is worth stating rather than
//! re-measuring.** `checker::instantiations` builds its mention graph by
//! walking `Expr::Const` occurrences; it contains no `_model` string and no
//! name-shape rule of any kind, so renaming a node renames a node and leaves
//! every edge where it was. Both facts below therefore transfer verbatim from
//! `T._model.rec_k` to `r._model` and from `T._model.iota_k_j` to
//! `r._model.iota_j`: the recursor's model is *mentioned* by its own ι
//! theorems' statements, and the ι theorems are mentioned by nothing and
//! defaulted. Seeding and defaulting are unchanged.
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
//! schedules, without changing any behaviour. The names below are
//! [`Scheme::Legacy`]'s because that is the fixture the measurement was taken
//! on; the paragraph above says why the conclusion is the tool's too:
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
//! `mini::Expr`s out of an [`Environment`], calls [`crate::mini::nested::plan`], and
//! produces a table of `(Name, σ) -> Name` pairs of syntax. Everything that
//! reads a certificate is on the other side of [`Recognised::model_of`].

use std::collections::HashMap;

use crate::mini::env::{ConstantInfo, Declaration, Environment, IndType};
use crate::mini::expr::{get_app, Expr, Name, E};

/// A constant at a ground instantiation — the pair `crate::mini::interp`'s `ConstKey`
/// is, spelled out rather than imported.
///
/// The two are the same type and the alias is deliberately *not* the one on the
/// interpretation side: `ci/check-mutual-blackbox.sh` scans this file for the
/// word `interp::`, and a module that produces a table the evidence layer
/// consumes has no business naming the store to do it. What crosses the
/// boundary is a `(Name, Vec<u32>) -> Name` map of syntax.
pub type ModelKey = (Name, Vec<u32>);

/// One nested declaration's outcome, whether or not a model was found for it.
#[derive(Clone, Debug)]
pub struct NestedRecord {
    /// The shape that stopped the model, as [`Missing::label`] spells it, or
    /// `None` when one was recognised and keyed.
    ///
    /// A `Some` here is what [`crate::mini::zoneb::ensure`] reports instead of
    /// walking the declaration's constructor spec — which would answer
    /// `nested occurrence`, the true but least informative of the reasons.
    pub why: Option<&'static str>,
    /// The export constants the model is responsible for, in fill order: the
    /// type former, its constructors, then **every** recursor the declaration
    /// owns.
    ///
    /// `T.rec_1` and `T.rec_2` are the reason this list exists.
    /// [`crate::mini::ledger::fill_declaration`]'s own list is `T`, its constructors
    /// and `T.rec`, which is every recursor an *ordinary* declaration has; a
    /// nested one has one per specialised member, and the ones past the first
    /// would otherwise be reached only by the lazy-fill path.
    pub constants: Vec<Name>,
}

/// Why a nested declaration got no model. Every variant is a **diagnostic**:
/// see the module header on what the check is and is not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Missing {
    /// No carrier in the environment under **either** [`Scheme`] — neither
    /// `T._model` nor `T._model.self`. `MODELGEN.md` §1.3: the absence of the
    /// carrier is "no model", not an error — the filter declined the
    /// declaration and said which shape stopped it.
    ///
    /// This label says **where** the lookup stopped and not **why** the model
    /// is absent; the why is the filter's, and it is on the filter's stderr,
    /// which [`crate::mini::convert`] writes through to the user (`nested model
    /// without funext`, say). Do not reach for a richer label here — this side
    /// does not know the reason and would have to guess one.
    NoCarrier,
    /// A model constant is declared at or after the declaration it models, so
    /// [`crate::mini::ledger::fill_declaration`] cannot read it when it resolves
    /// `⟦T⟧`.
    Later,
    /// The carrier is not a `def`, or is not `T`'s own type. Reachable only
    /// under [`Scheme::Legacy`]: a carrier that fails this under
    /// [`Scheme::Tool`] is not a tool tower, so [`Recogniser::step`] reads the
    /// legacy one instead and reports that scheme's verdict.
    Carrier,
    /// The `j`-th constructor's model is absent or is not its statement.
    Ctor,
    /// The `k`-th recursor's model is absent or is not `T.rec_k`'s
    /// statement.
    Rec,
    /// A rule's ι theorem is absent, or its statement is not an equation
    /// about the recursor's model applied to a constructor.
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
    /// The key is what a dispatch site holds: [`crate::mini::iota_model::fire`] has
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
    /// **`modelled`, split by which producer wrote the tower** —
    /// `modelled_tool + modelled_legacy == modelled`.
    ///
    /// It exists because a rename that stopped recognising and started
    /// declining leaves `seen` and every downstream total exactly where they
    /// were: the declines are simply counted elsewhere. A split adoption count
    /// is what says *which* names were read, and it is asserted per fixture in
    /// `checker/tests/mini_nested.rs`.
    pub modelled_tool: usize,
    pub modelled_legacy: usize,
}

/// `X._model` — the one name-forming operation the external producer has, read
/// off `vendor/lean-inductive-models/src/InductiveModels/Naming.lean:77`,
/// `def modelName (n : Name) : Name := Name.str n "_model"`.
fn model_suffix(x: &Name) -> Name { Name::str(x, "_model") }

/// **Which producer wrote a model tower**, and therefore how its declarations
/// are named. See the module header's "two producers, and the difference is
/// the key rather than the spelling".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scheme {
    /// `lean-inductive-models`, the external producer, which is authoritative.
    /// **`_model` is a suffix on the exact declaration being modelled**, so the
    /// carrier is `T._model`, constructor `C`'s model is `C._model` and
    /// recursor `R`'s is `R._model`; only a declaration that models no source
    /// constant is named off an index, and rule `j` of `R` is the one this
    /// module needs — `R._model.iota_j`.
    Tool,
    /// `modelgen/`, this repository's own filter, which is being retired.
    /// **`_model` is a namespace under the type former** and every leaf is a
    /// role word plus a position: `T._model.self`, `T._model.ctor_j`,
    /// `T._model.rec_k`, `T._model.iota_k_j`.
    ///
    /// Kept only because `modelgen/` is still what makes `init-prelude`
    /// accept, and it is not this tranche's to change. **It goes with
    /// `modelgen/`**; nothing new should be written against it.
    Legacy,
}

impl Scheme {
    /// The carrier: `⟦T⟧`'s model.
    fn carrier(self, t: &Name) -> Name {
        match self {
            Scheme::Tool => model_suffix(t),
            Scheme::Legacy => Name::str(&model_suffix(t), "self"),
        }
    }

    /// Constructor `j` of `T`, whose own exported name is `c`.
    ///
    /// **The two arguments are not both used, and that is the difference.**
    /// [`Scheme::Tool`] reads `c` and ignores `(t, j)`, so a constructor that
    /// does not live below `T` — `Naming.lean:20-27` says a private one need
    /// not — is still nameable, and the order of the `ctors` array is not part
    /// of the contract. [`Scheme::Legacy`] reads `(t, j)` and ignores `c`.
    fn ctor(self, t: &Name, j: usize, c: &Name) -> Name {
        match self {
            Scheme::Tool => model_suffix(c),
            Scheme::Legacy => Name::str(&model_suffix(t), &format!("ctor_{j}")),
        }
    }

    /// Recursor `k` of `T`, whose own exported name is `r` — `T.rec`,
    /// `T.rec_1`, … for `k = 0, 1, …`.
    fn rec(self, t: &Name, k: usize, r: &Name) -> Name {
        match self {
            Scheme::Tool => model_suffix(r),
            Scheme::Legacy => Name::str(&model_suffix(t), &format!("rec_{k}")),
        }
    }

    /// Rule `j` of recursor `k`, whose own exported name is `r`.
    ///
    /// A rule is a *field* of a recursor and has no exported declaration of its
    /// own, so this is the one place [`Scheme::Tool`] still spends an index —
    /// `Naming.lean:79-83`, "rule numbers are positions in the export's
    /// recursor-rule array".
    fn iota(self, t: &Name, k: usize, r: &Name, j: usize) -> Name {
        match self {
            Scheme::Tool => Name::str(&model_suffix(r), &format!("iota_{j}")),
            Scheme::Legacy => Name::str(&model_suffix(t), &format!("iota_{k}_{j}")),
        }
    }
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
    let mut sched = schedule.clone();
    let mut r = Recogniser::new(decls, schedule);
    // The whole-file form observes every declaration first, so `pos` is what
    // one `positions(env, decls)` sweep gave. The incremental form observes
    // each declaration as it arrives, which is the same map restricted to the
    // prefix — and [`settled`] cannot tell the two apart, because a name at a
    // position `≥ i` and a name at no position are both [`Missing::Later`].
    for (i, d) in decls.iter().enumerate() {
        r.observe(env, i, d);
    }
    for (i, d) in decls.iter().enumerate() {
        r.step(env, i, d, &mut sched);
    }
    for v in sched.values_mut() {
        v.sort();
        v.dedup();
    }
    Recognised {
        schedule: sched,
        model_of: r.model_of,
        model_iota: r.model_iota,
        nested: r.nested,
        seen: r.seen,
        modelled: r.modelled,
        modelled_tool: r.modelled_tool,
        modelled_legacy: r.modelled_legacy,
    }
}

/// Add σ to a name's schedule entry, and leave the entry **sorted and
/// deduplicated**.
///
/// The whole-file passes used to normalise the schedule in one sweep at the
/// end, before anything read it. A per-declaration pipeline reads it as it goes
/// — `Ledger::walk_decl` iterates a name's σ in the order they sit in the list
/// — so normalisation happens at every write instead. `crate::mini::decl_pass`
/// normalises the pre-pass's own entries once, before the loop, for the same
/// reason: the end-of-file sweep used to cover those too.
pub(crate) fn add_sigmas(
    schedule: &mut HashMap<Name, Vec<Vec<u32>>>,
    n: Name,
    sigmas: impl IntoIterator<Item = Vec<u32>>,
) {
    let e = schedule.entry(n).or_default();
    e.extend(sigmas);
    e.sort();
    e.dedup();
}

/// [`recognise`], one declaration at a time.
///
/// The invariant, and it is what makes the fused pipeline legal: **`step` reads
/// only the environment through the declaration it is handed.** A nested
/// declaration's model is emitted *before* it — that is `modelgen`'s emission
/// order (`modelgen/Modelgen/Driver.lean`: "the model … generated **before** the
/// declaration is added … nothing in the model mentions `T`") and it is also
/// what [`settled`] has always *required*, since a model at or after its own
/// declaration is [`Missing::Later`]. So everything [`shape`] looks up is either
/// the declaration itself, something the kernel minted for it, or a model
/// constant strictly earlier in the file.
pub struct Recogniser {
    /// [`Recognised::model_of`], filled as the declarations go past.
    pub model_of: HashMap<ModelKey, Name>,
    /// [`Recognised::model_iota`].
    pub model_iota: HashMap<(ModelKey, Name), Name>,
    /// [`Recognised::nested`].
    pub nested: HashMap<Name, NestedRecord>,
    pub seen: usize,
    pub modelled: usize,
    /// [`Recognised::modelled_tool`], [`Recognised::modelled_legacy`].
    pub modelled_tool: usize,
    pub modelled_legacy: usize,
    pos: HashMap<Name, usize>,
    applied: HashMap<Name, Vec<Vec<u32>>>,
}

impl Recogniser {
    /// The parse-only half: the declaration positions and the σ the file's own
    /// declarations apply each constant at. Neither reads an environment.
    pub fn new(decls: &[Declaration], schedule: &HashMap<Name, Vec<Vec<u32>>>) -> Recogniser {
        let mut pos: HashMap<Name, usize> = HashMap::new();
        for (i, d) in decls.iter().enumerate() {
            pos.insert(d.name(), i);
            if let Declaration::Mutual { types, .. } = d {
                for t in types {
                    pos.insert(t.name, i);
                }
            }
        }
        Recogniser {
            model_of: HashMap::new(),
            model_iota: HashMap::new(),
            nested: HashMap::new(),
            seen: 0,
            modelled: 0,
            modelled_tool: 0,
            modelled_legacy: 0,
            pos,
            // What the file's own declarations name, and at which ground σ. The
            // pre-pass's schedule is the other half; a recursor is keyed at the
            // union, for the reason the header gives.
            applied: applied_at(decls, schedule),
        }
    }

    /// **Record what the environment now says each declaration owns** — an
    /// inductive's constructors and its recursors, `Quot`'s family.
    ///
    /// Read off `env.owners` rather than predicted from the declaration, for
    /// [`export_recs`]'s reason: a nested declaration owns `T.rec_1` and
    /// `T.rec_2`, and how many it owns is the specialisation's answer and not
    /// the declaration's.
    ///
    /// Asked only of the declarations that own anything, which is what keeps
    /// the scan off the hot path: an axiom or a definition owns nothing, so the
    /// owner index is walked once per inductive rather than once per
    /// declaration. `i` is unused — a name's position is its **owner's**, and
    /// the owner is already in `pos` — and is taken so the call site reads as
    /// the loop body it is.
    pub fn observe(&mut self, env: &Environment, i: usize, d: &Declaration) {
        let _ = i;
        if !matches!(
            d,
            Declaration::Inductive { .. } | Declaration::Mutual { .. } | Declaration::Quot
        ) {
            return
        }
        let owned: Vec<(Name, usize)> = env
            .owners
            .iter()
            .filter_map(|(n, o)| Some((*n, *self.pos.get(o)?)))
            .collect();
        for (n, j) in owned {
            self.pos.insert(n, j);
        }
    }

    /// One declaration: is it nested, and does the export carry a model for it?
    /// `env` is zone A's environment through `d`; `schedule` is the run's, and
    /// the σ each model constant needs are added to it here.
    pub fn step(
        &mut self,
        env: &Environment,
        i: usize,
        d: &Declaration,
        schedule: &mut HashMap<Name, Vec<Vec<u32>>>,
    ) {
        let Declaration::Inductive { name, lparams, num_params, ty, ctors } = d else { return };
        let types = vec![IndType { name: *name, ty: *ty, ctors: ctors.clone() }];
        // **`nested::plan` answers "is this nested", and nothing else does.**
        // Not the export's `is_nested` flag, which `convert::load` has already
        // consumed at the parser gate, and not a name: the question here is
        // whether a constructor field mentions the declaration under a foreign
        // inductive, which is the same question the specialisation asks.
        match crate::mini::nested::plan(env, lparams, *num_params, &types) {
            Ok(Some(_)) => {}
            // `Ok(None)` is an ordinary declaration. `Err` is a nested one the
            // specialiser cannot express — the file would not have been
            // accepted, so it cannot arise here.
            _ => return,
        }
        self.seen += 1;
        // **The scheme is decided by the carrier, and the tower is then read
        // entirely in that scheme.** A well-formed `T._model` is the evidence
        // the external producer ran over this file; from there every remaining
        // lookup is its business, and a `Missing` is *the tool's tower is
        // wrong* — a decline, not a licence to go looking for a second tower
        // under other names. Deciding on the whole [`shape`] instead would do
        // exactly that, and would report a broken tool tower under the legacy
        // scheme's least informative label.
        //
        // The legacy arm goes when `modelgen/` does; nothing else here is
        // transitional.
        let scheme = match carrier_of(env, name, &self.pos, i, Scheme::Tool) {
            Ok(_) => Scheme::Tool,
            Err(_) => Scheme::Legacy,
        };
        match shape(env, name, ctors, &self.pos, i, scheme) {
            Ok(m) => {
                self.modelled += 1;
                match scheme {
                    Scheme::Tool => self.modelled_tool += 1,
                    Scheme::Legacy => self.modelled_legacy += 1,
                }
                self.key(env, name, &m, schedule);
            }
            Err(why) => self.decline(env, name, ctors, why),
        }
    }

    /// Has anything been recognised or declined? The tables go on the
    /// interpretation apparatus, and a file with no nested declaration must not
    /// acquire an apparatus it would otherwise never have had.
    pub fn any(&self) -> bool { !self.nested.is_empty() }

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

impl Recogniser {
    /// Fill the tables for one recognised model, and propagate its σ.
    fn key(
        &mut self,
        env: &Environment,
        name: &Name,
        m: &Model,
        schedule: &mut HashMap<Name, Vec<Vec<u32>>>,
    ) {
        let mut constants: Vec<Name> = Vec::new();
        // The type former and the constructors have no universe parameters of
        // their own, so `σ = []` is the whole population.
        for (export, model) in &m.mono {
            self.model_of.insert((*export, Vec::new()), *model);
            demand(schedule, model, &[Vec::new()]);
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
            let mut sigmas: Vec<Vec<u32>> = schedule.get(export).cloned().unwrap_or_default();
            for s in self.applied.get(export).into_iter().flatten() {
                if !sigmas.contains(s) {
                    sigmas.push(s.clone());
                }
            }
            for s in &sigmas {
                self.model_of.insert((*export, s.clone()), *model);
            }
            demand(schedule, model, &sigmas);
            sigmas_of.insert(*export, sigmas);
            constants.push(*export);
        }
        // A rule is keyed at the σ its recursor was keyed at, and at no other:
        // a rule at a σ the recursor has no interpretation at is a rule about a
        // redex this run cannot name.
        for (export, ctor, thm) in &m.iotas {
            let Some(sigmas) = sigmas_of.get(export) else { continue };
            for s in sigmas {
                self.model_iota.insert(((*export, s.clone()), *ctor), *thm);
            }
            demand(schedule, thm, sigmas);
        }
        let _ = env;
        self.nested.insert(*name, NestedRecord { why: None, constants });
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

/// Add σ to a model constant's schedule entry. **Never a default**: a constant
/// reached with an empty σ list keeps whatever the pre-pass gave it, and a σ
/// that is not propagated is a σ the keying above did not record either, so the
/// two cannot disagree.
fn demand(schedule: &mut HashMap<Name, Vec<Vec<u32>>>, n: &Name, sigmas: &[Vec<u32>]) {
    if sigmas.is_empty() {
        return
    }
    add_sigmas(schedule, *n, sigmas.iter().cloned());
}

/// **Every recursor the export declares for `T`, in member order** — `T.rec`,
/// `T.rec_1`, `T.rec_2`, … — with its [`ConstantInfo`].
///
/// Read off the environment and not off a [`crate::mini::nested::Plan`]: the plan's
/// member count is a *prediction* of how many recursors the declaration owns,
/// and the environment is what it actually owns. `env.owner` is checked as well
/// as the name, so a file's own `T.rec_1` that belongs to something else stops
/// the walk instead of being taken for a member.
fn export_recs<'e>(env: &'e Environment, t: &Name) -> Vec<(Name, &'e ConstantInfo)> {
    let mut out = Vec::new();
    for k in 0.. {
        let n = crate::mini::nested::Plan::rec_name(t, k);
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
/// declared type, rewrite each of `T`, its constructors and its recursors to
/// the model name [`Scheme`] gives it, and the result must be the model's
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
    scheme: Scheme,
) -> Result<Model, Missing> {
    let self_n = scheme.carrier(t);
    let recs = export_recs(env, t);

    // The rewriting, built before anything is compared. Its *keys* are the
    // export's names and its values the model's; a value that does not exist
    // is caught at the lookup that needs it, with the reason that names which
    // part of the tower is missing, rather than in one sweep that would report
    // every absence as the same thing.
    let mut rho: HashMap<Name, Name> = HashMap::new();
    rho.insert(*t, self_n);
    for (j, (c, _)) in ctors.iter().enumerate() {
        rho.insert(*c, scheme.ctor(t, j, c));
    }
    for (k, (r, _)) in recs.iter().enumerate() {
        rho.insert(*r, scheme.rec(t, k, r));
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
    carrier_of(env, t, pos, i, scheme)?;
    let Some(t_ci @ ConstantInfo::Inductive { .. }) = env.get(t) else {
        return Err(Missing::Carrier)
    };

    let mut mono: Vec<(Name, Name)> = vec![(*t, self_n)];
    for (j, (c, c_ty)) in ctors.iter().enumerate() {
        let m = scheme.ctor(t, j, c);
        let ci = model_const(env, pos, &m, i, Missing::Ctor)?;
        // At the *declaration's* level parameters, for [`at_export_levels`]'s
        // reason: `MODELGEN.md` §1 says every generated constant carries `ℓ⃗`,
        // and the export's constructor carries the declaration's own.
        let at = crate::mini::env::instantiate_lparams(
            ci.ty(),
            ci.lparams(),
            &t_ci.lparams().iter().map(|n| crate::mini::expr::Level::param(*n)).collect::<Vec<_>>(),
        );
        if ci.lparams().len() != t_ci.lparams().len()
            || at.ok().as_ref() != Some(&rename(&rho, c_ty))
        {
            return Err(Missing::Ctor)
        }
        mono.push((*c, m));
    }

    // ρ read backwards, for [`iota_key`]: an ι theorem's major is written in
    // the *model's* names at the root — `c._model`, because
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
        let m = scheme.rec(t, k, r);
        let ci = model_const(env, pos, &m, i, Missing::Rec)?;
        if at_export_levels(ci, r_ci).ok_or(Missing::Rec)? != rename(&rho, r_ci.ty()) {
            return Err(Missing::Rec)
        }
        // The rules, by index. `MODELGEN.md` §1.1's property 2 says a consumer
        // may line ι theorems up with rules by index and check the key by name
        // — so that is what this does, and the key it checks is read off the
        // theorem's **own left-hand side** rather than trusted from the index.
        let ConstantInfo::Recursor { rules, .. } = r_ci else { return Err(Missing::Rec) };
        for (j, (rule_ctor, _)) in rules.iter().enumerate() {
            let thm = scheme.iota(t, k, r, j);
            let thm_ci = model_const(env, pos, &thm, i, Missing::Iota)?;
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

/// **The carrier of `T`'s model in `scheme`, checked against `T`'s own type.**
///
/// Split out of [`shape`] because it is also **the scheme decision**
/// ([`Recogniser::step`]): a well-formed `T._model` is the evidence that the
/// external producer ran over this file, and it is the *only* evidence taken.
/// Once it is there the whole tower is read in [`Scheme::Tool`] and a later
/// absence is a decline; when it is not, the legacy tower is looked for instead.
///
/// The check is `T`'s declared type on the nose — `∀p⃗, Sort u`, since a
/// producer declines a declaration with indices — which is what stops the
/// scheme decision being a bare name lookup. It is not enough on its own to
/// stop a squatter: `nested_keying`'s `def UTree._model.self : Type := N` has
/// exactly `UTree`'s type and passes here, and is stopped by the position
/// check inside [`model_const`] and then by the constructors. The module
/// header's "why this is a table and not a name rule" is the full argument.
///
/// **The absence of the carrier is [`Missing::NoCarrier`] and not an error**
/// (`MODELGEN.md` §1.3): the producer declined the declaration and said which
/// shape stopped it, and a consumer that treated that as a failure would turn
/// every unsupported nested shape into a broken file.
fn carrier_of<'e>(
    env: &'e Environment,
    t: &Name,
    pos: &HashMap<Name, usize>,
    i: usize,
    scheme: Scheme,
) -> Result<&'e ConstantInfo, Missing> {
    let carrier = model_const(env, pos, &scheme.carrier(t), i, Missing::NoCarrier)?;
    let ConstantInfo::Def { .. } = carrier else { return Err(Missing::Carrier) };
    let Some(t_ci @ ConstantInfo::Inductive { .. }) = env.get(t) else {
        return Err(Missing::Carrier)
    };
    if at_export_levels(carrier, t_ci).ok_or(Missing::Carrier)? != *t_ci.ty() {
        return Err(Missing::Carrier)
    }
    Ok(carrier)
}

/// **One model constant, if the file settles it strictly before position `i`.**
///
/// `⟦T⟧` is resolved at `T`'s own position out of the carrier's, so a model
/// declared level with — or after — the declaration it models is one the alias
/// cannot look up. `modelgen` splices the model *before* the nested inductive,
/// so this holds for anything it wrote; it is checked because a `_model` name
/// in the file is not necessarily one it wrote.
///
/// # Three outcomes, and they are three different diagnostics
///
/// * **not in the file and not in the environment** — `absent`, the caller's
///   "this part of the tower is missing" label;
/// * **in the file at a position `≥ i`** — [`Missing::Later`], *whether or not
///   the environment has it yet*;
/// * settled before `i` — the constant.
///
/// **The middle case is why the position is consulted before the
/// environment.** Under the whole-file pipeline the environment was complete
/// when this ran, so a later model was found there and the position check was
/// what turned it into `Later`. `crate::mini::decl_pass` hands over the environment
/// through `i` only, where a later model is simply absent — and reporting
/// `no nested model in the export` for a model the export does carry is a
/// *worse* diagnostic, not merely a different one. `nested_keying`'s `UTree`
/// is the case: the file takes the model's own name for a declaration of its
/// own, after `UTree`, and `mini/tests/nested.rs` pins the reason.
///
/// Read the other way, this is the same answer the whole-file form gave in
/// every case: with a complete environment, "in the file at `≥ i`" and "in the
/// environment and at `≥ i`" coincide.
fn model_const<'e>(
    env: &'e Environment,
    pos: &HashMap<Name, usize>,
    n: &Name,
    i: usize,
    absent: Missing,
) -> Result<&'e ConstantInfo, Missing> {
    match pos.get(n) {
        Some(j) if *j < i => env.get(n).ok_or(absent),
        Some(_) => Err(Missing::Later),
        // Not a declaration of the file. It may still be in the environment —
        // a constructor or a recursor whose owner the position map missed — and
        // the whole-file form called that `Later` too.
        None => match env.get(n) {
            Some(_) => Err(Missing::Later),
            None => Err(absent),
        },
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
/// `model_alias` and [`crate::mini::iota_model::fire`] both carry the redex's σ
/// across positionally and neither has a name to carry.
fn at_export_levels(model: &ConstantInfo, export: &ConstantInfo) -> Option<E> {
    if model.lparams().len() != export.lparams().len() {
        return None
    }
    let us: Vec<crate::mini::expr::Level> =
        export.lparams().iter().map(|n| crate::mini::expr::Level::param(*n)).collect();
    crate::mini::env::instantiate_lparams(model.ty(), model.lparams(), &us).ok()
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
            Some(m) => crate::mini::expr::konst(*m, ls.clone()),
            None => *e,
        },
        Expr::App(f, x) => crate::mini::expr::app(rename(rho, f), rename(rho, x)),
        Expr::Forall { ty, body } => crate::mini::expr::forall(rename(rho, ty), rename(rho, body)),
        Expr::Lam { ty, body } => crate::mini::expr::lam(rename(rho, ty), rename(rho, body)),
        Expr::Let { ty, val, body } => crate::mini::expr::let_(rename(rho, ty), rename(rho, val), rename(rho, body)),
        Expr::Proj { ind, idx, s } => crate::mini::expr::proj(*ind, *idx, rename(rho, s)),
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
            let map = crate::mini::ground::ground_env(lparams, sigma);
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
            if let Some(s) = ls.iter().map(|l| crate::mini::ground::eval(l, map)).collect() {
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

// Which position in the declaration list each name is settled by — a
// declaration's own name, and every constructor and recursor the environment
// says it owns — is [`Recogniser::pos`], built by [`Recogniser::new`] and
// [`Recogniser::observe`]. It used to be one `positions(env, decls)` sweep over
// a finished environment; there is no finished environment to sweep now.

