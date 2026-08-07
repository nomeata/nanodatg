//! **The isomorphism a nested declaration's restoration stands on, built and
//! checked.**
//!
//! # Interface
//!
//! ```text
//! nested_ev::iso(env, lparams, num_params, types, plan) -> Result<Iso, Reason>
//! ```
//!
//! [`Iso::decls`] is a list of ordinary [`Declaration`]s in dependency order —
//! the specialised block under fresh names, a carrier `T._model.self`, one
//! `pack`/`unpack` pair per mimic with **both round trips as theorems**, the
//! declared type's own constructors, one recursor per block member, one
//! congruence per mimic, and **every one of those recursors' ι rules, as
//! theorems with proofs** — already checked into [`Iso::env`]. Nothing is
//! asserted that `kernel::add` did not accept: a proof this module builds and
//! the checker rejects is an `Err`, never a declaration.
//!
//! # What this is for
//!
//! [`crate::nested`] specialises `inductive Tree | leaf | node : List Tree →
//! Tree` into a mutual block with a *mimic* `Tree._nested.1` of `List Tree`,
//! checks the block, and then **restores** — rewrites the mimic back to
//! `List Tree` and its constructors back to `List`'s. Its own header says what
//! that costs: the restoration is a *rewrite, not a derivation*, and
//! `mini/tests/nested.rs`'s `the_round_trip_the_encoding_would_need_is_not_
//! definitional` is the kernel refusing to identify the two.
//!
//! This module builds the identification the rewrite stands on, as declarations
//! the kernel accepts:
//!
//! ```text
//! pack_i   : occ_i → B_i          by the real container's recursor
//! unpack_i : B_i → occ_i          by the block's recursor
//! unpackPack_i : ∀ l, Eq (unpack_i (pack_i l)) l
//! packUnpack_i : ∀ b, Eq (pack_i (unpack_i b)) b
//! ```
//!
//! and, over it, the recursors the export declares and **their rules proved**:
//!
//! ```text
//! rec_k    : Bₖ.rec's statement, at the model's names
//! iota_k_j : Eq (rec_k p⃗ M⃗ S⃗ (c f⃗)) (Sⱼ f⃗ ih⃗)   -- one per rule of rec_k
//! ```
//!
//! It does not make the rewrite sound on its own — that needs the
//! interpretation keyed to this development, which is `zoneb`'s and is not
//! here. What it does is turn "isomorphic, we believe" into two theorems with
//! proofs, per mimic, for every declaration it accepts.
//!
//! `mini/tests/fixtures/nested_model.lean` is this development written by hand
//! at `Tree`, together with the recursors and ι rules that sit on top of it;
//! this module is the same thing generated, and `mini/tests/nested.rs` checks
//! the two agree on the shapes both cover.
//!
//! # The carrier is fresh, and that is forced
//!
//! **The model may not reuse the export's own `T`.** `T` is installed by
//! [`crate::nested::add`] as a primitive `ConstantInfo::Inductive`, and the
//! block member `B₀` is a different constant; they are not convertible. So
//! `pack : List T → B₁` cannot be built at all — `List.cons`'s field arrives at
//! `T` and the block's `cons` wants `B₀`. The model therefore declares its own
//!
//! ```text
//! def T._model.self : Sort u := B₀
//! ```
//!
//! and rewrites every occurrence `T ↦ T._model.self` before using it.
//! `T._model.self` unfolds to `B₀` by δ, which is exactly what lets a field the
//! block types at `B₀` be handed to the *real* container's constructor. The
//! parallel development is the design and not a workaround: identifying it with
//! `T` is the keying step, `⟦T⟧ := ⟦T._model.self⟧`, and it lives in `zoneb`.
//!
//! # `unpack`'s motive vector is forced too
//!
//! A block recursor carries one motive per member at **one** motive universe,
//! so the members `unpack` does not eliminate into still need a motive at that
//! sort. The choice that works for every block whatever its constructors are is
//! the *identity* motive at the root and the occurrence at each mimic:
//!
//! ```text
//! motive₀ := fun _ : B₀ => B₀        minor for c  : fun f⃗ ih⃗ => c f⃗
//! motiveⱼ := fun _ : Bⱼ => occⱼ      minor for c' : fun f⃗ ih⃗ => c_real q⃗ g⃗
//! ```
//!
//! `fun _ => Bⱼ` at a mimic would not do: `unpack₁` for `Box BTree` needs
//! `unpack₂`'s result as its `mk` field, and that arrives as the induction
//! hypothesis at `motive₂`. The mimic minors need **no transport**; a field the
//! block types at `B₀` is passed through by the paragraph above, and a field at
//! another mimic is its own induction hypothesis.
//!
//! # The boundary, and the line the ι theorems must not cross
//!
//! This module is a **black box over the evidence layer**, on the same terms as
//! [`crate::mutual_aux`] and [`crate::nested`] and checked by the same rule
//! (`ci/check-mutual-blackbox.sh`): it emits Lean-world syntax, asks
//! [`crate::kernel::add`] whether it is well-formed, and reads back only zone
//! A's syntax — a `ConstantInfo`'s declared type, its constructor list, a
//! recursor's arity fields. It never names a certificate.
//!
//! **That survives the ι theorems, and it is why they could be written here.**
//! A rule of `T._model.rec_k` is a *Lean* theorem — an `Eq` between two Lean
//! terms, proved by a Lean proof term the kernel checks — so emitting it here
//! names no `Thm` and moves no allowlist. What must **not** happen here
//! is the next step: turning such a theorem into the TG equation
//! `⊢ ⟦lhs⟧ = ⟦rhs⟧` that a conversion site can use. That cashing is
//! `Interp::beta_spine`, `Interp::cond_app`, `derived::prop::cond_elim` and
//! `Scopes::close(..).discharge` composed, it names `Thm` throughout, and it
//! belongs in a separate module beside [`crate::iota_dep`] which never claims
//! this header. The temptation to do it here — the theorem is right there, and
//! the proof term is in hand — is exactly the temptation the black box exists
//! to refuse.
//!
//! # What it declines, each with a witness
//!
//! Every decline names a shape rather than a failure:
//!
//! * [`Reason::Polymorphic`] — the declaration has universe parameters of its
//!   own. **No fixture has one**, so this guard has no occupant and is here
//!   because every generated level list below is written at the block's own,
//!   which for a polymorphic declaration is not a closed list.
//! * [`Reason::Indexed`] — the declaration or a container has indices. No
//!   nested fixture has one; the mimic of an indexed container is indexed, and
//!   the recursor applications below are all written at zero indices.
//! * [`Reason::DependentFields`] — a constructor field's type mentions an
//!   earlier field. The congruence fold below builds a motive by replacing one
//!   argument of a constructor application, which is only well-typed when the
//!   remaining argument types do not depend on it.
//! * [`Reason::NoEq`] — the export declares no `Eq`, or one whose recursor is
//!   not Lean's shape. The round trips are equations; a `prelude` export that
//!   never mentions equality gets no theorems, and this module does not
//!   fabricate an `Eq` Lean never wrote. `nested_shapes.lean` used to be the
//!   witness and now declares an `Eq` for exactly this reason.
//! * [`Reason::NameTaken`] — a name under `T._model` is already declared.
//!
//! # The parameter telescope, and why every depth below is written out
//!
//! Every generated declaration is `∀p⃗, …` and every generated value is
//! `fun p⃗ => …`, so a reference to a member, a mimic, a `pack` or an `unpack`
//! is applied to `p⃗` before anything else. `Plan`'s occurrences are stored at
//! the block's own telescope depth, so using one anywhere deeper is a shift,
//! and **a term read at the wrong depth is the failure mode this project has
//! paid for most often** — three of the indexed row's five layers were exactly
//! that.
//!
//! Two things follow, and both are deliberate. Depths are named
//! ([`Gen::ps`], [`Gen::occ_at`], [`Gen::mem_at`], [`Gen::call`]) and never
//! written as a literal shift at a use site; and the *statements* the generator
//! emits are checked against an independently built expectation in
//! `mini/tests/nested.rs`'s `the_generated_round_trips_state_the_isomorphism`,
//! rather than only against the kernel. Well-typedness is not the claim: a
//! `pack` at the wrong parameter can be perfectly well-typed and prove
//! something weaker. At `np = 0` there is no depth to get wrong, which is why
//! that oracle was written before this telescope existed rather than after.

use std::collections::HashMap;
use std::rc::Rc;

use crate::env::instantiate_lparams;
use crate::env::{ConstantInfo, DefKind, Declaration, Environment, IndType};
use crate::expr::{app_n, bvar, forall, get_app, konst, lam, shift, substs, Expr, Level, Name, E};
use crate::nested::Plan;

/// Why a nested declaration's isomorphism could not be built. Each is a shape.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// The declaration has universe parameters of its own.
    Polymorphic,
    /// The declaration, or a container it nests into, has indices.
    Indexed,
    /// A constructor field's type mentions an earlier field.
    DependentFields,
    /// No `Eq`, or an `Eq` whose recursor is not the shape the round trips need.
    NoEq,
    /// A name under `T._model` is already declared.
    NameTaken,
    /// A shape `kernel::add` would already have rejected, a constructor field
    /// that is recursive **under a binder** — `Bₖ.rec`'s rule gives that an
    /// induction hypothesis and [`Rule::statement`] writes none — or a proof
    /// this module built and the checker did not accept.
    Malformed,
}

impl Reason {
    /// The word that reaches a `waiting:` row, as `ind-spec(T: nested model …)`.
    pub fn label(self) -> &'static str {
        match self {
            Reason::Polymorphic => "nested model with universe parameters",
            Reason::Indexed => "nested model with indices",
            Reason::DependentFields => "nested model with dependent fields",
            Reason::NoEq => "nested model without Eq",
            Reason::NameTaken => "nested model name taken",
            Reason::Malformed => "nested model shape",
        }
    }
}

/// The isomorphism of one nested declaration.
pub struct Iso {
    /// Every generated declaration, in dependency order and already checked
    /// into [`Iso::env`].
    pub decls: Vec<Declaration>,
    /// The caller's environment with the development added.
    pub env: Environment,
    /// `T._model.self`, the model's own carrier.
    pub self_name: Name,
    /// The block's members, root first.
    pub members: Vec<Name>,
    /// `(pack_i, unpack_i, unpackPack_i, packUnpack_i)`, one per mimic, in the
    /// order the declarations were emitted.
    pub maps: Vec<(Name, Name, Name, Name)>,
    /// `(the export's constructor, the model's)`, in declaration order. The
    /// model's carries the export's declared type with `T` rewritten to
    /// [`Iso::self_name`] and nothing else, which is the condition the keying
    /// rests on and `mini/tests/nested.rs` asserts.
    pub ctors: Vec<(Name, Name)>,
    /// `T._model.rec_k`, in member order — the model's counterpart of the
    /// export's `T.rec` / `T.rec_1` / …, each at the type zone A gives that
    /// recursor with the export's names rewritten to the model's.
    pub recs: Vec<Name>,
    /// `(member, the rule's constructor as the export names it, the theorem)`,
    /// one per rule of every `T._model.rec_k`, in the order `Bₖ.rec` binds
    /// them. The constructor is the **export's**: `Tree.node` at the root and
    /// `List.cons` at a mimic, which is the key the installed `T.rec_k` carries
    /// its rule under and what `mini/tests/nested.rs` compares against.
    pub iotas: Vec<(usize, Name, Name)>,
}

type R<T> = Result<T, Reason>;

/// **Build the isomorphism, or say which shape stopped it.**
///
/// The whole of the checker interaction is [`crate::kernel::add`], once per
/// generated declaration, in a scratch environment. A declaration the checker
/// rejects is an `Err(Reason::Malformed)`; nothing is emitted unchecked.
pub fn iso(
    env: &Environment,
    lparams: &[Name],
    num_params: u32,
    types: &[IndType],
    plan: &Plan,
) -> R<Iso> {
    if !lparams.is_empty() {
        return Err(Reason::Polymorphic)
    }
    let np = num_params;
    let root = types.first().ok_or(Reason::Malformed)?.name.clone();
    // The block's parameter binder types and its resultant sort. A member's
    // type is `∀p⃗, Sort u`; anything left over after the parameters is an index
    // telescope this module does not write.
    let mut ptys: Vec<E> = Vec::new();
    let mut cur = plan.types[0].ty.clone();
    for _ in 0..np {
        let Expr::Forall { ty, body } = &*cur.clone() else { return Err(Reason::Malformed) };
        ptys.push(ty.clone());
        cur = body.clone();
    }
    let Expr::Sort(u) = &*cur else { return Err(Reason::Indexed) };
    let u = u.clone();

    let model = Name::str(&root, "_model");
    let b = |i: usize| Name::Num(Rc::new(model.clone()), i as u64);
    let self_name = Name::str(&model, "self");
    for i in 0..plan.types.len() {
        if env.get(&b(i)).is_some() {
            return Err(Reason::NameTaken)
        }
    }
    if env.get(&self_name).is_some() {
        return Err(Reason::NameTaken)
    }

    let eq = Eq::read(env)?;
    let no: Rc<[Level]> = Vec::new().into();

    // ── 1. the block, renamed ────────────────────────────────────────────
    //
    // Member 0 is the export's own `T` and must not keep that name: `T` is a
    // primitive inductive in the caller's environment and this development is
    // about a different constant. Every member is renamed for uniformity.
    let mut ren: HashMap<Name, (u32, E)> = HashMap::new();
    for (i, t) in plan.types.iter().enumerate() {
        ren.insert(t.name.clone(), (0, konst(b(i), Rc::clone(&no))));
    }
    let block: Vec<IndType> = plan
        .types
        .iter()
        .enumerate()
        .map(|(i, t)| IndType {
            name: b(i),
            ty: t.ty.clone(),
            ctors: t
                .ctors
                .iter()
                .map(|(cn, cty)| (rename_ctor(&b(i), cn), crate::nested::restore(&ren, cty)))
                .collect(),
        })
        .collect();

    let mut out: Vec<Declaration> = Vec::new();
    let mut scratch = env.clone();
    let block_decl =
        Declaration::Mutual { lparams: Vec::new(), num_params: np, types: block.clone() };
    crate::kernel::add(&mut scratch, &block_decl).map_err(|_| Reason::Malformed)?;
    out.push(block_decl);

    // ── 2. the carrier ───────────────────────────────────────────────────
    let carrier = {
        let body = app_n(konst(b(0), Rc::clone(&no)), &params_at(np, np));
        lams(&ptys, body)
    };
    let self_decl = Declaration::Def {
        name: self_name.clone(),
        lparams: Vec::new(),
        ty: plan.types[0].ty.clone(),
        value: carrier,
        kind: DefKind::Def,
    };
    crate::kernel::add(&mut scratch, &self_decl).map_err(|_| Reason::Malformed)?;
    out.push(self_decl);

    // Every occurrence, with the export's `T` rewritten to the model's carrier.
    // `Plan` stores an occurrence at the block's own telescope depth, so these
    // are valid at depth `np` and nowhere else without a shift.
    let to_self: HashMap<Name, (u32, E)> =
        [(root.clone(), (0u32, konst(self_name.clone(), Rc::clone(&no))))].into_iter().collect();
    let occs: Vec<E> =
        plan.mimics.iter().map(|m| crate::nested::restore(&to_self, &m.occ)).collect();

    // ── 3. pack, unpack, and the two round trips, per mimic ──────────────
    let g = Gen {
        env: scratch.clone(),
        b: &block,
        u: &u,
        eq: &eq,
        occs: &occs,
        model: &model,
        no: &no,
        np,
        ptys: &ptys,
    };
    let mut maps = Vec::new();
    // Deeper mimics first: `pack_i` for a container whose field is another
    // occurrence calls that occurrence's `pack`, and discovery order puts the
    // deeper one later. Nesting strictly decreases, so this is a topological
    // order and a cycle cannot arise.
    let mut done = vec![false; plan.mimics.len()];
    for i in (0..plan.mimics.len()).rev() {
        let member = i + 1;
        let names = g.names(i);
        for n in [&names.0, &names.1, &names.2, &names.3] {
            if env.get(n).is_some() {
                return Err(Reason::NameTaken)
            }
        }
        for d in g.four(i, member, &names, &done)? {
            crate::kernel::add(&mut scratch, &d).map_err(|_| Reason::Malformed)?;
            out.push(d);
        }
        done[i] = true;
        maps.push(names);
    }

    // ── 4. the declared type's own constructors ──────────────────────────
    //
    // After the maps, because a field at a mimic is packed on the way in. The
    // model's constructor carries the **export's** declared type with `T`
    // rewritten to the carrier, so that the keying is an alias and not a
    // coincidence; `nested_ev`'s header says why that matters.
    let mut ctors = Vec::new();
    let mut ctor_tys: Vec<(Name, Name, E)> = Vec::new();
    for (j, (cn, cty)) in types[0].ctors.iter().enumerate() {
        let name = Name::str(&model, &format!("ctor_{j}"));
        if env.get(&name).is_some() {
            return Err(Reason::NameTaken)
        }
        let ty = crate::nested::restore(&to_self, cty);
        let d = g.ctor_value(j, &ty)?;
        let decl = Declaration::Def {
            name: name.clone(),
            lparams: Vec::new(),
            ty: ty.clone(),
            value: d,
            kind: DefKind::Def,
        };
        crate::kernel::add(&mut scratch, &decl).map_err(|_| Reason::Malformed)?;
        out.push(decl);
        ctors.push((cn.clone(), name.clone()));
        ctor_tys.push((cn.clone(), name, ty));
    }

    // ── 5. one recursor per block member ─────────────────────────────────
    //
    // The statement is **zone A's own**: `B_k.rec`'s type, with every name the
    // specialisation introduced rewritten to the model's counterpart. That is
    // the same table `nested::add` restores the *export's* recursor with, one
    // set of names along, so the model's `rec_k` and the export's `T.rec_k`
    // are the same statement about different constants — which is exactly what
    // makes the keying an alias.
    let mut heads: HashMap<Name, (u32, E)> = HashMap::new();
    heads.insert(b(0), (0, konst(self_name.clone(), Rc::clone(&no))));
    for (export_c, model_c) in &ctors {
        heads.insert(rename_ctor(&b(0), export_c), (0, konst(model_c.clone(), Rc::clone(&no))));
    }
    for (i, m) in plan.mimics.iter().enumerate() {
        heads.insert(b(i + 1), (np, occs[i].clone()));
        for (mc, real) in &m.ctors {
            let last = match mc {
                Name::Str(_, x) => x.to_string(),
                other => other.to_string(),
            };
            // The real constructor's own parameters mention the **export's** `T`,
            // because `Mimic::ctors` is built before the model exists. They have to
            // go to the carrier like every other occurrence.
            heads.insert(
                Name::str(&b(i + 1), &last),
                (np, crate::nested::restore(&to_self, real)),
            );
        }
    }
    let rec_names: Vec<Name> =
        (0..plan.types.len()).map(|k| Name::str(&model, &format!("rec_{k}"))).collect();
    for (k, rn) in rec_names.iter().enumerate() {
        if env.get(rn).is_some() {
            return Err(Reason::NameTaken)
        }
        heads.insert(Name::str(&b(k), "rec"), (0, konst(rn.clone(), Rc::clone(&no))));
    }
    let mut shapes = Vec::with_capacity(rec_names.len());
    for (k, rn) in rec_names.iter().enumerate() {
        let shape = g.rec_shape(k, &heads)?;
        let d = g.rec_decl(rn, &shape)?;
        crate::kernel::add(&mut scratch, &d).map_err(|_| Reason::Malformed)?;
        out.push(d);
        shapes.push(shape);
    }

    // ── 6. the congruences the ι rules are stated along ──────────────────
    for i in 0..plan.mimics.len() {
        let name = Name::str(&model, &format!("congrPack_{i}"));
        if env.get(&name).is_some() {
            return Err(Reason::NameTaken)
        }
        let d = g.congr_pack_decl(i, &name)?;
        crate::kernel::add(&mut scratch, &d).map_err(|_| Reason::Malformed)?;
        out.push(d);
    }

    // ── 7. the ι rules themselves ────────────────────────────────────────
    //
    // One theorem per rule of every `T._model.rec_k`, in the order `Bₖ.rec`
    // binds them. The statement is built from the block's own constructors and
    // the *export's* recursor telescope; the proof is `Eq.refl` where the
    // constructor has no packed field and a transport fold where it has.
    let mut iotas = Vec::new();
    for (k, shape) in shapes.iter().enumerate() {
        for (key, name, decl) in g.iota_decls(k, shape, &ctor_tys)? {
            if env.get(&name).is_some() {
                return Err(Reason::NameTaken)
            }
            crate::kernel::add(&mut scratch, &decl).map_err(|_| Reason::Malformed)?;
            out.push(decl);
            iotas.push((k, key, name));
        }
    }

    Ok(Iso {
        decls: out,
        env: scratch,
        self_name,
        members: (0..plan.types.len()).map(b).collect(),
        maps,
        ctors,
        recs: rec_names,
        iotas,
    })
}

/// `T.leaf` under member name `B`, as `B.leaf` — the last component kept and
/// the prefix replaced, so a mimic's `T._nested.1.cons` becomes `B₁.cons`.
fn rename_ctor(member: &Name, c: &Name) -> Name {
    match c {
        Name::Str(_, s) => Name::str(member, s),
        other => Name::str(member, &other.to_string()),
    }
}

/// The block's parameters as de Bruijn indices, at a scope of depth `d`.
/// Parameter `l` is the `l`-th binder from the outside, so it is `d − 1 − l`.
fn params_at(np: u32, d: u32) -> Vec<E> { (0..np).map(|l| bvar(d - 1 - l)).collect() }

/// `Eq`, `Eq.refl` and `Eq.rec` at the arities the round trips need.
struct Eq {
    eq: Name,
    refl: Name,
    rec: Name,
}

impl Eq {
    /// Read the three constants and check the recursor is Lean's shape —
    /// `Eq.rec α a motive base b h`, two parameters and one index. A different
    /// shape is an `Eq` this module cannot use, not one it should guess about.
    fn read(env: &Environment) -> R<Eq> {
        let eq = Name::simple("Eq");
        let refl = Name::str(&eq, "refl");
        let rec = Name::str(&eq, "rec");
        let Some(ConstantInfo::Inductive { num_params, num_indices, ctors, .. }) = env.get(&eq)
        else {
            return Err(Reason::NoEq)
        };
        if *num_params != 2 || *num_indices != 1 || ctors.len() != 1 {
            return Err(Reason::NoEq)
        }
        let Some(ConstantInfo::Recursor { num_params, num_motives, num_minors, num_indices, .. }) =
            env.get(&rec)
        else {
            return Err(Reason::NoEq)
        };
        if *num_params != 2 || *num_motives != 1 || *num_minors != 1 || *num_indices != 1 {
            return Err(Reason::NoEq)
        }
        if env.get(&refl).is_none() {
            return Err(Reason::NoEq)
        }
        Ok(Eq { eq, refl, rec })
    }

    fn ls(&self, u: &Level) -> Rc<[Level]> { vec![u.clone()].into() }

    /// `Eq.{u} α a b`.
    fn at(&self, u: &Level, a_ty: &E, x: &E, y: &E) -> E {
        app_n(konst(self.eq.clone(), self.ls(u)), &[a_ty.clone(), x.clone(), y.clone()])
    }

    /// `Eq.refl.{u} α a`.
    fn refl_at(&self, u: &Level, a_ty: &E, x: &E) -> E {
        app_n(konst(self.refl.clone(), self.ls(u)), &[a_ty.clone(), x.clone()])
    }

    /// `Eq.rec.{0,u}` — the motive is `Prop`-valued wherever an *equation* is
    /// transported, which is everything in the isomorphism.
    #[allow(clippy::too_many_arguments)]
    fn rec_at(&self, u: &Level, a_ty: &E, a: &E, motive: &E, base: &E, bb: &E, h: &E) -> E {
        self.rec_at_lvl(&Level::Zero, u, a_ty, a, motive, base, bb, h)
    }

    /// `Eq.rec.{v,u} α a motive base b h`. The recursors transport a *value*
    /// rather than an equation, so their motive sits at the eliminator's own
    /// universe and not at `Prop`.
    #[allow(clippy::too_many_arguments)]
    fn rec_at_lvl(
        &self,
        v: &Level,
        u: &Level,
        a_ty: &E,
        a: &E,
        motive: &E,
        base: &E,
        bb: &E,
        h: &E,
    ) -> E {
        let ls: Rc<[Level]> = vec![v.clone(), u.clone()].into();
        app_n(konst(self.rec.clone(), ls), &[
            a_ty.clone(),
            a.clone(),
            motive.clone(),
            base.clone(),
            bb.clone(),
            h.clone(),
        ])
    }
}

/// The generator's read-only context. Every accessor takes the **depth** it is
/// wanted at; nothing below writes a shift at a use site.
struct Gen<'a> {
    env: Environment,
    b: &'a [IndType],
    u: &'a Level,
    eq: &'a Eq,
    /// The occurrences, each valid at depth [`Gen::np`].
    occs: &'a [E],
    model: &'a Name,
    no: &'a Rc<[Level]>,
    np: u32,
    ptys: &'a [E],
}

/// One constructor, peeled past the parameters: its field types, each in scope
/// of the parameters and the earlier fields.
struct Ctor {
    name: Name,
    fields: Vec<E>,
}

/// **One member's recursor, as the model restates it.** Read once by
/// [`Gen::rec_shape`] and used by both the recursor and its ι rules, which
/// share the `np + nm + nmin` binders and differ only past them.
struct RecShape {
    /// The member being eliminated.
    k: usize,
    /// `Bₖ.rec`, the block's own.
    src: Name,
    /// The motive universe, the recursor's single level parameter.
    v: Level,
    lparams: Vec<Name>,
    nm: usize,
    nmin: usize,
    /// The declared type, at the model's names.
    ty: E,
    /// `np + nm + nmin + 1` binder types, each at the depth its own binder sits
    /// at; the last is the major premise.
    binders: Vec<E>,
}

/// The export-side constructor an ι rule is about, as it is *applied*.
///
/// At the root that is `T._model.ctor_j`, a **definition** over the block's own
/// constructor; at a mimic it is the real container's constructor at the
/// occurrence's levels and arguments. The two differ in what precedes the
/// fields — the block's parameters, or the occurrence's.
enum Head {
    Model(Name),
    Real(Name, Rc<[Level]>, Vec<E>),
}

/// Where one packed position of a rule stands in the transport fold.
#[derive(Clone, Copy)]
enum Move {
    /// At `unpackᵢ (packᵢ f)`, where the reduced left-hand side leaves it.
    Source,
    /// At `f`, having been transported along `unpackPackᵢ f`.
    Target,
    /// At the motive's own `#1`, along the motive's own `#0` — the position
    /// this step of the fold is abstracting.
    Abstract,
}

impl Gen<'_> {
    fn names(&self, i: usize) -> (Name, Name, Name, Name) {
        let s = |w: &str| Name::str(self.model, &format!("{w}_{i}"));
        (s("pack"), s("unpack"), s("unpackPack"), s("packUnpack"))
    }

    /// The block's parameters at depth `d`.
    fn ps(&self, d: u32) -> Vec<E> { params_at(self.np, d) }

    /// Occurrence `i` at depth `d`.
    fn occ_at(&self, i: usize, d: u32) -> E { shift(&self.occs[i], 0, d - self.np) }

    /// `Bₖ p⃗` at depth `d`.
    fn mem_at(&self, k: usize, d: u32) -> E {
        app_n(konst(self.b[k].name.clone(), Rc::clone(self.no)), &self.ps(d))
    }

    /// `f p⃗ x` at depth `d` — every generated map takes the parameters first.
    fn call(&self, f: &Name, d: u32, x: E) -> E {
        let mut a = self.ps(d);
        a.push(x);
        app_n(konst(f.clone(), Rc::clone(self.no)), &a)
    }

    /// `Bₖ.c p⃗ args` at depth `d`.
    fn block_ctor(&self, k: usize, c: &Name, d: u32, args: &[E]) -> E {
        let mut a = self.ps(d);
        a.extend_from_slice(args);
        app_n(konst(rename_ctor(&self.b[k].name, c), Rc::clone(self.no)), &a)
    }

    fn wrap_f(&self, body: E) -> E { foralls(self.ptys, body) }

    fn wrap_l(&self, body: E) -> E { lams(self.ptys, body) }

    /// A constructor's type at the occurrence's levels and parameters: its
    /// universe parameters instantiated, then its own parameter binders peeled
    /// and substituted, leaving the field telescope at depth `np`.
    fn inst_ctor(&self, cn: &Name, ls: &Rc<[Level]>, qs: &[E]) -> R<E> {
        let ci = self.env.get(cn).ok_or(Reason::Malformed)?;
        let names = ci.lparams().to_vec();
        let ty = instantiate_lparams(ci.ty(), &names, ls).map_err(|_| Reason::Malformed)?;
        let mut cur = ty;
        for _ in 0..qs.len() {
            let Expr::Forall { body, .. } = &*cur.clone() else { return Err(Reason::Malformed) };
            cur = body.clone();
        }
        Ok(substs(&cur, qs, 0))
    }

    /// Peel `skip` binders and then the field telescope, checking no field type
    /// mentions an earlier field — the condition the congruence fold needs.
    fn peel_ctor(&self, name: &Name, ty: &E, skip: u32) -> R<Ctor> {
        let mut cur = ty.clone();
        for _ in 0..skip {
            let Expr::Forall { body, .. } = &*cur.clone() else { return Err(Reason::Malformed) };
            cur = body.clone();
        }
        let mut fields = Vec::new();
        while let Expr::Forall { ty: d, body } = &*cur.clone() {
            for k in 0..fields.len() as u32 {
                if crate::expr::has_bvar(d, k) {
                    return Err(Reason::DependentFields)
                }
            }
            fields.push(d.clone());
            cur = body.clone();
        }
        Ok(Ctor { name: name.clone(), fields })
    }

    /// A constructor's field types lifted from the depth each binder sits at
    /// — field `k` is under the `k` before it — to a common depth `d`.
    fn fields_at(&self, fields: &[E], d: u32) -> Vec<E> {
        fields
            .iter()
            .enumerate()
            .map(|(k, f)| shift(f, 0, d - (self.np + k as u32)))
            .collect()
    }

    /// Which member a block field's type is at, if any.
    fn member_of(&self, t: &E) -> Option<usize> {
        let (h, _) = get_app(t);
        match &*h {
            Expr::Const(n, _) => self.b.iter().position(|x| x.name == *n),
            _ => None,
        }
    }

    /// The four declarations of one mimic.
    fn four(
        &self,
        i: usize,
        member: usize,
        names: &(Name, Name, Name, Name),
        done: &[bool],
    ) -> R<Vec<Declaration>> {
        let (pack, unpack, retract, section) = names;
        let np = self.np;
        let def = |name: &Name, ty: E, value: E, kind| Declaration::Def {
            name: name.clone(),
            lparams: Vec::new(),
            ty,
            value,
            kind,
        };
        let pack_ty = self.wrap_f(forall(self.occ_at(i, np), self.mem_at(member, np + 1)));
        let unpack_ty = self.wrap_f(forall(self.mem_at(member, np), self.occ_at(i, np + 1)));
        let retract_ty = self.wrap_f(forall(
            self.occ_at(i, np),
            self.eq.at(
                self.u,
                &self.occ_at(i, np + 1),
                &self.call(unpack, np + 1, self.call(pack, np + 1, bvar(0))),
                &bvar(0),
            ),
        ));
        let section_ty = self.wrap_f(forall(
            self.mem_at(member, np),
            self.eq.at(
                self.u,
                &self.mem_at(member, np + 1),
                &self.call(pack, np + 1, self.call(unpack, np + 1, bvar(0))),
                &bvar(0),
            ),
        ));
        Ok(vec![
            def(pack, pack_ty, self.wrap_l(self.pack_value(i, member)?), DefKind::Def),
            def(unpack, unpack_ty, self.wrap_l(self.unpack_value(member)?), DefKind::Def),
            def(
                retract,
                retract_ty,
                self.wrap_l(self.retract_value(i, names)?),
                DefKind::Theorem,
            ),
            def(
                section,
                section_ty,
                self.wrap_l(self.section_value(i, member, done)?),
                DefKind::Theorem,
            ),
        ])
    }

    /// The container of occurrence `i`: its head name, level list and the
    /// arguments it is applied to, at depth `np`.
    fn container(&self, i: usize) -> R<(Name, Rc<[Level]>, Vec<E>)> {
        let (head, qs) = get_app(&self.occs[i]);
        let Expr::Const(c, cls) = &*head else { return Err(Reason::Malformed) };
        let Some(ConstantInfo::Inductive { num_indices, .. }) = self.env.get(c) else {
            return Err(Reason::Malformed)
        };
        if *num_indices != 0 {
            return Err(Reason::Indexed)
        }
        Ok((c.clone(), Rc::clone(cls), qs))
    }

    fn ctors_of(&self, c: &Name) -> R<Vec<Name>> {
        let Some(ConstantInfo::Inductive { ctors, .. }) = self.env.get(c) else {
            return Err(Reason::Malformed)
        };
        Ok(ctors.clone())
    }

    /// The container's recursor at a motive of level `v`: the motive universe
    /// goes in front of the container's own level list.
    fn rec_levels(&self, c: &Name, v: Level) -> R<Rc<[Level]>> {
        let ci = self.env.get(c).ok_or(Reason::Malformed)?;
        let mut ls = vec![v];
        ls.extend(ci.lparams().iter().map(|p| Level::Param(p.clone())));
        Ok(ls.into())
    }

    /// `pack_i := C.rec q⃗ (fun _ => Bᵢ p⃗) minors…`, partially applied — its
    /// type is `∀ _ : occᵢ, Bᵢ p⃗` on the nose, the motive being constant.
    fn pack_value(&self, i: usize, member: usize) -> R<E> {
        let np = self.np;
        let (c, cls, qs) = self.container(i)?;
        let motive = lam(self.occ_at(i, np), self.mem_at(member, np + 1));
        let mut args = qs.clone();
        args.push(motive);
        for cn in self.ctors_of(&c)? {
            args.push(self.pack_minor(i, member, &cls, &qs, &cn)?);
        }
        Ok(app_n(konst(Name::str(&c, "rec"), self.rec_levels(&c, self.u.clone())?), &args))
    }

    /// `fun f⃗ ih⃗ => Bᵢ.c p⃗ g⃗`, where a field recursive in the container is its
    /// own induction hypothesis, a field at another mimic is packed, and
    /// anything else — a plain field, or a field at the root, which the block
    /// types at `B₀ p⃗` and `T._model.self p⃗` unfolds to — goes through
    /// untouched.
    fn pack_minor(
        &self,
        i: usize,
        member: usize,
        cls: &Rc<[Level]>,
        qs: &[E],
        cn: &Name,
    ) -> R<E> {
        let np = self.np;
        let cty = self.inst_ctor(cn, cls, qs)?;
        let ct = self.peel_ctor(cn, &cty, 0)?;
        // **A field's type lives at the depth its own binder sits at**, not at
        // the telescope's: field `k` is under the `k` fields before it. At
        // `np = 0` the occurrence has no free variables and the difference is
        // invisible, which is exactly why it is written out here.
        let recs: Vec<usize> = (0..ct.fields.len())
            .filter(|&k| ct.fields[k] == self.occ_at(i, np + k as u32))
            .collect();
        let n = ct.fields.len();
        let m = recs.len();
        let d = np + n as u32 + m as u32;
        let field = |k: usize| bvar(d - 1 - (np + k as u32));
        let ih = |t: usize| bvar((m - 1 - t) as u32);
        let mut args = Vec::with_capacity(n);
        for k in 0..n {
            if let Some(t) = recs.iter().position(|&r| r == k) {
                args.push(ih(t));
            } else if let Some(other) =
                (0..self.occs.len()).find(|&o| self.occ_at(o, np + k as u32) == ct.fields[k])
            {
                args.push(self.call(&self.names(other).0, d, field(k)));
            } else {
                args.push(field(k));
            }
        }
        let body = self.block_ctor(member, &ct.name, d, &args);
        // Binder types: the fields as declared, then one `Bᵢ p⃗` per recursive
        // field, each at the depth its own binder is introduced at.
        let mut tys: Vec<E> = ct.fields.clone();
        for t in 0..m {
            tys.push(self.mem_at(member, np + n as u32 + t as u32));
        }
        Ok(lams(&tys, body))
    }

    /// **`congrPack_i : ∀p⃗ l₀ l, Eq l₀ l → Eq (packᵢ l₀) (packᵢ l)`.**
    ///
    /// Small, and needed for a reason that is not obvious. The ι rule of a
    /// **root** constructor with a packed field has, on its left, the transport
    /// `recₖ`'s minor performs — along `packUnpack (pack f)`. Proving it means
    /// `Eq.rec` on `unpackPack f`, whose motive has to name a proof of
    /// `Eq (pack (unpack (pack f))) (pack x)` for the abstracted `x`, and only
    /// a *congruence* of `pack` is that. Proof irrelevance then identifies the
    /// two at `x := f`, which is where the triangle identity would otherwise
    /// have to be proved.
    fn congr_pack_decl(&self, i: usize, name: &Name) -> R<Declaration> {
        let np = self.np;
        let occ = |d: u32| self.occ_at(i, d);
        let mem = |d: u32| self.mem_at(i + 1, d);
        let pack = self.names(i).0;
        // `∀p⃗ (l₀ l : occᵢ) (h : Eq l₀ l), Eq (packᵢ l₀) (packᵢ l)`
        let ty = self.wrap_f(forall(
            occ(np),
            forall(
                occ(np + 1),
                forall(
                    self.eq.at(self.u, &occ(np + 2), &bvar(1), &bvar(0)),
                    self.eq.at(
                        self.u,
                        &mem(np + 3),
                        &self.call(&pack, np + 3, bvar(2)),
                        &self.call(&pack, np + 3, bvar(1)),
                    ),
                ),
            ),
        ));
        // `Eq.rec` on `h`, at `fun x _ => Eq (packᵢ l₀) (packᵢ x)`, landing at
        // `Eq.refl (packᵢ l₀)`.
        let d = np + 3;
        let l0 = bvar(2);
        let l = bvar(1);
        let h = bvar(0);
        let motive = lam(
            occ(d),
            lam(
                self.eq.at(self.u, &occ(d + 1), &shift(&l0, 0, 1), &bvar(0)),
                self.eq.at(
                    self.u,
                    &mem(d + 2),
                    &self.call(&pack, d + 2, shift(&l0, 0, 2)),
                    &self.call(&pack, d + 2, bvar(1)),
                ),
            ),
        );
        let base = self.eq.refl_at(self.u, &mem(d), &self.call(&pack, d, l0.clone()));
        let value = self.wrap_l(lams(&[occ(np), occ(np + 1), self.eq.at(self.u, &occ(np + 2), &bvar(1), &bvar(0))], self.eq.rec_at(
            self.u,
            &occ(d),
            &l0,
            &motive,
            &base,
            &l,
            &h,
        )));
        Ok(Declaration::Def {
            name: name.clone(),
            lparams: Vec::new(),
            ty,
            value,
            kind: DefKind::Theorem,
        })
    }

    /// `T._model.rec_k`.
    fn rec_name(&self, k: usize) -> Name { Name::str(self.model, &format!("rec_{k}")) }

    /// `T._model.congrPack_i`.
    fn congr_pack_name(&self, i: usize) -> Name {
        Name::str(self.model, &format!("congrPack_{i}"))
    }

    /// **The ι rules of one member's recursor**, one per rule `Bₖ.rec` carries,
    /// in the order it carries them.
    ///
    /// Each comes back as `(the export's constructor, the theorem's name, the
    /// theorem)`. The constructor is the key the *installed* `T.rec_k` files its
    /// rule under — `Tree.node` at the root, `List.cons` at a mimic — so a
    /// caller can line the two up without knowing how the block was named.
    fn iota_decls(
        &self,
        k: usize,
        shape: &RecShape,
        ctor_tys: &[(Name, Name, E)],
    ) -> R<Vec<(Name, Name, Declaration)>> {
        let np = self.np;
        let d0 = np + shape.nm as u32 + shape.nmin as u32;
        let prefix: Vec<E> = shape.binders[..d0 as usize].to_vec();
        // The block-wide minor index of this member's first constructor: the
        // minors are bound member by member, which is the order
        // [`Gen::block_minors`] rebuilds them in.
        let minor_base: usize = self.b[..k].iter().map(|t| t.ctors.len()).sum();

        let mut out = Vec::new();
        for (j, (bcn, bcty)) in self.b[k].ctors.iter().enumerate() {
            let bct = self.peel_ctor(bcn, bcty, np)?;
            // The export side: the constructor as it is applied, and the field
            // telescope the theorem binds — which is the **export's**, not the
            // block's, because the rule is an equation about the declared
            // recursor and its declared constructors.
            let (key, head, ext) = if k == 0 {
                let (export_c, model_c, mty) = ctor_tys.get(j).ok_or(Reason::Malformed)?;
                let ct = self.peel_ctor(model_c, mty, np)?;
                (export_c.clone(), Head::Model(model_c.clone()), ct.fields)
            } else {
                let real = self.real_ctor(k - 1, bcn)?;
                let (_, cls, qs) = self.container(k - 1)?;
                let cty = self.inst_ctor(&real, &cls, &qs)?;
                let ct = self.peel_ctor(&real, &cty, 0)?;
                (real.clone(), Head::Real(real, cls, qs), ct.fields)
            };
            if ext.len() != bct.fields.len() {
                return Err(Reason::Malformed)
            }
            let mem: Vec<Option<usize>> =
                bct.fields.iter().map(|f| self.member_of(f)).collect();
            // **A recursive field the head of whose type is not a member is one
            // this module cannot write.** `Bₖ.rec`'s rule gives an induction
            // hypothesis to a field of type `∀ …, Bₘ …` as well, and the
            // right-hand side below has none for it — so the statement would be
            // a different equation from the one the recursor obeys. Nothing in
            // the fixtures reaches it; it is a decline rather than a wrong
            // theorem.
            for (x, f) in bct.fields.iter().enumerate() {
                if mem[x].is_none() && self.b.iter().any(|t| crate::expr::has_const(&t.name, f)) {
                    return Err(Reason::Malformed)
                }
            }
            let moving: Vec<usize> =
                (0..mem.len()).filter(|&x| matches!(mem[x], Some(m) if m > 0)).collect();
            let rule = Rule {
                g: self,
                k,
                v: shape.v.clone(),
                nm: shape.nm,
                nmin: shape.nmin,
                d0,
                minor_ix: minor_base + j,
                head,
                ext,
                bcn: bcn.clone(),
                blk: bct.fields,
                mem,
                moving,
            };
            let mut binders = prefix.clone();
            for f in &rule.ext {
                binders.push(shift(f, 0, d0 - np));
            }
            let name = Name::str(self.model, &format!("iota_{k}_{j}"));
            out.push((key, name.clone(), Declaration::Def {
                name,
                lparams: shape.lparams.clone(),
                ty: foralls(&binders, rule.statement()?),
                value: lams(&binders, rule.value()?),
                kind: DefKind::Theorem,
            }));
        }
        Ok(out)
    }

    /// **`Bₖ.rec`'s statement at the model's names, with its telescope read
    /// off.** Separate from [`Gen::rec_decl`] because the ι rules are stated at
    /// the same telescope — the `np + nm + nmin` binders every member's
    /// recursor shares, then that member's own major — and rebuilding it from
    /// the environment twice is how the two would drift apart.
    fn rec_shape(&self, k: usize, heads: &HashMap<Name, (u32, E)>) -> R<RecShape> {
        let np = self.np;
        let src = Name::str(&self.b[k].name, "rec");
        let ConstantInfo::Recursor { lparams, ty, num_motives, num_minors, num_indices, .. } =
            self.env.get(&src).ok_or(Reason::Malformed)?.clone()
        else {
            return Err(Reason::Malformed)
        };
        if num_indices != 0 || lparams.len() != 1 {
            return Err(Reason::Indexed)
        }
        let nm = num_motives as usize;
        let nmin = num_minors as usize;
        if nm != self.b.len() {
            return Err(Reason::Malformed)
        }
        let ty = crate::nested::restore(heads, &ty);
        let mut binders = Vec::new();
        let mut cur = ty.clone();
        for _ in 0..(np as usize + nm + nmin + 1) {
            let Expr::Forall { ty: t, body } = &*cur.clone() else { return Err(Reason::Malformed) };
            binders.push(t.clone());
            cur = body.clone();
        }
        Ok(RecShape {
            k,
            src,
            v: Level::Param(lparams[0].clone()),
            lparams: lparams.to_vec(),
            nm,
            nmin,
            ty,
            binders,
        })
    }

    /// **One recursor per block member, at zone A's own statement.**
    ///
    /// The declared type is `Bₖ.rec`'s, restored through `heads` — the same
    /// table `nested::add` restores the *export's* recursor with, pointing at
    /// the model's names instead. So `T._model.rec_k` and `T.rec_k` are the
    /// same statement about different constants, which is the whole of what the
    /// keying needs.
    ///
    /// The value re-runs the block's recursor at a **shifted motive vector**:
    /// the caller's own at the root, and the caller's composed with `unpack` at
    /// each mimic. Three of the four minor shapes then go through untouched —
    /// a mimic's minor because `unpack` ι-reduces on the mimic's constructors
    /// to the real ones, and the induction hypotheses because the block's are
    /// already at the composed motive. **Only a root constructor with a packed
    /// field transports**, and it transports along `packUnpack`, one position
    /// at a time.
    ///
    /// At a mimic the major itself has to move: the block eliminates `Bₖ` and
    /// the export eliminates `occₖ`, so the recursor runs at `pack major` and
    /// the result comes back along `unpackPack major`. That and the induction
    /// hypothesis an ι rule moves ([`Rule::sides`]) are the only two `Eq.rec`s
    /// in this module whose motive is not `Prop`-valued, and they are the same
    /// transport at two depths.
    fn rec_decl(&self, name: &Name, shape: &RecShape) -> R<Declaration> {
        let np = self.np;
        let k = shape.k;
        let src = shape.src.clone();
        let v = shape.v.clone();
        let vs: Rc<[Level]> = vec![v.clone()].into();
        let nm = shape.nm;
        let nmin = shape.nmin;
        let ty = shape.ty.clone();
        let binders = shape.binders.clone();
        let d = binders.len() as u32;
        let motive = |j: usize| bvar(d - 1 - (np + j as u32));
        let minor = |t: usize| bvar(d - 1 - (np + nm as u32 + t as u32));
        let major = bvar(0);

        let mut args: Vec<E> = self.ps(d);
        args.extend(self.block_motives(d, &motive));
        let mins = self.block_minors(d, &motive, &minor, &v)?;
        if mins.len() != nmin || nm != self.b.len() {
            return Err(Reason::Malformed)
        }
        args.extend(mins);

        let value = if k == 0 {
            let mut a = args;
            a.push(major.clone());
            self.wrap_l_all(&binders, app_n(konst(src.clone(), vs), &a))
        } else {
            // The **retraction**, not the section: the major moves along
            // `unpack (pack l) = l` at the occurrence, and `packUnpack` is the
            // other one, about the mimic.
            let (pack, _, retract, _) = self.names(k - 1);
            let occ = self.occ_at(k - 1, d);
            let base = {
                let mut a = args;
                a.push(self.call(&pack, d, major.clone()));
                app_n(konst(src.clone(), vs), &a)
            };
            // `fun (x : occₖ) (_ : Eq (unpack (pack major)) x) => Mₖ x`.
            let trip = self.call(&self.names(k - 1).1, d, self.call(&pack, d, major.clone()));
            let mot = lam(
                occ.clone(),
                lam(
                    self.eq.at(self.u, &shift(&occ, 0, 1), &shift(&trip, 0, 1), &bvar(0)),
                    crate::expr::app(shift(&motive(k), 0, 2), bvar(1)),
                ),
            );
            let e = self.eq.rec_at_lvl(
                &v,
                self.u,
                &occ,
                &trip,
                &mot,
                &base,
                &major,
                &self.call(&retract, d, major.clone()),
            );
            self.wrap_l_all(&binders, e)
        };
        Ok(Declaration::Def {
            name: name.clone(),
            lparams: shape.lparams.clone(),
            ty,
            value,
            kind: DefKind::Def,
        })
    }

    /// **The block's motive vector at depth `d`** — the caller's own at the
    /// root, the caller's composed with `unpack` at each mimic.
    ///
    /// Depth-parameterised because it has two callers and they sit at different
    /// depths: the recursor's own binder telescope, and an ι rule's, which adds
    /// the constructor's fields on top of it. `Bᵢ.rec p⃗ M''⃗ S''⃗ (packᵢ f)` is
    /// the induction hypothesis an ι proof has to name, and **no model constant
    /// denotes it** — `T._model.rec_i` is that term already transported, of type
    /// `Mᵢ f` where the proof needs `Mᵢ (unpackᵢ (packᵢ f))`. So the vectors
    /// have to be rebuildable wherever they are wanted rather than referenced.
    fn block_motives(&self, d: u32, motive: &dyn Fn(usize) -> E) -> Vec<E> {
        (0..self.b.len())
            .map(|j| {
                if j == 0 {
                    motive(0)
                } else {
                    lam(
                        self.mem_at(j, d),
                        crate::expr::app(
                            shift(&motive(j), 0, 1),
                            self.call(&self.names(j - 1).1, d + 1, bvar(0)),
                        ),
                    )
                }
            })
            .collect()
    }

    /// **The block's minor vector at depth `d`**, in the block's own order —
    /// every member's constructors, member by member — which is the order
    /// `Bₖ.rec` binds them in and the order the caller's own minors arrive in.
    fn block_minors(
        &self,
        d: u32,
        motive: &dyn Fn(usize) -> E,
        minor: &dyn Fn(usize) -> E,
        v: &Level,
    ) -> R<Vec<E>> {
        let mut out = Vec::new();
        let mut t = 0usize;
        for j in 0..self.b.len() {
            for (cn, cty) in &self.b[j].ctors {
                out.push(self.rec_minor(j, cn, cty, &minor(t), d, motive, v)?);
                t += 1;
            }
        }
        Ok(out)
    }

    /// One minor of the block's recursor, built from the caller's own.
    #[allow(clippy::too_many_arguments)]
    fn rec_minor(
        &self,
        j: usize,
        cn: &Name,
        cty: &E,
        s_t: &E,
        d0: u32,
        motive: &dyn Fn(usize) -> E,
        v: &Level,
    ) -> R<E> {
        let np = self.np;
        let ct = self.peel_ctor(cn, cty, np)?;
        let recs: Vec<usize> =
            (0..ct.fields.len()).filter(|&x| self.member_of(&ct.fields[x]).is_some()).collect();
        let n = ct.fields.len();
        let m = recs.len();
        let d = d0 + n as u32 + m as u32;
        let field = |x: usize| bvar(d - 1 - (d0 + x as u32));
        let ih = |t: usize| bvar((m - 1 - t) as u32);
        // The caller's minor wants the fields at their **real** types, so a
        // field the block holds at a mimic is unpacked on the way in. The
        // induction hypotheses pass through: the block's are already at the
        // composed motive, which is what the caller's minor asks for.
        let mut real: Vec<E> = Vec::with_capacity(n);
        for x in 0..n {
            match self.member_of(&ct.fields[x]) {
                Some(mem) if mem > 0 => {
                    real.push(self.call(&self.names(mem - 1).1, d, field(x)))
                }
                _ => real.push(field(x)),
            }
        }
        let mut applied: Vec<E> = real.clone();
        for t in 0..m {
            applied.push(ih(t));
        }
        let body = app_n(shift(s_t, 0, d - d0), &applied);

        // Binder types: the block's own fields, then one hypothesis per
        // recursive field at the **composed** motive, each at its own depth.
        let mut tys: Vec<E> = self.fields_at(&ct.fields, d0).into_iter().enumerate().map(
            |(x, f)| shift(&f, 0, x as u32),
        ).collect();
        for (t, &r) in recs.iter().enumerate() {
            let dd = d0 + n as u32 + t as u32;
            let f = bvar(dd - 1 - (d0 + r as u32));
            let mem = self.member_of(&ct.fields[r]).ok_or(Reason::Malformed)?;
            tys.push(if mem == 0 {
                crate::expr::app(shift(&motive(0), 0, dd - d0), f)
            } else {
                crate::expr::app(
                    shift(&motive(mem), 0, dd - d0),
                    self.call(&self.names(mem - 1).1, dd, f),
                )
            });
        }

        if j > 0 {
            return Ok(lams(&tys, body))
        }
        // A root constructor: the caller's minor lands at
        // `M₀ (T._model.ctor f⃗_real)`, which unfolds to `M₀ (B₀.c (pack (unpack f⃗)))`,
        // and the block wants `M₀ (B₀.c f⃗)`. One transport per packed field.
        let mut lhs: Vec<E> = Vec::with_capacity(n);
        let mut proofs: Vec<Option<E>> = Vec::with_capacity(n);
        for x in 0..n {
            match self.member_of(&ct.fields[x]) {
                Some(mem) if mem > 0 => {
                    let nmm = self.names(mem - 1);
                    lhs.push(self.call(&nmm.0, d, self.call(&nmm.1, d, field(x))));
                    proofs.push(Some(self.call(&nmm.3, d, field(x))));
                }
                _ => {
                    lhs.push(field(x));
                    proofs.push(None);
                }
            }
        }
        let all: Vec<E> = (0..n).map(field).collect();
        let this = ct.name.clone();
        let names: Vec<Name> = self.b.iter().map(|x| x.name.clone()).collect();
        let no = Rc::clone(self.no);
        let np2 = np;
        let rebuild = move |a: &[E], extra: u32| {
            let mut vv = params_at(np2, d + extra);
            vv.extend_from_slice(a);
            app_n(konst(rename_ctor(&names[0], &this), Rc::clone(&no)), &vv)
        };
        let ftys = self.fields_at(&ct.fields, d);
        let m0 = shift(&motive(0), 0, d - d0);
        let out = self.fold_value(v, &m0, &ftys, &lhs, &all, &proofs, &rebuild, body)?;
        Ok(lams(&tys, out))
    }

    /// The value-transport counterpart of [`Gen::fold_congr`]: from
    /// `v : M (f lhs⃗)` and `pⱼ : Eq lhsⱼ rhsⱼ`, produce `M (f rhs⃗)`, one
    /// position at a time. The motive is the caller's own and lands at the
    /// eliminator's universe, which is the one place in this module an `Eq.rec`
    /// is not `Prop`-valued.
    #[allow(clippy::too_many_arguments)]
    fn fold_value(
        &self,
        v: &Level,
        m0: &E,
        field_tys: &[E],
        lhs: &[E],
        rhs: &[E],
        proofs: &[Option<E>],
        rebuild: &dyn Fn(&[E], u32) -> E,
        base: E,
    ) -> R<E> {
        let n = lhs.len();
        let mut acc = base;
        for j in 0..n {
            let Some(p) = &proofs[j] else { continue };
            if lhs[j] == rhs[j] {
                continue
            }
            let alpha = &field_tys[j];
            let up = |e: &E| shift(e, 0, 2);
            let mut mix: Vec<E> = Vec::with_capacity(n);
            for kk in 0..n {
                mix.push(if kk < j {
                    up(&rhs[kk])
                } else if kk == j {
                    bvar(1)
                } else {
                    up(&lhs[kk])
                });
            }
            let body = crate::expr::app(up(m0), rebuild(&mix, 2));
            let eqn = self.eq.at(self.u, &shift(alpha, 0, 1), &shift(&lhs[j], 0, 1), &bvar(0));
            let mot = lam(alpha.clone(), lam(eqn, body));
            // The motive's universe is the eliminator's, read off `M₀`'s own
            // codomain rather than assumed: `Eq.rec` at `Prop` here would be a
            // different rule.
            acc = self.eq.rec_at_lvl(
                v,
                self.u,
                alpha,
                &lhs[j],
                &mot,
                &acc,
                &rhs[j],
                p,
            );
        }
        Ok(acc)
    }

    /// `fun <binders> => body`, for a telescope already at its own depths.
    fn wrap_l_all(&self, tys: &[E], body: E) -> E { lams(tys, body) }

    /// `T._model.ctor_j := fun p⃗ f⃗ => B₀.c p⃗ g⃗`, where a field the block types
    /// at a **mimic** is packed on the way in and everything else — a plain
    /// field, or one at the root — passes through.
    ///
    /// The declared type is the *export's*, with `T` rewritten to the carrier;
    /// the field telescope below is read off **that**, so the parameters this
    /// binds are the ones the export declared and not ones reconstructed here.
    fn ctor_value(&self, j: usize, real_ty: &E) -> R<E> {
        let np = self.np;
        let cn = &self.b[0].ctors[j].0;
        let block = self.peel_ctor(cn, &self.b[0].ctors[j].1, np)?;
        let real = self.peel_ctor(cn, real_ty, np)?;
        if real.fields.len() != block.fields.len() {
            return Err(Reason::Malformed)
        }
        let n = real.fields.len();
        let d = np + n as u32;
        let field = |k: usize| bvar(d - 1 - (np + k as u32));
        let mut args = Vec::with_capacity(n);
        for k in 0..n {
            match self.member_of(&block.fields[k]) {
                Some(mem) if mem > 0 => {
                    args.push(self.call(&self.names(mem - 1).0, d, field(k)))
                }
                _ => args.push(field(k)),
            }
        }
        let body = self.block_ctor(0, cn, d, &args);
        Ok(self.wrap_l(lams(&real.fields, body)))
    }

    /// `unpack_i := Bᵢ.rec p⃗ motives… minors…`, partially applied.
    fn unpack_value(&self, member: usize) -> R<E> {
        let np = self.np;
        let mut args: Vec<E> = self.ps(np);
        for k in 0..self.b.len() {
            let cod =
                if k == 0 { self.mem_at(0, np + 1) } else { self.occ_at(k - 1, np + 1) };
            args.push(lam(self.mem_at(k, np), cod));
        }
        for k in 0..self.b.len() {
            for (cn, cty) in &self.b[k].ctors {
                args.push(self.unpack_minor(k, cn, cty)?);
            }
        }
        Ok(app_n(
            konst(Name::str(&self.b[member].name, "rec"), vec![self.u.clone()].into()),
            &args,
        ))
    }

    /// A member's minor for `unpack`: at the root, rebuild the constructor; at
    /// a mimic, build the **real** container's constructor, taking each field
    /// at another mimic from its induction hypothesis.
    fn unpack_minor(&self, k: usize, cn: &Name, cty: &E) -> R<E> {
        let np = self.np;
        let ct = self.peel_ctor(cn, cty, np)?;
        let recs: Vec<usize> =
            (0..ct.fields.len()).filter(|&x| self.member_of(&ct.fields[x]).is_some()).collect();
        let n = ct.fields.len();
        let m = recs.len();
        let d = np + n as u32 + m as u32;
        let field = |x: usize| bvar(d - 1 - (np + x as u32));
        let ih = |t: usize| bvar((m - 1 - t) as u32);

        let mut args = Vec::with_capacity(n);
        for x in 0..n {
            match self.member_of(&ct.fields[x]) {
                // A field at a *mimic* is unpacked, and its unpacked value is
                // exactly this recursor's induction hypothesis for it.
                Some(mem) if mem > 0 => {
                    let t = recs.iter().position(|&r| r == x).ok_or(Reason::Malformed)?;
                    args.push(ih(t));
                }
                // A field at the root passes through: the block types it at
                // `B₀ p⃗`, and the real constructor wants `T._model.self p⃗`,
                // which is that by δ.
                _ => args.push(field(x)),
            }
        }

        let body = if k == 0 {
            self.block_ctor(0, &ct.name, d, &(0..n).map(field).collect::<Vec<_>>())
        } else {
            let (_, cls, qs) = self.container(k - 1)?;
            let real = self.real_ctor(k - 1, cn)?;
            let mut a: Vec<E> = qs.iter().map(|q| shift(q, 0, d - np)).collect();
            a.extend(args);
            app_n(konst(real, cls), &a)
        };

        let mut tys: Vec<E> = ct.fields.clone();
        for (t, &r) in recs.iter().enumerate() {
            let dd = np + n as u32 + t as u32;
            let mem = self.member_of(&ct.fields[r]).ok_or(Reason::Malformed)?;
            tys.push(if mem == 0 { self.mem_at(0, dd) } else { self.occ_at(mem - 1, dd) });
        }
        Ok(lams(&tys, body))
    }

    /// The real container constructor a mimic's constructor stands for, by its
    /// last name component — the correspondence [`crate::nested`] builds the
    /// mimic from in the first place.
    fn real_ctor(&self, i: usize, cn: &Name) -> R<Name> {
        let (c, _, _) = self.container(i)?;
        let last = match cn {
            Name::Str(_, s) => s.to_string(),
            other => other.to_string(),
        };
        self.ctors_of(&c)?
            .into_iter()
            .find(|r| matches!(r, Name::Str(_, s) if **s == last))
            .ok_or(Reason::Malformed)
    }

    /// `unpackPack_i : ∀p⃗ l, Eq (unpack_i p⃗ (pack_i p⃗ l)) l`, by the
    /// container's own recursor, one congruence per field the round trip moves.
    fn retract_value(&self, i: usize, names: &(Name, Name, Name, Name)) -> R<E> {
        let np = self.np;
        let (pack, unpack, _, _) = names;
        let (c, cls, qs) = self.container(i)?;
        let trip = |x: E, d: u32| self.call(unpack, d, self.call(pack, d, x));
        let motive = lam(
            self.occ_at(i, np),
            self.eq.at(self.u, &self.occ_at(i, np + 1), &trip(bvar(0), np + 1), &bvar(0)),
        );
        let mut args = qs.clone();
        args.push(motive);
        for cn in self.ctors_of(&c)? {
            let cty = self.inst_ctor(&cn, &cls, &qs)?;
            let ct = self.peel_ctor(&cn, &cty, 0)?;
            let recs: Vec<usize> = (0..ct.fields.len())
                .filter(|&k| ct.fields[k] == self.occ_at(i, np + k as u32))
                .collect();
            let n = ct.fields.len();
            let m = recs.len();
            let d = np + n as u32 + m as u32;
            let field = |k: usize| bvar(d - 1 - (np + k as u32));
            let ih = |t: usize| bvar((m - 1 - t) as u32);
            let mut lhs = Vec::with_capacity(n);
            let mut rhs = Vec::with_capacity(n);
            let mut proofs: Vec<Option<E>> = Vec::with_capacity(n);
            for k in 0..n {
                rhs.push(field(k));
                if let Some(t) = recs.iter().position(|&r| r == k) {
                    lhs.push(trip(field(k), d));
                    proofs.push(Some(ih(t)));
                } else if let Some(other) =
                    (0..self.occs.len()).find(|&o| self.occ_at(o, np + k as u32) == ct.fields[k])
                {
                    let on = self.names(other);
                    lhs.push(self.call(&on.1, d, self.call(&on.0, d, field(k))));
                    proofs.push(Some(self.call(&on.2, d, field(k))));
                } else {
                    lhs.push(field(k));
                    proofs.push(None);
                }
            }
            let np2 = np;
            let cn2 = cn.clone();
            let cls2 = Rc::clone(&cls);
            let qs2 = qs.clone();
            let rebuild = move |a: &[E], extra: u32| {
                let mut v: Vec<E> = qs2.iter().map(|q| shift(q, 0, d + extra - np2)).collect();
                v.extend_from_slice(a);
                app_n(konst(cn2.clone(), Rc::clone(&cls2)), &v)
            };
            // **The fold uses a field's type at the minor's body depth**, and
            // `peel_ctor` returns it at the depth its own binder sits at. The
            // two differ by the fields that follow it, and at `np = 0` with a
            // closed field type they coincide — the shift that is invisible
            // there is the one written out here.
            let ftys = self.fields_at(&ct.fields, d);
            let body = self.fold_congr(&self.occ_at(i, d), &ftys, &lhs, &rhs, &proofs, &rebuild)?;
            // **The induction hypothesis is the motive at its own field**, not
            // the motive's codomain. Binder `n + t` is in scope of the `n`
            // fields and the `t` hypotheses before it, so the field it is about
            // is indexed at *that* depth and not at the body's.
            let mut tys: Vec<E> = ct.fields.clone();
            for (t, &r) in recs.iter().enumerate() {
                let dd = np + n as u32 + t as u32;
                let f = bvar(dd - 1 - (np + r as u32));
                tys.push(self.eq.at(
                    self.u,
                    &self.occ_at(i, dd),
                    &trip(f.clone(), dd),
                    &f,
                ));
            }
            args.push(lams(&tys, body));
        }
        Ok(app_n(konst(Name::str(&c, "rec"), self.rec_levels(&c, Level::Zero)?), &args))
    }

    /// `packUnpack_i : ∀p⃗ b, Eq (pack_i p⃗ (unpack_i p⃗ b)) b`, by the block's
    /// recursor.
    ///
    /// **The motive is the round trip only where the round trip exists.** A
    /// mimic this development has not reached yet has no `pack`, so its motive
    /// is reflexivity — which is all its own minors need, because a constructor
    /// whose field sits at an unreached mimic cannot occur: the emission order
    /// is topological and a field at a mimic is always at a *deeper* one.
    fn section_value(&self, i: usize, member: usize, done: &[bool]) -> R<E> {
        let np = self.np;
        let live = |k: usize| k > 0 && (k - 1 == i || done[k - 1]);
        let mut args: Vec<E> = self.ps(np);
        for k in 0..self.b.len() {
            args.push(lam(self.mem_at(k, np), self.section_motive(k, np + 1, &bvar(0), &live)));
        }
        for k in 0..self.b.len() {
            for (cn, cty) in &self.b[k].ctors {
                args.push(self.section_minor(k, cn, cty, &live)?);
            }
        }
        Ok(app_n(
            konst(Name::str(&self.b[member].name, "rec"), vec![Level::Zero].into()),
            &args,
        ))
    }

    /// The section's motive at member `k`, applied to `x`, at depth `d`.
    fn section_motive(&self, k: usize, d: u32, x: &E, live: &dyn Fn(usize) -> bool) -> E {
        let ty = self.mem_at(k, d);
        if live(k) {
            let nm = self.names(k - 1);
            self.eq.at(self.u, &ty, &self.call(&nm.0, d, self.call(&nm.1, d, x.clone())), x)
        } else {
            self.eq.at(self.u, &ty, x, x)
        }
    }

    fn section_minor(
        &self,
        k: usize,
        cn: &Name,
        cty: &E,
        live: &dyn Fn(usize) -> bool,
    ) -> R<E> {
        let np = self.np;
        let ct = self.peel_ctor(cn, cty, np)?;
        let recs: Vec<usize> =
            (0..ct.fields.len()).filter(|&x| self.member_of(&ct.fields[x]).is_some()).collect();
        let n = ct.fields.len();
        let m = recs.len();
        let d = np + n as u32 + m as u32;
        let field = |x: usize| bvar(d - 1 - (np + x as u32));
        let ih = |t: usize| bvar((m - 1 - t) as u32);
        // The induction hypothesis is the motive *at its own field*, indexed at
        // the depth that binder is introduced at.
        let mut tys: Vec<E> = ct.fields.clone();
        for (t, &r) in recs.iter().enumerate() {
            let dd = np + n as u32 + t as u32;
            let f = bvar(dd - 1 - (np + r as u32));
            let mem = self.member_of(&ct.fields[r]).ok_or(Reason::Malformed)?;
            tys.push(self.section_motive(mem, dd, &f, live));
        }
        let all: Vec<E> = (0..n).map(field).collect();
        let this = ct.name.clone();
        let kk = k;
        let np2 = np;
        let names: Vec<Name> = self.b.iter().map(|x| x.name.clone()).collect();
        let no = Rc::clone(self.no);
        let rebuild = move |a: &[E], extra: u32| {
            let mut v = params_at(np2, d + extra);
            v.extend_from_slice(a);
            app_n(konst(rename_ctor(&names[kk], &this), Rc::clone(&no)), &v)
        };
        let ty = self.mem_at(k, d);
        if !live(k) {
            let e = rebuild(&all, 0);
            return Ok(lams(&tys, self.eq.refl_at(self.u, &ty, &e)))
        }
        let mut lhs = Vec::with_capacity(n);
        let mut proofs: Vec<Option<E>> = Vec::with_capacity(n);
        for x in 0..n {
            match self.member_of(&ct.fields[x]) {
                Some(mem) if live(mem) => {
                    let t = recs.iter().position(|&r| r == x).ok_or(Reason::Malformed)?;
                    let nm = self.names(mem - 1);
                    lhs.push(self.call(&nm.0, d, self.call(&nm.1, d, field(x))));
                    proofs.push(Some(ih(t)));
                }
                _ => {
                    lhs.push(field(x));
                    proofs.push(None);
                }
            }
        }
        let ftys = self.fields_at(&ct.fields, d);
        let body = self.fold_congr(&ty, &ftys, &lhs, &all, &proofs, &rebuild)?;
        Ok(lams(&tys, body))
    }

    /// **One congruence per moving argument.** From `pⱼ : Eq lhsⱼ rhsⱼ` at the
    /// positions that move, build `Eq (f lhs⃗) (f rhs⃗)` by transporting one
    /// position at a time: at step `j` the accumulator proves
    /// `Eq (f lhs⃗) (f mix(j))`, where `mix(j)` is `rhs` below `j` and `lhs` at
    /// and above it, and `Eq.rec` on `pⱼ` advances it to `mix(j+1)`.
    ///
    /// This is where a constructor with **two or more** moving positions is
    /// paid for, and it is why the fold exists rather than a single transport:
    /// `nested_deep.lean`'s `DTree` has `cons : M₁ → M₀ → M₀`, two mimic fields
    /// in one constructor, and `nested_shapes.lean`'s
    /// `BTree.node : Pair BTree → Pair BTree → BTree` is the same shape at the
    /// root. Those two are the loop's only occupants.
    ///
    /// [`Rule::sides`] calls it a third way, and that use is the reason it is
    /// not a declaration: a mimic's ι rule needs the congruence of the *real*
    /// container's constructor with a **different** position abstracted at each
    /// step of its own fold, and a named lemma would be one per position.
    fn fold_congr(
        &self,
        goal_ty: &E,
        field_tys: &[E],
        lhs: &[E],
        rhs: &[E],
        proofs: &[Option<E>],
        rebuild: &dyn Fn(&[E], u32) -> E,
    ) -> R<E> {
        let n = lhs.len();
        let start = rebuild(lhs, 0);
        let mut acc = self.eq.refl_at(self.u, goal_ty, &start);
        for j in 0..n {
            let Some(p) = &proofs[j] else { continue };
            if lhs[j] == rhs[j] {
                continue
            }
            let alpha = &field_tys[j];
            // `motive : ∀ (x : Fⱼ) (_ : Eq Fⱼ lhsⱼ x), Prop`. The body sits
            // under **two** binders, so everything from the minor's scope moves
            // by two and `x` is `#1`.
            let up = |e: &E| shift(e, 0, 2);
            let mut mix: Vec<E> = Vec::with_capacity(n);
            for k in 0..n {
                mix.push(if k < j {
                    up(&rhs[k])
                } else if k == j {
                    bvar(1)
                } else {
                    up(&lhs[k])
                });
            }
            let body = self.eq.at(self.u, &up(goal_ty), &up(&start), &rebuild(&mix, 2));
            let eqn =
                self.eq.at(self.u, &shift(alpha, 0, 1), &shift(&lhs[j], 0, 1), &bvar(0));
            let motive = lam(alpha.clone(), lam(eqn, body));
            acc = self.eq.rec_at(self.u, alpha, &lhs[j], &motive, &acc, &rhs[j], p);
        }
        Ok(acc)
    }
}

// ────────────────────────────────────────────────────────── ι rules ──

/// **One ι rule of `T._model.rec_k`, under construction.**
///
/// The theorem's binder telescope is the recursor's own — `p⃗ M⃗ S⃗` — with the
/// constructor's **export-side** fields on the end, so a rule of `rec_1` binds
/// `List Tree`'s fields and not the mimic's. Everything below is written at an
/// explicit depth for the reason [`crate::nested_ev`]'s header gives; the two
/// depths that occur are the telescope's own and two deeper, inside a motive.
///
/// # The statement, and where the right-hand side comes from
///
/// The rule `Bₖ.rec` obeys is `minor f⃗ ih⃗`, one induction hypothesis per field
/// at a member. This builds that from the block's constructor rather than from
/// the recursor's rule list, because the field *types* it binds are the
/// export's; `mini/tests/nested.rs` compares the result against the rule the
/// installed `T.rec_k` carries, which is the same equation read the other way
/// round.
///
/// # The proof
///
/// A constructor with no packed field is `Eq.refl`: `pack`/`unpack` do not
/// appear, the block's ι rule fires, and the two sides are the same term.
///
/// Otherwise it is a **fold**, one `Eq.rec` per packed position, on
/// `unpackPackᵢ f` at a motive holding both sides in their *reduced* form —
/// the recursor already unfolded, so the kernel converts that against the
/// declared statement instead of this module reducing it by hand. At each step
/// the position moves twice over: the field value from `unpackᵢ (packᵢ f)` to
/// `f`, **and** the induction hypothesis for it from `Bₘ.rec … (packᵢ f)` to
/// `T._model.rec_m … f`, which is that term transported. `nested_deep.lean`'s
/// `M₀.cons : M₁ → M₀ → M₀` is the only constructor in the directory with two
/// packed positions, and it is why this is a fold and not one transport.
///
/// The proofs the fold needs are not the ones the reduct carries, and cannot
/// be: abstracting `f` leaves `packUnpackᵢ (packᵢ f)` at the wrong type. At the
/// root the substitute is [`Gen::congr_pack_decl`]; at a mimic it is the
/// congruence of the container's own constructor, built inline by
/// [`Gen::fold_congr`] because it has to move a different position at each step
/// of the same fold. **Proof irrelevance closes the difference** — the two are
/// proofs of one `Prop` — which is the triangle identity not being proved,
/// exactly as `mini/tests/fixtures/nested_model.lean`'s header says.
struct Rule<'g, 'a> {
    g: &'g Gen<'a>,
    /// The member being eliminated.
    k: usize,
    /// The motive universe.
    v: Level,
    nm: usize,
    nmin: usize,
    /// `np + nm + nmin`, the depth the shared telescope ends at.
    d0: u32,
    /// This constructor's minor, in the block-wide order.
    minor_ix: usize,
    /// The export-side constructor, as it is applied.
    head: Head,
    /// Its field types, each at depth `np + x`.
    ext: Vec<E>,
    /// The block constructor's name, and its field types at depth `np + x`.
    bcn: Name,
    blk: Vec<E>,
    /// Which block member each field sits at, if any.
    mem: Vec<Option<usize>>,
    /// The fields at a **mimic**, in order — the positions the fold moves.
    moving: Vec<usize>,
}

impl Rule<'_, '_> {
    fn np(&self) -> u32 { self.g.np }

    fn n(&self) -> usize { self.ext.len() }

    /// The depth of the theorem's own body.
    fn depth(&self) -> u32 { self.d0 + self.n() as u32 }

    fn motive(&self, j: usize, d: u32) -> E { bvar(d - 1 - (self.np() + j as u32)) }

    fn minor(&self, t: usize, d: u32) -> E {
        bvar(d - 1 - (self.np() + self.nm as u32 + t as u32))
    }

    fn field(&self, x: usize, d: u32) -> E { bvar(d - 1 - (self.d0 + x as u32)) }

    /// The export-side constructor applied to `vals`, at depth `d`.
    fn build(&self, vals: &[E], d: u32) -> E {
        match &self.head {
            Head::Model(n) => {
                let mut a = self.g.ps(d);
                a.extend_from_slice(vals);
                app_n(konst(n.clone(), Rc::clone(self.g.no)), &a)
            }
            Head::Real(n, ls, qs) => {
                // The occurrence's arguments are stored at the block's own
                // telescope depth, like every other occurrence in this module.
                let mut a: Vec<E> = qs.iter().map(|q| shift(q, 0, d - self.np())).collect();
                a.extend_from_slice(vals);
                app_n(konst(n.clone(), Rc::clone(ls)), &a)
            }
        }
    }

    /// `T._model.rec_m p⃗ M⃗ S⃗ x` at depth `d`.
    fn rec_call(&self, m: usize, x: &E, d: u32) -> E {
        let mut a = self.g.ps(d);
        a.extend((0..self.nm).map(|j| self.motive(j, d)));
        a.extend((0..self.nmin).map(|t| self.minor(t, d)));
        a.push(x.clone());
        app_n(konst(self.g.rec_name(m), vec![self.v.clone()].into()), &a)
    }

    /// `p⃗ M''⃗ S''⃗` at depth `d` — everything a block recursor takes before
    /// its major. Built once per use of [`Rule::sides`] because the induction
    /// hypothesis at every packed position needs it and it is the largest term
    /// in the proof.
    fn blk_prefix(&self, d: u32) -> R<Vec<E>> {
        let motive = |j: usize| self.motive(j, d);
        let minor = |t: usize| self.minor(t, d);
        let mut a = self.g.ps(d);
        a.extend(self.g.block_motives(d, &motive));
        a.extend(self.g.block_minors(d, &motive, &minor, &self.v)?);
        Ok(a)
    }

    /// `congrPack_o p⃗ l₀ l h` at depth `d`.
    fn congr_pack(&self, o: usize, l0: &E, l: &E, h: &E, d: u32) -> E {
        let mut a = self.g.ps(d);
        a.extend_from_slice(&[l0.clone(), l.clone(), h.clone()]);
        app_n(konst(self.g.congr_pack_name(o), Rc::clone(self.g.no)), &a)
    }

    /// **The two sides at depth `d`, at one stage of the fold** — the type they
    /// live at, the left, and the right.
    ///
    /// The left is the *reduced* left: the recursor unfolded, the block's ι
    /// rule fired and the minor β-reduced, which at the root is a chain of
    /// transports over `pack` and at a mimic is one transport of the whole
    /// constructor application. The right is the rule, with each moved
    /// position's induction hypothesis at `T._model.rec_m`.
    fn sides(&self, d: u32, mv: &[Move]) -> R<(E, E, E)> {
        let u = self.g.u;
        let blk = if self.moving.is_empty() { Vec::new() } else { self.blk_prefix(d)? };
        // Per field: its value and induction hypothesis at the **source**, where
        // the reduced left-hand side leaves it, and at this stage.
        let mut src_vals: Vec<E> = Vec::with_capacity(self.n());
        let mut src_ihs: Vec<E> = Vec::new();
        let mut vals: Vec<E> = Vec::with_capacity(self.n());
        let mut ihs: Vec<E> = Vec::new();
        for (x, at) in self.mem.iter().enumerate() {
            let f = self.field(x, d);
            match *at {
                None => {
                    src_vals.push(f.clone());
                    vals.push(f);
                }
                // A field at the **root** does not move: `pack` passes it
                // through, so both sides hold it at `f` and its hypothesis is
                // `T._model.rec_0` on the nose.
                Some(0) => {
                    let ih = self.rec_call(0, &f, d);
                    src_vals.push(f.clone());
                    src_ihs.push(ih.clone());
                    vals.push(f);
                    ihs.push(ih);
                }
                Some(m) => {
                    let o = m - 1;
                    let (pack, unpack, ..) = self.g.names(o);
                    let pk = self.g.call(&pack, d, f.clone());
                    let y = self.g.call(&unpack, d, pk.clone());
                    let w = {
                        let mut a = blk.clone();
                        a.push(pk);
                        app_n(
                            konst(
                                Name::str(&self.g.b[m].name, "rec"),
                                vec![self.v.clone()].into(),
                            ),
                            &a,
                        )
                    };
                    src_vals.push(y.clone());
                    src_ihs.push(w.clone());
                    match mv[x] {
                        Move::Source => {
                            vals.push(y);
                            ihs.push(w);
                        }
                        // Already moved: the value is the field and the
                        // hypothesis is `T._model.rec_m` at it, which δ-unfolds
                        // to exactly the transport the step below produced.
                        // Writing that unfolding out instead was measured — it
                        // is 2 % more expression nodes and the same wall clock.
                        Move::Target => {
                            vals.push(f.clone());
                            ihs.push(self.rec_call(m, &f, d));
                        }
                        // Being moved: the value is the motive's own `#1` and
                        // the transport is along its `#0`. At `#1 := y` and
                        // `#0 := Eq.refl` this ι-reduces back to `w`, which is
                        // what makes the previous stage the base of this step.
                        Move::Abstract => {
                            let occ = self.g.occ_at(o, d);
                            let mot = lam(
                                occ.clone(),
                                lam(
                                    self.g.eq.at(
                                        u,
                                        &self.g.occ_at(o, d + 1),
                                        &shift(&y, 0, 1),
                                        &bvar(0),
                                    ),
                                    crate::expr::app(shift(&self.motive(m, d), 0, 2), bvar(1)),
                                ),
                            );
                            ihs.push(self.g.eq.rec_at_lvl(
                                &self.v,
                                u,
                                &occ,
                                &y,
                                &mot,
                                &w,
                                &bvar(1),
                                &bvar(0),
                            ));
                            vals.push(bvar(1));
                        }
                    }
                }
            }
        }
        let apply = |vs: &[E], is: &[E]| {
            let mut a = vs.to_vec();
            a.extend_from_slice(is);
            app_n(self.minor(self.minor_ix, d), &a)
        };
        let base = apply(&src_vals, &src_ihs);
        let rhs = apply(&vals, &ihs);
        let ty = crate::expr::app(self.motive(self.k, d), self.build(&vals, d));

        let lhs = if self.k == 0 {
            // The root's minor lands at `M₀ (T._model.ctor_j f⃗)`, which unfolds
            // to `M₀ (B₀.c (pack (unpack f⃗)))`, and the block hands it
            // `M₀ (B₀.c f⃗)`. One transport per packed field, over `pack`.
            let mut bl_lhs: Vec<E> = Vec::with_capacity(self.n());
            let mut bl_rhs: Vec<E> = Vec::with_capacity(self.n());
            let mut proofs: Vec<Option<E>> = Vec::with_capacity(self.n());
            for x in 0..self.n() {
                match self.mem[x] {
                    Some(m) if m > 0 => {
                        let o = m - 1;
                        let (pack, _, retract, _) = self.g.names(o);
                        bl_lhs.push(self.g.call(&pack, d, src_vals[x].clone()));
                        bl_rhs.push(self.g.call(&pack, d, vals[x].clone()));
                        proofs.push(match mv[x] {
                            Move::Source => None,
                            Move::Target => {
                                let h = self.g.call(&retract, d, self.field(x, d));
                                Some(self.congr_pack(o, &src_vals[x], &vals[x], &h, d))
                            }
                            Move::Abstract => {
                                Some(self.congr_pack(o, &src_vals[x], &bvar(1), &bvar(0), d))
                            }
                        });
                    }
                    _ => {
                        bl_lhs.push(vals[x].clone());
                        bl_rhs.push(vals[x].clone());
                        proofs.push(None);
                    }
                }
            }
            let ftys = self.g.fields_at(&self.blk, d);
            let g = self.g;
            let bcn = self.bcn.clone();
            let rebuild = move |a: &[E], extra: u32| g.block_ctor(0, &bcn, d + extra, a);
            self.g.fold_value(
                &self.v,
                &self.motive(0, d),
                &ftys,
                &bl_lhs,
                &bl_rhs,
                &proofs,
                &rebuild,
                base,
            )?
        } else {
            // A mimic's rule transports the **whole** constructor application:
            // `recₖ` runs at `packᵢ (c f⃗)` and comes back along
            // `unpackPackᵢ (c f⃗)`, whose reduct is the congruence of `c` over
            // the packed positions. So the fold is inside the proof, and the
            // transport outside it is one `Eq.rec`.
            let i = self.k - 1;
            let occ = self.g.occ_at(i, d);
            let a0 = self.build(&src_vals, d);
            let b0 = self.build(&vals, d);
            let proofs: Vec<Option<E>> = (0..self.n())
                .map(|x| match self.mem[x] {
                    Some(m) if m > 0 => match mv[x] {
                        Move::Source => None,
                        Move::Target => {
                            Some(self.g.call(&self.g.names(m - 1).2, d, self.field(x, d)))
                        }
                        Move::Abstract => Some(bvar(0)),
                    },
                    _ => None,
                })
                .collect();
            let ftys = self.g.fields_at(&self.ext, d);
            let rebuild = |a: &[E], extra: u32| self.build(a, d + extra);
            let p = self.g.fold_congr(&occ, &ftys, &src_vals, &vals, &proofs, &rebuild)?;
            let mot = lam(
                occ.clone(),
                lam(
                    self.g.eq.at(u, &self.g.occ_at(i, d + 1), &shift(&a0, 0, 1), &bvar(0)),
                    crate::expr::app(shift(&self.motive(self.k, d), 0, 2), bvar(1)),
                ),
            );
            self.g.eq.rec_at_lvl(&self.v, u, &occ, &a0, &mot, &base, &b0, &p)
        };
        Ok((ty, lhs, rhs))
    }

    /// **The equation**: `Eq (recₖ p⃗ M⃗ S⃗ (c f⃗)) (Sⱼ f⃗ ih⃗)`, at the recursor's
    /// own motive universe.
    ///
    /// Free of the fold: the right-hand side is the rule `Bₖ.rec` obeys, one
    /// induction hypothesis per field at a member and each of them the model's
    /// **constant** `T._model.rec_m` rather than its unfolding, because that is
    /// what the export's own rule says and what the keying will read.
    fn statement(&self) -> R<E> {
        let d = self.depth();
        let all: Vec<E> = (0..self.n()).map(|x| self.field(x, d)).collect();
        let mut args = all.clone();
        for (at, f) in self.mem.iter().zip(all.iter()) {
            if let Some(m) = *at {
                args.push(self.rec_call(m, f, d));
            }
        }
        let major = self.build(&all, d);
        let ty = crate::expr::app(self.motive(self.k, d), major.clone());
        let lhs = self.rec_call(self.k, &major, d);
        let rhs = app_n(self.minor(self.minor_ix, d), &args);
        Ok(self.g.eq.at(&self.v, &ty, &lhs, &rhs))
    }

    /// The proof: `Eq.refl` with nothing to move, and otherwise one `Eq.rec` on
    /// `unpackPackᵢ f` per packed position, from a base where every one of them
    /// is still at the source and both sides are the same term.
    fn value(&self) -> R<E> {
        let d = self.depth();
        let mut mv = vec![Move::Source; self.n()];
        let (ty0, _, rhs0) = self.sides(d, &mv)?;
        let mut acc = self.g.eq.refl_at(&self.v, &ty0, &rhs0);
        for &x in &self.moving {
            let m = self.mem[x].ok_or(Reason::Malformed)?;
            let o = m - 1;
            let (pack, unpack, retract, _) = self.g.names(o);
            let f = self.field(x, d);
            let y = self.g.call(&unpack, d, self.g.call(&pack, d, f.clone()));
            let h = self.g.call(&retract, d, f.clone());
            let mut mv2 = mv.clone();
            mv2[x] = Move::Abstract;
            // The motive is the whole equation with this position abstracted;
            // at `#1 := unpackᵢ (packᵢ f)` and `#0 := Eq.refl` every transport
            // it introduced ι-reduces away and what is left is the accumulator's
            // own type.
            let (ty2, l2, r2) = self.sides(d + 2, &mv2)?;
            let occ = self.g.occ_at(o, d);
            let mot = lam(
                occ.clone(),
                lam(
                    self.g.eq.at(self.g.u, &self.g.occ_at(o, d + 1), &shift(&y, 0, 1), &bvar(0)),
                    self.g.eq.at(&self.v, &ty2, &l2, &r2),
                ),
            );
            acc = self.g.eq.rec_at(self.g.u, &occ, &y, &mot, &acc, &f, &h);
            mv[x] = Move::Target;
        }
        Ok(acc)
    }
}

// ─────────────────────────────────────────────────── syntax helpers ──

fn lams(tys: &[E], body: E) -> E { tys.iter().rev().fold(body, |b, t| lam(t.clone(), b)) }

fn foralls(tys: &[E], body: E) -> E { tys.iter().rev().fold(body, |b, t| forall(t.clone(), b)) }
