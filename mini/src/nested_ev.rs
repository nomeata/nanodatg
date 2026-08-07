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
//! `pack`/`unpack` pair per mimic, and **both round trips as theorems** —
//! already checked into [`Iso::env`]. Nothing is asserted that `kernel::add`
//! did not accept: a proof this module builds and the checker rejects is an
//! `Err`, never a declaration.
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
//! # The boundary
//!
//! This module is a **black box over the evidence layer**, on the same terms as
//! [`crate::mutual_aux`] and [`crate::nested`] and checked by the same rule
//! (`ci/check-mutual-blackbox.sh`): it emits Lean-world syntax, asks
//! [`crate::kernel::add`] whether it is well-formed, and reads back only zone
//! A's syntax — a `ConstantInfo`'s declared type, its constructor list, a
//! recursor's arity fields. It never names a certificate.
//!
//! # What it declines, each with a witness
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
    /// A shape `kernel::add` would already have rejected, or a proof this module
    /// built and the checker did not accept.
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
            ty,
            value: d,
            kind: DefKind::Def,
        };
        crate::kernel::add(&mut scratch, &decl).map_err(|_| Reason::Malformed)?;
        out.push(decl);
        ctors.push((cn.clone(), name));
    }

    Ok(Iso {
        decls: out,
        env: scratch,
        self_name,
        members: (0..plan.types.len()).map(b).collect(),
        maps,
        ctors,
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

    /// `Eq.rec.{0,u} α a motive base b h` — the motive is `Prop`-valued at every
    /// use here, because everything this module transports is an equation.
    #[allow(clippy::too_many_arguments)]
    fn rec_at(&self, u: &Level, a_ty: &E, a: &E, motive: &E, base: &E, bb: &E, h: &E) -> E {
        let ls: Rc<[Level]> = vec![Level::Zero, u.clone()].into();
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
    /// in one constructor, and it is the only occupant this loop has.
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

// ─────────────────────────────────────────────────── syntax helpers ──

fn lams(tys: &[E], body: E) -> E { tys.iter().rev().fold(body, |b, t| lam(t.clone(), b)) }

fn foralls(tys: &[E], body: E) -> E { tys.iter().rev().fold(body, |b, t| forall(t.clone(), b)) }
