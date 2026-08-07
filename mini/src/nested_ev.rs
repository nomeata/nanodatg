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
//!
//! Every decline names a shape rather than a failure, and each has a fixture
//! that exhibits it, so none of them is a defensive guess:
//!
//! * [`Reason::Parameterised`] — the declaration has parameters of its own.
//!   `nested_iota.lean`'s `PT (α) : List (PT α)`. Everything below is written at
//!   an empty parameter telescope; the generalisation is a `p⃗` prefix on every
//!   declaration and a shift on every occurrence, and it is not done here.
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
//!   fabricate an `Eq` Lean never wrote.
//! * [`Reason::NameTaken`] — a name under `T._model` is already declared.

use std::collections::HashMap;
use std::rc::Rc;

use crate::env::{ConstantInfo, DefKind, Declaration, Environment, IndType};
use crate::env::instantiate_lparams;
use crate::expr::{app_n, bvar, forall, get_app, konst, lam, substs, Expr, Level, Name, E};
use crate::nested::Plan;

/// Why a nested declaration's isomorphism could not be built. Each is a shape.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// The declaration has parameters of its own.
    Parameterised,
    /// The declaration, or a container it nests into, has indices.
    Indexed,
    /// A constructor field's type mentions an earlier field.
    DependentFields,
    /// No `Eq`, or an `Eq` whose recursor is not the shape the round trips need.
    NoEq,
    /// A name under `T._model` is already declared.
    NameTaken,
    /// A shape `kernel::add` would already have rejected — a member whose type
    /// is not a sort, a constructor that is not a `Π`-telescope at a member.
    Malformed,
}

impl Reason {
    /// The word that reaches a `waiting:` row, as `ind-spec(T: nested model …)`.
    pub fn label(self) -> &'static str {
        match self {
            Reason::Parameterised => "nested model with parameters",
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
    if num_params != 0 || !lparams.is_empty() {
        return Err(Reason::Parameterised)
    }
    let root = types.first().ok_or(Reason::Malformed)?.name.clone();
    // The block's resultant sort, which every member and every occurrence lives
    // at. Read off member 0's own type; anything but a bare sort is an index
    // telescope this module does not write.
    let Expr::Sort(u) = &*plan.types[0].ty else { return Err(Reason::Indexed) };
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
    let no = Rc::from(Vec::new());

    // ── 1. the block, renamed ────────────────────────────────────────────
    //
    // Member 0 is the export's own `T` and must not keep that name: `T` is a
    // primitive inductive in the caller's environment and this is a definition
    // over a different constant. Every member is renamed for uniformity.
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
        Declaration::Mutual { lparams: Vec::new(), num_params: 0, types: block.clone() };
    crate::kernel::add(&mut scratch, &block_decl).map_err(|_| Reason::Malformed)?;
    out.push(block_decl);

    // ── 2. the carrier ───────────────────────────────────────────────────
    let self_decl = Declaration::Def {
        name: self_name.clone(),
        lparams: Vec::new(),
        ty: plan.types[0].ty.clone(),
        value: konst(b(0), Rc::clone(&no)),
        kind: DefKind::Def,
    };
    crate::kernel::add(&mut scratch, &self_decl).map_err(|_| Reason::Malformed)?;
    out.push(self_decl);

    // Every occurrence, with the export's `T` rewritten to the model's carrier.
    let to_self: HashMap<Name, (u32, E)> =
        [(root.clone(), (0u32, konst(self_name.clone(), Rc::clone(&no))))].into_iter().collect();
    let occs: Vec<E> =
        plan.mimics.iter().map(|m| crate::nested::restore(&to_self, &m.occ)).collect();

    // ── 3. pack, unpack, and the two round trips, per mimic ──────────────
    //
    // `pack_i` may mention `pack_m` for a *deeper* mimic `m`, which discovery
    // order puts later, so the emission order is discovery order reversed. A
    // mimic graph with a cycle cannot arise — nesting strictly decreases — and
    // if one did, the `kernel::add` below would reject the forward reference.
    let g = Gen {
        env: scratch.clone(),
        b: &block,
        u: &u,
        eq: &eq,
        occs: &occs,
        model: &model,
        no: &no,
    };
    let mut maps = Vec::new();
    // Deeper mimics first: `pack_i` for a container whose field is another
    // occurrence calls that occurrence's `pack`, and discovery order puts the
    // deeper one later. Nesting strictly decreases, so this is a topological
    // order and a cycle cannot arise.
    let mut done = vec![false; plan.mimics.len()];
    let order: Vec<usize> = (0..plan.mimics.len()).rev().collect();
    for &i in &order {
        let member = i + 1; // mimics are members 1..
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

    Ok(Iso {
        decls: out,
        env: scratch,
        self_name,
        members: (0..plan.types.len()).map(b).collect(),
        maps,
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

/// The generator's read-only context.
struct Gen<'a> {
    env: Environment,
    b: &'a [IndType],
    u: &'a Level,
    eq: &'a Eq,
    occs: &'a [E],
    model: &'a Name,
    no: &'a Rc<[Level]>,
}

/// One constructor, peeled: its field types (each in scope of the earlier
/// fields) and the head constant.
struct Ctor {
    name: Name,
    fields: Vec<E>,
}

impl Gen<'_> {
    fn names(&self, i: usize) -> (Name, Name, Name, Name) {
        let s = |w: &str| Name::str(self.model, &format!("{w}_{i}"));
        (s("pack"), s("unpack"), s("unpackPack"), s("packUnpack"))
    }

    fn member(&self, i: usize) -> E { konst(self.b[i].name.clone(), Rc::clone(self.no)) }

    /// A constructor's type at the occurrence's levels and parameters: its
    /// universe parameters instantiated, then its `np` parameter binders peeled
    /// and substituted, leaving the field telescope.
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

    /// Peel a constructor's field telescope, checking no field type mentions an
    /// earlier field — the condition the congruence fold below needs.
    fn peel_ctor(&self, name: &Name, ty: &E) -> R<Ctor> {
        let mut fields = Vec::new();
        let mut cur = ty.clone();
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

    /// The four declarations of one mimic.
    fn four(
        &self,
        i: usize,
        member: usize,
        names: &(Name, Name, Name, Name),
        done: &[bool],
    ) -> R<Vec<Declaration>> {
        let (pack, unpack, retract, section) = names;
        let occ = &self.occs[i];
        let bi = self.member(member);
        let def = |name: &Name, ty: E, value: E, kind| Declaration::Def {
            name: name.clone(),
            lparams: Vec::new(),
            ty,
            value,
            kind,
        };
        Ok(vec![
            def(pack, forall(occ.clone(), bi.clone()), self.pack_value(i, member)?, DefKind::Def),
            def(
                unpack,
                forall(bi.clone(), shift1(occ)),
                self.unpack_value(member)?,
                DefKind::Def,
            ),
            def(
                retract,
                forall(
                    occ.clone(),
                    self.eq.at(
                        self.u,
                        &shift1(occ),
                        &app1(unpack, &app1(pack, &bvar(0))),
                        &bvar(0),
                    ),
                ),
                self.retract_value(i, member, names)?,
                DefKind::Theorem,
            ),
            def(
                section,
                forall(
                    bi.clone(),
                    self.eq.at(self.u, &bi, &app1(pack, &app1(unpack, &bvar(0))), &bvar(0)),
                ),
                self.section_value(i, member, done)?,
                DefKind::Theorem,
            ),
        ])
    }

    /// `pack_i := C.rec q⃗ (fun _ => Bᵢ) minors…`, partially applied — its type
    /// is `∀ _ : occᵢ, Bᵢ` on the nose, because the motive is constant.
    fn pack_value(&self, i: usize, member: usize) -> R<E> {
        let occ = &self.occs[i];
        let (head, qs) = get_app(occ);
        let Expr::Const(c, cls) = &*head else { return Err(Reason::Malformed) };
        let ConstantInfo::Inductive { num_indices, ctors, .. } =
            self.env.get(c).ok_or(Reason::Malformed)?
        else {
            return Err(Reason::Malformed)
        };
        if *num_indices != 0 {
            return Err(Reason::Indexed)
        }
        let bi = self.member(member);
        let motive = lam(occ.clone(), shift1(&bi));
        let mut args = qs.clone();
        args.push(motive);
        for (j, cn) in ctors.iter().enumerate() {
            args.push(self.pack_minor(i, member, c, cls, &qs, cn, j)?);
        }
        Ok(app_n(konst(Name::str(c, "rec"), self.rec_levels(c)?), &args))
    }

    /// The motive universe goes in front of the container's own level list —
    /// the order `kernel::add` mints a recursor's parameters in.
    fn rec_levels(&self, c: &Name) -> R<Rc<[Level]>> {
        let ci = self.env.get(c).ok_or(Reason::Malformed)?;
        let mut ls = vec![self.u.clone()];
        ls.extend(ci.lparams().iter().map(|p| Level::Param(p.clone())));
        Ok(ls.into())
    }

    /// `fun f⃗ ih⃗ => Bᵢ.c g⃗`, where a field recursive in the container is its
    /// own induction hypothesis, a field at another mimic is packed, and
    /// anything else — a plain field, or a field at the root, which the block
    /// types at `B₀` and `T._model.self` unfolds to — goes through untouched.
    #[allow(clippy::too_many_arguments)]
    fn pack_minor(
        &self,
        i: usize,
        member: usize,
        _c: &Name,
        cls: &Rc<[Level]>,
        qs: &[E],
        cn: &Name,
        _j: usize,
    ) -> R<E> {
        let cty = self.inst_ctor(cn, cls, qs)?;
        let ct = self.peel_ctor(cn, &cty)?;
        let occ = &self.occs[i];
        let recs: Vec<usize> =
            (0..ct.fields.len()).filter(|&k| ct.fields[k] == *occ).collect();
        let n = ct.fields.len();
        let m = recs.len();
        let depth = (n + m) as u32;
        let field = |k: usize| bvar(depth - 1 - k as u32);
        let ih = |t: usize| bvar((m - 1 - t) as u32);
        let mut args = Vec::with_capacity(n);
        for k in 0..n {
            if let Some(t) = recs.iter().position(|&r| r == k) {
                args.push(ih(t));
            } else if let Some(other) = self.occs.iter().position(|o| *o == ct.fields[k]) {
                args.push(app1(&self.names(other).0, &field(k)));
            } else {
                args.push(field(k));
            }
        }
        let body = app_n(
            konst(rename_ctor(&self.b[member].name, &ct.name), Rc::clone(self.no)),
            &args,
        );
        // Binder types: the fields as declared, then one `Bᵢ` per recursive
        // field. A field type is in scope of the earlier fields only, which
        // `peel_ctor` has already required it not to use.
        let mut tys: Vec<E> = ct.fields.clone();
        for _ in 0..m {
            tys.push(self.member(member));
        }
        Ok(lams(&tys, body))
    }

    /// `unpack_i := Bᵢ.rec motives… minors…`, partially applied.
    fn unpack_value(&self, member: usize) -> R<E> {
        let mut args: Vec<E> = Vec::new();
        for k in 0..self.b.len() {
            let dom = self.member(k);
            let cod = if k == 0 { shift1(&self.member(0)) } else { shift1(&self.occs[k - 1]) };
            args.push(lam(dom, cod));
        }
        for k in 0..self.b.len() {
            for (cn, cty) in &self.b[k].ctors {
                args.push(self.unpack_minor(k, cn, cty)?);
            }
        }
        Ok(app_n(konst(Name::str(&self.b[member].name, "rec"), self.block_rec_levels()), &args))
    }

    fn block_rec_levels(&self) -> Rc<[Level]> { vec![self.u.clone()].into() }

    /// A member's minor for `unpack`: at the root, rebuild the constructor; at
    /// a mimic, build the **real** container's constructor, taking each field
    /// at another mimic from its induction hypothesis.
    fn unpack_minor(&self, k: usize, cn: &Name, cty: &E) -> R<E> {
        let ct = self.peel_ctor(cn, cty)?;
        // Recursive fields of a block constructor are the ones at *any* member,
        // and they are the ones the recursor supplies an induction hypothesis
        // for, in field order.
        let member_of = |t: &E| {
            let (h, a) = get_app(t);
            if !a.is_empty() {
                return None
            }
            match &*h {
                Expr::Const(n, _) => self.b.iter().position(|x| x.name == *n),
                _ => None,
            }
        };
        let recs: Vec<usize> =
            (0..ct.fields.len()).filter(|&x| member_of(&ct.fields[x]).is_some()).collect();
        let n = ct.fields.len();
        let m = recs.len();
        let depth = (n + m) as u32;
        let field = |x: usize| bvar(depth - 1 - x as u32);
        let ih = |t: usize| bvar((m - 1 - t) as u32);

        let mut args = Vec::with_capacity(n);
        for x in 0..n {
            match member_of(&ct.fields[x]) {
                // A field at a *mimic* is unpacked, and its unpacked value is
                // exactly this recursor's induction hypothesis for it.
                Some(mem) if mem > 0 => {
                    let t = recs.iter().position(|&r| r == x).ok_or(Reason::Malformed)?;
                    args.push(ih(t));
                }
                // A field at the root passes through: the block types it `B₀`
                // and the real constructor wants `T._model.self`, which is `B₀`.
                _ => args.push(field(x)),
            }
        }

        let body = if k == 0 {
            app_n(konst(ct.name.clone(), Rc::clone(self.no)), &(0..n).map(field).collect::<Vec<_>>())
        } else {
            // The mimic's real counterpart, at the occurrence's own parameters.
            let (h, qs) = get_app(&self.occs[k - 1]);
            let Expr::Const(_, cls) = &*h else { return Err(Reason::Malformed) };
            let real = self.real_ctor(k, cn)?;
            let mut a: Vec<E> = qs.iter().map(|q| shift(q, depth)).collect();
            a.extend(args);
            app_n(konst(real, Rc::clone(cls)), &a)
        };

        let mut tys: Vec<E> = ct.fields.clone();
        for &r in &recs {
            let mem = member_of(&ct.fields[r]).ok_or(Reason::Malformed)?;
            tys.push(if mem == 0 { self.member(0) } else { shift(&self.occs[mem - 1], 0) });
        }
        Ok(lams(&tys, body))
    }

    /// The real container constructor a mimic's constructor stands for, by its
    /// last name component — the correspondence [`crate::nested`] builds the
    /// mimic from in the first place.
    fn real_ctor(&self, k: usize, cn: &Name) -> R<Name> {
        let (h, _) = get_app(&self.occs[k - 1]);
        let Expr::Const(c, _) = &*h else { return Err(Reason::Malformed) };
        let Some(ConstantInfo::Inductive { ctors, .. }) = self.env.get(c) else {
            return Err(Reason::Malformed)
        };
        let last = match cn {
            Name::Str(_, s) => s.to_string(),
            other => other.to_string(),
        };
        ctors
            .iter()
            .find(|r| matches!(r, Name::Str(_, s) if **s == last))
            .cloned()
            .ok_or(Reason::Malformed)
    }

    /// `unpackPack_i : ∀ l, Eq (unpack_i (pack_i l)) l`, by the container's own
    /// recursor, one congruence per field the round trip moves.
    fn retract_value(
        &self,
        i: usize,
        _member: usize,
        names: &(Name, Name, Name, Name),
    ) -> R<E> {
        let (pack, unpack, _, _) = names;
        let occ = &self.occs[i];
        let (head, qs) = get_app(occ);
        let Expr::Const(c, cls) = &*head else { return Err(Reason::Malformed) };
        let ConstantInfo::Inductive { ctors, .. } = self.env.get(c).ok_or(Reason::Malformed)?
        else {
            return Err(Reason::Malformed)
        };
        let trip = |x: &E| app1(unpack, &app1(pack, x));
        let motive = lam(occ.clone(), self.eq.at(self.u, &shift1(occ), &trip(&bvar(0)), &bvar(0)));
        let mut args = qs.clone();
        args.push(motive);
        for cn in ctors.iter() {
            let cty = self.inst_ctor(cn, cls, &qs)?;
            let ct = self.peel_ctor(cn, &cty)?;
            let recs: Vec<usize> =
                (0..ct.fields.len()).filter(|&k| ct.fields[k] == *occ).collect();
            let n = ct.fields.len();
            let m = recs.len();
            let depth = (n + m) as u32;
            let field = |k: usize| bvar(depth - 1 - k as u32);
            let ih = |t: usize| bvar((m - 1 - t) as u32);
            // The two sides of the equation, argument by argument, and the
            // proof that each pair is equal.
            let mut lhs = Vec::with_capacity(n);
            let mut rhs = Vec::with_capacity(n);
            let mut proofs: Vec<Option<E>> = Vec::with_capacity(n);
            for k in 0..n {
                rhs.push(field(k));
                if let Some(t) = recs.iter().position(|&r| r == k) {
                    lhs.push(trip(&field(k)));
                    proofs.push(Some(ih(t)));
                } else if let Some(other) = self.occs.iter().position(|o| *o == ct.fields[k]) {
                    let on = self.names(other);
                    lhs.push(app1(&on.1, &app1(&on.0, &field(k))));
                    proofs.push(Some(app1(&on.2, &field(k))));
                } else {
                    lhs.push(field(k));
                    proofs.push(None);
                }
            }
            let cn2 = cn.clone();
            let cls2 = Rc::clone(cls);
            let qs2 = qs.clone();
            let rebuild = move |a: &[E], d: u32| {
                let mut v: Vec<E> = qs2.iter().map(|q| shift(q, depth + d)).collect();
                v.extend_from_slice(a);
                app_n(konst(cn2.clone(), Rc::clone(&cls2)), &v)
            };
            let body = self.fold_congr(&shift(occ, depth), &ct.fields, &lhs, &rhs, &proofs, &rebuild)?;
            // **The induction hypothesis is the motive at its own field**, not
            // the motive's codomain. Binder `n + t` is in scope of the `n`
            // fields and the `t` hypotheses before it, so the field it is about
            // is indexed at *that* depth and not at the body's.
            let mut tys: Vec<E> = ct.fields.clone();
            for (t, &r) in recs.iter().enumerate() {
                let d = (n + t) as u32;
                let f = bvar(d - 1 - r as u32);
                tys.push(self.eq.at(self.u, &shift(occ, d), &trip(&f), &f));
            }
            args.push(lams(&tys, body));
        }
        Ok(app_n(konst(Name::str(c, "rec"), self.eq_rec_levels(c)?), &args))
    }

    /// The container's recursor at a `Prop`-valued motive.
    fn eq_rec_levels(&self, c: &Name) -> R<Rc<[Level]>> {
        let ci = self.env.get(c).ok_or(Reason::Malformed)?;
        let mut ls = vec![Level::Zero];
        ls.extend(ci.lparams().iter().map(|p| Level::Param(p.clone())));
        Ok(ls.into())
    }

    /// `packUnpack_i : ∀ b, Eq (pack_i (unpack_i b)) b`, by the block's
    /// recursor at the round-trip motive on every mimic and reflexivity at the
    /// root.
    ///
    /// **The motive is the round trip only where the round trip exists.** A
    /// mimic this development has not reached yet has no `pack`, so its motive
    /// is reflexivity — which is all its own minors need, because a constructor
    /// whose field sits at an unreached mimic cannot occur: the emission order
    /// is topological and a field at a mimic is always at a *deeper* one.
    fn section_value(&self, i: usize, member: usize, done: &[bool]) -> R<E> {
        let live = |k: usize| k > 0 && (k - 1 == i || done[k - 1]);
        let mut args: Vec<E> = Vec::new();
        for k in 0..self.b.len() {
            let dom = self.member(k);
            let body = if live(k) {
                let nm = self.names(k - 1);
                self.eq.at(
                    self.u,
                    &shift1(&self.member(k)),
                    &app1(&nm.0, &app1(&nm.1, &bvar(0))),
                    &bvar(0),
                )
            } else {
                self.eq.at(self.u, &shift1(&self.member(k)), &bvar(0), &bvar(0))
            };
            args.push(lam(dom, body));
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

    fn section_minor(&self, k: usize, cn: &Name, cty: &E, live: &dyn Fn(usize) -> bool) -> R<E> {
        let ct = self.peel_ctor(cn, cty)?;
        let member_of = |t: &E| {
            let (h, a) = get_app(t);
            if !a.is_empty() {
                return None
            }
            match &*h {
                Expr::Const(n, _) => self.b.iter().position(|x| x.name == *n),
                _ => None,
            }
        };
        let recs: Vec<usize> =
            (0..ct.fields.len()).filter(|&x| member_of(&ct.fields[x]).is_some()).collect();
        let n = ct.fields.len();
        let m = recs.len();
        let depth = (n + m) as u32;
        let field = |x: usize| bvar(depth - 1 - x as u32);
        let ih = |t: usize| bvar((m - 1 - t) as u32);
        // The induction hypothesis is the motive *at its own field*, indexed at
        // the depth that binder is introduced at.
        let mut tys: Vec<E> = ct.fields.clone();
        for (t, &r) in recs.iter().enumerate() {
            let mem = member_of(&ct.fields[r]).ok_or(Reason::Malformed)?;
            let d = (n + t) as u32;
            let f = bvar(d - 1 - r as u32);
            tys.push(if live(mem) {
                let nm = self.names(mem - 1);
                self.eq.at(self.u, &self.member(mem), &app1(&nm.0, &app1(&nm.1, &f)), &f)
            } else {
                self.eq.at(self.u, &self.member(mem), &f, &f)
            });
        }
        // Rebuilt with the ihs is the identity on the root's constructors, and
        // one congruence per mimic field on a mimic's.
        let cname = ct.name.clone();
        let no = Rc::clone(self.no);
        let all: Vec<E> = (0..n).map(field).collect();
        let rebuild = move |a: &[E], _d: u32| app_n(konst(cname.clone(), Rc::clone(&no)), a);
        let ty = self.member(k);
        if !live(k) {
            let e = rebuild(&all, 0);
            return Ok(lams(&tys, self.eq.refl_at(self.u, &ty, &e)))
        }
        let mut lhs = Vec::with_capacity(n);
        let mut proofs: Vec<Option<E>> = Vec::with_capacity(n);
        for x in 0..n {
            match member_of(&ct.fields[x]) {
                Some(mem) if live(mem) => {
                    let t = recs.iter().position(|&r| r == x).ok_or(Reason::Malformed)?;
                    let nm = self.names(mem - 1);
                    lhs.push(app1(&nm.0, &app1(&nm.1, &field(x))));
                    proofs.push(Some(ih(t)));
                }
                _ => {
                    lhs.push(field(x));
                    proofs.push(None);
                }
            }
        }
        let body = self.fold_congr(&ty, &ct.fields, &lhs, &all, &proofs, &rebuild)?;
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
    /// `nested_shapes`' `DTree` has `cons : M₂ → M₁ → M₁`, two mimic fields in
    /// one constructor.
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
            let up = |e: &E| shift(e, 2);
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
            let eqn = self.eq.at(self.u, &shift(alpha, 1), &shift(&lhs[j], 1), &bvar(0));
            let motive = lam(alpha.clone(), lam(eqn, body));
            acc = self.eq.rec_at(self.u, alpha, &lhs[j], &motive, &acc, &rhs[j], p);
        }
        Ok(acc)
    }

}

// ─────────────────────────────────────────────────── syntax helpers ──

fn app1(f: &Name, a: &E) -> E {
    app_n(konst(f.clone(), Vec::new().into()), std::slice::from_ref(a))
}

fn lams(tys: &[E], body: E) -> E { tys.iter().rev().fold(body, |b, t| lam(t.clone(), b)) }

fn shift1(e: &E) -> E { crate::expr::shift(e, 0, 1) }

fn shift(e: &E, d: u32) -> E { crate::expr::shift(e, 0, d) }
