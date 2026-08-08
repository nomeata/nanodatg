//! **Step 3–5 of the mutual arc: a `mutual … end` block as one aux inductive,
//! its members as ordinary definitions over it, and its recursor rules as
//! ordinary theorems.**
//!
//! # Interface
//!
//! ```text
//! mutual_aux::encode(env, &Declaration::Mutual { .. }) -> Result<Encoding, Reason>
//! ```
//!
//! [`Encoding::decls`] is a list of ordinary [`Declaration`]s in dependency
//! order — a tag inductive `Tag`, one indexed inductive `Aux`, one `def` per
//! member, one `def` per constructor, a packed motive, one `def` per recursor,
//! and one `theorem` per recursor rule proved by reflexivity.
//! [`Encoding::env`] is a temporary environment in which all of them have been
//! checked. Nothing else happens here: the caller feeds the list to the
//! ordinary evidence-producing pipeline, and what comes back is a TG term and a
//! typing proof for every constant of the block, under the block's own names.
//!
//! # The black box, and why it is a property of this file
//!
//! **This module never names a `Term`, a `Thm`, an `Ev` or an `Interp`.** It
//! moves `mini::Expr`s around and calls `kernel::add`, whose output is
//! accept-or-reject and a syntactic environment. Whether the encoding is
//! *right* is not decided here and cannot be: it is decided by the checker
//! accepting the reflexivity proofs, and by the interpretation the checker
//! produces for them. `ci/check-mutual-blackbox.sh` is that claim as a grep,
//! and the reason this is a file of its own rather than a section of
//! `zoneb.rs` or `kernel.rs` — at file granularity the check is writable, at
//! function granularity it is not.
//!
//! # The encoding
//!
//! For a block `T₀ … T_{n-1}` sharing a parameter telescope `p⃗` and a
//! resultant sort `Sort u`, where member `i` carries its own index telescope
//! `ix⃗ᵢ`:
//!
//! ```text
//! inductive Tag (p⃗)         : Sort W            -- Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗
//! inductive Aux (p⃗)         : Tag p⃗ → Sort u    -- every constructor of every member
//! def Tᵢ                    : ∀p⃗ ix⃗ᵢ, Sort u    := fun p⃗ ix⃗ᵢ => Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ)
//! def Tᵢ.ctorⱼ              : <its own type>    := fun p⃗ f⃗ => Aux.cᵢⱼ p⃗ f⃗
//! def Mot                   : …                 := fun p⃗ m⃗ => Tag.rec p⃗ (fun t => Aux p⃗ t → Sort v) m⃗
//! def Tᵢ.rec                : <zone A's type>   := fun p⃗ m⃗ k⃗ ix⃗ᵢ t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ (Tag.tᵢ p⃗ ix⃗ᵢ) t
//! theorem Tᵢ.rec._auxRuleⱼ  : <zone A's rule>   := Eq.refl _
//! ```
//!
//! Four things make it work, and each is load-bearing:
//!
//! * **`Tag` is an index of `Aux`, not a parameter.** It has to vary from
//!   constructor to constructor, which is what a parameter may not do.
//! * **The members' indices are inside the tag, so `Aux` has exactly one
//!   index.** Each `Tag` constructor carries *its own* member's telescope as
//!   fields, so the members are not required to agree on anything — the way
//!   they are required to agree on their parameters and their resultant sort,
//!   which the kernel checks and this encoding then relies on. A block whose
//!   members are unindexed is the case where every tag constructor is nullary;
//!   there is one path and nothing branches on the telescopes.
//! * **The minors are passed through untouched.** `Aux.rec`'s minor for `cᵢⱼ`
//!   wants `Mot p⃗ m⃗ (Tag.tᵢ p⃗ idx⃗) (Aux.cᵢⱼ p⃗ f⃗)`, and the minor in hand has
//!   type `mᵢ idx⃗ (Tᵢ.ctorⱼ p⃗ f⃗)`. Those are δι-equal — `Mot … (Tag.tᵢ p⃗ idx⃗)`
//!   reduces to `mᵢ idx⃗` by `Tag`'s own ι rule and `Tᵢ.ctorⱼ` unfolds to
//!   `Aux.cᵢⱼ` by δ — so no transport is built and none is needed. `Tag.rec`'s
//!   minor for `Tag.tᵢ` is `∀ix⃗ᵢ, Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ) → Sort v` and `mᵢ` is
//!   `∀ix⃗ᵢ, Tᵢ p⃗ ix⃗ᵢ → Sort v`, δ-equal without an η wrapper, which is why the
//!   packed motive hands `Tag.rec` the motives themselves.
//! * **Every `Tᵢ.rec` hands `Aux.rec` the same motive and the same minors**,
//!   differing only in the tag. That is why the induction hypothesis a rule
//!   produces, `Aux.rec … (Tag.t_k p⃗ idx⃗) …`, is *literally* what `T_k.rec …`
//!   unfolds to, and why the rule theorems are reflexivity rather than a
//!   transport. It holds across telescopes: `MA.mk : MB → MA N.z` builds at
//!   arity 1 and its ih is at `MB`'s arity 0.
//!
//! The statements are not invented here either. A recursor's declared type and
//! a rule's right-hand side are read from **zone A's own output** — the
//! `ConstantInfo::Recursor` `kernel::add_block` already put in the environment
//! — so what the theorems say is what the kernel already believes, and this
//! module only supplies the proofs.
//!
//! # The one number that is not syntax
//!
//! It is **`W`, the sort `Tag` is declared at**. `Tag`'s constructors carry the
//! members' index *values* as fields, so the kernel checks `sⱼ ≤ W` for every
//! index type's own sort `sⱼ` — and an index of type `N` is at `Sort 1` only
//! because `N`'s declaration says so. So the encoder asks the checker,
//! `kernel::sort_under`, whose entire output is a `Level`. Asking the checker a
//! question is not the boundary; reading its certificates is, and
//! `ci/check-mutual-blackbox.sh` licenses exactly two entry points by name.
//!
//! ```text
//! W = max(1, s₁ … s_k)     over EVERY member's index types
//! ```
//!
//! The `1` is not padding: `Tag.rec` has to eliminate into `Sort (max u (v+1))`
//! and a `Prop`-valued `Tag` could not. A block with no indices gets `Sort 1`
//! on the nose, which is the `Type` this was when `Tag` was an enumeration.
//!
//! **It is an over-approximation and does not need to be exact.** Nothing
//! constrains an index type's sort from above, so any `W` above the index sorts
//! is accepted; `sort_under` is handed `∀ix₁…ix_{j-1}, Iⱼ`, whose sort is the
//! `imax` of the earlier ones with `sⱼ` — above `sⱼ`, and below the `max` being
//! built because every earlier `sᵢ` is in that `max` too. Asking for `Iⱼ` alone
//! would need the earlier indices in scope, which is the same telescope.
//!
//! The cheap guess is `W = 1`, and it is right on every fixture but one: a
//! constructor that binds an index as a field forces `sⱼ ≤ u` by
//! `checkCtorParam`, and a `Prop`-valued family's indices are usually `N`. The
//! escape is a **`Prop`-valued family indexed by a large type** — no universe
//! constraint on the fields, and an index at `Type 1`, whose sort is `Sort 3`.
//! `mutual_index_sorts`' `SA`/`SB`/`SC` is that, and it is the only fixture
//! where `W` is not `1`.
//!
//! *What used to be here was the level `Tag.rec` runs at, `max(s⃗, u, v+1)`,
//! because the packed motive had the shared index telescope in front of it.
//! It does not any more — the indices are in the tag — so that level is the
//! purely syntactic `max(u, v+1)`, the `imax` a `Π` carries collapsing because
//! `v+1` is never zero. The index sorts did not stop mattering; they moved.*
//!
//! Rule theorems additionally need an `Eq` in the environment. A `prelude`
//! export that never mentions equality has none, and this module does not
//! fabricate one: the whole point is that everything downstream is a Lean term
//! the checker already knows how to interpret, and an `Eq` that mini minted
//! would be a declaration Lean never wrote. Such a block gets its encoding and
//! its recursors and no rule theorems, and [`Encoding::rules`] says how many it
//! got.

use std::rc::Rc;

use crate::env::{ConstantInfo, DefKind, Declaration, Environment};
use crate::expr::{app_n, bvar, bvars, forall, konst, lam, shift, sort, Expr, Level, Name, E, NameView};

/// Why a block could not be encoded. Each is a shape, not a failure.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// Not a `mutual … end` block at all.
    NotABlock,
    /// A member's type does not end in a sort after its parameters, or a
    /// constructor is not a `Π`-telescope ending at a member — shapes
    /// `kernel::add_block` would already have rejected.
    Malformed,
    /// A member's recursor is not in the environment, or is not the shape zone
    /// A builds. `encode` reads the statements from there rather than
    /// recomputing them.
    NoRecursor,
    /// The name the encoding wants for its `Tag`, `Aux` or `Mot` is taken.
    NameTaken,
}

impl Reason {
    /// The word that reaches the `waiting:` row, as `ind-spec(T: mutual …)`.
    pub fn label(self) -> &'static str {
        match self {
            Reason::NotABlock => "mutual",
            Reason::Malformed => "mutual block shape",
            Reason::NoRecursor => "mutual block recursor",
            Reason::NameTaken => "mutual aux name taken",
        }
    }
}

/// The encoding of one block.
pub struct Encoding {
    /// Every generated declaration, in dependency order and already checked
    /// into [`Encoding::env`].
    pub decls: Vec<Declaration>,
    /// A temporary environment: the caller's, with the block's own constants
    /// removed and the encoding added in their place.
    pub env: Environment,
    /// The auxiliary tag enumeration.
    pub tag: Name,
    /// The auxiliary carrier.
    pub aux: Name,
    /// How many recursor rules were stated as theorems. Zero when the
    /// environment has no `Eq`.
    pub rules: usize,
}

impl Encoding {
    /// Every name this encoding brings into being: the declarations
    /// themselves, and — for the two inductives — the constructors and the
    /// recursor `kernel::add` minted beside them.
    ///
    /// **The set [`expand`] copies, and copying more is a bug that has been
    /// made.** [`Encoding::env`] is the caller's environment with one block
    /// replaced, so it still holds the *original* form of every other block in
    /// the file. Copying it wholesale put the second block's encoding on top of
    /// the first block's, restoring the first block's inductives and leaving
    /// the file half-encoded — measured as eight `waiting:classifier` on
    /// `mutual_prop_even_odd`, which has four blocks.
    pub fn declares(&self) -> std::collections::HashSet<Name> {
        let mut out = std::collections::HashSet::new();
        for d in &self.decls {
            out.insert(d.name());
            if let Declaration::Inductive { name, ctors, .. } = d {
                for (c, _) in ctors {
                    out.insert(*c);
                }
                out.insert(Name::str(name, "rec"));
            }
        }
        out
    }
}

// ───────────────────────────────────────────────────── syntax helpers ──

/// `∀ tys, body`, `tys` outermost-first and each already in its own scope.
fn foralls(tys: &[E], body: E) -> E {
    tys.iter().rev().fold(body, |b, t| forall(t.clone(), b))
}

/// `fun tys => body`, same convention.
fn lams(tys: &[E], body: E) -> E { tys.iter().rev().fold(body, |b, t| lam(t.clone(), b)) }

/// Peel exactly `n` `∀` binders; `None` if there are fewer. No whnf: every
/// telescope this module peels is one the export wrote as a literal `Π`-nest.
fn peel(ty: &E, n: usize) -> Option<(Vec<E>, E)> {
    let mut tys = Vec::with_capacity(n);
    let mut cur = ty.clone();
    for _ in 0..n {
        let Expr::Forall { ty: d, body } = &*cur else { return None };
        tys.push(d.clone());
        let b = body.clone();
        cur = b;
    }
    Some((tys, cur))
}

/// Peel every `∀`.
fn peel_all(ty: &E) -> (Vec<E>, E) {
    let mut tys = Vec::new();
    let mut cur = ty.clone();
    while let Expr::Forall { ty: d, body } = &*cur {
        tys.push(d.clone());
        let b = body.clone();
        cur = b;
    }
    (tys, cur)
}

/// A telescope moved under `d` extra binders that sit *before* it.
///
/// Entry `j` is scoped under the `j` entries before it, so a reference of index
/// `< j` is one of those and stays put while anything further out moves by `d`.
///
/// **It has one caller now and it had four.** With `Aux` indexed by the members'
/// telescope directly, the telescope had to be moved past `Aux`'s tag binder,
/// past the motives and the tag inside the packed motive, past the motives
/// before each motive, and past the motives and the minors inside a rule. The
/// telescopes are inside the tag now, so `Aux`'s type and the packed motive do
/// not mention them at all, and `Tag.tᵢ`'s own fields are already in the scope
/// the export wrote them in — which leaves motive `k`'s telescope, moved past
/// the `k` motives that precede it. (A rule's *field* types still shift, by
/// `shift` directly rather than through here.) Every one of these is the
/// identity unless an index type mentions a parameter, which only
/// `mutual_index_sorts`' `VA`/`VB` does.
fn shift_all(tys: &[E], d: u32) -> Vec<E> {
    tys.iter().enumerate().map(|(j, t)| shift(t, j as u32, d)).collect()
}

fn params_of(lparams: &[Name]) -> Rc<[Level]> {
    lparams.iter().map(|n| Level::Param(*n)).collect::<Vec<_>>().into()
}

/// `T_k p⃗ ix⃗` becomes `Aux p⃗ (Tag.t_k p⃗ ix⃗)`, everywhere.
///
/// The member's index *values* become the tag constructor's arguments, which
/// is the whole of the generalisation at this site: `Aux` has one index, the
/// tag, and a member with no indices contributes `Aux p⃗ (Tag.t_k p⃗)`.
///
/// Every occurrence of a member inside a constructor's type is a **full**
/// application to the parameters — `kernel::add_block`'s `which_valid_ind_app`
/// has already required it — so the rewrite is total and a partial application
/// is a shape that cannot arise. It is checked anyway, because "cannot arise"
/// is a property of a check in another file.
#[allow(clippy::too_many_arguments)]
fn to_aux(
    e: &E,
    names: &[Name],
    tag_ctors: &[Name],
    aux: &Name,
    np: usize,
    nis: &[usize],
    us: &Rc<[Level]>,
) -> Result<E, Reason> {
    let (head, args) = crate::expr::get_app(e);
    if let Expr::Const(f, _) = &*head {
        if let Some(k) = names.iter().position(|n| n == f) {
            if args.len() != np + nis[k] {
                return Err(Reason::Malformed)
            }
            let rewritten: Vec<E> = args
                .iter()
                .map(|x| to_aux(x, names, tag_ctors, aux, np, nis, us))
                .collect::<Result<_, _>>()?;
            // `Tag.t_k` is a constructor of a *parameterised* inductive, so it
            // takes `p⃗` before the member's own indices.
            let tag_app = app_n(konst(tag_ctors[k], us.clone()), &rewritten);
            let mut a: Vec<E> = rewritten[..np].to_vec();
            a.push(tag_app);
            return Ok(app_n(konst(*aux, us.clone()), &a))
        }
    }
    let go = |x: &E| to_aux(x, names, tag_ctors, aux, np, nis, us);
    Ok(match &**e {
        Expr::App(f, x) => crate::expr::app(go(f)?, go(x)?),
        Expr::Forall { ty, body } => forall(go(ty)?, go(body)?),
        Expr::Lam { ty, body } => lam(go(ty)?, go(body)?),
        Expr::Let { ty, val, body } => {
            Rc::new(Expr::Let { ty: go(ty)?, val: go(val)?, body: go(body)? })
        }
        Expr::Proj { ind, idx, s } => {
            Rc::new(Expr::Proj { ind: *ind, idx: *idx, s: go(s)? })
        }
        _ => e.clone(),
    })
}

/// A name the environment does not already have, `base` with `_1`, `_2` … if
/// it does. The suffix is not decoration: a second mutual block in the same
/// file whose first member has the same name would collide, and a collision
/// here is `insert_new` failing halfway through a block.
fn fresh(env: &Environment, base: Name) -> Name {
    if env.get(&base).is_none() {
        return base
    }
    for i in 1u32.. {
        let n = Name::num(&base, u64::from(i));
        if env.get(&n).is_none() {
            return n
        }
    }
    unreachable!("u32 exhausted")
}

// ────────────────────────────────────────────────────────── the encoder ──

/// Encode one `mutual … end` block.
///
/// `env` is the environment the block was checked into — the encoding reads
/// each member's recursor from it, and returns a *copy* with the block's own
/// constants replaced by the encoding.
pub fn encode(env: &Environment, d: &Declaration) -> Result<Encoding, Reason> {
    let Declaration::Mutual { lparams, num_params, types } = d else {
        return Err(Reason::NotABlock)
    };
    let np = *num_params as usize;
    let n = types.len();
    let us = params_of(lparams);

    // The shared parameter telescope and the block's resultant sort, read off
    // the first member; `add_block` has checked that the members agree on
    // both. **Each member's own index telescope**, read off that member: the
    // kernel does not require them to agree and neither does this encoding —
    // they go into `Tag`'s constructors, one telescope each.
    //
    // Every entry of `ix_tys[i]` is scoped under `p⃗` and the entries before
    // it, which is exactly the scope `Tag.tᵢ`'s fields want, so it is used
    // there unshifted.
    let (param_tys, after_params) = peel(&types[0].ty, np).ok_or(Reason::Malformed)?;
    let (ix0, res0) = peel_all(&after_params);
    let Expr::Sort(u) = &*res0 else { return Err(Reason::Malformed) };
    let u = u.clone();
    let mut ix_tys: Vec<Vec<E>> = vec![ix0];
    for t in &types[1..] {
        let (_, a) = peel(&t.ty, np).ok_or(Reason::Malformed)?;
        let (i, r) = peel_all(&a);
        if !matches!(&*r, Expr::Sort(_)) {
            return Err(Reason::Malformed)
        }
        ix_tys.push(i);
    }
    let nis: Vec<usize> = ix_tys.iter().map(Vec::len).collect();

    // The temporary environment: the caller's, minus the block.
    let mut tmp = env.clone();
    for t in types {
        tmp.consts.remove(&t.name);
        let rec = Name::str(&t.name, "rec");
        tmp.consts.remove(&rec);
        tmp.owners.remove(&rec);
        for (c, _) in &t.ctors {
            tmp.consts.remove(c);
            tmp.owners.remove(c);
        }
    }

    let root = &types[0].name;
    let tag = fresh(&tmp, Name::str(root, "_auxTag"));
    let aux = fresh(&tmp, Name::str(root, "_auxCarrier"));
    let mot = fresh(&tmp, Name::str(root, "_auxMotive"));
    if tag == aux || aux == mot {
        return Err(Reason::NameTaken)
    }
    let names: Vec<Name> = types.iter().map(|t| t.name).collect();
    let tag_ctors: Vec<Name> =
        (0..n).map(|i| Name::num(&Name::str(&tag, "t"), i as u64)).collect();

    let mut decls: Vec<Declaration> = Vec::new();

    // `Tag p⃗`, with the parameters `d` binders in.
    let tag_at = |d: u32| app_n(konst(tag, us.clone()), &bvars(np as u32, d));
    // `Tag.tᵢ p⃗ ix⃗ᵢ`, with the parameters `dp` binders in and the indices `di`.
    let tag_ctor_at = |i: usize, dp: u32, di: u32| {
        let mut a = bvars(np as u32, dp);
        a.extend(bvars(nis[i] as u32, di));
        app_n(konst(tag_ctors[i], us.clone()), &a)
    };

    // **The level `Tag` lives at, and it is the one number in the encoding
    // that is not read off the declaration.** `Tag`'s constructors carry the
    // members' index *values* as fields, so `Tag` must be above every index
    // type's own sort — and an index of type `N` is at `Sort 1` only because
    // `N`'s declaration says so. The encoder therefore asks the checker
    // (`kernel::sort_under`, whose entire output is a `Level`); asking a
    // question is not the boundary, reading a certificate is.
    //
    // `max 1 …` rather than `max 0 …`: `Tag.rec` has to eliminate into
    // `Sort (max u (v+1))`, which a `Prop`-valued `Tag` could not, and a block
    // with no indices then gets `Sort 1` on the nose — the `Type` this was
    // before there were any index telescopes to carry.
    //
    // **It is an over-approximation and does not need to be exact.** What the
    // kernel checks of a constructor field is `sⱼ ≤ W`, so anything above the
    // index sorts is accepted, and nothing constrains an index type's sort
    // from above. `sort_under` is handed `∀ix₁…ix_{j-1}, Iⱼ`, whose sort is
    // the `imax` of the earlier ones with `sⱼ` — above `sⱼ` and below the
    // `max` being built, because every earlier `sᵢ` is in that `max` too.
    let big_w = {
        let mut w = Level::Succ(Rc::new(Level::Zero));
        for tel in &ix_tys {
            for (j, it) in tel.iter().enumerate() {
                let s = crate::kernel::sort_under(&tmp, &param_tys[..], &foralls(&tel[..j], it.clone()))
                    .map_err(|_| Reason::Malformed)?;
                w = Level::max(w, s);
            }
        }
        w.simplify()
    };

    // 1. `Tag`, one constructor per member, carrying **that member's own index
    //    telescope** as its fields. A block whose members are unindexed gets
    //    the enumeration this used to be, with every constructor nullary; that
    //    is the degeneracy and not a branch.
    add(&mut tmp, &mut decls, Declaration::Inductive {
            name: tag,
            lparams: lparams.clone(),
            num_params: *num_params,
            ty: foralls(&param_tys, sort(big_w.clone())),
            ctors: (0..n)
                .map(|i| {
                    // `∀p⃗ ix⃗ᵢ, Tag p⃗`.
                    (tag_ctors[i], foralls(&param_tys, foralls(&ix_tys[i], tag_at(nis[i] as u32))))
                })
                .collect(),
        },
    )?;

    // 2. `Aux`, the whole family as one inductive over the tag. The tag is an
    //    **index**: it differs from constructor to constructor, which is
    //    exactly what a parameter may not do. It is the *only* index —
    //    every member's own indices are inside the tag value now.
    let mut aux_ctors: Vec<(Name, E)> = Vec::new();
    for (i, t) in types.iter().enumerate() {
        for (j, (_, ct)) in t.ctors.iter().enumerate() {
            let cn = Name::str(&aux, &format!("c{i}_{j}"));
            aux_ctors.push((cn, to_aux(ct, &names, &tag_ctors, &aux, np, &nis, &us)?));
        }
    }
    let nc = aux_ctors.len();
    add(&mut tmp, &mut decls, Declaration::Inductive {
            name: aux,
            lparams: lparams.clone(),
            num_params: *num_params,
            // `∀p⃗, Tag p⃗ → Sort u`.
            ty: foralls(&param_tys, forall(tag_at(0), sort(u.clone()))),
            ctors: aux_ctors.clone(),
        },
    )?;

    // 3. The type formers, under their own names: `fun p⃗ ix⃗ᵢ => Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ)`.
    for (i, t) in types.iter().enumerate() {
        let body = {
            let mut a = bvars(np as u32, nis[i] as u32);
            a.push(tag_ctor_at(i, nis[i] as u32, 0));
            app_n(konst(aux, us.clone()), &a)
        };
        let mut tys = param_tys.clone();
        tys.extend(ix_tys[i].iter().cloned());
        add(&mut tmp, &mut decls,
            Declaration::Def {
                name: t.name,
                lparams: lparams.clone(),
                ty: t.ty.clone(),
                value: lams(&tys, body),
                kind: DefKind::Def,
            },
        )?;
    }

    // 4. The constructors, under their own names. `fun p⃗ f⃗ => Aux.cᵢⱼ p⃗ f⃗`
    //    typechecks because the field types differ from `Aux.cᵢⱼ`'s only by δ
    //    on the type formers just defined.
    let mut m = 0usize;
    for t in types.iter() {
        for (cn, ct) in t.ctors.iter() {
            let (binders, _) = peel_all(ct);
            let k = binders.len();
            if k < np {
                return Err(Reason::Malformed)
            }
            let body = app_n(konst(aux_ctors[m].0, us.clone()), &bvars(k as u32, 0));
            add(&mut tmp, &mut decls,
                Declaration::Def {
                    name: *cn,
                    lparams: lparams.clone(),
                    ty: ct.clone(),
                    value: lams(&binders, body),
                    kind: DefKind::Def,
                },
            )?;
            m += 1;
        }
    }

    // Zone A's own recursor for the first member fixes the motive's level and
    // the recursors' level list; every member's agrees, because the motive
    // telescope is the block's.
    let rec0 = Name::str(root, "rec");
    let Some(ConstantInfo::Recursor { lparams: lp2, num_motives, num_minors, .. }) = env.get(&rec0)
    else {
        return Err(Reason::NoRecursor)
    };
    let (lp2, num_motives, num_minors) = (lp2.clone(), *num_motives as usize, *num_minors as usize);
    if num_motives != n || num_minors != nc {
        return Err(Reason::NoRecursor)
    }
    // `elimToSort` gave the recursor one level parameter more than the block
    // when it eliminates large, and that extra one is the motive's.
    let big = lp2.len() == lparams.len() + 1;
    let v = if big { Level::Param(lp2[0]) } else { Level::Zero };
    let us2 = params_of(&lp2);

    // 5. The packed motive, `fun p⃗ m⃗ (t : Tag p⃗) => Aux p⃗ t → Sort v`.
    //
    //    **The level `Tag.rec` runs at is pure syntax now.** The motive body
    //    has no index telescope in front of it — the indices are in the tag —
    //    so it lives at `imax(u, v+1) = max(u, v+1)`, the `imax` collapsing
    //    because `v+1` is never zero. What used to be in this `max` and is not
    //    is the index types' own sorts, and those have not gone anywhere: they
    //    are `big_w`, the sort `Tag` itself was declared at.
    let w = Level::max(u.clone(), Level::Succ(Rc::new(v.clone()))).simplify();
    // Motive `k`'s type: `∀ix⃗_k, T_k p⃗ ix⃗_k → Sort v`, under `p⃗` and the `k`
    // motives before it — the one index shift the encoding still has.
    let motive_tys: Vec<E> = (0..n)
        .map(|k| {
            let mut a = bvars(np as u32, (k + nis[k]) as u32);
            a.extend(bvars(nis[k] as u32, 0));
            foralls(
                &shift_all(&ix_tys[k], k as u32),
                forall(app_n(konst(names[k], us.clone()), &a), sort(v.clone())),
            )
        })
        .collect();
    // Under `p⃗`, the `n` motives and `t`: `Aux p⃗ t → Sort v`.
    let packed_body = {
        let mut a = bvars(np as u32, (n + 1) as u32);
        a.push(bvar(0));
        forall(app_n(konst(aux, us.clone()), &a), sort(v.clone()))
    };
    let packed = lam(tag_at(n as u32), packed_body.clone());
    let mot_ty = {
        let mut tys = param_tys.clone();
        tys.extend(motive_tys.iter().cloned());
        foralls(&tys, forall(tag_at(n as u32), packed_body))
    };
    let mot_val = {
        // `Tag` is a `Type` at every instantiation — `big_w` is a `max` with a
        // `Succ` in it — so `Tag.rec` eliminates large and carries the block's
        // level parameters plus the motive's. Read, not assumed.
        match tmp.get(&Name::str(&tag, "rec")) {
            Some(ConstantInfo::Recursor { lparams: tlp, .. })
                if tlp.len() == lparams.len() + 1 => {}
            _ => return Err(Reason::NoRecursor),
        }
        let tag_rec_levels: Rc<[Level]> = {
            let mut l = vec![w];
            l.extend(us.iter().cloned());
            l.into()
        };
        let tag_rec = konst(Name::str(&tag, "rec"), tag_rec_levels);
        // `Tag.rec p⃗ (packed motive) m⃗`. Each minor is the member's own
        // motive, unwrapped: `Tag.rec`'s minor for `Tag.tᵢ` wants
        // `∀ix⃗ᵢ, Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ) → Sort v` and `mᵢ` has
        // `∀ix⃗ᵢ, Tᵢ p⃗ ix⃗ᵢ → Sort v`, which is the same by δ on `Tᵢ`.
        let mut a = bvars(np as u32, n as u32);
        a.push(packed);
        a.extend(bvars(n as u32, 0));
        let mut tys = param_tys.clone();
        tys.extend(motive_tys.iter().cloned());
        lams(&tys, app_n(tag_rec, &a))
    };
    add(&mut tmp, &mut decls, Declaration::Def {
            name: mot,
            lparams: lp2.clone(),
            ty: mot_ty,
            value: mot_val,
            kind: DefKind::Def,
        },
    )?;

    // `Aux.rec`'s own level list. It is the block's plus a motive level exactly
    // when `Aux` eliminates large, which usually agrees with the block but need
    // not: a block of several types never eliminates large, and `Aux` is one
    // type. Read, not assumed.
    let aux_rec = Name::str(&aux, "rec");
    let Some(ConstantInfo::Recursor { lparams: alp, .. }) = tmp.get(&aux_rec) else {
        return Err(Reason::NoRecursor)
    };
    let aux_rec_levels: Rc<[Level]> = if alp.len() == lparams.len() + 1 {
        let mut l = vec![v.clone()];
        l.extend(us.iter().cloned());
        l.into()
    } else if alp.len() == lparams.len() {
        us.clone()
    } else {
        return Err(Reason::NoRecursor)
    };

    // 6. The recursors, under their own names, at zone A's own declared type.
    for (i, t) in types.iter().enumerate() {
        let rec_name = Name::str(&t.name, "rec");
        let Some(ConstantInfo::Recursor { ty: rty, .. }) = env.get(&rec_name) else {
            return Err(Reason::NoRecursor)
        };
        let rty = rty.clone();
        let ni = nis[i];
        let (binders, _) = peel(&rty, np + n + nc + ni + 1).ok_or(Reason::NoRecursor)?;
        let body = {
            let off = (n + nc + ni + 1) as u32;
            let mut a = bvars(np as u32, off);
            let mut mot_args = bvars(np as u32, off);
            mot_args.extend(bvars(n as u32, (nc + ni + 1) as u32));
            a.push(app_n(konst(mot, us2.clone()), &mot_args));
            a.extend(bvars(nc as u32, (ni + 1) as u32));
            // `Aux` has exactly one index, the tag, and this member's own
            // indices are the arguments of the tag constructor. Then the major.
            a.push(tag_ctor_at(i, off, 1));
            a.push(bvar(0));
            app_n(konst(aux_rec, aux_rec_levels.clone()), &a)
        };
        add(&mut tmp, &mut decls, Declaration::Def {
                name: rec_name,
                lparams: lp2.clone(),
                ty: rty,
                value: lams(&binders, body),
                kind: DefKind::Def,
            },
        )?;
    }

    // 7. The rule theorems, when there is an `Eq` to state them with.
    let mut rules = 0usize;
    if let Some((eq, eq_refl)) = equality(&tmp) {
        for (i, t) in types.iter().enumerate() {
            let rec_name = Name::str(&t.name, "rec");
            let Some(ConstantInfo::Recursor { ty: rty, rules: rl, .. }) = env.get(&rec_name) else {
                return Err(Reason::NoRecursor)
            };
            let (rty, rl) = (rty.clone(), rl.clone());
            let (spine, _) = peel(&rty, np + n + nc).ok_or(Reason::NoRecursor)?;
            for (j, (cn, ct)) in t.ctors.iter().enumerate() {
                let Some((_, rhs)) = rl.iter().find(|(c, _)| c == cn) else {
                    return Err(Reason::NoRecursor)
                };
                let (cb, _) = peel_all(ct);
                let nf = cb.len().checked_sub(np).ok_or(Reason::Malformed)?;
                // A field's type sits under `np + f` binders in the
                // constructor and under `np + n + nc + f` here, so every
                // reference past the fields moves by the motives and minors.
                let mut tys = spine.clone();
                for (f, bt) in cb[np..].iter().enumerate() {
                    tys.push(shift(bt, f as u32, (n + nc) as u32));
                }
                // The constructor's result type says which indices the rule
                // is at: `Tᵢ p⃗ idx⃗`, read under `p⃗, f⃗` and moved past the
                // motives and the minors like the field types above.
                let res = shift(&peel_all(ct).1, nf as u32, (n + nc) as u32);
                let (_, ridx) = crate::expr::get_app(&res);
                if ridx.len() != np + nis[i] {
                    return Err(Reason::Malformed)
                }
                let ridx: Vec<E> = ridx[np..].to_vec();
                let ctor_app = {
                    let mut a = bvars(np as u32, (n + nc + nf) as u32);
                    a.extend(bvars(nf as u32, 0));
                    app_n(konst(*cn, us.clone()), &a)
                };
                let alpha = {
                    let mut a = ridx.clone();
                    a.push(ctor_app.clone());
                    app_n(bvar((nf + nc + (n - 1 - i)) as u32), &a)
                };
                let lhs = {
                    let mut a = bvars(np as u32, (n + nc + nf) as u32);
                    a.extend(bvars(n as u32, (nc + nf) as u32));
                    a.extend(bvars(nc as u32, nf as u32));
                    a.extend(ridx);
                    a.push(ctor_app);
                    app_n(konst(Name::str(&t.name, "rec"), us2.clone()), &a)
                };
                let vs: Rc<[Level]> = vec![v.clone()].into();
                let stmt =
                    app_n(konst(eq, vs.clone()), &[alpha.clone(), lhs.clone(), rhs.clone()]);
                let proof = app_n(konst(eq_refl, vs), &[alpha, lhs]);
                let name =
                    fresh(&tmp, Name::str(&Name::str(&t.name, "rec"), &format!("_auxRule{j}")));
                add(&mut tmp, &mut decls,
                    Declaration::Def {
                        name,
                        lparams: lp2.clone(),
                        ty: foralls(&tys, stmt),
                        value: lams(&tys, proof),
                        kind: DefKind::Theorem,
                    },
                )?;
                rules += 1;
            }
        }
    }

    Ok(Encoding { decls, env: tmp, tag, aux, rules })
}


// ────────────────────────────────────────────────────── the σ demand ──

/// **Which ground instantiations the encoding needs**, as a worklist fixpoint
/// over the generated declarations.
///
/// `checker::instantiations::compute` does this for an export file, and the
/// encoding is not in one: nothing in the `.ndjson` mentions `_auxCarrier`, so
/// the pre-pass that decided every other `(constant, σ)` pair has nothing to
/// say about it. Without this the store is filled at the wrong keys and every
/// use of `_auxMotive` at a non-zero motive level misses — measured, before
/// this existed, as three misses per block.
///
/// The rule is the pre-pass's own: a constant occurrence `c.{ℓ⃗}` inside a
/// declaration being interpreted at `σ` demands `c` at `ℓ⃗` evaluated under
/// `σ`. `seeds` are the pairs the caller already knows it wants — the block's
/// members, constructors and recursors, at the σ the export scheduled them at —
/// and everything else is reached from them.
///
/// Only names the encoding *declares* are followed. A constant from the
/// surrounding file is already scheduled by the file's own pre-pass and is
/// already in the store by the time the block is reached, so adding it here
/// would be this module deciding something the pre-pass owns.
///
/// **Measured, not assumed.** Following *every* constant instead — the file's
/// as well as the encoding's — was tried, and changes nothing: the same pairs,
/// the same certifications, and the same lazy fills.
///
/// That last measurement was the clue, and it was misread once. It said the
/// residue — `Eq`, at one σ on `mutual_iota_reduction` and
/// `mutual_index_sorts` and at two on `mutual_parameters` — was **not** a σ
/// this walk fails to reach, because `Eq`'s σ were scheduled by the file's own
/// pre-pass all along. What the walk cannot fix is *when*: a schedule entry is
/// discharged at the constant's own declaration, and the rule theorems used to
/// be emitted at the block, which in all three files is before `Eq` is
/// declared. [`expand`] emits them last now and `lazyFills` is 0 on all ten
/// mutual fixtures. Nothing here changed.
pub fn demand(
    enc: &Encoding,
    seeds: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
) -> std::collections::HashMap<Name, Vec<Vec<u32>>> {
    demand_over(&enc.env, &enc.declares(), seeds)
}

/// [`demand`] over any generated development, not only this module's.
///
/// The walk is a function of three things and of nothing else about the
/// encoding: the environment the generated constants were checked into, the set
/// of names the generation *declares* (which bounds what is followed), and the
/// seeds. [`crate::nested_splice`] has the same three and the same problem —
/// nothing in the `.ndjson` mentions `T._model.rec_0`, so the export's own
/// σ pre-pass has nothing to say about it — so it calls this rather than
/// carrying a second copy of the fixpoint.
pub fn demand_over(
    env: &Environment,
    mine: &std::collections::HashSet<Name>,
    seeds: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
) -> std::collections::HashMap<Name, Vec<Vec<u32>>> {
    use std::collections::{HashMap, HashSet};
    let mut out: HashMap<Name, Vec<Vec<u32>>> = HashMap::new();
    let mut seen: HashSet<(Name, Vec<u32>)> = HashSet::new();
    let mut work: Vec<(Name, Vec<u32>)> = Vec::new();
    let push = |work: &mut Vec<_>,
                    seen: &mut HashSet<(Name, Vec<u32>)>,
                    out: &mut HashMap<Name, Vec<Vec<u32>>>,
                    n: Name,
                    s: Vec<u32>| {
        if seen.insert((n, s.clone())) {
            out.entry(n).or_default().push(s.clone());
            work.push((n, s));
        }
    };
    for (n, ss) in seeds {
        if !mine.contains(n) {
            continue
        }
        for s in ss {
            push(&mut work, &mut seen, &mut out, *n, s.clone());
        }
    }
    while let Some((n, sigma)) = work.pop() {
        let Some(ci) = env.get(&n) else { continue };
        let map = crate::ground::ground_env(ci.lparams(), &sigma);
        let mut bodies: Vec<E> = vec![ci.ty().clone()];
        if let Some(v) = ci.value() {
            bodies.push(v.clone());
        }
        if let ConstantInfo::Recursor { rules, k_type, .. } = ci {
            bodies.extend(rules.iter().map(|(_, r)| r.clone()));
            bodies.extend(k_type.iter().cloned());
        }
        let mut found: Vec<(Name, Vec<u32>)> = Vec::new();
        for b in &bodies {
            consts(b, &map, mine, &mut found);
        }
        for (c, s) in found {
            push(&mut work, &mut seen, &mut out, c, s);
        }
    }
    for v in out.values_mut() {
        v.sort();
        v.dedup();
    }
    out
}

/// Every `Const` occurrence in `e` whose name the encoding declares, with its
/// levels evaluated at `map`. An occurrence whose levels do not evaluate — a
/// symbolic one — is skipped, exactly as the pre-pass skips it.
fn consts(
    e: &E,
    map: &std::collections::HashMap<Name, u32>,
    mine: &std::collections::HashSet<Name>,
    out: &mut Vec<(Name, Vec<u32>)>,
) {
    match &**e {
        Expr::Const(n, ls) => {
            if mine.contains(n) {
                let s: Option<Vec<u32>> = ls.iter().map(|l| crate::ground::eval(l, map)).collect();
                if let Some(s) = s {
                    out.push((*n, s));
                }
            }
        }
        Expr::App(f, x) => {
            consts(f, map, mine, out);
            consts(x, map, mine, out);
        }
        Expr::Forall { ty, body } | Expr::Lam { ty, body } => {
            consts(ty, map, mine, out);
            consts(body, map, mine, out);
        }
        Expr::Let { ty, val, body } => {
            consts(ty, map, mine, out);
            consts(val, map, mine, out);
            consts(body, map, mine, out);
        }
        Expr::Proj { s, .. } => consts(s, map, mine, out),
        _ => {}
    }
}


// ──────────────────────────────────────────── the block, expanded away ──

/// A declaration list with every `mutual … end` block replaced by its
/// encoding, ready for the ordinary interpretation pass.
pub struct Expanded {
    /// The environment the pass must run against: the caller's, with each
    /// encoded block's constants now the encoding's definitions.
    pub env: Environment,
    /// The declaration list, in file order, blocks expanded in place.
    pub decls: Vec<Declaration>,
    /// The schedule, with the σ the encoding needs added.
    pub schedule: std::collections::HashMap<Name, Vec<Vec<u32>>>,
    /// Blocks seen, blocks encoded, and rule theorems stated.
    pub blocks: usize,
    pub encoded: usize,
    pub rules: usize,
}

/// **Step 6.** Replace every block mini can encode by its encoding, so that the
/// ordinary pass interprets the encoding *under the block's own names* — which
/// is the installation, and is why there is no separate install step.
///
/// A block the encoder declines is left exactly as it was, and
/// `ledger::fill_declaration` records its reason as before.
///
/// **The names are the point.** The encoding defines `Tᵢ`, `Tᵢ.ctorⱼ` and
/// `Tᵢ.rec` under those very names, so `⟦Tᵢ.{σ}⟧` and its typing land in the
/// store at exactly the key every later use site looks them up by. Nothing is
/// copied, re-keyed or transported afterwards; the store does not know a block
/// was ever there.
///
/// # The rule theorems go last, and that is a dependency-order fix
///
/// Everything the encoding *defines* goes where the block was. The rule
/// **theorems** do not: they are appended after the whole file.
///
/// The export's declaration list is in dependency order, so a block's own
/// declaration already follows everything the block mentions. A rule theorem
/// mentions one thing the block does not — the `Eq` its statement is written
/// with — and the exporter, having no reason to put `Eq` before a block that
/// does not use it, routinely puts it *after*. `mutual_iota_reduction` and
/// `mutual_parameters` both declare `Eq` after their block; `mutual_index_sorts`
/// declares it after its first.
///
/// Emitting the rules at the block therefore emitted them before `⟦Eq.{σ}⟧` was
/// in the store, and the miss path built it — which is what the residue
/// recorded here as "one lazy fill, unexplained" was, at every one of the three
/// files that has a rule theorem. Instrumenting the miss path with a `panic!`
/// and reading the declaration order off the run is what settled it; the σ was
/// scheduled all along, which is why widening the σ walk (see [`demand`])
/// changed nothing.
///
/// Appending is correct rather than merely sufficient: a rule theorem is used
/// by nothing, so no declaration can depend on it, and everything it depends on
/// — the encoding's own definitions and the file's `Eq` — is declared before
/// the end of the list.
pub fn expand(
    env: &Environment,
    decls: &[Declaration],
    schedule: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
) -> Expanded {
    let mut out = Expanded {
        env: env.clone(),
        decls: Vec::with_capacity(decls.len()),
        schedule: schedule.clone(),
        blocks: 0,
        encoded: 0,
        rules: 0,
    };
    // The rule theorems of every block, held back until the whole file has been
    // emitted. See the header: their statements mention an `Eq` the block does
    // not, and the exporter puts it wherever the *file* needed it.
    let mut rules: Vec<Declaration> = Vec::new();
    for d in decls {
        let Declaration::Mutual { types, .. } = d else {
            out.decls.push(d.clone());
            continue
        };
        out.blocks += 1;
        let Ok(enc) = encode(env, d) else {
            out.decls.push(d.clone());
            continue
        };
        out.encoded += 1;
        out.rules += enc.rules;
        // A rule theorem is used by nothing, so the fixpoint below cannot reach
        // it; it is seeded at the σ of the recursor it is about.
        let mut seeds = schedule.clone();
        for t in types {
            let Some(ss) = schedule.get(&Name::str(&t.name, "rec")) else { continue };
            for g in &enc.decls {
                let n = g.name();
                if is_rule_of(&n, &t.name) {
                    seeds.entry(n).or_insert_with(|| ss.clone());
                    out.schedule.entry(n).or_default().extend(ss.iter().cloned());
                }
            }
        }
        for (n, ss) in demand(&enc, &seeds) {
            out.schedule.entry(n).or_default().extend(ss);
        }
        // **Only what this encoding declares.** See `Encoding::declares`.
        for k in enc.declares() {
            if let Some(v) = enc.env.consts.get(&k) {
                out.env.consts.insert(k, v.clone());
            }
            match enc.env.owners.get(&k) {
                Some(o) => {
                    out.env.owners.insert(k, *o);
                }
                None => {
                    out.env.owners.remove(&k);
                }
            }
        }
        for g in enc.decls {
            let n = g.name();
            if types.iter().any(|t| is_rule_of(&n, &t.name)) {
                rules.push(g);
            } else {
                out.decls.push(g);
            }
        }
    }
    out.decls.append(&mut rules);
    for v in out.schedule.values_mut() {
        v.sort();
        v.dedup();
    }
    out
}

/// Is `n` one of `t`'s recursor-rule theorems? The name is built here, so it is
/// recognised here rather than by a string search at the call site.
fn is_rule_of(n: &Name, t: &Name) -> bool {
    let rec = Name::str(t, "rec");
    let mut cur = *n;
    // `T.rec._auxRuleJ`, possibly with `fresh`'s numeric suffix on top.
    while let NameView::Num(p, _) = cur.view() {
        cur = p;
    }
    matches!(cur.view(), NameView::Str(p, sfx) if p == rec && sfx.starts_with("_auxRule"))
}

/// Check `d` into `tmp` and record it. **The declaration goes through
/// `kernel::add` and nothing else** — the same entry point every other
/// declaration in the file takes, which is what makes "pass it through the
/// existing pipeline" a statement about this code rather than about it.
fn add(tmp: &mut Environment, decls: &mut Vec<Declaration>, d: Declaration) -> Result<(), Reason> {
    crate::kernel::add(tmp, &d).map_err(|_| Reason::Malformed)?;
    decls.push(d);
    Ok(())
}

/// The environment's `Eq`, if it has Lean's.
///
/// **Read, never minted.** The rule theorems are Lean terms the checker
/// already knows how to interpret — `mini::direct` has a named clause for `Eq`
/// — and an `Eq` this module invented would be a declaration Lean never wrote,
/// which is the one thing the whole design is arranged to avoid. A `prelude`
/// export that never mentions equality simply gets no rule theorems.
///
/// The shape is checked rather than assumed, for the reason `direct.rs`'s
/// header gives: a declaration called `Eq` that is not Lean's `Eq` exists.
fn equality(env: &Environment) -> Option<(Name, Name)> {
    let eq = Name::simple("Eq");
    let refl = Name::str(&eq, "refl");
    let ConstantInfo::Inductive { lparams, num_params, num_indices, ctors, .. } = env.get(&eq)?
    else {
        return None
    };
    if lparams.len() != 1
        || *num_params != 2
        || *num_indices != 1
        || ctors.len() != 1
        || ctors[0] != refl
    {
        return None
    }
    env.get(&refl)?;
    Some((eq, refl))
}
