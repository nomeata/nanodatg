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
//! order — an enumeration `Tag`, one indexed inductive `Aux`, one `def` per
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
//! resultant sort `Sort u`:
//!
//! ```text
//! inductive Tag             : Type              -- n nullary constructors
//! inductive Aux (p⃗)         : Tag → Sort u      -- every constructor of every member
//! def Tᵢ                    : ∀p⃗, Sort u        := fun p⃗ => Aux p⃗ Tag.i
//! def Tᵢ.ctorⱼ              : <its own type>    := fun p⃗ f⃗ => Aux.cᵢⱼ p⃗ f⃗
//! def Mot                   : …                 := fun p⃗ m⃗ => Tag.rec (fun t => Aux p⃗ t → Sort v) m⃗
//! def Tᵢ.rec                : <zone A's type>   := fun p⃗ m⃗ k⃗ t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ Tag.i t
//! theorem Tᵢ.rec._auxRuleⱼ  : <zone A's rule>   := Eq.refl _
//! ```
//!
//! Three things make it work, and each is load-bearing:
//!
//! * **`Tag` is an index of `Aux`, not a parameter.** It has to vary from
//!   constructor to constructor, which is what a parameter may not do.
//! * **The minors are passed through untouched.** `Aux.rec`'s minor for `cᵢⱼ`
//!   wants `Mot p⃗ m⃗ Tag.i (Aux.cᵢⱼ p⃗ f⃗)`, and the minor in hand has type
//!   `mᵢ (Tᵢ.ctorⱼ p⃗ f⃗)`. Those are δι-equal — `Mot … Tag.i` reduces to `mᵢ` by
//!   `Tag`'s own ι rule and `Tᵢ.ctorⱼ` unfolds to `Aux.cᵢⱼ` by δ — so no
//!   transport is built and none is needed.
//! * **Every `Tᵢ.rec` hands `Aux.rec` the same motive and the same minors**,
//!   differing only in the tag. That is why the induction hypothesis a rule
//!   produces, `Aux.rec … Tag.k …`, is *literally* what `T_k.rec …` unfolds
//!   to, and why the rule theorems are reflexivity rather than a transport.
//!
//! The statements are not invented here either. A recursor's declared type and
//! a rule's right-hand side are read from **zone A's own output** — the
//! `ConstantInfo::Recursor` `kernel::add_block` already put in the environment
//! — so what the theorems say is what the kernel already believes, and this
//! module only supplies the proofs.
//!
//! # Indices
//!
//! A block whose members carry indices is encoded the same way, with the tag
//! in front of them:
//!
//! ```text
//! inductive Aux (p⃗) : Tag → ∀ ix, Sort u
//! def Tᵢ  := fun p⃗ ix => Aux p⃗ Tag.i ix
//! def Mot := fun p⃗ m⃗ => Tag.rec (fun t => ∀ix, Aux p⃗ t ix → Sort w′) m⃗
//! def Tᵢ.rec := fun p⃗ m⃗ k⃗ ix t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ Tag.i ix t
//! ```
//!
//! **One thing in that is not syntax, and it is the level `Tag.rec` runs at.**
//! The packed motive lives at `max(s₁ … s_k, u, v+1)` where `sⱼ` is the sort of
//! the `j`-th index *type*, and an index of type `N` is at `Sort 1` only
//! because `N`'s declaration says so. So the encoder asks the checker —
//! `kernel::sort_under`, whose entire output is a `Level`. Asking the checker a
//! question is not the boundary; reading its certificates is, and
//! `ci/check-mutual-blackbox.sh` licenses exactly two entry points by name.
//!
//! (The `imax` a `Π` really carries collapses to `max` throughout, because the
//! innermost factor is `v+1` and `v+1` is never zero. That is what makes the
//! level a `max` of things rather than a nest of conditionals.)
//!
//! **Out of scope: members whose index telescopes differ from one another.**
//! `Aux` has one index telescope, so the members must share theirs — the way
//! they already share their parameters, but by *this* encoding's rule and not
//! by the kernel's. Lifting it means an `Ix : Tag → Type` computed by recursion
//! on the tag, which is a different construction. It is
//! [`Reason::IndicesDiffer`] and it is counted.
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
use crate::expr::{app_n, bvar, bvars, forall, konst, lam, shift, sort, Expr, Level, Name, E};

/// Why a block could not be encoded. Each is a shape, not a failure.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// Not a `mutual … end` block at all.
    NotABlock,
    /// The members' index telescopes are not all the same. See the module
    /// header: `Aux` has one, so they must share one.
    IndicesDiffer,
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
            Reason::IndicesDiffer => "mutual with unequal index telescopes",
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
                    out.insert(c.clone());
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

fn no_levels() -> Rc<[Level]> { Vec::new().into() }

/// A telescope moved under `d` extra binders that sit *before* it.
///
/// Entry `j` is scoped under the `j` entries before it, so a reference of index
/// `< j` is one of those and stays put while anything further out moves by `d`.
/// This is the one piece of de Bruijn arithmetic the indexed encoding adds, and
/// it appears four times: in `Aux`'s type past the tag, in each motive's type
/// past the motives before it, in the packed motive past the motives and the
/// tag, and in a rule's field types past the motives and the minors.
fn shift_all(tys: &[E], d: u32) -> Vec<E> {
    tys.iter().enumerate().map(|(j, t)| shift(t, j as u32, d)).collect()
}

fn params_of(lparams: &[Name]) -> Rc<[Level]> {
    lparams.iter().map(|n| Level::Param(n.clone())).collect::<Vec<_>>().into()
}

/// `T_k p⃗ ix⃗` becomes `Aux p⃗ Tag.k ix⃗`, everywhere.
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
    ni: usize,
    us: &Rc<[Level]>,
) -> Result<E, Reason> {
    let (head, args) = crate::expr::get_app(e);
    if let Expr::Const(f, _) = &*head {
        if let Some(k) = names.iter().position(|n| n == f) {
            if args.len() != np + ni {
                return Err(Reason::Malformed)
            }
            // The tag goes *between* the parameters and the indices: it is
            // `Aux`'s first index, and `Aux.rec` therefore binds it first.
            let mut a: Vec<E> = Vec::with_capacity(np + ni + 1);
            for (j, x) in args.iter().enumerate() {
                if j == np {
                    a.push(konst(tag_ctors[k].clone(), no_levels()));
                }
                a.push(to_aux(x, names, tag_ctors, aux, np, ni, us)?);
            }
            if ni == 0 {
                a.push(konst(tag_ctors[k].clone(), no_levels()));
            }
            return Ok(app_n(konst(aux.clone(), us.clone()), &a))
        }
    }
    let go = |x: &E| to_aux(x, names, tag_ctors, aux, np, ni, us);
    Ok(match &**e {
        Expr::App(f, x) => crate::expr::app(go(f)?, go(x)?),
        Expr::Forall { ty, body } => forall(go(ty)?, go(body)?),
        Expr::Lam { ty, body } => lam(go(ty)?, go(body)?),
        Expr::Let { ty, val, body } => {
            Rc::new(Expr::Let { ty: go(ty)?, val: go(val)?, body: go(body)? })
        }
        Expr::Proj { ind, idx, s } => {
            Rc::new(Expr::Proj { ind: ind.clone(), idx: *idx, s: go(s)? })
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
        let n = Name::Num(Rc::new(base.clone()), u64::from(i));
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

    // The shared parameter telescope, the shared index telescope and the
    // block's resultant sort, read off the first member. `add_block` has
    // checked that the members agree on the parameters and the sort; the
    // *indices* it does not check, because the kernel does not require them to
    // agree — this encoding does.
    let (param_tys, after_params) = peel(&types[0].ty, np).ok_or(Reason::Malformed)?;
    let (ix_tys, res0) = peel_all(&after_params);
    let ni = ix_tys.len();
    let Expr::Sort(u) = &*res0 else { return Err(Reason::Malformed) };
    let u = u.clone();
    for t in &types[1..] {
        let (_, a) = peel(&t.ty, np).ok_or(Reason::Malformed)?;
        let (i, r) = peel_all(&a);
        if i != ix_tys {
            return Err(Reason::IndicesDiffer)
        }
        if !matches!(&*r, Expr::Sort(_)) {
            return Err(Reason::Malformed)
        }
    }

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
    let names: Vec<Name> = types.iter().map(|t| t.name.clone()).collect();
    let tag_ctors: Vec<Name> =
        (0..n).map(|i| Name::Num(Rc::new(Name::str(&tag, "t")), i as u64)).collect();

    let mut decls: Vec<Declaration> = Vec::new();

    // 1. `Tag`, an enumeration with one nullary constructor per member.
    let tag_k = konst(tag.clone(), no_levels());
    add(&mut tmp, &mut decls, Declaration::Inductive {
            name: tag.clone(),
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::Succ(Rc::new(Level::Zero))),
            ctors: tag_ctors.iter().map(|c| (c.clone(), tag_k.clone())).collect(),
        },
    )?;

    // 2. `Aux`, the whole family as one indexed inductive. The tag is an
    //    **index**: it differs from constructor to constructor, which is
    //    exactly what a parameter may not do.
    let mut aux_ctors: Vec<(Name, E)> = Vec::new();
    for (i, t) in types.iter().enumerate() {
        for (j, (_, ct)) in t.ctors.iter().enumerate() {
            let cn = Name::str(&aux, &format!("c{i}_{j}"));
            aux_ctors.push((cn, to_aux(ct, &names, &tag_ctors, &aux, np, ni, &us)?));
        }
    }
    let nc = aux_ctors.len();
    add(&mut tmp, &mut decls, Declaration::Inductive {
            name: aux.clone(),
            lparams: lparams.clone(),
            num_params: *num_params,
            // `∀p⃗, Tag → ∀ix, Sort u`. The index types come from the first
            // member and are shifted past the tag binder.
            ty: foralls(
                &param_tys,
                forall(tag_k.clone(), foralls(&shift_all(&ix_tys, 1), sort(u.clone()))),
            ),
            ctors: aux_ctors.clone(),
        },
    )?;

    // 3. The type formers, under their own names.
    for (i, t) in types.iter().enumerate() {
        let body = {
            let mut a = bvars(np as u32, 0);
            a.push(konst(tag_ctors[i].clone(), no_levels()));
            app_n(konst(aux.clone(), us.clone()), &a)
        };
        add(&mut tmp, &mut decls,
            Declaration::Def {
                name: t.name.clone(),
                lparams: lparams.clone(),
                ty: t.ty.clone(),
                value: lams(&param_tys, body),
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
            let body = app_n(konst(aux_ctors[m].0.clone(), us.clone()), &bvars(k as u32, 0));
            add(&mut tmp, &mut decls,
                Declaration::Def {
                    name: cn.clone(),
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
    let v = if big { Level::Param(lp2[0].clone()) } else { Level::Zero };
    let us2 = params_of(&lp2);

    // 5. The packed motive. `Tag.rec` is instantiated at the sort the motive
    //    body lives at, and that is the one number in the whole encoding that
    //    is not readable off the declaration: it is `max` over the *index
    //    types'* own sorts together with `u` and `v+1`, and an index of type
    //    `N` is at `Sort 1` only because `N`'s declaration says so. The `imax`
    //    a `Π` really carries collapses to `max` because the innermost factor
    //    is `v+1`, which is never zero — that is what makes this a `max` of
    //    things rather than a nest of conditionals.
    let w = {
        let mut w = Level::max(u.clone(), Level::Succ(Rc::new(v.clone())));
        for (j, it) in ix_tys.iter().enumerate() {
            let s = crate::kernel::sort_under(&tmp, &param_tys[..], &foralls(&ix_tys[..j], it.clone()))
                .map_err(|_| Reason::Malformed)?;
            // `sort_under` was handed `∀ix₁…ix_{j-1}, Iⱼ`, whose sort is the
            // `imax` of the earlier ones with `sⱼ` — an over-approximation of
            // `sⱼ` that is still below the `max` being built, because every
            // earlier `sᵢ` is in that `max` too. Asking for `Iⱼ` alone would
            // need the earlier indices in scope, which is the same telescope.
            w = Level::max(w, s);
        }
        w.simplify()
    };
    // `∀ix, Aux p⃗ t ix → Sort v`, as a telescope under `p⃗` and the `n` motives.
    let aux_at = |depth_params: u32, depth_tag: u32| {
        let mut a = bvars(np as u32, depth_params);
        a.push(bvar(depth_tag));
        a.extend(bvars(ni as u32, 0));
        forall(app_n(konst(aux.clone(), us.clone()), &a), sort(v.clone()))
    };
    let motive_tys: Vec<E> = (0..n)
        .map(|k| {
            let mut a = bvars(np as u32, (k + ni) as u32);
            a.extend(bvars(ni as u32, 0));
            foralls(
                &shift_all(&ix_tys, k as u32),
                forall(app_n(konst(names[k].clone(), us.clone()), &a), sort(v.clone())),
            )
        })
        .collect();
    // Under `p⃗`, the `n` motives and `t`: the indices sit `n + 1` binders in.
    let packed_body = foralls(&shift_all(&ix_tys, (n + 1) as u32), aux_at((n + 1 + ni) as u32, ni as u32));
    let packed = lam(tag_k.clone(), packed_body.clone());
    let mot_ty = {
        let mut tys = param_tys.clone();
        tys.extend(motive_tys.iter().cloned());
        foralls(&tys, forall(tag_k.clone(), packed_body))
    };
    let mot_val = {
        match tmp.get(&Name::str(&tag, "rec")) {
            Some(ConstantInfo::Recursor { lparams, .. }) if lparams.len() == 1 => {}
            _ => return Err(Reason::NoRecursor),
        }
        let tag_rec = konst(Name::str(&tag, "rec"), vec![w].into());
        let mut a = vec![packed];
        a.extend(bvars(n as u32, 0));
        let mut tys = param_tys.clone();
        tys.extend(motive_tys.iter().cloned());
        lams(&tys, app_n(tag_rec, &a))
    };
    add(&mut tmp, &mut decls, Declaration::Def {
            name: mot.clone(),
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
        let (binders, _) = peel(&rty, np + n + nc + ni + 1).ok_or(Reason::NoRecursor)?;
        let body = {
            let off = (n + nc + ni + 1) as u32;
            let mut a = bvars(np as u32, off);
            let mut mot_args = bvars(np as u32, off);
            mot_args.extend(bvars(n as u32, (nc + ni + 1) as u32));
            a.push(app_n(konst(mot.clone(), us2.clone()), &mot_args));
            a.extend(bvars(nc as u32, (ni + 1) as u32));
            // `Aux.rec` binds the tag first — it is `Aux`'s first index — and
            // then the members' own indices, then the major argument.
            a.push(konst(tag_ctors[i].clone(), no_levels()));
            a.extend(bvars(ni as u32, 1));
            a.push(bvar(0));
            app_n(konst(aux_rec.clone(), aux_rec_levels.clone()), &a)
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
                if ridx.len() != np + ni {
                    return Err(Reason::Malformed)
                }
                let ridx: Vec<E> = ridx[np..].to_vec();
                let ctor_app = {
                    let mut a = bvars(np as u32, (n + nc + nf) as u32);
                    a.extend(bvars(nf as u32, 0));
                    app_n(konst(cn.clone(), us.clone()), &a)
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
                    app_n(konst(eq.clone(), vs.clone()), &[alpha.clone(), lhs.clone(), rhs.clone()]);
                let proof = app_n(konst(eq_refl.clone(), vs), &[alpha, lhs]);
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
/// **Measured, not assumed, and there is one residue.** Following *every*
/// constant instead — the file's as well as the encoding's — was tried, and
/// changes nothing: the same pairs, the same certifications, and the same one
/// lazy fill, `Eq` at `σ = [1]` on `mutual_iota_reduction`. So the σ that fill
/// is about is not one this walk fails to reach, and widening the walk buys
/// only a wider schedule. The residue is pinned in `mini/tests/mutual.rs` and
/// unexplained; it costs nothing observable — that file certifies every one of
/// its twenty-six pairs — and it is the one place the design's `lazyFills = 0`
/// does not hold.
pub fn demand(
    enc: &Encoding,
    seeds: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
) -> std::collections::HashMap<Name, Vec<Vec<u32>>> {
    use std::collections::{HashMap, HashSet};
    let mine: HashSet<Name> = enc.declares();
    let mut out: HashMap<Name, Vec<Vec<u32>>> = HashMap::new();
    let mut seen: HashSet<(Name, Vec<u32>)> = HashSet::new();
    let mut work: Vec<(Name, Vec<u32>)> = Vec::new();
    let push = |work: &mut Vec<_>,
                    seen: &mut HashSet<(Name, Vec<u32>)>,
                    out: &mut HashMap<Name, Vec<Vec<u32>>>,
                    n: Name,
                    s: Vec<u32>| {
        if seen.insert((n.clone(), s.clone())) {
            out.entry(n.clone()).or_default().push(s.clone());
            work.push((n, s));
        }
    };
    for (n, ss) in seeds {
        if !mine.contains(n) {
            continue
        }
        for s in ss {
            push(&mut work, &mut seen, &mut out, n.clone(), s.clone());
        }
    }
    while let Some((n, sigma)) = work.pop() {
        let Some(ci) = enc.env.get(&n) else { continue };
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
            consts(b, &map, &mine, &mut found);
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
                    out.push((n.clone(), s));
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
                    seeds.entry(n.clone()).or_insert_with(|| ss.clone());
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
                out.env.consts.insert(k.clone(), v.clone());
            }
            match enc.env.owners.get(&k) {
                Some(o) => {
                    out.env.owners.insert(k, o.clone());
                }
                None => {
                    out.env.owners.remove(&k);
                }
            }
        }
        out.decls.extend(enc.decls);
    }
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
    let mut cur = n;
    // `T.rec._auxRuleJ`, possibly with `fresh`'s numeric suffix on top.
    while let Name::Num(p, _) = cur {
        cur = p;
    }
    matches!(cur, Name::Str(p, sfx) if **p == rec && sfx.starts_with("_auxRule"))
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
