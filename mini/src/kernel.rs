//! The port of `MiniKernel/Kernel.lean`.
//!
//! # Interface
//!
//! One file, like the original, and laid out in the original's order so the two
//! can be read side by side: context primitives, the `whnf`/`inferType`/
//! `isProp`/`inferProj`/telescope mutual block, the level order, definitional
//! equality, and `Environment.add`.
//!
//! **This is step (b) of MINI-DESIGN.md §12: acceptance only, no evidence.**
//! Every function returns exactly what mini-lean's returns, and `Result<_,
//! String>` is mini-lean's `Except String`. The evidence types of §5 (`Typing`,
//! `Conv`, `Ev`) do not appear yet; step (c) threads them through these same
//! signatures. Deviating from the original *here* would make the fidelity gate
//! (`mini/tests/tutorial.rs`) meaningless, so where the original is odd — the
//! `whnf` of a codomain sort performed outside the binder's scope in
//! `inferType`'s `.forall` clause, `natLit`'s dropped argument stack,
//! `Level.le`'s incompleteness — the oddity is reproduced and commented.
//!
//! Departures from mini-lean, all mechanical:
//!
//! * `ReaderT`'s implicit scoping becomes explicit push/pop on `Checker::lenv`,
//!   always through [`Checker::scoped`], which restores the telescope on the
//!   error path too. `openForall`/`openForallEager` become "push and return the
//!   body" rather than continuation-passing: a continuation-passing port
//!   recurses with a *new* closure type at each step, which does not
//!   monomorphise.
//! * The telescope is a `Vec` whose **last** element is `bvar 0`, where
//!   mini-lean's `List`'s **head** is.
//! * `appendError`'s message decoration is dropped except where it aids
//!   debugging; it cannot change a verdict.

use crate::env::{instantiate_lparams, ConstantInfo, DefKind, Declaration, Environment};
use crate::expr::{
    app, app_n, arrow, bvar, bvars, forall, get_app, has_bvar, has_const, konst, lam, shift, sort,
    subst, substs, Expr, Level, Name, E,
};
use std::rc::Rc;

pub type R<T> = Result<T, String>;

fn no_levels() -> Rc<[Level]> { Vec::new().into() }

fn levels(ls: &[Level]) -> Rc<[Level]> { ls.to_vec().into() }

/// `Array.extract`'s clamping slice, which mini-lean relies on in several
/// places (`retType.getApp.2[numParams:numParams+numIndices]` on a spine that
/// may be shorter).
fn slice(v: &[E], a: usize, b: usize) -> Vec<E> {
    let a = a.min(v.len());
    let b = b.min(v.len()).max(a);
    v[a..b].to_vec()
}

/// `sort` — the shape check, not the interpretation.
pub fn as_sort(e: &E) -> R<Level> {
    match &**e {
        Expr::Sort(u) => Ok(u.clone()),
        _ => Err(format!("Expected a sort, got {e}")),
    }
}

/// `assertLevelLe`.
pub fn assert_level_le(l1: &Level, l2: &Level) -> R<()> {
    if Level::le(&l1.simplify(), &l2.simplify(), 0) {
        Ok(())
    } else {
        Err(format!("Expected level inequality does not hold: {l1} ≤ {l2}"))
    }
}

/// `assertLevelEq`.
pub fn assert_level_eq(l1: &Level, l2: &Level) -> R<()> {
    let (a, b) = (l1.simplify(), l2.simplify());
    if Level::le(&a, &b, 0) && Level::le(&b, &a, 0) {
        Ok(())
    } else {
        Err(format!("Expected level equality does not hold: {l1} = {l2}"))
    }
}

/// `freshLevelName`.
fn fresh_level_name(used: &[Name]) -> Name {
    let mut n = 0u32;
    loop {
        let name = if n == 0 { Name::simple("v") } else { Name::simple(&format!("v{n}")) };
        if !used.contains(&name) {
            return name
        }
        n += 1;
    }
}

/// The data `checkCtorType`/`checkCtorParam`/`isValidIndApp` close over in the
/// original; a struct here because Rust has no local `let rec` with capture.
struct IndCtx<'a> {
    ind_name: &'a Name,
    lparams: &'a [Name],
    num_params: u32,
    num_indices: u32,
    ind_level: &'a Level,
}

/// `LEnv` and its monad, minus the unused `lparams` set (mini-lean never reads
/// it: `checkDeclarInfo`-style parameter validation does not exist there).
pub struct Checker<'e> {
    env: &'e Environment,
    /// The local typing environment, as a telescope. **`lenv.last()` is the
    /// type of `bvar 0`**; a `bvar j` inside `lenv[i]` refers to `lenv[i+j+1]`
    /// in mini-lean's indexing, i.e. one step further out.
    lenv: Vec<E>,
}

impl<'e> Checker<'e> {
    pub fn new(env: &'e Environment) -> Self { Checker { env, lenv: Vec::new() } }

    /// Environment lookup at the environment's own lifetime, so results may be
    /// held across `&mut self` calls (the environment is fixed for a
    /// `Checker`'s whole life).
    fn lookup(&self, n: &Name) -> Option<&'e ConstantInfo> { self.env.consts.get(n) }

    // ─────────────────────────────────────────── context primitives ──

    /// `getLocalType`.
    fn local_type(&self, idx: u32) -> R<E> {
        let n = self.lenv.len();
        if (idx as usize) >= n {
            return Err(format!("deBruijn index #{idx} out of bounds"))
        }
        Ok(shift(&self.lenv[n - 1 - idx as usize], 0, idx + 1))
    }

    /// `openType`, push half. Always paired by [`Checker::scoped`].
    fn push(&mut self, ty: E) { self.lenv.push(ty) }

    /// `openTypes` — a non-dependent telescope, each entry shifted past the
    /// ones pushed before it.
    fn push_types(&mut self, tys: &[E]) {
        for (i, t) in tys.iter().enumerate() {
            let d = u32::try_from(i).expect("telescope length");
            self.lenv.push(shift(t, 0, d));
        }
    }

    /// `readLocalTypes`: the innermost `n` types, brought into the current
    /// context and ordered outermost-first.
    fn read_local_types(&self, n: u32) -> R<Vec<E>> {
        if self.lenv.len() < n as usize {
            return Err(format!("Expected at least {n} local variables, got {}", self.lenv.len()))
        }
        let mut out: Vec<E> = (0..n).map(|i| self.local_type(i)).collect::<R<Vec<E>>>()?;
        out.reverse();
        Ok(out)
    }

    /// Run `f` with the telescope restored afterwards, on the error path too.
    /// This is `withReader`'s scoping, made explicit.
    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.lenv.len();
        let r = f(self);
        self.lenv.truncate(saved);
        r
    }

    /// `mkForall`: wrap `body` in `n` `Π`s with types read off the telescope.
    fn mk_forall(&self, n: u32, body: E) -> R<E> {
        let len = self.lenv.len();
        let n = (n as usize).min(len);
        let mut out = body;
        for i in 0..n {
            out = forall(self.lenv[len - 1 - i].clone(), out);
        }
        Ok(out)
    }

    /// `mkLambda`.
    fn mk_lambda(&self, n: u32, body: E) -> R<E> {
        let len = self.lenv.len();
        let n = (n as usize).min(len);
        let mut out = body;
        for i in 0..n {
            out = lam(self.lenv[len - 1 - i].clone(), out);
        }
        Ok(out)
    }

    // ─────────────────────────────────────────────────────── whnf ──

    /// `whnf`. Mini-lean's stack machine, with full eager delta and no
    /// lazy-delta heuristic; `go`'s recursion is a loop here.
    pub fn whnf(&mut self, e: &E) -> R<E> {
        let mut cur = e.clone();
        // `stack[0]` is the *first* argument, matching mini-lean's `a :: stack`.
        let mut stack: Vec<E> = Vec::new();
        loop {
            let node = cur.clone();
            match &*node {
                Expr::Const(name, ls) => {
                    let cinfo =
                        self.lookup(name).ok_or_else(|| format!("Unknown constant {name}"))?;
                    if let Some(value) = cinfo.value() {
                        cur = instantiate_lparams(value, cinfo.lparams(), ls)?;
                        continue
                    }
                    if let ConstantInfo::Recursor {
                        lparams, num_params, num_minors, num_indices, rules, k_type, ..
                    } = cinfo
                    {
                        let np = *num_params as usize;
                        let nm = *num_minors as usize;
                        let major_pos = np + 1 + nm + *num_indices as usize;
                        let Some(major) = stack.get(major_pos).cloned() else {
                            return Ok(app_n(node.clone(), &stack))
                        };
                        // The K-rule: an inductive proposition's major premise
                        // needs only to *have* the right type.
                        if let Some(kt) = k_type {
                            let kt = instantiate_lparams(kt, lparams, ls)?;
                            let kt = substs(&kt, &stack[..np], 0);
                            let major_ty = self.infer_type(&major)?;
                            if self.is_def_eq(&major_ty, &kt)? {
                                if rules.len() != 1 {
                                    return Err("Wrong number of rules for k-rule recursor".into())
                                }
                                let args = stack[..np + 1 + nm].to_vec();
                                let rhs = instantiate_lparams(&rules[0].1, lparams, ls)?;
                                cur = substs(&rhs, &args, 0);
                                stack = stack[major_pos + 1..].to_vec();
                                continue
                            }
                        }
                        let major2 = self.whnf(&major)?;
                        let (head, con_args) = get_app(&major2);
                        let mut fired = None;
                        if let Expr::Const(f, _) = &*head {
                            if let Some((_, rhs)) = rules.iter().find(|(c, _)| c == f) {
                                let fields = slice(&con_args, np, con_args.len());
                                let mut args = stack[..np + 1 + nm].to_vec();
                                args.extend(fields);
                                let rhs = instantiate_lparams(rhs, lparams, ls)?;
                                fired = Some(substs(&rhs, &args, 0));
                            }
                        }
                        if let Some(rhs) = fired {
                            cur = rhs;
                            stack = stack[major_pos + 1..].to_vec();
                            continue
                        }
                        let mut stack2 = stack.clone();
                        stack2[major_pos] = major2;
                        return Ok(app_n(node.clone(), &stack2))
                    }
                    return Ok(app_n(node.clone(), &stack))
                }
                Expr::App(f, a) => {
                    stack.insert(0, a.clone());
                    cur = f.clone();
                }
                Expr::Lam { body, .. } if !stack.is_empty() => {
                    let a = stack.remove(0);
                    cur = subst(body, &a);
                }
                Expr::Let { val, body, .. } => {
                    cur = subst(body, val);
                }
                Expr::Proj { ind, idx, s } => {
                    let s2 = self.whnf(s)?;
                    let stuck =
                        Rc::new(Expr::Proj { ind: ind.clone(), idx: *idx, s: s2.clone() });
                    let (head, args) = get_app(&s2);
                    let Expr::Const(f, _) = &*head else { return Ok(app_n(stuck, &stack)) };
                    let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind)
                    else {
                        return Ok(app_n(stuck, &stack))
                    };
                    if ctors.len() != 1 || &ctors[0] != f {
                        return Ok(app_n(stuck, &stack))
                    }
                    let pos = (*num_params + *idx) as usize;
                    if pos >= args.len() {
                        return Err(format!(
                            "Type error during reduction: projection index {} out of bounds for {s2}",
                            idx + 1
                        ))
                    }
                    cur = args[pos].clone();
                }
                Expr::NatLit(n) => {
                    // The parser catches these; mini-lean is explicit here too.
                    // Note the original drops `stack` on this branch — a nat
                    // literal is never in head position of an application.
                    if *n > 10 {
                        return Err(
                            "The mini kernel does not support nat literals larger than 10".into()
                        )
                    }
                    let nat = Name::simple("Nat");
                    return Ok(if *n == 0 {
                        konst(Name::str(&nat, "zero"), no_levels())
                    } else {
                        app(konst(Name::str(&nat, "succ"), no_levels()), Rc::new(Expr::NatLit(n - 1)))
                    })
                }
                _ => return Ok(app_n(node.clone(), &stack)),
            }
        }
    }

    // ────────────────────────────────────────────────── inferType ──

    pub fn infer_type(&mut self, e: &E) -> R<E> {
        match &**e {
            Expr::BVar(i) => self.local_type(*i),
            Expr::Const(name, ls) => {
                let cinfo = self.lookup(name).ok_or_else(|| format!("Unknown constant {name}"))?;
                instantiate_lparams(cinfo.ty(), cinfo.lparams(), ls)
            }
            Expr::Sort(u) => Ok(sort(u.clone().succ())),
            Expr::App(f, arg) => {
                let f_ty = self.infer_type(f)?;
                let f_ty = self.whnf(&f_ty)?;
                let Expr::Forall { ty, body } = &*f_ty else {
                    return Err(format!(
                        "Expected a function type in application of {f} to {arg}, got {f_ty}"
                    ))
                };
                let arg_ty = self.infer_type(arg)?;
                self.assert_is_def_eq(ty, &arg_ty)?;
                Ok(subst(body, arg))
            }
            Expr::Forall { ty, body } => {
                let s1 = self.infer_type(ty)?;
                let s1 = self.whnf(&s1)?;
                let l1 = as_sort(&s1)?;
                let s2 = self.scoped(|c| {
                    c.push(ty.clone());
                    c.infer_type(body)
                })?;
                // NB: mini-lean whnfs the codomain's sort *outside* the
                // binder's scope. Reproduced deliberately.
                let s2 = self.whnf(&s2)?;
                let l2 = as_sort(&s2)?;
                Ok(sort(Level::imax(l1, l2)))
            }
            Expr::Lam { ty, body } => {
                let s1 = self.infer_type(ty)?;
                let s1 = self.whnf(&s1)?;
                as_sort(&s1)?;
                let t2 = self.scoped(|c| {
                    c.push(ty.clone());
                    c.infer_type(body)
                })?;
                Ok(forall(ty.clone(), t2))
            }
            Expr::Let { ty, val, body } => {
                let s1 = self.infer_type(ty)?;
                let s1 = self.whnf(&s1)?;
                as_sort(&s1)?;
                let val_ty = self.infer_type(val)?;
                self.assert_is_def_eq(ty, &val_ty)?;
                // mini-lean substitutes rather than opening a `let` scope.
                let body2 = subst(body, val);
                self.infer_type(&body2)
            }
            Expr::Proj { ind, idx, s } => self.infer_proj(ind, *idx, s),
            Expr::NatLit(_) => Ok(konst(Name::simple("Nat"), no_levels())),
            Expr::StrLit(_) => Ok(konst(Name::simple("String"), no_levels())),
        }
    }

    /// `checkType`.
    pub fn check_type(&mut self, e: &E) -> R<()> { self.infer_type(e).map(|_| ()) }

    /// `isProp`.
    pub fn is_prop(&mut self, ty: &E) -> R<bool> {
        let s = self.infer_type(ty)?;
        let s = self.whnf(&s)?;
        Ok(as_sort(&s)?.is_zero())
    }

    /// `inferProj`.
    fn infer_proj(&mut self, n: &Name, idx: u32, e: &E) -> R<E> {
        let t = self.infer_type(e)?;
        let ty = self.whnf(&t)?;
        let (head, args) = get_app(&ty);
        let Expr::Const(ind_name, us) = &*head else {
            return Err(format!("Type of projected expression is not an inductive: {ty}"))
        };
        let Some(ConstantInfo::Inductive { num_params, num_indices, ctors, .. }) =
            self.lookup(ind_name)
        else {
            return Err(format!("Type of projected expression is not an inductive: {ty}"))
        };
        if args.len() != (*num_params + *num_indices) as usize {
            return Err("Invalid projection, expression is not fully applied".to_string())
        }
        if ctors.len() != 1 {
            return Err(format!("Invalid projection, {ind_name} has not exactly one constructor"))
        }
        let ctor_name = &ctors[0];
        let Some(ConstantInfo::Opaque { lparams: clp, ty: cty }) = self.lookup(ctor_name) else {
            return Err(format!("Constructor {ctor_name} not found in environment"))
        };
        let ctor_ty = instantiate_lparams(cty, clp, us)?;
        let params = slice(&args, 0, *num_params as usize);
        let mut ctor_ty = self.instantiate_foralls(&ctor_ty, &params)?;
        let is_prop_type = self.is_prop(&ctor_ty)?;
        for i in 0..idx {
            let cur = ctor_ty.clone();
            let Expr::Forall { ty: d, body: b } = &*cur else {
                return Err(format!(
                    "Projection index {} out of bounds for {ind_name}",
                    idx + 1
                ))
            };
            if is_prop_type && has_bvar(b, 0) && !self.is_prop(d)? {
                return Err(format!(
                    "Invalid projection; projection {} is depended upon and not a proposition.",
                    i + 1
                ))
            }
            ctor_ty = subst(b, &Rc::new(Expr::Proj { ind: n.clone(), idx: i, s: e.clone() }));
        }
        let cur = ctor_ty.clone();
        let Expr::Forall { ty: d, .. } = &*cur else {
            return Err(format!("Projection index {} out of bounds for {ind_name}", idx + 1))
        };
        if is_prop_type && !self.is_prop(d)? {
            return Err(format!(
                "Invalid projection; projection {} would project data out of a proposition",
                idx + 1
            ))
        }
        Ok(d.clone())
    }

    // ─────────────────────────────────────────── telescope helpers ──

    /// `openForall n type k`, push form: opens `n` binders and returns the body.
    /// The caller must be inside [`Checker::scoped`].
    fn open_forall_push(&mut self, n: u32, ty: &E) -> R<E> {
        let mut cur = ty.clone();
        for _ in 0..n {
            let t = self.whnf(&cur)?;
            let Expr::Forall { ty: d, body } = &*t else {
                return Err(format!("Insufficient number of parameters: {t}"))
            };
            let (d, body) = (d.clone(), body.clone());
            self.push(d);
            cur = body;
        }
        Ok(cur)
    }

    /// `openForallEager`, push form: returns `(binders opened, the whnf'd
    /// non-`Π` body)`. The caller must be inside [`Checker::scoped`].
    fn open_forall_eager_push(&mut self, ty: &E) -> R<(u32, E)> {
        let mut cur = ty.clone();
        let mut n = 0u32;
        loop {
            let t = self.whnf(&cur)?;
            let Expr::Forall { ty: d, body } = &*t else { return Ok((n, t.clone())) };
            let (d, body) = (d.clone(), body.clone());
            self.push(d);
            cur = body;
            n += 1;
        }
    }

    /// `instantiateForalls`.
    fn instantiate_foralls(&mut self, ty: &E, xs: &[E]) -> R<E> {
        let mut result = ty.clone();
        for x in xs {
            let t = self.whnf(&result)?;
            let Expr::Forall { body, .. } = &*t else {
                return Err(format!("Expected a function type, got {t}"))
            };
            result = subst(body, x);
        }
        Ok(result)
    }

    // ──────────────────────────────────────── definitional equality ──

    /// `isPropOrUnit` — defeq's proof-irrelevance gate.
    fn is_prop_or_unit(&mut self, t: &E) -> R<bool> {
        let s = self.infer_type(t)?;
        let s = self.whnf(&s)?;
        let u = as_sort(&s)?;
        if u.is_zero() {
            return Ok(true)
        }
        let tw = self.whnf(t)?;
        let (head, _) = get_app(&tw);
        let Expr::Const(name, _) = &*head else { return Ok(false) };
        let Some(ConstantInfo::Inductive { is_unit, .. }) = self.lookup(name) else {
            return Ok(false)
        };
        Ok(*is_unit)
    }

    /// `tryStructureEta`.
    fn try_structure_eta(&mut self, e1: &E, e2: &E) -> R<bool> {
        let (head, args) = get_app(e1);
        let Expr::Const(con_name, _) = &*head else { return Ok(false) };
        let t = self.infer_type(e1)?;
        let t = self.whnf(&t)?;
        let (ind_head, _) = get_app(&t);
        let Expr::Const(ind_name, _) = &*ind_head else { return Ok(false) };
        let Some(ConstantInfo::Inductive { num_params, ctors, .. }) = self.lookup(ind_name) else {
            return Ok(false)
        };
        if ctors.len() != 1 || &ctors[0] != con_name {
            return Ok(false)
        }
        let np = *num_params as usize;
        for (i, arg) in args.iter().enumerate().skip(np) {
            let p = Rc::new(Expr::Proj {
                ind: ind_name.clone(),
                idx: u32::try_from(i - np).expect("field index"),
                s: e2.clone(),
            });
            let arg = arg.clone();
            if !self.is_def_eq(&arg, &p)? {
                return Ok(false)
            }
        }
        Ok(true)
    }

    /// `tryFunEta`.
    fn try_fun_eta(&mut self, e1: &E, e2: &E) -> R<bool> {
        let Expr::Lam { ty: t1, body: b1 } = &**e1 else { return Ok(false) };
        let (t1, b1) = (t1.clone(), b1.clone());
        let rhs = app(shift(e2, 0, 1), bvar(0));
        self.scoped(|c| {
            c.push(t1);
            c.is_def_eq(&b1, &rhs)
        })
    }

    /// `isDefEq`: `assertIsDefEq` with the exception swallowed. The telescope is
    /// restored explicitly, which is what `ReaderT`'s backtracking does for the
    /// original.
    pub fn is_def_eq(&mut self, e1: &E, e2: &E) -> R<bool> {
        let saved = self.lenv.len();
        let r = self.assert_is_def_eq(e1, e2);
        self.lenv.truncate(saved);
        Ok(r.is_ok())
    }

    /// `assertIsDefEqImpl`. Clause order is the original's, which is what
    /// acceptance fidelity depends on.
    pub fn assert_is_def_eq(&mut self, e1: &E, e2: &E) -> R<()> {
        // Proof irrelevance first.
        let t1 = self.infer_type(e1)?;
        if self.is_prop_or_unit(&t1)? {
            return Ok(())
        }
        let a = self.whnf(e1)?;
        let b = self.whnf(e2)?;
        let differ = || {
            Err(format!("Expected definitional equality between {a} and {b}, but they differ."))
        };
        match (&*a, &*b) {
            (Expr::Sort(l1), Expr::Sort(l2)) => assert_level_eq(l1, l2),
            (Expr::Forall { ty: t1, body: b1 }, Expr::Forall { ty: t2, body: b2 })
            | (Expr::Lam { ty: t1, body: b1 }, Expr::Lam { ty: t2, body: b2 }) => {
                let (t1, b1, b2) = (t1.clone(), b1.clone(), b2.clone());
                self.assert_is_def_eq(&t1, t2)?;
                self.scoped(|c| {
                    c.push(t1.clone());
                    c.assert_is_def_eq(&b1, &b2)
                })
            }
            (Expr::BVar(n1), Expr::BVar(n2)) => {
                if n1 == n2 {
                    Ok(())
                } else {
                    differ()
                }
            }
            (Expr::App(f1, a1), Expr::App(f2, a2)) => {
                let (f1, a1, f2, a2) = (f1.clone(), a1.clone(), f2.clone(), a2.clone());
                self.assert_is_def_eq(&f1, &f2)?;
                self.assert_is_def_eq(&a1, &a2)
            }
            (Expr::Const(n1, ls1), Expr::Const(n2, ls2)) => {
                if n1 != n2 {
                    return differ()
                }
                if ls1.len() != ls2.len() {
                    return Err(format!("Mismatched level parameter list when checking {a} =?= {b}"))
                }
                for (l1, l2) in ls1.iter().zip(ls2.iter()) {
                    assert_level_eq(l1, l2)?;
                }
                Ok(())
            }
            (
                Expr::Proj { ind: n1, idx: i1, s: s1 },
                Expr::Proj { ind: n2, idx: i2, s: s2 },
            ) => {
                if n1 != n2 || i1 != i2 {
                    return Err(format!("Projections differ: {a} =?= {b}"))
                }
                let (s1, s2) = (s1.clone(), s2.clone());
                self.assert_is_def_eq(&s1, &s2)
            }
            _ => {
                if self.try_structure_eta(&a, &b)? {
                    return Ok(())
                }
                if self.try_structure_eta(&b, &a)? {
                    return Ok(())
                }
                if self.try_fun_eta(&a, &b)? {
                    return Ok(())
                }
                if self.try_fun_eta(&b, &a)? {
                    return Ok(())
                }
                differ()
            }
        }
    }

    /// `defEqParams`. Note the original does not whnf here, and neither does
    /// the official kernel.
    fn def_eq_params(&mut self, n: u32, type1: &E, type2: &E) -> R<()> {
        if n == 0 {
            return Ok(())
        }
        let Expr::Forall { ty: d1, body: b1 } = &**type1 else {
            return Err(format!("Expected a function type, got {type1}"))
        };
        let Expr::Forall { ty: d2, body: b2 } = &**type2 else {
            return Err(format!("Expected a function type, got {type2}"))
        };
        let (d1, b1, b2) = (d1.clone(), b1.clone(), b2.clone());
        self.assert_is_def_eq(&d1, d2)?;
        self.scoped(|c| {
            c.push(d1.clone());
            c.def_eq_params(n - 1, &b1, &b2)
        })
    }

    // ──────────────────────────────── the inductive declaration zone ──

    /// `isValidIndApp`.
    fn is_valid_ind_app(&self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<()> {
        let (head, args) = get_app(ty);
        let Expr::Const(f, us) = &*head else {
            return Err(format!("Expected an application headed by the current inductive, got {ty}"))
        };
        if f != ic.ind_name {
            return Err(format!("Expected an application headed by the current inductive, got {ty}"))
        }
        if us.len() != ic.lparams.len()
            || us.iter().zip(ic.lparams.iter()).any(|(l, p)| *l != Level::Param(p.clone()))
        {
            return Err(format!("Level parameters do not match those of {} in {ty}", ic.ind_name))
        }
        if args.len() != (ic.num_params + ic.num_indices) as usize {
            return Err(format!(
                "Expected {} arguments, got {} in {ty}",
                ic.num_params + ic.num_indices,
                args.len()
            ))
        }
        for i in 0..ic.num_params {
            if *args[i as usize] != Expr::BVar(sh + ic.num_params - (i + 1)) {
                return Err(format!("Unexpected parameter {} in {ty}", i + 1))
            }
        }
        for i in ic.num_params as usize..args.len() {
            if has_const(ic.ind_name, &args[i]) {
                return Err(format!(
                    "Unexpected recursive occurrence of {} in index argument {} of {ty}",
                    ic.ind_name,
                    i + 1
                ))
            }
        }
        Ok(())
    }

    /// `checkCtorParam`: universe bound, then strict positivity.
    fn check_ctor_param(&mut self, ic: &IndCtx<'_>, sh: u32, ctor_param: &E) -> R<()> {
        let s = self.infer_type(ctor_param)?;
        let u = as_sort(&s)?;
        if !matches!(ic.ind_level, Level::Zero) {
            assert_level_le(&u, ic.ind_level)?;
        }
        let cp = self.whnf(ctor_param)?;
        if has_const(ic.ind_name, &cp) {
            self.scoped(|c| {
                let (m, ret) = c.open_forall_eager_push(&cp)?;
                for d in c.read_local_types(m)? {
                    if has_const(ic.ind_name, &d) {
                        return Err(format!(
                            "Not strictly positive: {} occurs in domain",
                            ic.ind_name
                        ))
                    }
                }
                c.is_valid_ind_app(ic, sh + m, &ret)
            })?;
        }
        Ok(())
    }

    /// `checkCtorType`. NB: no whnf, matching the official kernel.
    fn check_ctor_type(&mut self, ic: &IndCtx<'_>, sh: u32, ty: &E) -> R<()> {
        if let Expr::Forall { ty: domain, body } = &**ty {
            let (domain, body) = (domain.clone(), body.clone());
            self.check_ctor_param(ic, sh, &domain)?;
            self.scoped(|c| {
                c.push(domain.clone());
                c.check_ctor_type(ic, sh + 1, &body)
            })
        } else {
            self.is_valid_ind_app(ic, sh, ty)
        }
    }

    /// The `elimToSort` walk over a single constructor's telescope.
    fn elim_to_sort_go(&mut self, t: &E) -> R<bool> {
        let Expr::Forall { ty: domain, body } = &**t else { return Ok(true) };
        let (domain, body) = (domain.clone(), body.clone());
        let s = self.infer_type(&domain)?;
        let u = as_sort(&s)?;
        self.scoped(|c| {
            c.push(domain.clone());
            let appears = c.scoped(|c2| {
                let (sh, res) = c2.open_forall_eager_push(&body)?;
                let (_, args) = get_app(&res);
                Ok(args.iter().any(|a| **a == Expr::BVar(sh)))
            })?;
            if !(u.is_zero() || appears) {
                return Ok(false)
            }
            c.elim_to_sort_go(&body)
        })
    }

    /// The recursor's type: steps 1–6 of mini-lean's `recType` builder.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_type(
        &mut self,
        ind_name: &Name,
        ind_type: &E,
        ctors: &[(Name, E)],
        num_params: u32,
        num_indices: u32,
        us: &Rc<[Level]>,
        motive_level: &Level,
    ) -> R<E> {
        let num_ctors = u32::try_from(ctors.len()).expect("constructor count");
        self.scoped(|c| {
            // 1. Parameters
            let ind_type = c.open_forall_push(num_params, ind_type)?;
            // 2. Motive
            let motive_type = c.scoped(|c| {
                c.open_forall_push(num_indices, &ind_type)?;
                let mut a = bvars(num_params, num_indices);
                a.extend(bvars(num_indices, 0));
                let major_type = app_n(konst(ind_name.clone(), us.clone()), &a);
                c.push(major_type);
                c.mk_forall(num_indices + 1, sort(motive_level.clone()))
            })?;
            c.push(motive_type);
            // 3. Minors
            let mut minor_types: Vec<E> = Vec::new();
            for (ctor_name, ctor_type) in ctors {
                let mt = c.scoped(|c| {
                    let params = bvars(num_params, 1);
                    let ctor_type = c.instantiate_foralls(ctor_type, &params)?;
                    let (num_fields, ctor_res_type) = c.open_forall_eager_push(&ctor_type)?;
                    // Recursive fields get an induction hypothesis.
                    let mut hyp_types: Vec<E> = Vec::new();
                    for field in bvars(num_fields, 0) {
                        let t = c.infer_type(&field)?;
                        let t = c.whnf(&t)?;
                        if !has_const(ind_name, &t) {
                            continue
                        }
                        let hyp = c.scoped(|c| {
                            let (m, ret) = c.open_forall_eager_push(&t)?;
                            let (_, rargs) = get_app(&ret);
                            let mut a = slice(
                                &rargs,
                                num_params as usize,
                                (num_params + num_indices) as usize,
                            );
                            a.push(app_n(shift(&field, 0, m), &bvars(m, 0)));
                            let body = app_n(bvar(num_fields + m), &a);
                            c.mk_forall(m, body)
                        })?;
                        hyp_types.push(hyp);
                    }
                    let nh = u32::try_from(hyp_types.len()).expect("hypothesis count");
                    c.push_types(&hyp_types);
                    let ctor_res_type = shift(&ctor_res_type, 0, nh);
                    let mut a: Vec<E> =
                        params.iter().map(|p| shift(p, 0, num_fields + nh)).collect();
                    a.extend(bvars(num_fields, nh));
                    let ctor_app = app_n(konst(ctor_name.clone(), us.clone()), &a);
                    let (_, rargs) = get_app(&ctor_res_type);
                    let mut a2 =
                        slice(&rargs, num_params as usize, (num_params + num_indices) as usize);
                    a2.push(ctor_app);
                    let motive_app = app_n(bvar(num_fields + nh), &a2);
                    c.mk_forall(num_fields + nh, motive_app)
                })?;
                minor_types.push(mt);
            }
            c.push_types(&minor_types);
            // 4. Indices
            c.open_forall_push(num_indices, &shift(&ind_type, 0, 1 + num_ctors))?;
            // 5. Major argument
            let mut a = bvars(num_params, 1 + num_ctors + num_indices);
            a.extend(bvars(num_indices, 0));
            let major_type = app_n(konst(ind_name.clone(), us.clone()), &a);
            c.push(major_type);
            // 6. Result type: the motive applied to indices and major argument
            let mut a = bvars(num_indices, 1);
            a.push(bvar(0));
            let result_type = app_n(bvar(num_ctors + num_indices + 1), &a);
            c.mk_forall(num_params + 1 + num_ctors + num_indices + 1, result_type)
        })
    }

    /// One iota rule's RHS: the body of `fun params motive minors fields => …`.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_rule(
        &mut self,
        ind_name: &Name,
        rec_name: &Name,
        rec_type: &E,
        ctor_type: &E,
        i: u32,
        num_params: u32,
        num_indices: u32,
        num_ctors: u32,
        us2: &Rc<[Level]>,
    ) -> R<E> {
        self.scoped(|c| {
            c.open_forall_push(num_params + 1 + num_ctors, rec_type)?;
            let ctor_type =
                c.instantiate_foralls(ctor_type, &bvars(num_params, 1 + num_ctors))?;
            let (num_fields, _) = c.open_forall_eager_push(&ctor_type)?;
            let minor = bvar(num_ctors - (i + 1) + num_fields);
            let fields = bvars(num_fields, 0);
            let mut ihs: Vec<E> = Vec::new();
            for field in &fields {
                let t = c.infer_type(field)?;
                let t = c.whnf(&t)?;
                if !has_const(ind_name, &t) {
                    continue
                }
                let ih = c.scoped(|c| {
                    let (m, ret) = c.open_forall_eager_push(&t)?;
                    let (_, rargs) = get_app(&ret);
                    let mut a = bvars(num_params + 1 + num_ctors, num_fields + m);
                    a.extend(slice(
                        &rargs,
                        num_params as usize,
                        (num_params + num_indices) as usize,
                    ));
                    a.push(app_n(shift(field, 0, m), &bvars(m, 0)));
                    let body = app_n(konst(rec_name.clone(), us2.clone()), &a);
                    c.mk_lambda(m, body)
                })?;
                ihs.push(ih);
            }
            let mut a = fields;
            a.extend(ihs);
            Ok(app_n(minor, &a))
        })
    }
}

// ────────────────────────────────────────────────── Environment.add ──

fn nodup(lparams: &[Name], name: &Name) -> R<()> {
    for (i, p) in lparams.iter().enumerate() {
        if lparams[i + 1..].contains(p) {
            return Err(format!("Duplicate level parameters in declaration of {name}"))
        }
    }
    Ok(())
}

/// `Environment.addQuot`, ported verbatim.
pub fn add_quot(env: &mut Environment) -> R<()> {
    let quot_name = Name::simple("Quot");
    let quot_mk_name = Name::str(&quot_name, "mk");
    let quot_lift_name = Name::str(&quot_name, "lift");
    let quot_ind_name = Name::str(&quot_name, "ind");
    let u = Name::simple("u");
    let v = Name::simple("v");
    let prop = sort(Level::Zero);
    let sort_u = sort(Level::Param(u.clone()));
    let sort_v = sort(Level::Param(v.clone()));
    let eq_name = Name::simple("Eq");

    let aar_prop = |i: u32| arrow(bvar(i), arrow(bvar(i + 1), prop.clone()));
    let mk_quot = |a: u32, r: u32| {
        app(app(konst(quot_name.clone(), levels(&[Level::Param(u.clone())])), bvar(a)), bvar(r))
    };

    // Quot : ∀ (α : Sort u) (_ : α → α → Prop), Sort u
    let quot_type = arrow(sort_u.clone(), arrow(aar_prop(0), sort_u.clone()));
    // Quot.mk : ∀ (α : Sort u) (r : α → α → Prop) (a : α), @Quot α r
    let quot_mk_type =
        arrow(sort_u.clone(), arrow(aar_prop(0), arrow(bvar(1), mk_quot(2, 1))));
    // Quot.lift
    let f_type = arrow(bvar(2), bvar(1));
    let h_type = arrow(
        bvar(3),
        arrow(
            bvar(4),
            arrow(
                app(app(bvar(4), bvar(1)), bvar(0)),
                app(
                    app(
                        app(konst(eq_name, levels(&[Level::Param(v.clone())])), bvar(4)),
                        app(bvar(3), bvar(2)),
                    ),
                    app(bvar(3), bvar(1)),
                ),
            ),
        ),
    );
    let quot_lift_type = arrow(
        sort_u.clone(),
        arrow(
            aar_prop(0),
            arrow(sort_v, arrow(f_type, arrow(h_type, arrow(mk_quot(4, 3), bvar(3))))),
        ),
    );
    // Quot.ind
    let beta_ind_type = arrow(mk_quot(1, 0), prop.clone());
    let h_ind_type = arrow(
        bvar(2),
        app(
            bvar(1),
            app(
                app(
                    app(konst(quot_mk_name.clone(), levels(&[Level::Param(u.clone())])), bvar(3)),
                    bvar(2),
                ),
                bvar(0),
            ),
        ),
    );
    let quot_ind_type = arrow(
        sort_u,
        arrow(
            aar_prop(0),
            arrow(beta_ind_type, arrow(h_ind_type, arrow(mk_quot(3, 2), app(bvar(2), bvar(0))))),
        ),
    );

    let lift_info = ConstantInfo::Recursor {
        lparams: vec![u.clone(), v],
        ty: quot_lift_type,
        num_params: 2,
        num_minors: 2,
        num_indices: 0,
        rules: vec![(quot_mk_name.clone(), app(bvar(2), bvar(0)))],
        k_type: None,
    };
    let ind_info = ConstantInfo::Recursor {
        lparams: vec![u.clone()],
        ty: quot_ind_type,
        num_params: 2,
        num_minors: 1,
        num_indices: 0,
        rules: vec![(quot_mk_name.clone(), app(bvar(1), bvar(0)))],
        k_type: None,
    };
    env.insert_new(quot_name, ConstantInfo::Opaque { lparams: vec![u.clone()], ty: quot_type })?;
    env.insert_new(
        quot_mk_name,
        ConstantInfo::Opaque { lparams: vec![u], ty: quot_mk_type },
    )?;
    env.insert_new(quot_lift_name, lift_info)?;
    env.insert_new(quot_ind_name, ind_info)
}

/// `Environment.add`.
///
/// Mini-lean's version is functional (`Except String Environment`), so a
/// rejected declaration leaves the environment untouched. This one mutates,
/// which is observably the same because the only caller aborts the file on the
/// first rejection — mini-lean's `--liberal` mode is not ported.
pub fn add(env: &mut Environment, decl: &Declaration) -> R<()> {
    match decl {
        Declaration::Axiom { name, lparams, ty } => {
            nodup(lparams, name)?;
            {
                let mut c = Checker::new(env);
                c.infer_type(ty)
                    .map_err(|e| format!("{e}\n… while checking declaration {name}"))?;
            }
            env.insert_new(
                name.clone(),
                ConstantInfo::Opaque { lparams: lparams.clone(), ty: ty.clone() },
            )
        }
        Declaration::Def { name, lparams, ty, value, kind } => {
            nodup(lparams, name)?;
            {
                let mut c = Checker::new(env);
                let go = |c: &mut Checker<'_>| -> R<()> {
                    let s = c.infer_type(ty)?;
                    let u = as_sort(&s)?;
                    if matches!(kind, DefKind::Theorem) && !u.is_zero() {
                        return Err(format!(
                            "The type of a theorem must be a proposition, but {ty} has universe {u}"
                        ))
                    }
                    let ty2 = c.infer_type(value)?;
                    c.assert_is_def_eq(ty, &ty2)
                };
                go(&mut c).map_err(|e| format!("{e}\n… while checking declaration {name}"))?;
            }
            let cinfo = match kind {
                DefKind::Def | DefKind::Theorem => ConstantInfo::Def {
                    lparams: lparams.clone(),
                    ty: ty.clone(),
                    value: value.clone(),
                },
                DefKind::Opaque => {
                    ConstantInfo::Opaque { lparams: lparams.clone(), ty: ty.clone() }
                }
            };
            env.insert_new(name.clone(), cinfo)
        }
        Declaration::Quot => add_quot(env),
        Declaration::Inductive { name: ind_name, lparams, num_params, ty: ind_type, ctors } => {
            add_inductive(env, ind_name, lparams, *num_params, ind_type, ctors)
        }
    }
}

fn add_inductive(
    env: &mut Environment,
    ind_name: &Name,
    lparams: &[Name],
    num_params: u32,
    ind_type: &E,
    ctors: &[(Name, E)],
) -> R<()> {
    nodup(lparams, ind_name)?;
    let num_ctors = u32::try_from(ctors.len()).expect("constructor count");

    // The type of the inductive: its indices and its universe.
    let (num_indices, ind_level) = {
        let mut c = Checker::new(env);
        let go = |c: &mut Checker<'_>| -> R<(u32, Level)> {
            c.check_type(ind_type)?;
            c.scoped(|c| {
                let t = c.open_forall_push(num_params, ind_type)?;
                let (ni, t) = c.open_forall_eager_push(&t)?;
                Ok((ni, as_sort(&t)?))
            })
        };
        go(&mut c)
            .map_err(|e| format!("{e}\n… while checking type of inductive {ind_name}"))?
    };

    // A "unit-like" type: one constructor, no fields.
    let is_unit = if ctors.len() == 1 {
        let mut c = Checker::new(env);
        c.scoped(|c| {
            let t = c.open_forall_push(num_params, &ctors[0].1)?;
            Ok(!matches!(&*t, Expr::Forall { .. }))
        })?
    } else {
        false
    };

    env.insert_new(
        ind_name.clone(),
        ConstantInfo::Inductive {
            lparams: lparams.to_vec(),
            ty: ind_type.clone(),
            num_params,
            num_indices,
            ctors: ctors.iter().map(|(n, _)| n.clone()).collect(),
            is_unit,
        },
    )?;

    // Constructor checks, with the inductive already in the environment.
    {
        let ic = IndCtx { ind_name, lparams, num_params, num_indices, ind_level: &ind_level };
        let mut c = Checker::new(env);
        for (ctor_name, ctor_type) in ctors {
            c.check_type(ctor_type)
                .map_err(|e| format!("{e}\n… while checking type of constructor {ctor_name}"))?;
            c.def_eq_params(num_params, ind_type, ctor_type).map_err(|e| {
                format!(
                    "{e}\n… while checking parameters of constructor {ctor_name} match those of {ind_name}"
                )
            })?;
            c.scoped(|c| {
                let t = c.open_forall_push(num_params, ctor_type)?;
                c.check_ctor_type(&ic, 0, &t)
            })
            .map_err(|e| format!("{e}\n… while checking constructor {ctor_name}"))?;
        }
    }

    for (ctor_name, ctor_type) in ctors {
        env.insert_new(
            ctor_name.clone(),
            ConstantInfo::Opaque { lparams: lparams.to_vec(), ty: ctor_type.clone() },
        )?;
    }

    // Large elimination?
    let elim_to_sort = {
        if ind_level.is_not_zero() {
            true
        } else if num_ctors == 0 {
            // TODO (mini-lean's own): mutual inductives should return false.
            true
        } else if num_ctors > 1 {
            false
        } else {
            let mut c = Checker::new(env);
            c.elim_to_sort_go(&ctors[0].1)?
        }
    };

    // The K-rule applies to an inductive proposition with one fieldless ctor.
    let k_type = {
        if ind_level.is_not_zero() || ctors.len() != 1 {
            None
        } else {
            let mut c = Checker::new(env);
            c.scoped(|c| {
                let t = c.open_forall_push(num_params, &ctors[0].1)?;
                Ok(if matches!(&*t, Expr::Forall { .. }) { None } else { Some(t) })
            })?
        }
    };

    let (motive_level, lparams2) = if elim_to_sort {
        let v = fresh_level_name(lparams);
        let mut l = vec![v.clone()];
        l.extend(lparams.iter().cloned());
        (Level::Param(v), l)
    } else {
        (Level::Zero, lparams.to_vec())
    };
    let us: Rc<[Level]> =
        lparams.iter().map(|n| Level::Param(n.clone())).collect::<Vec<_>>().into();
    let us2: Rc<[Level]> =
        lparams2.iter().map(|n| Level::Param(n.clone())).collect::<Vec<_>>().into();

    let rec_type = {
        let mut c = Checker::new(env);
        let rec_type = c.build_rec_type(
            ind_name,
            ind_type,
            ctors,
            num_params,
            num_indices,
            &us,
            &motive_level,
        )?;
        // Sanity check, at the recursor's own (symbolic) level parameters.
        c.check_type(&rec_type).map_err(|e| {
            format!("{e}\n… while checking type of recursor for {ind_name}:\n{rec_type}")
        })?;
        rec_type
    };

    let rec_name = Name::str(ind_name, "rec");
    let mut rules: Vec<(Name, E)> = Vec::new();
    for (i, (ctor_name, ctor_type)) in ctors.iter().enumerate() {
        let mut c = Checker::new(env);
        let rhs = c.build_rec_rule(
            ind_name,
            &rec_name,
            &rec_type,
            ctor_type,
            u32::try_from(i).expect("constructor index"),
            num_params,
            num_indices,
            num_ctors,
            &us2,
        )?;
        rules.push((ctor_name.clone(), rhs));
    }

    env.insert_new(
        rec_name,
        ConstantInfo::Recursor {
            lparams: lparams2,
            ty: rec_type,
            num_params,
            num_minors: num_ctors,
            num_indices,
            rules,
            k_type,
        },
    )
}
