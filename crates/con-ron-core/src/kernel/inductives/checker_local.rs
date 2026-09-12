//! The pieces of `ConLeche/Kernel/CheckerBase.lean` and
//! `ConLeche/Kernel/DeclCheck.lean` that the two inductive install routes
//! need — and nothing else.
//!
//! **Temporary, and owed to task #24.**  Those two files are that task's
//! (`kernel/checker*.rs`); this module exists so that task #25 can land the
//! `Inductives/*` routes without touching another task's files.  Every item
//! carries its con-leche citation, and the unification is a move plus a `use`
//! — no caller spells a body.  Nothing here is a stub: each function is the
//! cited text, transliterated under the same rules as the rest of the
//! directory (see `super`'s module note: one `fe: &FEnv` spelling, no
//! `CheckerOps` record, wrapper calls at `core_k::check_fuel()`).
//!
//! One item is owed elsewhere: `Expr.allLevelParamsDefined`
//! (`Kernel/Level.lean:256-300`) belongs in `kernel/level.rs`, which task #13
//! recorded as still owed.  It is here because the recursor and projection
//! stages are its first consumers.

use crate::cached::core_c;
use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::{CheckError, CheckM};
use crate::kernel::env;
use crate::kernel::env::{
    CheckMode, ConstantInfo, ConstantVal, IndCaps, ProjTable, RecRule, RecRuleFire,
    ReducibilityHint,
};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::inductives::struct_parts;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::ron::hashmap::HashMap;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// `unwrapOr` and the telescope opener (`CheckerBase.lean:105-154, 212-217`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:211-217 unwrapOr
/// Unwrap an optional value or fail with the given error.  Generic, as the
/// cited definition is; the error is built eagerly on both branches, which is
/// Lean's own strictness here.
pub fn unwrap_or<T>(o: Option<T>, err: CheckError) -> CheckM<T> {
    match o {
        Some(a) => Ok(a),
        None => Err(err),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:108-118 openPisAtFvars
/// The *specification* of the telescope opener: open the first `n`
/// `∀`-binders at fresh free variables `i .. i+n-1`, each fvar's type the
/// binder domain instantiated with the earlier fvars.  One whole-telescope
/// `instantiate1` pass per binder; the executed one is `open_pis_at_fvars`
/// below.  Ported so the provenance gate stays in step with its source.
pub fn open_pis_at_fvars_spec(n: u64, e: &Expr, i: u64) -> Option<(Vec<Expr>, Expr)> {
    if n == 0 {
        Some((Vec::new(), expr::dup(e)))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(dom, body, _) => {
                let fv: Expr = expr::fvar(i, expr::dup(dom));
                let opened: Expr = expr_ops::instantiate1(body, &fv, 0);
                match open_pis_at_fvars_spec(n - 1, &opened, i + 1) {
                    Some(q) => {
                        let mut fvs: Vec<Expr> = Vec::new();
                        fvs.push(fv);
                        fvs = core_k::append_exprs(fvs, &q.0);
                        Some((fvs, q.1))
                    }
                    None => None,
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:131-145 openPisAtFvarsFGo
/// The one-pass core: `acc` holds the already-created fvars, innermost binder
/// first; one `instantiateList` pass per domain instead of one
/// whole-telescope `instantiate1` pass per binder.
///
/// Deviation: Lean conses `fv` on the result on the way *out*; the port
/// carries an out-parameter `fvs` accumulated on the way *in*, which is the
/// same outermost-first list (task #13's pattern 3).  `acc` needs the *front*
/// cons the Lean spells, so it is rebuilt per binder (task #13's `cons_expr`
/// note): `O(|acc|)` pointer copies per binder of a telescope.
pub fn open_pis_at_fvars_f_go(
    acc: &Vec<Expr>,
    n: u64,
    e: &Expr,
    i: u64,
    fvs: Vec<Expr>,
) -> Option<(Vec<Expr>, Expr)> {
    if n == 0 {
        Some((fvs, expr_ops::instantiate_list(e, acc, 0)))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(dom, body, _) => {
                let fv: Expr = expr::fvar(i, expr_ops::instantiate_list(dom, acc, 0));
                let mut acc2: Vec<Expr> = Vec::new();
                acc2.push(expr::dup(&fv));
                acc2 = core_k::append_exprs(acc2, acc);
                let mut fvs = fvs;
                fvs.push(fv);
                open_pis_at_fvars_f_go(&acc2, n - 1, body, i + 1, fvs)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:147-154 openPisAtFvarsF
/// con-leche: ConLeche/Kernel/CheckerBase.lean:108-118 openPisAtFvars
/// **The executed telescope opener** — the one-pass walk with the cited
/// fallback for telescopes whose binders only appear after substitution
/// (`openPisAtFvarsF_eq` is the equation that makes this the port of both).
pub fn open_pis_at_fvars(n: u64, e: &Expr, i: u64) -> Option<(Vec<Expr>, Expr)> {
    match open_pis_at_fvars_f_go(&Vec::new(), n, e, i, Vec::new()) {
        Some(r) => Some(r),
        None => open_pis_at_fvars_spec(n, e, i),
    }
}

// ---------------------------------------------------------------------------
// `domsMatchAux` (`CheckerBase.lean:97-103, 120-129`)
// ---------------------------------------------------------------------------

/// con-leche: none — replaces the `g : Nat → Expr → Expr` argument of `domsMatchAux`
/// The one-method trait that stands for a Lean function argument (task #9's
/// pattern 1; §3.4 forbids closures).  Aeneas renders it as a dictionary
/// threaded through the recursion.
pub trait DomView {
    /// con-leche: none — the `g` of `domsMatchAux g`
    fn view(&self, i: u64, e: &Expr) -> Expr;
}

/// con-leche: none — `domsMatchAux (fun _ e => e)`, the identity view
/// Three of the four call sites pass the identity (`checkProjRule`,
/// `checkEtaThm`, `checkUnitThm`).
pub struct DomIdent;

/// con-leche: ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux
impl DomView for DomIdent {
    /// con-leche: none — `fun _ e => e`
    fn view(&self, _i: u64, e: &Expr) -> Expr {
        expr::dup(e)
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux
/// con-leche: ConLeche/Kernel/CheckerBase.lean:120-129 domsMatchAuxA
/// Compare binder domains at offsets `o₁`/`o₂` for `n` positions, the right
/// side viewed through `g`.  The `Array` twin (`domsMatchAuxA`, equal at
/// `List.toArray`) is the same function: the port has one list type.
pub fn doms_match_aux<G>(
    g: &G,
    bs1: &Vec<(Expr, BinderMeta)>,
    bs2: &Vec<(Expr, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
) -> bool
where
    G: DomView,
{
    doms_match_aux_from(g, bs1, bs2, o1, o2, n, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux
/// The `(List.range n).all` behind `doms_match_aux`.
pub fn doms_match_aux_from<G>(
    g: &G,
    bs1: &Vec<(Expr, BinderMeta)>,
    bs2: &Vec<(Expr, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
    i: u64,
) -> bool
where
    G: DomView,
{
    if i >= n {
        true
    } else if ((o1 + i) as usize) >= bs1.len() {
        false
    } else if ((o2 + i) as usize) >= bs2.len() {
        false
    } else {
        let viewed: Expr = g.view(i, &bs2[(o2 + i) as usize].0);
        if expr::beq(&bs1[(o1 + i) as usize].0, &viewed) {
            doms_match_aux_from(g, bs1, bs2, o1, o2, n, i + 1)
        } else {
            false
        }
    }
}

// ---------------------------------------------------------------------------
// `allLevelParamsDefined` (`Kernel/Level.lean:256-311`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// Are all level parameters of `e` — the binder data's included — declared?
/// The *logical* definition; the executed one is
/// `all_level_params_defined` below (the `@[csimp]` family, as in
/// `struct_parts`).  Ported so the provenance gate stays in step.
pub fn all_level_params_defined_spec(params: &Vec<Name>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => true,
        ExprKind::Fvar(_, t) => all_level_params_defined_spec(params, t),
        ExprKind::Sort(u) => level::all_params_defined(params, u),
        ExprKind::Const(_, us) => levels_defined_from(params, us, 0),
        ExprKind::Lit(_) => true,
        ExprKind::App(f, a) => {
            if all_level_params_defined_spec(params, f) {
                all_level_params_defined_spec(params, a)
            } else {
                false
            }
        }
        ExprKind::Lam(t, b, m) => {
            if all_level_params_defined_spec(params, t) {
                if all_level_params_defined_spec(params, b) {
                    prop_when::params_defined(params, &m.pw)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprKind::ForallE(t, b, m) => {
            if all_level_params_defined_spec(params, t) {
                if all_level_params_defined_spec(params, b) {
                    prop_when::params_defined(params, &m.pw)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprKind::LetE(t, v, b) => {
            if all_level_params_defined_spec(params, t) {
                if all_level_params_defined_spec(params, v) {
                    all_level_params_defined_spec(params, b)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprKind::Proj(_, _, sub) => all_level_params_defined_spec(params, sub),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// `us.all (Level.allParamsDefined params)`, as an index recursion.
pub fn levels_defined_from(params: &Vec<Name>, us: &Vec<Level>, i: usize) -> bool {
    if i >= us.len() {
        true
    } else if level::all_params_defined(params, &us[i]) {
        levels_defined_from(params, us, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// The memoized walk: the four leaf arms answer before the probe, every other
/// node is probed, walked and recorded.  As in `mentionsConstGo` the cited
/// walk does **not** short-circuit its `&&`s — both children are walked so
/// that the memo it hands back holds both answers — and the port keeps that.
pub fn all_level_params_defined_go(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    e: &Expr,
) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => true,
        ExprKind::Sort(u) => level::all_params_defined(params, u),
        ExprKind::Const(_, us) => levels_defined_from(params, us, 0),
        ExprKind::Lit(_) => true,
        _ => match struct_parts::memo_eb_get(memo, e) {
            Some(r) => r,
            None => {
                let r = all_level_params_defined_node(params, memo, e);
                memo.insert(expr::dup(e), r);
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// The inner `match e with` of the miss branch, split off so the probe's
/// borrow dies before the descent mutates the memo (task #14's rule).  The
/// last arm is the cited unreachable one.
pub fn all_level_params_defined_node(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    e: &Expr,
) -> bool {
    match &e.0.kind {
        ExprKind::Fvar(_, t) => all_level_params_defined_go(params, memo, t),
        ExprKind::App(f, a) => {
            let b1 = all_level_params_defined_go(params, memo, f);
            let b2 = all_level_params_defined_go(params, memo, a);
            if b1 {
                b2
            } else {
                false
            }
        }
        ExprKind::Lam(t, b, m) => {
            let b1 = all_level_params_defined_go(params, memo, t);
            let b2 = all_level_params_defined_go(params, memo, b);
            if b1 {
                if b2 {
                    prop_when::params_defined(params, &m.pw)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprKind::ForallE(t, b, m) => {
            let b1 = all_level_params_defined_go(params, memo, t);
            let b2 = all_level_params_defined_go(params, memo, b);
            if b1 {
                if b2 {
                    prop_when::params_defined(params, &m.pw)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprKind::LetE(t, v, b) => {
            let b1 = all_level_params_defined_go(params, memo, t);
            let b2 = all_level_params_defined_go(params, memo, v);
            let b3 = all_level_params_defined_go(params, memo, b);
            if b1 {
                if b2 {
                    b3
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprKind::Proj(_, _, sub) => all_level_params_defined_go(params, memo, sub),
        _ => all_level_params_defined_spec(params, e),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:405-407 Expr.allLevelParamsDefinedFast
/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// **The executed `allLevelParamsDefined`** — one memoized DAG walk with a
/// per-call memo.
pub fn all_level_params_defined(params: &Vec<Name>, e: &Expr) -> bool {
    let mut memo: HashMap<Expr, bool> = HashMap::new();
    all_level_params_defined_go(params, &mut memo, e)
}

// ---------------------------------------------------------------------------
// The `Eq` head readers and the stored-constant reader
// (`CheckerBase.lean:186-198, 219-224`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:186-189 isEqHead
/// Is the expression the pinned equality former at one level?
pub fn is_eq_head(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Const(c, us) => {
            if us.len() == 1 {
                name::beq(c, &basis_names::eq_name())
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:191-198 eqHeadLevel
/// The level an equality head carries — the statement's own `Eq.{ℓ}` level,
/// read off a head `isEqHead` has accepted.  Off shape it is `.zero`, which
/// `isEqHead` has already rejected wherever the result is used.
pub fn eq_head_level(e: &Expr) -> Level {
    match &e.0.kind {
        ExprKind::Const(_, us) => {
            if us.len() == 1 {
                level::dup(&us[0])
            } else {
                level::zero()
            }
        }
        _ => level::zero(),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:219-225 Env.findCV?
/// con-leche: ConLeche/Kernel/DeclCheck.lean:33-35 FEnv.findCV?
/// The stored constant under `n`, as a `ConstantVal`, if any.  The
/// iota-certificate checks consume only the stored constant's *type*, so no
/// theorem-kind filter is imposed.
pub fn find_cv(fe: &FEnv, n: &Name) -> Option<ConstantVal> {
    match fenv::find(fe, n) {
        Some(ci) => Some(env::to_constant_val(ci)),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// `checkConstantVal` (`CheckerBase.lean:72-96` / `DeclCheck.lean:463-485`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:73-97 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
/// Checks common to all declarations: fresh name, well-formed universe
/// parameters, and a type that is a type and mentions only declared
/// parameters.  Returns the constant with its type **annotated**; the guards
/// run on the annotated type.
///
/// Deviations: the six interpolated messages drop their interpolation (§3.1:
/// message strings need not match), and every `ops.*` is the `core_c`/`core_k`
/// wrapper at `core_k::check_fuel()` (`super`'s module note 2).
pub fn check_constant_val(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
) -> CheckM<ConstantVal> {
    const M_DUP: [u32; 21] = [
        100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116,
        105, 111, 110,
    ];
    const M_RESERVED: [u32; 19] = [
        114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109,
        101,
    ];
    const M_PROJ: [u32; 24] = [
        114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105,
        111, 110, 32, 110, 97, 109, 101,
    ];
    const M_LPS: [u32; 29] = [
        100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101,
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
    ];
    const M_BVAR: [u32; 26] = [
        108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98,
        108, 101, 32, 105, 110, 32, 116, 121,
    ];
    const M_FVAR: [u32; 26] = [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97,
        114, 105, 97, 98, 108, 101, 32, 32,
    ];
    const M_UNDECL: [u32; 32] = [
        117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115,
        101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110,
    ];
    const M_UNKNOWN: [u32; 17] = [
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32,
    ];
    if fenv::find(fe, &cv.name).is_some() {
        Err(core_types::invalid(core_types::code_points(&M_DUP)))
    } else if name::contains(&basis_names::reserved_basis_names(), &cv.name) {
        Err(core_types::invalid(core_types::code_points(&M_RESERVED)))
    } else if level::name_is_proj_fn_shape(&cv.name) {
        Err(core_types::invalid(core_types::code_points(&M_PROJ)))
    } else if !level::name_nodup(&cv.level_params) {
        Err(core_types::invalid(core_types::code_points(&M_LPS)))
    } else if !expr_ops::loose_bvars_bounded(0, &cv.ty) {
        Err(core_types::invalid(core_types::code_points(&M_BVAR)))
    } else if expr_ops::has_fvar(&cv.ty) {
        Err(core_types::invalid(core_types::code_points(&M_FVAR)))
    } else {
        match core_c::annotate(mode, core_k::check_fuel(), st, fe, 0, &cv.ty) {
            Err(err) => Err(err),
            Ok(ty) => {
                if !all_level_params_defined(&cv.level_params, &ty) {
                    Err(core_types::invalid(core_types::code_points(&M_UNDECL)))
                } else if !core_k::consts_resolve(fe, &ty) {
                    Err(core_types::invalid(core_types::code_points(&M_UNKNOWN)))
                } else {
                    match core_c::infer(mode, core_k::check_fuel(), st, fe, 0, &ty) {
                        Err(err) => Err(err),
                        Ok(stype) => match core_k::ensure_sort(
                            mode,
                            core_k::check_fuel(),
                            st,
                            fe,
                            0,
                            &stype,
                        ) {
                            Err(err) => Err(err),
                            Ok(_u) => Ok(ConstantVal {
                                name: name::dup(&cv.name),
                                level_params: prop_when::names_copy(&cv.level_params),
                                ty,
                            }),
                        },
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The three list certifiers (`CheckerBase.lean:156-184, 200-210`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:156-168 checkTypedList
/// Check each expression's inferred type against the corresponding expected
/// type (definitionally); throws on a length mismatch.
pub fn check_typed_list(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    as_: &Vec<Expr>,
    ts: &Vec<Expr>,
) -> CheckM<()> {
    check_typed_list_from(mode, st, fe, depth, as_, ts, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:156-168 checkTypedList
/// The index recursion behind `check_typed_list`; the `| _, _ =>` arm is the
/// cited arity throw.
pub fn check_typed_list_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    as_: &Vec<Expr>,
    ts: &Vec<Expr>,
    i: usize,
) -> CheckM<()> {
    const M_ARITY: [u32; 24] = [
        110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 114, 105, 116, 121, 32, 109,
        105, 115, 109, 97, 116, 99,
    ];
    const M_TY: [u32; 23] = [
        110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 116, 121, 112, 101, 32, 109, 105,
        115, 109, 97, 116, 99,
    ];
    if i >= as_.len() {
        if i >= ts.len() {
            Ok(())
        } else {
            Err(core_types::not_implemented(core_types::code_points(
                &M_ARITY,
            )))
        }
    } else if i >= ts.len() {
        Err(core_types::not_implemented(core_types::code_points(
            &M_ARITY,
        )))
    } else {
        match core_c::infer(mode, core_k::check_fuel(), st, fe, depth, &as_[i]) {
            Err(err) => Err(err),
            Ok(ty) => match core_c::defeq(
                mode,
                core_k::check_fuel(),
                st,
                fe,
                depth,
                &ty,
                &ts[i],
            ) {
                Err(err) => Err(err),
                Ok(true) => {
                    check_typed_list_from(mode, st, fe, depth, as_, ts, i + 1)
                }
                Ok(false) => Err(core_types::not_implemented(core_types::code_points(
                    &M_TY,
                ))),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:170-184 checkAnnotList
/// Check that each expression is a fixed point of the annotation pass in the
/// given context: its codomain-sort annotations are exactly the ones
/// annotation reconstructs.
pub fn check_annot_list(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    as_: &Vec<Expr>,
) -> CheckM<()> {
    check_annot_list_from(mode, st, fe, depth, as_, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:170-184 checkAnnotList
/// The index recursion behind `check_annot_list`.
pub fn check_annot_list_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    as_: &Vec<Expr>,
    i: usize,
) -> CheckM<()> {
    const M: [u32; 29] = [
        110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 110, 110, 111, 116, 97, 116,
        105, 111, 110, 32, 109, 105, 115, 109, 97, 116, 99,
    ];
    if i >= as_.len() {
        Ok(())
    } else {
        match core_c::annotate(mode, core_k::check_fuel(), st, fe, depth, &as_[i]) {
            Err(err) => Err(err),
            Ok(a_a) => {
                if expr::beq(&a_a, &as_[i]) {
                    check_annot_list_from(mode, st, fe, depth, as_, i + 1)
                } else {
                    Err(core_types::not_implemented(core_types::code_points(&M)))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:200-209 checkDefEqList
/// Pairwise definitional-equality check of two spines (throws on any
/// mismatch, including a length difference).
pub fn check_def_eq_list(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    as_: &Vec<Expr>,
    bs: &Vec<Expr>,
) -> CheckM<()> {
    check_def_eq_list_from(mode, st, fe, depth, as_, bs, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:200-209 checkDefEqList
/// The index recursion behind `check_def_eq_list`; the `| _, _ =>` arm is the
/// cited arity throw.
pub fn check_def_eq_list_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    as_: &Vec<Expr>,
    bs: &Vec<Expr>,
    i: usize,
) -> CheckM<()> {
    const M_ARITY: [u32; 30] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109,
        112, 111, 110, 101, 110, 116, 32, 97, 114, 105, 116, 121,
    ];
    const M_MIS: [u32; 32] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109,
        112, 111, 110, 101, 110, 116, 32, 109, 105, 115, 109, 97, 116, 99,
    ];
    if i >= as_.len() {
        if i >= bs.len() {
            Ok(())
        } else {
            Err(core_types::not_implemented(core_types::code_points(
                &M_ARITY,
            )))
        }
    } else if i >= bs.len() {
        Err(core_types::not_implemented(core_types::code_points(
            &M_ARITY,
        )))
    } else {
        match core_c::defeq(
            mode,
            core_k::check_fuel(),
            st,
            fe,
            depth,
            &as_[i],
            &bs[i],
        ) {
            Err(err) => Err(err),
            Ok(true) => check_def_eq_list_from(mode, st, fe, depth, as_, bs, i + 1),
            Ok(false) => Err(core_types::not_implemented(core_types::code_points(
                &M_MIS,
            ))),
        }
    }
}

// ---------------------------------------------------------------------------
// The two projection stages of `CheckerBase.lean` (`:233-289`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:235-250 checkProjShape
/// Stage 2b: the projection type's parameter telescope is *syntactically* the
/// constructor's, and the constructor's residual is the family applied to
/// exactly the parameters.
pub fn check_proj_shape(pty: &Expr, ctor_ty: &Expr, n_p: u64, n_f: u64) -> CheckM<()> {
    const M_PTY: [u32; 27] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    const M_CTY: [u32; 34] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    const M_ARITY: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 101, 115, 105, 100, 117, 97,
        108, 32, 97, 114, 105, 116, 121, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_HEAD: [u32; 31] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 101, 115, 105, 100, 117, 97,
        108, 32, 104, 101, 97, 100, 32, 32, 32, 32, 32, 32, 32,
    ];
    match expr_ops::strip_pis(n_p, pty) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_PTY))),
        Some(_) => match expr_ops::strip_pis(n_p + n_f, ctor_ty) {
            None => Err(core_types::not_implemented(core_types::code_points(&M_CTY))),
            Some(q) => {
                let args: Vec<Expr> = expr_ops::get_app_args(&q.1);
                if args.len() as u64 != n_p {
                    Err(core_types::not_implemented(core_types::code_points(
                        &M_ARITY,
                    )))
                } else {
                    let head: Expr = expr_ops::get_app_fn(&q.1);
                    match &head.0.kind {
                        ExprKind::Const(_, _) => Ok(()),
                        _ => Err(core_types::not_implemented(core_types::code_points(
                            &M_HEAD,
                        ))),
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:252-289 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// Stage 3: the reduction rule — λ over the constructor telescope returning
/// field `i`, annotated; its λ-domains stay the constructor's, and the frame
/// walks pin the parameter and domain annotations definitionally.
///
/// Deviation: the cited `let some … | throw` cascade is a `match` nest, so
/// every failure arm stays a tail position (task #18's pattern 3).
pub fn check_proj_rule(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    pty: &Expr,
    cvj: &ConstantVal,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> CheckM<Expr> {
    const M_TELE: [u32; 27] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    const M_SCOPE: [u32; 24] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 115, 99,
        111, 112, 105, 110, 103, 32,
    ];
    const M_WF: [u32; 32] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 119, 101,
        108, 108, 102, 111, 114, 109, 101, 100, 110, 101, 115, 115, 32, 32,
    ];
    const M_BODY: [u32; 22] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 98, 111,
        100, 121, 32, 32,
    ];
    const M_CTY: [u32; 34] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    const M_DOM: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 100, 111,
        109, 97, 105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
    ];
    match expr_ops::pis_to_lams(
        n_p + n_f,
        &cvj.ty,
        &expr::bvar(expr_ops::sub_nat(n_f, 1 + i)),
    ) {
        None => Err(core_types::not_implemented(core_types::code_points(
            &M_TELE,
        ))),
        Some(rhs) => {
            let scope_ok = if !expr_ops::has_fvar(&rhs) {
                expr_ops::loose_bvars_bounded(0, &rhs)
            } else {
                false
            };
            if !scope_ok {
                Err(core_types::not_implemented(core_types::code_points(
                    &M_SCOPE,
                )))
            } else {
                match core_c::annotate(mode, core_k::check_fuel(), st, fe, 0, &rhs) {
                    Err(err) => Err(err),
                    Ok(rhs_a) => {
                        let wf = if all_level_params_defined(lps, &rhs_a) {
                            if core_k::consts_resolve(fe, &rhs_a) {
                                if expr_ops::loose_bvars_bounded(0, &rhs_a) {
                                    !expr_ops::has_fvar(&rhs_a)
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        } else {
                            false
                        };
                        if !wf {
                            Err(core_types::not_implemented(core_types::code_points(&M_WF)))
                        } else {
                            match expr_ops::strip_lams(n_p + n_f, &rhs_a) {
                                None => Err(core_types::not_implemented(
                                    core_types::code_points(&M_TELE),
                                )),
                                Some(rq) => {
                                    if !expr::beq(
                                        &rq.1,
                                        &expr::bvar(expr_ops::sub_nat(n_f, 1 + i)),
                                    ) {
                                        Err(core_types::not_implemented(
                                            core_types::code_points(&M_BODY),
                                        ))
                                    } else {
                                        match expr_ops::strip_pis(n_p + n_f, &cvj.ty) {
                                            None => Err(core_types::not_implemented(
                                                core_types::code_points(&M_CTY),
                                            )),
                                            Some(cq) => {
                                                if !doms_match_aux(
                                                    &DomIdent,
                                                    &rq.0,
                                                    &cq.0,
                                                    0,
                                                    0,
                                                    n_p + n_f,
                                                ) {
                                                    Err(core_types::not_implemented(
                                                        core_types::code_points(&M_DOM),
                                                    ))
                                                } else {
                                                    check_proj_rule_frames(
                                                        mode, st, fe, pty, cvj, n_p, n_f,
                                                        rhs_a,
                                                    )
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:252-289 checkProjRule
/// The frame walks and the definitional parameter/domain pins of
/// `checkProjRule`'s tail, split off so the nest above stays readable and
/// every arm a tail call.  The two `M_*` messages repeat the cited ones.
pub fn check_proj_rule_frames(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    pty: &Expr,
    cvj: &ConstantVal,
    n_p: u64,
    n_f: u64,
    rhs_a: Expr,
) -> CheckM<Expr> {
    const M_PTY: [u32; 27] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    const M_CTY: [u32; 34] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    const M_TELE: [u32; 27] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 32,
    ];
    match open_pis_at_fvars(n_p, pty, 0) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_PTY))),
        Some(pq) => match expr_ops::inst_pis_at(&pq.0, &cvj.ty) {
            None => Err(core_types::not_implemented(core_types::code_points(&M_CTY))),
            Some(cq) => {
                let doms: Vec<Expr> = fvar_types_of(&pq.0);
                match check_def_eq_list(mode, st, fe, n_p + n_f, &doms, &cq.0) {
                    Err(err) => Err(err),
                    Ok(()) => match open_pis_at_fvars(n_f, &cq.1, n_p) {
                        None => Err(core_types::not_implemented(core_types::code_points(
                            &M_CTY,
                        ))),
                        Some(xq) => {
                            let frame: Vec<Expr> =
                                core_k::append_exprs(env::exprs_copy(&pq.0), &xq.0);
                            match expr_ops::inst_lams_at(&frame, &rhs_a) {
                                None => Err(core_types::not_implemented(
                                    core_types::code_points(&M_TELE),
                                )),
                                Some(lq) => {
                                    let ftys: Vec<Expr> = fvar_types_of(&frame);
                                    match check_def_eq_list(
                                        mode,
                                        st,
                                        fe,
                                        n_p + n_f,
                                        &ftys,
                                        &lq.0,
                                    ) {
                                        Err(err) => Err(err),
                                        Ok(()) => match core_c::infer(
                                            mode,
                                            core_k::check_fuel(),
                                            st,
                                            fe,
                                            0,
                                            &rhs_a,
                                        ) {
                                            Err(err) => Err(err),
                                            Ok(_rhs_ty) => Ok(rhs_a),
                                        },
                                    }
                                }
                            }
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: none — `fvs.map Expr.fvarTypeD` over a `Vec<Expr>`
/// The spine of declared annotations every frame pin compares against.
pub fn fvar_types_of(fvs: &Vec<Expr>) -> Vec<Expr> {
    fvar_types_of_from(fvs, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `fvar_types_of`
pub fn fvar_types_of_from(fvs: &Vec<Expr>, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= fvs.len() {
        out
    } else {
        let mut out = out;
        out.push(expr_ops::fvar_type_d(&fvs[i]));
        fvar_types_of_from(fvs, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The pinned `Eq` basis (`Kernel/Basis/Eq.lean:22-28`, `Kernel/BasisA.lean:30`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Basis/Eq.lean:22-28 eqRaw
/// con-leche: ConLeche/Kernel/BasisA.lean:29-49 _
/// The pinned equality former, as the environment stores it:
/// `Eq.{u} {α : Sort u} : α → α → Prop`, `ruleK := true`.
///
/// (`eqA` has no `def` line to cite: it is one entry of the
/// `#annotate_basis over []` command the second citation's range covers, so
/// the citation names no declaration.)
///
/// **`eqA = eqRaw`, and that is a fact, not an assumption.**  `eqA` is
/// `#annotate_basis`'s output, i.e. `annotateCore .verified` applied to
/// `eqRaw`'s type at elaboration time (`Kernel/BasisGen.lean`'s recipe).
/// Every binder of that type has codomain a `Sort` or a `∀` whose datum is
/// already `.never`, so `annotPwPi`'s head-symbol reader (`typeSortPW`)
/// answers `.never` at all three binders — which is the parse placeholder the
/// raw pin already carries.  The annotation pass is therefore the identity
/// here, and the module's test `eq_a_is_annotated` runs
/// `core_c::annotate` on it and compares, so a change upstream breaks a test
/// rather than a verdict.  (Task #22's `kernel/basis_tables.rs` will own this
/// pin; then this function is a `use`.)
pub fn eq_a() -> ConstantInfo {
    const EQ: [u32; 2] = [69, 113];
    const U: [u32; 1] = [117];
    let u_n: Name = name::mk_str(name::anonymous(), core_types::code_points(&U));
    let u: Level = level::param(name::dup(&u_n));
    let mut lps: Vec<Name> = Vec::new();
    lps.push(u_n);
    let never = BinderMeta {
        pw: prop_when::never(),
    };
    let body = expr::forall_e(
        expr::sort(u),
        expr::forall_e(
            expr::bvar(0),
            expr::forall_e(
                expr::bvar(1),
                expr::sort(level::zero()),
                BinderMeta {
                    pw: prop_when::never(),
                },
            ),
            BinderMeta {
                pw: prop_when::never(),
            },
        ),
        never,
    );
    let mut caps: IndCaps = env::ind_caps_default();
    caps.rule_k = true;
    ConstantInfo::IndInfo(
        ConstantVal {
            name: name::mk_str(name::anonymous(), core_types::code_points(&EQ)),
            level_params: lps,
            ty: body,
        },
        caps,
    )
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// The four sites' shared guard `env.find? eqName = some eqA` — "the pinned
/// `Eq` basis is installed, unmodified".  Written once because the cited
/// `eqA` has no Rust value until task #22 lands `kernel/basis_tables.rs`.
pub fn eq_basis_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::eq_name()) {
        Some(ci) => constant_info_beq(ci, &eq_a()),
        None => false,
    }
}

// ---------------------------------------------------------------------------
// The derived structural equalities (`Kernel/Env.lean`'s `deriving DecidableEq`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:196-201 ConstantVal
/// Lean's `deriving DecidableEq` on `ConstantVal`, componentwise.
pub fn constant_val_beq(a: &ConstantVal, b: &ConstantVal) -> bool {
    if name::beq(&a.name, &b.name) {
        if prop_when::names_beq(&a.level_params, &b.level_params) {
            expr::beq(&a.ty, &b.ty)
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:357-384 IndCaps
/// Lean's `deriving DecidableEq` on `IndCaps`, componentwise.
pub fn ind_caps_beq(a: &IndCaps, b: &IndCaps) -> bool {
    if a.eta == b.eta {
        if name::beq(&a.eta_ctor, &b.eta_ctor) {
            if a.eta_params == b.eta_params {
                if a.eta_fields == b.eta_fields {
                    if a.unitlike == b.unitlike {
                        if a.unit_params == b.unit_params {
                            if a.rule_k == b.rule_k {
                                prop_when::beq(&a.sort_z, &b.sort_z)
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:203-247 RecRuleFire
/// Lean's `deriving DecidableEq` on `RecRuleFire`.
pub fn rec_rule_fire_beq(a: &RecRuleFire, b: &RecRuleFire) -> bool {
    match a {
        RecRuleFire::Inert => match b {
            RecRuleFire::Inert => true,
            _ => false,
        },
        RecRuleFire::Plain => match b {
            RecRuleFire::Plain => true,
            _ => false,
        },
        RecRuleFire::Nested(l1, p1) => match b {
            RecRuleFire::Nested(l2, p2) => {
                if expr::levels_beq(l1, l2) {
                    struct_parts::exprs_beq(p1, p2)
                } else {
                    false
                }
            }
            _ => false,
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:249-292 RecRule
/// Lean's `deriving DecidableEq` on `RecRule`, componentwise.
pub fn rec_rule_beq(a: &RecRule, b: &RecRule) -> bool {
    if name::beq(&a.ctor, &b.ctor) {
        if a.nfields == b.nfields {
            if a.ctor_params == b.ctor_params {
                if rec_rule_fire_beq(&a.fire, &b.fire) {
                    if expr::beq(&a.rhs, &b.rhs) {
                        if a.k == b.k {
                            if a.eta == b.eta {
                                a.params_blind == b.params_blind
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:249-292 RecRule
/// The list equality of `deriving DecidableEq (List RecRule)`.
pub fn rec_rules_beq(a: &Vec<RecRule>, b: &Vec<RecRule>) -> bool {
    if a.len() == b.len() {
        rec_rules_beq_from(a, b, 0)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:249-292 RecRule
/// The index recursion behind `rec_rules_beq`.
pub fn rec_rules_beq_from(a: &Vec<RecRule>, b: &Vec<RecRule>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if rec_rule_beq(&a[i], &b[i]) {
        rec_rules_beq_from(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:312-322 ReducibilityHint
/// Lean's `deriving DecidableEq` on `ReducibilityHint`.
pub fn reducibility_hint_beq(a: &ReducibilityHint, b: &ReducibilityHint) -> bool {
    match a {
        ReducibilityHint::Opaque => match b {
            ReducibilityHint::Opaque => true,
            _ => false,
        },
        ReducibilityHint::Abbrev => match b {
            ReducibilityHint::Abbrev => true,
            _ => false,
        },
        ReducibilityHint::Regular(h1) => match b {
            ReducibilityHint::Regular(h2) => h1 == h2,
            _ => false,
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:386-441 ProjTable
/// Lean's `deriving DecidableEq` on `ProjTable`, componentwise.
pub fn proj_table_beq(a: &ProjTable, b: &ProjTable) -> bool {
    if name::beq(&a.struct_name, &b.struct_name) {
        if prop_when::names_beq(&a.level_params, &b.level_params) {
            if a.num_params == b.num_params {
                if name::beq(&a.ctor, &b.ctor) {
                    if a.num_fields == b.num_fields {
                        if level::beq(&a.struct_sort, &b.struct_sort) {
                            if struct_parts::exprs_beq(&a.bodies, &b.bodies) {
                                if expr::levels_beq(&a.guards, &b.guards) {
                                    a.off == b.off
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:470-496 ConstantInfo
/// Lean's `deriving DecidableEq` on `ConstantInfo`, which the pinned-basis
/// guards read as `==` and as `= some eqA`.
pub fn constant_info_beq(a: &ConstantInfo, b: &ConstantInfo) -> bool {
    match a {
        ConstantInfo::AxiomInfo(v1) => match b {
            ConstantInfo::AxiomInfo(v2) => constant_val_beq(v1, v2),
            _ => false,
        },
        ConstantInfo::DefnInfo(v1, e1, h1) => match b {
            ConstantInfo::DefnInfo(v2, e2, h2) => {
                if constant_val_beq(v1, v2) {
                    if expr::beq(e1, e2) {
                        reducibility_hint_beq(h1, h2)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        },
        ConstantInfo::ThmInfo(v1, e1) => match b {
            ConstantInfo::ThmInfo(v2, e2) => {
                if constant_val_beq(v1, v2) {
                    expr::beq(e1, e2)
                } else {
                    false
                }
            }
            _ => false,
        },
        ConstantInfo::IndInfo(v1, c1) => match b {
            ConstantInfo::IndInfo(v2, c2) => {
                if constant_val_beq(v1, v2) {
                    ind_caps_beq(c1, c2)
                } else {
                    false
                }
            }
            _ => false,
        },
        ConstantInfo::CtorInfo(v1, p1, f1) => match b {
            ConstantInfo::CtorInfo(v2, p2, f2) => {
                if constant_val_beq(v1, v2) {
                    if p1 == p2 {
                        f1 == f2
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        },
        ConstantInfo::RecInfo(v1, m1, r1, rs1) => match b {
            ConstantInfo::RecInfo(v2, m2, r2, rs2) => {
                if constant_val_beq(v1, v2) {
                    if m1 == m2 {
                        if r1 == r2 {
                            rec_rules_beq(rs1, rs2)
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        },
        ConstantInfo::ProjInfo(t1) => match b {
            ConstantInfo::ProjInfo(t2) => proj_table_beq(t1, t2),
            _ => false,
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:736-742 blockRecSuffixDec
/// con-leche: ConLeche/Kernel/Env.lean:670-675 recsFormSuffix
/// The substituted decision behind `@decide _ (blockRecSuffixDec block)`: the
/// recursors form a suffix of the block.  `recsFormSuffix_iff` is the cited
/// equivalence, and `env::recs_form_suffix` (task #14) is the tag pass.
pub fn block_rec_suffix_ok(block: &Vec<ConstantInfo>) -> bool {
    env::recs_form_suffix(block)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cached::state_c;
    use crate::kernel::env::Env;

    /// **`eqA` really is `eqRaw`**: running the checker's own annotation pass
    /// on the pin's type over the empty environment reproduces it, which is
    /// what `#annotate_basis` computes (`ConLeche/Kernel/BasisGen.lean`).
    #[test]
    fn eq_a_is_annotated() {
        let fe: FEnv = fenv::mk_fenv(Env { consts: Vec::new() });
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let pin = eq_a();
        let ty = env::constant_info_type(&pin);
        match core_c::annotate(&mode, core_k::check_fuel(), &mut st, &fe, 0, &ty) {
            Ok(a) => assert!(
                expr::beq(&a, &ty),
                "the annotation pass must be the identity on the Eq pin"
            ),
            Err(_) => panic!("annotating the Eq pin failed"),
        }
    }

    /// `eq_basis_pinned` accepts the pin and rejects a modified one.
    #[test]
    fn eq_basis_pinned_reads_the_store() {
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(eq_a());
        let fe: FEnv = fenv::mk_fenv(Env { consts });
        assert!(eq_basis_pinned(&fe));
        // the same constant without the K capability is not the pin
        let mut consts2: Vec<ConstantInfo> = Vec::new();
        let ty = env::constant_info_type(&eq_a());
        let mut l: Vec<Name> = Vec::new();
        l.push(name::mk_str(name::anonymous(), vec![117]));
        consts2.push(ConstantInfo::IndInfo(
            ConstantVal {
                name: basis_names::eq_name(),
                level_params: l,
                ty,
            },
            env::ind_caps_default(),
        ));
        let fe2: FEnv = fenv::mk_fenv(Env { consts: consts2 });
        assert!(!eq_basis_pinned(&fe2));
        // and an empty environment has no pin
        let fe3: FEnv = fenv::mk_fenv(Env { consts: Vec::new() });
        assert!(!eq_basis_pinned(&fe3));
    }

    /// `open_pis_at_fvars` opens a two-binder telescope at `0`/`1`, with each
    /// fvar carrying its instantiated domain, and declines a short one.
    #[test]
    fn open_pis_at_fvars_opens_a_telescope() {
        let s1 = expr::sort(level::succ(level::zero()));
        // `∀ (a : Sort 1) (b : a), b`
        let tele = expr::forall_e(
            expr::dup(&s1),
            expr::forall_e(
                expr::bvar(0),
                expr::bvar(0),
                BinderMeta {
                    pw: prop_when::never(),
                },
            ),
            BinderMeta {
                pw: prop_when::never(),
            },
        );
        match open_pis_at_fvars(2, &tele, 0) {
            Some(q) => {
                assert_eq!(q.0.len(), 2);
                assert!(expr::beq(&q.0[0], &expr::fvar(0, expr::dup(&s1))));
                assert!(expr::beq(
                    &q.0[1],
                    &expr::fvar(1, expr::fvar(0, expr::dup(&s1)))
                ));
                assert!(expr::beq(
                    &q.1,
                    &expr::fvar(1, expr::fvar(0, expr::dup(&s1)))
                ));
            }
            None => panic!("the telescope should open"),
        }
        assert!(open_pis_at_fvars(3, &tele, 0).is_none());
        // and it agrees with the specification walk
        match (
            open_pis_at_fvars(2, &tele, 0),
            open_pis_at_fvars_spec(2, &tele, 0),
        ) {
            (Some(a), Some(b)) => {
                assert!(struct_parts::exprs_beq(&a.0, &b.0));
                assert!(expr::beq(&a.1, &b.1));
            }
            _ => panic!("both walks must open the telescope"),
        }
    }

    /// `all_level_params_defined` reads the binder data too, as the cited
    /// definition does.
    #[test]
    fn all_level_params_defined_reads_binder_data() {
        let u = name::mk_str(name::anonymous(), vec![117]);
        let mut ps: Vec<Name> = Vec::new();
        ps.push(name::dup(&u));
        let sort_u = expr::sort(level::param(name::dup(&u)));
        assert!(all_level_params_defined(&ps, &sort_u));
        assert!(!all_level_params_defined(&Vec::new(), &sort_u));
        // the datum's parameters count
        let mut qs: Vec<Name> = Vec::new();
        qs.push(name::dup(&u));
        let pi = expr::forall_e(
            expr::sort(level::zero()),
            expr::bvar(0),
            BinderMeta {
                pw: prop_when::if_all_zero(qs),
            },
        );
        assert!(all_level_params_defined(&ps, &pi));
        assert!(!all_level_params_defined(&Vec::new(), &pi));
        // and the memoized walk agrees with the specification
        assert_eq!(
            all_level_params_defined(&ps, &pi),
            all_level_params_defined_spec(&ps, &pi)
        );
    }
}
