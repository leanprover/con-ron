//! `ConLeche/Kernel/CheckerBase.lean` — the declaration checker's common
//! ground: the per-declaration constant check (`checkConstantVal`), the
//! strategy-independent telescope helpers every install path shares, and the
//! projection-rule stages.
//!
//! ## `CheckerOps` is cited, not ported — the knot rule again
//!
//! con-leche writes the whole declaration checker *once*, monad-polymorphically
//! against a record `ops : CheckerOps m` of the core's five entry points plus
//! `orElse`, and instantiates it twice: with the pure knot (`fueledOps`,
//! `pureOps` — the verification's subject) and, in `Cached/CheckerC.lean`,
//! with the memoized knot the binary executes (`sharedOpsC`).  DESIGN.md
//! §3.1's knot ruling applies unchanged: **no trait in the recursion, no
//! closures**, so the record parameter is dropped and its slots are called by
//! name through `kernel::type_checker`, which is `sharedOpsC` spelled as
//! seven functions at `checkFuel`.  Every function below that the Lean gives
//! an `ops` therefore takes `(mode, st, fe, …)` instead.
//!
//! `orElse` is the record's one non-core slot and the **only place in the
//! checker where a thrown error is recovered from**; it is ported in
//! `crate::cached::checker_c`, where `sharedOpsC` — the instantiation that
//! actually delivers the outcome — writes it.
//!
//! ## The `F`-twins collapse
//!
//! `ConLeche/Kernel/DeclCheck.lean` mirrors every function here with an
//! `FEnv`-indexed twin (`checkConstantValF`, `checkProjRuleF`, `FEnv.findCV?`)
//! whose only difference is that environment lookups go through the index.
//! The port has one environment spelling — the index (task #18's deviation 3)
//! — so each such pair is **one** Rust function with two citations.  The
//! `Array` twin `domsMatchAuxA` collapses into `domsMatchAux` the same way,
//! because a `Vec` is already the array.

use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::{CheckError, CheckM};
use crate::kernel::decl_check;
use crate::kernel::env;
use crate::kernel::env::{CheckMode, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprView};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::inductives::struct_parts;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::type_checker;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The common per-declaration check (`CheckerBase.lean:73-97`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:71-91 unresolvedConstsError
/// **The verdict at a term whose constants do not all resolve.**  A term that
/// mentions `sorryAx` declines — that axiom is tolerated as a declaration and
/// installs nothing, so a use of it is a positively detected unsupported
/// feature, never a malformed stream; anything else is an unknown constant
/// and rejects.  The cited `where_ : String` argument only names the slot in
/// the message, and §3.1 says messages need not match, so the port takes no
/// such argument: the two verdicts are the two messages.
pub fn unresolved_consts_error(e: &Expr) -> CheckError {
    const S: [u32; 24] = [
        117, 115, 101, 32, 111, 102, 32, 116, 104, 101, 32, 115, 111, 114, 114, 121, 65, 120,
        32, 97, 120, 105, 111, 109,
    ];
    const U: [u32; 16] = [
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116,
    ];
    if struct_parts::mentions_const(&basis_names::sorry_ax_name(), e) {
        core_types::not_implemented(core_types::code_points(&S))
    } else {
        core_types::invalid(core_types::code_points(&U))
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
/// Checks common to all declarations: fresh name, no reserved name, no
/// reserved projection shape, well-formed universe parameters, and a type
/// that is a type and mentions only declared parameters.  Returns the
/// constant with its type **annotated**; the guards run on the annotated
/// type.
pub fn check_constant_val(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
) -> CheckM<ConstantVal> {
    if fenv::find(fe, &cv.name).is_some() {
        Err(core_types::invalid({ const M: [u32; 21] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if name::contains(&basis_names::reserved_basis_names(), &cv.name) {
        Err(core_types::invalid({ const M: [u32; 19] = [114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
    } else if level::name_is_proj_fn_shape(&cv.name) {
        Err(core_types::invalid({ const M: [u32; 24] = [114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
    } else if !level::name_nodup(&cv.level_params) {
        Err(core_types::invalid({ const M: [u32; 44] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if !expr_ops::loose_bvars_bounded(0, &cv.ty) {
        Err(core_types::invalid({ const M: [u32; 28] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else if expr_ops::has_fvar(&cv.ty) {
        Err(core_types::invalid({ const M: [u32; 32] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, fe, 0, &cv.ty) {
            Err(err) => Err(err),
            Ok(ty) => check_constant_val_after_annot(mode, st, fe, cv, ty),
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
/// The tail of `check_constant_val` past the annotation: the level-parameter
/// and resolution guards on the annotated type, the type's own sort, and the
/// record update `{ cv with type := type }`.  Split off so the annotation's
/// state-threading call is a tail call and the two guard groups do not join
/// on a borrowed state (task #18's rule for gated certificates).
///
/// The resolution guard is the **memoized** walk
/// (`decl_check::consts_resolve_f_fast`), because the cited
/// `checkConstantValF` says `type.constsResolveF fe` and `constsResolveF` is
/// `@[csimp]`-swapped for `constsResolveFFast`
/// (`DeclCheck.lean:197-204`); the pure `core_k::consts_resolve` this used to
/// call is the *spec* of that value and re-traverses a DAG-shared type as a
/// tree, which does not finish on con-leche task #215's `tower_struct`
/// (task #30 found it there, once the `beq` pair memo stopped hiding it).
pub fn check_constant_val_after_annot(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
    ty: Expr,
) -> CheckM<ConstantVal> {
    if !expr_ops::all_level_params_defined_fast(&cv.level_params, &ty) {
        Err(core_types::invalid({ const M: [u32; 37] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else if !decl_check::consts_resolve_f_fast(fe, &ty) {
        Err(unresolved_consts_error(&ty))
    } else {
        match type_checker::infer_type_core(mode, st, fe, 0, &ty) {
            Err(err) => Err(err),
            Ok(stype) => match type_checker::ensure_sort_core(mode, st, fe, 0, &stype) {
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

// ---------------------------------------------------------------------------
// Telescope helpers (`CheckerBase.lean:99-154`)
// ---------------------------------------------------------------------------

/// con-leche: none — replaces the `g : Nat → Expr → Expr` argument of `domsMatchAux`
/// The one-method trait that stands for the cited function argument (task
/// #9's pattern 1; DESIGN.md §3.4 forbids closures).  Aeneas renders it as a
/// dictionary threaded through the recursion.
pub trait DomView {
    /// con-leche: none — the `g` of `domsMatchAux g`
    fn view(&self, i: u64, e: &Expr) -> Expr;
}

/// con-leche: none — `domsMatchAux (fun _ e => e)`, the identity view
/// The view every call site in this file and three of the four in the
/// inductive routes pass (`checkProjRule`, `checkEtaThm`, `checkUnitThm`);
/// the fourth, `checkProjIotaF`, renames
/// (`kernel::inductives::modeled::DomProjFwd`).
pub struct DomIdent;

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
impl DomView for DomIdent {
    /// con-leche: none — `fun _ e => e`
    fn view(&self, _i: u64, e: &Expr) -> Expr {
        expr::dup(e)
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
/// con-leche: ConLeche/Kernel/CheckerBase.lean:142-151 domsMatchAuxA
/// Compare binder domains at offsets `o1`/`o2` for `n` positions, the right
/// side viewed through `g`.
///
/// One deviation: the cited `Array` twin is the same function here —
/// con-leche wrote it because `List` indexing is linear per access, and a
/// `Vec` is already the array, so `domsMatchAux` and `domsMatchAuxA` are one
/// Rust function and its `domsMatchAuxA_eq` is the equation between them.
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

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
/// The `(List.range n).all` of the cited function as an index recursion
/// (task #3's pattern).
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
    } else {
        let j1: u64 = o1 + i;
        let j2: u64 = o2 + i;
        if j1 >= bs1.len() as u64 {
            false
        } else if j2 >= bs2.len() as u64 {
            false
        } else {
            let viewed: Expr = g.view(i, &bs2[j2 as usize].0);
            if expr::beq(&bs1[j1 as usize].0, &viewed) {
                doms_match_aux_from(g, bs1, bs2, o1, o2, n, i + 1)
            } else {
                false
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars
/// Open the first `n` `∀`-binders at fresh free variables `0..n-1` (each
/// fvar's type is the binder domain, instantiated with the earlier fvars).
/// Returns the fvars and the opened body.
///
/// Deviation: `fv :: fvs` is `expr_ops::cons_expr`, the project's spelling of
/// a cons on a `Vec<Expr>` — a fresh vector filled front to back, `O(width)`
/// where Lean's cons is `O(1)`, deliberate and bounded by the telescope width
/// (task #14's point 5).  It is *not* `Vec::insert`: no function of the port
/// calls that primitive (task #50, `AENEAS_FINDINGS.md` §3.9).
pub fn open_pis_at_fvars(n: u64, e: &Expr, i: u64) -> Option<(Vec<Expr>, Expr)> {
    if n == 0 {
        Some((Vec::new(), expr::dup(e)))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(dom, body, _) => {
                let fv: Expr = expr::fvar(i, expr::dup(dom));
                let opened: Expr = expr_ops::instantiate1(body, &fv, 0);
                match open_pis_at_fvars(n - 1, &opened, i + 1) {
                    Some((fvs, b)) => Some((expr_ops::cons_expr(&fv, &fvs), b)),
                    None => None,
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo
/// Core of `openPisAtFvarsF`: `acc` holds the already-created fvars,
/// innermost binder first.  One `instantiateList` pass per domain instead of
/// one whole-telescope `instantiate1` pass per binder.
///
/// Deviation: `fv :: acc` and `fv :: fvs` are `expr_ops::cons_expr` (see
/// `open_pis_at_fvars`); `acc` is passed by shared reference and copied on
/// the way down, because a `Vec` has no shared tail — the cons *is* that copy,
/// so the step is one pass, not a copy and an insertion.
pub fn open_pis_at_fvars_f_go(
    acc: &Vec<Expr>,
    n: u64,
    e: &Expr,
    i: u64,
) -> Option<(Vec<Expr>, Expr)> {
    if n == 0 {
        Some((Vec::new(), expr_ops::instantiate_list_fast(e, acc, 0)))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(dom, body, _) => {
                let fv: Expr = expr::fvar(i, expr_ops::instantiate_list_fast(dom, acc, 0));
                let acc2: Vec<Expr> = expr_ops::cons_expr(&fv, acc);
                match open_pis_at_fvars_f_go(&acc2, n - 1, body, i + 1) {
                    Some((fvs, b)) => Some((expr_ops::cons_expr(&fv, &fvs), b)),
                    None => None,
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF
/// One-pass `openPisAtFvars` (equal to it: `openPisAtFvarsF_eq`; the fallback
/// covers telescopes whose binders only appear after substitution).  **The
/// executed one.**
pub fn open_pis_at_fvars_f(n: u64, e: &Expr, i: u64) -> Option<(Vec<Expr>, Expr)> {
    match open_pis_at_fvars_f_go(&Vec::new(), n, e, i) {
        Some(r) => Some(r),
        None => open_pis_at_fvars(n, e, i),
    }
}

// ---------------------------------------------------------------------------
// The list checks (`CheckerBase.lean:156-209`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList
/// Check each expression's inferred type against the corresponding expected
/// type (definitionally); throws on a length mismatch.  Used to pin a nested
/// rule's stored parameter instantiations to the constructor's parameter
/// domains.
pub fn check_typed_list(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ts: &Vec<Expr>,
) -> CheckM<()> {
    check_typed_list_from(mode, st, fe, depth, xs, ts, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList
/// The cited two-list recursion as one index recursion (task #14's point 7):
/// both exhausted, both in range, or the arity throw.
pub fn check_typed_list_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ts: &Vec<Expr>,
    i: usize,
) -> CheckM<()> {
    if i >= xs.len() && i >= ts.len() {
        Ok(())
    } else if i >= xs.len() || i >= ts.len() {
        Err(core_types::not_implemented({ const M: [u32; 25] = [110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 114, 105, 116, 121, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
    } else {
        match type_checker::infer_type_core(mode, st, fe, depth, &xs[i]) {
            Err(err) => Err(err),
            Ok(ty) => match type_checker::is_def_eq_core(mode, st, fe, depth, &ty, &ts[i]) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        check_typed_list_from(mode, st, fe, depth, xs, ts, i + 1)
                    } else {
                        Err(core_types::not_implemented({ const M: [u32; 24] = [110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList
/// Check that each expression is a fixed point of the annotation pass in the
/// given context: its codomain-sort annotations are exactly the ones
/// annotation reconstructs.
pub fn check_annot_list(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
) -> CheckM<()> {
    check_annot_list_from(mode, st, fe, depth, xs, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList
/// The cited `List` recursion as an index recursion.
pub fn check_annot_list_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    i: usize,
) -> CheckM<()> {
    if i >= xs.len() {
        Ok(())
    } else {
        match type_checker::annotate_core(mode, st, fe, depth, &xs[i]) {
            Err(err) => Err(err),
            Ok(a_a) => {
                if expr::beq(&a_a, &xs[i]) {
                    check_annot_list_from(mode, st, fe, depth, xs, i + 1)
                } else {
                    Err(core_types::not_implemented({ const M: [u32; 30] = [110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:208-211 isEqHead
/// Is the expression the pinned equality former at one level?
pub fn is_eq_head(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Const(c, us) => {
            if us.len() == 1 {
                name::beq(c, &basis_names::eq_name())
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel
/// The level an equality head carries — the statement's own `Eq.{ℓ}` level,
/// read off a head `isEqHead` has accepted.  Off shape it is `.zero`, which
/// `isEqHead` has already rejected wherever the result is used.
pub fn eq_head_level(e: &Expr) -> Level {
    match expr::view(&e) {
        ExprView::Const(_, us) => {
            if us.len() == 1 {
                level::dup(&us[0])
            } else {
                level::zero()
            }
        }
        _ => level::zero(),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList
/// Pairwise definitional-equality check of two spines (throws on any
/// mismatch, including a length difference).
pub fn check_def_eq_list(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ys: &Vec<Expr>,
) -> CheckM<()> {
    check_def_eq_list_from(mode, st, fe, depth, xs, ys, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList
/// The cited two-list recursion as one index recursion.
pub fn check_def_eq_list_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ys: &Vec<Expr>,
    i: usize,
) -> CheckM<()> {
    if i >= xs.len() && i >= ys.len() {
        Ok(())
    } else if i >= xs.len() || i >= ys.len() {
        Err(core_types::not_implemented({ const M: [u32; 30] = [105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 32, 97, 114, 105, 116, 121]; core_types::code_points(&M) }))
    } else {
        match type_checker::is_def_eq_core(mode, st, fe, depth, &xs[i], &ys[i]) {
            Err(err) => Err(err),
            Ok(ok) => {
                if ok {
                    check_def_eq_list_from(mode, st, fe, depth, xs, ys, i + 1)
                } else {
                    Err(core_types::not_implemented({ const M: [u32; 33] = [105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:233-239 unwrapOr
/// Unwrap an optional value or fail with the given error (the `Option`-shaped
/// checks stay bind-shaped for the verification batteries).  Its call sites
/// are `DeclCheck.lean`'s iota-theorem mirrors, which belong to the
/// inductive-install family and are not ported yet; ported here, and
/// uncalled, so the gate stays in step with its source.
pub fn unwrap_or<T>(o: Option<T>, err: CheckError) -> CheckM<T> {
    match o {
        Some(a) => Ok(a),
        None => Err(err),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:241-247 Env.findCV?
/// con-leche: ConLeche/Kernel/DeclCheck.lean:33-35 FEnv.findCV?
/// The stored constant under `n`, as a `ConstantVal`, if any.  The
/// iota-certificate checks consume only the stored constant's *type* (any
/// stored constant witnesses its type's inhabitation in the model), so no
/// theorem-kind filter is imposed.
pub fn find_cv(fe: &FEnv, n: &Name) -> Option<ConstantVal> {
    match fenv::find(fe, n) {
        Some(ci) => Some(env::to_constant_val(ci)),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:249-254 piResultSort
/// The result sort of a syntactic pi telescope (the sort the type former's
/// type ends in), if it ends in a sort at all.
pub fn pi_result_sort(e: &Expr) -> Option<Level> {
    let r: Expr = expr_ops::pi_result(e);
    match expr::view(&r) {
        ExprView::Sort(u) => Some(level::dup(u)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The projection stages (`CheckerBase.lean:235-289`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape
/// Stage 2b: the projection type's parameter telescope is *syntactically* the
/// constructor's, and the constructor's residual is the family applied to
/// exactly the parameters — the syntactic pins the rule's total λ-equality
/// derivation folds over.
pub fn check_proj_shape(pty: &Expr, ctor_ty: &Expr, n_p: u64, n_f: u64) -> CheckM<()> {
    match expr_ops::strip_pis(n_p, pty) {
        None => Err(core_types::not_implemented({ const M: [u32; 25] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
        Some(_) => match expr_ops::strip_pis(n_p + n_f, ctor_ty) {
            None => Err(core_types::not_implemented({ const M: [u32; 32] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
            Some((_, cbody)) => {
                let args: Vec<Expr> = expr_ops::get_app_args(&cbody);
                if args.len() as u64 != n_p {
                    Err(core_types::not_implemented({ const M: [u32; 37] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32, 97, 114, 105, 116, 121]; core_types::code_points(&M) }))
                } else {
                    let f: Expr = expr_ops::get_app_fn(&cbody);
                    match expr::view(&f) {
                        ExprView::Const(_, _) => Ok(()),
                        _ => Err(core_types::not_implemented({ const M: [u32; 36] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32, 104, 101, 97, 100]; core_types::code_points(&M) })),
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// Stage 3: the reduction rule — λ over the constructor telescope returning
/// field `i`, annotated; its λ-domains stay the constructor's.  The syntactic
/// half; the definitional pins (the frame walks) are
/// `check_proj_rule_certs`.
///
/// The indexed mirror is this same function (the `F`-collapse), and it is the
/// mirror's *one-pass* walkers that are called (`openPisAtFvarsF`,
/// `instPisAtF`, `instLamsAtF`, `domsMatchAuxA`) — the executed spelling.
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
    match expr_ops::pis_to_lams(
        n_p + n_f,
        &cvj.ty,
        &expr::bvar(expr_ops::sub_nat(n_f, 1 + i)),
    ) {
        None => Err(core_types::not_implemented({ const M: [u32; 25] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
        Some(rhs) => {
            if expr_ops::has_fvar(&rhs) {
                Err(core_types::not_implemented({ const M: [u32; 23] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 115, 99, 111, 112, 105, 110, 103]; core_types::code_points(&M) }))
            } else if !expr_ops::loose_bvars_bounded(0, &rhs) {
                Err(core_types::not_implemented({ const M: [u32; 23] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 115, 99, 111, 112, 105, 110, 103]; core_types::code_points(&M) }))
            } else {
                match type_checker::annotate_core(mode, st, fe, 0, &rhs) {
                    Err(err) => Err(err),
                    Ok(rhs_a) => {
                        if !proj_rule_wf(fe, &rhs_a, lps) {
                            Err(core_types::not_implemented({ const M: [u32; 30] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 119, 101, 108, 108, 102, 111, 114, 109, 101, 100, 110, 101, 115, 115]; core_types::code_points(&M) }))
                        } else {
                            check_proj_rule_shape(mode, st, fe, pty, cvj, n_p, n_f, i, rhs_a)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// The annotated rule's four-way well-formedness conjunction, as an `if` nest
/// (task #3's pattern 9).
pub fn proj_rule_wf(fe: &FEnv, rhs_a: &Expr, lps: &Vec<Name>) -> bool {
    if expr_ops::all_level_params_defined_fast(lps, rhs_a) {
        if decl_check::consts_resolve_f_fast(fe, rhs_a) {
            if expr_ops::loose_bvars_bounded(0, rhs_a) {
                !expr_ops::has_fvar(rhs_a)
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

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// The syntactic stage past the annotation: the rule's λ telescope, its body
/// `bvar (nF - 1 - i)`, and its domains against the constructor's
/// (`domsMatchAuxA`).  Then the definitional pins.
pub fn check_proj_rule_shape(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    pty: &Expr,
    cvj: &ConstantVal,
    n_p: u64,
    n_f: u64,
    i: u64,
    rhs_a: Expr,
) -> CheckM<Expr> {
    match expr_ops::strip_lams(n_p + n_f, &rhs_a) {
        None => Err(core_types::not_implemented({ const M: [u32; 25] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
        Some((rbinders, rrbody)) => {
            if !expr::beq(&rrbody, &expr::bvar(expr_ops::sub_nat(n_f, 1 + i))) {
                Err(core_types::not_implemented({ const M: [u32; 20] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 98, 111, 100, 121]; core_types::code_points(&M) }))
            } else {
                match expr_ops::strip_pis(n_p + n_f, &cvj.ty) {
                    None => Err(core_types::not_implemented({ const M: [u32; 32] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
                    Some((cbinders_r, _)) => {
                        if !doms_match_aux(&DomIdent, &rbinders, &cbinders_r, 0, 0, n_p + n_f)
                        {
                            Err(core_types::not_implemented({ const M: [u32; 31] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 100, 111, 109, 97, 105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                        } else {
                            check_proj_rule_certs(mode, st, fe, pty, cvj, n_p, n_f, rhs_a)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// The frame walks and the definitional parameter/domain pins: the projection
/// type's opened parameter annotations are definitionally the constructor's
/// instantiated parameter domains, and the whole frame's annotations are
/// definitionally the rule λ-tower's instantiated domains.  Finally the
/// rule's own inference.
pub fn check_proj_rule_certs(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    pty: &Expr,
    cvj: &ConstantVal,
    n_p: u64,
    n_f: u64,
    rhs_a: Expr,
) -> CheckM<Expr> {
    match open_pis_at_fvars_f(n_p, pty, 0) {
        None => Err(core_types::not_implemented({ const M: [u32; 25] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
        Some((fvs_p, _)) => match expr_ops::inst_pis_at_f(&fvs_p, &cvj.ty) {
            None => Err(core_types::not_implemented({ const M: [u32; 32] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
            Some((cdoms_p, crest_p)) => {
                let ptypes: Vec<Expr> = fvar_types(&fvs_p);
                match check_def_eq_list(mode, st, fe, n_p + n_f, &ptypes, &cdoms_p) {
                    Err(err) => Err(err),
                    Ok(()) => match open_pis_at_fvars_f(n_f, &crest_p, n_p) {
                        None => Err(core_types::not_implemented({ const M: [u32; 32] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
                        Some((x_fvs, _)) => {
                            let frame: Vec<Expr> = core_k::append_exprs(fvs_p, &x_fvs);
                            match expr_ops::inst_lams_at_f(&frame, &rhs_a) {
                                None => Err(core_types::not_implemented({ const M: [u32; 25] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101]; core_types::code_points(&M) })),
                                Some((ldoms, _)) => {
                                    let ftypes: Vec<Expr> = fvar_types(&frame);
                                    match check_def_eq_list(
                                        mode,
                                        st,
                                        fe,
                                        n_p + n_f,
                                        &ftypes,
                                        &ldoms,
                                    ) {
                                        Err(err) => Err(err),
                                        Ok(()) => match type_checker::infer_type_core(
                                            mode, st, fe, 0, &rhs_a,
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

/// con-leche: none — `fvs.map Expr.fvarTypeD` of `checkProjRule`/`checkIotaThm`
/// `List.map` over a `Vec<Expr>`; DESIGN.md §3.4 forbids the closure.
pub fn fvar_types(fvs: &Vec<Expr>) -> Vec<Expr> {
    fvar_types_from(fvs, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `fvar_types`
/// The accumulator is passed by value and returned (task #6's rule).
pub fn fvar_types_from(fvs: &Vec<Expr>, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= fvs.len() {
        out
    } else {
        let mut out = out;
        out.push(expr_ops::fvar_type_d(&fvs[i]));
        fvar_types_from(fvs, i + 1, out)
    }
}

#[cfg(test)]
mod tests {
    use crate::cached::state_c;
    use crate::cached::state_c::CState;
    use crate::kernel::basis_names;
    use crate::kernel::checker_base;
    use crate::kernel::core_types::CheckError;
    use crate::kernel::env::{CheckMode, ConstantInfo, ConstantVal};
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr};
    use crate::kernel::fenv;
    use crate::kernel::fenv::FEnv;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;

    pub fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn never_meta() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    fn ax(n: Name, ty: Expr) -> ConstantInfo {
        ConstantInfo::AxiomInfo(ConstantVal { name: n, level_params: Vec::new(), ty })
    }

    fn cv(n: Name, ty: Expr) -> ConstantVal {
        ConstantVal { name: n, level_params: Vec::new(), ty }
    }

    /// `A : Sort 1`, `a : A`, `f : forall (_ : A), A` — hand-built axioms,
    /// newest first as `Env.consts` is (`core_k`'s test environment).
    fn env_afa() -> FEnv {
        let a_ty = expr::mk_const(nm("A"), Vec::new());
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ax(
            nm("f"),
            expr::forall_e(expr::dup(&a_ty), expr::dup(&a_ty), never_meta()),
        ));
        consts.push(ax(nm("a"), expr::dup(&a_ty)));
        consts.push(ax(nm("A"), expr::sort(level::succ(level::zero()))));
        fenv::mk_fenv(crate::kernel::env::env_of(&consts))
    }

    fn is_invalid(e: &CheckError) -> bool {
        match e {
            CheckError::Invalid(_) => true,
            _ => false,
        }
    }

    /// **The duplicate-name guard.**  `checkConstantVal` on a name the
    /// environment already stores is `.invalid` — the first of the cited
    /// function's six syntactic guards, and the one every install path
    /// relies on for freshness.
    #[test]
    fn check_constant_val_rejects_a_duplicate_name() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let dup = cv(nm("a"), expr::mk_const(nm("A"), Vec::new()));
        match checker_base::check_constant_val(&mode, &mut st, &fe, &dup) {
            Ok(_) => panic!("a duplicate declaration must not check"),
            Err(e) => assert!(is_invalid(&e), "a duplicate is invalid, not a decline"),
        }
        // the same header under a fresh name goes through, with its type
        // annotated and its sort run
        let mut st2: CState = state_c::cstate_new();
        let fresh = cv(nm("b"), expr::mk_const(nm("A"), Vec::new()));
        match checker_base::check_constant_val(&mode, &mut st2, &fe, &fresh) {
            Ok(cva) => {
                assert!(name::beq(&cva.name, &nm("b")));
                assert!(expr::beq(&cva.ty, &expr::mk_const(nm("A"), Vec::new())));
            }
            Err(_) => panic!("a fresh constant over a resolving type must check"),
        }
        // a reserved basis name is invalid too
        let mut st3: CState = state_c::cstate_new();
        let reserved = cv(basis_names::eq_name(), expr::sort(level::succ(level::zero())));
        match checker_base::check_constant_val(&mode, &mut st3, &fe, &reserved) {
            Ok(_) => panic!("a reserved basis name must not check"),
            Err(e) => assert!(is_invalid(&e)),
        }
        // and so is a type mentioning an unstored constant
        let mut st4: CState = state_c::cstate_new();
        let unknown = cv(nm("c"), expr::mk_const(nm("Z"), Vec::new()));
        match checker_base::check_constant_val(&mode, &mut st4, &fe, &unknown) {
            Ok(_) => panic!("an unresolved type must not check"),
            Err(_) => (),
        }
    }

    /// `isEqHead` / `eqHeadLevel` read the pinned equality former at exactly
    /// one level, and `piResultSort` the sort a telescope ends in.
    #[test]
    fn the_equality_head_readers_and_pi_result_sort() {
        let one = level::succ(level::zero());
        let mut us: Vec<Level> = Vec::new();
        us.push(level::dup(&one));
        let head = expr::mk_const(basis_names::eq_name(), us);
        assert!(checker_base::is_eq_head(&head));
        assert!(level::beq(&checker_base::eq_head_level(&head), &one));
        // a bare `Eq` (no level) is not the head, and reads `.zero`
        let bare = expr::mk_const(basis_names::eq_name(), Vec::new());
        assert!(!checker_base::is_eq_head(&bare));
        assert!(level::beq(&checker_base::eq_head_level(&bare), &level::zero()));
        // another constant at one level is not the head either
        let mut us2: Vec<Level> = Vec::new();
        us2.push(level::dup(&one));
        assert!(!checker_base::is_eq_head(&expr::mk_const(nm("A"), us2)));
        // `piResultSort` of `forall (_ : A), Sort 1`
        let pi = expr::forall_e(
            expr::mk_const(nm("A"), Vec::new()),
            expr::sort(level::dup(&one)),
            never_meta(),
        );
        match checker_base::pi_result_sort(&pi) {
            Some(u) => assert!(level::beq(&u, &one)),
            None => panic!("the telescope ends in a sort"),
        }
        assert!(checker_base::pi_result_sort(&expr::mk_const(nm("A"), Vec::new())).is_none());
    }

    /// `openPisAtFvars` and its one-pass twin open the same telescope, and
    /// both refuse one that is too short.
    #[test]
    fn open_pis_at_fvars_and_its_one_pass_twin_agree() {
        let a = expr::mk_const(nm("A"), Vec::new());
        // `forall (x : A) (y : A), A`
        let ty = expr::forall_e(
            expr::dup(&a),
            expr::forall_e(expr::dup(&a), expr::dup(&a), never_meta()),
            never_meta(),
        );
        let slow = checker_base::open_pis_at_fvars(2, &ty, 0);
        let fast = checker_base::open_pis_at_fvars_f(2, &ty, 0);
        match (slow, fast) {
            (Some((fvs1, b1)), Some((fvs2, b2))) => {
                assert_eq!(fvs1.len(), 2);
                assert_eq!(fvs2.len(), 2);
                assert!(expr::beq(&fvs1[0], &expr::fvar(0, expr::dup(&a))));
                assert!(expr::beq(&fvs1[1], &expr::fvar(1, expr::dup(&a))));
                assert!(expr::beq(&fvs1[0], &fvs2[0]));
                assert!(expr::beq(&fvs1[1], &fvs2[1]));
                assert!(expr::beq(&b1, &b2));
                assert!(expr::beq(&b1, &a));
            }
            _ => panic!("both walks open a two-binder telescope"),
        }
        assert!(checker_base::open_pis_at_fvars(3, &ty, 0).is_none());
        assert!(checker_base::open_pis_at_fvars_f(3, &ty, 0).is_none());
        // and `n = 0` is the identity on any term
        match checker_base::open_pis_at_fvars_f(0, &a, 7) {
            Some((fvs, b)) => {
                assert_eq!(fvs.len(), 0);
                assert!(expr::beq(&b, &a));
            }
            None => panic!("zero binders always open"),
        }
    }

    /// `checkDefEqList` throws on a length difference, and `domsMatchAux`
    /// compares at the two offsets.
    #[test]
    fn the_list_checks_and_doms_match_aux() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm("A"), Vec::new());
        let mut xs: Vec<Expr> = Vec::new();
        xs.push(expr::dup(&a));
        let ys: Vec<Expr> = Vec::new();
        match checker_base::check_def_eq_list(&mode, &mut st, &fe, 0, &xs, &ys) {
            Ok(()) => panic!("a length difference must throw"),
            Err(_) => (),
        }
        // equal singletons check (the syntactic fast path answers)
        let mut ys2: Vec<Expr> = Vec::new();
        ys2.push(expr::dup(&a));
        match checker_base::check_def_eq_list(&mode, &mut st, &fe, 0, &xs, &ys2) {
            Ok(()) => (),
            Err(_) => panic!("A is definitionally equal to A"),
        }
        // `domsMatchAux` at offsets 1/0 over one position
        let mut bs1: Vec<(Expr, BinderMeta)> = Vec::new();
        bs1.push((expr::sort(level::zero()), never_meta()));
        bs1.push((expr::dup(&a), never_meta()));
        let mut bs2: Vec<(Expr, BinderMeta)> = Vec::new();
        bs2.push((expr::dup(&a), never_meta()));
        assert!(checker_base::doms_match_aux(&checker_base::DomIdent, &bs1, &bs2, 1, 0, 1));
        assert!(!checker_base::doms_match_aux(&checker_base::DomIdent, &bs1, &bs2, 0, 0, 1));
        // out of range is false, and zero positions is vacuously true
        assert!(!checker_base::doms_match_aux(&checker_base::DomIdent, &bs1, &bs2, 0, 0, 2));
        assert!(checker_base::doms_match_aux(&checker_base::DomIdent, &bs1, &bs2, 9, 9, 0));
    }
}
