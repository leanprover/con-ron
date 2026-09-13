//! `ConLeche/Kernel/CheckerSplit.lean` — the declaration checker **split at
//! the install/check seam** (con-leche task #253).
//!
//! `checker::check_decl` installs a declaration and checks it in one run.
//! For a `defn`, `thm` or `opaque` the two halves are separable: the
//! **install half** runs the syntactic guards and the annotation of the type
//! — and, for a definition or an opaque, of the value — and pushes the
//! constant; the **check half** runs the inferences and the conversion, and
//! reads only the environment the constant was installed at and the data the
//! install half produced.  Every other kind is not separable and its install
//! half IS `checkDecl`.
//!
//! These three functions are the two halves as pure functions over
//! `CheckerOps`: the specification the driver's cached twins (`annotValueC`,
//! `checkPending`, `Cached/Installed.lean`) simulate, with
//! `checkDecl_of_split_*` (`ConLeche/Verify/CheckerSplit.lean`) saying that
//! the two halves are `checkDecl`.  The datum that crosses the seam,
//! `ValueGroup`, and its `ValueKind` are `crate::cached::parsed_c` (task #14
//! took them with the other two seam records); `ValueKind.word` is not ported
//! — it renders the kind into a message string, and DESIGN.md §3.1 says
//! message strings need not match.
//!
//! The `CheckerOps` collapse and the `F`-twin collapse are
//! `kernel::checker_base`'s module note.

use crate::cached::parsed_c::{ValueGroup, ValueKind};
use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::checker_base;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env::{CheckMode, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::name;
use crate::kernel::prop_when;
use crate::kernel::type_checker;

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove checker_split::install_constant_val_refines, then delete this line
/// `checkConstantVal` minus its inference: the syntactic guards and the
/// annotation of the type.  The **install half** of the seam.
pub fn install_constant_val(
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
            Ok(ty) => {
                if !expr_ops::all_level_params_defined_fast(&cv.level_params, &ty) {
                    Err(core_types::invalid({ const M: [u32; 37] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
                } else if !core_k::consts_resolve(fe, &ty) {
                    Err(checker_base::unresolved_consts_error(&ty))
                } else {
                    Ok(ConstantVal {
                        name: name::dup(&cv.name),
                        level_params: prop_when::names_copy(&cv.level_params),
                        ty,
                    })
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove checker_split::install_value_refines, then delete this line
/// The value half of `check{Defn,Thm,Opaque}Val` minus its inference: the
/// guards and the annotation of the value.
pub fn install_value(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckM<Expr> {
    if !expr_ops::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, fe, 0, value) {
            Err(err) => Err(err),
            Ok(value_a) => {
                if !expr_ops::all_level_params_defined_fast(&cv.level_params, &value_a) {
                    Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
                } else if !core_k::consts_resolve(fe, &value_a) {
                    Err(checker_base::unresolved_consts_error(&value_a))
                } else {
                    Ok(value_a)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:36-42 ValueKind
/// `g.kind = .thm` as a constructor test — the cited `DecidableEq` instance
/// at the one value the check half branches on (`crate::cached::parsed_c`
/// holds the type).
pub fn is_thm(k: &ValueKind) -> bool {
    match k {
        ValueKind::Thm => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup
/// **The check half of a value declaration**, at the environment the constant
/// was installed at: the type's sort, the theorem's is-a-proposition test,
/// for a theorem the value's guards and annotation (a theorem's value reaches
/// the check half raw), and the value's type against the declared one — the
/// inference and conversion calls of `checkConstantVal` and
/// `check{Defn,Thm,Opaque}Val`, in their order.
pub fn check_value_group(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    g: &ValueGroup,
) -> CheckM<()> {
    match type_checker::infer_type_core(mode, st, fe, 0, &g.cv_a.ty) {
        Err(err) => Err(err),
        Ok(stype) => match type_checker::ensure_sort_core(mode, st, fe, 0, &stype) {
            Err(err) => Err(err),
            Ok(u) => {
                if is_thm(&g.kind) {
                    match core_k::lift_fueled(level::is_equiv(&u, &level::zero())) {
                        Err(err) => Err(err),
                        Ok(is_prop) => {
                            if is_prop {
                                match install_value(mode, st, fe, &g.cv_a, &g.jv) {
                                    Err(err) => Err(err),
                                    Ok(jv) => check_value_group_tail(mode, st, fe, g, jv),
                                }
                            } else {
                                Err(core_types::invalid({ const M: [u32; 36] = [116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110]; core_types::code_points(&M) }))
                            }
                        }
                    }
                } else {
                    check_value_group_tail(mode, st, fe, g, expr::dup(&g.jv))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup
/// The cited tail past the `let jv ← if …` join: the value's inferred type
/// against the declared one.  Split off so the two branches of the join are
/// tail calls (task #18's rule for a gated certificate whose arms rejoin).
pub fn check_value_group_tail(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    g: &ValueGroup,
    jv: Expr,
) -> CheckM<()> {
    match type_checker::infer_type_core(mode, st, fe, 0, &jv) {
        Err(err) => Err(err),
        Ok(vtype) => match type_checker::is_def_eq_core(mode, st, fe, 0, &vtype, &g.cv_a.ty) {
            Err(err) => Err(err),
            Ok(ok) => {
                if ok {
                    Ok(())
                } else {
                    Err(core_types::invalid({ const M: [u32; 28] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
                }
            }
        },
    }
}

/* Not ported here: `checkConstantVal`'s and `check{Defn,Thm,Opaque}Val`'s
   own bodies are `kernel::checker_base` and `kernel::checker`; this file
   only re-cuts them at the seam.  `ValueKind` and `ValueGroup` are
   `crate::cached::parsed_c` (task #14), and `ValueKind.word` (`:44-48`) is
   message rendering only. */
