//! `arena::checker_split` — the install/check seam of a value declaration.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckerSplit.lean`, which is
//! con-leche's `Kernel/CheckerSplit.lean`: `checkDecl`'s three value kinds
//! split into an INSTALL half (the syntactic guards and the annotation) and a
//! CHECK half (the inference and the conversion), with `ValueGroup` as the
//! datum that crosses the seam.
//!
//! **This is where (C)'s per-declaration bracket lives** (DESIGN.md §8.3, and
//! `arena::checker`'s `check_pending`).  `arena::core`'s `enter_scratch` /
//! `drop_scratch` bracket the CHECK half and nothing else, because the split is
//! exactly the line between what a declaration LEAVES BEHIND and what it merely
//! computes:
//!
//! * the install half writes the annotated type and the annotated value, and
//!   those are the terms the environment stores — so they must be PERSISTENT,
//!   and the half runs outside the bracket;
//! * the check half infers the type's sort, infers the value's type and
//!   compares it with the declared one.  Everything it allocates is
//!   intermediate, and the scratch tier is dropped at its end.
//!
//! `ValueKind.word` (`CheckerSplit.lean:44-48`) has no Rust counterpart: it
//! renders the kind into the type-mismatch message, and the port drops the
//! interpolation (§3.1), so the message is one constant for all three kinds —
//! `con_ron_core::kernel::checker_split`'s own note says the same.

use crate::arena::checker_base::{
    check_constant_val_guards, consts_resolve_f_fast, install_constant_val_tail,
    unresolved_consts_error,
};
use crate::arena::checker_base::all_level_params_defined;
use crate::arena::core::{
    annotate_core, ensure_sort_core, infer_type_core, is_def_eq_core, lift_fueled, lvl_eq,
    zero_level, CHECK_FUEL, CORE_WALK_FUEL,
};
use crate::arena::env::{IConstantVal, IFEnv};
use crate::arena::expr_ops::{has_fvar_fast, loose_bvars_bounded_fast};
use crate::arena::handle::EIdx;
use crate::arena::monad::{fail, AState};
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::ron::hashmap::Dup;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"loose bound variable in value"`, as code points.
pub const M_LOOSE_VALUE: [u32; 29] = [
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98,
    108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unexpected free variable in value"`, as code points.
pub const M_FVAR_VALUE: [u32; 33] = [
    117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97,
    114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"undeclared universe parameter in value"`, as code points.
pub const M_UNDECL_VALUE: [u32; 38] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115,
    101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108,
    117, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type of theorem is not a proposition"`, as code points.
pub const M_THM_NOT_PROP: [u32; 36] = [
    116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115,
    32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type mismatch in declaration"`, as code points.
pub const M_TYPE_MISMATCH_DECL: [u32; 28] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100,
    101, 99, 108, 97, 114, 97, 116, 105, 111, 110
];

// ---------------------------------------------------------------------------
// The seam's records (`CheckerSplit.lean:33-58` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:36-42 ValueKind
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:36-40 ValueKind` — the
/// three declaration kinds whose value check is separable from their install.
/// Census class (P): no term in it, copied verbatim.
pub enum ValueKind {
    Defn,
    Thm,
    Opaque,
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:36-42 ValueKind
/// The cited `deriving DecidableEq` at the one value the check half branches
/// on (`g.kind = .thm`), spelled as a constructor test.
pub fn is_thm(k: &ValueKind) -> bool {
    match k {
        ValueKind::Thm => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:50-59 ValueGroup
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:54-58 ValueGroup` — what
/// the install half hands the check half: the kind, the header with its type
/// annotated, and the value — ANNOTATED for a definition or an opaque, RAW for
/// a theorem (the install half never looked at it: a theorem is stored by its
/// statement, and the check half annotates the value itself).
pub struct ValueGroup {
    pub kind: ValueKind,
    pub cv_a: IConstantVal,
    pub jv: EIdx,
}

// ---------------------------------------------------------------------------
// The install half (`CheckerSplit.lean:60-101` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:64-84 installConstantVal`
/// — `checkConstantVal` minus its inference: the syntactic guards and the
/// annotation of the type.  con-leche writes the shared clauses out twice and
/// so does the twin; the port writes them once, as
/// `arena::checker_base::{check_constant_val_guards, install_constant_val_tail}`,
/// and both front doors call them — the two functions ARE the twin's two
/// clause groups, so nothing is lost and a drift between the halves is
/// impossible.
pub fn install_constant_val(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<IConstantVal, CheckError> {
    match check_constant_val_guards(st, fe, cv) {
        Err(e) => Err(e),
        Ok(()) => match annotate_core(st, mode, fe, CHECK_FUEL, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(ty) => install_constant_val_tail(st, fe, cv, ty),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:89-101 installValue` — the
/// value half of `check{Defn,Thm,Opaque}Val` minus its inference: the guards
/// and the annotation of the value.
pub fn install_value(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<EIdx, CheckError> {
    match loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, value) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                fail(CheckError::Invalid(code_points(&M_LOOSE_VALUE)))
            } else {
                match has_fvar_fast(st, CORE_WALK_FUEL, value) {
                    Err(e) => Err(e),
                    Ok(f) => {
                        if f {
                            fail(CheckError::Invalid(code_points(&M_FVAR_VALUE)))
                        } else {
                            match annotate_core(st, mode, fe, CHECK_FUEL, 0, value) {
                                Err(e) => Err(e),
                                Ok(value_a) => install_value_tail(st, fe, cv, value_a),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:89-101 installValue` — the
/// tail past the annotation: the level-parameter and resolution guards on the
/// ANNOTATED value.
pub fn install_value_tail(
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    value_a: EIdx,
) -> Result<EIdx, CheckError> {
    match all_level_params_defined(st, &cv.level_params, &value_a) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                fail(CheckError::Invalid(code_points(&M_UNDECL_VALUE)))
            } else {
                match consts_resolve_f_fast(st, fe, &value_a) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        if !r {
                            match unresolved_consts_error(st, &value_a) {
                                Err(e) => Err(e),
                                Ok(e) => fail(e),
                            }
                        } else {
                            Ok(value_a)
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The check half (`CheckerSplit.lean:103-124` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:109-123 checkValueGroup` —
/// **the check half of a value declaration**, at the environment the constant
/// was installed at: the type's sort, the theorem's is-a-proposition test, for
/// a theorem the value's guards and annotation, and the value's type against
/// the declared one — the inference and conversion calls of `checkConstantVal`
/// and `check{Defn,Thm,Opaque}Val`, in their order, with their messages.
pub fn check_value_group(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ValueGroup,
) -> Result<(), CheckError> {
    match infer_type_core(st, mode, fe, CHECK_FUEL, 0, &g.cv_a.ty) {
        Err(e) => Err(e),
        Ok(stype) => match ensure_sort_core(st, mode, fe, CHECK_FUEL, 0, &stype) {
            Err(e) => Err(e),
            Ok(u) => check_value_group_value(st, mode, fe, g, &u),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:109-123 checkValueGroup` —
/// the cited `let jv ← if g.kind = .thm then … else pure g.jv`: a theorem's
/// statement must be a proposition, and its raw value's guards and annotation
/// run here.  A definition's or an opaque's value was annotated at the install
/// and is taken as it is.
pub fn check_value_group_value(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ValueGroup,
    u: &crate::arena::handle::LIdx,
) -> Result<(), CheckError> {
    if is_thm(&g.kind) {
        match zero_level(st) {
            Err(e) => Err(e),
            Ok(z) => match lvl_eq(st, u, &z) {
                Err(e) => Err(e),
                Ok(o) => match lift_fueled(o) {
                    Err(e) => Err(e),
                    Ok(is_prop) => {
                        if is_prop {
                            match install_value(st, mode, fe, &g.cv_a, &g.jv) {
                                Err(e) => Err(e),
                                Ok(jv) => check_value_group_tail(st, mode, fe, g, jv),
                            }
                        } else {
                            fail(CheckError::Invalid(code_points(&M_THM_NOT_PROP)))
                        }
                    }
                },
            },
        }
    } else {
        check_value_group_tail(st, mode, fe, g, g.jv.dup2())
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:109-123 checkValueGroup` —
/// the cited tail past the `let jv ← if …` join: the value's inferred type
/// against the declared one.  Split off so the two branches of the join are
/// tail calls.
pub fn check_value_group_tail(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ValueGroup,
    jv: EIdx,
) -> Result<(), CheckError> {
    match infer_type_core(st, mode, fe, CHECK_FUEL, 0, &jv) {
        Err(e) => Err(e),
        Ok(vtype) => {
            match is_def_eq_core(st, mode, fe, CHECK_FUEL, 0, &vtype, &g.cv_a.ty) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(())
                    } else {
                        fail(CheckError::Invalid(code_points(&M_TYPE_MISMATCH_DECL)))
                    }
                }
            }
        }
    }
}
