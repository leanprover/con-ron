//! `arena::checker_split` — the install/check seam of a value declaration.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckerSplit.lean`, which is
//! con-leche's `Kernel/CheckerSplit.lean`: `checkDecl`'s three value kinds
//! split into an INSTALL half (the syntactic guards) and a CHECK half (the
//! inference and the conversion), with `ValueGroup` as the datum that crosses
//! the seam.  Since con-leche's task #342 the install half computes nothing
//! but verdicts: the constant is stored as declared.
//!
//! **This is where (C)'s per-declaration bracket lives** (DESIGN.md §8.3, and
//! `arena::checker`'s `check_pending`).  `arena::core`'s `enter_scratch` /
//! `drop_scratch` bracket the CHECK half and nothing else, because the split is
//! exactly the line between what a declaration LEAVES BEHIND and what it merely
//! computes:
//!
//! * the install half stores the declared type and value, which the parse
//!   already put in the persistent tier;
//! * the check half infers the type's sort, infers the value's type and
//!   compares it with the declared one.  Everything it allocates is
//!   intermediate, and the scratch tier is dropped at its end.
//!
//! `ValueKind.word` IS ported, where `con_ron_core::kernel::checker_split`
//! skips it: it renders the kind into the type-mismatch message, and the port
//! drops the *name* interpolation (§3.1) but keeps the KIND, because that word
//! is what makes the two folds — `check_decls_pure`'s
//! `check{Defn,Thm,Opaque}Val` and `install_then_check`'s `check_value_group`
//! — report the same message on the same stream.  con-ron-core's two lanes
//! differ there ("type mismatch in definition" against "type mismatch in
//! declaration") and nothing of it compares them; the arena's differential
//! test does (`chk_install` against `check_decls_pure`), which is exactly the
//! agreement con-leche's `fullyChecked_checkDecls` is about.

use crate::arena::checker_base::{
    check_constant_val_guards, consts_resolve_f_fast, install_header_tail,
    unresolved_consts_fail,
};
use crate::arena::checker_base::all_level_params_defined;
use crate::arena::core::{
    ensure_sort_core, infer_type_core, is_def_eq_core, lift_fueled, lvl_eq, zero_level,
    CHECK_FUEL, CORE_WALK_FUEL,
};
use crate::arena::env::{IConstantVal, IFEnv};
use crate::arena::expr_ops::{has_fvar_fast, loose_bvars_bounded_fast};
use crate::arena::handle::EIdx;
use crate::arena::monad::{fail, AState};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::ron::hashmap::Dup;
use crate::arena::store::PersTier;

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
/// `"type mismatch in definition"`, as code points.
pub const M_TYPE_MISMATCH_DEFN: [u32; 27] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100,
    101, 102, 105, 110, 105, 116, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type mismatch in theorem"`, as code points.
pub const M_TYPE_MISMATCH_THM: [u32; 24] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116,
    104, 101, 111, 114, 101, 109
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type mismatch in opaque"`, as code points.
pub const M_TYPE_MISMATCH_OPAQUE: [u32; 23] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 111,
    112, 97, 113, 117, 101
];

// ---------------------------------------------------------------------------
// The seam's records (`CheckerSplit.lean:33-58` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:36-42 ValueKind
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:33-40 ValueKind` — the
/// three declaration kinds whose value check is separable from their install.
/// Census class (P): no term in it, copied verbatim.
pub enum ValueKind {
    Defn,
    Thm,
    Opaque,
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:44-48 ValueKind.word
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:42-47 ValueKind.word` — the
/// kind's word in `checkDecl`'s type-mismatch message.  The twin returns the
/// word and the caller interpolates it into a `String`; the port has the three
/// whole messages as constants and returns the one the kind selects, which is
/// the same three strings minus the name (the module note).
pub fn value_kind_word(k: &ValueKind) -> Vec<u32> {
    match k {
        ValueKind::Defn => code_points(&M_TYPE_MISMATCH_DEFN),
        ValueKind::Thm => code_points(&M_TYPE_MISMATCH_THM),
        ValueKind::Opaque => code_points(&M_TYPE_MISMATCH_OPAQUE),
    }
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

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:50-58 ValueGroup
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:49-58 ValueGroup` — what
/// the install half hands the check half: the kind, the header and the value
/// — guarded for a definition or an opaque, unguarded for a theorem (the
/// install half never looked at it: a theorem is stored by its statement, and
/// the check half runs the value's guards itself).  Task #119: the header
/// field is `cv` (con-leche's `cvA`, the annotated header, is gone).
pub struct ValueGroup {
    pub kind: ValueKind,
    pub cv: IConstantVal,
    pub jv: EIdx,
}

// ---------------------------------------------------------------------------
// The install half (`CheckerSplit.lean:60-101` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:63-81 installHeader
/// con-leche: ConLeche/Cached/Installed.lean:94-113 installHeaderC
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:60-84 installHeader` —
/// `checkConstantVal` minus its inference: the syntactic guards, header and
/// type.  con-leche writes the clauses out twice and so does the twin; the
/// port writes them once, as `arena::checker_base::{check_constant_val_guards,
/// install_header_tail}`, and both front doors call them.  Task #119: was
/// `installConstantVal`, which also annotated the type and returned the
/// annotated header.
pub fn install_header(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    match check_constant_val_guards(pers, vis, st, fe, cv) {
        Err(e) => Err(e),
        Ok(()) => install_header_tail(pers, vis, st, fe, cv),
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:83-94 installValueGuards
/// con-leche: ConLeche/Cached/Installed.lean:115-125 installValueGuardsC
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:86-101 installValueGuards`
/// — the value half of `check{Defn,Thm,Opaque}Val` minus its inference: the
/// value's syntactic guards (no loose bound variable, no free variable,
/// declared universe parameters, resolving constants).  Task #119: was
/// `installValue`, which also annotated the value.
pub fn install_value_guards(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(), CheckError> {
    match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, value) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                fail(CheckError::Invalid(code_points(&M_LOOSE_VALUE)))
            } else {
                match has_fvar_fast(pers, st, CORE_WALK_FUEL, value) {
                    Err(e) => Err(e),
                    Ok(f) => {
                        if f {
                            fail(CheckError::Invalid(code_points(&M_FVAR_VALUE)))
                        } else {
                            install_value_guards_tail(pers, vis, st, fe, cv, value)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:83-94 installValueGuards
/// con-leche: ConLeche/Cached/Installed.lean:115-125 installValueGuardsC
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:86-101 installValueGuards`
/// — the two guards past the scope tests: the level-parameter and the
/// resolution guard (else `unresolvedConstsErrorL`'s verdict).
pub fn install_value_guards_tail(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(), CheckError> {
    match all_level_params_defined(pers, st, &cv.level_params, value) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                fail(CheckError::Invalid(code_points(&M_UNDECL_VALUE)))
            } else {
                match consts_resolve_f_fast(pers, vis, st, fe, value) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        if !r {
                            unresolved_consts_fail(pers, vis, st, fe, value)
                        } else {
                            Ok(())
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

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:96-112 checkValueGroup
/// con-leche: ConLeche/Cached/Installed.lean:254-272 checkPending
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:103-121 checkValueGroup` —
/// **the check half of a value declaration**, at the environment the constant
/// was installed at: the type's sort, the theorem's is-a-proposition test, for
/// a theorem the value's guards, and the value's type against the declared one
/// — the inference and conversion calls of `checkConstantVal` and
/// `check{Defn,Thm,Opaque}Val`, in their order, with their messages.
pub fn check_value_group(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ValueGroup,
) -> Result<(), CheckError> {
    match infer_type_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &g.cv.ty) {
        Err(e) => Err(e),
        Ok(stype) => match ensure_sort_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &stype) {
            Err(e) => Err(e),
            Ok(u) => check_value_group_value(pers, vis, st, mode, fe, g, &u),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:96-112 checkValueGroup
/// con-leche: ConLeche/Cached/Installed.lean:254-272 checkPending
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:103-121 checkValueGroup` —
/// the cited `if g.kind = .thm then …`: a theorem's statement must be a
/// proposition, and its raw value's guards run here.  A definition's or an
/// opaque's value was guarded at the install.
pub fn check_value_group_value(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ValueGroup,
    u: &crate::arena::handle::LIdx,
) -> Result<(), CheckError> {
    if is_thm(&g.kind) {
        match zero_level(st) {
            Err(e) => Err(e),
            Ok(z) => match lvl_eq(pers, st, u, &z) {
                Err(e) => Err(e),
                Ok(o) => match lift_fueled(o) {
                    Err(e) => Err(e),
                    Ok(is_prop) => {
                        if is_prop {
                            match install_value_guards(pers, vis, st, fe, &g.cv, &g.jv) {
                                Err(e) => Err(e),
                                Ok(()) => check_value_group_tail(pers, vis, st, mode, fe, g),
                            }
                        } else {
                            fail(CheckError::Invalid(code_points(&M_THM_NOT_PROP)))
                        }
                    }
                },
            },
        }
    } else {
        check_value_group_tail(pers, vis, st, mode, fe, g)
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:96-112 checkValueGroup
/// con-leche: ConLeche/Cached/Installed.lean:254-272 checkPending
/// Lean twin: `proof/ConRon/Arena/CheckerSplit.lean:103-121 checkValueGroup` —
/// the cited tail past the theorem's test: the value's inferred type against
/// the declared one.  Split off so the two branches of the `if` are tail
/// calls.
pub fn check_value_group_tail(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ValueGroup,
) -> Result<(), CheckError> {
    match infer_type_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &g.jv) {
        Err(e) => Err(e),
        Ok(vtype) => {
            match is_def_eq_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &vtype, &g.cv.ty) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(())
                    } else {
                        fail(CheckError::Invalid(value_kind_word(&g.kind)))
                    }
                }
            }
        }
    }
}
