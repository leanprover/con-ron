//! `arena::check_decl` — the checker's fold step, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckDecl.lean`, which is con-leche's
//! `Kernel/CheckDecl.lean`: `checkShapeless`, `checkDecl` and
//! `checkDeclsPure` (moved out of `Kernel/Checker.lean` upstream, because the
//! uniform inductive route's stages sit above the checker's value stages).
//! The stages it dispatches to are `arena::checker`'s (the pinned basis
//! install), `arena::decl_check`'s (values, the certified `Nat` operations,
//! the pinned axioms) and `arena::inductives::block_tail`'s (the uniform
//! inductive route).
//!
//! ## The twin's deviations
//!
//! * **The one `match d with` is one dispatch and seven arm functions**, so
//!   every arm stays a tail call (task #97-P4c's split rule), as it was when
//!   this code lived in `arena::checker`.
//! * **The executed tier's flushes are where `Cached/ParsedC.lean` and
//!   `Cached/CheckerC.lean` put them** (task #97g item 4): the arena has one
//!   environment representation and one core, the cached one.

use crate::arena::basis::{basis_kind_decls, basis_pin_hit, quot_pin_hit};
use crate::arena::canon::i_constant_info_canon_eq;
use crate::arena::checker::check_basis_decl;
use crate::arena::checker_base;
use crate::arena::checker_base::{check_constant_val, nidx_contains_from};
use crate::arena::core::{
    drop_scratch, enter_scratch, flush_caches, nat_div_mod_names, nat_op_deps,
    nat_op_equations, nat_op_guard, nat_op_names, CORE_WALK_FUEL,
};
use crate::arena::decl_check::{
    certify_nat_eqs, check_defn_val, check_div_mod_pin, check_opaque_val, check_reduce_pin,
    check_thm_val, defn_value, nat_op_stored_ok_all, of_reduce_ax_ok,
    std_axiom_ok, subst_const0_pairs, trust_compiler_ok,
};
use crate::arena::env::{
    i_constant_info_dup, i_constant_val_dup, i_env_empty, ifenv_restrict_to, mk_ifenv, IConstantInfo,
    IConstantVal, IDeclaration, IFEnv,
};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::inductives::{block_parts, block_tail};
use crate::arena::monad::{fail, AState};
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::promote::{promote_new, PMemo};
use crate::arena::std_axioms::{choice_name, propext_name};
use crate::arena::trust_axioms::{
    of_reduce_bool_name, of_reduce_nat_name, reduce_op_names, trust_compiler_name,
};
use crate::arena::pins::{pin_quot_sound, pin_sorry_ax};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{BasisKind, CheckMode, QuotKind, ReducibilityHint};
use crate::ron::hashmap::Eq2;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's rejects and declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'number of parameters mismatch'`, as code points.
pub const M_NUM_PARAMS: [u32; 29] = [
    110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
    32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'inductive block : shape not recognised'`, as code points — the cited
/// message with the block's name dropped (§3.1: the port drops the
/// interpolation).
pub const M_SHAPELESS: [u32; 38] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 58, 32, 115, 104,
    97, 112, 101, 32, 110, 111, 116, 32, 114, 101, 99, 111, 103, 110, 105, 115, 101, 100,
];


// ---------------------------------------------------------------------------
// A block the recogniser does not read
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckDecl.lean:26-38 checkShapeless
/// con-leche: ConLeche/Cached/ParsedC.lean:78-86 checkShapelessS
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:67-78 checkShapeless` — **an
/// inductive block the recogniser does not read**: its type formers are
/// checked as constants (a reserved name, a duplicate, a malformed type are
/// official's rejects and stay rejects), and what survives that is a POSITIVE
/// decline, since the uniform route takes every block it recognises.  It never
/// returns an environment.
pub fn check_shapeless(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
) -> Result<IFEnv, CheckError> {
    match check_shapeless_formers(pers, st, mode, &fe, block, 0) {
        Err(e) => Err(e),
        Ok(()) => fail(CheckError::NotImplemented(code_points(&M_SHAPELESS))),
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:26-38 checkShapeless
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:67-78 checkShapeless` — the cited
/// `block.foldlM`, as an index recursion (§3.4 forbids the closure): every
/// type former checked as a constant and discarded, every other member
/// skipped.
pub fn check_shapeless_formers(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    block: &Vec<IConstantInfo>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= block.len() {
        Ok(())
    } else {
        match &block[i] {
            IConstantInfo::IndInfo(cv, _) => {
                match check_constant_val(pers, fe.visible_below, st, mode, fe, cv) {
                    Err(e) => Err(e),
                    Ok(_) => check_shapeless_formers(pers, st, mode, fe, block, i + 1),
                }
            }
            _ => check_shapeless_formers(pers, st, mode, fe, block, i + 1),
        }
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quotient soundness axiom mismatch"`, as code points.
pub const M_QUOT_SOUND_MISMATCH: [u32; 33] = [
    113, 117, 111, 116, 105, 101, 110, 116, 32, 115, 111, 117, 110, 100, 110, 101, 115,
    115, 32, 97, 120, 105, 111, 109, 32, 109, 105, 115, 109, 97, 116, 99, 104
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quotient declaration mismatch"`, as code points.
pub const M_QUOT_DECL_MISMATCH: [u32; 29] = [
    113, 117, 111, 116, 105, 101, 110, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
    111, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"nonstandard structural Nat operation environment"`, as code points.
pub const M_NONSTD_NAT_ENV: [u32; 48] = [
    110, 111, 110, 115, 116, 97, 110, 100, 97, 114, 100, 32, 115, 116, 114, 117, 99, 116,
    117, 114, 97, 108, 32, 78, 97, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110,
    32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"structural Nat operation not stored"`, as code points.
pub const M_NAT_NOT_STORED: [u32; 35] = [
    115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 78, 97, 116, 32, 111, 112, 101,
    114, 97, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"nonstandard structural Nat operation"`, as code points.
pub const M_NONSTD_NAT: [u32; 36] = [
    110, 111, 110, 115, 116, 97, 110, 100, 97, 114, 100, 32, 115, 116, 114, 117, 99, 116,
    117, 114, 97, 108, 32, 78, 97, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported Lean.trustCompiler shape"`, as code points.
pub const M_TRUSTCOMPILER_SHAPE: [u32; 36] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 76, 101, 97, 110, 46, 116,
    114, 117, 115, 116, 67, 111, 109, 112, 105, 108, 101, 114, 32, 115, 104, 97, 112, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust axiom environment"`, as code points.
pub const M_TRUST_AXIOM_ENV: [u32; 44] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105,
    108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 97, 120, 105, 111, 109, 32, 101, 110,
    118, 105, 114, 111, 110, 109, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"standard axiom shape mismatch"`, as code points.
pub const M_STD_AXIOM_SHAPE: [u32; 29] = [
    115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109, 32, 115, 104, 97,
    112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"non-standard axiom"`, as code points.
pub const M_NONSTD_AXIOM: [u32; 18] = [
    110, 111, 110, 45, 115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109
];

// ---------------------------------------------------------------------------
// One declaration (`Checker.lean:80-192` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — **check a
/// single declaration, extending the environment on success.**  The twin's one
/// `match d with` is one dispatch and seven arm functions here, so every arm
/// stays a tail call (task #97-P4c's split rule).
pub fn check_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    d: &IDeclaration,
) -> Result<IFEnv, CheckError> {
    match d {
        IDeclaration::DefnDecl(cv, value, hint) => {
            check_defn_decl(pers, st, mode, pins, fe, cv, value, hint)
        }
        IDeclaration::ThmDecl(cv, value) => check_thm_decl(pers, st, mode, fe, cv, value),
        IDeclaration::OpaqueDecl(cv, value) => check_opaque_decl(pers, st, mode, fe, cv, value),
        IDeclaration::AxiomDecl(cv) => check_axiom_decl(pers, st, mode, fe, cv),
        IDeclaration::BasisDecl(kind) => check_basis_decl(pers, st, fe, kind),
        IDeclaration::IndDecl(block, n_p) => check_ind_decl(pers, st, mode, fe, block, *n_p),
        IDeclaration::QuotDecl(k, cv) => check_quot_decl(pers, st, fe, k, cv),
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `.defnDecl` arm: the common constant check, the value check, then the two
/// pinned-`Nat` gates.
///
/// Deviation: the twin holds `fe` (pre-insertion) and `fe2` (extended) at once;
/// `IFEnv` has no cheap copy, so the port keeps ONE index and remembers the
/// pre-insertion visibility bound `k_pre` —
/// `con_ron_core::kernel::checker::check_defn_decl`'s own arrangement.
pub fn check_defn_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<IFEnv, CheckError> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match check_defn_val(pers, st, mode, fe, &cv_a, value, hint) {
            Err(e) => Err(e),
            Ok(fe2) => check_defn_pins(pers, st, mode, pins, fe2, k_pre, &cv_a.name),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `.defnDecl` arm's two pinned-`Nat` gates, in the twin's order.
pub fn check_defn_pins(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match nat_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, n) {
                match check_structural_nat_pin(pers, st, mode, fe2, k_pre, n) {
                    Err(e) => Err(e),
                    Ok(fe3) => check_defn_div_mod_pin(pers, st, mode, pins, fe3, k_pre, n),
                }
            } else {
                check_defn_div_mod_pin(pers, st, mode, pins, fe2, k_pre, n)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `natDivModNames.contains` gate of the `.defnDecl` arm.
pub fn check_defn_div_mod_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match nat_div_mod_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, n) {
                check_div_mod_pin(pers, st, mode, pins, fe2, k_pre, n)
            } else {
                Ok(fe2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// structural-`Nat` gate: the environment guards at the EXTENDED environment,
/// then `certifyNatEqs` at the PRE-insertion one over the equations with the
/// operation's self-references substituted.  Certifying after insertion would
/// let the operation's own fast path discharge its all-literal equations
/// vacuously.
pub fn check_structural_nat_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match nat_op_guard(pers, fe2.visible_below, st, &fe2, n) {
        Err(e) => Err(e),
        Ok(g) => match nat_op_deps(st, n) {
            Err(e) => Err(e),
            Ok(deps) => match nat_op_stored_ok_all(pers, fe2.visible_below, st, &fe2, &deps, 0) {
                Err(e) => Err(e),
                Ok(d) => {
                    if !g || !d {
                        fail(CheckError::NotImplemented(code_points(&M_NONSTD_NAT_ENV)))
                    } else {
                        check_structural_nat_pin_eqs(pers, st, mode, fe2, k_pre, n)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the stored
/// value, the equations, and their certification at the pre-insertion view.
pub fn check_structural_nat_pin_eqs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match defn_value(fe2.visible_below, &fe2, n) {
        None => fail(CheckError::Internal(code_points(&M_NAT_NOT_STORED))),
        Some(value2) => match nat_op_equations(pers, st, 0, n) {
            Err(e) => Err(e),
            Ok(eqs) => match subst_const0_pairs(pers, st, n, &value2, &eqs, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(seqs) => check_structural_nat_pin_certify(pers, st, mode, fe2, k_pre, &seqs),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// certification itself, with the index restricted to the pre-insertion bound
/// and handed back at the bound it came in at (the arm's standing deviation).
pub fn check_structural_nat_pin_certify(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    seqs: &Vec<(EIdx, EIdx)>,
) -> Result<IFEnv, CheckError> {
    let k2: u64 = fe2.visible_below;
    let fe_pre: IFEnv = ifenv_restrict_to(fe2, k_pre);
    let r: Result<bool, CheckError> = certify_nat_eqs(pers, fe_pre.visible_below, st, mode, &fe_pre, seqs, 0);
    let fe3: IFEnv = ifenv_restrict_to(fe_pre, k2);
    match r {
        Err(e) => Err(e),
        Ok(ok) => {
            if ok {
                Ok(fe3)
            } else {
                fail(CheckError::NotImplemented(code_points(&M_NONSTD_NAT)))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `.thmDecl` arm.
pub fn check_thm_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match check_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => check_thm_val(pers, st, mode, fe, &cv_a, value),
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `.opaqueDecl` arm: the opaque check, then the compiler-trust gate for
/// `Lean.reduceNat`/`Lean.reduceBool`.
pub fn check_opaque_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match check_opaque_val(pers, st, mode, fe, &cv_a, value) {
            Err(e) => Err(e),
            Ok(fe2) => check_opaque_reduce_pin(pers, st, mode, fe2, k_pre, &cv_a.name, value),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `reduceOpNames.contains` gate of the `.opaqueDecl` arm.
pub fn check_opaque_reduce_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match reduce_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, n) {
                check_reduce_pin(pers, st, mode, fe2, k_pre, n, value)
            } else {
                Ok(fe2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `.axiomDecl` arm.  **`Quot.sound` is the pinned quotient BLOCK's own
/// record**: the export writes it as an ordinary axiom record beside the four
/// `#QUOT` ones, so it arrives here — compared with the pin and installing
/// NOTHING of its own, and DECLINING when it does not match.  The comparison
/// precedes the common checks because the name is a reserved basis name: this
/// record IS the pinned block's, not a redeclaration of it.
pub fn check_axiom_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match pin_quot_sound(st) {
        Err(e) => Err(e),
        Ok(qs) => {
            if cv.name.eq2(&qs) {
                check_quot_sound_record(pers, st, fe, cv)
            } else {
                check_axiom_decl_std(pers, st, mode, fe, cv)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `.axiomDecl` arm's `Quot.sound` test, against slot 4 of the pinned quotient
/// block.  The twin's `blk[4]?` is the bound test; the block has exactly five
/// members, so the `none` arm is unreachable and declines, as the twin's does.
pub fn check_quot_sound_record(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match basis_kind_decls(pers, st, &BasisKind::QuotK) {
        Err(e) => Err(e),
        Ok(blk) => {
            if blk.len() <= 4 {
                fail(CheckError::NotImplemented(code_points(
                    &M_QUOT_SOUND_MISMATCH,
                )))
            } else {
                let pinned: IConstantInfo = i_constant_info_dup(&blk[4]);
                let mine: IConstantInfo =
                    IConstantInfo::AxiomInfo(i_constant_val_dup(cv));
                match i_constant_info_canon_eq(pers, st, &mine, &pinned) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        if r {
                            Ok(fe)
                        } else {
                            fail(CheckError::NotImplemented(code_points(
                                &M_QUOT_SOUND_MISMATCH,
                            )))
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the rest of
/// the `.axiomDecl` arm: the two standard axioms and the `Init` compiler-trust
/// family are INSTALLED, `sorryAx` is tolerated and installs nothing, and
/// anything else — including a pinned NAME with a non-pinned shape — is a
/// positive decline at its own record.
pub fn check_axiom_decl_std(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match check_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match std_axiom_ok(pers, fe.visible_below, st, &fe, &cv_a) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    Ok(crate::arena::env::ifenv_push(
                        fe,
                        IConstantInfo::AxiomInfo(cv_a),
                    ))
                } else {
                    check_axiom_decl_trust(pers, st, fe, cv_a)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the
/// `Lean.trustCompiler` branch: `True` is trivially realizable, so the axiom is
/// installed exactly like a checked `opaque` with witness `True.intro` over the
/// pinned `True` family.
pub fn check_axiom_decl_trust(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv_a: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match trust_compiler_name(st) {
        Err(e) => Err(e),
        Ok(tn) => {
            if cv_a.name.eq2(&tn) {
                match trust_compiler_ok(pers, fe.visible_below, st, &fe, &cv_a) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        if ok {
                            Ok(crate::arena::env::ifenv_push(
                                fe,
                                IConstantInfo::AxiomInfo(cv_a),
                            ))
                        } else {
                            fail(CheckError::NotImplemented(code_points(
                                &M_TRUSTCOMPILER_SHAPE,
                            )))
                        }
                    }
                }
            } else {
                check_axiom_decl_of_reduce(pers, st, fe, cv_a)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the pinned
/// `ofReduce*` axioms: over the pinned `Eq` basis, the element inductive and
/// the identity-certified reduce opaque, `∀ a b, reduce a = b → a = b`
/// interprets to an inhabited proposition.
pub fn check_axiom_decl_of_reduce(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv_a: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match of_reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(on) => match of_reduce_bool_name(st) {
            Err(e) => Err(e),
            Ok(ob) => {
                if cv_a.name.eq2(&on) || cv_a.name.eq2(&ob) {
                    match of_reduce_ax_ok(pers, fe.visible_below, st, &fe, &cv_a) {
                        Err(e) => Err(e),
                        Ok(ok) => {
                            if ok {
                                Ok(crate::arena::env::ifenv_push(
                                    fe,
                                    IConstantInfo::AxiomInfo(cv_a),
                                ))
                            } else {
                                fail(CheckError::NotImplemented(code_points(
                                    &M_TRUST_AXIOM_ENV,
                                )))
                            }
                        }
                    }
                } else {
                    check_axiom_decl_rest(st, fe, cv_a)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the last
/// three tests: a pinned standard-axiom NAME whose shape did not match
/// declines under its own message, `sorryAx` is tolerated as a DECLARATION and
/// installs nothing (a USE of it declines at the record that uses it), and
/// every other axiom is a positive decline.
pub fn check_axiom_decl_rest(
    st: &mut AState,
    fe: IFEnv,
    cv_a: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match propext_name(st) {
        Err(e) => Err(e),
        Ok(pn) => match choice_name(st) {
            Err(e) => Err(e),
            Ok(cn) => {
                if cv_a.name.eq2(&pn) || cv_a.name.eq2(&cn) {
                    fail(CheckError::NotImplemented(code_points(&M_STD_AXIOM_SHAPE)))
                } else {
                    match pin_sorry_ax(st) {
                        Err(e) => Err(e),
                        Ok(sa) => {
                            if cv_a.name.eq2(&sa) {
                                Ok(fe)
                            } else {
                                fail(CheckError::NotImplemented(code_points(
                                    &M_NONSTD_AXIOM,
                                )))
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:156-265 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — the `.indDecl`
/// arm.  **THE PINNED BASIS BLOCKS FIRST**: a stream's `Nat` block arrives as
/// an ordinary inductive block and is recognised HERE; a block under a pinned
/// name that does NOT match falls through to the ordinary route, where
/// `check_constant_val`'s reserved-name check REJECTS it.  Then the DECLARED
/// parameter count (con-leche's task #228: `indParamsOk` is official's own
/// check, one-sided, so a `false` is official's reject), and ONE ROUTE: the
/// uniform route takes every block the recogniser reads (`blockParts?`), at
/// any number of members, nested ones included; any other block declines once
/// its formers are checked as constants (`checkShapeless`).
pub fn check_ind_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    n_p: u64,
) -> Result<IFEnv, CheckError> {
    match basis_pin_hit(pers, st, block) {
        Err(e) => Err(e),
        Ok(Some(kind)) => check_basis_decl(pers, st, fe, &kind),
        Ok(None) => match checker_base::ind_params_ok(pers, st, n_p, block, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(CheckError::Invalid(code_points(&M_NUM_PARAMS))),
            Ok(true) => match block_parts::block_parts(pers, st, n_p, block) {
                Err(e) => Err(e),
                Ok(Some(p)) => block_tail::check_block(pers, st, mode, fe, block, &p),
                Ok(None) => check_shapeless(pers, st, mode, fe, block),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-214 checkDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:82-211 checkDecl` — **the
/// quotient package**: the export writes it as four records; each is compared
/// with the pinned block's constant at its own kind, and the FIRST that matches
/// installs the pinned block whole.
pub fn check_quot_decl(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    k: &QuotKind,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match quot_pin_hit(pers, st, k, cv) {
        Err(e) => Err(e),
        Ok(hit) => {
            if hit {
                match k {
                    QuotKind::Type => check_basis_decl(pers, st, fe, &BasisKind::QuotK),
                    _ => Ok(fe),
                }
            } else {
                match k {
                    QuotKind::Sound => fail(CheckError::NotImplemented(code_points(
                        &M_QUOT_SOUND_MISMATCH,
                    ))),
                    _ => fail(CheckError::NotImplemented(code_points(
                        &M_QUOT_DECL_MISMATCH,
                    ))),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The theorem's fold (`Checker.lean:194-208` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckDecl.lean:216-220 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:213-233 checkDeclStep` — **one
/// step of the pure fold, bracketed**: `check_decl` inside the per-declaration
/// scratch tier, with the constants it installed promoted before the tier
/// goes.
///
/// The bracket is `annot_step`'s, letter for letter — one `check_decl` where
/// phase A has an install half, and no `ValueGroup` because the pure fold
/// checks what it installs in the same step.  DESIGN.md §8.3's amendment (task
/// #97-P6-2) puts it here too, so that **the two folds stay one algorithm**:
/// the tier regime is not an optimisation of the driver's fold that the
/// theorem's fold may do without, it is where every term the checker builds
/// lives, and a Theorem-1 statement about a fold with no tiers would say
/// nothing about the fold the binary runs.
pub fn check_decl_step(
    _pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    d: &IDeclaration,
) -> Result<IFEnv, CheckError> {
    let vis: u64 = fe.visible_below;
    flush_caches(st);
    let mut tier: PersTier = enter_scratch(st);
    match check_decl(&tier, st, mode, pins, fe, d) {
        Err(e) => {
            drop_scratch(st, tier);
            Err(e)
        }
        Ok(fe2) => {
            let k: u64 = fe2.visible_below - vis;
            match promote_new(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, k, fe2) {
                Err(e) => {
                    drop_scratch(st, tier);
                    Err(e)
                }
                Ok((_, fe3)) => {
                    drop_scratch(st, tier);
                    Ok(fe3)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:216-220 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:235-244 checkDeclsPureGo` — the
/// cited `foldlM` as an index recursion threading the index by value (§3.4
/// forbids the closure).  The step is the bracketed one.
pub fn check_decls_pure_go(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    ds: &Vec<IDeclaration>,
    i: usize,
) -> Result<IFEnv, CheckError> {
    if i >= ds.len() {
        Ok(fe)
    } else {
        match check_decl_step(pers, st, mode, pins, fe, &ds[i]) {
            Err(e) => Err(e),
            Ok(fe2) => check_decls_pure_go(pers, st, mode, pins, fe2, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:216-220 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:246-250 checkDeclsPure` — the
/// fold from the empty environment.  THE THEOREM'S SHAPE (module note): one
/// step per record, install and check together, each step bracketed.
pub fn check_decls_pure(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
) -> Result<IFEnv, CheckError> {
    check_decls_pure_go(pers, st, mode, pins, mk_ifenv(i_env_empty()), ds, 0)
}

