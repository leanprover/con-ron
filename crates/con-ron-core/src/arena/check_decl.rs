//! `arena::check_decl` — the checker's fold step, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckDecl.lean`, which is con-leche's
//! `Kernel/CheckDecl.lean`: `checkShapeless`, `checkDecl` and
//! `checkDeclsPure` (moved out of `Kernel/Checker.lean` upstream, because the
//! uniform inductive route's stages sit above the checker's value stages).
//! The stages it dispatches to are `arena::decl_check`'s (values, the
//! certified `Nat` operations, the pinned axioms, the pinned blocks and the
//! quotient records) and `arena::inductives::block_tail`'s (the uniform
//! inductive route).
//!
//! ## The twin's deviations
//!
//! * **The one `match d with` is one dispatch and six arm functions**, so
//!   every arm stays a tail call (task #97-P4c's split rule), as it was when
//!   this code lived in `arena::checker`.
//! * **The executed tier's flushes are where `Cached/ParsedC.lean` and
//!   `Cached/CheckerC.lean` put them** (task #97g item 4): the arena has one
//!   environment representation and one core, the cached one.

use crate::arena::basis::basis_name_hit;
use crate::arena::checker_base;
use crate::arena::checker_base::{check_constant_val, nidx_contains_from};
use crate::arena::core::{nat_div_mod_names, nat_op_deps, nat_op_equations, nat_op_guard, nat_op_names};
use crate::arena::decl_check::{
    certify_nat_eqs, check_basis_block, check_defn_val, check_div_mod_pin, check_opaque_val,
    check_quot_record, check_reduce_pin, check_thm_val, defn_value, nat_op_stored_ok_all,
    of_reduce_ax_ok, std_axiom_ok, subst_const0_pairs, trust_compiler_ok,
};
use crate::arena::env::{
    i_constant_info_dup, i_constant_val_dup, ifenv_pop_temp, ifenv_push, ifenv_push_temp,
    IConstantInfo, IConstantVal, IDeclaration, IFEnv,
};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::inductives::{block_shape, block_tail};
use crate::arena::monad::{fail, read_name_m, AState};
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::pins::{pin_quot_sound, pin_sorry_ax};
use crate::arena::std_axioms::{choice_name, propext_name};
use crate::arena::store::PersTier;
use crate::arena::trust_axioms::{
    of_reduce_bool_name, of_reduce_nat_name, reduce_op_names, trust_compiler_name,
};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{CheckMode, QuotKind, ReducibilityHint};
use crate::kernel::trust_axioms as ctrust;
use crate::ron::hashmap::Eq2;

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
/// con-leche: ConLeche/Cached/ParsedC.lean:68-76 checkShapelessS
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:53-64 checkShapeless` — **an
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
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:53-64 checkShapeless` — the cited
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
                match check_constant_val(pers, st, mode, fe, cv, false) {
                    Err(e) => Err(e),
                    Ok(_) => check_shapeless_formers(pers, st, mode, fe, block, i + 1),
                }
            }
            _ => check_shapeless_formers(pers, st, mode, fe, block, i + 1),
        }
    }
}

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

// ---------------------------------------------------------------------------
// One declaration
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — **check a single
/// declaration, extending the environment on success**: every kind is checked
/// in its arm.  The twin's one `match d with` is one dispatch and six arm
/// functions here, so every arm stays a tail call (task #97-P4c's split rule).
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
        IDeclaration::IndDecl(block, n_p) => check_ind_decl(pers, st, mode, fe, block, *n_p),
        IDeclaration::QuotDecl(k, cv) => check_quot_record(pers, st, fe, k, cv),
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the `.defnDecl`
/// arm: the common constant check (a definition may take a certified
/// operation's name), the value check returning the record unpushed, then the
/// two pinned-`Nat` gates, then the push.
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
    match check_constant_val(pers, st, mode, &fe, cv, true) {
        Err(e) => Err(e),
        Ok(()) => match check_defn_val(pers, st, mode, &fe, cv, value, hint) {
            Err(e) => Err(e),
            Ok(ci) => check_defn_pins(pers, st, mode, pins, fe, ci, &cv.name),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the `.defnDecl`
/// arm's structural-`Nat` gate (`natOpNames.contains`), then the next.
pub fn check_defn_pins(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    ci: IConstantInfo,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match nat_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, n) {
                let mut fe1: IFEnv = fe;
                match check_structural_nat_pin(pers, st, mode, &mut fe1, &ci, n) {
                    Err(e) => Err(e),
                    Ok(()) => check_defn_div_mod_pin(pers, st, mode, pins, fe1, ci, n),
                }
            } else {
                check_defn_div_mod_pin(pers, st, mode, pins, fe, ci, n)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the
/// `natDivModNames.contains` gate of the `.defnDecl` arm, and the push last.
pub fn check_defn_div_mod_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    ci: IConstantInfo,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match nat_div_mod_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, n) {
                let mut fe1: IFEnv = fe;
                match check_div_mod_pin(pers, st, mode, pins, &mut fe1, &ci, n) {
                    Err(e) => Err(e),
                    Ok(()) => Ok(ifenv_push(fe1, ci)),
                }
            } else {
                Ok(ifenv_push(fe, ci))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the
/// structural-`Nat` gate: the environment guards and the stored value at `fe2`,
/// the environment with the definition, then `certifyNatEqs` at `fe`, the one
/// without it, over the equations with the operation's self-references
/// substituted.  Certifying with the definition stored would let the
/// operation's own fast path discharge its all-literal equations vacuously.
///
/// Deviation: the cited `fe2` is `fe.overlay [ci]`; the port pushes `ci` in
/// place for the reads at `fe2` and pops it before the certification
/// (`ifenv_push_temp`/`ifenv_pop_temp`, the port's overlay).
pub fn check_structural_nat_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &mut IFEnv,
    ci: &IConstantInfo,
    n: &NIdx,
) -> Result<(), CheckError> {
    let prev: Option<u64> = ifenv_push_temp(fe, i_constant_info_dup(ci));
    let at_fe2: Result<EIdx, CheckError> = check_structural_nat_pin_at_fe2(pers, st, fe, n);
    ifenv_pop_temp(fe, n, prev);
    match at_fe2 {
        Err(e) => Err(e),
        Ok(value2) => check_structural_nat_pin_eqs(pers, st, mode, fe, n, &value2),
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the reads at
/// `fe2`: `natOpGuard` and the dependencies' storage, then the stored value.
pub fn check_structural_nat_pin_at_fe2(
    pers: &PersTier,
    st: &mut AState,
    fe2: &IFEnv,
    n: &NIdx,
) -> Result<EIdx, CheckError> {
    match nat_op_guard(pers, st, fe2, n) {
        Err(e) => Err(e),
        Ok(g) => match nat_op_deps(st, n) {
            Err(e) => Err(e),
            Ok(deps) => match nat_op_stored_ok_all(pers, st, fe2, &deps, 0) {
                Err(e) => Err(e),
                Ok(d) => {
                    if !g || !d {
                        fail(CheckError::NotImplemented(code_points(&M_NONSTD_NAT_ENV)))
                    } else {
                        match defn_value(pers, fe2, n) {
                            None => fail(CheckError::Internal(code_points(&M_NAT_NOT_STORED))),
                            Some(value2) => Ok(value2),
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the equations,
/// substituted with the stored value, certified at `fe`.
pub fn check_structural_nat_pin_eqs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n: &NIdx,
    value2: &EIdx,
) -> Result<(), CheckError> {
    match nat_op_equations(pers, st, 0, n) {
        Err(e) => Err(e),
        Ok(eqs) => match subst_const0_pairs(pers, st, n, value2, &eqs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(seqs) => match certify_nat_eqs(pers, st, mode, fe, &seqs, 0) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(())
                    } else {
                        fail(CheckError::NotImplemented(code_points(&M_NONSTD_NAT)))
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the `.thmDecl`
/// arm: the common constant check, the value check (`checkThmValCI`), the push
/// of the statement.
pub fn check_thm_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match check_constant_val(pers, st, mode, &fe, cv, false) {
        Err(e) => Err(e),
        Ok(()) => match check_thm_val(pers, st, mode, &fe, cv, value) {
            Err(e) => Err(e),
            Ok(ci) => Ok(ifenv_push(fe, ci)),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the `.opaqueDecl`
/// arm: the opaque check returning the record unpushed, the compiler-trust gate
/// for `Lean.reduceNat`/`Lean.reduceBool`, the push last.
pub fn check_opaque_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match check_constant_val(pers, st, mode, &fe, cv, false) {
        Err(e) => Err(e),
        Ok(()) => match check_opaque_val(pers, st, mode, &fe, cv, value) {
            Err(e) => Err(e),
            Ok(ci) => check_opaque_reduce_pin(pers, st, mode, fe, ci, &cv.name, value),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the
/// `reduceOpNames.contains` gate of the `.opaqueDecl` arm, and the push.
pub fn check_opaque_reduce_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    ci: IConstantInfo,
    n: &NIdx,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match reduce_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, n) {
                let mut fe1: IFEnv = fe;
                match check_reduce_pin(pers, st, mode, &mut fe1, &ci, n, value) {
                    Err(e) => Err(e),
                    Ok(()) => Ok(ifenv_push(fe1, ci)),
                }
            } else {
                Ok(ifenv_push(fe, ci))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the `.axiomDecl`
/// arm.  **`Quot.sound` is the pinned quotient package's own record**: the
/// export writes it as an ordinary axiom record beside the four `#QUOT` ones.
/// The name is a reserved basis name: this record IS the package's, not a
/// redeclaration of it, so it is checked as a quotient record.
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
                check_quot_record(pers, st, fe, &QuotKind::Sound, cv)
            } else {
                check_axiom_decl_std(pers, st, mode, fe, cv)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the rest of
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
    match check_constant_val(pers, st, mode, &fe, cv, false) {
        Err(e) => Err(e),
        Ok(()) => match std_axiom_ok(pers, st, &fe, cv) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    Ok(ifenv_push(
                        fe,
                        IConstantInfo::AxiomInfo(i_constant_val_dup(cv)),
                    ))
                } else {
                    check_axiom_decl_trust(pers, st, fe, i_constant_val_dup(cv))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the
/// `Lean.trustCompiler` branch: `True` is trivially realizable, so the axiom is
/// installed exactly like a checked `opaque` with witness `True.intro` over the
/// pinned `True` family.
pub fn check_axiom_decl_trust(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match trust_compiler_name(st) {
        Err(e) => Err(e),
        Ok(tn) => {
            if cv.name.eq2(&tn) {
                match trust_compiler_ok(pers, st, &fe, &cv) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        if ok {
                            Ok(ifenv_push(
                                fe,
                                IConstantInfo::AxiomInfo(cv),
                            ))
                        } else {
                            fail(CheckError::NotImplemented(code_points(
                                &M_TRUSTCOMPILER_SHAPE,
                            )))
                        }
                    }
                }
            } else {
                check_axiom_decl_of_reduce(pers, st, fe, cv)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the pinned
/// `ofReduce*` axioms: over the pinned `Eq` basis, the element inductive and
/// the identity-certified reduce opaque, `∀ a b, reduce a = b → a = b`
/// interprets to an inhabited proposition.
pub fn check_axiom_decl_of_reduce(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match of_reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(on) => match of_reduce_bool_name(st) {
            Err(e) => Err(e),
            Ok(ob) => {
                if cv.name.eq2(&on) || cv.name.eq2(&ob) {
                    match of_reduce_ax_ok(pers, st, &fe, &cv) {
                        Err(e) => Err(e),
                        Ok(ok) => {
                            if ok {
                                Ok(ifenv_push(
                                    fe,
                                    IConstantInfo::AxiomInfo(cv),
                                ))
                            } else {
                                fail(CheckError::NotImplemented(code_points(
                                    &M_TRUST_AXIOM_ENV,
                                )))
                            }
                        }
                    }
                } else {
                    check_axiom_decl_rest(pers, st, fe, cv)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:175-247 checkDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the last
/// three tests: a pinned standard-axiom NAME whose shape did not match
/// declines under its own message, `sorryAx` is tolerated as a DECLARATION and
/// installs nothing (a USE of it declines at the record that uses it), and
/// every other axiom is a positive decline, its message naming the axiom and
/// the tactic that apparently added it (`kernel::trust_axioms::
/// non_std_axiom_msg`, over the name read back from the store).
pub fn check_axiom_decl_rest(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match propext_name(st) {
        Err(e) => Err(e),
        Ok(pn) => match choice_name(st) {
            Err(e) => Err(e),
            Ok(cn) => {
                if cv.name.eq2(&pn) || cv.name.eq2(&cn) {
                    fail(CheckError::NotImplemented(code_points(&M_STD_AXIOM_SHAPE)))
                } else {
                    match pin_sorry_ax(st) {
                        Err(e) => Err(e),
                        Ok(sa) => {
                            if cv.name.eq2(&sa) {
                                Ok(fe)
                            } else {
                                match read_name_m(pers, st, &cv.name) {
                                    Err(e) => Err(e),
                                    Ok(n) => fail(CheckError::NotImplemented(
                                        ctrust::non_std_axiom_msg(&n),
                                    )),
                                }
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:40-185 checkDecl
/// con-leche: ConLeche/Cached/ParsedC.lean:154-173 checkIndDeclC
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:102-184 checkDecl` — the `.indDecl`
/// arm.  **THE PINNED BASIS BLOCKS FIRST**: a stream's `Nat` block arrives as
/// an ordinary inductive block; its members' names say it is the pinned block's
/// record, and its check compares it with the pin (`check_basis_block`).  Then
/// the DECLARED parameter count (con-leche's task #228: `indParamsOk` is
/// official's own check, one-sided, so a `false` is official's reject), and ONE
/// ROUTE: the uniform route takes every block the recogniser reads
/// (`blockShape?`), at any number of members, nested ones included; any other
/// block declines once its formers are checked as constants
/// (`checkShapeless`).
pub fn check_ind_decl(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    n_p: u64,
) -> Result<IFEnv, CheckError> {
    match basis_name_hit(pers, st, block) {
        Err(e) => Err(e),
        Ok(Some(kind)) => check_basis_block(pers, st, fe, &kind, block),
        Ok(None) => match checker_base::ind_params_ok(pers, st, n_p, block, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(CheckError::Invalid(code_points(&M_NUM_PARAMS))),
            Ok(true) => match block_shape::block_shape(pers, st, n_p, block) {
                Err(e) => Err(e),
                Ok(Some(p)) => block_tail::check_block(pers, st, mode, fe, block, &p),
                Ok(None) => check_shapeless(pers, st, mode, fe, block),
            },
        },
    }
}
