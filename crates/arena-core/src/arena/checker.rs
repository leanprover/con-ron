//! `arena::checker` — the declaration fold, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Checker.lean`, which is con-leche's
//! `Kernel/Checker.lean`'s `checkDecl`/`checkDeclsPure` and
//! `Cached/Installed.lean`'s two-phase `checkDecls`.
//!
//! ## Two folds, and which is which
//!
//! * **`check_decls_pure`** is the THEOREM's shape —
//!   `ConLeche/Model/Fold.lean`'s `checkDeclsPure_sound_of` consumes it, and
//!   DESIGN.md §8.2's Theorem 1 folds `checkDecl` over the stream.  One step
//!   per record, install and check together.
//! * **`install_then_check`** is what the BINARY runs: phase A installs every
//!   record, annotating its header and its value but not inferring; phase B
//!   checks each recorded declaration against the PREFIX VIEW it was installed
//!   at.  con-leche proves the two are the same accept
//!   (`fullyChecked_checkDecls`); the arena's two call the same `checkDecl`
//!   pieces, which is what keeps them the same computation.
//!
//! ## The per-declaration bracket lives in phase B
//!
//! DESIGN.md §8.3: "Persistent = parse + installed environment; scratch = one
//! declaration's check."  Phase A's business is exactly the terms the
//! environment KEEPS, so it runs outside the bracket; phase B's business is
//! exactly what a declaration merely COMPUTES, so `check_pending` is
//! `enter_scratch` … `drop_scratch` around `check_value_group` and every node
//! it appends goes with the tier.  Two things are deliberately NOT bracketed:
//! phase A's fallback (`annot_step_other`, the whole `check_decl` for the kinds
//! whose check is not separable from their install — they install what they
//! check), and `check_decls_pure`, which is the theorem's shape.
//!
//! ## The pins are interned at startup
//!
//! `intern_all_pins` is DESIGN.md §8.6 P2d's one-time tree walk, and it is what
//! makes every later `pin`/`intern_ci` of the same datum return the PERSISTENT
//! handle whatever tier is live (§8.3: `intern` probes the persistent table
//! first).  Without it a reserved name first interned inside a scratch tier
//! would compare unequal to the stream's own persistent copy of it, which is
//! the one way hash-consing can go wrong across the tier boundary.

use crate::arena::basis::{basis_kind_decls, basis_kind_decls_a, basis_pin_hit, quot_pin_hit};
use crate::arena::canon::i_constant_info_canon_eq;
use crate::arena::checker_base::{check_constant_val, nidx_contains_from};
use crate::arena::checker_split::{
    check_value_group, install_constant_val, install_value, ValueGroup, ValueKind,
};
use crate::arena::core::{
    drop_scratch, enter_scratch, nat_div_mod_names, nat_op_deps, nat_op_equations,
    nat_op_guard, nat_op_names, pin,
};
use crate::arena::decl_check::{
    certify_nat_eqs, check_defn_val, check_div_mod_pin, check_opaque_val, check_reduce_pin,
    check_thm_val, defn_value, install_basis_decls, nat_op_stored_ok_all, of_reduce_ax_ok,
    std_axiom_ok, subst_const0_pairs, trust_compiler_ok,
};
use crate::arena::env::{
    i_constant_info_dup, i_constant_infos_dup, i_constant_val_dup, i_env_empty,
    ifenv_restrict_to, mk_ifenv, IConstantInfo, IConstantVal, IDeclaration, IFEnv,
};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::monad::{fail, AState};
use crate::arena::nat_op_pin_set::{intern_pin_sets, INatOpPinSet};
use crate::arena::std_axioms::{choice_name, propext_name};
use crate::arena::trust_axioms::{
    of_reduce_bool_name, of_reduce_nat_name, reduce_op_names, trust_compiler_name,
};
use con_ron_core::kernel::basis_names;
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env as cenv;
use con_ron_core::kernel::env::{BasisKind, CheckMode, QuotKind, ReducibilityHint};
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quotient basis requires the pinned Eq basis"`, as code points.
pub const M_QUOT_BASIS_EQ: [u32; 43] = [
    113, 117, 111, 116, 105, 101, 110, 116, 32, 98, 97, 115, 105, 115, 32, 114, 101, 113,
    117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 112, 105, 110, 110, 101, 100, 32, 69,
    113, 32, 98, 97, 115, 105, 115
];

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

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `" (declaration "`, as code points.
pub const M_AT_DECL_OPEN: [u32; 14] = [
    32, 40, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `")"`, as code points.
pub const M_AT_DECL_CLOSE: [u32; 1] = [41];

// ---------------------------------------------------------------------------
// The pinned basis install (`Checker.lean:65-78` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:427-437 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:73-78 checkBasisDecl` —
/// **install the pinned (pre-annotated) basis block.**  The three records that
/// install one — the fold's own `basisDecl` kind, a stream block
/// `basis_pin_hit` recognises and a quotient record `quot_pin_hit` recognises
/// — share this body.  The quotient block's types mention the pinned equality
/// former, which is why it requires the `Eq` basis first.
pub fn check_basis_decl(
    st: &mut AState,
    fe: IFEnv,
    kind: &BasisKind,
) -> Result<IFEnv, CheckError> {
    match kind {
        BasisKind::QuotK => match crate::arena::decl_check::eq_basis_pinned(st, &fe) {
            Err(e) => Err(e),
            Ok(b) => {
                if !b {
                    fail(CheckError::NotImplemented(code_points(&M_QUOT_BASIS_EQ)))
                } else {
                    check_basis_decl_install(st, fe, kind)
                }
            }
        },
        _ => check_basis_decl_install(st, fe, kind),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:427-437 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:73-78 checkBasisDecl` — the
/// cited `installBasisDecls fe (← BasisKind.declsA kind)`, past the quotient
/// gate.  Split off so the gate's two branches are tail calls.
pub fn check_basis_decl_install(
    st: &mut AState,
    fe: IFEnv,
    kind: &BasisKind,
) -> Result<IFEnv, CheckError> {
    match basis_kind_decls_a(st, kind) {
        Err(e) => Err(e),
        Ok(decls) => install_basis_decls(fe, &decls, 0),
    }
}

// ---------------------------------------------------------------------------
// One declaration (`Checker.lean:80-192` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — **check a
/// single declaration, extending the environment on success.**  The twin's one
/// `match d with` is one dispatch and seven arm functions here, so every arm
/// stays a tail call (task #97-P4c's split rule).
pub fn check_decl(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    d: &IDeclaration,
) -> Result<IFEnv, CheckError> {
    match d {
        IDeclaration::DefnDecl(cv, value, hint) => {
            check_defn_decl(st, mode, pins, fe, cv, value, hint)
        }
        IDeclaration::ThmDecl(cv, value) => check_thm_decl(st, mode, fe, cv, value),
        IDeclaration::OpaqueDecl(cv, value) => check_opaque_decl(st, mode, fe, cv, value),
        IDeclaration::AxiomDecl(cv) => check_axiom_decl(st, mode, fe, cv),
        IDeclaration::BasisDecl(kind) => check_basis_decl(st, fe, kind),
        IDeclaration::IndDecl(block, n_p) => check_ind_decl(st, mode, fe, block, *n_p),
        IDeclaration::QuotDecl(k, cv) => check_quot_decl(st, fe, k, cv),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.defnDecl` arm: the common constant check, the value check, then the two
/// pinned-`Nat` gates.
///
/// Deviation: the twin holds `fe` (pre-insertion) and `fe2` (extended) at once;
/// `IFEnv` has no cheap copy, so the port keeps ONE index and remembers the
/// pre-insertion visibility bound `k_pre` —
/// `con_ron_core::kernel::checker::check_defn_decl`'s own arrangement.
pub fn check_defn_decl(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<IFEnv, CheckError> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match check_defn_val(st, mode, fe, &cv_a, value, hint) {
            Err(e) => Err(e),
            Ok(fe2) => check_defn_pins(st, mode, pins, fe2, k_pre, &cv_a.name),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.defnDecl` arm's two pinned-`Nat` gates, in the twin's order.
pub fn check_defn_pins(
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
                match check_structural_nat_pin(st, mode, fe2, k_pre, n) {
                    Err(e) => Err(e),
                    Ok(fe3) => check_defn_div_mod_pin(st, mode, pins, fe3, k_pre, n),
                }
            } else {
                check_defn_div_mod_pin(st, mode, pins, fe2, k_pre, n)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `natDivModNames.contains` gate of the `.defnDecl` arm.
pub fn check_defn_div_mod_pin(
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
                check_div_mod_pin(st, mode, pins, fe2, k_pre, n)
            } else {
                Ok(fe2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// structural-`Nat` gate: the environment guards at the EXTENDED environment,
/// then `certifyNatEqs` at the PRE-insertion one over the equations with the
/// operation's self-references substituted.  Certifying after insertion would
/// let the operation's own fast path discharge its all-literal equations
/// vacuously.
pub fn check_structural_nat_pin(
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match nat_op_guard(st, &fe2, n) {
        Err(e) => Err(e),
        Ok(g) => match nat_op_deps(st, n) {
            Err(e) => Err(e),
            Ok(deps) => match nat_op_stored_ok_all(st, &fe2, &deps, 0) {
                Err(e) => Err(e),
                Ok(d) => {
                    if !g || !d {
                        fail(CheckError::NotImplemented(code_points(&M_NONSTD_NAT_ENV)))
                    } else {
                        check_structural_nat_pin_eqs(st, mode, fe2, k_pre, n)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the stored
/// value, the equations, and their certification at the pre-insertion view.
pub fn check_structural_nat_pin_eqs(
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    n: &NIdx,
) -> Result<IFEnv, CheckError> {
    match defn_value(&fe2, n) {
        None => fail(CheckError::Internal(code_points(&M_NAT_NOT_STORED))),
        Some(value2) => match nat_op_equations(st, 0, n) {
            Err(e) => Err(e),
            Ok(eqs) => match subst_const0_pairs(st, n, &value2, &eqs, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(seqs) => check_structural_nat_pin_certify(st, mode, fe2, k_pre, &seqs),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// certification itself, with the index restricted to the pre-insertion bound
/// and handed back at the bound it came in at (the arm's standing deviation).
pub fn check_structural_nat_pin_certify(
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    seqs: &Vec<(EIdx, EIdx)>,
) -> Result<IFEnv, CheckError> {
    let k2: u64 = fe2.visible_below;
    let fe_pre: IFEnv = ifenv_restrict_to(fe2, k_pre);
    let r: Result<bool, CheckError> = certify_nat_eqs(st, mode, &fe_pre, seqs, 0);
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.thmDecl` arm.
pub fn check_thm_decl(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match check_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => check_thm_val(st, mode, fe, &cv_a, value),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.opaqueDecl` arm: the opaque check, then the compiler-trust gate for
/// `Lean.reduceNat`/`Lean.reduceBool`.
pub fn check_opaque_decl(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match check_opaque_val(st, mode, fe, &cv_a, value) {
            Err(e) => Err(e),
            Ok(fe2) => check_opaque_reduce_pin(st, mode, fe2, k_pre, &cv_a.name, value),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `reduceOpNames.contains` gate of the `.opaqueDecl` arm.
pub fn check_opaque_reduce_pin(
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
                check_reduce_pin(st, mode, fe2, k_pre, n, value)
            } else {
                Ok(fe2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.axiomDecl` arm.  **`Quot.sound` is the pinned quotient BLOCK's own
/// record**: the export writes it as an ordinary axiom record beside the four
/// `#QUOT` ones, so it arrives here — compared with the pin and installing
/// NOTHING of its own, and DECLINING when it does not match.  The comparison
/// precedes the common checks because the name is a reserved basis name: this
/// record IS the pinned block's, not a redeclaration of it.
pub fn check_axiom_decl(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match pin(st, &basis_names::quot_sound_name()) {
        Err(e) => Err(e),
        Ok(qs) => {
            if cv.name.eq2(&qs) {
                check_quot_sound_record(st, fe, cv)
            } else {
                check_axiom_decl_std(st, mode, fe, cv)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.axiomDecl` arm's `Quot.sound` test, against slot 4 of the pinned quotient
/// block.  The twin's `blk[4]?` is the bound test; the block has exactly five
/// members, so the `none` arm is unreachable and declines, as the twin's does.
pub fn check_quot_sound_record(
    st: &mut AState,
    fe: IFEnv,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match basis_kind_decls(st, &BasisKind::QuotK) {
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
                match i_constant_info_canon_eq(st, &mine, &pinned) {
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the rest of
/// the `.axiomDecl` arm: the two standard axioms and the `Init` compiler-trust
/// family are INSTALLED, `sorryAx` is tolerated and installs nothing, and
/// anything else — including a pinned NAME with a non-pinned shape — is a
/// positive decline at its own record.
pub fn check_axiom_decl_std(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match check_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match std_axiom_ok(st, &fe, &cv_a) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    Ok(crate::arena::env::ifenv_push(
                        fe,
                        IConstantInfo::AxiomInfo(cv_a),
                    ))
                } else {
                    check_axiom_decl_trust(st, fe, cv_a)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `Lean.trustCompiler` branch: `True` is trivially realizable, so the axiom is
/// installed exactly like a checked `opaque` with witness `True.intro` over the
/// pinned `True` family.
pub fn check_axiom_decl_trust(
    st: &mut AState,
    fe: IFEnv,
    cv_a: IConstantVal,
) -> Result<IFEnv, CheckError> {
    match trust_compiler_name(st) {
        Err(e) => Err(e),
        Ok(tn) => {
            if cv_a.name.eq2(&tn) {
                match trust_compiler_ok(st, &fe, &cv_a) {
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
                check_axiom_decl_of_reduce(st, fe, cv_a)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the pinned
/// `ofReduce*` axioms: over the pinned `Eq` basis, the element inductive and
/// the identity-certified reduce opaque, `∀ a b, reduce a = b → a = b`
/// interprets to an inhabited proposition.
pub fn check_axiom_decl_of_reduce(
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
                    match of_reduce_ax_ok(st, &fe, &cv_a) {
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the last
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
                    match pin(st, &basis_names::sorry_ax_name()) {
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — the
/// `.indDecl` arm.  **THE PINNED BASIS BLOCKS FIRST**: a stream's `Nat` block
/// arrives as an ordinary inductive block and is recognised HERE; a block under
/// a pinned name that does NOT match falls through to the ordinary route, where
/// `check_constant_val`'s reserved-name check REJECTS it.  The route itself is
/// `arena::inductives`' seam (task #97-P4d part 2).
pub fn check_ind_decl(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    n_p: u64,
) -> Result<IFEnv, CheckError> {
    match basis_pin_hit(st, block) {
        Err(e) => Err(e),
        Ok(Some(kind)) => check_basis_decl(st, fe, &kind),
        Ok(None) => crate::arena::inductives::check_ind_decl(
            cenv::check_mode_dup(mode),
            fe,
            i_constant_infos_dup(block),
            n_p,
            st,
        ),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:86-192 checkDecl` — **the
/// quotient package**: the export writes it as four records; each is compared
/// with the pinned block's constant at its own kind, and the FIRST that matches
/// installs the pinned block whole.
pub fn check_quot_decl(
    st: &mut AState,
    fe: IFEnv,
    k: &QuotKind,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match quot_pin_hit(st, k, cv) {
        Err(e) => Err(e),
        Ok(hit) => {
            if hit {
                match k {
                    QuotKind::Type => check_basis_decl(st, fe, &BasisKind::QuotK),
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

/// con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/Checker.lean:199-202 checkDeclsPureGo` — the
/// cited `foldlM` as an index recursion threading the index by value (§3.4
/// forbids the closure).
pub fn check_decls_pure_go(
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
        match check_decl(st, mode, pins, fe, &ds[i]) {
            Err(e) => Err(e),
            Ok(fe2) => check_decls_pure_go(st, mode, pins, fe2, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/Checker.lean:206-208 checkDeclsPure` — the
/// fold from the empty environment.  THE THEOREM'S SHAPE (module note): one
/// step per record, no bracket.
pub fn check_decls_pure(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
) -> Result<IFEnv, CheckError> {
    check_decls_pure_go(st, mode, pins, mk_ifenv(i_env_empty()), ds, 0)
}

// ---------------------------------------------------------------------------
// The two-phase fold the binary runs (`Checker.lean:210-341` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Installed.lean:83-91 PendingCheck
/// Lean twin: `proof/ConRon/Arena/Checker.lean:216-220 PendingCheck` — a
/// phase-A record awaiting its phase-B check: the datum that crosses the
/// install/check seam, the fold position of the declaration (its error tag) and
/// the environment counter at the install.
pub struct PendingCheck {
    pub vg: ValueGroup,
    pub pos: u64,
    pub vis: u64,
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — phase A's
/// step body: annotate-and-install for the three value kinds, the ordinary step
/// `check_decl` for everything else.  `i` is the fold position the record is
/// tagged with.  The four arms are four functions, so every one of them is a
/// tail call.
pub fn annot_step(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    pd: &IDeclaration,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match pd {
        IDeclaration::DefnDecl(cv, value, hint) => {
            annot_step_defn(st, mode, pins, i, fe, pend, pd, cv, value, hint)
        }
        IDeclaration::ThmDecl(cv, value) => annot_step_thm(st, mode, i, fe, pend, cv, value),
        IDeclaration::OpaqueDecl(cv, value) => {
            annot_step_opaque(st, mode, pins, i, fe, pend, pd, cv, value)
        }
        _ => annot_step_other(st, mode, pins, fe, pend, pd),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — the
/// `.defnDecl` arm: a pin-certified operation takes the ordinary step (its
/// check is not separable from its install), everything else is annotated,
/// installed and recorded as pending.
#[allow(clippy::too_many_arguments)]
pub fn annot_step_defn(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    pd: &IDeclaration,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match nat_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => match nat_div_mod_names(st) {
            Err(e) => Err(e),
            Ok(ds) => {
                if nidx_contains_from(&ns, 0, &cv.name) || nidx_contains_from(&ds, 0, &cv.name)
                {
                    annot_step_other(st, mode, pins, fe, pend, pd)
                } else {
                    annot_step_defn_install(st, mode, i, fe, pend, cv, value, hint)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — the
/// `.defnDecl` arm's install and push.  **The counter is read BEFORE the
/// push**, as the twin's note insists: read after it, the push copies the whole
/// index at every install.
#[allow(clippy::too_many_arguments)]
pub fn annot_step_defn_install(
    st: &mut AState,
    mode: &CheckMode,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match install_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match install_value(st, mode, &fe, &cv_a, value) {
            Err(e) => Err(e),
            Ok(jv) => {
                let vis: u64 = fe.visible_below;
                let fe2: IFEnv = crate::arena::env::ifenv_push(
                    fe,
                    IConstantInfo::DefnInfo(
                        i_constant_val_dup(&cv_a),
                        jv.dup2(),
                        cenv::reducibility_hint_dup(hint),
                    ),
                );
                let mut pend2 = pend;
                pend2.push(PendingCheck {
                    vg: ValueGroup { kind: ValueKind::Defn, cv_a, jv },
                    pos: i,
                    vis,
                });
                Ok((fe2, pend2))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — the
/// `.thmDecl` arm: **a theorem installs BY STATEMENT**.  The header's install
/// half only; the value is recorded raw and never touched here (phase B
/// annotates it), so phase A never enters a theorem's body.
pub fn annot_step_thm(
    st: &mut AState,
    mode: &CheckMode,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match install_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => {
            let vis: u64 = fe.visible_below;
            let fe2: IFEnv = crate::arena::env::ifenv_push(
                fe,
                IConstantInfo::ThmInfo(i_constant_val_dup(&cv_a), value.dup2()),
            );
            let mut pend2 = pend;
            pend2.push(PendingCheck {
                vg: ValueGroup { kind: ValueKind::Thm, cv_a, jv: value.dup2() },
                pos: i,
                vis,
            });
            Ok((fe2, pend2))
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — the
/// `.opaqueDecl` arm: a `reduce*` witness takes the ordinary step (its identity
/// certificate is part of its install), everything else is annotated, installed
/// **as an axiom** — an opaque's value being a discarded witness — and recorded
/// as pending.
#[allow(clippy::too_many_arguments)]
pub fn annot_step_opaque(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    pd: &IDeclaration,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match reduce_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, &cv.name) {
                annot_step_other(st, mode, pins, fe, pend, pd)
            } else {
                annot_step_opaque_install(st, mode, i, fe, pend, cv, value)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — the opaque
/// arm's install and push, the counter read before it.
pub fn annot_step_opaque_install(
    st: &mut AState,
    mode: &CheckMode,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match install_constant_val(st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match install_value(st, mode, &fe, &cv_a, value) {
            Err(e) => Err(e),
            Ok(jv) => {
                let vis: u64 = fe.visible_below;
                let fe2: IFEnv = crate::arena::env::ifenv_push(
                    fe,
                    IConstantInfo::AxiomInfo(i_constant_val_dup(&cv_a)),
                );
                let mut pend2 = pend;
                pend2.push(PendingCheck {
                    vg: ValueGroup { kind: ValueKind::Opaque, cv_a, jv },
                    pos: i,
                    vis,
                });
                Ok((fe2, pend2))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:230-258 annotStep` — the
/// catch-all arm, shared by the three gated branches above: the ordinary step,
/// which leaves the records untouched.
pub fn annot_step_other(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    pd: &IDeclaration,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match check_decl(st, mode, pins, fe, pd) {
        Err(e) => Err(e),
        Ok(fe2) => Ok((fe2, pend)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:185-195 annotDeclStep
/// Lean twin: `proof/ConRon/Arena/Checker.lean:269-274 annotDeclStep` — phase
/// A's step with the position carried and the error tagged: a failing step
/// reports the `CheckError` together with `i`, the fold position of the
/// declaration that failed.
///
/// Deviation: the twin restores the PRE-step state on a failure (it is written
/// as a state function); a failure aborts the whole fold here, so nothing reads
/// the state afterwards and no snapshot is taken —
/// `con_ron_core::cached::installed::annot_decl_step`'s arrangement.
pub fn annot_decl_step(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>),
    pd: &IDeclaration,
) -> Result<(u64, IFEnv, Vec<PendingCheck>), (CheckError, u64)> {
    let i: u64 = p.0;
    match annot_step(st, mode, pins, i, p.1, p.2, pd) {
        Err(e) => Err((e, i)),
        Ok(q) => Ok((i + 1, q.0, q.1)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-287 annotFold` — phase A as
/// a fold over the records, as an index recursion threading the accumulator by
/// value.
pub fn annot_fold(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>),
    ds: &Vec<IDeclaration>,
    i: usize,
) -> Result<(u64, IFEnv, Vec<PendingCheck>), (CheckError, u64)> {
    if i >= ds.len() {
        Ok(p)
    } else {
        match annot_decl_step(st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => annot_fold(st, mode, pins, q, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending
/// Lean twin: `proof/ConRon/Arena/Checker.lean:299-303 checkPending` —
/// **phase B's check of one record**, against the prefix view
/// `fe.restrictTo pc.vis`.
///
/// **This is (C)'s per-declaration bracket** (DESIGN.md §8.3): the scratch tier
/// is turned on, `check_value_group` runs the inference and the conversion, and
/// the tier — with every node they appended and every cache row naming one — is
/// dropped.  Deviation: the twin's `throw` skips its `dropScratch` and the
/// caller restores the pre-record state instead; the port drops the tier on
/// BOTH paths, which lands in the same place (scratch off, persistent
/// untouched) without a snapshot.  The index comes in at the installed bound
/// and goes back out there, the twin's `restrictTo` happening in between.
pub fn check_pending(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    pc: &PendingCheck,
) -> Result<IFEnv, CheckError> {
    enter_scratch(st);
    let k: u64 = fe.visible_below;
    let fe_v: IFEnv = ifenv_restrict_to(fe, pc.vis);
    let r: Result<(), CheckError> = check_value_group(st, mode, &fe_v, &pc.vg);
    drop_scratch(st);
    match r {
        Err(e) => Err(e),
        Ok(()) => Ok(ifenv_restrict_to(fe_v, k)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList
/// Lean twin: `proof/ConRon/Arena/Checker.lean:308-314 checkPendingList` —
/// phase B as a pure walk: every record checked at its own prefix view, a
/// failure tagged with the record's fold position.
pub fn check_pending_list(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    pend: &Vec<PendingCheck>,
    i: usize,
) -> Result<IFEnv, (CheckError, u64)> {
    if i >= pend.len() {
        Ok(fe)
    } else {
        match check_pending(st, mode, fe, &pend[i]) {
            Err(e) => Err((e, pend[i].pos)),
            Ok(fe2) => check_pending_list(st, mode, fe2, pend, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:320-327 installThenCheck` —
/// **the declaration fold the binary runs**: install every record (phase A),
/// check every recorded declaration (phase B), return the environment.  The
/// `× Nat` of the error is the failure's POSITION in the fold.
///
/// Deviation: the twin's result is `AM (Except (CheckError × Nat) IFEnv)` — an
/// outer failure the two phases never produce, because `annotDeclStep` and
/// `checkPendingList` tag every error into the inner `Except`.  The port has
/// the one `Result` with the tagged error, which is
/// `con_ron_core::cached::installed::check_decls`' shape.
pub fn install_then_check(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
) -> Result<IFEnv, (CheckError, u64)> {
    match annot_fold(
        st,
        mode,
        pins,
        (0, mk_ifenv(i_env_empty()), Vec::new()),
        ds,
        0,
    ) {
        Err(e) => Err(e),
        Ok(p) => check_pending_list(st, mode, p.1, &p.2, 0),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:337-341 atDecl` — the fold's
/// failure, with its POSITION rendered into the message.  It sits beside
/// `frontend`'s `at_line`, which does the same for the PARSE's position and
/// must not be confused with it: a line number and a fold position are
/// different numbers.
pub fn at_decl(e: CheckError, n: u64) -> CheckError {
    match e {
        CheckError::NotImplemented(w) => CheckError::NotImplemented(at_decl_text(w, n)),
        CheckError::Invalid(w) => CheckError::Invalid(at_decl_text(w, n)),
        CheckError::Internal(w) => CheckError::Internal(at_decl_text(w, n)),
        CheckError::Native(w) => CheckError::Native(at_decl_text(w, n)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:337-341 atDecl` — the twin's
/// `s!"{w} (declaration {n})"`, as code points; `toString n` is
/// `con_ron_core::kernel::core_k::nat_to_dec`, the port's own decimal
/// recursion.
pub fn at_decl_text(w: Vec<u32>, n: u64) -> Vec<u32> {
    let out = cp_append(w, &code_points(&M_AT_DECL_OPEN), 0);
    let out = cp_append(out, &core_k::nat_to_dec(n), 0);
    cp_append(out, &code_points(&M_AT_DECL_CLOSE), 0)
}

/// con-leche: none — `String.append`; the port stores a message as `Vec<u32>` (DESIGN.md §3.3)
/// The cursor push behind `at_decl_text`: `Vec::append` is not in the Aeneas
/// subset (it would be a new external), so the code points are pushed one at a
/// time, which is what every other accumulator of the port does.
pub fn cp_append(out: Vec<u32>, s: &Vec<u32>, i: usize) -> Vec<u32> {
    if i >= s.len() {
        out
    } else {
        let mut out2 = out;
        out2.push(s[i]);
        cp_append(out2, s, i + 1)
    }
}

// ---------------------------------------------------------------------------
// The startup walk (`Checker.lean:343-373` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — **the
/// one-time tree walk of DESIGN.md §8.6 P2d**: every datum the checker compares
/// a stream record against, interned into the tier that is live at the call —
/// which, at the driver's call, is the persistent one.
///
/// The six basis blocks in both forms (the RAW ones `basis_pin_hit` and
/// `quot_pin_hit` compare against, the ANNOTATED ones `check_basis_decl`
/// installs), the standard and compiler-trust axiom pins, the reserved names
/// the guards compare by handle, and the `Nat`-operation pin variants, whose
/// interned form is the checker's pin-list parameter (con-leche's task #304).
pub fn intern_all_pins(
    st: &mut AState,
    pins: &Vec<NatOpPinSet>,
) -> Result<Vec<INatOpPinSet>, CheckError> {
    match intern_all_basis(st, 0) {
        Err(e) => Err(e),
        Ok(()) => match intern_all_axiom_pins(st) {
            Err(e) => Err(e),
            Ok(()) => match intern_all_names(st) {
                Err(e) => Err(e),
                Ok(()) => intern_pin_sets(st, pins, 0, Vec::new()),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the six
/// basis blocks in both forms, as a cursor over
/// `con_ron_core::kernel::basis_raw::block_pin_kinds` plus `quotK` (the twin
/// spells the twelve calls out).
pub fn intern_all_basis(st: &mut AState, i: usize) -> Result<(), CheckError> {
    let ks: Vec<BasisKind> = all_basis_kinds();
    if i >= ks.len() {
        Ok(())
    } else {
        match basis_kind_decls(st, &ks[i]) {
            Err(e) => Err(e),
            Ok(_) => match basis_kind_decls_a(st, &ks[i]) {
                Err(e) => Err(e),
                Ok(_) => intern_all_basis(st, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the six
/// kinds the startup walk interns, in the twin's order.
pub fn all_basis_kinds() -> Vec<BasisKind> {
    let mut ks: Vec<BasisKind> = Vec::with_capacity(6);
    ks.push(BasisKind::EqK);
    ks.push(BasisKind::NatK);
    ks.push(BasisKind::PunitK);
    ks.push(BasisKind::EmptyK);
    ks.push(BasisKind::FalseK);
    ks.push(BasisKind::QuotK);
    ks
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the
/// standard and compiler-trust axiom pins, in the twin's order.  The twin's
/// `iffA`/`propextA` family is this port's raw one (`arena::std_axioms`'
/// module note).
pub fn intern_all_axiom_pins(st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::iff_raw(st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::iff_intro_raw(st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::iff_rec_raw(st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::nonempty_raw(st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_axiom_pins_rest(st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the
/// rest of the axiom pins and the two reduce pins.
pub fn intern_all_axiom_pins_rest(st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::nonempty_intro_raw(st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::nonempty_rec_raw(st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::propext_raw(st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::choice_raw(st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_trust_pins(st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the
/// compiler-trust shapes and the two reduce pins.
pub fn intern_all_trust_pins(st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::trust_axioms::true_cv_a(st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::trust_axioms::true_intro_cv_a(st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::trust_axioms::trust_compiler_a(st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::trust_axioms::bool_cv_a(st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_reduce_pins(st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the
/// four `reduce*`/`ofReduce*` shapes and the two pinned defining expressions.
pub fn intern_all_reduce_pins(st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::trust_axioms::reduce_nat_cv_a(st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::trust_axioms::reduce_bool_cv_a(st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::trust_axioms::of_reduce_nat_a(st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::trust_axioms::of_reduce_bool_a(st) {
                    Err(e) => Err(e),
                    Ok(_) => match crate::arena::trust_axioms::reduce_nat_decl_pin(st) {
                        Err(e) => Err(e),
                        Ok(_) => match crate::arena::trust_axioms::reduce_bool_decl_pin(st)
                        {
                            Err(e) => Err(e),
                            Ok(_) => Ok(()),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:356-373 internAllPins` — the
/// reserved names the guards compare by handle.
pub fn intern_all_names(st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::core::reserved_basis_names(st) {
        Err(e) => Err(e),
        Ok(_) => match nat_op_names(st) {
            Err(e) => Err(e),
            Ok(_) => match nat_div_mod_names(st) {
                Err(e) => Err(e),
                Ok(_) => match reduce_op_names(st) {
                    Err(e) => Err(e),
                    Ok(_) => match pin(st, &basis_names::sorry_ax_name()) {
                        Err(e) => Err(e),
                        Ok(_) => match pin(st, &basis_names::quot_sound_name()) {
                            Err(e) => Err(e),
                            Ok(_) => Ok(()),
                        },
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The differential test (`proof/ConRon/Arena/CheckerTest.lean`)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::canon::i_constant_info_beq;
    use crate::arena::intern::{intern_ci_list, intern_cv, intern_decls};
    use crate::arena::std_axioms::i_constant_val_matches_pin;
    use crate::arena::store::EStore;
    use con_ron_core::cached::state_c;
    use con_ron_core::cached::state_c::CState;
    use con_ron_core::kernel::basis_raw;
    use con_ron_core::kernel::canon as ccanon;
    use con_ron_core::kernel::checker as ckr;
    use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, Declaration, Env};
    use con_ron_core::kernel::expr;
    use con_ron_core::kernel::expr::{BinderMeta, Expr};
    use con_ron_core::kernel::fenv;
    use con_ron_core::kernel::level;
    use con_ron_core::kernel::name;
    use con_ron_core::kernel::name::Name;
    use con_ron_core::kernel::prop_when;
    use con_ron_core::kernel::std_axioms as cstd;
    use con_ron_core::ron::ptr::P;

    // --- the mode, the pins, and the outcome comparisons ---------------------

    /// The mode every check runs at: `.verified`, the lane the bridge is
    /// stated at.
    fn mu() -> CheckMode {
        CheckMode::Verified
    }

    /// The empty pin list, which is what `CheckerTest.lean` passes: no subject
    /// below reaches the `Nat.div`/`Nat.mod` variant loop with its guards
    /// passing, so the list's contents are not what is under test.
    fn no_pins() -> Vec<NatOpPinSet> {
        Vec::new()
    }

    /// The empty pin list, interned.
    fn no_pins_i() -> Vec<INatOpPinSet> {
        Vec::new()
    }

    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture must build without a decline"),
        }
    }

    /// The arena's error against con-ron-core's: same constructor, same
    /// message.  `Native` — the port's own decline, which no con-leche `throw`
    /// stands behind — never matches, which is right: a `Native` claims
    /// nothing (the twin's `errEq`, whose fourth constructor has no con-leche
    /// counterpart at all).
    fn err_eq(a: &CheckError, b: &CheckError) -> bool {
        match (a, b) {
            (CheckError::NotImplemented(x), CheckError::NotImplemented(y)) => {
                name::str_eq(x, y)
            }
            (CheckError::Invalid(x), CheckError::Invalid(y)) => name::str_eq(x, y),
            (CheckError::Internal(x), CheckError::Internal(y)) => name::str_eq(x, y),
            _ => false,
        }
    }

    /// `Env.consts` as owned records: con-ron-core shares a stored constant
    /// through a `P`, and `intern_ci_list` wants the values.
    fn unshare(cs: &Vec<P<ConstantInfo>>) -> Vec<ConstantInfo> {
        let mut out: Vec<ConstantInfo> = Vec::with_capacity(cs.len());
        let mut i: usize = 0;
        while i < cs.len() {
            out.push(con_ron_core::kernel::env::constant_info_dup(&cs[i]));
            i += 1;
        }
        out
    }

    /// **The whole-environment comparison.**  The twin reads the arena's
    /// environment BACK (`denoteCIList`) and compares with con-leche's; the
    /// port INTERNS con-ron-core's and compares handles, which is the same
    /// test read in the other direction — `denoteE` is injective, so two
    /// constants have the same handles exactly when they denote the same
    /// values — and needs no second readback.  It is also slightly stronger:
    /// it compares the install-computed fields (`ctorParams`, `fire`, the
    /// reducibility hint) that a readback compares too but a `canon` would not.
    fn env_agrees(st: &mut AState, fe: &IFEnv, env: &Env) -> bool {
        let want = ok(intern_ci_list(st, &unshare(&env.consts)));
        let got = &fe.env.consts;
        if want.len() != got.len() {
            return false;
        }
        let mut i: usize = 0;
        while i < want.len() {
            if !i_constant_info_beq(&want[i], &got[i]) {
                return false;
            }
            i += 1;
        }
        true
    }

    // --- the three runs ------------------------------------------------------

    /// Intern a declaration list and run the arena's `check_decls_pure` on it.
    fn run_decls(ds_cl: &Vec<Declaration>) -> (AState, Result<IFEnv, CheckError>) {
        let mut st = AState::init(EStore::empty());
        let ds = ok(intern_decls(&mut st, ds_cl));
        let r = check_decls_pure(&mut st, &mu(), &no_pins_i(), &ds);
        (st, r)
    }

    /// con-ron-core's own `check_decls_pure` on the same values.
    fn core_decls(ds_cl: &Vec<Declaration>) -> Result<Env, CheckError> {
        let mut cst: CState = state_c::cstate_new();
        match ckr::check_decls_pure(&mu(), &no_pins(), &mut cst, ds_cl) {
            Ok(fe) => Ok(fe.env),
            Err(e) => Err(e),
        }
    }

    /// The arena's `check_decls_pure` against con-ron-core's, over the WHOLE
    /// outcome: the same environment, constant for constant, or the same error.
    fn chk_decls(ds_cl: &Vec<Declaration>) -> bool {
        let (mut st, r) = run_decls(ds_cl);
        match (r, core_decls(ds_cl)) {
            (Ok(fe), Ok(env)) => env_agrees(&mut st, &fe, &env),
            (Err(a), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    /// The arena's `check_decl` at a non-empty environment against
    /// con-ron-core's.  The environment is built by `check_decls_pure` on
    /// con-ron-core's side and by interning ITS result on the arena's, so the
    /// two calls see the same environment and the check is about the STEP.
    fn chk_decl(env_cl: &Env, d_cl: &Declaration) -> bool {
        let mut st = AState::init(EStore::empty());
        let cs = ok(intern_ci_list(&mut st, &unshare(&env_cl.consts)));
        let mut ds1: Vec<Declaration> = Vec::with_capacity(1);
        ds1.push(con_ron_core::frontend::export_c::declaration_dup(d_cl));
        let ds = ok(intern_decls(&mut st, &ds1));
        let fe0: IFEnv = mk_ifenv(crate::arena::env::IEnv { consts: cs });
        let arena = check_decl(&mut st, &mu(), &no_pins_i(), fe0, &ds[0]);
        let mut cst: CState = state_c::cstate_new();
        let fe_cl = fenv::mk_fenv(con_ron_core::kernel::env::env_dup(env_cl));
        let core = ckr::check_decl(&mu(), &no_pins(), &mut cst, fe_cl, d_cl);
        match (arena, core) {
            (Ok(fe), Ok(fe2)) => env_agrees(&mut st, &fe, &fe2.env),
            (Err(a), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    /// The TWO-PHASE fold against con-ron-core's ONE-PHASE `check_decls_pure`,
    /// over the whole outcome — con-leche proves the two are the same accept
    /// (`fullyChecked_checkDecls`), and this is that agreement, measured.  The
    /// startup pin walk runs in front, as `run_pipeline` will.
    ///
    /// It is also the test of the per-declaration BRACKET, since `check_pending`
    /// is the only caller of `enter_scratch`/`drop_scratch`: a handle that
    /// leaked out of the scratch tier would make the installed environment
    /// compare unequal to con-ron-core's.
    fn chk_install(ds_cl: &Vec<Declaration>) -> bool {
        let mut st = AState::init(EStore::empty());
        let ds = ok(intern_decls(&mut st, ds_cl));
        let pins = ok(intern_all_pins(&mut st, &no_pins()));
        let arena = install_then_check(&mut st, &mu(), &pins, &ds);
        match (arena, core_decls(ds_cl)) {
            (Ok(fe), Ok(env)) => env_agrees(&mut st, &fe, &env),
            (Err((a, _)), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    /// con-ron-core's own outcome, pinned by hand: an accept whose environment
    /// has this many constants.
    fn ok_size(r: &Result<Env, CheckError>, n: usize) -> bool {
        match r {
            Ok(env) => env.consts.len() == n,
            Err(_) => false,
        }
    }

    /// con-ron-core's own outcome, pinned by hand: a failure of this kind and
    /// this message.
    fn fails_with(r: &Result<Env, CheckError>, x: &CheckError) -> bool {
        match r {
            Err(e) => err_eq(e, x),
            Ok(_) => false,
        }
    }

    // --- the subjects, written once as con-ron-core values -------------------

    fn nm(s: &str) -> Name {
        name::mk_str(name::anonymous(), s.chars().map(|c| c as u32).collect())
    }

    fn never() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    fn nat_ty() -> Expr {
        expr::mk_const(basis_names::nat_name(), Vec::new())
    }

    fn zero_e() -> Expr {
        expr::mk_const(basis_names::nat_zero_name(), Vec::new())
    }

    fn succ_e() -> Expr {
        expr::mk_const(basis_names::nat_succ_name(), Vec::new())
    }

    fn cv(n: Name, lps: Vec<Name>, ty: Expr) -> ConstantVal {
        ConstantVal { name: n, level_params: lps, ty }
    }

    fn hint() -> ReducibilityHint {
        ReducibilityHint::Regular(1)
    }

    /// `two := Nat.succ (Nat.succ Nat.zero)`.
    fn d_two() -> Declaration {
        Declaration::DefnDecl(
            cv(nm("two"), Vec::new(), nat_ty()),
            expr::app(succ_e(), expr::app(succ_e(), zero_e())),
            hint(),
        )
    }

    /// A definition whose value does not inhabit its declared type.
    fn d_two_bad() -> Declaration {
        Declaration::DefnDecl(
            cv(nm("bad"), Vec::new(), nat_ty()),
            expr::sort(level::zero()),
            hint(),
        )
    }

    /// A definition whose type mentions a constant nothing declares.
    fn d_unknown() -> Declaration {
        Declaration::DefnDecl(
            cv(nm("u"), Vec::new(), expr::mk_const(nm("nope"), Vec::new())),
            zero_e(),
            hint(),
        )
    }

    /// A definition under a reserved basis name.
    fn d_reserved() -> Declaration {
        Declaration::DefnDecl(
            cv(basis_names::nat_name(), Vec::new(), nat_ty()),
            zero_e(),
            hint(),
        )
    }

    /// A definition with a loose bound variable in its value.
    fn d_loose() -> Declaration {
        Declaration::DefnDecl(
            cv(nm("l"), Vec::new(), nat_ty()),
            expr::bvar(0),
            hint(),
        )
    }

    /// A definition with duplicate universe parameters.
    fn d_dup_univ() -> Declaration {
        let mut lps: Vec<Name> = Vec::with_capacity(2);
        lps.push(nm("u"));
        lps.push(nm("u"));
        Declaration::DefnDecl(cv(nm("d"), lps, nat_ty()), zero_e(), hint())
    }

    /// The proposition a theorem is stated at: `Eq.{1} Nat 0 0`, over the
    /// pinned `Eq` basis — an ORDINARY user axiom is a positive decline at its
    /// own record, so a proposition has to come from the basis rather than be
    /// postulated.
    fn p_e() -> Expr {
        expr::app(
            expr::app(
                expr::app(
                    expr::mk_const(basis_names::eq_name(), cstd::one_level()),
                    nat_ty(),
                ),
                zero_e(),
            ),
            zero_e(),
        )
    }

    /// `Eq.refl Nat 0`.
    fn pf_e() -> Expr {
        expr::app(
            expr::app(
                expr::mk_const(basis_names::eq_refl_name(), cstd::one_level()),
                nat_ty(),
            ),
            zero_e(),
        )
    }

    /// A theorem: `Eq.refl Nat 0` proves `0 = 0`.
    fn d_thm() -> Declaration {
        Declaration::ThmDecl(cv(nm("t"), Vec::new(), p_e()), pf_e())
    }

    /// A theorem whose type is not a proposition.
    fn d_thm_not_prop() -> Declaration {
        Declaration::ThmDecl(cv(nm("tn"), Vec::new(), nat_ty()), zero_e())
    }

    /// A theorem whose value does not inhabit its statement.
    fn d_thm_bad() -> Declaration {
        Declaration::ThmDecl(cv(nm("tb"), Vec::new(), p_e()), zero_e())
    }

    /// An `opaque`: stored as an `axiomInfo`, its value a discarded witness.
    fn d_opaque() -> Declaration {
        Declaration::OpaqueDecl(
            cv(nm("o"), Vec::new(), nat_ty()),
            expr::app(succ_e(), expr::app(succ_e(), zero_e())),
        )
    }

    /// `sorryAx`: the one axiom tolerated as a DECLARATION, installing nothing.
    fn d_sorry() -> Declaration {
        Declaration::AxiomDecl(cv(
            basis_names::sorry_ax_name(),
            Vec::new(),
            expr::forall_e(
                expr::sort(level::succ(level::zero())),
                expr::bvar(0),
                never(),
            ),
        ))
    }

    /// `propext` at a shape the pinned `Iff` family does not back.
    fn d_propext() -> Declaration {
        Declaration::AxiomDecl(cv(
            cstd::propext_name(),
            Vec::new(),
            expr::sort(level::zero()),
        ))
    }

    /// An ordinary user axiom: a positive decline at its own record.
    fn d_other_ax() -> Declaration {
        Declaration::AxiomDecl(cv(nm("myax"), Vec::new(), nat_ty()))
    }

    /// `Nat.add` under a nonstandard body: the structural-`Nat` pin gate's
    /// subject.  The environment has no `Nat.add` dependencies, so the gate
    /// declines with its environment message.
    fn d_nat_op(n: Name) -> Declaration {
        Declaration::DefnDecl(
            cv(
                n,
                Vec::new(),
                expr::forall_e(
                    nat_ty(),
                    expr::forall_e(nat_ty(), nat_ty(), never()),
                    never(),
                ),
            ),
            expr::lam(
                nat_ty(),
                expr::lam(nat_ty(), expr::bvar(1), never()),
                never(),
            ),
            hint(),
        )
    }

    fn d_nat_add() -> Declaration {
        d_nat_op(name::mk_str(
            basis_names::nat_name(),
            "add".chars().map(|c| c as u32).collect(),
        ))
    }

    /// `Nat.div` under a nonstandard body: the WF-recursive pin gate's subject,
    /// declining at `divModEnvGuard` (the environment has no `Nat.ble`).
    fn d_nat_div() -> Declaration {
        d_nat_op(name::mk_str(
            basis_names::nat_name(),
            "div".chars().map(|c| c as u32).collect(),
        ))
    }

    // --- the lists -----------------------------------------------------------

    fn list1(a: Declaration) -> Vec<Declaration> {
        let mut v: Vec<Declaration> = Vec::with_capacity(1);
        v.push(a);
        v
    }

    /// The basis prefix every accepting list starts with: the pinned `Eq`
    /// block, then the pinned `Nat` block.
    fn basis_prefix() -> Vec<Declaration> {
        let mut v: Vec<Declaration> = Vec::with_capacity(2);
        v.push(Declaration::BasisDecl(BasisKind::EqK));
        v.push(Declaration::BasisDecl(BasisKind::NatK));
        v
    }

    /// The basis prefix plus the given records.
    fn prefixed(ds: Vec<Declaration>) -> Vec<Declaration> {
        let mut v = basis_prefix();
        let mut ds = ds;
        while ds.len() > 0 {
            let d = ds.remove(0);
            v.push(d);
        }
        v
    }

    /// The accepting list: the two basis blocks, a definition, a theorem, an
    /// opaque, and a tolerated `sorryAx`.
    fn ds_good() -> Vec<Declaration> {
        prefixed(vec![d_two(), d_thm(), d_opaque(), d_sorry()])
    }

    /// The quotient block, which requires the pinned `Eq` basis first.
    fn ds_quot() -> Vec<Declaration> {
        let mut v: Vec<Declaration> = Vec::with_capacity(2);
        v.push(Declaration::BasisDecl(BasisKind::EqK));
        v.push(Declaration::BasisDecl(BasisKind::QuotK));
        v
    }

    /// The quotient block WITHOUT the `Eq` basis: a decline.
    fn ds_quot_bad() -> Vec<Declaration> {
        list1(Declaration::BasisDecl(BasisKind::QuotK))
    }

    /// A duplicate declaration: the second `two` is invalid input.
    fn ds_dup() -> Vec<Declaration> {
        prefixed(vec![d_two(), d_two()])
    }

    // --- what con-ron-core itself says ---------------------------------------

    /// `chk_decls` passes when the two checkers AGREE, and two agreeing
    /// failures agree.  These five lines pin con-ron-core's own outcome by
    /// hand, so that the differential below is evidence of something.
    #[test]
    fn con_ron_cores_own_outcome_on_the_subjects() {
        assert!(ok_size(&core_decls(&basis_prefix()), 7));
        assert!(ok_size(&core_decls(&ds_good()), 10));
        assert!(ok_size(&core_decls(&ds_quot()), 8));
        assert!(fails_with(
            &core_decls(&ds_quot_bad()),
            &CheckError::NotImplemented(code_points(&M_QUOT_BASIS_EQ))
        ));
        assert!(fails_with(
            &core_decls(&ds_dup()),
            &CheckError::Invalid(code_points(
                &crate::arena::checker_base::M_DUP_DECL
            ))
        ));
    }

    // --- the differential: `check_decls_pure` --------------------------------

    #[test]
    fn check_decls_pure_agrees_on_the_basis_blocks() {
        assert!(chk_decls(&basis_prefix()));
        assert!(chk_decls(&ds_quot()));
        assert!(chk_decls(&ds_quot_bad()));
        assert!(chk_decls(&list1(Declaration::BasisDecl(BasisKind::PunitK))));
        assert!(chk_decls(&list1(Declaration::BasisDecl(BasisKind::EmptyK))));
        assert!(chk_decls(&list1(Declaration::BasisDecl(BasisKind::FalseK))));
    }

    #[test]
    fn check_decls_pure_agrees_on_the_accept_lane() {
        assert!(chk_decls(&ds_good()));
        assert!(chk_decls(&ds_dup()));
        assert!(chk_decls(&prefixed(vec![d_sorry()])));
    }

    #[test]
    fn check_decls_pure_agrees_on_the_reject_lane() {
        assert!(chk_decls(&prefixed(vec![d_two_bad()])));
        assert!(chk_decls(&prefixed(vec![d_unknown()])));
        assert!(chk_decls(&prefixed(vec![d_reserved()])));
        assert!(chk_decls(&prefixed(vec![d_loose()])));
        assert!(chk_decls(&prefixed(vec![d_dup_univ()])));
        assert!(chk_decls(&prefixed(vec![d_thm_bad()])));
        assert!(chk_decls(&prefixed(vec![d_thm_not_prop()])));
    }

    #[test]
    fn check_decls_pure_agrees_on_the_decline_lane() {
        assert!(chk_decls(&prefixed(vec![d_propext()])));
        assert!(chk_decls(&prefixed(vec![d_other_ax()])));
        assert!(chk_decls(&prefixed(vec![d_nat_add()])));
        assert!(chk_decls(&prefixed(vec![d_nat_div()])));
    }

    // --- the differential: `check_decl` at a non-empty environment ------------

    /// The environment `basis_prefix` installs, on con-ron-core's side.
    fn env_basis() -> Env {
        match core_decls(&basis_prefix()) {
            Ok(env) => env,
            Err(_) => panic!("the basis prefix must install"),
        }
    }

    #[test]
    fn check_decl_agrees_at_a_non_empty_environment() {
        let e = env_basis();
        assert_eq!(e.consts.len(), 7);
        assert!(chk_decl(&e, &d_two()));
        assert!(chk_decl(&e, &d_two_bad()));
        assert!(chk_decl(&e, &d_unknown()));
        assert!(chk_decl(&e, &d_reserved()));
        assert!(chk_decl(&e, &d_loose()));
        assert!(chk_decl(&e, &d_dup_univ()));
    }

    #[test]
    fn check_decl_agrees_on_the_axiom_and_basis_arms() {
        let e = env_basis();
        assert!(chk_decl(&e, &d_opaque()));
        assert!(chk_decl(&e, &d_sorry()));
        assert!(chk_decl(&e, &d_propext()));
        assert!(chk_decl(&e, &d_other_ax()));
        assert!(chk_decl(&e, &d_nat_add()));
        assert!(chk_decl(&e, &d_nat_div()));
        assert!(chk_decl(&e, &Declaration::BasisDecl(BasisKind::PunitK)));
        assert!(chk_decl(&e, &Declaration::BasisDecl(BasisKind::QuotK)));
        assert!(chk_decl(
            &e,
            &Declaration::QuotDecl(
                QuotKind::Type,
                cv(basis_names::quot_name(), Vec::new(), nat_ty())
            )
        ));
    }

    // --- the differential: the TWO-PHASE fold --------------------------------

    #[test]
    fn install_then_check_agrees_with_the_one_phase_fold() {
        assert!(chk_install(&basis_prefix()));
        assert!(chk_install(&ds_good()));
        assert!(chk_install(&ds_quot()));
        assert!(chk_install(&ds_quot_bad()));
        assert!(chk_install(&ds_dup()));
        assert!(chk_install(&prefixed(vec![d_two_bad()])));
    }

    #[test]
    fn install_then_check_agrees_on_the_rest() {
        assert!(chk_install(&prefixed(vec![d_unknown()])));
        assert!(chk_install(&prefixed(vec![d_thm_bad()])));
        assert!(chk_install(&prefixed(vec![d_thm_not_prop()])));
        assert!(chk_install(&prefixed(vec![d_opaque()])));
        assert!(chk_install(&prefixed(vec![d_nat_add()])));
        assert!(chk_install(&prefixed(vec![d_nat_div()])));
    }

    // --- the pieces below `check_decl` ---------------------------------------

    /// The arena's `std_axiom_ok` against con-ron-core's.
    fn chk_std_axiom(env_cl: &Env, c: &ConstantVal) -> bool {
        let mut st = AState::init(EStore::empty());
        let cs = ok(intern_ci_list(&mut st, &unshare(&env_cl.consts)));
        let icv = ok(intern_cv(&mut st, c));
        let fe: IFEnv = mk_ifenv(crate::arena::env::IEnv { consts: cs });
        let got = ok(crate::arena::decl_check::std_axiom_ok(&mut st, &fe, &icv));
        let fe_cl = fenv::mk_fenv(con_ron_core::kernel::env::env_dup(env_cl));
        got == cstd::std_axiom_ok(&fe_cl, c)
    }

    #[test]
    fn std_axiom_ok_agrees() {
        let e = env_basis();
        assert!(chk_std_axiom(
            &e,
            &cv(cstd::propext_name(), Vec::new(), expr::sort(level::zero()))
        ));
        assert!(chk_std_axiom(
            &e,
            &cv(cstd::choice_name(), Vec::new(), expr::sort(level::zero()))
        ));
        assert!(chk_std_axiom(&e, &cv(nm("x"), Vec::new(), nat_ty())));
    }

    /// The arena's `matchesPin` against con-ron-core's, on a term that differs
    /// only in a binder's `pw` datum (which the comparison forgives), on one
    /// that differs in its type (which it does not), and on one that differs in
    /// its level parameters.
    fn chk_matches_pin(c: &ConstantVal, pin: &ConstantVal) -> bool {
        let mut st = AState::init(EStore::empty());
        let a = ok(intern_cv(&mut st, c));
        let b = ok(intern_cv(&mut st, pin));
        let got = ok(i_constant_val_matches_pin(&st, &a, &b));
        got == cstd::matches_pin_fast(c, pin)
    }

    #[test]
    fn matches_pin_agrees() {
        let two = nm("two");
        assert!(chk_matches_pin(
            &cv(name::dup(&two), Vec::new(), nat_ty()),
            &cv(name::dup(&two), Vec::new(), nat_ty())
        ));
        assert!(chk_matches_pin(
            &cv(name::dup(&two), Vec::new(), nat_ty()),
            &cv(name::dup(&two), Vec::new(), expr::sort(level::zero()))
        ));
        assert!(chk_matches_pin(
            &cv(
                name::dup(&two),
                Vec::new(),
                expr::forall_e(nat_ty(), nat_ty(), never())
            ),
            &cv(
                name::dup(&two),
                Vec::new(),
                expr::forall_e(
                    nat_ty(),
                    nat_ty(),
                    expr::binder_meta(prop_when::if_all_zero(Vec::new()))
                )
            )
        ));
        let mut lps: Vec<Name> = Vec::with_capacity(1);
        lps.push(nm("u"));
        assert!(chk_matches_pin(
            &cv(name::dup(&two), lps, nat_ty()),
            &cv(name::dup(&two), Vec::new(), nat_ty())
        ));
    }

    /// The arena's `canonEqList` against con-ron-core's, on the pinned blocks
    /// and on a block that is not one.
    fn chk_canon_list(xs: &Vec<ConstantInfo>, ys: &Vec<ConstantInfo>) -> bool {
        let mut st = AState::init(EStore::empty());
        let a = ok(intern_ci_list(&mut st, xs));
        let b = ok(intern_ci_list(&mut st, ys));
        let got = ok(crate::arena::canon::canon_eq_list(&mut st, &a, &b, 0));
        got == ccanon::canon_eq_list(xs, ys)
    }

    #[test]
    fn canon_eq_list_agrees() {
        let nat = basis_raw::basis_kind_decls(&BasisKind::NatK);
        let eq = basis_raw::basis_kind_decls(&BasisKind::EqK);
        assert!(chk_canon_list(&nat, &basis_raw::basis_kind_decls(&BasisKind::NatK)));
        assert!(chk_canon_list(&eq, &basis_raw::basis_kind_decls(&BasisKind::EqK)));
        assert!(chk_canon_list(&eq, &nat));
        assert!(chk_canon_list(
            &con_ron_core::kernel::basis_tables::basis_decls_a(&BasisKind::EqK),
            &eq
        ));
    }

    /// The arena's `basisPinHit` against con-ron-core's.
    fn chk_basis_pin_hit(block: &Vec<ConstantInfo>) -> bool {
        let mut st = AState::init(EStore::empty());
        let b = ok(intern_ci_list(&mut st, block));
        let got = ok(basis_pin_hit(&mut st, &b));
        let want = basis_raw::basis_pin_hit(block);
        match (got, want) {
            (None, None) => true,
            (Some(x), Some(y)) => basis_kind_beq(&x, &y),
            _ => false,
        }
    }

    /// The six-constructor enum's equality, which `kernel::env` does not carry.
    fn basis_kind_beq(a: &BasisKind, b: &BasisKind) -> bool {
        match (a, b) {
            (BasisKind::EqK, BasisKind::EqK) => true,
            (BasisKind::NatK, BasisKind::NatK) => true,
            (BasisKind::PunitK, BasisKind::PunitK) => true,
            (BasisKind::EmptyK, BasisKind::EmptyK) => true,
            (BasisKind::FalseK, BasisKind::FalseK) => true,
            (BasisKind::QuotK, BasisKind::QuotK) => true,
            _ => false,
        }
    }

    #[test]
    fn basis_pin_hit_agrees() {
        assert!(chk_basis_pin_hit(&basis_raw::basis_kind_decls(&BasisKind::NatK)));
        assert!(chk_basis_pin_hit(&basis_raw::basis_kind_decls(&BasisKind::EqK)));
        assert!(chk_basis_pin_hit(&basis_raw::basis_kind_decls(&BasisKind::PunitK)));
        assert!(chk_basis_pin_hit(&basis_raw::basis_kind_decls(&BasisKind::QuotK)));
        assert!(chk_basis_pin_hit(&Vec::new()));
    }

    // --- the startup walk and `atDecl` ---------------------------------------

    /// `intern_all_pins` puts every pinned datum in the PERSISTENT tier, which
    /// is what makes a later `pin` of the same name — inside a scratch tier —
    /// hand back the persistent handle.  Beyond the twin's `#guard`s: the Lean
    /// tests this from outside, through `chkInstall`'s readback.
    #[test]
    fn the_startup_walk_interns_into_the_persistent_tier() {
        let mut st = AState::init(EStore::empty());
        let _ = ok(intern_all_pins(&mut st, &no_pins()));
        let n0 = st.store.pers_count();
        assert!(n0 > 0);
        // a scratch tier, and the same names again: nothing new is appended
        // and every handle is persistent
        enter_scratch(&mut st);
        let eqn = ok(pin(&mut st, &basis_names::eq_name()));
        assert!(eqn.is_persistent());
        let blk = ok(basis_kind_decls_a(&mut st, &BasisKind::EqK));
        let mut i: usize = 0;
        while i < blk.len() {
            let cvv = ok(crate::arena::env::i_constant_info_to_constant_val(
                &mut st.store,
                &blk[i],
            ));
            assert!(cvv.ty.is_persistent());
            i += 1;
        }
        assert_eq!(st.store.pers_count(), n0);
        drop_scratch(&mut st);
    }

    /// `at_decl` renders the fold position into the message, and only into the
    /// message: the kind is untouched.  Beyond the twin's `#guard`s.
    #[test]
    fn at_decl_renders_the_position() {
        let e = CheckError::Invalid(code_points(&M_NONSTD_AXIOM));
        match at_decl(e, 12) {
            CheckError::Invalid(m) => {
                let want: Vec<u32> = "non-standard axiom (declaration 12)"
                    .chars()
                    .map(|c| c as u32)
                    .collect();
                assert!(name::str_eq(&m, &want));
            }
            _ => panic!("at_decl keeps the kind"),
        }
    }
}
