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
    drop_scratch, enter_scratch, flush_caches, nat_div_mod_names, nat_op_deps,
    nat_op_equations, nat_op_guard, nat_op_names, CORE_WALK_FUEL,
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
use crate::arena::promote::{promote_new, promote_vg, PMemo};
use crate::arena::std_axioms::{choice_name, propext_name};
use crate::arena::trust_axioms::{
    of_reduce_bool_name, of_reduce_nat_name, reduce_op_names, trust_compiler_name,
};
use crate::arena::pins::{pin_quot_sound, pin_sorry_ax, Pins};
use crate::arena::env::nidx_vec_dup;
use crate::arena::store::{EStore, ETables, LTables, LsTables, NTables};
use crate::kernel::core_k;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env as cenv;
use crate::kernel::env::{BasisKind, CheckMode, QuotKind, ReducibilityHint};
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// `"arena: phase boundary on a frozen store"`, as code points: `freeze_tier`'s
/// decline when the store it is handed is already frozen.  Raised as the port's
/// own `Native` (the store's `M_FROZEN` is its precedent): con-leche and the
/// twin have no frozen tier, so the refinement claims nothing when it fires,
/// and no run of the binary reaches it — the one store the driver freezes is
/// phase A's, whose four flags are down.
pub const M_REFREEZE: [u32; 39] = [
    97, 114, 101, 110, 97, 58, 32, 112, 104, 97, 115, 101, 32, 98, 111, 117, 110, 100, 97,
    114, 121, 32, 111, 110, 32, 97, 32, 102, 114, 111, 122, 101, 110, 32, 115, 116, 111, 114,
    101
];

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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:78-89 checkBasisDecl` —
/// **install the pinned (pre-annotated) basis block.**  The three records that
/// install one — the fold's own `basisDecl` kind, a stream block
/// `basis_pin_hit` recognises and a quotient record `quot_pin_hit` recognises
/// — share this body.  The quotient block's types mention the pinned equality
/// former, which is why it requires the `Eq` basis first.
pub fn check_basis_decl(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    kind: &BasisKind,
) -> Result<IFEnv, CheckError> {
    match kind {
        BasisKind::QuotK => match crate::arena::decl_check::eq_basis_pinned(pers, fe.visible_below, st, &fe) {
            Err(e) => Err(e),
            Ok(b) => {
                if !b {
                    fail(CheckError::NotImplemented(code_points(&M_QUOT_BASIS_EQ)))
                } else {
                    check_basis_decl_install(pers, st, fe, kind)
                }
            }
        },
        _ => check_basis_decl_install(pers, st, fe, kind),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:427-437 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:78-89 checkBasisDecl` — the
/// cited `installBasisDecls fe (← BasisKind.declsA kind)`, past the quotient
/// gate.  Split off so the gate's two branches are tail calls.
pub fn check_basis_decl_install(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    kind: &BasisKind,
) -> Result<IFEnv, CheckError> {
    match basis_kind_decls_a(pers, st, kind) {
        Err(e) => Err(e),
        Ok(decls) => install_basis_decls(fe, &decls, 0),
    }
}

// ---------------------------------------------------------------------------
// One declaration (`Checker.lean:80-192` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — **check a
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the stored
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the rest of
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the pinned
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the last
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

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — the
/// `.indDecl` arm.  **THE PINNED BASIS BLOCKS FIRST**: a stream's `Nat` block
/// arrives as an ordinary inductive block and is recognised HERE; a block under
/// a pinned name that does NOT match falls through to the ordinary route, where
/// `check_constant_val`'s reserved-name check REJECTS it.  The route itself is
/// `arena::inductives`' seam (task #97-P4d part 2).
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
        Ok(None) => crate::arena::inductives::check_ind_decl(
            pers,
            cenv::check_mode_dup(mode),
            fe,
            i_constant_infos_dup(block),
            n_p,
            st,
        ),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:439-626 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean:93-202 checkDecl` — **the
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

/// con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/Checker.lean:204-224 checkDeclStep` — **one
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
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    d: &IDeclaration,
) -> Result<IFEnv, CheckError> {
    let vis: u64 = fe.visible_below;
    flush_caches(st);
    enter_scratch(st);
    match check_decl(pers, st, mode, pins, fe, d) {
        Err(e) => Err(e),
        Ok(fe2) => {
            let k: u64 = fe2.visible_below - vis;
            match promote_new(pers, st, PMemo::empty(), CORE_WALK_FUEL, k, fe2) {
                Err(e) => Err(e),
                Ok((_, fe3)) => {
                    drop_scratch(st);
                    Ok(fe3)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/Checker.lean:226-235 checkDeclsPureGo` — the
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

/// con-leche: ConLeche/Kernel/Checker.lean:628-632 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/Checker.lean:237-241 checkDeclsPure` — the
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

// ---------------------------------------------------------------------------
// The two-phase fold the binary runs (`Checker.lean:210-341` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Installed.lean:83-91 PendingCheck
/// Lean twin: `proof/ConRon/Arena/Checker.lean:269-277 PendingCheck` — a
/// phase-A record awaiting its phase-B check: the datum that crosses the
/// install/check seam, the fold position of the declaration (its error tag) and
/// the environment counter at the install.
pub struct PendingCheck {
    pub vg: ValueGroup,
    pub pos: u64,
    pub vis: u64,
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — phase
/// A's step BODY: annotate-and-install for the three value kinds, the ordinary
/// step `check_decl` for everything else.  The four arms are four functions,
/// so every one of them is a tail call.
///
/// **The body, not the step** — `annot_step` below is this under the
/// per-declaration bracket, and the split exists so the bracket is written
/// ONCE for the four arms instead of four times (DESIGN.md §8.3, "Phase A runs
/// in the scratch tier too, with promotion", task #97-P6-2).  What the body
/// returns is what a step LEAVES BEHIND: the extended environment, and — for
/// the three value kinds — the `ValueGroup` phase B will check.  The fold
/// position and the environment counter the pending record carries are the
/// bracket's to supply.
pub fn annot_step_go(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pd: &IDeclaration,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match pd {
        IDeclaration::DefnDecl(cv, value, hint) => {
            annot_step_defn(pers, st, mode, pins, fe, pd, cv, value, hint)
        }
        IDeclaration::ThmDecl(cv, value) => annot_step_thm(pers, st, mode, fe, cv, value),
        IDeclaration::OpaqueDecl(cv, value) => {
            annot_step_opaque(pers, st, mode, pins, fe, pd, cv, value)
        }
        _ => annot_step_other(pers, st, mode, pins, fe, pd),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:318-372 annotStep` — **phase
/// A's step, bracketed**; `i` is the fold position the record is tagged with.
///
/// **The bracket, and why phase A has one** (DESIGN.md §8.3, "Phase A runs in
/// the scratch tier too, with promotion", the coordinator's amendment after
/// task #97-P4f's measurement).  Task #97-P4d ran phase A in the PERSISTENT
/// tier, on the reading that the install writes exactly the terms the
/// environment keeps.  It does — but it does not write ONLY those:
/// `install_constant_val` and `install_value` annotate, and annotation infers,
/// and inference reduces, and every intermediate of all of that was interned
/// permanently beside them.  Measured on `Init`: 5.06 M permanent nodes on top
/// of the parse's 6.14 M, **+82 %**, and con-ron-arena's peak RSS 3.9× today's
/// con-ron.  con-leche and con-ron get the same effect from GC; the arena's
/// answer is con-leche #64's, and it is the bracket phase B already has with
/// one operation added at its end:
///
/// ```text
/// flush_caches; enter_scratch; <the step>; promote; drop_scratch
/// ```
///
/// `promote` (`arena::promote`) is the memoised structural copy scratch →
/// persistent, run on **exactly what leaves the step**: the `k` constants the
/// step installed (`promote_new`, `k` from the counter read before it) and the
/// pending record (`promote_vg` — an `opaque`'s value is not in the
/// environment, so the seam has to be promoted beside it, at the SAME memo, so
/// that the sharing between a header's type and its value survives the copy).
/// A persistent handle promotes to itself, so a record that installs what the
/// parse already built pays one tier-bit test per handle.  After it the
/// environment and the `PendingCheck`s name persistent handles only, which is
/// what lets `drop_scratch` take the tier — and it must run after the step and
/// before the drop: the scratch nodes are gone once the tier is dropped.
///
/// **The flush stays where con-leche puts it, at the head** — `annotStepC`
/// reaches its four arms through `annotValueC` (`Cached/Installed.lean:139`),
/// the `.thmDecl` arm's own `flushC` (`:168`) and `checkDeclStepC`
/// (`Cached/ParsedC.lean:279-282`), so con-leche enters every phase-A record
/// with EMPTY caches (task #97g's item 4).  `drop_scratch` flushes too, so
/// what the head flush covers is the FIRST record of the fold, whose caches
/// are whatever `intern_all_pins` left.
pub fn annot_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    i: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    pd: &IDeclaration,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    let vis: u64 = fe.visible_below;
    flush_caches(st);
    enter_scratch(st);
    match annot_step_go(pers, st, mode, pins, fe, pd) {
        Err(e) => Err(e),
        Ok((fe2, vg_opt)) => {
            let k: u64 = fe2.visible_below - vis;
            match vg_opt {
                None => match promote_new(pers, st, PMemo::empty(), CORE_WALK_FUEL, k, fe2) {
                    Err(e) => Err(e),
                    Ok((_, fe3)) => {
                        drop_scratch(st);
                        Ok((fe3, pend))
                    }
                },
                Some(vg) => annot_step_promote(pers, st, i, vis, k, fe2, pend, vg),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:318-372 annotStep` — the
/// bracket's `some vg` arm: the seam promoted first and the environment at the
/// SAME memo, then the tier dropped and the record pushed.
#[allow(clippy::too_many_arguments)]
pub fn annot_step_promote(
    pers: &PersTier,
    st: &mut AState,
    i: u64,
    vis: u64,
    k: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    vg: ValueGroup,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    match promote_vg(pers, st, PMemo::empty(), CORE_WALK_FUEL, vg) {
        Err(e) => Err(e),
        Ok((m, vg2)) => match promote_new(pers, st, m, CORE_WALK_FUEL, k, fe) {
            Err(e) => Err(e),
            Ok((_, fe2)) => {
                drop_scratch(st);
                let mut pend2 = pend;
                pend2.push(PendingCheck {
                    vg: vg2,
                    pos: i,
                    vis,
                });
                Ok((fe2, pend2))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — the
/// `.defnDecl` arm: a pin-certified operation takes the ordinary step (its
/// check is not separable from its install), everything else is annotated,
/// installed and recorded as pending.
#[allow(clippy::too_many_arguments)]
pub fn annot_step_defn(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pd: &IDeclaration,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match nat_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => match nat_div_mod_names(st) {
            Err(e) => Err(e),
            Ok(ds) => {
                if nidx_contains_from(&ns, 0, &cv.name) || nidx_contains_from(&ds, 0, &cv.name)
                {
                    annot_step_other(pers, st, mode, pins, fe, pd)
                } else {
                    annot_step_defn_install(pers, st, mode, fe, cv, value, hint)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — the
/// `.defnDecl` arm's install and push.  The environment counter the pending
/// record carries is the BRACKET's now (task #97-P6-2): it reads it before the
/// step, which is both con-leche's own RC-linearity note — read it after the
/// push and the push copies the whole index — and what makes the promotion's
/// `k` computable without holding `fe` across the step.
pub fn annot_step_defn_install(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match install_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match install_value(pers, fe.visible_below, st, mode, &fe, &cv_a, value) {
            Err(e) => Err(e),
            Ok(jv) => {
                let fe2: IFEnv = crate::arena::env::ifenv_push(
                    fe,
                    IConstantInfo::DefnInfo(
                        i_constant_val_dup(&cv_a),
                        jv.dup2(),
                        cenv::reducibility_hint_dup(hint),
                    ),
                );
                Ok((
                    fe2,
                    Some(ValueGroup { kind: ValueKind::Defn, cv_a, jv }),
                ))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — the
/// `.thmDecl` arm: **a theorem installs BY STATEMENT**.  The header's install
/// half only; the value is recorded raw and never touched here (phase B
/// annotates it), so phase A never enters a theorem's body.
pub fn annot_step_thm(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match install_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => {
            let fe2: IFEnv = crate::arena::env::ifenv_push(
                fe,
                IConstantInfo::ThmInfo(i_constant_val_dup(&cv_a), value.dup2()),
            );
            Ok((
                fe2,
                Some(ValueGroup { kind: ValueKind::Thm, cv_a, jv: value.dup2() }),
            ))
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — the
/// `.opaqueDecl` arm: a `reduce*` witness takes the ordinary step (its identity
/// certificate is part of its install), everything else is annotated, installed
/// **as an axiom** — an opaque's value being a discarded witness — and recorded
/// as pending.
pub fn annot_step_opaque(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pd: &IDeclaration,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match reduce_op_names(st) {
        Err(e) => Err(e),
        Ok(ns) => {
            if nidx_contains_from(&ns, 0, &cv.name) {
                annot_step_other(pers, st, mode, pins, fe, pd)
            } else {
                annot_step_opaque_install(pers, st, mode, fe, cv, value)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — the
/// opaque arm's install and push.  **An `opaque`'s value is not in the
/// environment**: the arm pushes `.axiomInfo cvA` and hands the annotated
/// VALUE to the pending record alone, which is why the bracket promotes the
/// `ValueGroup` beside the environment and at the same memo.
pub fn annot_step_opaque_install(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match install_constant_val(pers, fe.visible_below, st, mode, &fe, cv) {
        Err(e) => Err(e),
        Ok(cv_a) => match install_value(pers, fe.visible_below, st, mode, &fe, &cv_a, value) {
            Err(e) => Err(e),
            Ok(jv) => {
                let fe2: IFEnv = crate::arena::env::ifenv_push(
                    fe,
                    IConstantInfo::AxiomInfo(i_constant_val_dup(&cv_a)),
                );
                Ok((
                    fe2,
                    Some(ValueGroup { kind: ValueKind::Opaque, cv_a, jv }),
                ))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:279-316 annotStepGo` — the
/// catch-all arm, shared by the three gated branches above: the ordinary step,
/// which records nothing pending.
pub fn annot_step_other(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pd: &IDeclaration,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match check_decl(pers, st, mode, pins, fe, pd) {
        Err(e) => Err(e),
        Ok(fe2) => Ok((fe2, None)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:185-195 annotDeclStep
/// Lean twin: `proof/ConRon/Arena/Checker.lean:374-388 annotDeclStep` — phase
/// A's step with the position carried and the error tagged: a failing step
/// reports the `CheckError` together with `i`, the fold position of the
/// declaration that failed.
///
/// Deviation: the twin restores the PRE-step state on a failure (it is written
/// as a state function); a failure aborts the whole fold here, so nothing reads
/// the state afterwards and no snapshot is taken —
/// `con_ron_core::cached::installed::annot_decl_step`'s arrangement.
pub fn annot_decl_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>),
    pd: &IDeclaration,
) -> Result<(u64, IFEnv, Vec<PendingCheck>), (CheckError, u64)> {
    let i: u64 = p.0;
    match annot_step(pers, st, mode, pins, i, p.1, p.2, pd) {
        Err(e) => Err((e, i)),
        Ok(q) => Ok((i + 1, q.0, q.1)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:390-401 annotFold` — phase A as
/// a fold over the records, as an index recursion threading the accumulator by
/// value.
pub fn annot_fold(
    pers: &PersTier,
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
        match annot_decl_step(pers, st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => annot_fold(pers, st, mode, pins, q, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending
/// Lean twin: `proof/ConRon/Arena/Checker.lean:403-419 checkPending` —
/// **phase B's check of one record**, against the prefix view
/// `fe.restrictTo pc.vis`.
///
/// **This is (C)'s per-declaration bracket** (DESIGN.md §8.3): the scratch tier
/// is turned on, `check_value_group` runs the inference and the conversion, and
/// the tier — with every node they appended and every cache row naming one — is
/// dropped.  Deviation: the twin's `throw` skips its `dropScratch` and the
/// caller restores the pre-record state instead; the port drops the tier on
/// BOTH paths, which lands in the same place (scratch off, persistent
/// untouched) without a snapshot.
///
/// **The index comes in by REFERENCE and the twin's `restrictTo` is the scalar
/// `pc.vis`** (task #97-P6-6b).  It used to come in by value, be restricted to
/// the record's prefix bound and be handed back at the installed one, which is
/// exactly what forbade a pool: `n` workers cannot each own the environment
/// (`ifenv_dup` is ≈1.4 GB a worker on Mathlib) and cannot each restrict a
/// shared one.  With the bound a parameter this function borrows the index,
/// mutates nothing outside `st`, and is what a worker runs.
pub fn check_pending(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pc: &PendingCheck,
) -> Result<(), CheckError> {
    enter_scratch(st);
    let r: Result<(), CheckError> = check_value_group(pers, pc.vis, st, mode, fe, &pc.vg);
    drop_scratch(st);
    r
}

/// con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList
/// Lean twin: `proof/ConRon/Arena/Checker.lean:421-430 checkPendingList` —
/// phase B as a pure walk: every record checked at its own prefix view, a
/// failure tagged with the record's fold position.
pub fn check_pending_list(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pend: &Vec<PendingCheck>,
    i: usize,
) -> Result<(), (CheckError, u64)> {
    if i >= pend.len() {
        Ok(())
    } else {
        match check_pending(pers, st, mode, fe, &pend[i]) {
            Err(e) => Err((e, pend[i].pos)),
            Ok(()) => check_pending_list(pers, st, mode, fe, pend, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:432-443 installThenCheck` —
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
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
) -> Result<IFEnv, (CheckError, u64)> {
    match annot_fold(
        pers,
        st,
        mode,
        pins,
        (0, mk_ifenv(i_env_empty()), Vec::new()),
        ds,
        0,
    ) {
        Err(e) => Err(e),
        Ok(p) => match check_pending_list(pers, st, mode, &p.1, &p.2, 0) {
            Err(e) => Err(e),
            Ok(()) => Ok(p.1),
        },
    }
}

// ---------------------------------------------------------------------------
// The driver's fold: the phase boundary and phase B on a worker
// (task #97-P5-Driver)
//
// `install_then_check` above threads ONE state through both phases.  The
// binary does not: at the phase boundary it FREEZES the persistent tier into
// one `PersTier` every phase-B worker borrows, and each worker checks its
// records on a state of its own over that tier (`crates/con-ron/src/pool.rs`).
// Every sequential piece of that is here, in the verified crate, so that the driver is a straight line
// of calls into extracted functions and the one thing it does not share with
// `check_decls_phased` below is the pool's scheduling:
//
//   annot_fold_hooked       phase A (`annot_fold`, plus a read-only hook)
//   freeze_tier             the boundary
//   worker_state            a phase-B worker's state over the frozen tier
//   check_pending_worker    phase B on one worker in record order — what the
//                           pool is argued equal to, by record index
//   thaw_tier               the boundary undone
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:67-141 installLoop
/// What the driver prints between phase A's steps (the `--progress`
/// heartbeat's install line), as a trait the verified fold calls: the hook
/// takes the state by SHARED reference and returns nothing, so it cannot
/// change a verdict — `annot_fold_hooked` is `annot_fold` with a call to it
/// before each step, and `Refine2/Checker/Phased.lean` proves the two equal.
/// `Modeller`'s arrangement (`frontend::types`): the trait is declared here,
/// the implementations live in the unverified crate.
pub trait InstallHook {
    /// con-leche: Main.lean:67-141 installLoop
    /// Before record `pos` of `total` is installed.
    fn install_before(&self, pers: &PersTier, ar: &EStore, pos: u64, total: usize, d: &IDeclaration);
}

/// con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls
/// Lean twin: none — `annot_fold` with the driver's hook; the twin has no hook
/// and the refinement is `annot_fold`'s, through the equation
/// `annot_fold_hooked_eq` (`Refine2/Checker/Phased.lean`).
/// **Phase A as the driver runs it**: `annot_fold` step for step, with
/// `h.install_before` called before each record.  The hook reads the store and
/// writes nothing the fold can see.
#[allow(clippy::too_many_arguments)]
pub fn annot_fold_hooked<H: InstallHook>(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>),
    ds: &Vec<IDeclaration>,
    i: usize,
    h: &H,
) -> Result<(u64, IFEnv, Vec<PendingCheck>), (CheckError, u64)> {
    if i >= ds.len() {
        Ok(p)
    } else {
        h.install_before(pers, &st.store, p.0, ds.len(), &ds[i]);
        match annot_decl_step(pers, st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => annot_fold_hooked(pers, st, mode, pins, q, ds, i + 1, h),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls
/// Lean twin: none — the fold's start triple, `(0, mkIFEnv IEnv.empty, #[])`,
/// which `installThenCheck` writes inline.
/// Phase A's starting accumulator, so that the driver builds it with the same
/// call the verified fold does.
pub fn fold_start() -> (u64, IFEnv, Vec<PendingCheck>) {
    (0, mk_ifenv(i_env_empty()), Vec::new())
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the twin has no tier to move; its phase-B worker reads the
/// persistent tier where it is (`AState.worker`, `Arena/Phased.lean`).
/// **The persistent tier out of the store and into a value** (task
/// #97-P6-6b's driver function, moved here by task #97-P5-Driver): the four
/// stores' persistent tables are moved into one `PersTier` and the four
/// `shared_on` flags go up, so every later persistent read of this store goes
/// to the tier the caller now holds and a persistent append is declined
/// (`arena::store`'s frozen-tier guard).
///
/// **A store that is already frozen is declined** (`M_REFREEZE`, `Native`):
/// its own persistent tables are empty and its reads go to a tier this
/// function cannot see, so moving the tables out would hand back an empty
/// tier.  The driver freezes phase A's store once, with every flag down, and
/// the guard is what lets the refinement state the boundary with no
/// hypothesis about the flags.
pub fn freeze_tier(ar: &mut EStore) -> Result<PersTier, CheckError> {
    if ar.shared_on || ar.lss.shared_on || ar.lss.ls.shared_on || ar.lss.ls.ns.shared_on {
        Err(CheckError::Native(code_points(&M_REFREEZE)))
    } else {
        let n: NTables = core::mem::replace(&mut ar.lss.ls.ns.pers, NTables::empty());
        let l: LTables = core::mem::replace(&mut ar.lss.ls.pers, LTables::empty());
        let ls: LsTables = core::mem::replace(&mut ar.lss.pers, LsTables::empty());
        let e: ETables = core::mem::replace(&mut ar.pers, ETables::empty());
        ar.shared_on = true;
        ar.lss.shared_on = true;
        ar.lss.ls.shared_on = true;
        ar.lss.ls.ns.shared_on = true;
        Ok(PersTier { n, l, ls, e })
    }
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the inverse of `freeze_tier`, which has none either.
/// **`freeze_tier` inverted**: the tier back into the store and the flags
/// down, so that everything after phase B — the verdict line's label, the
/// failing record's name, the receipts — reads the handles it was given.
/// `thaw_tier(ar, freeze_tier(ar))` leaves a store with its flags down exactly
/// as it found it (`Refine2/Checker/Phased.lean`'s `freeze_thaw`).
pub fn thaw_tier(ar: &mut EStore, tier: PersTier) {
    ar.lss.ls.ns.pers = tier.n;
    ar.lss.ls.pers = tier.l;
    ar.lss.pers = tier.ls;
    ar.pers = tier.e;
    ar.shared_on = false;
    ar.lss.shared_on = false;
    ar.lss.ls.shared_on = false;
    ar.lss.ls.ns.shared_on = false;
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the twin has no tier to move.
/// **`thaw_tier` for a store whose flags may have moved**: each store gets
/// back the tier its reads went to — `tier`'s table if its `shared_on` flag is
/// up, its own table otherwise — and the four flags go down.  When every flag
/// is up, which is the only case the checker reaches, this is `thaw_tier`.
/// The frozen-tier `Nat.div`/`Nat.mod` attempt
/// (`arena::decl_check::check_div_mod_pin_attempt`, task #97-T2-LOCKSTEP D4c)
/// thaws its kept post-attempt state with it, so that the refinement carries
/// the attempt's own relation across the thaw with no fact about the flags
/// (`Refine2/Checker/Base.lean`'s `thaw_read_tier_rel`).
pub fn thaw_read_tier(ar: &mut EStore, tier: PersTier) {
    let PersTier { n, l, ls, e } = tier;
    if ar.lss.ls.ns.shared_on {
        ar.lss.ls.ns.pers = n;
    }
    if ar.lss.ls.shared_on {
        ar.lss.ls.pers = l;
    }
    if ar.lss.shared_on {
        ar.lss.pers = ls;
    }
    if ar.shared_on {
        ar.pers = e;
    }
    ar.shared_on = false;
    ar.lss.shared_on = false;
    ar.lss.ls.shared_on = false;
    ar.lss.ls.ns.shared_on = false;
}

/// con-leche: none — the pin table is handles, so a copy is a copy of words
/// Lean twin: none — the value is `Pins` itself (`Refine2`'s `pins_dup_val`).
/// A phase-B worker's copy of the driver's `Pins`: sixty-eight handles into the
/// frozen tier and nothing else, so every record's state may own one and none
/// of them has to intern anything to fill it.
pub fn pins_dup(p: &Pins) -> Pins {
    Pins {
        names: nidx_vec_dup(&p.names),
        reserved: nidx_vec_dup(&p.reserved),
        empty_levels: p.empty_levels.dup2(),
        zero_level: p.zero_level.dup2(),
        sort_one: p.sort_one.dup2(),
    }
}

/// con-leche: Main.lean:262-278 checkWorker
/// Lean twin: `proof/ConRon/Arena/Phased.lean:37-44 AState.worker` — the twin's
/// phase-B worker reads the persistent tier where it is.
/// **A phase-B worker's start state** (task #97-P6-6b's `pool::worker_state`,
/// moved here by task #97-P5-Driver): an empty store whose four `shared_on`
/// flags are up, so that every persistent read goes to the `PersTier` the
/// boundary froze and a persistent append is declined; fresh memos and caches;
/// and a copy of the pins.  The scratch tier is off until `check_pending`
/// opens it.
pub fn worker_state(pins: &Pins) -> AState {
    let mut st = AState::init(EStore::empty());
    st.store.shared_on = true;
    st.store.lss.shared_on = true;
    st.store.lss.ls.shared_on = true;
    st.store.lss.ls.ns.shared_on = true;
    st.pins = pins_dup(pins);
    st
}

/// con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList
/// Lean twin: `proof/ConRon/Arena/Phased.lean:46-54 checkPendingWorker` —
/// **phase B on ONE worker, in record order**: a worker's state
/// (`worker_state`) and `check_pending_list` from it, over the frozen tier.
/// This is `pool::check_pool` at one worker call for call — the worker claims
/// the records in order and checks each with `check_pending` on its one
/// state — and it is the walk the pool's merged table is argued equal to by
/// record index at every worker count (`pool.rs`'s note, which also states
/// the one thing a second worker adds).
pub fn check_pending_worker(
    pers: &PersTier,
    mode: &CheckMode,
    fe: &IFEnv,
    pins: &Pins,
    pend: &Vec<PendingCheck>,
) -> Result<(), (CheckError, u64)> {
    let mut st = worker_state(pins);
    check_pending_list(pers, &mut st, mode, fe, pend, 0)
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Phased.lean:56-67 installThenCheckPhased` —
/// **the declaration fold the binary runs**, sequentially: phase A
/// (`annot_fold_hooked`), the boundary (`freeze_tier`), phase B on one worker
/// over the frozen tier (`check_pending_worker`), the boundary undone
/// (`thaw_tier`).  `driver::check_decls_driver` is this function with the
/// observer's read-only lines between the calls and `pool::check_pool` in
/// place of `check_pending_worker`; the capstone (`ConRon.Capstone`) is
/// stated about this one.
pub fn check_decls_phased<H: InstallHook>(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    h: &H,
) -> Result<IFEnv, (CheckError, u64)> {
    match annot_fold_hooked(pers, st, mode, pins, fold_start(), ds, 0, h) {
        Err(e) => Err(e),
        Ok(p) => match freeze_tier(&mut st.store) {
            Err(e) => Err((e, p.0)),
            Ok(tier) => {
                let r = check_pending_worker(&tier, mode, &p.1, &st.pins, &p.2);
                thaw_tier(&mut st.store, tier);
                match r {
                    Err(e) => Err(e),
                    Ok(()) => Ok(p.1),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:445-457 atDecl` — the fold's
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:445-457 atDecl` — the twin's
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — **the
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
    pers: &PersTier,
    st: &mut AState,
    pins: &Vec<NatOpPinSet>,
) -> Result<Vec<INatOpPinSet>, CheckError> {
    match intern_all_basis(pers, st, 0) {
        Err(e) => Err(e),
        Ok(()) => match intern_all_axiom_pins(pers, st) {
            Err(e) => Err(e),
            Ok(()) => match intern_all_names(st) {
                Err(e) => Err(e),
                Ok(()) => intern_pin_sets(pers, st, pins, 0, Vec::new()),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the six
/// basis blocks in both forms, as a cursor over
/// `con_ron_core::kernel::basis_raw::block_pin_kinds` plus `quotK` (the twin
/// spells the twelve calls out).
pub fn intern_all_basis(pers: &PersTier, st: &mut AState, i: usize) -> Result<(), CheckError> {
    let ks: Vec<BasisKind> = all_basis_kinds();
    if i >= ks.len() {
        Ok(())
    } else {
        match basis_kind_decls(pers, st, &ks[i]) {
            Err(e) => Err(e),
            Ok(_) => match basis_kind_decls_a(pers, st, &ks[i]) {
                Err(e) => Err(e),
                Ok(_) => intern_all_basis(pers, st, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the six
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the
/// standard and compiler-trust axiom pins, in the twin's order.  The twin's
/// `iffA`/`propextA` family is this port's raw one (`arena::std_axioms`'
/// module note).
pub fn intern_all_axiom_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::iff_raw(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::iff_intro_raw(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::iff_rec_raw(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::nonempty_raw(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_axiom_pins_rest(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the
/// rest of the axiom pins and the two reduce pins.
pub fn intern_all_axiom_pins_rest(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::nonempty_intro_raw(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::nonempty_rec_raw(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::propext_raw(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::choice_raw(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_trust_pins(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the
/// compiler-trust shapes and the two reduce pins.
pub fn intern_all_trust_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::trust_axioms::true_cv_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::trust_axioms::true_intro_cv_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::trust_axioms::trust_compiler_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::trust_axioms::bool_cv_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_reduce_pins(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the
/// four `reduce*`/`ofReduce*` shapes and the two pinned defining expressions.
pub fn intern_all_reduce_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::trust_axioms::reduce_nat_cv_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::trust_axioms::reduce_bool_cv_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::trust_axioms::of_reduce_nat_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::trust_axioms::of_reduce_bool_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => match crate::arena::trust_axioms::reduce_nat_decl_pin(pers, st) {
                        Err(e) => Err(e),
                        Ok(_) => match crate::arena::trust_axioms::reduce_bool_decl_pin(pers, st)
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:461-497 internAllPins` — the
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
                    Ok(_) => match pin_sorry_ax(st) {
                        Err(e) => Err(e),
                        Ok(_) => match pin_quot_sound(st) {
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

    /// con-leche: none — a test fixture
    /// The state the driver builds: an empty store with the reserved-name
    /// pins interned (task #97-P6-4a).  Every subject below reads a pin
    /// somewhere, so this is the only state they can run in.
    fn pinned_state() -> AState {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        match crate::arena::pins::intern_reserved_pins(pers, &mut st) {
            Ok(()) => st,
            Err(_) => panic!("the reserved-name pins must intern"),
        }
    }
    use crate::arena::core::pin;
    use crate::arena::intern::{intern_ci_list, intern_cv};
    use crate::arena::std_axioms::i_constant_val_matches_pin;
    use crate::arena::store::EStore;
    use crate::kernel::basis_names;
    use crate::kernel::basis_raw;
    use crate::kernel::canon as ccanon;
    use crate::kernel::env::{ConstantInfo, ConstantVal, Env};
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr};
    use crate::kernel::fenv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;
    use crate::kernel::std_axioms as cstd;
    use crate::ron::ptr::P;

    // --- the mode, the pins, and the outcome comparisons ---------------------


    /// The empty pin list, which is what `CheckerTest.lean` passes: no subject
    /// below reaches the `Nat.div`/`Nat.mod` variant loop with its guards
    /// passing, so the list's contents are not what is under test.
    fn no_pins() -> Vec<NatOpPinSet> {
        Vec::new()
    }


    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture must build without a decline"),
        }
    }


    /// `Env.consts` as owned records: con-ron-core shares a stored constant
    /// through a `P`, and `intern_ci_list` wants the values.
    fn unshare(cs: &Vec<P<ConstantInfo>>) -> Vec<ConstantInfo> {
        let mut out: Vec<ConstantInfo> = Vec::with_capacity(cs.len());
        let mut i: usize = 0;
        while i < cs.len() {
            out.push(crate::kernel::env::constant_info_dup(&cs[i]));
            i += 1;
        }
        out
    }


    // --- the three runs ------------------------------------------------------








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



    fn cv(n: Name, lps: Vec<Name>, ty: Expr) -> ConstantVal {
        ConstantVal { name: n, level_params: lps, ty }
    }




















    // --- the lists -----------------------------------------------------------








    // --- what con-ron-core itself says ---------------------------------------


    // --- the differential: `check_decls_pure` --------------------------------





    // --- the differential: `check_decl` at a non-empty environment ------------




    // --- the differential: the TWO-PHASE fold --------------------------------



    // --- the pieces below `check_decl` ---------------------------------------

    /// The arena's `std_axiom_ok` against con-ron-core's.
    fn chk_std_axiom(env_cl: &Env, c: &ConstantVal) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let cs = ok(intern_ci_list(pers, &mut st, &unshare(&env_cl.consts)));
        let icv = ok(intern_cv(pers, &mut st, c));
        let fe: IFEnv = mk_ifenv(crate::arena::env::IEnv { consts: cs });
        let got = ok(crate::arena::decl_check::std_axiom_ok(pers, fe.visible_below, &mut st, &fe, &icv));
        let fe_cl = fenv::mk_fenv(crate::kernel::env::env_dup(env_cl));
        got == cstd::std_axiom_ok(&fe_cl, c)
    }

    /// The environment the basis prefix installs, built directly rather than
    /// by running a checker over `basis_prefix()`: a `.basisDecl` install IS
    /// `BasisKind.declsA`, pushed in order (task #97-SWAP — the `Expr`-tree
    /// checker that used to produce this environment is gone, and the table it
    /// would have installed is right here).
    fn env_basis() -> Env {
        let mut cs: Vec<ConstantInfo> = Vec::new();
        for k in [BasisKind::EqK, BasisKind::NatK] {
            let mut b = crate::kernel::basis_tables::basis_decls_a(&k);
            while b.len() > 0 {
                cs.push(b.remove(0));
            }
        }
        crate::kernel::env::env_of(&cs)
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
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let a = ok(intern_cv(pers, &mut st, c));
        let b = ok(intern_cv(pers, &mut st, pin));
        let got = ok(i_constant_val_matches_pin(pers, &st, &a, &b));
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
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let a = ok(intern_ci_list(pers, &mut st, xs));
        let b = ok(intern_ci_list(pers, &mut st, ys));
        let got = ok(crate::arena::canon::canon_eq_list(pers, &mut st, &a, &b, 0));
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
            &crate::kernel::basis_tables::basis_decls_a(&BasisKind::EqK),
            &eq
        ));
    }

    /// The arena's `basisPinHit` against con-ron-core's.
    fn chk_basis_pin_hit(block: &Vec<ConstantInfo>) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let b = ok(intern_ci_list(pers, &mut st, block));
        let got = ok(basis_pin_hit(pers, &mut st, &b));
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
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let _ = ok(intern_all_pins(pers, &mut st, &no_pins()));
        let n0 = st.store.pers_count(pers);
        assert!(n0 > 0);
        // a scratch tier, and the same names again: nothing new is appended
        // and every handle is persistent
        enter_scratch(&mut st);
        let eqn = ok(pin(pers, &mut st, &basis_names::eq_name()));
        assert!(eqn.is_persistent());
        let blk = ok(basis_kind_decls_a(pers, &mut st, &BasisKind::EqK));
        let mut i: usize = 0;
        while i < blk.len() {
            let cvv = ok(crate::arena::env::i_constant_info_to_constant_val(
                pers,
                &mut st.store,
                &blk[i],
            ));
            assert!(cvv.ty.is_persistent());
            i += 1;
        }
        assert_eq!(st.store.pers_count(pers), n0);
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

    /// **The startup walk at the binary's own pin list**, not the empty one
    /// every check above runs with: the embedded `con-ron-pins/1` text
    /// (`kernel::pins_text::PINS_TEXT`, 26 721 records) decoded and interned
    /// into the persistent tier.  This is the path `run_pipeline` takes and the
    /// one thing about it that could fail quietly — the `2^27` handle cap, or a
    /// fresh-memo walk that does not finish.
    ///
    /// It runs on a 1 GB stack for `pins_decode`'s own reason (it recurses once
    /// per record), which is what the driver gives its checker threads anyway.
    #[test]
    fn the_startup_walk_interns_the_embedded_pins() {
        let h = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(|| {
                let pers: &PersTier = &PersTier::empty();
                let pins = match crate::kernel::pins_decode::decode_embedded() {
                    Ok(v) => v,
                    Err(_) => panic!("the embedded pin text must decode"),
                };
                assert!(pins.len() > 0);
                let mut st = pinned_state();
                let ip = ok(intern_all_pins(pers, &mut st, &pins));
                assert_eq!(ip.len(), pins.len());
                // every interned pin is a PERSISTENT handle — the startup walk
                // runs before the first `enter_scratch`, which is what makes a
                // later `intern` of the same node hand the persistent one back
                let mut i: usize = 0;
                while i < ip.len() {
                    assert!(ip[i].div_pin.is_persistent());
                    assert!(ip[i].mod_pin.is_persistent());
                    assert!(ip[i].div_proofs.len() > 0);
                    i += 1;
                }
                st.store.node_count(pers)
            })
            .unwrap()
            .join()
            .unwrap();
        assert!(h > 0);
    }
}
