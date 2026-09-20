//! `arena::decl_check` — the declaration-level checks, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/DeclCheck.lean`, which is con-leche's
//! `Kernel/DeclCheck.lean` and the declaration-level halves of
//! `Kernel/Checker.lean`, `StdAxioms.lean` and `TrustAxioms.lean`.
//!
//! ## One twin per PAIR
//!
//! con-leche carries each of these functions twice — once reading the linear
//! environment and once the index (`DeclCheck.lean`'s `…F` mirrors, which is
//! what both binaries run).  The arena has ONE environment type, so each pair
//! collapses into one twin carrying a `con-leche:` line per collapsed
//! declaration, and the twin keeps the UNSUFFIXED name.
//!
//! ## No closures
//!
//! * `divModCertStmts`' eleven local lambdas are named functions here, and its
//!   twenty opening `let`s are one record (`CertCtx`) — the treatment task
//!   #97-P4c gives `natOpEquations`' eight (`NatEqCtx`), so the seven branches
//!   read as the twin's;
//! * `divModCertsGuard`'s `(… .zip …).all` is an index recursion, bounded by
//!   the shorter list, which is what a `zip` means.
//!
//! ## What is `arena::inductives`'
//!
//! The modeled and native inductive installs are the other half of this phase
//! (task #97-P4d part 2).  Eight of `DeclCheck.lean`'s declarations are
//! theirs, because they call into those modules and nothing here does.

use crate::arena::canon::i_constant_info_beq;
use crate::arena::checker_base::{
    all_level_params_defined, astate_dup, consts_resolve_f_fast, or_else_attempt,
    OrElseStep,
};
use crate::arena::checker_split::{install_value, M_THM_NOT_PROP};
use crate::arena::core::{
    annotate_core, bool_false_name, bool_name, bool_true_name, const_e, ensure_sort_core,
    infer_type_core, is_def_eq_core, lift_fueled, lvl_eq, nat_add_name, nat_ap1, nat_ap2,
    nat_ble_name, nat_div_name, nat_gcd_name, nat_land_name, nat_lor_name, nat_mod_name,
    nat_mul_name, nat_op_deps, nat_op_guard, nat_op_stored_ok, nat_shift_left_name,
    nat_shift_right_name, nat_sub_name, nat_xor_name, pin, subst_const0, subst_const_all,
    zero_level, CHECK_FUEL, CORE_WALK_FUEL,
};
use crate::arena::env::{
    i_constant_info_dup, i_constant_info_to_constant_val, ifenv_find, ifenv_push,
    IConstantInfo, IConstantVal, IFEnv,
};
use crate::arena::expr_ops::{has_fvar_fast, loose_bvars_bounded_fast};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::monad::{fail, intern_e, intern_l_node, intern_ls_node, AState};
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::std_axioms::{
    choice_name, choice_raw, eq_a, i_constant_val_matches_pin, iff_intro_name,
    iff_intro_raw, iff_name, iff_raw, iff_rec_name, iff_rec_raw, nat_a, nonempty_intro_name,
    nonempty_intro_raw, nonempty_name, nonempty_raw, nonempty_rec_name, nonempty_rec_raw,
    propext_name, propext_raw,
};
use crate::arena::store::{ENodeView, LNodeView};
use crate::arena::trust_axioms::{
    bool_cv_a, of_reduce_op, of_reduce_pin_a, reduce_cert_var, reduce_decl_pin,
    reduce_nat_name, reduce_op_cv_a, true_cv_a, true_intro_cv_a, true_intro_name, true_name,
    trust_compiler_a,
};
use con_ron_core::kernel::basis_names;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::{CheckMode, ReducibilityHint};
use con_ron_core::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported Nat.div/mod spelling: no pin variant matched"`, as code points.
pub const M_DIVMOD_NO_VARIANT: [u32; 56] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 78, 97, 116, 46, 100, 105,
    118, 47, 109, 111, 100, 32, 115, 112, 101, 108, 108, 105, 110, 103, 58, 32, 110, 111,
    32, 112, 105, 110, 32, 118, 97, 114, 105, 97, 110, 116, 32, 109, 97, 116, 99, 104,
    101, 100
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported Nat.div/mod environment"`, as code points.
pub const M_DIVMOD_ENV: [u32; 35] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 78, 97, 116, 46, 100, 105,
    118, 47, 109, 111, 100, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"Nat.div/mod operation not stored"`, as code points.
pub const M_DIVMOD_NOT_STORED: [u32; 32] = [
    78, 97, 116, 46, 100, 105, 118, 47, 109, 111, 100, 32, 111, 112, 101, 114, 97, 116,
    105, 111, 110, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust opaque declaration"`, as code points.
pub const M_REDUCE_DECL: [u32; 45] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108,
    101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 100, 101,
    99, 108, 97, 114, 97, 116, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust opaque spelling: pin ground constants absent"`, as code points.
pub const M_REDUCE_PIN_ABSENT: [u32; 71] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108,
    101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 115, 112,
    101, 108, 108, 105, 110, 103, 58, 32, 112, 105, 110, 32, 103, 114, 111, 117, 110, 100,
    32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 97, 98, 115, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust opaque spelling"`, as code points.
pub const M_REDUCE_SPELLING: [u32; 42] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108,
    101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 115, 112,
    101, 108, 108, 105, 110, 103
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"pinned compiler-trust opaque is not the identity"`, as code points.
pub const M_REDUCE_NOT_ID: [u32; 48] = [
    112, 105, 110, 110, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114,
    117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 105, 115, 32, 110, 111, 116, 32,
    116, 104, 101, 32, 105, 100, 101, 110, 116, 105, 116, 121
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

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"duplicate declaration"`, as code points (`arena::checker_base`'s, spelled
/// again here because `install_basis_decl` is this module's).
pub const M_DUP_DECL: [u32; 21] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116,
    105, 111, 110
];

// ---------------------------------------------------------------------------
// The standard axioms' environment shape (`DeclCheck.lean:44-90` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the
/// pinned `Eq` basis, as its own function.  The twin's
/// `fe.find? eqName == some eqA` is a whole-constant comparison
/// (`arena::canon::i_constant_info_beq`), which is what `deriving DecidableEq`
/// gives the twin.
pub fn eq_basis_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match pin(st, &basis_names::eq_name()) {
        Err(e) => Err(e),
        Ok(en) => match eq_a(st) {
            Err(e) => Err(e),
            Ok(ea) => match ifenv_find(fe, &en) {
                Some(ci) => Ok(i_constant_info_beq(ci, &ea)),
                None => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the stored
/// `Iff` type former against the pin.  Factored out of the twin's `&&` cascade
/// so each lookup's `match` ends before the next one begins (task #14's borrow
/// rule, `con_ron_core::kernel::std_axioms::iff_pinned`'s arrangement).
pub fn iff_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match iff_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::IndInfo(cv_i, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_i);
                match iff_raw(st) {
                    Err(e) => Err(e),
                    Ok(p) => matches_pin_of_ci(st, &cv, p),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:115-117 ConstantVal.matchesPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the
/// twin's `cvI.matchesPin (← (← iffA).toConstantVal)`: the pin's common data,
/// then the comparison.  One function, because six call sites spell it.
pub fn matches_pin_of_ci(
    st: &mut AState,
    cv: &IConstantVal,
    pin_ci: IConstantInfo,
) -> Result<bool, CheckError> {
    match i_constant_info_to_constant_val(&mut st.store, &pin_ci) {
        Err(e) => Err(e),
        Ok(pcv) => i_constant_val_matches_pin(st, cv, &pcv),
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the stored
/// `Iff.intro` against the pin, at the pinned arity `2 2`.
pub fn iff_intro_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match iff_intro_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::CtorInfo(cv_ii, n_p, n_f)) => {
                if *n_p == 2 && *n_f == 2 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ii);
                    match iff_intro_raw(st) {
                    Err(e) => Err(e),
                    Ok(p) => matches_pin_of_ci(st, &cv, p),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the stored
/// `Iff.rec` against the pin, at the pinned arity `4 4`.  Only its *type* is
/// used, never its reduction rules.
pub fn iff_rec_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match iff_rec_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::RecInfo(cv_ir, m_i, r_p, _)) => {
                if *m_i == 4 && *r_p == 4 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ir);
                    match iff_rec_raw(st) {
                    Err(e) => Err(e),
                    Ok(p) => matches_pin_of_ci(st, &cv, p),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the stored
/// `Nonempty` type former against the pin.
pub fn nonempty_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match nonempty_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::IndInfo(cv_n, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_n);
                match nonempty_raw(st) {
                    Err(e) => Err(e),
                    Ok(p) => matches_pin_of_ci(st, &cv, p),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the stored
/// `Nonempty.intro` against the pin, at the pinned arity `1 1`.
pub fn nonempty_intro_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match nonempty_intro_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::CtorInfo(cv_ni, n_p, n_f)) => {
                if *n_p == 1 && *n_f == 1 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ni);
                    match nonempty_intro_raw(st) {
                    Err(e) => Err(e),
                    Ok(p) => matches_pin_of_ci(st, &cv, p),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the stored
/// `Nonempty.rec` against the pin, at the pinned arity `3 3`.
pub fn nonempty_rec_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match nonempty_rec_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::RecInfo(cv_nr, m_i, r_p, _)) => {
                if *m_i == 3 && *r_p == 3 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_nr);
                    match nonempty_rec_raw(st) {
                    Err(e) => Err(e),
                    Ok(p) => matches_pin_of_ci(st, &cv, p),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — is this
/// checked axiom one of the two recognized standard axioms, over
/// standardly-shaped stored `Iff` / `Nonempty` families (and the pinned `Eq`
/// basis)?  All three of each family's constants are pinned, not just the
/// type, because the verification has to REALIZE the axiom and nothing turns
/// an inhabitant of an opaque family into its fields except that family's own
/// recursor.
pub fn std_axiom_ok(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match propext_name(st) {
        Err(e) => Err(e),
        Ok(pn) => {
            if cv_a.name.eq2(&pn) {
                std_axiom_ok_propext(st, fe, cv_a)
            } else {
                match choice_name(st) {
                    Err(e) => Err(e),
                    Ok(cn) => {
                        if cv_a.name.eq2(&cn) {
                            std_axiom_ok_choice(st, fe, cv_a)
                        } else {
                            Ok(false)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the
/// `propext` branch: the pinned `Eq` basis and the three `Iff` constants, then
/// the axiom's own type.  The pin is `propextRaw` rather than the twin's
/// `propextA`, which `matchesPin` cannot tell apart (`arena::std_axioms`'
/// module note).
pub fn std_axiom_ok_propext(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match eq_basis_pinned(st, fe) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                Ok(false)
            } else {
                match iff_pinned(st, fe) {
                    Err(e) => Err(e),
                    Ok(b1) => {
                        if !b1 {
                            Ok(false)
                        } else {
                            std_axiom_ok_propext_rest(st, fe, cv_a)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the two
/// remaining `Iff` constants and `propext`'s own type.
pub fn std_axiom_ok_propext_rest(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match iff_intro_pinned(st, fe) {
        Err(e) => Err(e),
        Ok(b2) => {
            if !b2 {
                Ok(false)
            } else {
                match iff_rec_pinned(st, fe) {
                    Err(e) => Err(e),
                    Ok(b3) => {
                        if !b3 {
                            Ok(false)
                        } else {
                            match propext_raw(st) {
                                Err(e) => Err(e),
                                Ok(p) => i_constant_val_matches_pin(st, cv_a, &p),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the
/// `Classical.choice` branch: the three `Nonempty` constants, then the axiom's
/// own type.
pub fn std_axiom_ok_choice(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match nonempty_pinned(st, fe) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match nonempty_intro_pinned(st, fe) {
                    Err(e) => Err(e),
                    Ok(b2) => {
                        if !b2 {
                            Ok(false)
                        } else {
                            std_axiom_ok_choice_rest(st, fe, cv_a)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:54-90 stdAxiomOk` — the
/// recursor and `Classical.choice`'s own type.
pub fn std_axiom_ok_choice_rest(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match nonempty_rec_pinned(st, fe) {
        Err(e) => Err(e),
        Ok(b3) => {
            if !b3 {
                Ok(false)
            } else {
                match choice_raw(st) {
                    Err(e) => Err(e),
                    Ok(c) => i_constant_val_matches_pin(st, cv_a, &c),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The compiler-trust family's environment shape (`DeclCheck.lean:92-152`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:158-169 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:98-107 trustCompilerOk` — the
/// stored `True` against its pin.
pub fn true_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match true_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::IndInfo(cv_t, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_t);
                match true_cv_a(st) {
                    Err(e) => Err(e),
                    Ok(p) => i_constant_val_matches_pin(st, &cv, &p),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:158-169 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:98-107 trustCompilerOk` — the
/// stored `True.intro` against its pin, at the pinned arity `0 0`.
pub fn true_intro_pinned(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match true_intro_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(fe, &n) {
            Some(IConstantInfo::CtorInfo(cv_ti, n_p, n_f)) => {
                if *n_p == 0 && *n_f == 0 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ti);
                    match true_intro_cv_a(st) {
                        Err(e) => Err(e),
                        Ok(p) => i_constant_val_matches_pin(st, &cv, &p),
                    }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:158-169 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:98-107 trustCompilerOk` — is
/// `Lean.trustCompiler` installable here?  The `True` family must be stored
/// with the pinned shapes, and the checked axiom's type must match the pin.
pub fn trust_compiler_ok(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match true_pinned(st, fe) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match true_intro_pinned(st, fe) {
                    Err(e) => Err(e),
                    Ok(b2) => {
                        if !b2 {
                            Ok(false)
                        } else {
                            match trust_compiler_a(st) {
                                Err(e) => Err(e),
                                Ok(p) => i_constant_val_matches_pin(st, cv_a, &p),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:171-177 reduceStoredOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:282-286 reduceStoredOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:113-116 reduceStoredOk` — is
/// the reduce operation `c` stored as a checked opaque (`axiomInfo`, the
/// storage kind of every checked `opaque`) of the pinned type?
pub fn reduce_stored_ok(
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match ifenv_find(fe, c) {
        Some(IConstantInfo::AxiomInfo(cv_r)) => {
            let cv = crate::arena::env::i_constant_val_dup(cv_r);
            match reduce_op_cv_a(st, c) {
                Err(e) => Err(e),
                Ok(p) => i_constant_val_matches_pin(st, &cv, &p),
            }
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:179-186 reduceElemOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:288-294 reduceElemOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:122-130 reduceElemOk` — the
/// element-inductive shape an `ofReduce*` axiom needs: the pinned `Nat` basis
/// resp. a standardly-shaped stored `Bool`.
pub fn reduce_elem_ok(
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(rn) => {
            if c.eq2(&rn) {
                match pin(st, &basis_names::nat_name()) {
                    Err(e) => Err(e),
                    Ok(nn) => match nat_a(st) {
                        Err(e) => Err(e),
                        Ok(na) => match ifenv_find(fe, &nn) {
                            Some(ci) => Ok(i_constant_info_beq(ci, &na)),
                            None => Ok(false),
                        },
                    },
                }
            } else {
                reduce_elem_ok_bool(st, fe)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:179-186 reduceElemOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:122-130 reduceElemOk` — the
/// `Bool` branch: a standardly-shaped stored `Bool` inductive.
pub fn reduce_elem_ok_bool(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match bool_name(st) {
        Err(e) => Err(e),
        Ok(bn) => match ifenv_find(fe, &bn) {
            Some(IConstantInfo::IndInfo(cv_b, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_b);
                match bool_cv_a(st) {
                    Err(e) => Err(e),
                    Ok(p) => i_constant_val_matches_pin(st, &cv, &p),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:188-198 ofReduceAxOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:296-302 ofReduceAxOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:136-142 ofReduceAxOk` — is
/// this checked axiom a pinned `ofReduce*` over a standardly-shaped
/// environment?
pub fn of_reduce_ax_ok(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
) -> Result<bool, CheckError> {
    match of_reduce_op(st, &cv_a.name) {
        Err(e) => Err(e),
        Ok(c) => match eq_basis_pinned(st, fe) {
            Err(e) => Err(e),
            Ok(b) => {
                if !b {
                    Ok(false)
                } else {
                    of_reduce_ax_ok_rest(st, fe, cv_a, &c)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:188-198 ofReduceAxOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:136-142 ofReduceAxOk` — the
/// element and storage guards, then the axiom's own type.
pub fn of_reduce_ax_ok_rest(
    st: &mut AState,
    fe: &IFEnv,
    cv_a: &IConstantVal,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match reduce_elem_ok(st, fe, c) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match reduce_stored_ok(st, fe, c) {
                    Err(e) => Err(e),
                    Ok(b2) => {
                        if !b2 {
                            Ok(false)
                        } else {
                            match of_reduce_pin_a(st, &cv_a.name) {
                                Err(e) => Err(e),
                                Ok(p) => i_constant_val_matches_pin(st, cv_a, &p),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:209-213 reducePinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:304-308 reducePinGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:147-152 reducePinGuard` —
/// syntactic guards on the generated reduce pin (checked once at install).
pub fn reduce_pin_guard(
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match reduce_decl_pin(st, c) {
        Err(e) => Err(e),
        Ok(p) => ground_guards(st, fe, &p),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:209-213 reducePinGuard
/// con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:147-152 reducePinGuard` (and
/// `:411-416 divModPinGuard`, which is the same four guards on a different
/// pin) — closed, free-variable-free, level-monomorphic and resolving.  The
/// twin writes the four out twice; one function here.
pub fn ground_guards(
    st: &mut AState,
    fe: &IFEnv,
    p: &EIdx,
) -> Result<bool, CheckError> {
    match loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, p) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                Ok(false)
            } else {
                match has_fvar_fast(st, CORE_WALK_FUEL, p) {
                    Err(e) => Err(e),
                    Ok(f) => {
                        if f {
                            Ok(false)
                        } else {
                            ground_guards_rest(st, fe, p)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:209-213 reducePinGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:147-152 reducePinGuard` — the
/// two semantic guards, past the two syntactic ones.
pub fn ground_guards_rest(
    st: &mut AState,
    fe: &IFEnv,
    p: &EIdx,
) -> Result<bool, CheckError> {
    let empty: Vec<NIdx> = Vec::new();
    match all_level_params_defined(st, &empty, p) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                Ok(false)
            } else {
                consts_resolve_f_fast(st, fe, p)
            }
        }
    }
}

/// con-leche: none — `(natOpDeps c).all (natOpStoredOk fe)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:159-162 natOpStoredOkAll` —
/// an explicit list recursion (DESIGN.md §3.4 forbids the closure `List.all`
/// takes).  con-leche's `natOpGuard` has the WEAKER dependency test; this is
/// the stronger one `divModEnvGuard` asks for, which pins the type too.
pub fn nat_op_stored_ok_all(
    st: &mut AState,
    fe: &IFEnv,
    ns: &Vec<NIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ns.len() {
        Ok(true)
    } else {
        match nat_op_stored_ok(st, fe, &ns[i]) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    nat_op_stored_ok_all(st, fe, ns, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The `Nat.div`/`Nat.mod` pin variants (`DeclCheck.lean:170-199` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:118-130 divModDeclPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:178-186 divModDeclPin` — the
/// pinned defining expression of a pin-certified WF-recursive op in one pin
/// variant.  con-leche's `c = natDivName` chain is a handle comparison here.
pub fn div_mod_decl_pin(
    st: &mut AState,
    ps: &INatOpPinSet,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    match div_mod_slot(st, c) {
        Err(e) => Err(e),
        Ok(0) => Ok(ps.div_pin.dup2()),
        Ok(1) => Ok(ps.gcd_pin.dup2()),
        Ok(2) => Ok(ps.land_pin.dup2()),
        Ok(3) => Ok(ps.lor_pin.dup2()),
        Ok(4) => Ok(ps.xor_pin.dup2()),
        Ok(5) => Ok(ps.shift_left_pin.dup2()),
        Ok(6) => Ok(ps.shift_right_pin.dup2()),
        Ok(_) => Ok(ps.mod_pin.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:118-130 divModDeclPin
/// con-leche: ConLeche/Kernel/Checker.lean:132-142 divModCertProofs
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:178-186 divModDeclPin` — the
/// twin's seven-way `if c == …` chain, once: both `divModDeclPin` and
/// `divModCertProofs` walk it, and over handles each test interns a name.
/// `7` is the `else` arm, `Nat.mod`.
pub fn div_mod_slot(st: &mut AState, c: &NIdx) -> Result<u64, CheckError> {
    match nat_div_name(st) {
        Err(e) => Err(e),
        Ok(n) => {
            if c.eq2(&n) {
                Ok(0)
            } else {
                div_mod_slot_1(st, c)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:118-130 divModDeclPin
/// The chain's second test onward (`gcd`, `land`, `lor`).
pub fn div_mod_slot_1(st: &mut AState, c: &NIdx) -> Result<u64, CheckError> {
    match nat_gcd_name(st) {
        Err(e) => Err(e),
        Ok(n) => {
            if c.eq2(&n) {
                Ok(1)
            } else {
                match nat_land_name(st) {
                    Err(e) => Err(e),
                    Ok(n2) => {
                        if c.eq2(&n2) {
                            Ok(2)
                        } else {
                            match nat_lor_name(st) {
                                Err(e) => Err(e),
                                Ok(n3) => {
                                    if c.eq2(&n3) {
                                        Ok(3)
                                    } else {
                                        div_mod_slot_2(st, c)
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

/// con-leche: ConLeche/Kernel/Checker.lean:118-130 divModDeclPin
/// The chain's last three tests (`xor`, `shiftLeft`, `shiftRight`) and the
/// `else` arm.
pub fn div_mod_slot_2(st: &mut AState, c: &NIdx) -> Result<u64, CheckError> {
    match nat_xor_name(st) {
        Err(e) => Err(e),
        Ok(n) => {
            if c.eq2(&n) {
                Ok(4)
            } else {
                match nat_shift_left_name(st) {
                    Err(e) => Err(e),
                    Ok(n2) => {
                        if c.eq2(&n2) {
                            Ok(5)
                        } else {
                            match nat_shift_right_name(st) {
                                Err(e) => Err(e),
                                Ok(n3) => {
                                    if c.eq2(&n3) {
                                        Ok(6)
                                    } else {
                                        Ok(7)
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

/// con-leche: ConLeche/Kernel/Checker.lean:132-142 divModCertProofs
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:191-199 divModCertProofs` —
/// the certificate proof terms of a pin-certified WF-recursive op in one pin
/// variant, one per statement of `divModCertStmts`.
pub fn div_mod_cert_proofs(
    st: &mut AState,
    ps: &INatOpPinSet,
    c: &NIdx,
) -> Result<Vec<EIdx>, CheckError> {
    match div_mod_slot(st, c) {
        Err(e) => Err(e),
        Ok(0) => Ok(crate::arena::env::eidx_vec_dup(&ps.div_proofs)),
        Ok(1) => Ok(crate::arena::env::eidx_vec_dup(&ps.gcd_proofs)),
        Ok(2) => Ok(crate::arena::env::eidx_vec_dup(&ps.land_proofs)),
        Ok(3) => Ok(crate::arena::env::eidx_vec_dup(&ps.lor_proofs)),
        Ok(4) => Ok(crate::arena::env::eidx_vec_dup(&ps.xor_proofs)),
        Ok(5) => Ok(crate::arena::env::eidx_vec_dup(&ps.shift_left_proofs)),
        Ok(6) => Ok(crate::arena::env::eidx_vec_dup(&ps.shift_right_proofs)),
        Ok(_) => Ok(crate::arena::env::eidx_vec_dup(&ps.mod_proofs)),
    }
}

// ---------------------------------------------------------------------------
// The pinned characterization statements (`DeclCheck.lean:201-332`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:210-218 eqAt1` — the
/// statements' `Eq.{1} τ a b` former.
pub fn eq_at1(
    st: &mut AState,
    ty: &EIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match intern_l_node(st, LNodeView::Succ(z)) {
            Err(e) => Err(e),
            Ok(one) => {
                let mut us: Vec<crate::arena::handle::LIdx> = Vec::with_capacity(1);
                us.push(one);
                match intern_ls_node(st, us) {
                    Err(e) => Err(e),
                    Ok(hus) => eq_at1_app(st, hus, ty, a, b),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:210-218 eqAt1` — the three
/// applications, past the universe argument.
pub fn eq_at1_app(
    st: &mut AState,
    hus: crate::arena::handle::LsIdx,
    ty: &EIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match pin(st, &basis_names::eq_name()) {
        Err(e) => Err(e),
        Ok(en) => match intern_e(st, ENodeView::Const(en, hus)) {
            Err(e) => Err(e),
            Ok(e0) => match intern_e(st, ENodeView::App(e0, ty.dup2())) {
                Err(e) => Err(e),
                Ok(e1) => match intern_e(st, ENodeView::App(e1, a.dup2())) {
                    Err(e) => Err(e),
                    Ok(e2) => intern_e(st, ENodeView::App(e2, b.dup2())),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:222-225 natOne` — the numeral
/// `1` as `Nat.succ Nat.zero`.
pub fn nat_one(st: &mut AState) -> Result<EIdx, CheckError> {
    match pin(st, &basis_names::nat_succ_name()) {
        Err(e) => Err(e),
        Ok(s) => match pin(st, &basis_names::nat_zero_name()) {
            Err(e) => Err(e),
            Ok(z) => match const_e(st, &z) {
                Err(e) => Err(e),
                Ok(ze) => nat_ap1(st, &s, &ze),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:229-231 natVar` — the open
/// statements' variables `x := fvar 0`, `y := fvar 1` at `Nat`.
pub fn nat_var(st: &mut AState, i: u64) -> Result<EIdx, CheckError> {
    match pin(st, &basis_names::nat_name()) {
        Err(e) => Err(e),
        Ok(nt) => match const_e(st, &nt) {
            Err(e) => Err(e),
            Ok(ty) => intern_e(st, ENodeView::FVar(i, ty)),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// the twenty `let`s the twin's `do` block opens with, as one record.  Over
/// handles each of them interns, and the seven branches below read exactly as
/// the twin's; this is task #97-P4c's `NatEqCtx` treatment of
/// `natOpEquations`' eight.
pub struct CertCtx {
    pub nat_ty: EIdx,
    pub x: EIdx,
    pub y: EIdx,
    pub one: EIdx,
    pub ble_n: NIdx,
    pub bool_ty: EIdx,
    pub b_t: EIdx,
    pub b_f: EIdx,
    pub z: EIdx,
    pub two: EIdx,
    pub mod_n: NIdx,
    pub div_n: NIdx,
    pub add_n: NIdx,
    pub mul_n: NIdx,
    pub sub_n: NIdx,
    pub gcd_n: NIdx,
    pub sl_n: NIdx,
    pub sr_n: NIdx,
    pub land_n: NIdx,
    pub lor_n: NIdx,
    pub xor_n: NIdx,
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// first half of the twin's opening `let`s: the types, the variables and the
/// two `Bool` constructors.
pub fn cert_ctx(st: &mut AState) -> Result<CertCtx, CheckError> {
    match pin(st, &basis_names::nat_name()) {
        Err(e) => Err(e),
        Ok(nt) => match const_e(st, &nt) {
            Err(e) => Err(e),
            Ok(nat_ty) => match nat_var(st, 0) {
                Err(e) => Err(e),
                Ok(x) => match nat_var(st, 1) {
                    Err(e) => Err(e),
                    Ok(y) => match nat_one(st) {
                        Err(e) => Err(e),
                        Ok(one) => cert_ctx_bool(st, nat_ty, x, y, one),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// `Bool` constants and the numerals `0` and `2`.
pub fn cert_ctx_bool(
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
) -> Result<CertCtx, CheckError> {
    match nat_ble_name(st) {
        Err(e) => Err(e),
        Ok(ble_n) => match bool_name(st) {
            Err(e) => Err(e),
            Ok(bn) => match const_e(st, &bn) {
                Err(e) => Err(e),
                Ok(bool_ty) => match bool_true_name(st) {
                    Err(e) => Err(e),
                    Ok(btn) => match const_e(st, &btn) {
                        Err(e) => Err(e),
                        Ok(b_t) => match bool_false_name(st) {
                            Err(e) => Err(e),
                            Ok(bfn) => match const_e(st, &bfn) {
                                Err(e) => Err(e),
                                Ok(b_f) => cert_ctx_nums(
                                    st, nat_ty, x, y, one, ble_n, bool_ty, b_t, b_f,
                                ),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// numerals and the eleven operation names.
pub fn cert_ctx_nums(
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
    ble_n: NIdx,
    bool_ty: EIdx,
    b_t: EIdx,
    b_f: EIdx,
) -> Result<CertCtx, CheckError> {
    match pin(st, &basis_names::nat_zero_name()) {
        Err(e) => Err(e),
        Ok(zn) => match const_e(st, &zn) {
            Err(e) => Err(e),
            Ok(z) => match pin(st, &basis_names::nat_succ_name()) {
                Err(e) => Err(e),
                Ok(sn) => match nat_ap1(st, &sn, &one) {
                    Err(e) => Err(e),
                    Ok(two) => cert_ctx_names(
                        st, nat_ty, x, y, one, ble_n, bool_ty, b_t, b_f, z, two,
                    ),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// eleven operation names, in the twin's order.
pub fn cert_ctx_names(
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
    ble_n: NIdx,
    bool_ty: EIdx,
    b_t: EIdx,
    b_f: EIdx,
    z: EIdx,
    two: EIdx,
) -> Result<CertCtx, CheckError> {
    match nat_mod_name(st) {
        Err(e) => Err(e),
        Ok(mod_n) => match nat_div_name(st) {
            Err(e) => Err(e),
            Ok(div_n) => match nat_add_name(st) {
                Err(e) => Err(e),
                Ok(add_n) => match nat_mul_name(st) {
                    Err(e) => Err(e),
                    Ok(mul_n) => match nat_sub_name(st) {
                        Err(e) => Err(e),
                        Ok(sub_n) => match nat_gcd_name(st) {
                            Err(e) => Err(e),
                            Ok(gcd_n) => cert_ctx_names_rest(
                                st, nat_ty, x, y, one, ble_n, bool_ty, b_t, b_f, z, two,
                                mod_n, div_n, add_n, mul_n, sub_n, gcd_n,
                            ),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// last five names, and the record.
#[allow(clippy::too_many_arguments)]
pub fn cert_ctx_names_rest(
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
    ble_n: NIdx,
    bool_ty: EIdx,
    b_t: EIdx,
    b_f: EIdx,
    z: EIdx,
    two: EIdx,
    mod_n: NIdx,
    div_n: NIdx,
    add_n: NIdx,
    mul_n: NIdx,
    sub_n: NIdx,
    gcd_n: NIdx,
) -> Result<CertCtx, CheckError> {
    match nat_shift_left_name(st) {
        Err(e) => Err(e),
        Ok(sl_n) => match nat_shift_right_name(st) {
            Err(e) => Err(e),
            Ok(sr_n) => match nat_land_name(st) {
                Err(e) => Err(e),
                Ok(land_n) => match nat_lor_name(st) {
                    Err(e) => Err(e),
                    Ok(lor_n) => match nat_xor_name(st) {
                        Err(e) => Err(e),
                        Ok(xor_n) => Ok(CertCtx {
                            nat_ty,
                            x,
                            y,
                            one,
                            ble_n,
                            bool_ty,
                            b_t,
                            b_f,
                            z,
                            two,
                            mod_n,
                            div_n,
                            add_n,
                            mul_n,
                            sub_n,
                            gcd_n,
                            sl_n,
                            sr_n,
                            land_n,
                            lor_n,
                            xor_n,
                        }),
                    },
                },
            },
        },
    }
}

/// con-leche: none — the one-element hypothesis list `[h]` of `divModCertStmts`
/// A `Vec` literal needs a push (§3.4 has no `vec!`).
pub fn cert_hyp1(h: EIdx) -> Vec<EIdx> {
    let mut hs: Vec<EIdx> = Vec::with_capacity(1);
    hs.push(h);
    hs
}

/// con-leche: none — the two-element hypothesis list `[h1, h2]` of `divModCertStmts`
/// As `cert_hyp1`.
pub fn cert_hyp2(h1: EIdx, h2: EIdx) -> Vec<EIdx> {
    let mut hs: Vec<EIdx> = Vec::with_capacity(2);
    hs.push(h1);
    hs.push(h2);
    hs
}

/// con-leche: none — the certificate list of `divModCertStmts`
/// One cons onto the statement list, as a function (§3.4 has no `vec!`).
pub fn cert_push(
    out: Vec<(Vec<EIdx>, EIdx)>,
    hyps: Vec<EIdx>,
    eq: EIdx,
) -> Vec<(Vec<EIdx>, EIdx)> {
    let mut out2 = out;
    out2.push((hyps, eq));
    out2
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// twin's `eqAt1 boolTy (← natAp2 bleN a b) r`, the guard shape all seven
/// branches are written with.
pub fn cert_guard(
    st: &mut AState,
    cx: &CertCtx,
    a: &EIdx,
    b: &EIdx,
    r: &EIdx,
) -> Result<EIdx, CheckError> {
    match nat_ap2(st, &cx.ble_n, a, b) {
        Err(e) => Err(e),
        Ok(g) => {
            let bt = cx.bool_ty.dup2();
            eq_at1(st, &bt, &g, r)
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// twin's `eqAt1 natTy (← natAp2 c x y) rhs`, the characteristic equation all
/// seven branches are written with.
pub fn cert_eq(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    rhs: &EIdx,
) -> Result<EIdx, CheckError> {
    let x = cx.x.dup2();
    let y = cx.y.dup2();
    match nat_ap2(st, c, &x, &y) {
        Err(e) => Err(e),
        Ok(lhs) => {
            let nt = cx.nat_ty.dup2();
            eq_at1(st, &nt, &lhs, rhs)
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// bitwise branches' `op2 (div2 x two) (div2 y two)`, written three times in
/// the twin.
pub fn cert_halves(st: &mut AState, cx: &CertCtx, c: &NIdx) -> Result<EIdx, CheckError> {
    let (x, y, two, dn) = (cx.x.dup2(), cx.y.dup2(), cx.two.dup2(), cx.div_n.dup2());
    match nat_ap2(st, &dn, &x, &two) {
        Err(e) => Err(e),
        Ok(hx) => match nat_ap2(st, &dn, &y, &two) {
            Err(e) => Err(e),
            Ok(hy) => nat_ap2(st, c, &hx, &hy),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// **the pinned characterization statements** of a pin-certified WF-recursive
/// op, in *open* form over `x := fvar 0`, `y := fvar 1` (the hypotheses become
/// `fvar 2, fvar 3`): per certificate, the list of hypothesis types and the
/// characteristic equation `Eq Nat lhs rhs`.  The guards are spelled with the
/// already-certified `Nat.ble` and the numeral `1` as `Nat.succ Nat.zero`.
pub fn div_mod_cert_stmts(
    st: &mut AState,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_ctx(st) {
        Err(e) => Err(e),
        Ok(cx) => div_mod_cert_stmts_at(st, &cx, c),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// seven-way branch, in the twin's order.
pub fn div_mod_cert_stmts_at(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    if c.eq2(&cx.gcd_n) {
        cert_gcd(st, cx, c)
    } else if c.eq2(&cx.sl_n) {
        cert_shift_left(st, cx, c)
    } else if c.eq2(&cx.sr_n) {
        cert_shift_right(st, cx, c)
    } else if c.eq2(&cx.land_n) {
        cert_land(st, cx, c)
    } else if c.eq2(&cx.lor_n) {
        cert_lor(st, cx, c)
    } else if c.eq2(&cx.xor_n) {
        cert_xor(st, cx, c)
    } else {
        cert_div_mod(st, cx, c)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`.
pub fn cert_gcd(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, mn) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.mod_n.dup2(),
    );
    match cert_guard(st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match nat_ap2(st, &mn, &y, &x) {
                Err(e) => Err(e),
                Ok(yx) => match nat_ap2(st, c, &yx, &x) {
                    Err(e) => Err(e),
                    Ok(r1) => match cert_eq(st, cx, c, &r1) {
                        Err(e) => Err(e),
                        Ok(e1) => match cert_eq(st, cx, c, &y) {
                            Err(e) => Err(e),
                            Ok(e2) => Ok(cert_push(
                                cert_push(Vec::new(), cert_hyp1(h1), e1),
                                cert_hyp1(h2),
                                e2,
                            )),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`.
pub fn cert_shift_left(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, mul, sub, two) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.mul_n.dup2(),
        cx.sub_n.dup2(),
        cx.two.dup2(),
    );
    match cert_guard(st, cx, &one, &y, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &y, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match nat_ap2(st, &mul, &two, &x) {
                Err(e) => Err(e),
                Ok(tx) => match nat_ap2(st, &sub, &y, &one) {
                    Err(e) => Err(e),
                    Ok(y1) => match nat_ap2(st, c, &tx, &y1) {
                        Err(e) => Err(e),
                        Ok(r1) => cert_two_eqs(st, cx, c, h1, h2, r1, x),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// `pure [([h1], e1), ([h2], e2)]` the six non-`div`/`mod` branches end with.
pub fn cert_two_eqs(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    h1: EIdx,
    h2: EIdx,
    r1: EIdx,
    r2: EIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_eq(st, cx, c, &r1) {
        Err(e) => Err(e),
        Ok(e1) => match cert_eq(st, cx, c, &r2) {
            Err(e) => Err(e),
            Ok(e2) => Ok(cert_push(
                cert_push(Vec::new(), cert_hyp1(h1), e1),
                cert_hyp1(h2),
                e2,
            )),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`.
pub fn cert_shift_right(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, div, sub, two) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.div_n.dup2(),
        cx.sub_n.dup2(),
        cx.two.dup2(),
    );
    match cert_guard(st, cx, &one, &y, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &y, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match nat_ap2(st, &sub, &y, &one) {
                Err(e) => Err(e),
                Ok(y1) => match nat_ap2(st, c, &x, &y1) {
                    Err(e) => Err(e),
                    Ok(inner) => match nat_ap2(st, &div, &inner, &two) {
                        Err(e) => Err(e),
                        Ok(r1) => cert_two_eqs(st, cx, c, h1, h2, r1, x),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`, `x = 0 → … = 0`.
pub fn cert_land(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, add, mul, mn, two, z) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.add_n.dup2(),
        cx.mul_n.dup2(),
        cx.mod_n.dup2(),
        cx.two.dup2(),
        cx.z.dup2(),
    );
    match cert_guard(st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match cert_halves(st, cx, c) {
                Err(e) => Err(e),
                Ok(rec1) => match nat_ap2(st, &mul, &two, &rec1) {
                    Err(e) => Err(e),
                    Ok(t2) => match nat_ap2(st, &mn, &x, &two) {
                        Err(e) => Err(e),
                        Ok(mx) => match nat_ap2(st, &mn, &y, &two) {
                            Err(e) => Err(e),
                            Ok(my) => match nat_ap2(st, &mul, &mx, &my) {
                                Err(e) => Err(e),
                                Ok(p) => match nat_ap2(st, &add, &t2, &p) {
                                    Err(e) => Err(e),
                                    Ok(r1) => cert_two_eqs(st, cx, c, h1, h2, r1, z),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
/// `x = 0 → x ||| y = y`.
pub fn cert_lor(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
    );
    match cert_guard(st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match cert_lor_rhs(st, cx, c) {
                Err(e) => Err(e),
                Ok(r1) => cert_two_eqs(st, cx, c, h1, h2, r1, y),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// `lor` branch's right-hand side.
pub fn cert_lor_rhs(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    let (x, y, add, mul, sub, mn, two) = (
        cx.x.dup2(),
        cx.y.dup2(),
        cx.add_n.dup2(),
        cx.mul_n.dup2(),
        cx.sub_n.dup2(),
        cx.mod_n.dup2(),
        cx.two.dup2(),
    );
    match cert_halves(st, cx, c) {
        Err(e) => Err(e),
        Ok(rec1) => match nat_ap2(st, &mul, &two, &rec1) {
            Err(e) => Err(e),
            Ok(t2) => match nat_ap2(st, &mn, &x, &two) {
                Err(e) => Err(e),
                Ok(mx) => match nat_ap2(st, &mn, &y, &two) {
                    Err(e) => Err(e),
                    Ok(my) => match nat_ap2(st, &add, &mx, &my) {
                        Err(e) => Err(e),
                        Ok(s) => match nat_ap2(st, &mul, &mx, &my) {
                            Err(e) => Err(e),
                            Ok(p) => match nat_ap2(st, &sub, &s, &p) {
                                Err(e) => Err(e),
                                Ok(d) => nat_ap2(st, &add, &t2, &d),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` —
/// `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
/// `x = 0 → x ^^^ y = y`.
pub fn cert_xor(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
    );
    match cert_guard(st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match cert_xor_rhs(st, cx, c) {
                Err(e) => Err(e),
                Ok(r1) => cert_two_eqs(st, cx, c, h1, h2, r1, y),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// `xor` branch's right-hand side.
pub fn cert_xor_rhs(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    let (x, y, add, mul, mn, two) = (
        cx.x.dup2(),
        cx.y.dup2(),
        cx.add_n.dup2(),
        cx.mul_n.dup2(),
        cx.mod_n.dup2(),
        cx.two.dup2(),
    );
    match cert_halves(st, cx, c) {
        Err(e) => Err(e),
        Ok(rec1) => match nat_ap2(st, &mul, &two, &rec1) {
            Err(e) => Err(e),
            Ok(t2) => match nat_ap2(st, &mn, &x, &two) {
                Err(e) => Err(e),
                Ok(mx) => match nat_ap2(st, &mn, &y, &two) {
                    Err(e) => Err(e),
                    Ok(my) => match nat_ap2(st, &add, &mx, &my) {
                        Err(e) => Err(e),
                        Ok(s) => match nat_ap2(st, &mn, &s, &two) {
                            Err(e) => Err(e),
                            Ok(m) => nat_ap2(st, &add, &t2, &m),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// twin's `else` branch, `Nat.div` and `Nat.mod`: three certificates, with
/// `recRhs`/`baseRhs` as the twin's two locals.
pub fn cert_div_mod(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_rec_rhs(st, cx, c) {
        Err(e) => Err(e),
        Ok(rec_rhs) => {
            let base_rhs: EIdx = if c.eq2(&cx.div_n) {
                cx.z.dup2()
            } else {
                cx.x.dup2()
            };
            cert_div_mod_guards(st, cx, c, rec_rhs, base_rhs)
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// twin's `recRhs`: `Nat.succ (c (x - y) y)` for `Nat.div`, `c (x - y) y` for
/// `Nat.mod`.
pub fn cert_rec_rhs(st: &mut AState, cx: &CertCtx, c: &NIdx) -> Result<EIdx, CheckError> {
    let (x, y, sub) = (cx.x.dup2(), cx.y.dup2(), cx.sub_n.dup2());
    match nat_ap2(st, &sub, &x, &y) {
        Err(e) => Err(e),
        Ok(d) => match nat_ap2(st, c, &d, &y) {
            Err(e) => Err(e),
            Ok(step) => {
                if c.eq2(&cx.div_n) {
                    match pin(st, &basis_names::nat_succ_name()) {
                        Err(e) => Err(e),
                        Ok(sn) => nat_ap1(st, &sn, &step),
                    }
                } else {
                    Ok(step)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// `div`/`mod` branch's four guards and three certificates.
pub fn cert_div_mod_guards(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    rec_rhs: EIdx,
    base_rhs: EIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
    );
    match cert_guard(st, cx, &y, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(st, cx, &one, &y, &bt) {
            Err(e) => Err(e),
            Ok(h2) => match cert_guard(st, cx, &y, &x, &bf) {
                Err(e) => Err(e),
                Ok(h3) => match cert_guard(st, cx, &one, &y, &bf) {
                    Err(e) => Err(e),
                    Ok(h4) => {
                        cert_div_mod_eqs(st, cx, c, h1, h2, h3, h4, rec_rhs, base_rhs)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-332 divModCertStmts` — the
/// twin's `pure [([h1, h2], e1), ([h3], e2), ([h4], e2)]`.
#[allow(clippy::too_many_arguments)]
pub fn cert_div_mod_eqs(
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    h1: EIdx,
    h2: EIdx,
    h3: EIdx,
    h4: EIdx,
    rec_rhs: EIdx,
    base_rhs: EIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_eq(st, cx, c, &rec_rhs) {
        Err(e) => Err(e),
        Ok(e1) => match cert_eq(st, cx, c, &base_rhs) {
            Err(e) => Err(e),
            Ok(e2) => {
                let out = cert_push(Vec::new(), cert_hyp2(h1, h2), e1);
                let out = cert_push(out, cert_hyp1(h3), e2.dup2());
                Ok(cert_push(out, cert_hyp1(h4), e2))
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The certificate checks (`DeclCheck.lean:334-537` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:224-237 divModCertApplied
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:338-352 divModCertApplied` —
/// the vendored proof applied to the statement's free variables (`x`, `y`,
/// then one `fvar` per hypothesis, carrying the hypothesis *type* as its
/// annotation — the checker's implicit local context).
pub fn div_mod_cert_applied(
    st: &mut AState,
    proof_s: &EIdx,
    hyps: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    match nat_var(st, 0) {
        Err(e) => Err(e),
        Ok(x) => match nat_var(st, 1) {
            Err(e) => Err(e),
            Ok(y) => match intern_e(st, ENodeView::App(proof_s.dup2(), x)) {
                Err(e) => Err(e),
                Ok(b1) => match intern_e(st, ENodeView::App(b1, y)) {
                    Err(e) => Err(e),
                    Ok(base) => div_mod_cert_applied_hyps(st, base, hyps),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:224-237 divModCertApplied
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:338-352 divModCertApplied` —
/// the twin's three-way `match hyps with | [h1] | [h1, h2] | _`.
pub fn div_mod_cert_applied_hyps(
    st: &mut AState,
    base: EIdx,
    hyps: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    if hyps.len() == 1 {
        match intern_e(st, ENodeView::FVar(2, hyps[0].dup2())) {
            Err(e) => Err(e),
            Ok(f2) => intern_e(st, ENodeView::App(base, f2)),
        }
    } else if hyps.len() == 2 {
        match intern_e(st, ENodeView::FVar(2, hyps[0].dup2())) {
            Err(e) => Err(e),
            Ok(f2) => match intern_e(st, ENodeView::App(base, f2)) {
                Err(e) => Err(e),
                Ok(a1) => match intern_e(st, ENodeView::FVar(3, hyps[1].dup2())) {
                    Err(e) => Err(e),
                    Ok(f3) => intern_e(st, ENodeView::App(a1, f3)),
                },
            },
        }
    } else {
        Ok(base)
    }
}

/// con-leche: none — `hyps.map (Expr.substConst0 c annVal)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:356-361 substConst0List` — an
/// explicit list recursion (§3.4 forbids the closure).
pub fn subst_const0_list(
    st: &mut AState,
    n: &NIdx,
    r: &EIdx,
    hs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= hs.len() {
        Ok(out)
    } else {
        match subst_const0(st, n, r, CORE_WALK_FUEL, &hs[i]) {
            Err(e) => Err(e),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                subst_const0_list(st, n, r, hs, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — `(hyps.map …).all (fun h => h.constsResolveF fe)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:365-368 constsResolveAll` — an
/// explicit list recursion.
pub fn consts_resolve_all(
    st: &mut AState,
    fe: &IFEnv,
    hs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= hs.len() {
        Ok(true)
    } else {
        match consts_resolve_f_fast(st, fe, &hs[i]) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    consts_resolve_all(st, fe, hs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:239-250 divModCertGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:321-330 divModCertGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:375-384 divModCertGuard` — the
/// syntactic guards of one certificate check: the substituted proof is closed,
/// level-monomorphic and resolving, and the substituted statement components
/// resolve.
pub fn div_mod_cert_guard(
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    hyps: &Vec<EIdx>,
    eq_e: &EIdx,
    proof: &EIdx,
) -> Result<bool, CheckError> {
    match subst_const_all(st, c, ann_val, CORE_WALK_FUEL, proof) {
        Err(e) => Err(e),
        Ok(p) => match ground_guards(st, fe, &p) {
            Err(e) => Err(e),
            Ok(g) => {
                if !g {
                    Ok(false)
                } else {
                    div_mod_cert_guard_rest(st, fe, c, ann_val, hyps, eq_e)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:239-250 divModCertGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:375-384 divModCertGuard` — the
/// two statement-component guards, past the proof's four.
pub fn div_mod_cert_guard_rest(
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    hyps: &Vec<EIdx>,
    eq_e: &EIdx,
) -> Result<bool, CheckError> {
    match subst_const0_list(st, c, ann_val, hyps, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(hs) => match consts_resolve_all(st, fe, &hs, 0) {
            Err(e) => Err(e),
            Ok(r) => {
                if !r {
                    Ok(false)
                } else {
                    match subst_const0(st, c, ann_val, CORE_WALK_FUEL, eq_e) {
                        Err(e) => Err(e),
                        Ok(q) => consts_resolve_f_fast(st, fe, &q),
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:391-405 divModEnvGuard` —
/// environment prerequisites of a certified `Nat.div`/`Nat.mod`: dependency
/// guard, pinned dependencies, the pinned `Eq` basis, and the `Bool`
/// constructors stored at the type `Bool` itself.
pub fn div_mod_env_guard(
    st: &mut AState,
    fe2: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match nat_op_guard(st, fe2, c) {
        Err(e) => Err(e),
        Ok(g) => {
            if !g {
                Ok(false)
            } else {
                match nat_op_deps(st, c) {
                    Err(e) => Err(e),
                    Ok(deps) => match nat_op_stored_ok_all(st, fe2, &deps, 0) {
                        Err(e) => Err(e),
                        Ok(d) => {
                            if !d {
                                Ok(false)
                            } else {
                                div_mod_env_guard_rest(st, fe2)
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:391-405 divModEnvGuard` — the
/// pinned `Eq` basis and the two `Bool` constructors.
pub fn div_mod_env_guard_rest(st: &mut AState, fe2: &IFEnv) -> Result<bool, CheckError> {
    match eq_basis_pinned(st, fe2) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                Ok(false)
            } else {
                match bool_true_name(st) {
                    Err(e) => Err(e),
                    Ok(btn) => match bool_ctor_typed(st, fe2, &btn) {
                        Err(e) => Err(e),
                        Ok(t) => {
                            if !t {
                                Ok(false)
                            } else {
                                match bool_false_name(st) {
                                    Err(e) => Err(e),
                                    Ok(bfn) => bool_ctor_typed(st, fe2, &bfn),
                                }
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:391-405 divModEnvGuard` — the
/// twin's `(← ci.toConstantVal).type != boolTy`, which it spells twice: the
/// guards' `true`/`false` must inhabit the `Bool` value semantically.
pub fn bool_ctor_typed(
    st: &mut AState,
    fe2: &IFEnv,
    n: &NIdx,
) -> Result<bool, CheckError> {
    match ifenv_find(fe2, n) {
        Some(ci) => {
            let c = i_constant_info_dup(ci);
            match i_constant_info_to_constant_val(&mut st.store, &c) {
                Err(e) => Err(e),
                Ok(cv) => match bool_name(st) {
                    Err(e) => Err(e),
                    Ok(bn) => match const_e(st, &bn) {
                        Err(e) => Err(e),
                        Ok(bool_ty) => Ok(cv.ty.eq2(&bool_ty)),
                    },
                },
            }
        }
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:332-336 divModPinGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:411-416 divModPinGuard` —
/// syntactic guards on one variant's pin (generated; checked once at install
/// rather than proven about the blob).
pub fn div_mod_pin_guard(
    st: &mut AState,
    ps: &INatOpPinSet,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match div_mod_decl_pin(st, ps, c) {
        Err(e) => Err(e),
        Ok(p) => ground_guards(st, fe, &p),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:423-430 divModCertsGuardGo` —
/// all of one variant's certificates' syntactic guards at once, `zip`ped with
/// the statements.  A `zip` stops at the shorter list, which is why the bound
/// is the minimum (the twin's two `[]` clauses are both `true`).
pub fn div_mod_certs_guard_go(
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= stmts.len() || i >= proofs.len() {
        Ok(true)
    } else {
        match div_mod_cert_guard(
            st,
            fe,
            c,
            ann_val,
            &stmts[i].0,
            &stmts[i].1,
            &proofs[i],
        ) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    div_mod_certs_guard_go(st, fe, c, ann_val, stmts, proofs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:436-438 divModCertsGuard` —
/// the statements and the variant's proofs, zipped.
pub fn div_mod_certs_guard(
    st: &mut AState,
    ps: &INatOpPinSet,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
) -> Result<bool, CheckError> {
    match div_mod_cert_stmts(st, c) {
        Err(e) => Err(e),
        Ok(stmts) => match div_mod_cert_proofs(st, ps, c) {
            Err(e) => Err(e),
            Ok(proofs) => div_mod_certs_guard_go(st, fe, c, ann_val, &stmts, &proofs, 0),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts
/// con-leche: ConLeche/Kernel/DeclCheck.lean:861-875 checkDivModCertsF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:447-461 checkDivModCerts` —
/// check the pinned certificates of op `c`: per certificate, the vendored
/// proof (with the op's self-references replaced by the stored annotated value
/// — the checks run in the *pre-insertion* environment) is applied to free
/// variables typed by the pinned open statement, its type inferred, and
/// compared against the pinned characteristic equation.  The twin's
/// two-`List` recursion is one index recursion; its `_, _ => pure false` is
/// the length mismatch.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_certs(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= stmts.len() && i >= proofs.len() {
        Ok(true)
    } else if i >= stmts.len() || i >= proofs.len() {
        Ok(false)
    } else {
        match div_mod_cert_guard(st, fe, c, ann_val, &stmts[i].0, &stmts[i].1, &proofs[i]) {
            Err(e) => Err(e),
            Ok(g) => {
                if !g {
                    Ok(false)
                } else {
                    check_div_mod_cert_at(st, mode, fe, c, ann_val, stmts, proofs, i)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:447-461 checkDivModCerts` —
/// one certificate, past its guard: the substituted proof applied, annotated,
/// inferred and compared.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_cert_at(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    match subst_const_all(st, c, ann_val, CORE_WALK_FUEL, &proofs[i]) {
        Err(e) => Err(e),
        Ok(p) => match subst_const0_list(st, c, ann_val, &stmts[i].0, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(hs) => match div_mod_cert_applied(st, &p, &hs) {
                Err(e) => Err(e),
                Ok(applied) => match annotate_core(st, mode, fe, CHECK_FUEL, 4, &applied) {
                    Err(e) => Err(e),
                    Ok(applied_a) => {
                        check_div_mod_cert_tail(st, mode, fe, c, ann_val, stmts, proofs, i, applied_a)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:447-461 checkDivModCerts` —
/// the inference and the comparison, then the next certificate.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_cert_tail(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
    applied_a: EIdx,
) -> Result<bool, CheckError> {
    match infer_type_core(st, mode, fe, CHECK_FUEL, 4, &applied_a) {
        Err(e) => Err(e),
        Ok(tp) => match subst_const0(st, c, ann_val, CORE_WALK_FUEL, &stmts[i].1) {
            Err(e) => Err(e),
            Ok(rhs) => match is_def_eq_core(st, mode, fe, CHECK_FUEL, 4, &tp, &rhs) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        check_div_mod_certs(st, mode, fe, c, ann_val, stmts, proofs, i + 1)
                    } else {
                        Ok(false)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt
/// con-leche: ConLeche/Kernel/DeclCheck.lean:877-885 checkDivModPinAtF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:470-477 checkDivModPinAt` —
/// **one pin variant's attempt**: the stored value against the variant's pin by
/// definitional equality, and on a match the variant's certificates.  `true` =
/// matched; `false` = the pin is not definitionally equal, or a certificate did
/// not check.  The third outcome is an error thrown from inside, which
/// `or_else_attempt` turns into "this variant does not match".
pub fn check_div_mod_pin_at(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    ps: &INatOpPinSet,
) -> Result<bool, CheckError> {
    match div_mod_decl_pin(st, ps, c) {
        Err(e) => Err(e),
        Ok(p) => match annotate_core(st, mode, fe, CHECK_FUEL, 0, &p) {
            Err(e) => Err(e),
            Ok(pin_a) => match is_def_eq_core(st, mode, fe, CHECK_FUEL, 0, value2, &pin_a) {
                Err(e) => Err(e),
                Ok(ok_pin) => {
                    if ok_pin {
                        check_div_mod_pin_certs(st, mode, fe, c, value2, ps)
                    } else {
                        Ok(false)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:470-477 checkDivModPinAt` —
/// the certificates, past the pin comparison.
pub fn check_div_mod_pin_certs(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    ps: &INatOpPinSet,
) -> Result<bool, CheckError> {
    match div_mod_cert_stmts(st, c) {
        Err(e) => Err(e),
        Ok(stmts) => match div_mod_cert_proofs(st, ps, c) {
            Err(e) => Err(e),
            Ok(proofs) => {
                check_div_mod_certs(st, mode, fe, c, value2, &stmts, &proofs, 0)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:330-336 divModAttemptReason
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:483-486 divModAttemptReason` —
/// what a variant failed on, for the decline message.  The twin renders
/// `{toolchain}: {repr e}`; the port drops the interpolation (§3.1) and keeps
/// the RECOVERED ERROR's own message, which is
/// `con_ron_core::kernel::checker::check_div_mod_pin_loop`'s `tried`
/// accumulator exactly.
pub fn div_mod_attempt_reason(e: CheckError) -> Vec<u32> {
    core_types::message(e)
}

/// con-leche: ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop
/// con-leche: ConLeche/Kernel/DeclCheck.lean:887-901 checkDivModPinLoopF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:501-521 checkDivModPinLoop` —
/// **the variant loop**: the first variant whose guards pass and whose attempt
/// succeeds enables the fast path; every other outcome moves on to the next
/// variant, and when none is left the stream DECLINES.
///
/// This is (C)'s one variant-fallback point.  con-leche's
/// `ops.orElse … fun r => …` passes a continuation, which §3.4 forbids; the
/// continuation is this loop's own tail call, and the decision is
/// `or_else_attempt`'s four-way step — `Recovered` resumes at the PRE-attempt
/// state, which is `astate_dup`'s snapshot here (the twin gets it free from
/// its state function), and `Failed` (a `Native` error only) is the verdict.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_pin_loop(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    variants: &Vec<INatOpPinSet>,
    i: usize,
    tried: Vec<u32>,
) -> Result<(), CheckError> {
    if i >= variants.len() {
        fail(CheckError::NotImplemented(tried))
    } else {
        match div_mod_pin_guard(st, &variants[i], fe, c) {
            Err(e) => Err(e),
            Ok(g1) => match div_mod_certs_guard(st, &variants[i], fe, c, value2) {
                Err(e) => Err(e),
                Ok(g2) => {
                    if g1 && g2 {
                        check_div_mod_pin_try(st, mode, fe, c, value2, variants, i, tried)
                    } else {
                        check_div_mod_pin_loop(
                            st, mode, fe, c, value2, variants, i + 1, tried,
                        )
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:501-521 checkDivModPinLoop` —
/// one variant's attempt and the four-way step it decides.  The snapshot is
/// taken only here, where the twin's `orElseAttempt` has the pre-attempt state
/// in hand for free (`arena::checker_base`'s module note 6).
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_pin_try(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    variants: &Vec<INatOpPinSet>,
    i: usize,
    tried: Vec<u32>,
) -> Result<(), CheckError> {
    let snapshot: AState = astate_dup(st);
    let attempt: Result<bool, CheckError> =
        check_div_mod_pin_at(st, mode, fe, c, value2, &variants[i]);
    match or_else_attempt(attempt) {
        OrElseStep::Matched => Ok(()),
        OrElseStep::Continued => {
            check_div_mod_pin_loop(st, mode, fe, c, value2, variants, i + 1, tried)
        }
        OrElseStep::Recovered(e) => {
            *st = snapshot;
            check_div_mod_pin_loop(
                st,
                mode,
                fe,
                c,
                value2,
                variants,
                i + 1,
                div_mod_attempt_reason(e),
            )
        }
        OrElseStep::Failed(e) => Err(e),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:362-388 checkDivModPin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:903-913 checkDivModPinF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:529-537 checkDivModPin` — the
/// pin-certified operations' install gate, run after the ordinary definition
/// check (`fe2` is the already-extended environment, `fe` the pre-insertion one
/// all checks run in).  The variant list is its parameter (con-leche's task
/// #304).
///
/// Deviation: the twin's two environments are ONE index at two visibility
/// bounds here, taken by value at the extended bound and handed back there —
/// `con_ron_core::kernel::checker::check_div_mod_pin`'s own arrangement, and
/// the reason is the same: `IFEnv` has no cheap copy.
pub fn check_div_mod_pin(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe2: IFEnv,
    k_pre: u64,
    c: &NIdx,
) -> Result<IFEnv, CheckError> {
    match div_mod_env_guard(st, &fe2, c) {
        Err(e) => Err(e),
        Ok(g) => {
            if !g {
                fail(CheckError::NotImplemented(code_points(&M_DIVMOD_ENV)))
            } else {
                match defn_value(&fe2, c) {
                    None => fail(CheckError::Internal(code_points(&M_DIVMOD_NOT_STORED))),
                    Some(value2) => {
                        check_div_mod_pin_at_pre(st, mode, pins, fe2, k_pre, c, value2)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:362-388 checkDivModPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:529-537 checkDivModPin` — the
/// loop at the PRE-insertion view, and the index handed back at the bound it
/// came in at.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_pin_at_pre(
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe2: IFEnv,
    k_pre: u64,
    c: &NIdx,
    value2: EIdx,
) -> Result<IFEnv, CheckError> {
    let k2: u64 = fe2.visible_below;
    let fe_pre: IFEnv = crate::arena::env::ifenv_restrict_to(fe2, k_pre);
    let r: Result<(), CheckError> = check_div_mod_pin_loop(
        st,
        mode,
        &fe_pre,
        c,
        &value2,
        pins,
        0,
        code_points(&M_DIVMOD_NO_VARIANT),
    );
    match r {
        Err(e) => Err(e),
        Ok(()) => Ok(crate::arena::env::ifenv_restrict_to(fe_pre, k2)),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:362-388 checkDivModPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:529-537 checkDivModPin` — the
/// twin's `match fe2.find? c with | some (.defnInfo _ value' _)`: the stored
/// definition's value, COPIED before the state is taken mutably (task #14's
/// rule).
pub fn defn_value(fe: &IFEnv, c: &NIdx) -> Option<EIdx> {
    match ifenv_find(fe, c) {
        Some(IConstantInfo::DefnInfo(_, v, _)) => Some(v.dup2()),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:390-425 checkReducePin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:915-934 checkReducePinF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:545-564 checkReducePin` — the
/// `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the ordinary
/// opaque check: the stored constant carries the pinned type, the witness value
/// is definitionally equal to the build-time pin, and the *identity
/// certificate* `value x ≡ x` over an opened `fvar` at the element type holds.
///
/// Deviation: as `check_div_mod_pin`, the two environments are one index at two
/// visibility bounds.
pub fn check_reduce_pin(
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    k_pre: u64,
    c: &NIdx,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match reduce_stored_ok(st, &fe2, c) {
        Err(e) => Err(e),
        Ok(s) => {
            if !s {
                fail(CheckError::NotImplemented(code_points(&M_REDUCE_DECL)))
            } else {
                let k2: u64 = fe2.visible_below;
                let fe_pre: IFEnv = crate::arena::env::ifenv_restrict_to(fe2, k_pre);
                let r: Result<(), CheckError> =
                    check_reduce_pin_pre(st, mode, &fe_pre, c, value);
                match r {
                    Err(e) => Err(e),
                    Ok(()) => Ok(crate::arena::env::ifenv_restrict_to(fe_pre, k2)),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:390-425 checkReducePin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:545-564 checkReducePin` — the
/// body at the pre-insertion view: the element guard, the pin's own syntactic
/// guards, the definitional comparison of the witness against the pin, and the
/// identity certificate.
pub fn check_reduce_pin_pre(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value: &EIdx,
) -> Result<(), CheckError> {
    match reduce_elem_ok(st, fe, c) {
        Err(e) => Err(e),
        Ok(el) => {
            if !el {
                fail(CheckError::NotImplemented(code_points(&M_REDUCE_DECL)))
            } else {
                match reduce_pin_guard(st, fe, c) {
                    Err(e) => Err(e),
                    Ok(g) => {
                        if !g {
                            fail(CheckError::NotImplemented(code_points(
                                &M_REDUCE_PIN_ABSENT,
                            )))
                        } else {
                            check_reduce_pin_value(st, mode, fe, c, value)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:390-425 checkReducePin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:545-564 checkReducePin` — the
/// witness and the pin, annotated and compared.
pub fn check_reduce_pin_value(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value: &EIdx,
) -> Result<(), CheckError> {
    match annotate_core(st, mode, fe, CHECK_FUEL, 0, value) {
        Err(e) => Err(e),
        Ok(val_a) => match reduce_decl_pin(st, c) {
            Err(e) => Err(e),
            Ok(p) => match annotate_core(st, mode, fe, CHECK_FUEL, 0, &p) {
                Err(e) => Err(e),
                Ok(pin_a) => {
                    match is_def_eq_core(st, mode, fe, CHECK_FUEL, 0, &val_a, &pin_a) {
                        Err(e) => Err(e),
                        Ok(ok_pin) => {
                            if ok_pin {
                                check_reduce_identity(st, mode, fe, c, &val_a)
                            } else {
                                fail(CheckError::NotImplemented(code_points(
                                    &M_REDUCE_SPELLING,
                                )))
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:390-425 checkReducePin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:545-564 checkReducePin` — the
/// identity certificate: `valA x ≡ x` at depth 1 over `reduceCertVar`.
pub fn check_reduce_identity(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    val_a: &EIdx,
) -> Result<(), CheckError> {
    match reduce_cert_var(st, c) {
        Err(e) => Err(e),
        Ok(x) => match intern_e(st, ENodeView::App(val_a.dup2(), x.dup2())) {
            Err(e) => Err(e),
            Ok(ax) => match is_def_eq_core(st, mode, fe, CHECK_FUEL, 1, &ax, &x) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(())
                    } else {
                        fail(CheckError::Internal(code_points(&M_REDUCE_NOT_ID)))
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The structural-`Nat` recurrence certification (`DeclCheck.lean:566-587`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:108-116 certifyNatEqs
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:571-577 certifyNatEqs` —
/// certify a list of recurrence equations by definitional equality (at depth 2:
/// the equations' variables are `fvar 0`/`fvar 1`).
pub fn certify_nat_eqs(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    eqs: &Vec<(EIdx, EIdx)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= eqs.len() {
        Ok(true)
    } else {
        match is_def_eq_core(st, mode, fe, CHECK_FUEL, 2, &eqs[i].0, &eqs[i].1) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    certify_nat_eqs(st, mode, fe, eqs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: none — `(natOpEquations 0 c).map fun eq => (substConst0 …, substConst0 …)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:581-587 substConst0Pairs` — an
/// explicit list recursion.
pub fn subst_const0_pairs(
    st: &mut AState,
    n: &NIdx,
    r: &EIdx,
    eqs: &Vec<(EIdx, EIdx)>,
    i: usize,
    out: Vec<(EIdx, EIdx)>,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    if i >= eqs.len() {
        Ok(out)
    } else {
        match subst_const0(st, n, r, CORE_WALK_FUEL, &eqs[i].0) {
            Err(e) => Err(e),
            Ok(a) => match subst_const0(st, n, r, CORE_WALK_FUEL, &eqs[i].1) {
                Err(e) => Err(e),
                Ok(b) => {
                    let mut out2 = out;
                    out2.push((a, b));
                    subst_const0_pairs(st, n, r, eqs, i + 1, out2)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The three value kinds' full checks (`DeclCheck.lean:589-648`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:838-853 checkDefnValF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:596-602 checkDefnVal` — check
/// a `def` declaration's value against its checked constant, returning the
/// pushed index.  The reducibility hint is stored untouched: it steers only the
/// lazy delta unfolding order, never a verdict.
pub fn check_defn_val(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<IFEnv, CheckError> {
    match install_value(st, mode, &fe, cv, value) {
        Err(e) => Err(e),
        Ok(value_a) => match infer_type_core(st, mode, &fe, CHECK_FUEL, 0, &value_a) {
            Err(e) => Err(e),
            Ok(vtype) => {
                match is_def_eq_core(st, mode, &fe, CHECK_FUEL, 0, &vtype, &cv.ty) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        if ok {
                            Ok(ifenv_push(
                                fe,
                                IConstantInfo::DefnInfo(
                                    crate::arena::env::i_constant_val_dup(cv),
                                    value_a,
                                    con_ron_core::kernel::env::reducibility_hint_dup(hint),
                                ),
                            ))
                        } else {
                            fail(CheckError::Invalid(code_points(&M_TYPE_MISMATCH_DEFN)))
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:609-620 checkThmVal` — check a
/// `theorem` declaration's value against its checked constant (whose type must
/// additionally be a proposition).  **A theorem is stored by its statement**:
/// the constant keeps the record's own (raw) value as an unread datum, and the
/// annotated value is a realizability witness, checked and then discarded.
pub fn check_thm_val(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match infer_type_core(st, mode, &fe, CHECK_FUEL, 0, &cv.ty) {
        Err(e) => Err(e),
        Ok(stype) => match ensure_sort_core(st, mode, &fe, CHECK_FUEL, 0, &stype) {
            Err(e) => Err(e),
            Ok(u) => match zero_level(st) {
                Err(e) => Err(e),
                Ok(z) => match lvl_eq(st, &u, &z) {
                    Err(e) => Err(e),
                    Ok(o) => match lift_fueled(o) {
                        Err(e) => Err(e),
                        Ok(is_prop) => {
                            if is_prop {
                                check_thm_val_witness(st, mode, fe, cv, value)
                            } else {
                                fail(CheckError::Invalid(code_points(&M_THM_NOT_PROP)))
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:609-620 checkThmVal` — the
/// witness half: the value's guards and annotation, its inferred type against
/// the statement, and the push of `.thmInfo cv value` — the **raw** value, as
/// the twin's clause stores it.
pub fn check_thm_val_witness(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match install_value(st, mode, &fe, cv, value) {
        Err(e) => Err(e),
        Ok(jv) => match infer_type_core(st, mode, &fe, CHECK_FUEL, 0, &jv) {
            Err(e) => Err(e),
            Ok(vtype) => {
                match is_def_eq_core(st, mode, &fe, CHECK_FUEL, 0, &vtype, &cv.ty) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        if ok {
                            Ok(ifenv_push(
                                fe,
                                IConstantInfo::ThmInfo(
                                    crate::arena::env::i_constant_val_dup(cv),
                                    value.dup2(),
                                ),
                            ))
                        } else {
                            fail(CheckError::Invalid(code_points(&M_TYPE_MISMATCH_THM)))
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:627-633 checkOpaqueVal` —
/// check an `opaque` declaration's value against its checked constant: exactly
/// the theorem check without the is-a-proposition requirement.  The result is
/// stored as an `axiomInfo` — the checked value is a realizability witness,
/// consumed by the model extension and then discarded.
pub fn check_opaque_val(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IFEnv, CheckError> {
    match install_value(st, mode, &fe, cv, value) {
        Err(e) => Err(e),
        Ok(value_a) => match infer_type_core(st, mode, &fe, CHECK_FUEL, 0, &value_a) {
            Err(e) => Err(e),
            Ok(vtype) => {
                match is_def_eq_core(st, mode, &fe, CHECK_FUEL, 0, &vtype, &cv.ty) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        if ok {
                            Ok(ifenv_push(
                                fe,
                                IConstantInfo::AxiomInfo(
                                    crate::arena::env::i_constant_val_dup(cv),
                                ),
                            ))
                        } else {
                            fail(CheckError::Invalid(code_points(
                                &M_TYPE_MISMATCH_OPAQUE,
                            )))
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:26-30 installBasisDecl
/// con-leche: ConLeche/Kernel/DeclCheck.lean:855-859 installBasisDeclF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:639-642 installBasisDecl` —
/// install one pinned basis declaration (duplicate-checked), returning the
/// pushed index.
pub fn install_basis_decl(
    fe: IFEnv,
    ci: IConstantInfo,
) -> Result<IFEnv, CheckError> {
    if ifenv_find(&fe, &crate::arena::env::i_constant_info_name(&ci)).is_some() {
        fail(CheckError::Invalid(code_points(&M_DUP_DECL)))
    } else {
        Ok(ifenv_push(fe, ci))
    }
}

/// con-leche: none — `kind.declsA.foldlM installBasisDecl`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:646-648 installBasisDecls` —
/// an explicit list recursion (§3.4), threading the index by value.
pub fn install_basis_decls(
    fe: IFEnv,
    decls: &Vec<IConstantInfo>,
    i: usize,
) -> Result<IFEnv, CheckError> {
    if i >= decls.len() {
        Ok(fe)
    } else {
        match install_basis_decl(fe, i_constant_info_dup(&decls[i])) {
            Err(e) => Err(e),
            Ok(fe2) => install_basis_decls(fe2, decls, i + 1),
        }
    }
}
