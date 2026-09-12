//! `ConLeche/Cached/ParsedC.lean` — **the parsed-declaration checker**: one
//! `DeclC` straight from the direct parse, checked as it is installed, with
//! the syntactic passes memoised on the `ExprC` DAG
//! (`crate::cached::expr_ops_c`) and the core entry points taken from the
//! cached knot.  Plus the two records that cross the install/check seam,
//! `ValueGroup` (`ConLeche/Kernel/CheckerSplit.lean`) and `PendingCheck`
//! (`ConLeche/Cached/Installed.lean`).
//!
//! ## What this file is, against `kernel::checker`
//!
//! `checkDeclC` mirrors `Kernel/Checker.lean`'s `checkDecl` branch by branch,
//! and the differences are exactly three:
//!
//! 1. **The syntactic guards are the cached ones.**  `ExprC.looseBVarsBounded`,
//!    `ExprC.hasFvar`, `ExprC.allLevelParamsDefined` and `constsResolveFC`
//!    replace `Expr.looseBVarsBounded`, `Expr.hasFvar`,
//!    `Expr.allLevelParamsDefined` and `Expr.constsResolveF`.  The first three
//!    are `cached::expr_ops_c`'s, the fourth `cached::state_c`'s.
//! 2. **Every accepted constant is recorded in `ienv`.**  `recordCConst` runs
//!    between the resolution guard and the inference (definitions, theorems,
//!    opaques) resp. before each axiom install, tagged with the very `Expr`
//!    objects pushed into the index — that entry is what the cached lazy
//!    accessors (`constTyAtM`, `constValAtM`) read.
//! 3. **The pinned-name tests come before the push.**  `checkDeclC`'s `defn`
//!    and `opaque` arms branch first and hand `fe` to `push` unshared, which
//!    is con-leche's own RC-linearity rule; the port threads the index by
//!    value (task #14), so the same branch is what keeps the common arm a
//!    single tail call.
//!
//! Everything else is shared: the pin gates (`checker::check_defn_pins`,
//! `check_reduce_pin`), the axiom pins (`std_axioms`, `trust_axioms`) and the
//! basis install (`checker::check_basis_decl`) are the `FEnv`-indexed twins
//! the port already spells once (task #18's deviation 3), and `sharedOpsC`'s
//! five core slots are `kernel::type_checker`'s (task #24's collapse 1).
//!
//! Every memo policy the cached lane prescribes is therefore the cited one:
//! `state_c::consts_resolve_fc` (task #23) probes *before* the match and so
//! records the four atom kinds too, which the `Expr`-level
//! `decl_check::consts_resolve_f_fast` does not — that difference was the one
//! deviation this module carried while task #23 was in flight, and calling
//! `constsResolveFC` by name is what retired it.
//!
//! **Nothing here is a placeholder.**  `checkDeclC`'s `.indDecl` arm
//! dispatches to task #25's two install routes (`check_ind_decl_c`).
//!
//! `DeclC` is `Declaration` with the *value* constructors' payloads at
//! `ExprC`, which is `Expr` (task #10, surprise 1), and **without**
//! `Declaration`'s `deriving DecidableEq, Repr, Inhabited` — con-leche
//! derives nothing on `DeclC`, deliberately (task #10's note on the
//! round-trip comparison).  Its `indDecl` carries *installed*
//! `ConstantInfo`s, so a parsed declaration transitively contains `IndCaps`,
//! `RecRule` (with `RecRuleFire`) and `ProjTable`, whose install-computed
//! fields are at their parse placeholders (task #10, surprise 2;
//! `env::rec_rule_parsed`, `env::ind_caps_default`).

use crate::cached::expr_ops_c;
use crate::cached::state_c;
use crate::cached::state_c::CState;
use crate::cached::state_c::CheckCM;
use crate::kernel::basis_names;
use crate::kernel::checker;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::env;
use crate::kernel::env::BasisKind;
use crate::kernel::env::CheckMode;
use crate::kernel::env::ConstantInfo;
use crate::kernel::env::ConstantVal;
use crate::kernel::env::ReducibilityHint;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::inductives::inductives_c;
use crate::kernel::inductives::native_parts;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::std_axioms;
use crate::kernel::trust_axioms;
use crate::kernel::type_checker;
use std::vec::Vec;

/// con-leche: ConLeche/Cached/ParsedC.lean:55-61 DeclC
/// A parsed declaration over `ExprC`.  Its constant-value records *are*
/// `ConLeche.ConstantVal` (con-leche task #198: the separate `ConstantValC`
/// is gone), so the header's type is an ordinary `Expr` — which is the same
/// type as the value payloads here, `ExprC` being `Expr`.
pub enum DeclC {
    AxiomDecl(ConstantVal),
    DefnDecl(ConstantVal, Expr, ReducibilityHint),
    ThmDecl(ConstantVal, Expr),
    OpaqueDecl(ConstantVal, Expr),
    BasisDecl(BasisKind),
    IndDecl(Vec<ConstantInfo>, u64),
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:38-42 ValueKind
/// The three declaration kinds whose value check is separable from their
/// install.  `ValueKind.word` (`:45-48`) is not ported: it renders the
/// kind into a type-mismatch message, and §3.1 says message strings need not
/// match.
pub enum ValueKind {
    Defn,
    Thm,
    Opaque,
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:38-42 ValueKind
/// The copy.
pub fn value_kind_dup(k: &ValueKind) -> ValueKind {
    match k {
        ValueKind::Defn => ValueKind::Defn,
        ValueKind::Thm => ValueKind::Thm,
        ValueKind::Opaque => ValueKind::Opaque,
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:56-59 ValueGroup
/// What the install half hands the check half: the kind, the header with its
/// type annotated, and the value — **annotated** for a definition or an
/// opaque (the install half annotated it and stored it), **raw** for a
/// theorem (the install half never looked at it: a theorem is stored by its
/// statement, and the check half annotates the value itself).
pub struct ValueGroup {
    pub kind: ValueKind,
    pub cv_a: ConstantVal,
    pub jv: Expr,
}

/// con-leche: ConLeche/Cached/Installed.lean:74-77 PendingCheck
/// A phase-A record awaiting its phase-B check: the datum that crosses the
/// install/check seam, the fold position of the declaration (its error tag)
/// and the environment counter at the install — `fe.visibleBelow` before the
/// push, i.e. the number of constants installed before it, which phase B
/// feeds to `fenv::restrict_to`.
///
/// Deviation: the two `Nat`s are `u64` (§3.3).
pub struct PendingCheck {
    pub vg: ValueGroup,
    pub pos: u64,
    pub vis: u64,
}

// ---------------------------------------------------------------------------
// The parsed-declaration checker (`ParsedC.lean:63-241`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ParsedC.lean:67-69 opSIxC
/// Parsed `ensureSort` (no per-call conversion): `ensureSortI` over the
/// cached knot at `checkFuel`, which is `type_checker::ensure_sort_core` —
/// the one place the knot is named (task #24's collapse 1).
pub fn op_s_ix_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    i: &Expr,
) -> CheckCM<Level> {
    type_checker::ensure_sort_core(mode, st, fe, d, i)
}

/// con-leche: ConLeche/Cached/ParsedC.lean:71-96 checkConstantValC
/// `checkConstantVal` on a *parsed* declaration: the checks of
/// `checkConstantValF` with the syntactic passes memoised on the `ExprC` DAG
/// and the operations on `ExprC` values.  Returns the constant with its type
/// **annotated**, together with that annotated type — the cited
/// `(⟨cv.name, cv.levelParams, tyE⟩, jty)` at `tyE := jty`, i.e. both
/// components hold the same node.
///
/// The difference from `checker_base::check_constant_val` is exactly the
/// memo policy: `ExprC.looseBVarsBounded`, `ExprC.hasFvar` and
/// `ExprC.allLevelParamsDefined` are `cached::expr_ops_c`'s, and
/// `constsResolveFC` is the cached walk (deviation below).  That is why this
/// is a second function and not a second citation on the `Expr`-level one.
pub fn check_constant_val_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
) -> CheckCM<(ConstantVal, Expr)> {
    if fenv::find(fe, &cv.name).is_some() {
        Err(core_types::invalid({ const M: [u32; 21] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if name::contains(&basis_names::reserved_basis_names(), &cv.name) {
        Err(core_types::invalid({ const M: [u32; 19] = [114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
    } else if level::name_is_proj_fn_shape(&cv.name) {
        Err(core_types::invalid({ const M: [u32; 24] = [114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
    } else if !level::name_nodup(&cv.level_params) {
        Err(core_types::invalid({ const M: [u32; 44] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if !expr_ops_c::loose_bvars_bounded(0, &cv.ty) {
        Err(core_types::invalid({ const M: [u32; 28] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else if expr_ops_c::has_fvar(&cv.ty) {
        Err(core_types::invalid({ const M: [u32; 32] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, fe, 0, &cv.ty) {
            Err(err) => Err(err),
            Ok(jty) => check_constant_val_c_after_annot(mode, st, fe, cv, jty),
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:71-96 checkConstantValC
/// The tail past the annotation: the level-parameter and resolution guards on
/// the annotated type, the type's own sort through `opSIxC`, and the record
/// update.  Split off so the annotation's state-threading call is a tail call
/// and the guard groups do not join on a borrowed state (task #24's
/// deviation 7).
pub fn check_constant_val_c_after_annot(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
    jty: Expr,
) -> CheckCM<(ConstantVal, Expr)> {
    if !expr_ops_c::all_level_params_defined(&cv.level_params, &jty) {
        Err(core_types::invalid({ const M: [u32; 37] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else if !state_c::consts_resolve_fc(fe, &jty) {
        Err(core_types::invalid({ const M: [u32; 24] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::infer_type_core(mode, st, fe, 0, &jty) {
            Err(err) => Err(err),
            Ok(jsty) => match op_s_ix_c(mode, st, fe, 0, &jsty) {
                Err(err) => Err(err),
                Ok(_u) => {
                    let cv_a: ConstantVal = ConstantVal {
                        name: name::dup(&cv.name),
                        level_params: prop_when::names_copy(&cv.level_params),
                        ty: expr::dup(&jty),
                    };
                    Ok((cv_a, jty))
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:98-115 checkDefnValC
/// `checkDefnValP` over `ExprC`: the value's syntactic guards, its
/// annotation, the `ienv` record, and the comparison of its inferred type
/// against the declared one, returning the pushed index.
pub fn check_defn_val_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    value: &Expr,
    hint: &ReducibilityHint,
) -> CheckCM<FEnv> {
    if !expr_ops_c::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops_c::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, &fe, 0, value) {
            Err(err) => Err(err),
            Ok(jv) => check_defn_val_c_after_annot(mode, st, fe, cv_a, jty, jv, hint),
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:98-115 checkDefnValC
/// The tail past the annotation.  `recordCConst` runs **between** the
/// resolution guard and the inference, as the cited code has it: the `ienv`
/// entry is what the cached lazy accessors (`constTyAtM`, `constValAtM`)
/// read, and it is tagged with the very `Expr` objects that are about to be
/// pushed (`vE := jv`, so both components of the value pair are that node).
pub fn check_defn_val_c_after_annot(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    jv: Expr,
    hint: &ReducibilityHint,
) -> CheckCM<FEnv> {
    if !expr_ops_c::all_level_params_defined(&cv_a.level_params, &jv) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !state_c::consts_resolve_fc(&fe, &jv) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        state_c::record_c_const(
            st,
            name::dup(&cv_a.name),
            expr::dup(&cv_a.ty),
            expr::dup(jty),
            Some((expr::dup(&jv), expr::dup(&jv))),
        );
        match type_checker::infer_type_core(mode, st, &fe, 0, &jv) {
            Err(err) => Err(err),
            Ok(jvt) => match type_checker::is_def_eq_core(mode, st, &fe, 0, &jvt, jty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::push(
                            fe,
                            ConstantInfo::DefnInfo(
                                env::constant_val_dup(cv_a),
                                jv,
                                env::reducibility_hint_dup(hint),
                            ),
                        ))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 27] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:117-138 checkThmValC
/// `checkThmValP` over `ExprC`: the statement must be a proposition first.
/// Deviation: the cited `liftFueled "level comparison"` is monomorphic and
/// stringless (task #18's deviation 1), i.e. `core_k::lift_fueled`.
pub fn check_thm_val_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    value: &Expr,
) -> CheckCM<FEnv> {
    match type_checker::infer_type_core(mode, st, &fe, 0, jty) {
        Err(err) => Err(err),
        Ok(jsty) => match op_s_ix_c(mode, st, &fe, 0, &jsty) {
            Err(err) => Err(err),
            Ok(ul) => match core_k::lift_fueled(level::is_equiv(&ul, &level::zero())) {
                Err(err) => Err(err),
                Ok(is_prop) => {
                    if is_prop {
                        check_thm_val_c_witness(mode, st, fe, cv_a, jty, value)
                    } else {
                        Err(core_types::invalid({ const M: [u32; 36] = [116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110]; core_types::code_points(&M) }))
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:117-138 checkThmValC
/// The witness half: the value's syntactic guards and its annotation.  Split
/// off so the is-a-proposition gate is a tail call (task #24's deviation 7).
pub fn check_thm_val_c_witness(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    value: &Expr,
) -> CheckCM<FEnv> {
    if !expr_ops_c::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops_c::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, &fe, 0, value) {
            Err(err) => Err(err),
            Ok(jv) => check_thm_val_c_checked(mode, st, fe, cv_a, jty, value, jv),
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:117-138 checkThmValC
/// The tail past the witness annotation.  The `ienv` record carries **no**
/// value (`recordCConst … none`) and the push stores the record's own *raw*
/// value, unread: a theorem is stored by its statement and is opaque to
/// reduction, so the annotated witness is checked and then discarded.
pub fn check_thm_val_c_checked(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    value: &Expr,
    jv: Expr,
) -> CheckCM<FEnv> {
    if !expr_ops_c::all_level_params_defined(&cv_a.level_params, &jv) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !state_c::consts_resolve_fc(&fe, &jv) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        state_c::record_c_const(
            st,
            name::dup(&cv_a.name),
            expr::dup(&cv_a.ty),
            expr::dup(jty),
            None,
        );
        match type_checker::infer_type_core(mode, st, &fe, 0, &jv) {
            Err(err) => Err(err),
            Ok(jvt) => match type_checker::is_def_eq_core(mode, st, &fe, 0, &jvt, jty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::push(
                            fe,
                            ConstantInfo::ThmInfo(
                                env::constant_val_dup(cv_a),
                                expr::dup(value),
                            ),
                        ))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 24] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 104, 101, 111, 114, 101, 109]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:140-156 checkOpaqueValC
/// `checkOpaqueValP` over `ExprC`: exactly the theorem check without the
/// is-a-proposition requirement, stored as an `axiomInfo` because the
/// official kernel's `is_delta` never unfolds an opaque.
pub fn check_opaque_val_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    value: &Expr,
) -> CheckCM<FEnv> {
    if !expr_ops_c::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops_c::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, &fe, 0, value) {
            Err(err) => Err(err),
            Ok(jv) => check_opaque_val_c_after_annot(mode, st, fe, cv_a, jty, jv),
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:140-156 checkOpaqueValC
/// The tail past the annotation.
pub fn check_opaque_val_c_after_annot(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    jv: Expr,
) -> CheckCM<FEnv> {
    if !expr_ops_c::all_level_params_defined(&cv_a.level_params, &jv) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !state_c::consts_resolve_fc(&fe, &jv) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        state_c::record_c_const(
            st,
            name::dup(&cv_a.name),
            expr::dup(&cv_a.ty),
            expr::dup(jty),
            None,
        );
        match type_checker::infer_type_core(mode, st, &fe, 0, &jv) {
            Err(err) => Err(err),
            Ok(jvt) => match type_checker::is_def_eq_core(mode, st, &fe, 0, &jvt, jty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::push(
                            fe,
                            ConstantInfo::AxiomInfo(env::constant_val_dup(cv_a)),
                        ))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 23] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 111, 112, 97, 113, 117, 101]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// One parsed declaration, mirroring `checkDeclSPPlain` branch by branch.
/// The six arms are six functions, so every one of them is a tail call
/// (task #18's rule for a gated cascade).
pub fn check_decl_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    pd: &DeclC,
) -> CheckCM<FEnv> {
    match pd {
        DeclC::DefnDecl(cv, value, hint) => {
            check_defn_decl_c(mode, st, fe, cv, value, hint)
        }
        DeclC::ThmDecl(cv, value) => check_thm_decl_c(mode, st, fe, cv, value),
        DeclC::OpaqueDecl(cv, value) => check_opaque_decl_c(mode, st, fe, cv, value),
        DeclC::AxiomDecl(cv) => check_axiom_decl_c(mode, st, fe, cv),
        DeclC::BasisDecl(kind) => check_basis_decl_c(fe, kind),
        DeclC::IndDecl(block, n_p) => check_ind_decl_c(mode, st, fe, block, *n_p),
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.defnDecl` arm.  **The pinned-name test comes first**, which is the
/// cited arm's own RC-linearity shape: with `fe` still live after the push —
/// the pin gates read it at the pre-insertion bound — `checkDefnValC`'s
/// `fe.push` would copy the whole index on every definition, so con-leche
/// branches before the push and the common arm hands `fe` to it unshared.
/// The port's index is threaded by value (task #14), so the same branch is
/// what keeps the common arm a single tail call.
///
/// Deviation (task #24's module note 1): the pre-insertion environment is a
/// *visibility bound*, `k_pre = fe.visibleBelow` read off before the push,
/// not a second value.
pub fn check_defn_decl_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
    hint: &ReducibilityHint,
) -> CheckCM<FEnv> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val_c(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok((cv_a, jty)) => {
            if name::contains(&core_k::nat_op_names(), &cv_a.name)
                || name::contains(&core_k::nat_div_mod_names(), &cv_a.name)
            {
                match check_defn_val_c(mode, st, fe, &cv_a, &jty, value, hint) {
                    Err(err) => Err(err),
                    Ok(fe2) => check_defn_pins_c(mode, st, fe2, k_pre, &cv_a.name),
                }
            } else {
                check_defn_val_c(mode, st, fe, &cv_a, &jty, value, hint)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.defnDecl` arm's two pinned-`Nat` gates — the structural-operation
/// recurrence certificates and the `Nat.div`/`Nat.mod` pin variants.
///
/// Deviation: they are `checkDecl`'s gates character for character
/// (`natOpGuardF`/`natOpStoredOkF`/`certifyNatEqs` and `checkDivModPinF` are
/// the `FEnv`-indexed twins of `natOpGuard`/`natOpStoredOk`/`certifyNatEqs`
/// and `checkDivModPin`, and the port has one environment spelling — task
/// #18's deviation 3), so this is a wrapper over `checker::check_defn_pins`
/// rather than a second copy.  `sharedOpsC mode fe`, the record the cited
/// code passes them, is the collapse of task #24's note 1: there is no
/// record, and the slots are `kernel::type_checker`'s by name.
pub fn check_defn_pins_c(
    mode: &CheckMode,
    st: &mut CState,
    fe2: FEnv,
    k_pre: u64,
    n: &Name,
) -> CheckCM<FEnv> {
    checker::check_defn_pins(mode, st, fe2, k_pre, n)
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.thmDecl` arm.
pub fn check_thm_decl_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckCM<FEnv> {
    match check_constant_val_c(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok((cv_a, jty)) => check_thm_val_c(mode, st, fe, &cv_a, &jty, value),
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.opaqueDecl` arm: the compiler-trust gate for
/// `Lean.reduceNat`/`Lean.reduceBool`, tested before the push for the cited
/// RC-linearity reason (the comment in `checkDeclC` itself), then the opaque
/// check.  `checkReducePinF` returns the index where the Lean returns `Unit`
/// (task #24's module note 1), so returning it *is* the cited `pure fe2`.
pub fn check_opaque_decl_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckCM<FEnv> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val_c(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok((cv_a, jty)) => {
            if name::contains(&trust_axioms::reduce_op_names(), &cv_a.name) {
                match check_opaque_val_c(mode, st, fe, &cv_a, &jty, value) {
                    Err(err) => Err(err),
                    Ok(fe2) => {
                        checker::check_reduce_pin(mode, st, fe2, k_pre, &cv_a.name, value)
                    }
                }
            } else {
                check_opaque_val_c(mode, st, fe, &cv_a, &jty, value)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.axiomDecl` arm.  The one thing it adds to `checkDecl`'s is the
/// `recordCConst` before each install: the cached lane keeps the accepted
/// constant's annotated type in `ienv`, tagged with the very `Expr` object
/// pushed into the index.  The tolerated whitelist (`sorryAx`) is
/// well-formedness-checked and **not** recorded and not stored, as the cited
/// `pure fe` arm has it.
pub fn check_axiom_decl_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
) -> CheckCM<FEnv> {
    match check_constant_val_c(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok((cv_a, jty)) => {
            if std_axioms::std_axiom_ok(&fe, &cv_a) {
                state_c::record_c_const(
                    st,
                    name::dup(&cv_a.name),
                    expr::dup(&cv_a.ty),
                    jty,
                    None,
                );
                Ok(fenv::push(fe, ConstantInfo::AxiomInfo(cv_a)))
            } else if name::beq(&cv_a.name, &trust_axioms::trust_compiler_name()) {
                if trust_axioms::trust_compiler_ok(&fe, &cv_a) {
                    state_c::record_c_const(
                        st,
                        name::dup(&cv_a.name),
                        expr::dup(&cv_a.ty),
                        jty,
                        None,
                    );
                    Ok(fenv::push(fe, ConstantInfo::AxiomInfo(cv_a)))
                } else {
                    Err(core_types::not_implemented({ const M: [u32; 36] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 76, 101, 97, 110, 46, 116, 114, 117, 115, 116, 67, 111, 109, 112, 105, 108, 101, 114, 32, 115, 104, 97, 112, 101]; core_types::code_points(&M) }))
                }
            } else if name::beq(&cv_a.name, &trust_axioms::of_reduce_nat_name())
                || name::beq(&cv_a.name, &trust_axioms::of_reduce_bool_name())
            {
                if trust_axioms::of_reduce_ax_ok(&fe, &cv_a) {
                    state_c::record_c_const(
                        st,
                        name::dup(&cv_a.name),
                        expr::dup(&cv_a.ty),
                        jty,
                        None,
                    );
                    Ok(fenv::push(fe, ConstantInfo::AxiomInfo(cv_a)))
                } else {
                    Err(core_types::not_implemented({ const M: [u32; 44] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 97, 120, 105, 111, 109, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116]; core_types::code_points(&M) }))
                }
            } else if name::beq(&cv_a.name, &std_axioms::propext_name())
                || name::beq(&cv_a.name, &std_axioms::choice_name())
            {
                Err(core_types::not_implemented({ const M: [u32; 29] = [115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109, 32, 115, 104, 97, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
            } else if name::contains(&std_axioms::tolerated_axiom_names(), &cv_a.name) {
                Ok(fe)
            } else {
                Err(core_types::not_implemented({ const M: [u32; 18] = [110, 111, 110, 45, 115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109]; core_types::code_points(&M) }))
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.basisDecl` arm: the pinned `Eq` basis prerequisite of the quotient
/// block, then the install fold.
///
/// Deviation: the cited arm is `checkDecl`'s character for character —
/// `installBasisDeclF` is `installBasisDecl`'s indexed twin and the port has
/// one environment spelling (task #18's deviation 3) — so this is a wrapper
/// over `checker::check_basis_decl` rather than a second copy.  The blocks it
/// installs come from `kernel::basis_pins`, task #22's generated table.
pub fn check_basis_decl_c(fe: FEnv, kind: &BasisKind) -> CheckCM<FEnv> {
    checker::check_basis_decl(fe, kind)
}

/// con-leche: ConLeche/Cached/ParsedC.lean:158-241 checkDeclC
/// The `.indDecl` arm.  **The declared parameter count first, and for both
/// routes** (con-leche task #228): `indParamsOk` is official's own check,
/// one-sided, and it runs before the dispatch because it is a property of the
/// DECLARATION and not of a route — so a block with a wrong `nparams` is
/// *rejected* here.
///
/// **ONE ROUTE, dispatched by the recogniser alone** (con-leche tasks #210
/// and #219): a block `nativeParts?` recognises is the fixpoint route's,
/// every other one the modeled path's.  The two drivers are task #25's
/// `kernel::inductives::inductives_c`, whose module note names this call site
/// — `check_native_s` takes the index by reference and `fenv::dup`s it
/// internally (`native_install::check_native_pass_former`), so the extended
/// index it returns *is* the arm's result and `fe` is consumed by being
/// dropped; `check_ind_decl_s` takes it by value, as the port's other install
/// paths do.
///
/// No placeholder is left in this module: `checkDeclC` is complete.
pub fn check_ind_decl_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    block: &Vec<ConstantInfo>,
    n_p: u64,
) -> CheckCM<FEnv> {
    if env::ind_params_ok(n_p, block) {
        match native_parts::native_parts(n_p, block) {
            Some(p) => inductives_c::check_native_s(mode, st, &fe, &p),
            None => inductives_c::check_ind_decl_s(mode, st, fe, block),
        }
    } else {
        Err(core_types::invalid({ const M: [u32; 29] = [110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:259-262 checkDeclStepC
/// One step of the parsed-declaration fold: **flush, then check**.  The flush
/// is what makes one `CState` safe for a whole stream — every
/// environment-dependent memo is emptied, the self-certified `ienv` and the
/// three level-operation memos survive (`state_c::flushed`).
pub fn check_decl_step_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    pd: &DeclC,
) -> CheckCM<FEnv> {
    state_c::flush_c(st);
    check_decl_c(mode, st, fe, pd)
}

/* Not ported from `ParsedC.lean` (DESIGN.md §3.1: message strings need not
   match, because the theorem never reads them):

   * `msSecs` (`:245-247`) — milliseconds rendered as `s.d` seconds for the
     driver's progress line;
   * `declCLabel` (`:249-257`) — a parsed declaration's display label
     (`Main.declCName`'s shared spelling).

   Both are `String`-valued and on no verdict path.  The declaration fold
   itself (`checkDecls`, `checkPending`) is `Cached/Installed.lean`'s, a
   different file. */

#[cfg(test)]
mod tests {
    use crate::cached::parsed_c;
    use crate::cached::parsed_c::DeclC;
    use crate::cached::parsed_c::ValueKind;
    use crate::cached::state_c;
    use crate::cached::state_c::CState;
    use crate::kernel::basis_names;
    use crate::kernel::core_types::CheckError;
    use crate::kernel::env;
    use crate::kernel::env::BasisKind;
    use crate::kernel::env::CheckMode;
    use crate::kernel::env::ConstantInfo;
    use crate::kernel::env::ConstantVal;
    use crate::kernel::env::Env;
    use crate::kernel::env::ReducibilityHint;
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr};
    use crate::kernel::fenv;
    use crate::kernel::fenv::FEnv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn cv(s: &str) -> ConstantVal {
        ConstantVal {
            name: nm(s),
            level_params: Vec::new(),
            ty: expr::sort(level::zero()),
        }
    }

    fn cvt(s: &str, ty: Expr) -> ConstantVal {
        ConstantVal { name: nm(s), level_params: Vec::new(), ty }
    }

    fn never() -> BinderMeta {
        BinderMeta { pw: prop_when::never() }
    }

    /// `Sort 1`, the type of `Sort 0`.
    fn sort1() -> Expr {
        expr::sort(level::succ(level::zero()))
    }

    fn is_invalid(e: &CheckError) -> bool {
        match e {
            CheckError::Invalid(_) => true,
            _ => false,
        }
    }

    fn is_not_implemented(e: &CheckError) -> bool {
        match e {
            CheckError::NotImplemented(_) => true,
            _ => false,
        }
    }

    /// The empty index: nothing this test set checks needs a stored constant,
    /// because `Sort`/Π/λ terms resolve against no environment.
    fn empty_fenv() -> FEnv {
        fenv::mk_fenv(env::empty())
    }

    /// **`checkConstantValC`'s two rejects.**  A stored name is `.invalid`
    /// (the index is consulted before anything is annotated), and so is a type
    /// with a loose bound variable — `ExprC.looseBVarsBounded 0` is the
    /// `O(1)` cached-bound read, and this is the one place the port can see it
    /// answer `false`.  A reserved basis name is the third.  The positive
    /// control checks with its type **annotated** and paired with itself.
    #[test]
    fn check_constant_val_c_rejects_a_duplicate_and_a_loose_bvar() {
        let mode = CheckMode::Verified;

        // a duplicate: `a` is already stored
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ConstantInfo::AxiomInfo(cvt("a", sort1())));
        let fe: FEnv = fenv::mk_fenv(Env { consts });
        let mut st: CState = state_c::cstate_new();
        match parsed_c::check_constant_val_c(&mode, &mut st, &fe, &cvt("a", sort1())) {
            Ok(_) => panic!("a duplicate declaration must not check"),
            Err(e) => assert!(is_invalid(&e), "a duplicate is a reject, not a decline"),
        }

        // a loose bound variable in the type
        let mut st2: CState = state_c::cstate_new();
        match parsed_c::check_constant_val_c(
            &mode,
            &mut st2,
            &empty_fenv(),
            &cvt("b", expr::bvar(0)),
        ) {
            Ok(_) => panic!("a loose bound variable in a type must not check"),
            Err(e) => assert!(is_invalid(&e)),
        }
        // and the guard is the cached bound read, answering `false` at 0
        assert!(!crate::cached::expr_ops_c::loose_bvars_bounded(0, &expr::bvar(0)));

        // a reserved basis name
        let reserved: Name = name::dup(&basis_names::reserved_basis_names()[0]);
        let mut st3: CState = state_c::cstate_new();
        match parsed_c::check_constant_val_c(
            &mode,
            &mut st3,
            &empty_fenv(),
            &cvt("x", sort1()),
        ) {
            Ok(_) => (),
            Err(_) => panic!("`x : Sort 1` under a fresh name must check"),
        }
        let mut st4: CState = state_c::cstate_new();
        match parsed_c::check_constant_val_c(
            &mode,
            &mut st4,
            &empty_fenv(),
            &ConstantVal { name: reserved, level_params: Vec::new(), ty: sort1() },
        ) {
            Ok(_) => panic!("a reserved basis name must not check"),
            Err(e) => assert!(is_invalid(&e)),
        }

        // the positive control's shape: the constant comes back with its type
        // annotated, and the second component is that same annotated type
        let mut st5: CState = state_c::cstate_new();
        match parsed_c::check_constant_val_c(
            &mode,
            &mut st5,
            &empty_fenv(),
            &cvt("y", sort1()),
        ) {
            Ok((cv_a, jty)) => {
                assert!(name::beq(&cv_a.name, &nm("y")));
                assert!(expr::beq(&cv_a.ty, &jty));
                assert!(expr::beq(&jty, &sort1()));
            }
            Err(_) => panic!("`y : Sort 1` must check"),
        }
    }

    /// **`checkDefnValC` accepts `(λ x : Sort 1. x) : Sort 1 → Sort 1`.**  The
    /// value annotates, every level parameter is defined (there are none),
    /// every constant resolves (there are none), `infer` gives
    /// `∀ (_ : Sort 1), Sort 1` and `defeq` matches the declared type — so the
    /// definition installs as a `defnInfo` holding the **annotated** value and
    /// the visibility bound advances by one.  The `ienv` record is asserted
    /// too, because writing it is this file's deviation 2 from
    /// `kernel::checker`.
    #[test]
    fn check_defn_val_c_accepts_the_identity_on_sort_1() {
        let mode = CheckMode::Verified;
        let ty: Expr = expr::forall_e(sort1(), sort1(), never());
        let value: Expr = expr::lam(sort1(), expr::bvar(0), never());
        let mut st: CState = state_c::cstate_new();

        let (cv_a, jty) =
            match parsed_c::check_constant_val_c(&mode, &mut st, &empty_fenv(), &cvt("id1", ty)) {
                Ok(p) => p,
                Err(_) => panic!("`id1 : Sort 1 → Sort 1` must check as a header"),
            };
        match parsed_c::check_defn_val_c(
            &mode,
            &mut st,
            empty_fenv(),
            &cv_a,
            &jty,
            &value,
            &ReducibilityHint::Abbrev,
        ) {
            Ok(fe2) => {
                match fenv::find(&fe2, &nm("id1")) {
                    Some(ConstantInfo::DefnInfo(cvd, stored, _)) => {
                        assert!(name::beq(&cvd.name, &nm("id1")));
                        // the *annotated* value is what is stored, and it is
                        // still the identity λ
                        assert!(expr::beq(stored, &value));
                    }
                    _ => panic!("the definition must be installed as a `defnInfo`"),
                }
                assert_eq!(fe2.visible_below, 1);
                // deviation 2: the accepted constant is in `ienv`, with its
                // value pair present (a definition, unlike a theorem)
                match st.ienv.get(&nm("id1")) {
                    Some(entry) => {
                        assert!(expr::beq(&entry.ty, &jty));
                        assert!(entry.val.is_some());
                    }
                    None => panic!("`recordCConst` must have written the `ienv` entry"),
                }
            }
            Err(_) => panic!("`(λ x : Sort 1. x) : Sort 1 → Sort 1` must check"),
        }

        // the negative control: the same header with a value of the wrong
        // type is the one *reject* the value check can produce
        let mut st2: CState = state_c::cstate_new();
        let ty2: Expr = expr::forall_e(sort1(), sort1(), never());
        let (cv_b, jty2) =
            match parsed_c::check_constant_val_c(&mode, &mut st2, &empty_fenv(), &cvt("id2", ty2)) {
                Ok(p) => p,
                Err(_) => panic!("the header must check"),
            };
        match parsed_c::check_defn_val_c(
            &mode,
            &mut st2,
            empty_fenv(),
            &cv_b,
            &jty2,
            &sort1(),
            &ReducibilityHint::Abbrev,
        ) {
            Ok(_) => panic!("`Sort 1 : Sort 1 → Sort 1` must not check"),
            Err(e) => assert!(is_invalid(&e), "a type mismatch is a reject"),
        }
    }

    /// `checkDeclStepC` flushes and then dispatches, and the `.indDecl` arm
    /// reaches task #25's two routes: the declared parameter count is checked
    /// first and for both of them, so a wrong `nparams` is a **reject**
    /// (official's own), while a block the recogniser refuses and the
    /// modeller has no `_model` for is refused from *inside* the modeled
    /// route — not by a placeholder.
    #[test]
    fn check_decl_step_c_flushes_and_dispatches_the_ind_arm() {
        let mode = CheckMode::Verified;
        let mut st: CState = state_c::cstate_new();

        // **The flush happens first.**  Seed an environment-dependent memo
        // and an `ienv` entry, then run a step whose check fails at
        // `checkConstantValC`'s very first guard — a duplicate name — so
        // nothing downstream annotates anything: what is left in `annot_c`
        // afterwards is exactly what the flush left.
        st.annot_c.insert(expr::bvar(0), expr::bvar(0));
        state_c::record_c_const(&mut st, nm("k"), sort1(), sort1(), None);
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ConstantInfo::AxiomInfo(cvt("k", sort1())));
        let fe_k: FEnv = fenv::mk_fenv(Env { consts });
        match parsed_c::check_decl_step_c(
            &mode,
            &mut st,
            fe_k,
            &DeclC::AxiomDecl(cvt("k", sort1())),
        ) {
            Ok(_) => panic!("a duplicate axiom must not check"),
            Err(e) => assert!(is_invalid(&e)),
        }
        // flushed: the environment-dependent memo is empty, and the
        // self-certified `ienv` survives (`state_c::flushed`)
        assert_eq!(st.annot_c.len(), 0);
        assert!(st.ienv.get(&nm("k")).is_some());

        // **The `.indDecl` arm reaches the routes.**  `T : Sort 0` with a
        // constructor is well-formed at `nparams = 0`, the recogniser refuses
        // it (no recursor record), and the modeled route then finds no
        // `T._model` — so the refusal comes from inside the route.
        let good_block: Vec<ConstantInfo> = {
            let mut b: Vec<ConstantInfo> = Vec::new();
            b.push(ConstantInfo::IndInfo(cv("T"), env::ind_caps_default()));
            b.push(ConstantInfo::CtorInfo(cv("T.mk"), 0, 0));
            b
        };
        assert!(env::ind_params_ok(0, &good_block));
        let mut st_i: CState = state_c::cstate_new();
        match parsed_c::check_decl_c(
            &mode,
            &mut st_i,
            empty_fenv(),
            &DeclC::IndDecl(good_block, 0),
        ) {
            Ok(_) => panic!("a `T : Sort 0` block with no model must not install"),
            Err(_) => (),
        }

        // a declared parameter count the block cannot satisfy is a *reject*
        let mut st2: CState = state_c::cstate_new();
        let mut bad_block: Vec<ConstantInfo> = Vec::new();
        bad_block.push(ConstantInfo::IndInfo(cv("U"), env::ind_caps_default()));
        assert!(!env::ind_params_ok(3, &bad_block));
        match parsed_c::check_decl_c(
            &mode,
            &mut st2,
            empty_fenv(),
            &DeclC::IndDecl(bad_block, 3),
        ) {
            Ok(_) => panic!("a wrong `nparams` must not check"),
            Err(e) => assert!(is_invalid(&e), "a wrong `nparams` is official's own reject"),
        }

        // and an axiom the pins do not know is a decline at its own record,
        // through the same fold
        let mut st3: CState = state_c::cstate_new();
        match parsed_c::check_decl_c(
            &mode,
            &mut st3,
            empty_fenv(),
            &DeclC::AxiomDecl(cvt("myAxiom", sort1())),
        ) {
            Ok(_) => panic!("a non-standard axiom must not be installed"),
            Err(e) => assert!(is_not_implemented(&e)),
        }
    }

    /// A `DeclC` list is what `check_decls` consumes; an `indDecl` block
    /// carries *installed* records at their parse placeholders.
    #[test]
    fn decl_list_shape() {
        let ds = vec![
            DeclC::AxiomDecl(cv("ax")),
            DeclC::BasisDecl(BasisKind::NatK),
            DeclC::IndDecl(
                vec![
                    ConstantInfo::IndInfo(cv("T"), env::ind_caps_default()),
                    ConstantInfo::CtorInfo(cv("T.mk"), 0, 0),
                    ConstantInfo::RecInfo(
                        cv("T.rec"),
                        0,
                        0,
                        vec![env::rec_rule_parsed(nm("T.mk"), 0, expr::bvar(0))],
                    ),
                ],
                0,
            ),
        ];
        assert_eq!(ds.len(), 3);
        match &ds[2] {
            DeclC::IndDecl(block, n_p) => {
                assert_eq!(*n_p, 0);
                assert!(env::recs_form_suffix(block));
                assert!(env::ind_params_ok(*n_p, block));
            }
            _ => panic!("wrong constructor"),
        }
    }

    /// `PendingCheck` records the datum, the fold position and the
    /// installation counter the prefix view is taken at.
    #[test]
    fn pending_check_carries_the_seam() {
        let pc = parsed_c::PendingCheck {
            vg: parsed_c::ValueGroup {
                kind: ValueKind::Thm,
                cv_a: cv("t"),
                jv: expr::bvar(0),
            },
            pos: 4,
            vis: 3,
        };
        assert_eq!((pc.pos, pc.vis), (4, 3));
        assert!(matches!(pc.vg.kind, ValueKind::Thm));
        assert!(name::beq(&pc.vg.cv_a.name, &nm("t")));
        assert!(matches!(
            parsed_c::value_kind_dup(&ValueKind::Opaque),
            ValueKind::Opaque
        ));
    }
}
