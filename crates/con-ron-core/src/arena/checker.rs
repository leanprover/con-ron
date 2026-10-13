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
//!   record, guarding its header and its value but not inferring; phase B
//!   checks each recorded declaration against the PREFIX VIEW it was installed
//!   at.  con-leche proves the two are the same accept
//!   (`fullyChecked_checkDecls`); the arena's two call the same `checkDecl`
//!   pieces, which is what keeps them the same computation.
//!
//! ## Every step is bracketed
//!
//! DESIGN.md §8.3: "Persistent = parse + installed environment; scratch = one
//! declaration's check."  Both phases and both folds run each record inside
//! `enter_scratch` … `drop_scratch`.  Phase B's `check_pending` brackets
//! `check_value_group`, and every node it appends goes with the tier.  Phase
//! A's `install_step` brackets the install too (the fallback
//! `install_step_other` included), because the ordinary step's installers
//! infer and inference interns: `promote` copies exactly what leaves the step
//! — the installed constants and the pending record — to the persistent tier
//! before the drop (see `install_step`).
//! `check_decls_pure`'s step, `check_decl_step`, is bracketed the same way.
//!
//! ## The pins are interned at startup
//!
//! `intern_all_pins` is DESIGN.md §8.6 P2d's one-time tree walk, and it is what
//! makes every later `pin`/`intern_ci` of the same datum return the PERSISTENT
//! handle whatever tier is live (§8.3: `intern` probes the persistent table
//! first).  Without it a reserved name first interned inside a scratch tier
//! would compare unequal to the stream's own persistent copy of it, which is
//! the one way hash-consing can go wrong across the tier boundary.

use crate::arena::basis::{basis_kind_decls, basis_kind_decls_a};
use crate::arena::checker_base::nidx_contains_from;
use crate::arena::checker_split::{
    check_value_group, install_header, install_value_guards, ValueGroup, ValueKind,
};
use crate::arena::core::{
    drop_scratch, enter_record, enter_scratch, flush_caches, leave_record, nat_div_mod_names, nat_op_names, CORE_WALK_FUEL,
};
use crate::arena::decl_check::install_basis_decls;
use crate::arena::env::{
    i_constant_val_dup, i_env_empty, mk_ifenv, IConstantInfo, IConstantVal, IDeclaration, IFEnv,
};
use crate::arena::handle::EIdx;
use crate::arena::monad::{fail, AState};
use crate::arena::nat_op_pin_set::{intern_pin_sets, INatOpPinSet};
use crate::arena::promote::{promote_new, promote_vg, PMemo};
use crate::arena::trust_axioms::reduce_op_names;
use crate::arena::pins::{pin_quot_sound, pin_sorry_ax, Pins};
use crate::arena::env::nidx_vec_dup;
use crate::arena::store::{EStore, ETables, LTables, LsTables, NTables};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env as cenv;
use crate::kernel::env::{BasisKind, CheckMode, ReducibilityHint};
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::ron::hashmap::Dup;
use crate::arena::store::PersTier;

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
/// ``"`And` must be the standard `And`"``, as code points: `installDeclStep`'s
/// reject of a record that fails the `And` pin.
pub const M_AND_PIN: [u32; 32] = [
    96, 65, 110, 100, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 116, 104, 101, 32, 115,
    116, 97, 110, 100, 97, 114, 100, 32, 96, 65, 110, 100, 96
];

// ---------------------------------------------------------------------------
// The pinned basis install (`Checker.lean:65-78` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:423-433 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:37-48 checkBasisDecl` —
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

/// con-leche: ConLeche/Kernel/Checker.lean:423-433 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:37-48 checkBasisDecl` — the
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
// The two-phase fold the binary runs (`Checker.lean:210-341` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Installed.lean:85-93 PendingCheck
/// Lean twin: `proof/ConRon/Arena/Checker.lean:103-111 PendingCheck` — a
/// phase-A record awaiting its phase-B check: the datum that crosses the
/// install/check seam, the fold position of the declaration (its error tag) and
/// the environment counter at the install.
pub struct PendingCheck {
    pub vg: ValueGroup,
    pub pos: u64,
    pub vis: u64,
}

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — phase
/// A's step BODY: guard-and-install for the three value kinds, the ordinary
/// step `check_decl` for everything else.  The four arms are four functions,
/// so every one of them is a tail call.  (Task #119, con-leche task #342
/// L-DEAD's renames: was `annot_step_go`, `annotStepC`.)
///
/// **The body, not the step** — `install_step` below is this under the
/// per-declaration bracket.  What the body returns is what a step LEAVES
/// BEHIND: the extended environment, and — for the three value kinds — the
/// `ValueGroup` phase B will check.  The fold position and the environment
/// counter the pending record carries are the bracket's to supply.
pub fn install_step_go(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pd: &IDeclaration,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match pd {
        IDeclaration::DefnDecl(cv, value, hint) => {
            install_step_defn(pers, st, mode, pins, fe, pd, cv, value, hint)
        }
        IDeclaration::ThmDecl(cv, value) => install_step_thm(pers, st, fe, cv, value),
        IDeclaration::OpaqueDecl(cv, value) => {
            install_step_opaque(pers, st, mode, pins, fe, pd, cv, value)
        }
        _ => install_step_other(pers, st, mode, pins, fe, pd),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:153-207 installStep` — **phase
/// A's step, bracketed**; `i` is the fold position the record is tagged with.
///
/// **The bracket** (DESIGN.md §8.3, "Phase A runs in the scratch tier too,
/// with promotion", task #97-P6-2):
///
/// ```text
/// flush_caches; enter_scratch; <the step>; promote; drop_scratch
/// ```
///
/// `promote` (`arena::promote`) is the memoised structural copy scratch →
/// persistent, run on **exactly what leaves the step**: the `k` constants the
/// step installed (`promote_new`) and the pending record (`promote_vg`, at the
/// SAME memo).  A persistent handle promotes to itself, so a record that
/// installs what the parse already built — every value kind since task #119,
/// whose install half interns nothing — pays one tier-bit test per handle;
/// the blocks the ordinary step installs (inductives, the basis) still build
/// terms.  The flush stays where con-leche puts it, at the head
/// (`installGuardsC` and the `.thmDecl` arm's own `flushC`, and
/// `checkDeclStepC`'s), so every phase-A record starts with EMPTY caches.
pub fn install_step(
    _pers: &PersTier,
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
    let mut tier: PersTier = enter_scratch(st);
    match install_step_go(&tier, st, mode, pins, fe, pd) {
        Err(e) => {
            drop_scratch(st, tier);
            Err(e)
        }
        Ok((fe2, vg_opt)) => {
            let k: u64 = fe2.visible_below - vis;
            match vg_opt {
                None => match promote_new(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, k, fe2) {
                    Err(e) => {
                        drop_scratch(st, tier);
                        Err(e)
                    }
                    Ok((_, fe3)) => {
                        drop_scratch(st, tier);
                        Ok((fe3, pend))
                    }
                },
                Some(vg) => install_step_promote(tier, st, i, vis, k, fe2, pend, vg),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:153-207 installStep` — the
/// bracket's `some vg` arm: the seam promoted first and the environment at the
/// SAME memo, then the tier dropped and the record pushed.
#[allow(clippy::too_many_arguments)]
pub fn install_step_promote(
    tier: PersTier,
    st: &mut AState,
    i: u64,
    vis: u64,
    k: u64,
    fe: IFEnv,
    pend: Vec<PendingCheck>,
    vg: ValueGroup,
) -> Result<(IFEnv, Vec<PendingCheck>), CheckError> {
    let mut tier: PersTier = tier;
    match promote_vg(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, vg) {
        Err(e) => {
            drop_scratch(st, tier);
            Err(e)
        }
        Ok((m, vg2)) => match promote_new(&mut tier, st, m, CORE_WALK_FUEL, k, fe) {
            Err(e) => {
                drop_scratch(st, tier);
                Err(e)
            }
            Ok((_, fe2)) => {
                drop_scratch(st, tier);
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

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — the
/// `.defnDecl` arm: a pin-certified operation takes the ordinary step (its
/// check is not separable from its install), everything else is guarded,
/// installed and recorded as pending.
#[allow(clippy::too_many_arguments)]
pub fn install_step_defn(
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
                    install_step_other(pers, st, mode, pins, fe, pd)
                } else {
                    install_step_defn_install(pers, st, fe, cv, value, hint)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:127-133 installGuardsC
/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — the
/// `.defnDecl` arm's guards (`installGuardsC`: the header's, then the value's)
/// and its push: the constant is stored AS DECLARED.  The environment counter
/// the pending record carries is the BRACKET's (task #97-P6-2).
pub fn install_step_defn_install(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match install_header(pers, fe.visible_below, st, &fe, cv) {
        Err(e) => Err(e),
        Ok(()) => match install_value_guards(pers, fe.visible_below, st, &fe, cv, value) {
            Err(e) => Err(e),
            Ok(()) => {
                let fe2: IFEnv = crate::arena::env::ifenv_push(
                    fe,
                    IConstantInfo::DefnInfo(
                        i_constant_val_dup(cv),
                        value.dup2(),
                        cenv::reducibility_hint_dup(hint),
                    ),
                );
                Ok((
                    fe2,
                    Some(ValueGroup { kind: ValueKind::Defn, cv: i_constant_val_dup(cv), jv: value.dup2() }),
                ))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — the
/// `.thmDecl` arm: **a theorem installs BY STATEMENT**.  The header's guards
/// only; the value is recorded raw and never touched here (phase B guards it),
/// so phase A never enters a theorem's body.
pub fn install_step_thm(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match install_header(pers, fe.visible_below, st, &fe, cv) {
        Err(e) => Err(e),
        Ok(()) => {
            let fe2: IFEnv = crate::arena::env::ifenv_push(
                fe,
                IConstantInfo::ThmInfo(i_constant_val_dup(cv)),
            );
            Ok((
                fe2,
                Some(ValueGroup { kind: ValueKind::Thm, cv: i_constant_val_dup(cv), jv: value.dup2() }),
            ))
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — the
/// `.opaqueDecl` arm: a `reduce*` witness takes the ordinary step (its identity
/// certificate is part of its install), everything else is guarded, installed
/// **as an axiom** — an opaque's value being a discarded witness — and recorded
/// as pending.
pub fn install_step_opaque(
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
                install_step_other(pers, st, mode, pins, fe, pd)
            } else {
                install_step_opaque_install(pers, st, fe, cv, value)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:127-133 installGuardsC
/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — the
/// opaque arm's guards and push.  **An `opaque`'s value is not in the
/// environment**: the arm pushes `.axiomInfo cv` and hands the VALUE to the
/// pending record alone, which is why the bracket promotes the `ValueGroup`
/// beside the environment and at the same memo.
pub fn install_step_opaque_install(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match install_header(pers, fe.visible_below, st, &fe, cv) {
        Err(e) => Err(e),
        Ok(()) => match install_value_guards(pers, fe.visible_below, st, &fe, cv, value) {
            Err(e) => Err(e),
            Ok(()) => {
                let fe2: IFEnv = crate::arena::env::ifenv_push(
                    fe,
                    IConstantInfo::AxiomInfo(i_constant_val_dup(cv)),
                );
                Ok((
                    fe2,
                    Some(ValueGroup { kind: ValueKind::Opaque, cv: i_constant_val_dup(cv), jv: value.dup2() }),
                ))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:135-173 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:113-151 installStepGo` — the
/// catch-all arm, shared by the three gated branches above: the ordinary step,
/// which records nothing pending.
pub fn install_step_other(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: IFEnv,
    pd: &IDeclaration,
) -> Result<(IFEnv, Option<ValueGroup>), CheckError> {
    match crate::arena::check_decl::check_decl(pers, st, mode, pins, fe, pd) {
        Err(e) => Err(e),
        Ok(fe2) => Ok((fe2, None)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:175-196 installDeclStep
/// Lean twin: `proof/ConRon/Arena/Checker.lean:209-236 installDeclStep` — phase
/// A's step with the position carried and the error tagged: a failing step
/// reports the `CheckError` together with `i`, the fold position of the
/// declaration that failed.  (Task #119: was `annot_decl_step`.)
///
/// **The `And` pin comes first** (con-leche's ANDPIN, `basis::and_pin_ok`): a
/// record that declares `And`, `And.intro` or `And.rec` and is not the
/// toolchain's `And` block is rejected here, whatever its kind, ahead of the
/// kind dispatch and outside the scratch bracket.
///
/// Deviation: the twin restores the PRE-step state on a failure (it is written
/// as a state function); a failure aborts the whole fold here, so nothing reads
/// the state afterwards and no snapshot is taken.
pub fn install_decl_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>),
    pd: &IDeclaration,
) -> Result<(u64, IFEnv, Vec<PendingCheck>), (CheckError, u64)> {
    let i: u64 = p.0;
    match crate::arena::basis::and_pin_ok(pers, st, pd) {
        Err(e) => Err((e, i)),
        Ok(ok_and) => {
            if ok_and {
                match install_step(pers, st, mode, pins, i, p.1, p.2, pd) {
                    Err(e) => Err((e, i)),
                    Ok(q) => Ok((i + 1, q.0, q.1)),
                }
            } else {
                Err((CheckError::Invalid(code_points(&M_AND_PIN)), i))
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:431-448 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:238-249 installFold` — phase A
/// as a fold over the records, as an index recursion threading the accumulator
/// by value.  (Task #119: was `annot_fold`.)
pub fn install_fold(
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
        match install_decl_step(pers, st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => install_fold(pers, st, mode, pins, q, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:254-272 checkPending
/// Lean twin: `proof/ConRon/Arena/Checker.lean:251-267 checkPending` —
/// **phase B's check of one record**, against the prefix view
/// `fe.restrictTo pc.vis`.
///
/// **This is (C)'s per-declaration bracket** (DESIGN.md §8.3), on a store that
/// is ALREADY frozen (task #98-FREEZE): the bracket only empties the scratch
/// tier and the memos (`enter_record`), `check_value_group` runs the inference
/// and the conversion against `pers`, and the scratch tier is emptied again
/// (`leave_record`).  Deviation: the twin's `throw` skips its `dropScratch`
/// and the caller restores the pre-record state instead; the port empties the
/// tier on BOTH paths, which lands in the same place without a snapshot.
///
/// **The index comes in by REFERENCE and the twin's `restrictTo` is the scalar
/// `pc.vis`** (task #97-P6-6b), which is what lets `n` workers share it.
pub fn check_pending(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pc: &PendingCheck,
) -> Result<(), CheckError> {
    enter_record(st);
    let r: Result<(), CheckError> = check_value_group(pers, pc.vis, st, mode, fe, &pc.vg);
    leave_record(st);
    r
}

// ---------------------------------------------------------------------------
// The driver's fold: the phase boundary and phase B on a worker
// (task #97-P5-Driver)
//
// The binary FREEZES the persistent tier at the phase boundary into one
// `PersTier` every phase-B worker borrows, and each worker checks its records
// on a state of its own over that tier (`crates/con-ron/src/pool.rs`).  Every
// sequential piece of that is here, in the verified crate:
//
//   install_fold_hooked     phase A (`install_fold`, plus a read-only hook)
//   freeze_tier             the boundary
//   worker_state            a phase-B worker's state over the frozen tier
//   thaw_tier               the boundary undone
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/ParInstall.lean:113-194 installLoop
/// What the driver prints between phase A's steps (the `--progress`
/// heartbeat's install line), as a trait the verified fold calls: the hook
/// takes the state by SHARED reference and returns nothing, so it cannot
/// change a verdict — `install_fold_hooked` is `install_fold` with a call to it
/// before each step, and `Refine2/Checker/Phased.lean` proves the two equal.
/// `Modeller`'s arrangement (`frontend::types`): the trait is declared here,
/// the implementations live in the unverified crate.
pub trait InstallHook {
    /// con-leche: ConLeche/Driver/ParInstall.lean:113-194 installLoop
    /// Before record `pos` of `total` is installed.
    fn install_before(&self, pers: &PersTier, ar: &EStore, pos: u64, total: usize, d: &IDeclaration);
}

/// con-leche: ConLeche/Cached/Installed.lean:431-448 checkDecls
/// Lean twin: none — `install_fold` with the driver's hook; the twin has no
/// hook and the refinement is `install_fold`'s, through the equation
/// `install_fold_hooked_eq` (`Refine2/Checker/Phased.lean`).
/// **Phase A as the driver runs it**: `install_fold` step for step, with
/// `h.install_before` called before each record.  The hook reads the store and
/// writes nothing the fold can see.
#[allow(clippy::too_many_arguments)]
pub fn install_fold_hooked<H: InstallHook>(
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
        match install_decl_step(pers, st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => install_fold_hooked(pers, st, mode, pins, q, ds, i + 1, h),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:431-448 checkDecls
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
/// persistent tables move into one `PersTier` handed back `frozen`, for the
/// phase-B workers to read.  Task #98-FREEZE: this is a pure MOVE — the
/// store's scratch tiers and flags are untouched (a worker's store is its own,
/// `worker_state`), there is no flag to test and so no decline (`M_REFREEZE`
/// is gone), and `thaw_tier` puts the tables back where they were.  The
/// driver's store is not read between the two.
pub fn freeze_tier(ar: &mut EStore) -> PersTier {
    let n: NTables = core::mem::replace(&mut ar.lss.ls.ns.pers, NTables::empty());
    let l: LTables = core::mem::replace(&mut ar.lss.ls.pers, LTables::empty());
    let ls: LsTables = core::mem::replace(&mut ar.lss.pers, LsTables::empty());
    let e: ETables = core::mem::replace(&mut ar.pers, ETables::empty());
    PersTier {
        frozen: true,
        n,
        l,
        ls,
        e,
    }
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the inverse of `freeze_tier`, which has none either.
/// **`freeze_tier` inverted**: the tables back into the store, so that
/// everything after phase B — the verdict line's label, the failing record's
/// name, the receipts — reads the handles it was given.
/// `thaw_tier(ar, freeze_tier(ar))` leaves the store exactly as it found it
/// (`Refine2/Checker/Phased.lean`'s `freeze_tier_ok`).
pub fn thaw_tier(ar: &mut EStore, tier: PersTier) {
    ar.lss.ls.ns.pers = tier.n;
    ar.lss.ls.pers = tier.l;
    ar.lss.pers = tier.ls;
    ar.pers = tier.e;
}

/// con-leche: none — the pin table is handles, so a copy is a copy of words
/// Lean twin: none — the value is `Pins` itself (`Refine2`'s `pins_dup_val`).
/// A phase-B worker's copy of the driver's `Pins`: seventy handles into the
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

/// con-leche: ConLeche/Driver/CheckPool.lean:180-196 checkWorker
/// Lean twin: `proof/ConRon/Arena/Phased.lean:29-36 AState.worker` — the twin's
/// phase-B worker reads the persistent tier where it is.
/// **A phase-B worker's start state** (task #97-P6-6b's `pool::worker_state`,
/// moved here by task #97-P5-Driver): the empty store, FROZEN
/// (`EStore::empty_frozen`, task #98-FREEZE), so that every persistent read
/// goes to the `PersTier` the boundary froze and every append is a scratch
/// append; fresh memos and caches; and a copy of the pins.  The store stays
/// frozen for the worker's life: `check_pending` only empties its scratch tier.
pub fn worker_state(pins: &Pins) -> AState {
    let mut st = AState::init(EStore::empty_frozen());
    st.pins = pins_dup(pins);
    st
}

// ---------------------------------------------------------------------------
// The startup walk (`Checker.lean:343-373` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// con-leche: ConLeche/Kernel/BasisA.lean:48-54 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — **the
/// one-time tree walk of DESIGN.md §8.6 P2d**: every datum the checker compares
/// a stream record against, interned into the tier that is live at the call —
/// which, at the driver's call, is the persistent one.
///
/// The five basis blocks in both forms (the RAW ones `basis_pin_hit` and
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

/// con-leche: ConLeche/Kernel/BasisA.lean:48-54 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the five
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

/// con-leche: ConLeche/Kernel/BasisA.lean:48-54 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the five
/// kinds the startup walk interns, in the twin's order.
pub fn all_basis_kinds() -> Vec<BasisKind> {
    let mut ks: Vec<BasisKind> = Vec::with_capacity(5);
    ks.push(BasisKind::EqK);
    ks.push(BasisKind::NatK);
    ks.push(BasisKind::EmptyK);
    ks.push(BasisKind::FalseK);
    ks.push(BasisKind::QuotK);
    ks
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the
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

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the
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

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the
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

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the
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

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:309-344 internAllPins` — the
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
    use crate::arena::intern::{intern_ci_list, intern_cv};
    use crate::arena::std_axioms::i_constant_val_matches_pin;
    use crate::arena::store::EStore;
    use crate::arena::basis::basis_pin_hit;
    
    use crate::kernel::basis_names;
    use crate::kernel::basis_raw;

    use crate::kernel::env::{ConstantInfo, ConstantVal};
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr};

    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;
    use crate::kernel::std_axioms as cstd;

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

    /// The environment the basis prefix installs, built directly rather than
    /// by running a checker over `basis_prefix()`: a `.basisDecl` install IS
    /// `BasisKind.declsA`, pushed in order (task #97-SWAP), and the stored
    /// list is that one reversed (the `Env` deviation).
    fn basis_consts() -> Vec<ConstantInfo> {
        let mut cs: Vec<ConstantInfo> = Vec::new();
        for k in [BasisKind::EqK, BasisKind::NatK] {
            let mut b = crate::kernel::basis_tables::basis_decls_a(&k);
            while b.len() > 0 {
                cs.push(b.remove(0));
            }
        }
        cs.reverse();
        cs
    }

    /// The arena's `std_axiom_ok` of `c` in the basis environment.
    fn std_axiom(c: &ConstantVal) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let cs = ok(intern_ci_list(pers, &mut st, &basis_consts()));
        let icv = ok(intern_cv(pers, &mut st, c));
        let fe: IFEnv = mk_ifenv(crate::arena::env::IEnv { consts: cs });
        ok(crate::arena::decl_check::std_axiom_ok(pers, fe.visible_below, &mut st, &fe, &icv))
    }

    /// The expected answers are what the `Expr`-tree reference implementation
    /// (`kernel::std_axioms`, deleted by task #105) gave on the same inputs,
    /// which this test used to compare against.
    #[test]
    fn std_axiom_ok_answers() {
        assert_eq!(std_axiom(&cv(cstd::propext_name(), Vec::new(), expr::sort(level::zero()))), false);
        assert_eq!(std_axiom(&cv(cstd::choice_name(), Vec::new(), expr::sort(level::zero()))), false);
        assert_eq!(std_axiom(&cv(nm("x"), Vec::new(), nat_ty())), false);
    }

    /// The arena's `matchesPin`.
    fn matches_pin(c: &ConstantVal, pin: &ConstantVal) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let a = ok(intern_cv(pers, &mut st, c));
        let b = ok(intern_cv(pers, &mut st, pin));
        ok(i_constant_val_matches_pin(pers, &st, &a, &b))
    }

    /// On an identical term, one that differs in its type, one that differs
    /// only in a binder's `pw` datum (which the comparison forgives), and one
    /// that differs in its level parameters.  Expected answers as in
    /// `std_axiom_ok_answers`.
    #[test]
    fn matches_pin_answers() {
        let two = nm("two");
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), nat_ty()),
            &cv(name::dup(&two), Vec::new(), nat_ty())
        ), true);
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), nat_ty()),
            &cv(name::dup(&two), Vec::new(), expr::sort(level::zero()))
        ), false);
        assert_eq!(matches_pin(
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
        ), true);
        let mut lps: Vec<Name> = Vec::with_capacity(1);
        lps.push(nm("u"));
        assert_eq!(matches_pin(
            &cv(name::dup(&two), lps, nat_ty()),
            &cv(name::dup(&two), Vec::new(), nat_ty())
        ), false);
    }

    /// The arena's `canonEqList`.
    fn canon_list(xs: &Vec<ConstantInfo>, ys: &Vec<ConstantInfo>) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let a = ok(intern_ci_list(pers, &mut st, xs));
        let b = ok(intern_ci_list(pers, &mut st, ys));
        ok(crate::arena::canon::canon_eq_list(pers, &mut st, &a, &b, 0))
    }

    /// On the pinned blocks and on a block that is not one.  Expected answers
    /// as in `std_axiom_ok_answers`.
    #[test]
    fn canon_eq_list_answers() {
        let nat = basis_raw::basis_kind_decls(&BasisKind::NatK);
        let eq = basis_raw::basis_kind_decls(&BasisKind::EqK);
        assert_eq!(canon_list(&nat, &basis_raw::basis_kind_decls(&BasisKind::NatK)), true);
        assert_eq!(canon_list(&eq, &basis_raw::basis_kind_decls(&BasisKind::EqK)), true);
        assert_eq!(canon_list(&eq, &nat), false);
        assert_eq!(canon_list(
            &crate::kernel::basis_tables::basis_decls_a(&BasisKind::EqK),
            &eq
        ), false);
    }

    /// The arena's `basisPinHit`, as the kind's ordinal (`None` as 9).
    fn pin_hit(block: &Vec<ConstantInfo>) -> u8 {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let b = ok(intern_ci_list(pers, &mut st, block));
        match ok(basis_pin_hit(pers, &mut st, &b)) {
            None => 9,
            Some(BasisKind::EqK) => 0,
            Some(BasisKind::NatK) => 1,
            Some(BasisKind::EmptyK) => 2,
            Some(BasisKind::FalseK) => 3,
            Some(BasisKind::QuotK) => 4,
        }
    }

    /// The raw blocks hit their own kind; the quotient package is not a block
    /// pin (its records arrive one at a time) and neither is nothing.
    /// Expected answers as in `std_axiom_ok_answers`.
    #[test]
    fn basis_pin_hit_answers() {
        assert_eq!(pin_hit(&basis_raw::basis_kind_decls(&BasisKind::NatK)), 1);
        assert_eq!(pin_hit(&basis_raw::basis_kind_decls(&BasisKind::EqK)), 0);
        assert_eq!(pin_hit(&basis_raw::basis_kind_decls(&BasisKind::QuotK)), 9);
        assert_eq!(pin_hit(&Vec::new()), 9);
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
        let tier = enter_scratch(&mut st);
        let eqn = ok(crate::arena::monad::intern_name(&tier, &mut st, &basis_names::eq_name()));
        assert!(eqn.is_persistent());
        let blk = ok(basis_kind_decls_a(&tier, &mut st, &BasisKind::EqK));
        let mut i: usize = 0;
        while i < blk.len() {
            let cvv = ok(crate::arena::env::i_constant_info_to_constant_val(
                &tier,
                &mut st.store,
                &blk[i],
            ));
            assert!(cvv.ty.is_persistent());
            i += 1;
        }
        assert_eq!(st.store.pers_count(&tier), n0);
        drop_scratch(&mut st, tier);
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
