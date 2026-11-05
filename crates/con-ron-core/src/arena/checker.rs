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
//!   record, guarding its header and its value but not inferring, and pushes an
//!   inductive block as stored (`inductives::stored_install`); phase B runs the
//!   jobs, in fold order: each recorded declaration's check against the PREFIX
//!   VIEW it was installed at, and each block's checked install, compared with
//!   its stored pushes (`block_check`).  con-leche proves the two are the same
//!   accept (`fullyChecked_checkDecls`); the arena's two call the same
//!   `checkDecl` pieces, which is what keeps them the same computation.
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
//! `check_decls_pure`'s step, `check_decl_step`, is bracketed the same way.  An
//! inductive block's stored install has brackets of its own
//! (`inductives::stored_install`'s note).
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
    IProjTable,
};
use crate::arena::inductives::stored_install;
use crate::arena::handle::EIdx;
use crate::arena::monad::{fail, AState};
use crate::arena::nat_op_pin_set::{intern_pin_sets, INatOpPinSet};
use crate::arena::promote::{promote_new, promote_vg, scratch_restore, scratch_save, PMemo, ScratchFrame};
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

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"inductive block : the stored install's constants or tables are not the checked install's"`, as code points — the cited message with the block's name dropped
/// (§3.1); the verdict line names the record.
pub const M_PUSHES_DIFFER: [u32; 88] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 58, 32, 116, 104, 101, 32, 115, 116, 111, 114, 101, 100, 32, 105, 110, 115, 116, 97, 108, 108, 39, 115, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 111, 114, 32, 116, 97, 98, 108, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 101, 32, 99, 104, 101, 99, 107, 101, 100, 32, 105, 110, 115, 116, 97, 108, 108, 39, 115
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"check phase: no such block check"`, as code points.
pub const M_NO_BLOCK_CHECK: [u32; 32] = [
    99, 104, 101, 99, 107, 32, 112, 104, 97, 115, 101, 58, 32, 110, 111, 32, 115, 117, 99, 104, 32, 98, 108, 111, 99, 107, 32, 99, 104, 101, 99, 107
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"check phase: no such record"`, as code points.
pub const M_NO_RECORD: [u32; 27] = [
    99, 104, 101, 99, 107, 32, 112, 104, 97, 115, 101, 58, 32, 110, 111, 32, 115, 117, 99, 104, 32, 114, 101, 99, 111, 114, 100
];

// ---------------------------------------------------------------------------
// The pinned basis install (`Checker.lean:65-78` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:464-474 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:42-53 checkBasisDecl` —
/// **install the pinned (stored) basis block.**  The three records that
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

/// con-leche: ConLeche/Kernel/Checker.lean:464-474 checkBasisDecl
/// Lean twin: `proof/ConRon/Arena/CheckDecl.lean:42-53 checkBasisDecl` — the
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
        Ok(decls) => install_basis_decls(pers, fe, &decls, 0),
    }
}

// ---------------------------------------------------------------------------
// The two-phase fold the binary runs (`Checker.lean:210-341` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Installed.lean:91-99 PendingCheck
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-132 PendingCheck` — a
/// phase-A record awaiting its phase-B check: the datum that crosses the
/// install/check seam, the fold position of the declaration (its error tag) and
/// the environment counter at the install.
pub struct PendingCheck {
    pub vg: ValueGroup,
    pub pos: u64,
    pub vis: u64,
}

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — phase
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

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:174-231 installStep` — **phase
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
/// persistent, run on **exactly what leaves the step**: the `k` constants and
/// the `kt` projection tables the step installed (`promote_new`) and the
/// pending record (`promote_vg`, at the
/// SAME memo).  A persistent handle promotes to itself, so a record that
/// installs what the parse already built — every value kind since task #119,
/// whose install half interns nothing — pays a tier-bit test and a decode per handle.  The flush stays where con-leche puts it, at the head
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
    let nt: u64 = fe.env.tables.len() as u64;
    flush_caches(st);
    let mut tier: PersTier = enter_scratch(st);
    let saved: ScratchFrame = scratch_save(st);
    match install_step_go(&tier, st, mode, pins, fe, pd) {
        Err(e) => {
            drop_scratch(st, tier);
            Err(e)
        }
        Ok((fe2, vg_opt)) => {
            scratch_restore(st, saved);
            let k: u64 = fe2.visible_below - vis;
            let kt: u64 = fe2.env.tables.len() as u64 - nt;
            match vg_opt {
                None => match promote_new(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, k, kt, fe2) {
                    Err(e) => {
                        drop_scratch(st, tier);
                        Err(e)
                    }
                    Ok((_, fe3)) => {
                        drop_scratch(st, tier);
                        Ok((fe3, pend))
                    }
                },
                Some(vg) => install_step_promote(tier, st, i, vis, k, kt, fe2, pend, vg),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:174-231 installStep` — the
/// bracket's `some vg` arm: the seam promoted first and the environment at the
/// SAME memo, then the tier dropped and the record pushed.
#[allow(clippy::too_many_arguments)]
pub fn install_step_promote(
    tier: PersTier,
    st: &mut AState,
    i: u64,
    vis: u64,
    k: u64,
    kt: u64,
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
        Ok((m, vg2)) => match promote_new(&mut tier, st, m, CORE_WALK_FUEL, k, kt, fe) {
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

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — the
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

/// con-leche: ConLeche/Cached/Installed.lean:131-137 installGuardsC
/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — the
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

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — the
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

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — the
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

/// con-leche: ConLeche/Cached/Installed.lean:131-137 installGuardsC
/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — the
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

/// con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC
/// Lean twin: `proof/ConRon/Arena/Checker.lean:134-172 installStepGo` — the
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

/// con-leche: ConLeche/Verify/Cached/Defer.lean:51-57 BlockCheck
/// Lean twin: `proof/ConRon/Arena/Checker.lean:233-244 BlockCheck` — **a block's job of the
/// check phase**: the block, its parameter count, its fold position (the error
/// tag), the counter it was installed at, and what the stored install pushed: the
/// slots `c_lo .. c_hi` of the environment's constants and `t_lo .. t_hi` of its
/// tables.  The twin carries the view it runs at and the pushes as values; here
/// they are the frozen base read below `vis` and a range of it.
pub struct BlockCheck {
    pub block: Vec<IConstantInfo>,
    pub n_p: u64,
    pub pos: u64,
    pub vis: u64,
    pub c_lo: u64,
    pub c_hi: u64,
    pub t_lo: u64,
    pub t_hi: u64,
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:121-127 installStepG
/// Lean twin: `proof/ConRon/Arena/Checker.lean:246-260 installBlockStep` — **phase A's
/// step on an inductive block**: the stored install, whose push ranges the job
/// records.  No value check is recorded: the block's verdict is its job's.  The
/// caches go on the way out too, because a block the recogniser does not read has
/// no bracket: every phase-A step leaves them empty.
#[allow(clippy::too_many_arguments)]
pub fn install_block_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    i: u64,
    fe: IFEnv,
    jobs: Vec<BlockCheck>,
    block: &Vec<IConstantInfo>,
    n_p: u64,
) -> Result<(IFEnv, Vec<BlockCheck>), CheckError> {
    let vis: u64 = fe.visible_below;
    let c_lo: u64 = fe.env.consts.len() as u64;
    let t_lo: u64 = fe.env.tables.len() as u64;
    flush_caches(st);
    match stored_install::stored_install(pers, st, mode, fe, block, n_p) {
        Err(e) => Err(e),
        Ok(fe2) => {
            flush_caches(st);
            let c_hi: u64 = fe2.env.consts.len() as u64;
            let t_hi: u64 = fe2.env.tables.len() as u64;
            let mut d: Vec<BlockCheck> = jobs;
            d.push(BlockCheck {
                block: crate::arena::env::i_constant_infos_dup(block),
                n_p,
                pos: i,
                vis,
                c_lo,
                c_hi,
                t_lo,
                t_hi,
            });
            Ok((fe2, d))
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:179-200 installDeclStep
/// con-leche: ConLeche/Verify/Cached/Defer.lean:108-110 deferredBlock?
/// Lean twin: `proof/ConRon/Arena/Checker.lean:262-297 installDeclStep` — phase
/// A's step with the position carried and the error tagged: a failing step
/// reports the `CheckError` together with `i`, the fold position of the
/// declaration that failed.  An inductive block is installed as stored
/// (`install_block_step`), every other record by its ordinary step.
///
/// **The `And` pin comes first** (con-leche's ANDPIN, `basis::and_pin_ok`): a
/// record that declares `And`, `And.intro` or `And.rec` and is not the
/// toolchain's `And` block is rejected here, whatever its kind, ahead of the
/// kind dispatch and outside the scratch bracket.
///
/// Deviation: the twin hands back the empty state on a failure (it is written as
/// a state function); here the state stays with the caller.
pub fn install_decl_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>),
    pd: &IDeclaration,
) -> Result<(u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>), (CheckError, u64)> {
    let i: u64 = p.0;
    match crate::arena::basis::and_pin_ok(pers, st, pd) {
        Err(e) => Err((e, i)),
        Ok(ok_and) => {
            if ok_and {
                match pd {
                    IDeclaration::IndDecl(block, n_p) => {
                        match install_block_step(pers, st, mode, i, p.1, p.3, block, *n_p) {
                            Err(e) => Err((e, i)),
                            Ok(q) => Ok((i + 1, q.0, p.2, q.1)),
                        }
                    }
                    _ => match install_step(pers, st, mode, pins, i, p.1, p.2, pd) {
                        Err(e) => Err((e, i)),
                        Ok(q) => Ok((i + 1, q.0, q.1, p.3)),
                    },
                }
            } else {
                Err((CheckError::Invalid(code_points(&M_AND_PIN)), i))
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:317-334 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:299-310 installFold` — phase A
/// as a fold over the records, as an index recursion threading the accumulator
/// by value.
pub fn install_fold(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>),
    ds: &Vec<IDeclaration>,
    i: usize,
) -> Result<(u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>), (CheckError, u64)> {
    if i >= ds.len() {
        Ok(p)
    } else {
        match install_decl_step(pers, st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => install_fold(pers, st, mode, pins, q, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:317-334 checkDecls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:299-310 installFold` at `ds.take n`
/// (`phaseAFailure`) — `install_fold` over the records `i .. n`.
#[allow(clippy::too_many_arguments)]
pub fn install_prefix(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    p: (u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>),
    ds: &Vec<IDeclaration>,
    i: usize,
    n: usize,
) -> Result<(u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>), (CheckError, u64)> {
    if i >= ds.len() || i >= n {
        Ok(p)
    } else {
        match install_decl_step(pers, st, mode, pins, p, &ds[i]) {
            Err(e) => Err(e),
            Ok(q) => install_prefix(pers, st, mode, pins, q, ds, i + 1, n),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:258-276 checkPending
/// Lean twin: `proof/ConRon/Arena/Checker.lean:312-328 checkPending` —
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
    let saved: ScratchFrame = scratch_save(st);
    let r: Result<(), CheckError> = check_value_group(pers, pc.vis, st, mode, fe, &pc.vg);
    scratch_restore(st, saved);
    leave_record(st);
    r
}

// ---------------------------------------------------------------------------
// The block jobs, and the check phase's jobs in fold order
// (`ConLeche/Verify/Cached/Defer.lean`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Verify/Cached/Defer.lean:68-70 pushesAgree
/// Lean twin: `proof/ConRon/Arena/Checker.lean:332-339 pushesAgree` — the checked
/// install's pushed constants against the base's slots, from slot `i` of the job's
/// layer on.
pub fn consts_agree(pers: &PersTier, w: &IFEnv, b: &BlockCheck, i: usize) -> bool {
    if i >= w.env.consts.len() {
        true
    } else {
        let s: usize = b.c_lo as usize + i;
        if s < pers.env.env.consts.len()
            && stored_install::i_constant_info_beq_p(&w.env.consts[i], &pers.env.env.consts[s])
        {
            consts_agree(pers, w, b, i + 1)
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:68-70 pushesAgree
/// Lean twin: `proof/ConRon/Arena/Checker.lean:332-339 pushesAgree` — the tables
/// likewise.
pub fn tables_agree(pers: &PersTier, w: &IFEnv, b: &BlockCheck, i: usize) -> bool {
    if i >= w.env.tables.len() {
        true
    } else {
        let s: usize = b.t_lo as usize + i;
        if s < pers.env.env.tables.len() {
            let t: &IProjTable = &pers.env.env.tables[s];
            if stored_install::i_proj_table_beq_p(&w.env.tables[i], t) {
                tables_agree(pers, w, b, i + 1)
            } else {
                false
            }
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:68-70 pushesAgree
/// Lean twin: `proof/ConRon/Arena/Checker.lean:332-339 pushesAgree` — **the checked
/// install pushed what the stored install pushed**: the job's own layer holds
/// exactly its pushes, in install order, and so does the recorded range of the
/// base.
pub fn pushes_agree(pers: &PersTier, w: &IFEnv, b: &BlockCheck) -> bool {
    w.env.consts.len() as u64 == b.c_hi - b.c_lo
        && w.env.tables.len() as u64 == b.t_hi - b.t_lo
        && consts_agree(pers, w, b, 0)
        && tables_agree(pers, w, b, 0)
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:77-84 blockCheck
/// Lean twin: `proof/ConRon/Arena/Checker.lean:341-352 blockCheck` — **the block's job**:
/// its checked install at an empty layer over the frozen base at the block's
/// counter, from fresh caches and an empty scratch tier, and the comparison of
/// its pushes with the stored install's.  A difference is an internal error: the
/// stored reading is not the checked install's, a defect of the reader, not of
/// the stream.  Nothing the job builds outlives it: the tier and the layer go.
pub fn block_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    b: &BlockCheck,
) -> Result<(), CheckError> {
    enter_record(st);
    let saved: ScratchFrame = scratch_save(st);
    let r: Result<IFEnv, CheckError> = crate::arena::check_decl::check_ind_decl(
        pers,
        st,
        mode,
        crate::arena::env::ifenv_layer(b.vis, b.vis),
        &b.block,
        b.n_p,
    );
    scratch_restore(st, saved);
    let v: Result<(), CheckError> = match r {
        Err(e) => Err(e),
        Ok(w) => {
            if pushes_agree(pers, &w, b) {
                Ok(())
            } else {
                fail(CheckError::Internal(code_points(&M_PUSHES_DIFFER)))
            }
        }
    };
    leave_record(st);
    v
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:217-221 blockFailure
/// Lean twin: `proof/ConRon/Arena/Checker.lean:354-362 blockFailure` — **the first failing
/// block job from `i` on**, in fold order, with its position.
pub fn block_failure(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    d: &Vec<BlockCheck>,
    i: usize,
) -> Option<(CheckError, u64)> {
    if i >= d.len() {
        None
    } else {
        match block_check(pers, st, mode, &d[i]) {
            Err(e) => Some((e, d[i].pos)),
            Ok(()) => block_failure(pers, st, mode, d, i + 1),
        }
    }
}

/// con-leche: ConLeche/Driver/ParInstall.lean:690-808 commitLoop
/// Lean twin: `proof/ConRon/Arena/Checker.lean:373-399 phaseAFailure` — **the verdict of a
/// phase A that failed at record `i` with `e`**: the first failing block job before
/// it; else, at a block past its `And` pin, that block's own job (a name was taken,
/// or the store gave out); else `e`.
///
/// The failing step took the environment with it, and the environment is what the
/// jobs read, so the records before `i` are installed once more, on the state the
/// failure left: a step is a function of the index and the record.  Con-leche's
/// commit loop holds its index across the step; a rejection need not be fast, and
/// this keeps the accepting path's index threaded by value.
pub fn phase_a_failure(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    e: CheckError,
    i: u64,
) -> (CheckError, u64) {
    match install_prefix(pers, st, mode, pins, fold_start(), ds, 0, i as usize) {
        Err(e2) => e2,
        Ok(q) => {
            let own: Option<BlockCheck> = phase_a_own_job(pers, st, ds, i, &q.1);
            let tier: PersTier = freeze_tier(&mut st.store, q.1);
            let mut w: AState = worker_state(&st.pins);
            let r: Option<(CheckError, u64)> = match block_failure(&tier, &mut w, mode, &q.3, 0) {
                Some(f) => Some(f),
                None => match own {
                    None => None,
                    Some(b) => match block_check(&tier, &mut w, mode, &b) {
                        Err(e2) => Some((e2, i)),
                        Ok(()) => None,
                    },
                },
            };
            let _ = thaw_tier(&mut st.store, tier);
            match r {
                Some(f) => f,
                None => (e, i),
            }
        }
    }
}

/// con-leche: ConLeche/Driver/ParInstall.lean:690-808 commitLoop
/// Lean twin: `proof/ConRon/Arena/Checker.lean:373-399 phaseAFailure` — the failing record's
/// own job, when it is a block that passed its `And` pin: no pushes recorded, so a
/// checked install that passes is the internal error it should be.
pub fn phase_a_own_job(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
    i: u64,
    fe: &IFEnv,
) -> Option<BlockCheck> {
    if (i as usize) < ds.len() {
        match &ds[i as usize] {
            IDeclaration::IndDecl(block, n_p) => match crate::arena::basis::and_pin_ok(pers, st, &ds[i as usize]) {
                Ok(true) => Some(BlockCheck {
                    block: crate::arena::env::i_constant_infos_dup(block),
                    n_p: *n_p,
                    pos: i,
                    vis: fe.visible_below,
                    c_lo: fe.env.consts.len() as u64,
                    c_hi: fe.env.consts.len() as u64,
                    t_lo: fe.env.tables.len() as u64,
                    t_hi: fe.env.tables.len() as u64,
                }),
                _ => None,
            },
            _ => None,
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:255-276 runJob
/// Lean twin: `proof/ConRon/Arena/Checker.lean:406-424 runJob` — **run a job**: a block job
/// (`j.0`) or a recorded value check, by its index in its array, on a worker's
/// state; the error tagged with its fold position.  `fe` is the empty layer every
/// value check reads the frozen base through.
pub fn run_job(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pend: &Vec<PendingCheck>,
    d: &Vec<BlockCheck>,
    j: &(bool, u64),
) -> Result<(), (CheckError, u64)> {
    if j.0 {
        if (j.1 as usize) < d.len() {
            match block_check(pers, st, mode, &d[j.1 as usize]) {
                Err(e) => Err((e, d[j.1 as usize].pos)),
                Ok(()) => Ok(()),
            }
        } else {
            Err((CheckError::Internal(code_points(&M_NO_BLOCK_CHECK)), 0))
        }
    } else if (j.1 as usize) < pend.len() {
        match check_pending(pers, st, mode, fe, &pend[j.1 as usize]) {
            Err(e) => Err((e, pend[j.1 as usize].pos)),
            Ok(()) => Ok(()),
        }
    } else {
        Err((CheckError::Internal(code_points(&M_NO_RECORD)), 0))
    }
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder
/// Lean twin: `proof/ConRon/Arena/Checker.lean:439-443 jobOrder` — **the jobs in fold order**:
/// the recorded checks and the block checks, each array sorted by position, merged
/// (a block before a record at a larger position).
pub fn job_order(pend: &Vec<PendingCheck>, d: &Vec<BlockCheck>) -> Vec<(bool, u64)> {
    job_order_go(pend, d, 0, 0, Vec::with_capacity(pend.len() + d.len()))
}

/// con-leche: ConLeche/Verify/Cached/Defer.lean:281-292 jobOrder
/// Lean twin: `proof/ConRon/Arena/Checker.lean:426-437 jobOrderGo` — the merge, from
/// positions `a` and `b`.
pub fn job_order_go(
    pend: &Vec<PendingCheck>,
    d: &Vec<BlockCheck>,
    a: usize,
    b: usize,
    acc: Vec<(bool, u64)>,
) -> Vec<(bool, u64)> {
    let mut o: Vec<(bool, u64)> = acc;
    if a < pend.len() {
        if b < d.len() && d[b].pos < pend[a].pos {
            o.push((true, b as u64));
            job_order_go(pend, d, a, b + 1, o)
        } else {
            o.push((false, a as u64));
            job_order_go(pend, d, a + 1, b, o)
        }
    } else if b < d.len() {
        o.push((true, b as u64));
        job_order_go(pend, d, a, b + 1, o)
    } else {
        o
    }
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
//   freeze_tier             the boundary, and the index with it
//   worker_state            a phase-B worker's state over the frozen tier
//   thaw_tier               the boundary undone
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/ParInstall.lean:668-808 commitLoop
/// What the driver prints between phase A's steps (the `--progress`
/// heartbeat's install line), as a trait the verified fold calls: the hook
/// takes the state by SHARED reference and returns nothing, so it cannot
/// change a verdict — `install_fold_hooked` is `install_fold` with a call to it
/// before each step, and `Refine2/Checker/Phased.lean` proves the two equal.
/// `Modeller`'s arrangement (`frontend::types`): the trait is declared here,
/// the implementations live in the unverified crate.
pub trait InstallHook {
    /// con-leche: ConLeche/Driver/ParInstall.lean:668-808 commitLoop
    /// Before record `pos` of `total` is installed.
    fn install_before(&self, pers: &PersTier, ar: &EStore, pos: u64, total: usize, d: &IDeclaration);
}

/// con-leche: ConLeche/Cached/Installed.lean:317-334 checkDecls
/// Lean twin: none — `install_fold` over every record, with the driver's hook; the
/// twin has no hook and the refinement is `install_fold`'s, through the equation
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
    p: (u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>),
    ds: &Vec<IDeclaration>,
    i: usize,
    h: &H,
) -> Result<(u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>), (CheckError, u64)> {
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

/// con-leche: ConLeche/Cached/Installed.lean:317-334 checkDecls
/// Lean twin: none — the fold's start, `(0, mkIFEnv IEnv.empty, #[], #[])`,
/// which `installThenCheck` writes inline.
/// Phase A's starting accumulator, so that the driver builds it with the same
/// call the verified fold does.
pub fn fold_start() -> (u64, IFEnv, Vec<PendingCheck>, Vec<BlockCheck>) {
    (0, mk_ifenv(i_env_empty()), Vec::new(), Vec::new())
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the twin has no tier to move; its phase-B worker reads the
/// persistent tier where it is (`AState.worker`, `Arena/Checker.lean`).
/// **The persistent tier and the installed index out of phase A and into a
/// value**: the four persistent tables and `fe` move into one `PersTier` handed
/// back `frozen`, for the phase-B workers to read (`fe` is what `ifenv_find` reads
/// below an own layer).  A pure MOVE: the store's scratch tiers and flags are
/// untouched (a worker's store is its own, `worker_state`), and `thaw_tier` puts
/// everything back where it was.  The driver's store is not read between the two.
pub fn freeze_tier(ar: &mut EStore, fe: IFEnv) -> PersTier {
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
        env: fe,
    }
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the inverse of `freeze_tier`, which has none either.
/// **`freeze_tier` inverted**: the tables back into the store and the index back
/// to the caller, so that everything after phase B — the verdict line's label,
/// the failing record's name, the receipts — reads the handles it was given.
/// `thaw_tier(ar, freeze_tier(ar, fe))` leaves the store exactly as it found it
/// and answers `fe` (`Refine2/Checker/Phased.lean`'s `freeze_tier_ok`).
pub fn thaw_tier(ar: &mut EStore, tier: PersTier) -> IFEnv {
    ar.lss.ls.ns.pers = tier.n;
    ar.lss.ls.pers = tier.l;
    ar.lss.pers = tier.ls;
    ar.pers = tier.e;
    tier.env
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

/// con-leche: ConLeche/Kernel/FEnv.lean:113-136 FEnv
/// Lean twin: none — the twin's value check reads one environment
/// (`fe.restrictTo pc.vis`).  **The layer every value check reads the frozen base
/// through**: empty, and with no bound of its own (`arena::env::ifenv_layer`).
pub fn check_layer() -> IFEnv {
    crate::arena::env::ifenv_layer(0, u64::MAX)
}

/// con-leche: ConLeche/Driver/CheckPool.lean:213-227 checkWorker
/// Lean twin: `proof/ConRon/Arena/Checker.lean:364-371 AState.worker` — the twin's
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — **the
/// one-time tree walk of DESIGN.md §8.6 P2d**: every datum the checker compares
/// a stream record against, interned into the tier that is live at the call —
/// which, at the driver's call, is the persistent one.
///
/// The five basis blocks in both forms (the RAW ones `basis_pin_hit` and
/// `quot_pin_hit` compare against, the STORED ones `check_basis_decl`
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the five
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the five
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the
/// standard and compiler-trust axiom pins, in the twin's order.
pub fn intern_all_axiom_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::iff_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::iff_intro_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::iff_rec_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::nonempty_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_axiom_pins_rest(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the
/// rest of the axiom pins and the two reduce pins.
pub fn intern_all_axiom_pins_rest(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::nonempty_intro_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::nonempty_rec_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::propext_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::choice_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_trust_pins(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the
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
/// Lean twin: `proof/ConRon/Arena/Checker.lean:490-520 internAllPins` — the
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
    use crate::kernel::expr::Expr;

    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
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
        let fe: IFEnv = mk_ifenv(crate::arena::env::IEnv {
            consts: cs,
            tables: Vec::new(),
        });
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
        i_constant_val_matches_pin(&a, &b)
    }

    /// On an identical term, one that differs in its type, one that differs
    /// in a binder's codomain, and one that differs in its level parameters.  Expected answers as in
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
            &cv(name::dup(&two), Vec::new(), expr::forall_e(nat_ty(), nat_ty())),
            &cv(name::dup(&two), Vec::new(), expr::forall_e(nat_ty(), nat_ty()))
        ), true);
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), expr::forall_e(nat_ty(), nat_ty())),
            &cv(
                name::dup(&two),
                Vec::new(),
                expr::forall_e(nat_ty(), expr::sort(level::zero()))
            )
        ), false);
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
            let cvv = crate::arena::env::i_constant_info_to_constant_val(&blk[i]);
            assert!(cvv.ty.is_persistent());
            i += 1;
        }
        assert_eq!(st.store.pers_count(&tier), n0);
        drop_scratch(&mut st, tier);
    }

    /// **The startup walk at the binary's own pin list**, not the empty one
    /// every check above runs with: the embedded `con-ron-pins/2` text
    /// (`kernel::pins_text::PINS_TEXT`, 26 721 records) decoded and interned
    /// into the persistent tier.  This is the path `run_pipeline` takes and the
    /// one thing about it that could fail quietly — the handle-index cap, or a
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
