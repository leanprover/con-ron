//! `arena::fenv` — the indexed environment's guard twins.
//!
//! The Rust twin of `proof/ConRon/Arena/FEnv.lean`, which is itself the
//! seven `F`-suffixed NAMES of `ConLeche/Kernel/FEnv.lean` and nothing else.
//!
//! con-leche's `FEnv.lean` is fourteen declarations: the indexed environment
//! `FEnv` and its five operations, and the seven `F`-suffixed guard twins that
//! read the environment *through the index* rather than through the
//! association list.  **The arena splits them the other way round**, and this
//! module records why:
//!
//! * the environment half — `IFEnv`, `mk_ifenv_go`, `mk_ifenv`, `ifenv_find`,
//!   `ifenv_restrict_to`, `ifenv_push`, `ifenv_find_proj` — is `arena::env`'s
//!   (task #97e), because the arena has ONE environment type and the
//!   declaration layer is where it belongs;
//! * the guard half is `arena::core`'s, as the ONE twin of each con-leche PAIR
//!   (`natLitSupported` / `natLitSupportedF`, and its six siblings).
//!   con-leche needs two spellings because its kernel tier reads `Env` and its
//!   `Cached` tier reads `FEnv`; the arena's checker reads `IFEnv` and nothing
//!   else (DESIGN.md §8.3, lesson 13), so the two collapse.
//!
//! The import order forces the split: con-leche's `FEnv.lean` imports
//! `Core.lean`, while the arena's `Core.lean` has to CALL the guards from
//! inside `whnfCoreBody` and `inferBody`.  So the bodies are where the guards
//! must be defined, and what is left for this module is the seven `F`-suffixed
//! NAMES — which P4d, the census and anyone reading con-leche's `Cached` tier
//! beside the arena will look for.  The twin makes them `abbrev`s, so that
//! they are the same function and no second definition exists to drift; the
//! Rust makes them one-line delegations, which is the same thing after
//! inlining.

use crate::arena::core;
use crate::arena::env::IFEnv;
use crate::arena::handle::{LsIdx, NIdx};
use crate::arena::monad::AState;
use con_ron_core::kernel::core_types::CheckError;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/FEnv.lean:97-99 FEnv.towerSlotsAllF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:38-39 IFEnv.towerSlotsAllF` —
/// `towerSlotsAll` through the index; the arena's `tower_slots_all` already is
/// that (see the module note).
pub fn ifenv_tower_slots_all_f(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n_f: u64,
) -> Result<bool, CheckError> {
    core::tower_slots_all(pers, st, fe, t, n_f)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:101-103 FEnv.andRescueSlotsF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:43-45 IFEnv.andRescueSlotsF` —
/// `andRescueSlots` through the index.
pub fn ifenv_and_rescue_slots_f(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ctor: &NIdx,
    n_p: u64,
    ust: &LsIdx,
) -> Result<bool, CheckError> {
    core::and_rescue_slots(pers, st, fe, ctor, n_p, ust)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:105-110 FEnv.recSlotsAllF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:49-50 IFEnv.recSlotsAllF` —
/// `recSlotsAll` through the index.
pub fn ifenv_rec_slots_all_f(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n_f: u64,
) -> Result<bool, CheckError> {
    core::rec_slots_all(pers, st, fe, t, n_f)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:116-119 natLitSupportedF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:54 natLitSupportedF` —
/// `natLitSupported` through the index.
pub fn nat_lit_supported_f(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    core::nat_lit_supported(pers, st, fe)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:121-130 strLitSupportedF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:58 strLitSupportedF` —
/// `strLitSupported` through the index.
pub fn str_lit_supported_f(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    core::str_lit_supported(pers, st, fe)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:62 natOpGuardF` — `natOpGuard`
/// through the index.
pub fn nat_op_guard_f(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    core::nat_op_guard(pers, st, fe, c)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF
/// Lean twin: `proof/ConRon/Arena/FEnv.lean:66 natOpStoredF` — `natOpStored`
/// through the index (con-leche's task #161 item B3).
pub fn nat_op_stored_f(fe: &IFEnv, c: &NIdx) -> bool {
    core::nat_op_stored(fe, c)
}
