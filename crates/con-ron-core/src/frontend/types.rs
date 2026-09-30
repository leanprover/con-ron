//! `proof/ConRon/Arena/Frontend/Types.lean` — **the frontend's own types over
//! handles** (task #97 P4e part 1).
//!
//! The representation-free half of con-leche's frontend
//! (`ConLeche/Frontend/Export.lean`): the record verdict a declaration record
//! carries out of the parse when it produces no state.
//!
//! **Everything else this module used to hold is gone** (task #105,
//! con-leche's `uniform-inds` merge): the projection rewrite's owner
//! (`ProjRecOwner`, `ConLeche/Frontend/ProjRec.lean`) and the in-process
//! modeller's seam (`BlockRec`, `ModelCtx`, `ConstTable`, `Modeller`,
//! `DeclineModeller`, `wants`, `hintHeight`, `ConLeche/Frontend/InModel*.lean`)
//! were deleted upstream along with the routes they served — every inductive
//! block installs through the kernel's uniform installer now, unconditionally,
//! and `export_c::install_ind_d` needs nothing from either seam.
//!
//! **The error channel.**  con-leche's frontend runs in `abbrev M := Except
//! String` and pairs a failure with the input LINE at the chunk drivers
//! (`Except (CheckError × Nat)`); DESIGN.md §8.4 gives (B) one monad and the
//! twin's census records that "the frontend's own `M` collapses into `AM`".
//! The Rust merges the two arms the same way `con_ron_core::frontend::
//! export_c` does, into one `Result` with two arms
//! ([`export_c::LineErr`](super::export_c::LineErr)); the difference from
//! con-ron-core's is that the message arm carries a whole `CheckError` and not
//! a `Vec<u32>`, because `EStore::intern` can decline with `Native` at the
//! `2^27` cap (DESIGN.md §8.3) and that kind must survive to the exit code.

use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;

// ---------------------------------------------------------------------------
// Record verdicts (`Types.lean:44-59` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/Export.lean:68-76 RecordVerdict
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:39-46 RecordVerdict` —
/// what a declaration record carries out of the parse when it does not produce
/// a state: a positive DECLINE, or a REJECT (the record's redundant fields
/// contradict the block's own declarations).  A message is a `Vec<u32>` of
/// code points (DESIGN.md §3.3), as every Lean `String` is in the port.
pub enum RecordVerdict {
    Declined(Vec<u32>),
    Invalid(Vec<u32>),
}

/// con-leche: ConLeche/Frontend/Export.lean:78-82 RecordVerdict.toError
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:48-53 RecordVerdict.toError`
/// — the checker error a record verdict becomes; the caller pairs it with the
/// line the record was read at.
pub fn record_verdict_to_error(v: RecordVerdict) -> CheckError {
    match v {
        RecordVerdict::Declined(what) => core_types::not_implemented(what),
        RecordVerdict::Invalid(what) => core_types::invalid(what),
    }
}
