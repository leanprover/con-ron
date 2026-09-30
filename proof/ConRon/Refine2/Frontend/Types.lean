/-
# `ConRon.Refine2.Frontend.Types` — `crates/con-ron-core/src/frontend/types.rs`

**Task #97-P5-Frontend**, shrunk by task #105 (con-leche's `uniform-inds`
merge): the in-process modeller's seam (`BlockRec`, `ModelCtx`, `ConstTable`,
`Modeller`, `DeclineModeller`, `wants`, `hintHeight`) and the projection
rewrite's owner (`ProjRecOwner`) are gone upstream, and with them
`hint_height_refines`, `ctx_tbl_refines`, `ctx_height_refines`,
`ctx_block_refines`, `wants_nested_refines`, `wants_refines` and
`decline_modeller_refines` — every one of them about a Rust item that no
longer exists.  What is left of `types.rs` is `RecordVerdict` and its
`toError`, one statement.

**The one statement is closed**: `record_verdict_to_error` is one `rfl` past
the generated `match`.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend

/-! ## The record verdict -/

/-- **`types::record_verdict_to_error` refines `RecordVerdict.toError`**
(`Arena/Frontend/Types.lean:58-63`).  What is claimed is the KIND: a verdict's
message is a message like any other and the theorem does not read one
(DESIGN §3.1). -/
theorem record_verdict_to_error_refines {v : frontend.types.RecordVerdict}
    {lv : Arena.Frontend.RecordVerdict} {e : kernel.core_types.CheckError}
    (hk : lVerdictKind lv = absVerdictKind v)
    (h : frontend.types.record_verdict_to_error v = ok e) :
    absAErrKind e = lAErrKind lv.toError := by
  rw [frontend.types.record_verdict_to_error.eq_def] at h
  cases v <;> cases lv <;> simp [lVerdictKind, absVerdictKind] at hk <;>
    simp only [kernel.core_types.not_implemented, kernel.core_types.invalid,
      Result.ok.injEq] at h <;> subst h <;>
    simp [Arena.Frontend.RecordVerdict.toError, absAErrKind, lAErrKind]

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.Frontend.record_verdict_to_error_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms record_verdict_to_error_refines

end ConRon.Refine2.Frontend
