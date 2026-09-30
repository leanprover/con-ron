/-
# `ConRon.Arena.Frontend.Types` — the frontend's own types over handles
(DESIGN.md §8, task #97e; task #105 shrinks this to one record)

The representation-free half of con-leche's frontend
(`ConLeche/Frontend/Export.lean`) that survives con-leche's `uniform-inds`
merge (445b9cf4).  Before task #105 this module also carried the
projection-function rewrite's owner (`ProjRecOwner`), the in-process
modeller's resolved block records (`MIndTypeRec`/`MIndCtorRec`/`MIndRecRec`/
`BlockRec`/`ConstTable`/`Ctx`/`hintHeight`/`wants`) and the modeller seam
itself (`Modeller`/`declineModeller`) — all deleted upstream (con-leche's
`Frontend/{InModel*, ProjRec}.lean` are gone) and with them here: every
inductive block, mutual and nested included, now installs through one
uniform kernel installer (`crate::arena::inductives`, the kernel lane's),
so the frontend has nothing left to generate or rewrite.

**The error monad `M` is gone.**  con-leche's frontend runs in
`abbrev M := Except String` and pairs a failure with the input LINE at the
chunk drivers (`Except (CheckError × Nat)`).  DESIGN §8.4 gives (B) one monad,
`AM = StateT AState (Except CheckError)`, and the twins census records that
"the frontend's own `M` collapses into `AM`" as one of the places the
mechanical transliteration rule is knowingly too crude.  So a `throw
s!"undefined name index {i}"` becomes `fail (.internal …)` with the same text
and the same exit code (3), and it is the one thing that loses its line
number: `Arena/Main.lean`'s seam is

    runPipeline : List ByteArray → CheckMode → List NatOpPinSet
                → Except CheckError Nat

which has no position channel at all, so the number would be dropped one
level up in any case.  The chunk drivers below still carry con-leche's
`Except (CheckError × Nat)` for the two failures that are *values* rather
than exceptions — a scan error and a record verdict — and `runPipeline`
folds the line into those messages before returning.
-/
import ConRon.Arena.Env

namespace ConRon.Arena.Frontend

open ConLeche
open ConRon.Arena

/-! ## Record verdicts -/

/-- con-leche: ConLeche/Frontend/Export.lean:68-76 RecordVerdict — what a
declaration record carries out of the parse when it does not produce a state:
a positive DECLINE, or a REJECT (the record's redundant fields contradict the
block's own declarations). -/
inductive RecordVerdict where
  | declined (what : String)
  | invalid (what : String)
  deriving Repr, DecidableEq

/-- con-leche: ConLeche/Frontend/Export.lean:78-82 RecordVerdict.toError — the
checker error a record verdict becomes; the caller pairs it with the line the
record was read at. -/
def RecordVerdict.toError : RecordVerdict → CheckError
  | .declined what => .notImplemented what
  | .invalid what => .invalid what

end ConRon.Arena.Frontend
