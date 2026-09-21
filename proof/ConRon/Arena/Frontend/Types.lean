/-
# `ConRon.Arena.Frontend.Types` — the frontend's own types over handles
(DESIGN.md §8, task #97e)

The representation-free half of con-leche's frontend
(`ConLeche/Frontend/Export.lean`) plus the two records the parse hands to
things it does not own: the projection rewrite's owner
(`ConLeche/Frontend/ProjRec.lean`) and the in-process modeller's block
(`ConLeche/Frontend/InModel/Mutual.lean`).

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

**The in-process modeller is a one-method seam** (DESIGN §8.2's `Modeller`,
the Rust port's unverified hook).  con-leche calls `InModel.generate` directly;
(B) takes a `Modeller` parameter whose single method maps handles to handles.
Two instantiations exist: `declineModeller` below, which declines every block
it is asked about, and `Arena/Frontend/InModel.lean`'s `inProcessModeller`,
which the driver uses — it reads the block back and calls **con-leche's own
generator**, which is exact by construction and unverified by design (a wrong
generated record is rejected or declined by the fold, never accepted; the
generator owns coverage and no soundness).
-/
import ConRon.Arena.Env

namespace ConRon.Arena.Frontend

open ConLeche
open ConRon.Arena

/-! ## Record verdicts -/

/-- con-leche: ConLeche/Frontend/Export.lean:71-79 RecordVerdict — what a
declaration record carries out of the parse when it does not produce a state:
a positive DECLINE, or a REJECT (the record's redundant fields contradict the
block's own declarations). -/
inductive RecordVerdict where
  | declined (what : String)
  | invalid (what : String)
  deriving Repr, DecidableEq

/-- con-leche: ConLeche/Frontend/Export.lean:81-85 RecordVerdict.toError — the
checker error a record verdict becomes; the caller pairs it with the line the
record was read at. -/
def RecordVerdict.toError : RecordVerdict → CheckError
  | .declined what => .notImplemented what
  | .invalid what => .invalid what

/-! ## The projection rewrite's owner -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:83-104 ProjRecOwner — what the
projection-function rewrite needs to know about one structure-like owner `T` of
a parsed inductive block the direct install does not serve.  A field-for-field
mirror; the rewrite that READS it is `Arena/Frontend/ProjRec.lean` (task #97e
part 2). -/
structure ProjRecOwner where
  T : NIdx
  lps : List NIdx
  nP : Nat
  ctor : NIdx
  nF : Nat
  recName : NIdx
  recLps : List NIdx
  recType : EIdx
  numMotives : Nat
  numMinors : Nat
  deriving Repr, Inhabited

/-! ## The in-process modeller's block

con-leche's `InModel` namespace has its own `IndTypeRec`/`IndCtorRec`/
`IndRecRec` — the *resolved* shape records, not the scanner's — so the twins
carry an `M` prefix to keep them apart from `ConLeche.Frontend.IndTypeRec`,
which `Arena/Frontend/ExportC.lean` uses as it is (the scanner is reused, not
twinned). -/

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:81-90 IndTypeRec — one
type former of a parsed block, resolved. -/
structure MIndTypeRec where
  cv : IConstantVal
  nP : Nat
  nIdx : Nat
  ctors : List NIdx
  isRec : Bool
  isReflexive : Bool
  numNested : Nat
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:92-97 IndCtorRec — one
constructor of a parsed block, resolved. -/
structure MIndCtorRec where
  cv : IConstantVal
  nP : Nat
  nF : Nat
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:99-108 IndRecRec — one
recursor of a parsed block, resolved. -/
structure MIndRecRec where
  cv : IConstantVal
  nP : Nat
  nM : Nat
  nm : Nat
  nI : Nat
  rules : List IRecRule
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:110-115 BlockRec — a parsed
inductive block. -/
structure BlockRec where
  types : List MIndTypeRec
  ctors : List MIndCtorRec
  recs : List MIndRecRec
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Frontend/InModel/Kit.lean:368-369 ConstTable — the
declared types of the constants pushed so far, by name. -/
abbrev ConstTable := NIdx → Option (List NIdx × EIdx)

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:117-124 Ctx — what the
generator reads besides the block. -/
structure Ctx where
  tbl : ConstTable
  heights : NIdx → Nat
  blocks : NIdx → Option BlockRec := fun _ => none

/-- con-leche: ConLeche/Frontend/InModel/Kit.lean:522-525 hintHeight — the
definitional height a reducibility hint carries. -/
def hintHeight : ReducibilityHint → Nat
  | .regular n => n
  | _ => 0

/-- con-leche: ConLeche/Frontend/InModel.lean:34-37 wants — is the block one
the modeller is for: mutual (several types) or nested (`numNested > 0`)?  It
reads counts and no term, so it is the same function over handles. -/
def wants (b : BlockRec) : Bool :=
  b.types.length > 1 || b.types.any (·.numNested > 0)

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — **the modeller
seam** (DESIGN §8.2's `Modeller`).  One method: a block in, the model records
it generates in stream order or the reason it is declined.  Handles in,
handles out: the CHECKER never sees an `Expr`, whatever an instantiation does
behind the seam.

The seam is UNVERIFIED by design: soundness needs nothing from it, since a
wrong generated record is rejected or declined by the fold, and its
correctness decides only coverage.  That is what licenses
`Arena/Frontend/InModel.lean`'s instantiation, which reads the block back,
calls con-leche's generator and interns the result: the readback is bounded to
one block, it is exact (it IS the denotation), and the unverified layer it
adds is the layer DESIGN §8.2 already calls unverified. -/
structure Modeller where
  generate : Ctx → BlockRec → AM (Except String (List IDeclaration))

/-- con-leche: none — the modeller that declines every block.  A decline here
is `installIndD`'s `.declined` verdict, naming the block: the same positive
statement con-leche makes when its own generator declines a residual class.
It is no longer what the driver runs (`Arena/Frontend/InModel.lean`'s
`inProcessModeller` is, since task #97e part 2) and is kept as the seam's
trivial instantiation — the one a run with modelling switched off wants, and
the one a proof about the seam is easiest to state at. -/
def declineModeller : Modeller :=
  ⟨fun _ _ => pure (.error "the arena's in-process modeller is not ported yet")⟩

end ConRon.Arena.Frontend
