/-
# `ConRon.Bridge.Frontend.Chunks` — **the parser's exactness**

DESIGN §8.2's parser tier, in full:

    denoteDecls (Arena.parse chunks) = parseChunks chunks

Five theorems get there, in the order `Arena/Frontend/ExportC.lean` defines
the functions: `applyFinalLine`, `feedChunk`, `chunkStep`, `chunkFinish`,
`parseChunks` — with `parseBytes` beside them, because the prelude is parsed
by `parseBytes` and not by `parseChunks`.

## What is NOT here, and why that is the point

**The scanner.**  `Arena/Frontend/ExportC.lean` imports
`ConLeche.Frontend.Scan.Fast` and calls `scanLineFwd` — con-leche's own
function on con-leche's own `ByteArray`, returning con-leche's own `LineRec`.
There is no twin, so there is nothing to relate: where the original campaign
needed five files and ~15 000 lines (`RefineOld/Frontend/Scan{Kit,Str,Obj,
Expr,Ind,Line}.lean`, plus `Utf8DecodeSpec` and `UnescapeSpec` as named
obligations), this tier needs **zero**.  That is the single largest saving of
the arena rewrite's proof, and it is a consequence of (B) being Lean: a Lean
twin may CALL con-leche where a Rust port must re-implement.

**The chunks.**  `Arena.Frontend.parseChunks` takes `List ByteArray` and so
does con-leche's, byte for byte — so there is no `absChunks`
(`RefineOld/Frontend/Abs.lean:438`) either, and the capstone's hypothesis is
literally `ConLeche.jsonWithTheoremFalse chunks`.  The second saving, and the
reason the byte-level capstone is a two-step composition rather than a
transport across an abstraction.

**The error channel.**  Both sides carry `Except (CheckError × Nat)` for the
two failures that are VALUES (a scan error, a record verdict), and the twin's
`CheckError` is con-leche's own type — `Arena/Frontend/Types.lean` says the
frontend's `M` collapses into `AM` and nothing else moves.  So there is no
`absErrKind`/`ParseErrSim` (`RefineOld/Frontend/ChunksR.lean:226`) either; the
theorems are one-directional (twin accepts ⇒ con-leche accepts) and a twin
failure claims nothing, which is all the capstone needs.

## The one escape hatch

con-leche writes `parseChunks`'s fold as a `where go`; the twin writes it as
the top-level `parseChunksGo`, because "the arena's Rust twin is a loop of its
own and a `where` clause has no name to cite"
(`Arena/Frontend/ExportC.lean`).  `parseChunksC` below is con-leche's `go`
respelled at the top level with `parseChunks_eq` as its `rfl` equation —
`RefineOld/Frontend/ChunksR.lean:673`'s `parseBytesFinal`/`parseBytes_eq`
pattern, for the same reason.
-/
import ConRon.Bridge.Frontend.Lines

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The escape hatch -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:895-901 parseChunks.go — the
streaming fold, respelled at the top level so the twin's `parseChunksGo` has
a named original to be stated against. -/
def parseChunksC (st : ConLeche.Frontend.StateD) (carry : ByteArray)
    (lineNo total : Nat) :
    List ByteArray → Except (ConLeche.CheckError × Nat) ConLeche.Frontend.ParseResultD
  | [] => ConLeche.Frontend.chunkFinish st carry lineNo
  | c :: cs =>
    match ConLeche.Frontend.chunkStep st carry lineNo total c with
    | .error e => .error e
    | .ok (st, carry, lineNo, total) => parseChunksC st carry lineNo total cs

/-- con-leche: ConLeche/Frontend/ExportC.lean:895-901 parseChunks.go — the
respelling is the original, step for step.  A list induction whose step is
`rfl` on both sides: `where go` and a top-level `def` with the same clauses
are the same function, and only Lean's equation compiler stands between
them. -/
theorem parseChunksC_eq (st : ConLeche.Frontend.StateD) (carry : ByteArray)
    (lineNo total : Nat) (cs : List ByteArray) :
    ConLeche.Frontend.parseChunks.go st carry lineNo total cs
      = parseChunksC st carry lineNo total cs := by
  induction cs generalizing st carry lineNo total with
  | nil => rfl
  | cons c cs ih =>
    simp only [ConLeche.Frontend.parseChunks.go, parseChunksC]
    split <;> simp_all

/-- con-leche: ConLeche/Frontend/ExportC.lean:891-893 parseChunks — the entry
point at the respelling. -/
theorem parseChunks_eq (chunks : List ByteArray) (im ce : Bool) :
    ConLeche.Frontend.parseChunks chunks im ce
      = parseChunksC (.init im ce) .empty 0 0 chunks :=
  parseChunksC_eq _ _ _ _ _

/-! ## The initial state -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:757 StateD.init — **the two
tables start related**: index 0 of the name table is the handle
`Name.anonymous` interns at and index 0 of the level table the handle
`Level.zero` interns at, which is `IdTableRel.singleton` at
`Bridge/Specs.lean`'s `internNNode_spec` / `internLNode_spec`.

`sorry`: two intern specs and `IdTableRel.singleton`; every other field is
the structure's default on both sides, so `MapRel` of two empty maps and
`denoteDeclArray` of the empty array are `rfl`-level.  Task #97-P3-Frontend's
sorry list, item 15. -/
theorem StateD_init_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {im ce : Bool} {sd : StateD}
    (hrun : StateD.init im ce s = .ok (sd, s')) :
    ParseStep s s' ∧ PersStateD sd ∧
      StateDRel s'.store sd (ConLeche.Frontend.StateD.init im ce) := by
  sorry

/-! ## The line feed -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:767-768 applyFinalLine — the
stream's last line, the one no newline ends.  The scanner is con-leche's own
call on both sides, so the only step with content is `applyLine`.

`sorry`: `cases` on `scanLineFwd`'s answer — the same value on both sides —
and `applyLine_run` in the `.ok` arm.  Task #97-P3-Frontend's sorry list,
item 16. -/
theorem applyFinalLine_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {b : ByteArray} {i : USize} {lineNo : Nat}
    (hrun : applyFinalLine md sd b i lineNo s = .ok (.ok sd', s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.applyFinalLine sc b i lineNo = .ok sc' ∧
        StateDRel s'.store sd' sc' := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:787-788 feedChunk — **every
complete line of a buffer, applied in order**: the state, the line count and
where the incomplete tail begins.  The three numbers are `Nat`/`USize` on both
sides and must come out EQUAL, not merely related — they are the fold's own
bookkeeping and the next chunk's input.

`sorry`: the loop's strong induction on `b.size - i.toNat` (the twin's own
`termination_by`), with `applyLine_run` at the step and the two guards —
`scanLineFwd`'s verdict and `newlineFrom` — evaluated once and shared, since
both sides call con-leche's functions on the same bytes.  Task
#97-P3-Frontend's sorry list, item 16 — **the tier's second critical path**,
after `processLineCoreD_run`. -/
theorem feedChunk_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {b : ByteArray} {i : USize} {lineNo lineNo' : Nat}
    {tail : USize}
    (hrun : feedChunk md sd b i lineNo s = .ok (.ok (sd', lineNo', tail), s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.feedChunk sc b i lineNo
          = .ok (sc', lineNo', tail) ∧ StateDRel s'.store sd' sc' := by
  sorry

/-! ## The chunk drivers -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:857-858 chunkStep — one chunk:
the carried tail in front, every complete line fed, the new tail cut off.  The
carry, the line count and the running total come out equal, as `feedChunk`'s
do.

`sorry`: the size guard (`total + buf0.size ≥ USize.size`, the same test on
both sides), the `carry ++ buf0` concatenation (the same `ByteArray` on both
sides — the twin does not abstract bytes) and `feedChunk_run`.  Task
#97-P3-Frontend's sorry list, item 17. -/
theorem chunkStep_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd sd' : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {carry carry' : ByteArray} {lineNo total : Nat}
    {buf0 : ByteArray} {lineNo' total' : Nat}
    (hrun : chunkStep md sd carry lineNo total buf0 s
      = .ok (.ok (sd', carry', lineNo', total'), s')) :
    ParseStep s s' ∧ PersStateD sd' ∧
      ∃ sc', ConLeche.Frontend.chunkStep sc carry lineNo total buf0
          = .ok (sc', carry', lineNo', total') ∧ StateDRel s'.store sd' sc' := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:868-869 chunkFinish — the end of
the stream: the carried tail, if any, is its last line.

`sorry`: `applyFinalLine_run` and `ParseResultRel.ofState`.  Task
#97-P3-Frontend's sorry list, item 17. -/
theorem chunkFinish_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {carry : ByteArray} {lineNo : Nat} {r : ParseResultD}
    (hrun : chunkFinish md sd carry lineNo s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, ConLeche.Frontend.chunkFinish sc carry lineNo = .ok rc ∧
        ParseResultRel s'.store r rc := by
  sorry

/-! ## The two entry points -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:831-832 parseBytes — the whole
input fed at once, then the last line.  **This is the prelude's parse**
(`Arena/Frontend/Prelude.lean`'s `builtinPreludeE` is `parseBytes` of
`PreludeText.preludeText`), so it carries its own statement rather than being
a corollary of the chunk fold.

`sorry`: `StateD_init_run`, `feedChunk_run`, `applyFinalLine_run`.  Task
#97-P3-Frontend's sorry list, item 18. -/
theorem parseBytes_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {b : ByteArray} {im ce : Bool}
    {r : ParseResultD} (hrun : parseBytes md b im ce s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, ConLeche.Frontend.parseBytes b im ce = .ok rc ∧
        ParseResultRel s'.store r rc := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:895-901 parseChunks.go — the
streaming fold, step by step.

`sorry`: the list induction, with `chunkStep_run` at the step and
`chunkFinish_run` at the end; `ParseStep.trans` carries the frame and
`StateDRel.ext` carries the relation past each step's appends.  Task
#97-P3-Frontend's sorry list, item 18. -/
theorem parseChunksGo_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    (hp : PersStateD sd) {carry : ByteArray} {lineNo total : Nat}
    {chunks : List ByteArray} {r : ParseResultD}
    (hrun : parseChunksGo md sd carry lineNo total chunks s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, parseChunksC sc carry lineNo total chunks = .ok rc ∧
        ParseResultRel s'.store r rc := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:891-893 parseChunks —
**DESIGN §8.2'S PARSER STATEMENT**: the twin's streaming parse denotes
con-leche's, record for record.

`Bridge/Checker/Capstone.lean`'s two frontend obligations are its two
conclusions: `denoteDecls s'.store r.decls.toList = some rc.decls.toList` is
the `decls` clause of `ParseResultRel` (which is what `denoteDeclArray` is),
and `PersParseResult r` is `∀ x ∈ ds, PersDecl x`.

`sorry`: `StateD_init_run` and `parseChunksGo_run` through `parseChunks_eq`.
Task #97-P3-Frontend's sorry list, item 18. -/
theorem parseChunks_run {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {chunks : List ByteArray} {im ce : Bool}
    {r : ParseResultD}
    (hrun : parseChunks md chunks im ce s = .ok (.ok r, s')) :
    ParseStep s s' ∧ PersParseResult r ∧
      ∃ rc, ConLeche.Frontend.parseChunks chunks im ce = .ok rc ∧
        ParseResultRel s'.store r rc := by
  sorry

/-- con-leche: ConLeche/Frontend/ExportC.lean:891-893 parseChunks — **the
exactness equation, at its letter.**  DESIGN §8.2 writes the parser tier as
`denoteDecls (Arena.parse chunks) = parseChunks chunks`, and this is that
sentence with the `Option` the readback needs and the state the `AM` threads:
*the declarations the twin parsed denote, and what they denote is exactly the
declarations con-leche parsed.*

The record count travels with it — `ParseResultRel.genRecords` is
`r.genRecords = rc.genRecords`, which is what `Arena/Main.lean`'s verdict
number (`r.decls.size - r.genRecords`) is read off — so DESIGN §8.2's "and
the same for the record count / `genRecords`" is this corollary's second
conjunct. -/
theorem parseChunks_exact {md : Modeller} (hmw : ModellerWF md)
    (hmr : ModellerRefines md) {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {chunks : List ByteArray} {im ce : Bool}
    {r : ParseResultD}
    (hrun : parseChunks md chunks im ce s = .ok (.ok r, s')) :
    ∃ rc, ConLeche.Frontend.parseChunks chunks im ce = .ok rc ∧
      denoteDecls s'.store r.decls.toList = some rc.decls.toList ∧
      r.decls.size = rc.decls.size ∧ r.genRecords = rc.genRecords ∧
      (∀ d ∈ r.decls, PersDecl d) := by
  obtain ⟨-, hpers, rc, hrc, hrel⟩ := parseChunks_run hmw hmr hok hoff hrun
  have h := hrel.decls
  simp only [denoteDeclArray, Option.map_eq_some_iff] at h
  obtain ⟨xs, hxs, hEq⟩ := h
  have hdec : denoteDecls s'.store r.decls.toList = some rc.decls.toList := by
    rw [hxs, ← hEq]
  have hlen : r.decls.size = rc.decls.size := by
    have hlen := denoteDecls_length _ _ hxs
    rw [← hEq]
    simpa using hlen
  exact ⟨rc, hrc, hdec, hlen, hrel.genRecords, hpers⟩

end ConRon.Bridge.Frontend
