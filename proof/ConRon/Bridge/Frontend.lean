/-
# `ConRon.Bridge.Frontend` — Theorem 1's FRONTEND tier

DESIGN §8.2's parser statement and the byte-level capstone:

    denoteDecls (Arena.parse chunks) = parseChunks chunks        (exactness)
    a file that declares a theorem of type `False` is rejected   (the letter)

Nine modules, in dependency order:

* `Bridge/Frontend/Rel.lean` — the parse-state relation (`StateDRel`,
  `ParseResultRel`, `PersStateD`), the three generic shapes it is built from
  (`OptRel`, `IdTableRel`, `MapRel`) and the parse's frame (`ParseStep`);
* `Bridge/Frontend/ProjRec.lean` — the projection rewrite and the owner
  census, with the three deviations `Arena/Frontend/ProjRec.lean`'s module
  note records as three theorems;
* `Bridge/Frontend/Shared.lean` — `denoteEShared = denoteE`
  (`Arena/Frontend/Readback.lean`'s own stated obligation) and the intern
  direction;
* `Bridge/Frontend/Modeller.lean` — the seam's two promises (`ModellerWF`,
  `ModellerRefines`), and the delegating instantiation that keeps both;
* `Bridge/Frontend/Lines.lean` — one scanned line, applied: the three entry
  parsers, the declaration records, `processLineCoreD` and `applyLine`;
* `Bridge/Frontend/Chunks.lean` — **the parser's exactness**: `feedChunk`,
  `chunkStep`, `chunkFinish`, `parseBytes`, `parseChunks`;
* `Bridge/Frontend/Prepare.lean` — the two permuting passes and the prelude;
* `Bridge/Frontend/Capstone.lean` — **`Arena.no_False_declaration`**, its
  `_prelude` instance, and `_pipeline` at `Arena/Main.lean`'s one seam;
* `Bridge/Frontend/Axioms.lean` — the trust census.

## What this tier does NOT contain, and why

**A scanner tier.**  `Arena/Frontend/ExportC.lean` imports
`ConLeche.Frontend.Scan.Fast` and calls `scanLineFwd` — con-leche's own
function, on con-leche's own `ByteArray`, returning con-leche's own `LineRec`.
There is no twin, so there is nothing to prove.  The original campaign needed
`RefineOld/Frontend/Scan{WF,Kit,Str,Obj,Expr,Ind,Line}.lean` — seven files,
~16 000 lines, and two standing obligations (`Utf8DecodeSpec`,
`UnescapeSpec`) — for exactly this.  **That is the largest single saving of
the arena rewrite's proof**, and it is a consequence of (B) being written in
Lean: a Lean twin may CALL con-leche where a Rust port must re-implement.

**A byte abstraction.**  Chunks are `List ByteArray` on both sides, so there
is no `absChunks` (`RefineOld/Frontend/Abs.lean:438`), no `absByte`, no
`absPos`, and the capstone's hypothesis is literally
`ConLeche.jsonWithTheoremFalse chunks`.

**An error abstraction.**  `CheckError` is con-leche's own type in the twin,
so there is no `absErrKind` and no `ParseErrSim`
(`RefineOld/Frontend/ChunksR.lean:226`): every theorem here is
one-directional — *the twin accepting implies con-leche accepting* — which is
the only direction the capstone consumes, and a twin failure claims nothing,
exactly as `Bridge/Checker`'s arms claim nothing about a `native` decline.

## The import rule

`Bridge/Frontend/Capstone.lean` adds **two** imports to the library's rule:
`ConRon.Arena.Main` (the seam `runPipeline` lives there, and
`Arena.no_False_declaration_pipeline` is a statement about it) and
`ConLeche.MainTheorem` (for `ConLeche.jsonWithTheoremFalse` and
`ConLeche.Frontend.parseChunks_jsonWithTheoremFalse`, which is con-leche's own
file-level lemma and the one thing this tier may not re-derive).  Both are
prebuilt in con-leche's `.lake`, so neither costs elaboration.
-/
import ConRon.Bridge.Frontend.Rel
import ConRon.Bridge.Frontend.ProjRec
import ConRon.Bridge.Frontend.Shared
import ConRon.Bridge.Frontend.Modeller
import ConRon.Bridge.Frontend.Lines
import ConRon.Bridge.Frontend.Chunks
import ConRon.Bridge.Frontend.Prepare
import ConRon.Bridge.Frontend.Capstone
import ConRon.Bridge.Frontend.Axioms
