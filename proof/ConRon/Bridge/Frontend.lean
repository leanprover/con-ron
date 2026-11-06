/-
# `ConRon.Bridge.Frontend` — Theorem 1's FRONTEND tier

DESIGN §8.2's parser statement and the byte-level capstone:

    denoteDecls (Arena.parse chunks) = parseChunks chunks        (exactness)
    a file that declares a theorem of type `False` is rejected   (the letter)

The modules, in dependency order:

* `Bridge/Frontend/Rel.lean` — the parse-state relation (`StateDRel`,
  `ParseResultRel`, `PersStateD`), the three generic shapes it is built from
  (`OptRel`, `ListRel`, `IdTableRel`), the transport that carries
  it across an append (`StateDRel.ext`) and the parse's frame
  (`ParseStep`);
* `Bridge/Frontend/Shared.lean` — the intern direction;
* `Bridge/Frontend/Lines.lean` — one scanned line, applied: the three entry
  parsers, the declaration records, `processLineCoreD` and `applyLine`;
* `Bridge/Frontend/Chunks.lean` — **the parser's exactness**: `feedChunk`,
  `chunkStep`, `chunkFinish`, `parseBytes`, `parseChunks`;
* `Bridge/Frontend/Prepare.lean` — the two permuting passes and the prelude;
* `Bridge/Frontend/Capstone.lean` — **`no_False_theorem_accepted_pure`**,
  the letter at the pure fold (a stream that declares a theorem of type
  `False` is never accepted), with the stream lemmas `ConRon/Capstone.lean`'s
  byte-level capstones are assembled from;
* `Bridge/Frontend/Axioms.lean` — the trust census;
* `Bridge/Frontend/Olean/*` — **the `.olean` reader**, on the record of one file system snapshot
  (`modelFs`): `Nodes`, `Fast`, `Read`, `Parse` (a view is the specification's `decodeModuleSpec`),
  `Files`, `Closure` (the reads, `closureOrder`, the lazy load `loadAt_run`), `Merge`, `MergeAll`, `EmitRec`, `EmitWalk`,
  `EmitRun`, `Blocks`, `Records` (`readOleans_run`, the whole read).

## What this tier does NOT contain, and why

**A scanner tier.**  `Arena/Frontend/ExportC.lean` imports
`ConLeche.Frontend.Scan.Fast` and calls `scanLineFwd` — con-leche's own
function, on con-leche's own `ByteArray`, returning con-leche's own `LineRec`.
There is no twin, so there is nothing to prove, and no scanner obligation
(`Utf8DecodeSpec`, `UnescapeSpec`) is named.  It is a consequence of (B) being
written in Lean: a Lean twin may CALL con-leche where a Rust port must
re-implement.

**A byte abstraction.**  Chunks are `List ByteArray` on both sides, so there
is no `absChunks`, no `absByte`, no `absPos`, and the capstone's hypothesis is
literally `ConLeche.jsonWithTheoremFalse chunks`.

**An error abstraction.**  `CheckError` is con-leche's own type in the twin,
so there is no `absErrKind` and no `ParseErrSim`: every theorem here is
one-directional — *the twin accepting implies con-leche accepting* — which is
the only direction the capstone consumes, and a twin failure claims nothing,
exactly as `Bridge/Checker`'s arms claim nothing about a `native` decline.

## The import rule

`Bridge/Frontend/Capstone.lean` adds **two** imports to the library's rule:
con-leche's `Semantics/Bridge/DeclRun` and `Model/Fold`, for
`Semantics.declThmRun_of` and `Model.no_proof_of_False_pure`.  Both are
prebuilt in con-leche's `.lake`, so neither costs elaboration.
-/
module

public import ConRon.Bridge.Frontend.Rel
public import ConRon.Bridge.Frontend.Shared
public import ConRon.Bridge.Frontend.Lines
public import ConRon.Bridge.Frontend.Chunks
public import ConRon.Bridge.Frontend.Prepare
public import ConRon.Bridge.Frontend.Capstone
public import ConRon.Bridge.Frontend.Axioms
public import ConRon.Bridge.Frontend.Olean.Records

public section
