/-
# `ConRon.Bridge.Frontend.Modeller` — the seam's two promises

DESIGN §8.2 puts the in-process modeller OUTSIDE the verified surface, and
`Arena/Frontend/Types.lean`'s `Modeller` is the one-method seam that says so:

    structure Modeller where
      generate : Ctx → BlockRec → AM (Except String (List IDeclaration))

The original campaign carried exactly two hypotheses about it into
`conron.no_False_declaration` (`proof/ConRon/RefineOld/Main.lean:730-735`):

* `hgen : Frontend.ModellerWF inst g` (`RefineOld/Frontend/Base.lean:154`) —
  *whatever it returns is well formed*;
* `hmr : Frontend.ModellerRefines inst g Frontend.CtxRel`
  (`RefineOld/Frontend/ChunksR.lean:143`) — *when it returns, it returns
  con-leche's own records; when it declines, con-leche declines too*.

This module is those two, transposed from "Rust model vs con-leche" to "twin
vs con-leche".  What changes is only what "well formed" and "is con-leche's"
mean over handles:

| original | here |
|---|---|
| `DeclarationWF d` (the port's own record predicate) | `PersDecl d` **and** the record DENOTES (`Bridge/Checker/Inv.lean`'s `denoteDecls`) |
| `ds.val.map absDeclaration` | `denoteDecls st' hs` |
| `absBlockRec b` | `BlockRecRel st b bP` (`Bridge/Frontend/Rel.lean`) |
| `CtxRel ctx lctx` | `CtxRel st ctx lctx` (the store is a parameter) |

and one thing is ADDED that the original did not need: the seam runs in `AM`,
so it moves the store, and the promise has to say what it does to it —
`StateOK`, `Ext` and the frame (`caches`, `pins`, `scratchOn`).  That is the
shape every `@[spec]` theorem of `Bridge/Specs.lean` has, and it is what lets
a caller compose the seam with the rest of the line's work.

## The one instantiation, and why it is not a hypothesis forever

`Arena/Frontend/InModel.lean`'s `inProcessModeller` **delegates to con-leche's
own generator**: it reads the block back (`denoteBlockRec`), calls
`ConLeche.Frontend.InModel.generate` verbatim, and interns the result
(`internDecls`).  So `ModellerRefines` for it is not a promise about a foreign
program at all — it is the readback/intern exactness of
`Arena/Frontend/Readback.lean`, and `inProcessModeller_refines` below states
it as a theorem rather than an axiom.  `Bridge/Frontend/Capstone.lean` still
takes the two as HYPOTHESES, because the capstone is stated at an arbitrary
`Modeller` (`runPipeline` fixes one, and the assembled letters do not) and
because that is the discipline the original campaign fixed: *a statement about
an unverified argument is a hypothesis of the statement, never an axiom of the
environment*.
-/
import ConRon.Bridge.Frontend.Rel
import ConRon.Arena.Frontend.InModel

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The two promises -/

/-- con-leche: none
`RefineOld/Frontend/Base.lean:154 ModellerWF` — **the seam's first promise**:
every declaration the modeller returns is one the rest of the pipeline can
read — it DENOTES in the store the call leaves behind, and its handles are
PERSISTENT (the parse runs with the scratch tier closed, so a generated record
that were not would vanish at the fold's first `dropScratch`).

This is the clause that discharges `Bridge/Checker/Capstone.lean`'s `hpd` for
the generated half of the stream; the parsed half gets it from the parse. -/
def ModellerWF (md : Modeller) : Prop :=
  ∀ ctx b s hs s', md.generate ctx b s = .ok (.ok hs, s') →
    StateOK s' ∧ Ext s.store s'.store ∧
      (∀ d ∈ hs, PersDecl d) ∧ (denoteDecls s'.store hs).isSome = true ∧
      s'.memos = s.memos ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      s'.store.scratchOn = s.store.scratchOn

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
`RefineOld/Frontend/ChunksR.lean:143 ModellerRefines` — **the seam's second
promise**: at a context and a block that denote con-leche's, the modeller's
answer is con-leche's answer.  Both signs, as the original: what it RETURNS is
what con-leche's generator returns (up to the denotation), and where it
DECLINES con-leche declines too.

The decline half is what makes the parse's exactness an `iff` at the record
level without a second induction: `installIndD`'s `.declined` verdict is
con-leche's `.declined` verdict, so a stream the twin declines is a stream
con-leche declines, and the capstone's contrapositive ("the twin never
accepts") does not have to reason about coverage at all. -/
def ModellerRefines (md : Modeller) : Prop :=
  ∀ ctx ctxP b bP s o s', CtxRel s.store ctx ctxP → BlockRecRel s.store b bP →
    md.generate ctx b s = .ok (o, s') →
    (∀ hs, o = .ok hs → ∀ dsP, denoteDecls s'.store hs = some dsP →
        ConLeche.Frontend.InModel.generate ctxP bP = .ok dsP) ∧
      (∀ m, o = .error m → ∃ w, ConLeche.Frontend.InModel.generate ctxP bP = .error w)

/-! ## The instantiation the driver runs

`inProcessModeller` cannot disagree with con-leche — it *calls* con-leche —
so both promises are theorems about the readback and the intern rather than
assumptions about a foreign program.  They are stated here and proved where
`Arena/Frontend/Readback.lean`'s exactness is
(`Bridge/Frontend/Shared.lean`). -/

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — **the delegating
modeller keeps the first promise.**

`sorry`: `Arena/Frontend/Readback.lean`'s intern exactness
(`internDecls_run`, `Bridge/Frontend/Shared.lean`) gives the denotation and
the persistence of the generated records in one; the frame conjuncts are
`internExpr`'s, which never writes `caches`, `pins` or the scratch flag.  Task
#97-P3-Frontend's sorry list, item 8. -/
theorem inProcessModeller_wf : ModellerWF inProcessModeller := by
  sorry

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — **the delegating
modeller keeps the second promise**, and this is the one theorem of the tier
that is about a seam rather than about a function: `inProcessModeller` runs
`ConLeche.Frontend.InModel.generate (ctxOf s.store ctx) bP`, so what has to be
shown is that `ctxOf s.store ctx` IS `ctxP` and `denoteBlockRec s.store b` IS
`bP` — the readback is the denotation, which is
`Bridge/Frontend/Shared.lean`'s `denoteEShared_eq` lifted to the block and the
context.

`sorry`: `ctxOf_eq_of_ctxRel` and `denoteBlockRec_eq_of_blockRecRel`
(`Bridge/Frontend/Shared.lean`), then `internDecls_run` for the returned
records.  The context equality is the only part with content: `ctxOf` probes
the name store (`nameHandle?`) where `CtxRel` quantifies over handles that
denote, and the two agree because `denoteN` is injective (DESIGN §8.3's
exactness obligation, `Arena/Denote.lean`'s `denoteN_inj`).  Task
#97-P3-Frontend's sorry list, item 8. -/
theorem inProcessModeller_refines : ModellerRefines inProcessModeller := by
  sorry

/-- con-leche: none — the modeller that declines everything keeps the second
promise only where con-leche declines too, so it is NOT a `ModellerRefines`
and the fact is worth recording: `declineModeller` is the seam's trivial
instantiation for a run with modelling switched off, and a proof about it
would be a proof about a different pipeline.  What it does keep is the first
promise, vacuously — it never returns records. -/
theorem declineModeller_wf : ModellerWF declineModeller := by
  intro ctx b s hs s' h
  injection h with h1
  injection h1 with h2 _
  exact nomatch h2

end ConRon.Bridge.Frontend
