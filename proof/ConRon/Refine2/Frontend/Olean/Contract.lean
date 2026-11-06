/-
# `ConRon.Refine2.Frontend.Olean.Contract` — what the capstone asks of Theorem 2 at the reader

**Tasks #142, #143.**  `ReadOleansRefines` is the statement `ConRon/Capstone.lean`'s `.olean`
theorems take of the Rust reader, and `ReadOleans.lean`'s `read_oleans_refines` proves: the
Rust's accepting read is the twin's accepting read, on a record of the file system answering
as the Rust's instance (`FsRel`), at the abstracted search path and roots, the results related
by `OleanReadRel` and the states as `parse_chunks_refines` relates them.

A read's result (upstream task #481) is an `OleanRead`: the records, a theorem's value a
reference into its file; what a theorem's check needs to read it (`values`, a `ModRef` per
module of the closure's order); the merged constants, which `usedOf` reads; and the reader's
pins.  The check-phase read of a value is `ReadValue.lean`'s `read_value_refines`.
-/
import ConRon.Refine2.Frontend.Olean.Merge
import ConRon.Refine2.Frontend.Olean.FsRel
import ConRon.Refine2.Frontend.Shape
import ConRon.Arena.Frontend.Olean.Records

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend.Olean

/-- **`records::ModRef` against the twin's**: the module's name and its frontier. -/
structure ModRefRel (m : frontend.olean.records.ModRef) (m' : Arena.Frontend.Olean.ModRef) :
    Prop where
  «name» : absNIdx m.name = m'.name
  frontier : FrontierRel m.frontier m'.frontier

/-- **`records::OleanRead` against the twin's**: the records, the modules' references, the
merged constants and the reader's pins. -/
structure OleanReadRel (rd : frontend.olean.records.OleanRead)
    (rd' : Arena.Frontend.Olean.OleanRead) : Prop where
  decls : rd.decls.val.map absIDeclaration = rd'.decls.toList
  values : List.Forall₂ ModRefRel rd.values.val rd'.values.toList
  merged : MergedRel rd.merged rd'.merged
  pins : absPins rd.pins = rd'.pins

/-- **Theorem 2 at the reader, as the capstone takes it.**  `read_oleans` is the store's, and the
rest of the state stands still around it. -/
def ReadOleansRefines : Prop :=
  ∀ {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
    {pers : arena.store.PersTier} {rst : arena.monad.AState} {lst : ConRon.Arena.AState}
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {roots : alloc.vec.Vec arena.handle.NIdx}
    {rd : frontend.olean.records.OleanRead} {ar' : arena.store.EStore},
    FsRel inst fsv fs → AStateRel₀ pers rst lst → AStateInv pers rst →
    frontend.olean.records.read_oleans inst fsv pers rst.store dirs roots none = ok (.Ok rd, ar') →
    ∃ rd' lst', Arena.Frontend.Olean.readOleans fs (absSearchPath dirs) (absNIdxArr roots) none lst
        = .ok (.ok rd', lst') ∧ OleanReadRel rd rd' ∧
      AStateRel₀ pers { rst with store := ar' } lst' ∧ AStateInv pers { rst with store := ar' }

end ConRon.Refine2.Frontend.Olean
