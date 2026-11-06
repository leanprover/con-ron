/-
# `ConRon.Refine2.Frontend.Olean.Contract` — what the capstone asks of Theorem 2 at the reader

**Task #142.**  `ReadOleansRefines` is the statement `ConRon/Capstone.lean`'s `.olean` theorems
take of the Rust reader until `read_oleans_refines` proves it: the Rust's accepting read is the
twin's accepting read, on a record of the file system answering as the Rust's instance
(`FsRel`), at the abstracted search path and roots, the result and the state related as
`parse_chunks_refines` relates them.
-/
import ConRon.Refine2.Frontend.Olean.FsRel
import ConRon.Refine2.Frontend.Shape
import ConRon.Arena.Frontend.Olean.Records

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend.Olean

/-- The search path of the command line, as the twin's. -/
def absSearchPath (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) : List System.FilePath :=
  dirs.val.map fun d => ⟨ConRon.Refine.absString d⟩

/-- **Theorem 2 at the reader, as the capstone takes it.**  `read_oleans` is the store's, and the
rest of the state stands still around it. -/
def ReadOleansRefines : Prop :=
  ∀ {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
    {pers : arena.store.PersTier} {rst : arena.monad.AState} {lst : ConRon.Arena.AState}
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {roots : alloc.vec.Vec arena.handle.NIdx}
    {r : frontend.export_c.ParseResultD} {ar' : arena.store.EStore},
    FsRel inst fsv fs → AStateRel₀ pers rst lst → AStateInv pers rst →
    frontend.olean.records.read_oleans inst fsv pers rst.store dirs roots none = ok (.Ok r, ar') →
    ∃ rv lst', Arena.Frontend.Olean.readOleans fs (absSearchPath dirs) (absNIdxArr roots) none lst
        = .ok (.ok rv, lst') ∧ ParseResultDRel r rv ∧
      AStateRel₀ pers { rst with store := ar' } lst' ∧ AStateInv pers { rst with store := ar' }

end ConRon.Refine2.Frontend.Olean
