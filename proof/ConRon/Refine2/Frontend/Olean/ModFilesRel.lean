/-
# `ConRon.Refine2.Frontend.Olean.ModFilesRel` — the relations of the file tier

**Task #142, Theorem 2.**  `ModFilesRel`: the files of a module against upstream's
`ModFiles`, with `PartFits` on every part.  `AS`: the judgement of a function that reaches a
file read.  A failing read of the instance claims nothing of the twin (`FsRel`), so such a
function claims its accept only: `Ok` in the Rust is a run of the twin, in related states,
and an `Err` claims nothing.
-/
import ConRon.Refine2.Frontend.Olean.Parts
import ConRon.Refine2.Frontend.Olean.FsRel
import ConRon.Refine2.Frontend.Olean.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena

/-- **The files of a module, as upstream's**, every part as `part_of_bytes` leaves it. -/
structure ModFilesRel (f : frontend.olean.view.ModFiles) (f' : ConLeche.Frontend.Olean.ModFiles) :
    Prop where
  exported : f'.exported = absPart f.exported
  server : f'.server = f.server.map absPart
  «private» : f'.private = f.private_part.map absPart
  fitsE : PartFits f.exported
  fitsS : ∀ p, f.server = some p → PartFits p
  fitsP : ∀ p, f.private_part = some p → PartFits p

/-- **The accept of a function that reaches a file read**: the Rust's `Ok` over `st.store` is
a run of the twin, in related states.  An `Err` claims nothing. -/
def AS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore))
    (x : AM β) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ a s', m = ok (.Ok a, s') →
      ∃ b lst', x.run lst = .ok (b, lst') ∧ R a b ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')

end ConRon.Refine2.Frontend.Olean
