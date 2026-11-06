/-
# `ConRon.Refine2.Frontend.Olean.Lazy` — `olean/lazy.rs` against the twin's

**Task #143, Theorem 2** (upstream task #481).  A module's load, its theorems' values left in
the file: what each constant mentions, read off the file (`uses_go`, `uses_roots`, `uses_of`,
`uses_read`), the constants with a theorem's value a reference (`lazy_entry`, `value_ref`),
the frontier (`frontier_walk`, `frontier_of`), and the load around them (`load_at`,
`load_view`).  The two walks carry fuel on both sides (the twin's `Arena/Frontend/Olean/
Lazy.lean` note); a stack is a `Vec` and its top against a `List` (`StackRel`).
-/
import ConRon.Refine2.Frontend.Olean.Sparse
import ConRon.Refine2.Frontend.Olean.Closure
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Arena.Frontend.Olean.Lazy

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.lazy (load_at load_view)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (loadAt loadView)

/-- **`load_view` is `loadView`**: the load of a module's private view, everything but its
theorems' values, with the reason where it does not read. -/
theorem load_view_refines {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {i : Std.U64} {m : arena.handle.NIdx}
    {f : frontend.olean.view.ModFiles} {f' : ConLeche.Frontend.Olean.ModFiles}
    (hf : ModFilesRel f f') :
    CS pers LoadedRel st lst (load_view pk pers st.store i m f)
      (loadView (absPins pk) i.val (absNIdx m) f') := by
  sorry -- T143-STUB

end ConRon.Refine2.Frontend.Olean
