/-
# `ConRon.Refine2.Inductives.Top` — the tier's top statement

**Task #97-P5-Ind**, the deliverable (DESIGN.md §8.2); lockstep since task
#97-T2-LOCKSTEP.  `crates/con-ron-core/src/arena/inductives.rs` against
`proof/ConRon/Arena/Inductives.lean`: the `.indDecl` dispatch — the declared
parameter count first, and for both routes, then ONE ROUTE (con-leche's task
#210): the fixpoint route takes every block its recogniser recognises, and
everything else is the modeled path's.

`inductives_check_ind_decl_refines` is what `Refine2/Checker/Top.lean`'s
`check_ind_decl_refines` (the basis-pin wrapper one level above) calls.  It is
stated lockstep: `AStateRel₀`, `AStateInv`, the environment related and well
formed (`IFEnvRelI`, which is also the answer relation, because the checker's
fold needs both for its next step), and the Rust run.  No `KnotRel` binder:
`knotRel_checkFuel'` is a theorem (`Refine2/Checker/KnotHyp.lean`).

**`IndRel` and `ind_rel` are gone from this file** (task #97-T2-LOCKSTEP lane
Inductives).  `IndRel` (`Refine2/Checker/Shape.lean`) states the seam over the
old `AStateRel`/`SimRel`, which a lockstep statement does not imply (the old
shapes carry the twin's `StoreWF` and `Ext`, which are Theorem 1's), and it
has no consumer left: the Checker tier calls this theorem directly.

**`check_ind_decl` takes no `vis` argument**: it passes `fe.visible_below` to
`checker_base::ind_params_ok` itself and moves `fe` into the two routes, so
task #97-P5-Checker's finding 10 stops at this door.
-/
import ConRon.Refine2.Inductives.Modeled
-- `StructParts.lean` is a LEAF of the tier: `struct_install.rs` calls its
-- generators, but no other `Refine2/Inductives` module imports it, so until
-- round 4 it was outside `lake build ConRonRefine2` altogether — 47
-- declarations of the tier that the landing gate never elaborated.  The index
-- imports it for that reason and for no other.
import ConRon.Refine2.Inductives.StructParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- **`arena::inductives::check_ind_decl` ⊑ `Inductives.checkIndDecl`** — the
`.indDecl` arm.  The name carries the module qualifier because
`Refine2/Checker/Top.lean` already has a `check_ind_decl_refines`, about
`arena::checker::check_ind_decl` — the basis-pin wrapper ONE level above this
one.
The declared parameter count is official's own check and one-sided, so a
`false` is official's REJECT and both sides raise `.invalid`; past it the
recogniser alone routes the block, and no model lookup is needed to decide
which way it goes (con-leche's task #219).

What is NOT here is the pinned basis block: a stream's `Nat` block arrives as
an ordinary `indDecl` and `basisPinHit` recognises it in
`arena::checker::check_decl`, before this, exactly where con-leche places it. -/
theorem inductives_check_ind_decl_refines {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {n_p : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.check_ind_decl pers mode rf block n_p st = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (Inductives.checkIndDecl (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) := by
  sorry

end ConRon.Refine2
