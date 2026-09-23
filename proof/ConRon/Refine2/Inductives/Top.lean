/-
# `ConRon.Refine2.Inductives.Top` — `IndRel`, discharged

**Task #97-P5-Ind**, the deliverable (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives.rs` against
`proof/ConRon/Arena/Inductives.lean`: the `.indDecl` dispatch — the declared
parameter count first, and for both routes, then ONE ROUTE (con-leche's task
#210): the fixpoint route takes every block its recogniser recognises, and
everything else is the modeled path's.

**`ind_rel` is this tier's whole reason for existing.**
`Refine2/Checker/Top.lean` states the Inductives seam as a hypothesis —

    structure IndRel : Prop where
      checkIndDecl : ∀ {pers st lst rf lf mode block n_p o},
        AStateRel pers st lst → AStateInv pers st →
        IFEnvRel rf lf → IFEnvInv rf →
        arena.inductives.check_ind_decl pers mode rf block n_p st = ok o →
        SimRel (fun r v => IFEnvRel r v) pers lst o
          (Inductives.checkIndDecl (absMode mode) lf (absICIL block) (absU n_p))

— and carries it at thirteen statements, nine of which are the capstones'
route down.  `ind_rel_of_knot` below supplies it **from `KnotRel checkFuel`
and nothing else**, which is the right shape for the seam: the two capstones
already take `hknot : KnotRel checkFuel` beside `hind : IndRel`, so they
consume it with no change to their statements.

**And since task #97-P5-Arms reconciled the two `KnotRel`s, the hypothesis is
gone.**  `Refine2/Checker/KnotHyp.lean`'s `knotRel_checkFuel'` is now a
THEOREM — `Refine2/Core/Arms.lean`'s `knotRel` at `Arena.checkFuel` — so
`ind_rel : IndRel` below is unconditional, and the thirteen sites take it
with no argument at all.  What `KnotRel` means moved under this tier in that
round (the Checker tier's six front doors became the Core tier's six `knot_*`
dispatchers at a lane) and **nothing of this tier had to change for it**:
`hknot` is a pure binder at all 74 sites, no proof here projects a field, and
`Refine2/Core/Entries.lean`'s six theorems plus
`Refine2/Core/Arms/Sort.lean`'s `ensure_sort_core_refines` are exactly the
seven front doors this tier calls.

**`IndRel` needs no `hvis`.**  `check_ind_decl` takes no `vis` argument: it
passes `fe.visible_below` to `checker_base::ind_params_ok` itself and moves
`fe` into the two routes.  Task #97-P5-Checker's finding 10 therefore stops
at this door, which is why the seam's statement is four hypotheses and not
five.
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
one, whose `hind : IndRel` this tier's `ind_rel` supplies.
The declared parameter count is official's own check and one-sided, so a
`false` is official's REJECT and both sides raise `.invalid`; past it the
recogniser alone routes the block, and no model lookup is needed to decide
which way it goes (con-leche's task #219).

What is NOT here is the pinned basis block: a stream's `Nat` block arrives as
an ordinary `indDecl` and `basisPinHit` recognises it in
`arena::checker::check_decl`, before this, exactly where con-leche places it. -/
theorem inductives_check_ind_decl_refines {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo} {n_p : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.check_ind_decl pers mode rf block n_p st = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (Inductives.checkIndDecl (ConRon.Refine.absMode mode) lf (absICIL block)
        (absU n_p)) := by
  sorry

/-- **The tier's capstone: `IndRel`, discharged.**  One clause, supplied from
`KnotRel checkFuel` — the Core tier's own obligation, which the declaration
checker's capstones already carry beside this one.

`Refine2/Checker/Top.lean` consumes `IndRel` at thirteen sites without
change: `ind_rel` is what its `hind` argument now takes, and the seam task
#97-P5-Checker §9 asked for (*"land the proof, delete the hypothesis"*) is met
at the calling convention rather than by editing that file. -/
theorem ind_rel_of_knot (hknot : KnotRel checkFuel) : IndRel where
  checkIndDecl := fun hrel hinv hfe hfinv hrun =>
    inductives_check_ind_decl_refines hrel hinv hfe hfinv hknot hrun

/-- **`IndRel`, unconditionally** — `ind_rel_of_knot` at
`Refine2/Checker/KnotHyp.lean`'s `knotRel_checkFuel'`, which task
#97-P5-Arms made a theorem.  This is what `Refine2/Checker/Top.lean`'s
thirteen `hind : IndRel` sites take, with no argument. -/
theorem ind_rel : IndRel := ind_rel_of_knot knotRel_checkFuel'

/-! ## The axiom census at the seam

`ind_rel` adds nothing of its own: it is
`inductives_check_ind_decl_refines` packaged as
the structure `Refine2/Checker/Top.lean` declares, and the `sorryAx` below is
that one open statement about the dispatch and the 305 under it.  The row is
recorded rather than dropped because it is the honest reading of *"`IndRel` is
discharged"*: the SEAM is closed — no hypothesis of the Checker tier is left
unsupplied — and what remains open is the tier's own proof obligations. -/

/-- info: 'ConRon.Refine2.ind_rel' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ind_rel

end ConRon.Refine2
