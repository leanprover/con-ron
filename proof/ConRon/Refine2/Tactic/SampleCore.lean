/-
# `ConRon.Refine2.Tactic.SampleCore` — the lockstep tactic on a knot arm

Task #97-T2-TACTIC, sample 3.  `ensure_sort` (old: `Core/Arms/Sort.lean`,
`ensure_sort_refines`, 101 lines) — a D1 function.  The knot's `whnf` slot is
taken in lockstep form as a hypothesis, the way `KnotRel`'s fields become
`hrel₀ → hinv → hctx → hf → LS …` after the migration.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Core.Arms.Sort

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.Sample

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-- `KnotRel.whnf` in lockstep form. -/
def WhnfLS (f : Nat) : Prop :=
  ∀ {pers vis st mode lane fu fe lfe depth e lst},
    AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
    LS pers (fun a b => b = absEIdx a)
      (arena.core.knot_whnf pers vis st mode lane fu fe depth e) lst
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane f).whnf (absU depth) (absEIdx e))

/-- As the twin is today: the zip stops at the D1 site. -/
theorem ensure_sort_refines' {f : Nat} (hW : WhnfLS f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.ensure_sort pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absLIdx pers lst o
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  unfold WhnfLS at hW
  refine LS.toSim₀ ?_ hrun
  rw [arena.core.ensure_sort, ensureSort]
  lockstep
  -- STUCK: D1 (`ensure_sort`): the Rust tests the tag and reads `view_sort`,
  -- the twin reads `view`
  all_goals sorry

/-- **`ensureSort` with the D1 fix applied** (tag first, as the Rust). -/
def ensureSortTF (r : CoreFnsA) (_fe : IFEnv) (depth : Nat) (e : EIdx) : AM LIdx := do
  let w ← r.whnf depth e
  if w.tag == ETag.sort then
    match ← viewSort w with
    | none => failDanglingE
    | some u => pure u
  else fail (.invalid "expected a sort")

theorem ensure_sort_tf_refines' {f : Nat} (hW : WhnfLS f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f)
    (hrun : arena.core.ensure_sort pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absLIdx pers lst o
      (ensureSortTF (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  unfold WhnfLS at hW
  refine LS.toSim₀ ?_ hrun
  rw [arena.core.ensure_sort, ensureSortTF]
  lockstep


/-! ## The axiom census -/

#print axioms ensure_sort_refines'
#print axioms ensure_sort_tf_refines'

end ConRon.Refine2.Lockstep.Sample
