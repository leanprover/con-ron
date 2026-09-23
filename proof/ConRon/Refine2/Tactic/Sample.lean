/-
# `ConRon.Refine2.Tactic.Sample` — the lockstep tactic on a sample of Theorem-2 lemmas

Task #97-T2-TACTIC.  COPIES of existing Theorem-2 lemmas, restated in the
lockstep shape (`AStateRel₀`, no `Ext`, no resolves clause) and proved with
`lockstep`.  Nothing here is used by the tier; the lemmas are primed so they
cannot collide with the migration lanes.  The measurements are DESIGN task
#97-T2-TACTIC's table.
-/
import ConRon.Refine2.Tactic.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.Sample

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## 1. A memoised `_go` walk: `lift_loose_bvars_go` (old: `ExprOps/Mut.lean`, 495 + 9 lines) -/

section lift
attribute [local lockstep_simp] liftArmApp liftArmLam liftArmForallE liftArmLet liftArmProj

set_option profiler true in
theorem lift_loose_bvars_go_aux' (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (amount fuel : Std.U64) (h : arena.handle.EIdx) (c : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c) lst
        (liftLooseBVarsGo (absU amount) n (absEIdx h) (absU c)) := by
  induction n with
  | zero =>
    intro pers st lst amount fuel h c hn hrel hinv
    rw [arena.expr_ops.lift_loose_bvars_go, liftLooseBVarsGo_zero]
    lockstep
  | succ m ih =>
    intro pers st lst amount fuel h c hn hrel hinv
    rw [arena.expr_ops.lift_loose_bvars_go, liftLooseBVarsGo_succ]
    lockstep


/-- The public statement, in `Sim₀` form. -/
theorem lift_loose_bvars_go_refines' {pers st lst} {amount fuel : Std.U64}
    {h : arena.handle.EIdx} {c : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.lift_loose_bvars_go pers st amount fuel h c = ok o) :
    Sim₀ absEIdx pers lst o (liftLooseBVarsGo (absU amount) (absU fuel) (absEIdx h) (absU c)) :=
  LS.toSim₀ (lift_loose_bvars_go_aux' _ amount fuel h c rfl hrel hinv) hrun

end lift

#print axioms lift_loose_bvars_go_refines'

end ConRon.Refine2.Lockstep.Sample
