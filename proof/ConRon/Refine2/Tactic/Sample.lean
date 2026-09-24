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

/-! ## 0. Straight-line intern wrappers: `intern_rebuilt_{app,bind}` (old: 29 / 57 lines) -/

theorem intern_rebuilt_app_refines' {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {f a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.expr_ops.intern_rebuilt_app pers st h same f a = ok o) :
    Sim₀ absEIdx pers lst o (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) := by
  refine LS.toSim₀ ?_ hrun
  rw [arena.expr_ops.intern_rebuilt_app, internRebuiltApp]
  lockstep

theorem intern_rebuilt_bind_refines' {pers st lst} {h : arena.handle.EIdx}
    {same : Bool} {tag : Std.U32} {ty body : arena.handle.EIdx}
    {m : kernel.expr.BinderMeta} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpw : ConRon.Refine.PropWhenWF m.pw)
    (hrun : arena.expr_ops.intern_rebuilt_bind pers st h same tag ty body m = ok o) :
    Sim₀ absEIdx pers lst o
      (internRebuiltBind (absEIdx h) same (absU32 tag) (absEIdx ty) (absEIdx body)
        (ConRon.Refine.absBinderMeta m)) := by
  refine LS.toSim₀ ?_ hrun
  rw [arena.expr_ops.intern_rebuilt_bind, internRebuiltBind]
  lockstep

/-! ## 1. A memoised `_go` walk: `lift_loose_bvars_go` (old: `ExprOps/Mut.lean`, 495 + 9 lines) -/

section lift
attribute [local lockstep_simp] liftArmApp liftArmLam liftArmForallE liftArmLet liftArmProj

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

/-! ## 1b. The canonical memoised walk: `instantiate1_go` (old: `ExprOps/Mut.lean`, 511 + 10 lines) -/

section inst1
attribute [local lockstep_simp] instantiate1ArmApp instantiate1ArmBind instantiate1ArmBVar
  instantiate1ArmLet instantiate1ArmProj

theorem instantiate1_go_aux' (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (v : arena.handle.EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.expr_ops.instantiate1_go pers st v fuel h d) lst
        (instantiate1Go (absEIdx v) n (absEIdx h) (absU d)) := by
  induction n with
  | zero =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_go, instantiate1Go_zero]
    lockstep
  | succ m ih =>
    intro pers st lst v fuel h d hn hrel hinv
    rw [arena.expr_ops.instantiate1_go, instantiate1Go_succ]
    lockstep

end inst1


/-! ## 2. A telescope: `inst_pis_from` (old: `ExprOps/Mut.lean`, 76 + 10 lines) — a D1 function

`instantiate1_fast` is a sibling walk of sample 1; its lockstep statement is
taken as a hypothesis (`hI1`), which the tactic finds in the context. -/

/-- The lockstep statement of `instantiate1_fast` (the shape sample 1 proves). -/
def I1Spec : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (fuel : Std.U64) (e v : arena.handle.EIdx) (d : Std.U64),
    AStateRel₀ pers st lst → AStateInv pers st →
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_fast pers st fuel e v d) lst
      (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d))

/-- **`instPis` with the D1 fix applied** — the twin spelled tag-first, as the
Rust is (`if h.tag == ETag.forallE then match ← viewBind h with …`); against
the twin as it was, the zip stopped at the Rust's `view_bind` (DESIGN
#97-T2-TACTIC §4, row 5; that stuck demonstration is deleted).  This is
the twin edit task #97-T2-AUDIT §4 prescribes for the 94 D1 functions. -/
def instPisTF (fuel : Nat) : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: rest => do
    if h.tag == ETag.forallE then
      match ← viewBind h with
      | none => failDanglingE
      | some (_, body, _) => do
        let b ← instantiate1Fast fuel body a 0
        instPisTF fuel b rest
    else pure none

theorem inst_pis_from_tf_aux' (hI1 : I1Spec) (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (e : arena.handle.EIdx) (args : alloc.vec.Vec arena.handle.EIdx)
      (i : Std.Usize),
      args.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absOptE a) (arena.expr_ops.inst_pis_from pers st fuel e args i) lst
        (instPisTF (absU fuel) (absEIdx e) (absEIdxListFrom args i)) := by
  unfold I1Spec at hI1
  induction n with
  | zero =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [arena.expr_ops.inst_pis_from, listFrom_nil args i (by omega), instPisTF]
    lockstep
  | succ k ih =>
    intro pers st lst fuel e args i hn hrel hinv
    rw [arena.expr_ops.inst_pis_from, listFrom_cons args i (by omega), instPisTF]
    lockstep


/-! ## The axiom census -/

#print axioms intern_rebuilt_app_refines'
#print axioms intern_rebuilt_bind_refines'
#print axioms lift_loose_bvars_go_refines'
#print axioms instantiate1_go_aux'
#print axioms inst_pis_from_tf_aux'

end ConRon.Refine2.Lockstep.Sample
