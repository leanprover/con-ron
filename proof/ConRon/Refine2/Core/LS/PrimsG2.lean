/-
# `ConRon.Refine2.Core.LS.PrimsG2` — the `prop_read` answers' well-formedness

Task #97-P5-Core round 5, region G2.  `Core/LS/PropRead.lean` proves the
`prop_read` walks in lockstep with the answer's `PropWhenWF` carried in the
relation (`optPwWF`): `subst_pw` is exact only at a well-formed datum.  The
facts it needs about the Rust values it reads are here: a level read is well
formed, `never` is, and the dangling declines never answer `Ok`.  (The
binder-datum reads and the annotation pass's binder stack went with
con-leche's task #342.)
-/
import ConRon.Refine2.Core.LS.Prims
import ConRon.Refine2.Core.LS.PrimsA1
import ConRon.Refine2.Core.LS.PrimsB

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

namespace ConRon.Refine2.Lockstep.PG2

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## The well-formedness predicates -/

/-- A `prop_read` answer is well formed. -/
def optPwWF : Option kernel.prop_when.PropWhen → Prop
  | some p => ConRon.Refine.PropWhenWF p
  | none => True

attribute [local lockstep_simp] optPwWF

theorem fail_dangling_e_not_ok {T : Type} {o} (h : arena.monad.fail_dangling_e T = ok o) :
    ∀ p, o ≠ .Ok p := by
  rw [arena.monad.fail_dangling_e] at h
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [arena.monad.fail] at h
  cases Result.ok_injective h
  intro p hp; cases hp

theorem fail_dangling_ls_not_ok {T : Type} {o} (h : arena.monad.fail_dangling_ls T = ok o) :
    ∀ p, o ≠ .Ok p := by
  rw [arena.monad.fail_dangling_ls] at h
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [arena.monad.fail] at h
  cases Result.ok_injective h
  intro p hp; cases hp

/-- `read_level`'s answer is well formed (`denote_l_wf`). -/
theorem read_level_wf {pers st} (hinv : AStateInv pers st) {h : arena.handle.LIdx} {l}
    (hrun : arena.monad.read_level pers st h = ok (.Ok l)) : ConRon.Refine.LevelWF l := by
  rw [arena.monad.read_level] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls] at hn
  have hn2 : n = st.store.lss.ls := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hdw := denote_l_wf hinv.store.lss.lvl hv
  cases v with
  | none =>
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    simp at hrun
  | some x =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hrun
    subst hrun
    exact hdw x rfl

theorem never_wf {pw} (h : kernel.prop_when.never = ok pw) : ConRon.Refine.PropWhenWF pw :=
  ConRon.Refine.PropWhen.never_wf h

@[local lockstep_simp] theorem forall_none_eq_imp {α : Type} (P : α → Prop) :
    (∀ p, (none : Option α) = some p → P p) = True := by simp

end ConRon.Refine2.Lockstep.PG2

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.PG2.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.PG2.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep
attribute [scoped lockstep_simp] optPwWF forall_none_eq_imp
end ConRon.Refine2.Lockstep.PG2.CoreLSReg
