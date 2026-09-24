/-
# `ConRon.Refine2.Core.LS.PropRead` — `arena::prop_read` in lockstep

Task #97-P5-Core round 6.  The four `prop_read` entries the Core bodies call
(`proof_pw`, `type_sort_pw`, `is_proof_fast`, `not_proof_fast`) were the last
fields of `ExprOpsHyp` with no Theorem 2 of their own.  The twin
(`Arena/PropRead.lean`) was made tag-first where the port is (`peelNeverPis`,
`numArgs`, `residualPW`, `proofPW`: task #97-T2-AUDIT's D1 list), after which
every walk here is a `lockstep` zip over `AStateRel₀`/`AStateInv`, with no
store invariant.
-/
import ConRon.Refine2.Core.LS.PrimsE
import ConRon.Refine2.Core.LS.PrimsD
import ConRon.Refine2.Core.LS.PrimsG
import ConRon.Refine2.Core.LS.PrimsG2
import ConRon.Arena.PropRead
import ConRon.Refine.PropRead

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg
  ConRon.Refine2.Lockstep.PB.CoreLSReg ConRon.Refine2.Lockstep.PE.CoreLSReg
  ConRon.Refine2.Lockstep.PD.CoreLSReg ConRon.Refine2.Lockstep.PG.CoreLSReg
  ConRon.Refine2.Lockstep.PG2.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal ConRon.Refine2.Lockstep.EViewMetaWF

namespace ConRon.Refine2.Lockstep.PPR

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep
open ConRon.Refine2.Lockstep.PE

/-! ## The two `PropWhen` tests, on well-formed data -/

@[lockstep] theorem has_params_ls {pw : kernel.prop_when.PropWhen}
    (hpw : ConRon.Refine.PropWhenWF pw) :
    LSP (kernel.prop_when.has_params pw)
      (fun b => b = (ConRon.Refine.absPropWhen pw).hasParams) :=
  fun _ h => ConRon.Refine.PropWhen.has_params_refines hpw h

@[lockstep] theorem is_prop_ls {pw : kernel.prop_when.PropWhen}
    (hpw : ConRon.Refine.PropWhenWF pw) :
    LSP (kernel.prop_read.is_prop pw)
      (fun b => b = (ConRon.Refine.absPropWhen pw).isProp) :=
  fun _ h => ConRon.Refine.PropRead.is_prop_refines hpw h

/-! ## The three view-only readers -/

theorem peel_never_pis_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.map absEIdx) (arena.prop_read.peel_never_pis pers st k h)
        st lst (peelNeverPis n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.peel_never_pis, peelNeverPis]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.peel_never_pis, peelNeverPis]
    lockstep

@[lockstep] theorem peel_never_pis_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map absEIdx) (arena.prop_read.peel_never_pis pers st k h)
      st lst (peelNeverPis (absU k) (absEIdx h)) :=
  peel_never_pis_aux _ k h rfl hrel hinv

theorem num_args_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absU a) (arena.prop_read.num_args pers st fuel h)
        st lst (numArgs n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.num_args, numArgs]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.num_args, numArgs]
    lockstep

@[lockstep] theorem num_args_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a) (arena.prop_read.num_args pers st fuel h)
      st lst (numArgs (absU fuel) (absEIdx h)) :=
  num_args_aux _ fuel h rfl hrel hinv

/-- `read_level` (the store read of a level) against `readLevel`, with the
answer's well-formedness (`zeroness_of`'s premise). -/
@[lockstep] theorem read_level_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LSR pers (fun a b => ConRon.Refine.LevelWF a ∧ b = ConRon.Refine.absLevel a)
      (arena.monad.read_level pers st h) st lst (Arena.readLevel (absLIdx h)) := by
  intro o hm
  have H := read_level_run₀ hrel hinv hm
  cases o with
  | Err e => exact H
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := H
    exact ⟨_, lst', hx, ⟨PG2.read_level_wf hinv hm, rfl⟩, h1, h2⟩

@[lockstep] theorem residual_pw_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (res : Option arena.handle.EIdx) :
    LSR pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.residual_pw pers st res)
      st lst (residualPW (res.map absEIdx)) := by
  apply LSR.of_LS
  rcases res with _ | r <;> rw [arena.prop_read.residual_pw] <;>
    simp only [Option.map_none, Option.map_some, residualPW] <;> lockstep

/-! ## The head readers and the entries -/

@[lockstep] theorem head_type_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (h : arena.handle.EIdx) (n : Std.U64) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a) (arena.prop_read.head_type_pw pers vis st fe h n)
      lst (headTypePW lfe (absEIdx h) (absU n)) := by
  rw [arena.prop_read.head_type_pw, headTypePW]
  lockstep

@[lockstep] theorem type_sort_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (t : arena.handle.EIdx) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.type_sort_pw pers vis st fe fuel t)
      lst (typeSortPW lfe (absU fuel) (absEIdx t)) := by
  rw [arena.prop_read.type_sort_pw, typeSortPW]
  lockstep

@[lockstep] theorem head_proof_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.head_proof_pw pers vis st fe fuel h)
      lst (headProofPW lfe (absU fuel) (absEIdx h)) := by
  rw [arena.prop_read.head_proof_pw, headProofPW]
  lockstep

@[lockstep] theorem proof_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (a : arena.handle.EIdx) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a) (arena.prop_read.proof_pw pers vis st fe fuel a)
      lst (proofPW lfe (absU fuel) (absEIdx a)) := by
  rw [arena.prop_read.proof_pw, proofPW]
  lockstep

@[lockstep] theorem is_proof_fast_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (a : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (arena.prop_read.is_proof_fast pers vis st fe fuel a)
      lst (isProofFast lfe (absU fuel) (absEIdx a)) := by
  rw [arena.prop_read.is_proof_fast, isProofFast]
  lockstep

@[lockstep] theorem not_proof_fast_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (a : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (arena.prop_read.not_proof_fast pers vis st fe fuel a)
      lst (notProofFast lfe (absU fuel) (absEIdx a)) := by
  rw [arena.prop_read.not_proof_fast, notProofFast]
  lockstep

/-! ## The `Sim₀` forms `ExprOpsHyp` states (the WF conjunct dropped) -/

theorem LS.weaken {α β : Type} {pers : arena.store.PersTier} {R R' : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R m lst x) (hR : ∀ a b, R a b → R' a b) :
    LS pers R' m lst x := by
  intro o st' hm
  have H := h o st' hm
  cases o with
  | Err e => exact H
  | Ok a =>
    obtain ⟨b, lst', hx, hr, h1, h2⟩ := H
    exact ⟨b, lst', hx, hR a b hr, h1, h2⟩

theorem proof_pw_sim {pers st lst vis fe lfe} {fuel : Std.U64} {a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (hrun : arena.prop_read.proof_pw pers vis st fe fuel a = ok o) :
    Sim₀ ExprOps.absPwOpt pers lst o (proofPW lfe (absU fuel) (absEIdx a)) :=
  LS.toSim₀ (LS.weaken (proof_pw_ls hrel hinv hctx fuel a) fun _ _ h => h.2) hrun

theorem type_sort_pw_sim {pers st lst vis fe lfe} {fuel : Std.U64} {t : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (hrun : arena.prop_read.type_sort_pw pers vis st fe fuel t = ok o) :
    Sim₀ ExprOps.absPwOpt pers lst o (typeSortPW lfe (absU fuel) (absEIdx t)) :=
  LS.toSim₀ (LS.weaken (type_sort_pw_ls hrel hinv hctx fuel t) fun _ _ h => h.2) hrun

end ConRon.Refine2.Lockstep.PPR
