/-
# `ConRon.Refine2.Core.LS.PropRead` — `arena::prop_read` in lockstep

Task #97-P5-Core round 6.  The four `prop_read` entries the Core bodies call
(`proof_pw`, `type_sort_pw`, `is_proof_fast`, `not_proof_fast`) were the last
fields of `ExprOpsHyp` with no Theorem 2 of their own.  The twin
(`Arena/PropRead.lean`) was made tag-first where the port is (`peelPis`,
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

/-! ## The `PropWhen` test, on well-formed data -/

@[lockstep] theorem is_prop_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_read.is_prop pw)
      (fun b => b = (ConRon.Refine.absPropWhen pw).isProp) :=
  fun _ h => ConRon.Refine.PropRead.is_prop_refines h

@[local lockstep_simp] theorem unwrap_fuel_abs :
    absU arena.prop_read.UNWRAP_FUEL = 4 := by
  rw [arena.prop_read.UNWRAP_FUEL]; rfl

/-! ## The view-only readers -/

theorem peel_pis_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.map absEIdx) (arena.prop_read.peel_pis pers st k h)
        st lst (peelPis n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.peel_pis, peelPis]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.peel_pis, peelPis]
    lockstep

@[lockstep] theorem peel_pis_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map absEIdx) (arena.prop_read.peel_pis pers st k h)
      st lst (peelPis (absU k) (absEIdx h)) :=
  peel_pis_aux _ k h rfl hrel hinv

theorem binder_dom_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.map absEIdx) (arena.prop_read.binder_dom pers st k h)
        st lst (binderDom n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.binder_dom, binderDom]
    lockstep
  | succ m ih =>
    intro pers st lst k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.binder_dom, binderDom]
    lockstep

@[lockstep] theorem binder_dom_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map absEIdx) (arena.prop_read.binder_dom pers st k h)
      st lst (binderDom (absU k) (absEIdx h)) :=
  binder_dom_aux _ k h rfl hrel hinv

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

/-! ## The identity-wrapper unfolding -/

theorem lam_proj_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel k : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.map fun p => (absU p.1, absU p.2))
        (arena.prop_read.lam_proj pers st fuel k h)
        st lst (lamProj? n (absU k) (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.lam_proj, lamProj?]
    lockstep
  | succ m ih =>
    intro pers st lst fuel k h hn hrel hinv
    apply LSR.of_LS
    rw [arena.prop_read.lam_proj, lamProj?]
    lockstep

@[lockstep] theorem lam_proj_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map fun p => (absU p.1, absU p.2))
      (arena.prop_read.lam_proj pers st fuel k h)
      st lst (lamProj? (absU fuel) (absU k) (absEIdx h)) :=
  lam_proj_aux _ fuel k h rfl hrel hinv

theorem unwrap_id_defs_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (fuel nn : Std.U64) (e : arena.handle.EIdx),
      nn.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = absEIdx a)
        (arena.prop_read.unwrap_id_defs pers vis st fe fuel nn e)
        lst (unwrapIdDefs lfe (absU fuel) n (absEIdx e)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst fuel nn e hn hrel hinv hctx
    rw [arena.prop_read.unwrap_id_defs, unwrapIdDefs]
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst fuel nn e hn hrel hinv hctx
    rw [arena.prop_read.unwrap_id_defs, unwrapIdDefs]
    lockstep
    -- glue: the twin's `args.getD (k - 1 - j) e` is the port's `args[k - 1 - j]`
    -- under its two length tests
    convert ih fuel a _ (by scalar_tac) hrel hinv hctx using 2
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by scalar_tac)]
    simp only [Option.map_some, Option.getD_some]
    congr 2
    scalar_tac

@[lockstep] theorem unwrap_id_defs_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel n : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.prop_read.unwrap_id_defs pers vis st fe fuel n e)
      lst (unwrapIdDefs lfe (absU fuel) (absU n) (absEIdx e)) :=
  unwrap_id_defs_aux _ fuel n e rfl hrel hinv hctx

theorem peel_pis_w_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (fuel k : Std.U64) (h : arena.handle.EIdx),
      k.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.prop_read.peel_pis_w pers vis st fe fuel k h)
        lst (peelPisW lfe (absU fuel) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst fuel k h hn hrel hinv hctx
    rw [arena.prop_read.peel_pis_w, peelPisW]
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst fuel k h hn hrel hinv hctx
    rw [arena.prop_read.peel_pis_w, peelPisW]
    lockstep

@[lockstep] theorem peel_pis_w_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel k : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.prop_read.peel_pis_w pers vis st fe fuel k h)
      lst (peelPisW lfe (absU fuel) (absU k) (absEIdx h)) :=
  peel_pis_w_aux _ fuel k h rfl hrel hinv hctx

/-! ## The head readers and the entries -/

@[lockstep] theorem subst_pw_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (lps : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) {pw : kernel.prop_when.PropWhen}
    (hpw : ConRon.Refine.PropWhenWF pw) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.subst_pw_at pers st lps us pw)
      lst (substPWAt (lps.val.map absNIdx) (absLsIdx us) (ConRon.Refine.absPropWhen pw)) := by
  rw [arena.prop_read.subst_pw_at.eq_def]
  cases pw with
  | Never => simp only [ConRon.Refine.absPropWhen, substPWAt]; lockstep
  | IfAllZero ps =>
    -- glue: the twin matches the abstracted list's shape, the port tests
    -- its length; split the list once for both
    cases hv : ps.val with
    | nil =>
      simp only [ConRon.Refine.absPropWhen, ConRon.Refine.absNames, hv, List.map_nil, substPWAt]
      lockstep
      all_goals
        intro o st' h
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, rfl, ⟨by simp_all [PG2.optPwWF], by
          simp_all [ExprOps.absPwOpt, ConRon.Refine.absPropWhen, ConRon.Refine.absNames]⟩,
          by assumption, by assumption⟩
    | cons x xs =>
      simp only [ConRon.Refine.absPropWhen, ConRon.Refine.absNames, hv, List.map_cons, substPWAt]
      lockstep
      all_goals
        intro o st' h
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, rfl, ⟨by simp_all [PG2.optPwWF], by
          simp_all [ExprOps.absPwOpt, ConRon.Refine.absPropWhen, ConRon.Refine.absNames,
            ConRon.Refine.absLevels]⟩,
          by assumption, by assumption⟩

@[lockstep] theorem head_type_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (root : arena.handle.EIdx) (d : Std.U64) (h : arena.handle.EIdx)
    (n : Std.U64) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.head_type_pw pers vis st fe fuel root d h n)
      lst (headTypePW lfe (absU fuel) (absEIdx root) (absU d) (absEIdx h) (absU n)) := by
  rw [arena.prop_read.head_type_pw, headTypePW]
  lockstep

theorem type_sort_pw_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (fuel : Std.U64) (root t : arena.handle.EIdx) (d : Std.U64),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
        (arena.prop_read.type_sort_pw_go pers vis st fe fuel root t d)
        lst (typeSortPWGo lfe (absEIdx root) n (absEIdx t) (absU d)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst fuel root t d hn hrel hinv hctx
    rw [arena.prop_read.type_sort_pw_go, typeSortPWGo]
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst fuel root t d hn hrel hinv hctx
    rw [arena.prop_read.type_sort_pw_go, typeSortPWGo]
    lockstep

@[lockstep] theorem type_sort_pw_go_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (root t : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.type_sort_pw_go pers vis st fe fuel root t d)
      lst (typeSortPWGo lfe (absEIdx root) (absU fuel) (absEIdx t) (absU d)) :=
  type_sort_pw_go_aux _ fuel root t d rfl hrel hinv hctx

@[lockstep] theorem type_sort_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (t : arena.handle.EIdx) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.type_sort_pw pers vis st fe fuel t)
      lst (typeSortPW lfe (absU fuel) (absEIdx t)) := by
  rw [arena.prop_read.type_sort_pw, typeSortPW]
  exact type_sort_pw_go_ls hrel hinv hctx fuel t t 0#u64

@[lockstep] theorem head_proof_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.head_proof_pw pers vis st fe fuel h)
      lst (headProofPW lfe (absU fuel) (absEIdx h)) := by
  rw [arena.prop_read.head_proof_pw, headProofPW]
  lockstep

theorem proof_pw_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {vis : Std.U64} {st : arena.monad.AState}
      {fe : arena.env.IFEnv} {lfe : IFEnv} {lst : AState}
      (fuel : Std.U64) (a : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe →
      LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
        (arena.prop_read.proof_pw pers vis st fe fuel a)
        lst (proofPW lfe n (absEIdx a)) := by
  induction n with
  | zero =>
    intro pers vis st fe lfe lst fuel a hn hrel hinv hctx
    rw [arena.prop_read.proof_pw, proofPW]
    lockstep
  | succ m ih =>
    intro pers vis st fe lfe lst fuel a hn hrel hinv hctx
    rw [arena.prop_read.proof_pw, proofPW]
    lockstep

@[lockstep] theorem proof_pw_ls {pers st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel : Std.U64) (a : arena.handle.EIdx) :
    LS pers (fun a b => PG2.optPwWF a ∧ b = ExprOps.absPwOpt a)
      (arena.prop_read.proof_pw pers vis st fe fuel a)
      lst (proofPW lfe (absU fuel) (absEIdx a)) :=
  proof_pw_aux _ fuel a rfl hrel hinv hctx

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
