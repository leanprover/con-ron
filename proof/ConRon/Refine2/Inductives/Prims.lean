/-
# `ConRon.Refine2.Inductives.Prims` — the tier's `@[lockstep]` callees from other tiers

Task #97-T2-LOCKSTEP lane Inductives round 3.  The tier's Rust calls about
65 functions outside `arena::inductives` (the core's level comparison, the
environment's readers, the checker's `checker_base`, the promote tier's name
builders …).  Their Theorem-2 lemmas live with their owners, mostly as
`_refines`/`_run` statements in `Sim₀`/`LSS` form without the `@[lockstep]`
attribute; this file files them for the tactic — in `LS` form where a
conversion is needed, by `attribute [lockstep]` where not — and adds the
Rust-only specs the tier's zips need.  Nothing here restates an owner's lemma.
-/
import ConRon.Refine2.Checker.Base
import ConRon.Refine2.Inductives.Env
import ConRon.Refine2.ExprOps.Mut

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep in
/-- `arena::monad::intern_n_node` ⊑ `internNNode` (`Refine2/Specs.lean`). -/
@[lockstep] theorem intern_n_node_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_n_node pers st v) lst
      (Arena.internNNode (absNNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_n_node_run₀ hrel hinv v hvwf h

/-! ## The mode gates: each is its twin field, a Rust-only step -/

open Lockstep in
@[lockstep] theorem tt_checks_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.tt_checks m) (fun b => TwinEq (ConRon.Refine.absMode m).ttChecks b) := by
  intro b h
  cases m <;> (simp only [kernel.env.tt_checks, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem verified_checks_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m) (fun b => TwinEq (ConRon.Refine.absMode m).verifiedChecks b) := by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem beta_gate_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.beta_gate m) (fun b => TwinEq (ConRon.Refine.absMode m).betaGate b) := by
  intro b h
  cases m <;> (simp only [kernel.env.beta_gate, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem io_gate_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.io_gate m) (fun b => TwinEq (ConRon.Refine.absMode m).ioGate b) := by
  intro b h
  cases m <;> (simp only [kernel.env.io_gate, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem certs_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.certs m) (fun b => TwinEq (ConRon.Refine.absMode m).certs b) := by
  intro b h
  cases m <;> (simp only [kernel.env.certs, Result.ok.injEq] at h; rw [← h]; rfl)

/-! ## The port's message and name-part constants

A name the port builds from a constant (`intern_n_node (Str n (code_points
REC))`) is the twin's `.str n "rec"`: the literal is `lift (to_slice REC)` then
`code_points`, two Rust-only steps whose specs carry the code points, and the
side goals `absString v = "rec"` / `StrWF v` are then a computation on a
three-element list. -/

open Lockstep in
@[lockstep] theorem lift_to_slice_spec {n : Std.Usize} (X : Array Std.U32 n) :
    LSP (lift (Array.to_slice X)) (fun s => s.val = X.val) := by
  intro s h
  simp only [lift, Result.ok.injEq] at h
  subst h
  simp

open Lockstep in
@[lockstep] theorem code_points_spec (s : Slice Std.U32) :
    LSP (kernel.core_types.code_points s) (fun v => v.val = s.val) :=
  fun _ h => ConRon.Refine.Env.code_points_val h

open Lean Elab Tactic in
/-- Fails unless the goal mentions a name-part string (`absString`, `StrWF`,
`NNodeViewWF`): the string tier's `simp only [global_simps] at *` is not free. -/
elab "ind_str_guard" : tactic => do
  let t ← getMainTarget
  unless t.containsConst (fun n => n == ``ConRon.Refine.absString ||
      n == ``ConRon.Refine.StrWF || n == ``NNodeViewWF || n == ``absNNodeView) do
    throwError "ind_str_guard: no string goal"

/-- The string side goals of a constant name part. -/
macro "ind_str_side" : tactic =>
  `(tactic| (ind_str_guard
             try simp only [global_simps] at *
             simp_all [Array.make, ConRon.Refine.absString, ConRon.Refine.StrWF, NNodeViewWF, absNNodeView]
             try decide))

macro_rules
  | `(tactic| lockstep_side_ext) => `(tactic| (ind_str_side; done))

/-! ## Three Core readers the inductive routes call (task #97-T2-LOCKSTEP lane
Inductives round 4): `proj_model_name`, `pi_result_is_prop`, `pi_result_z`.
No lane owns them; both the Native/Struct/Sum tier and the Modeled lane use them. -/

open Lockstep in
@[lockstep] theorem nat_to_dec_spec (i : Std.U64) :
    LSP (kernel.core_k.nat_to_dec i)
      (fun r => ConRon.Refine.absCodes r.val = toString i.val ∧ ConRon.Refine.StrWF r) :=
  fun _ h => ConRon.Refine.CoreK.nat_to_dec_refines h

open Lockstep in
@[lockstep] theorem code_points_from_zero_spec (s : Slice Std.U32) (out : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.code_points_from s 0#usize out)
      (fun v => v.val = out.val ++ s.val) := by
  intro v h
  have := ConRon.Refine.Env.code_points_from_val s _ 0#usize out v (le_refl _) h
  simpa using this

open Lockstep in
/-- `kernel::level::zeroness_of` is the twin's `Level.zeronessOf` at a
well-formed level (the cached readback's output carries the `LevelWF`). -/
@[lockstep] theorem zeroness_of_twin (l : kernel.level.Level) (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.zeroness_of l)
      (fun pw => TwinEq ((ConRon.Refine.absLevel l).zeronessOf) (ConRon.Refine.absPropWhen pw) ∧
        ConRon.Refine.PropWhenWF pw) :=
  fun pw h => ⟨(ConRon.Refine.ExprOps.zeroness_of_refines hl pw h).1.symm,
    (ConRon.Refine.ExprOps.zeroness_of_refines hl pw h).2⟩

open Lockstep in
/-- `prop_when::if_all_zero` of the empty list is the twin's `.ifAllZero []`. -/
@[lockstep] theorem if_all_zero_new_twin :
    LSP (kernel.prop_when.if_all_zero (alloc.vec.Vec.new kernel.name.Name))
      (fun pw => TwinEq (ConLeche.PropWhen.ifAllZero []) (ConRon.Refine.absPropWhen pw) ∧
        ConRon.Refine.PropWhenWF pw) := by
  intro pw h
  have hwf : ConRon.Refine.PropWhenWF pw :=
    ConRon.Refine.PropWhenWF.if_all_zero (by simp [ConRon.Refine.NamesWF, alloc.vec.Vec.new]) h
  refine ⟨?_, hwf⟩
  simp only [kernel.prop_when.if_all_zero, kernel.prop_when.of_repr, alloc.vec.Vec.new,
    alloc.vec.Vec.len] at h
  rw [if_pos (by rfl)] at h
  simp at h
  subst h
  rfl

/-! ## The checker tier's statements in `LS` form

The checker tier's own `@[lockstep]` companions (`Checker/{Base,Pins,Axioms}`)
serve the tier directly.  What is left here has none there: `Checker/Canon`'s
are `private`/`local`, and `name_read_sim` has no `LS` form.  One
`LS.ofSim₀` line each, in their own namespace so a companion the checker lane
adds later does not clash. -/

namespace IndPrims

open Lockstep in
@[lockstep] theorem name_read_sim_ls
    {pers : arena.store.PersTier}
    {st : arena.monad.AState}
    {lst : AState}
    {pin : Result (core.result.Result arena.handle.NIdx kernel.core_types.CheckError)}
    {tw : AM NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hS : ∀ r, pin = ok r → SimRE absNIdx lst r tw) :
    LS pers (fun a b => b = absNIdx a) ((do let r ← pin; ok (r, st))) lst
                            tw :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv hS h


open Lockstep in
@[lockstep] theorem canon_names_go_ls
    {pers st lst}
    {i n : Std.U64}
    {out : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.canon.canon_names_go pers st i n out) lst
      (do pure (absNIdxL out ++ (← canonNamesGo (absU i) (absU n)))) :=
  LS.ofSim₀ fun _ h => canon_names_go_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_names_ls
    {pers st lst}
    {n : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.canon.canon_names pers st n) lst
                             (canonNames (absU n)) :=
  LS.ofSim₀ fun _ h => canon_names_refines hrel hinv h


open Lockstep in
@[lockstep] theorem i_constant_val_canon_eq_ls
    {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.i_constant_val_canon_eq pers st cv cv2) lst
      ((absIConstantVal cv).canonEq (absIConstantVal cv2)) :=
  LS.ofSim₀ fun _ h => i_constant_val_canon_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_eq_cv_and_rules_ls
    {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.canon_eq_cv_and_rules pers st cv cv2 rs rs2) lst
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonRulesEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absIRecRuleL rs) (absIRecRuleL rs2)
        else pure false) :=
  LS.ofSim₀ fun _ h => canon_eq_cv_and_rules_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_eq_cv_and_value_ls
    {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {v v2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.canon_eq_cv_and_value pers st cv cv2 v v2) lst
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonExprEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absEIdx v) (absEIdx v2)
        else pure false) :=
  LS.ofSim₀ fun _ h => canon_eq_cv_and_value_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_eq_list_ls
    {pers st lst}
    {xs ys : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.canon_eq_list pers st xs ys i) lst
      (canonEqList (absICILFrom xs i) (absICILFrom ys i)) :=
  LS.ofSim₀ fun _ h => canon_eq_list_refines hrel hinv h


end IndPrims

theorem IFEnv.restrictTo_of_eq {lf : IFEnv} {k : Nat} (h : k = lf.visibleBelow) :
    lf.restrictTo k = lf := by
  subst h; rfl

-- A checker-tier statement at a split counter reads `lf.restrictTo (absU vis)`;
-- where the counter is the environment's own (`hvis`), that IS `lf`.
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (apply IFEnv.restrictTo_of_eq; assumption))

attribute [lockstep] proj_table_name_lss

/-! ## The recursor rule's two install bits (`core::rec_rule_bits`)

Moved down from `PrimsModeled.lean` (coordinator's ruling, task #97-T2-LOCKSTEP
lane Inductives Install), names kept: the sum route's `sum_rules` needs them
too.  The record-field equations are registered locally: `Shape`'s
`absIRecRule_{ctor,nfields,rhs}_eq`, `Core/LS/Iota`'s `absIRecRule_{fire,k,eta}` and
`absIIndCaps_{eta,etaCtor}`, and the ones only this tier needs in `IndModeledPrims`. -/

namespace IndModeledPrims

theorem absIRecRule_ctorParams (r : arena.env.IRecRule) :
    (absIRecRule r).ctorParams = absU r.ctor_params := rfl
theorem absIRecRule_paramsBlind (r : arena.env.IRecRule) :
    (absIRecRule r).paramsBlind = r.params_blind := rfl

theorem absIIndCaps_ruleK (c : arena.env.IIndCaps) : (absIIndCaps c).ruleK = c.rule_k := rfl

/-- `decide (x = 0)` at a `u64` is the twin's `(x : Nat) == 0`. -/
theorem decide_u64_eq_zero (x : Std.U64) : decide (x = 0#u64) = (x.val == 0) := by
  by_cases h : x = 0#u64
  · subst h; rfl
  · have : x.val ≠ 0 := fun hc => h (by scalar_tac)
    simp [h, this]

end IndModeledPrims

section RuleBits
open Lockstep IndModeledPrims
attribute [local lockstep_simp] absIRecRule_ctor_eq absIRecRule_nfields_eq
  IndModeledPrims.absIRecRule_ctorParams Lockstep.absIRecRule_fire
  absIRecRule_rhs_eq Lockstep.absIRecRule_k Lockstep.absIRecRule_eta
  IndModeledPrims.absIRecRule_paramsBlind Lockstep.absIIndCaps_eta Lockstep.absIIndCaps_etaCtor IndModeledPrims.absIIndCaps_ruleK IndModeledPrims.decide_u64_eq_zero etag_const_abs

@[lockstep] theorem rec_rule_k_of_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) (ctor : arena.handle.NIdx) :
    LS pers (fun a b => b = a) (arena.core.rec_rule_k_of pers vis st rf ctor) lst
      (recRuleKOf lf (absNIdx ctor)) := by
  rw [arena.core.rec_rule_k_of, recRuleKOf]
  lockstep

@[lockstep] theorem rec_rule_eta_of_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) (rn ctor : arena.handle.NIdx) :
    LS pers (fun a b => b = a) (arena.core.rec_rule_eta_of pers vis st rf rn ctor) lst
      (recRuleEtaOf lf (absNIdx rn) (absNIdx ctor)) := by
  rw [arena.core.rec_rule_eta_of, recRuleEtaOf]
  lockstep
  -- the level-parameter comparison, in `nidx_vec_beq`'s `decide` form
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp_all [absNIdxList]
    exact beq_eq_decide _ _

@[lockstep] theorem rec_rule_bits_ls {pers st lst} {vis : Std.U64} {rf lf}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (hvis : absU vis = lf.visibleBelow) (rn : arena.handle.NIdx)
    (rl : arena.env.IRecRule) :
    LS pers (fun a b => b = absIRecRule a) (arena.core.rec_rule_bits pers vis st rf rn rl) lst
      (recRuleBits lf (absNIdx rn) (absIRecRule rl)) := by
  rw [arena.core.rec_rule_bits, recRuleBits]
  lockstep

end RuleBits

open Lockstep in
/-- `arena::canon::eidx_vec_beq` from `0` is `==` on the abstracted lists. -/
@[lockstep] theorem canon_eidx_vec_beq_twin (a b : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.canon.eidx_vec_beq a b 0#usize) (fun o => o = (absEIdxL a == absEIdxL b)) := by
  intro o h
  rw [eidx_vec_beq_refines h]
  have e : ∀ v : alloc.vec.Vec arena.handle.EIdx, absEIdxLFrom v 0#usize = absEIdxL v := by
    intro v; simp [absEIdxLFrom, absEIdxL]
  rw [e, e]
  cases h' : decide (absEIdxL a = absEIdxL b) <;> simp_all

end ConRon.Refine2
