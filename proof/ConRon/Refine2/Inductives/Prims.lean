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

/-! ## The checker tier's statements in `LS` form

The checker tier's own `@[lockstep]` companions (`Checker/{Base,Pins,Axioms}`)
serve the tier directly.  What is left here has none there: `Checker/Canon`'s
are `private`/`local`, and `name_read_sim` has no `LS` form.  One
`LS.ofSim₀` line each, in their own namespace so a companion the checker lane
adds later does not clash. -/

namespace IndPrims

end IndPrims

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
attribute [local lockstep_simp] Lockstep.absIRecRule_ctor absIRecRule_nfields_eq
  IndModeledPrims.absIRecRule_ctorParams Lockstep.absIRecRule_fire
  Lockstep.absIRecRule_rhs Lockstep.absIRecRule_k Lockstep.absIRecRule_eta
  IndModeledPrims.absIRecRule_paramsBlind Lockstep.PC1.absIIndCaps_eta Lockstep.PC1.absIIndCaps_etaCtor IndModeledPrims.absIIndCaps_ruleK IndModeledPrims.decide_u64_eq_zero etag_const_abs

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
