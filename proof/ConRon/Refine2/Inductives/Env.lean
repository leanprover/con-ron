/-
# `ConRon.Refine2.Inductives.Env` — the tier's environment readers and the Core front doors

**Task #105** (DESIGN.md §8.2, Theorem 2).  The layer of the tier that sees
the Core knot's front doors (`Refine2/Checker/KnotHyp.lean`: `whnf_ls`,
`infer_type_core_ls`, `is_def_eq_core_ls`, …) and the Core leaves
(`Refine2/Core/LS/Leaves.lean`: `zero_level_ls`, `lvl_eq_ls`,
`lift_fueled_ls`), but not the checker tier proper (`Checker/Base.lean` and
above, which `Inductives/Prims.lean` imports).  It carries the environment
index's readers as `TwinEq`s and the side alternatives that turn the tier's
`IFEnvRelI rf lf` (and a split counter) into the front doors' `CoreCtx vis rf
lf` — moved here from `Inductives/Shape.lean`.
-/
import ConRon.Refine2.Inductives.Abs
import ConRon.Refine2.Checker.KnotHyp
import ConRon.Refine2.Core.LS.Leaves

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- The Core front doors (`Refine2/Checker/KnotHyp.lean`) take `CoreCtx vis rf
lf`; the tier carries `IFEnvRelI rf lf` and, at a split counter, `absU vis =
lf.visibleBelow` — `IFEnvInv.coreCtx`/`coreCtxSelf` turn those into it. -/
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| first
      | (apply IFEnvInv.coreCtxSelf <;> first
          | (apply IFEnvRelI.rel; assumption) | (apply IFEnvRelI.inv; assumption))
      | (apply IFEnvInv.coreCtx <;> first
          | (apply IFEnvRelI.rel; assumption) | (apply IFEnvRelI.inv; assumption)
          | assumption | (checker_env_facts; simp_all; done)))


-- A twin `if` whose test a `TwinEq` rewrote to a literal.
attribute [lockstep_simp] ite_true ite_false

/-! ## Two environment-record constants -/

open Lockstep in
/-- `i_ind_caps_default` is the twin's `{}` (the zero word is `default`, the
empty `if_all_zero` is `.ifAllZero []`). -/
@[lockstep] theorem i_ind_caps_default_twin :
    LSP arena.env.i_ind_caps_default (fun o => TwinEq ({} : IIndCaps) (absIIndCaps o) ∧
      ConRon.Refine.PropWhenWF o.sort_z) := by
  intro o h
  refine ⟨?_, ?_⟩
  swap
  · rw [arena.env.i_ind_caps_default] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    exact ConRon.Refine.PropWhen.if_all_zero_wf (fun n hn => by simp [alloc.vec.Vec.new] at hn) hpw
  simp only [arena.env.i_ind_caps_default, arena.handle.NIdx.of_word,
    kernel.prop_when.if_all_zero, kernel.prop_when.of_repr, alloc.vec.Vec.new,
    alloc.vec.Vec.len] at h
  simp at h
  rw [ite_eq_left (by rfl)] at h
  simp at h
  subst h
  simp [TwinEq, absIIndCaps]
  rfl

/-! ## The environment index's readers, as `TwinEq`s

`ifenv_find`/`find_ci` read the Rust index; the twin's `find?` is the same
lookup (`ifenv_find_abs`, `Refine2/Core/Arms/Delta.lean`).  The twin
environment is fixed by the `CoreCtx` side goal, which the tier's side
extension discharges from `IFEnvRelI` (and the split counter). -/

open Lockstep in
@[lockstep] theorem ifenv_find_twin {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (n : arena.handle.NIdx) (hctx : CoreCtx vis rf lf) :
    LSP (arena.env.ifenv_find vis rf n)
      (fun o => TwinEq (lf.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs hctx h).symm


-- `lf.restrictTo (absU vis)` at the split counter IS `lf` (`hvis`): the
-- checker tier's statements are at the restriction, the tier's twins at `lf`.
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (simp only [IFEnv.restrictTo] at *; checker_env_facts; simp_all; done))



end ConRon.Refine2
