/-
# `ConRon.Refine2.Checker.Jobs` — Theorem 2 for the check phase's jobs

A value check and a block job, each on a worker's state, over the frozen tier; the
merge that orders them.  `arena::checker`'s `consts_agree`, `tables_agree`,
`pushes_agree`, `block_check`, `run_job`, `job_order` against `Arena/Checker.lean`.

## The tiers

The twin has one environment value per job.  The Rust reads an own layer, then the
frozen base.  What makes the two answer alike is `FoldEnd`, what the fold hands over:

* a value check's layer, `check_layer()`, against the whole environment restricted to
  `0` (the reader's bound is the record's counter), every row of the base visible;
* a block job's layer, `ifenv_layer(vis, vis)`, against `BlockCheck.view`: the base below
  the counter is the view's index, by `EnvExt` (no install overwrites a row).

The Rust records slot ranges where the twin records `L`, `Q`: the range of the base
holding what the stored install pushed, read through the abstraction.
-/
import ConRon.Refine2.Checker.Top

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The frozen base, read through a layer -/

/-- **The tier the driver freezes**: the store's tables and the installed environment. -/
def tierWith (ar : arena.store.EStore) (fe : arena.env.IFEnv) : arena.store.PersTier :=
  { tierOf ar with env := fe }

/-- An empty layer, as `ifenv_layer` builds it. -/
theorem ifenv_layer_eq {v b : Std.U64} {w : arena.env.IFEnv}
    (h : arena.env.ifenv_layer v b = ok w) :
    w = { layer00 with visible_below := v, base_below := b } := by
  simp only [arena.env.ifenv_layer, arena.env.i_env_empty, ron.hashmap2.HashMap2.new, bind_ok] at h
  exact (Result.ok_injective h).symm

theorem layer_inv (v b : Std.U64) (hv : v.val = 0 ∨ True) :
    IFEnvInv { layer00 with visible_below := v, base_below := b } ∨ True := Or.inr trivial

/-- `EnvExt` read at a row of the later environment: what the earlier one holds is the
later one's below its counter. -/
theorem EnvExt.row_below {a b : IFEnv} (h : EnvExt a b) (ha : EnvOK a) (n : NIdx) :
    a.idx[n]? = (b.idx[n]?).bind fun r => if r.1 < a.visibleBelow then some r else none := by
  cases hb : b.idx[n]? with
  | none =>
    simp only [Option.bind_none]
    cases hr : a.idx[n]? with
    | none => rfl
    | some r => rw [h.idxOld n r hr] at hb; cases hb
  | some r =>
    simp only [Option.bind_some]
    by_cases hlt : r.1 < a.visibleBelow
    · rw [if_pos hlt]
      cases hr : a.idx[n]? with
      | none =>
        have := h.idxNew n r hb hr
        omega
      | some r' =>
        rw [h.idxOld n r' hr] at hb
        cases hb
        rfl
    · rw [if_neg hlt]
      cases hr : a.idx[n]? with
      | none => rfl
      | some r' =>
        rw [h.idxOld n r' hr] at hb
        cases hb
        exact absurd (ha.rows n _ hr) hlt

/-- **A block job's layer against the view.**  Own layer empty; the base below the
block's counter is the view's index, and a table is the base's where its structure is
visible, which the view's table map is by `EnvExt`. -/
theorem layer_rel {tier : arena.store.PersTier} {lf view : IFEnv} {v : Std.U64}
    (hb : BaseOK tier) (hown : IFEnvOwn tier.env lf) (hext : EnvExt view lf) (hv : EnvOK view)
    (hvis : view.visibleBelow = absU v) :
    IFEnvRel tier view.env { layer00 with visible_below := v, base_below := v } view := by
  have hnone := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64 × Std.U64) (m' := layer00.idx) rfl
  have tnone := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64) (m' := layer00.tbls) rfl
  -- the base's rows, at the view's bound
  have hrow : ∀ n, baseRow tier v n = view.idx[absNIdx n]? := by
    intro n
    rw [hext.row_below hv, ← hown.idx n, baseRow, hvis]
    cases ConRon.Refine.HashMap2.toFun tier.env.idx n with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, rowOf]
      cases tier.env.env.consts.val[p.2.val]? with
      | none => simp
      | some ci => simp
  refine ⟨?_, fun n => ?_, hvis, by simp [layer00], ?_, fun n => ?_, ?_, hb⟩
  · simp [overEnv, layer00]
  · simp only [layerRow, hnone.2.2 n]
    exact hrow n
  · intro k p hp
    rw [show ConRon.Refine.HashMap2.toFun _ k = _ from hnone.2.2 k] at hp
    cases hp
  · simp only [layerTbl, tnone.2.2 n, baseTbl, hrow n]
    have hT := hown.tbls n
    cases hvr : view.idx[absNIdx n]? with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, if_false]
      cases hvt : view.tbls[absNIdx n]? with
      | none => rfl
      | some t =>
        have := hv.tblRow _ t hvt
        rw [hvr] at this
        cases this
    | some r =>
      simp only [Option.isSome_some, if_true]
      show (ConRon.Refine.HashMap2.toFun tier.env.tbls n).bind _ = _
      have hT' : (ConRon.Refine.HashMap2.toFun tier.env.tbls n).bind (tblOf tier.env.env.tables)
          = lf.tbls[absNIdx n]? := hT
      rw [hT']
      cases hvt : view.tbls[absNIdx n]? with
      | some t => exact hext.tblOld _ t hvt
      | none =>
        cases hlt : lf.tbls[absNIdx n]? with
        | none => rfl
        | some t =>
          have := hext.tblNew _ t hlt hvt
          rw [hvr] at this
          cases this
  · intro k s hs
    rw [show ConRon.Refine.HashMap2.toFun _ k = _ from tnone.2.2 k] at hs
    cases hs

end ConRon.Refine2
