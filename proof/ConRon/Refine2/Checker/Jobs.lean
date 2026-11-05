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
    · rw [ite_eq_left hlt]
      cases hr : a.idx[n]? with
      | none =>
        have := h.idxNew n r hb hr
        omega
      | some r' =>
        rw [h.idxOld n r' hr] at hb
        cases hb
        rfl
    · rw [ite_eq_right hlt]
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
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      cases hvt : view.tbls[absNIdx n]? with
      | none => rfl
      | some t =>
        have := hv.tblRow _ t hvt
        rw [hvr] at this
        cases this
    | some r =>
      simp only [Option.isSome_some, ite_true]
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

/-! ## A value check's layer -/

/-- **A value check's layer against the whole environment**: its own layer is empty,
every row of the base is below the largest counter, and a table's structure has a row. -/
theorem check_layer_rel {tier : arena.store.PersTier} {lf : IFEnv} {layer : arena.env.IFEnv}
    (hb : BaseOK tier) (hown : IFEnvOwn tier.env lf) (hok : EnvOK lf)
    (hL : arena.checker.check_layer = ok layer) :
    IFEnvRel tier lf.env layer (lf.restrictTo 0) ∧ IFEnvInv layer := by
  rw [arena.checker.check_layer] at hL
  obtain rfl := ifenv_layer_eq hL
  have hnone := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64 × Std.U64) (m' := layer00.idx) rfl
  have tnone := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.NIdx) (V := Std.U64) (m' := layer00.tbls) rfl
  have hrow : ∀ n, baseRow tier core.num.U64.MAX n = lf.idx[absNIdx n]? := by
    intro n
    rw [← hown.idx n, baseRow]
    cases hp : ConRon.Refine.HashMap2.toFun tier.env.idx n with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, rowOf]
      cases hc : tier.env.env.consts.val[p.2.val]? with
      | none => simp
      | some ci =>
        have hr : lf.idx[absNIdx n]? = some (absU p.1, absIConstantInfo ci) := by
          rw [← hown.idx n, hp]; simp [hc]
        have h1 := hok.rows _ _ hr
        have h2 : lf.visibleBelow < 2 ^ 64 := by
          rw [hown.visibleBelow]; exact tier.env.visible_below.hBounds
        have hm : absU core.num.U64.MAX = 2 ^ 64 - 1 := rfl
        have h3 : absU p.1 < absU core.num.U64.MAX := by
          rw [hm]
          have h1' : absU p.1 < lf.visibleBelow := h1
          omega
        simpa using h3
  refine ⟨⟨?_, fun n => ?_, ?_, by simp [layer00], ?_, fun n => ?_, ?_, hb⟩, ?_⟩
  · simp [overEnv, layer00, IFEnv.restrictTo]
  · simp only [layerRow, hnone.2.2 n]
    exact hrow n
  · simp [IFEnv.restrictTo, absU]
  · intro k p hp
    rw [show ConRon.Refine.HashMap2.toFun _ k = _ from hnone.2.2 k] at hp
    cases hp
  · simp only [layerTbl, tnone.2.2 n, baseTbl, hrow n]
    show _ = lf.tbls[absNIdx n]?
    cases hr : lf.idx[absNIdx n]? with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      cases ht : lf.tbls[absNIdx n]? with
      | none => rfl
      | some t =>
        have := hok.tblRow _ t ht
        rw [hr] at this
        cases this
    | some r =>
      simp only [Option.isSome_some, ite_true]
      exact hown.tbls n
  · intro k s hs
    rw [show ConRon.Refine.HashMap2.toFun _ k = _ from tnone.2.2 k] at hs
    cases hs
  · refine ⟨hnone.1, by simp [layer00], fun n p hp => ?_, tnone.1, fun n q hq => ?_⟩
    · rw [show ConRon.Refine.HashMap2.toFun _ n = _ from hnone.2.2 n] at hp; cases hp
    · rw [show ConRon.Refine.HashMap2.toFun _ n = _ from tnone.2.2 n] at hq; cases hq

/-! ## A block's job -/

/-- A recorded job against the twin's, at the frozen tier. -/
structure JobRel (tier : arena.store.PersTier) (b : arena.checker.BlockCheck) (tb : BlockCheck) :
    Prop where
  layer : ∀ w, arena.env.ifenv_layer b.vis b.vis = ok w → IFEnvRelI tier tb.view.env w tb.view
  block : tb.block = b.block.val.map absIConstantInfo
  nP : tb.nP = absU b.n_p
  pos : tb.pos = absU b.pos
  clo : b.c_lo.val ≤ b.c_hi.val
  chi : b.c_hi.val ≤ tier.env.env.consts.val.length
  tlo : b.t_lo.val ≤ b.t_hi.val
  thi : b.t_hi.val ≤ tier.env.env.tables.val.length
  L : tb.L = ((tier.env.env.consts.val.drop b.c_lo.val).take (b.c_hi.val - b.c_lo.val)).map
    absIConstantInfo
  Q : tb.Q = ((tier.env.env.tables.val.drop b.t_lo.val).take (b.t_hi.val - b.t_lo.val)).map
    absIProjTable

theorem listBeqBy_length {α : Type} {f : α → α → Bool} :
    ∀ {xs ys : List α}, xs.length ≠ ys.length → listBeqBy f xs ys = false
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [listBeqBy]
    rw [listBeqBy_length (by simpa using h)]
    simp

/-- `consts_agree` from slot `i` on is `listBeqBy` of the rest, when the two ranges have
the same length. -/
theorem consts_agree_abs {tier : arena.store.PersTier} {w : arena.env.IFEnv}
    {b : arena.checker.BlockCheck} (hw : ∀ c ∈ w.env.consts.val, IConstantInfoWF c)
    (hb : ∀ c ∈ tier.env.env.consts.val, IConstantInfoWF c)
    (hlen : w.env.consts.val.length = b.c_hi.val - b.c_lo.val)
    (hhi : b.c_hi.val ≤ tier.env.env.consts.val.length) (hlo : b.c_lo.val ≤ b.c_hi.val) (n : Nat) :
    ∀ (i : Std.Usize) {o : Bool}, w.env.consts.val.length - i.val = n →
      arena.checker.consts_agree tier w b i = ok o →
      o = listBeqBy IConstantInfo.beqP ((w.env.consts.val.drop i.val).map absIConstantInfo)
        (((tier.env.env.consts.val.drop b.c_lo.val).take (b.c_hi.val - b.c_lo.val)).drop i.val
          |>.map absIConstantInfo) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i o hn h
    rw [arena.checker.consts_agree.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val w.env.consts
    by_cases hge : i ≥ alloc.vec.Vec.len w.env.consts
    · have hle : w.env.consts.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hle, List.drop_eq_nil_of_le (by simp; omega)]
      rfl
    · have hlt : i.val < w.env.consts.val.length := by scalar_tac
      rw [ite_eq_right hge] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hfit : b.c_lo.val ≤ Std.Usize.max :=
        le_trans (le_trans hlo hhi) tier.env.env.consts.property
      have hi2v : i2.val = b.c_lo.val := by
        rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hfit]
        exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
      obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hsv : s.val = b.c_lo.val + i.val := by
        rw [ConRon.Refine.HashMap.uscalar_add_eq hs, hi2v]
      have hslt : s.val < tier.env.env.consts.val.length := by omega
      have hsb : s < alloc.vec.Vec.len tier.env.env.consts := by
        apply (Std.UScalar.lt_equiv _ _).mpr
        rw [alloc.vec.Vec.len_val]; exact hslt
      rw [ite_eq_left hsb] at h
      obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨ii1, hii1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hib, hiiE⟩ := ConRon.Refine2.ExprOps.vecIndexAt hii
      obtain ⟨hi1b, hii1E⟩ := ConRon.Refine2.ExprOps.vecIndexAt hii1
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbeq := i_constant_info_beq_p_abs (hw ii (by rw [← hiiE]; exact List.getElem_mem _))
        (hb ii1 (by rw [← hii1E]; exact List.getElem_mem _)) hb1
      have hdw : w.env.consts.val.drop i.val = ii :: w.env.consts.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hiiE]
      have hdb : ((tier.env.env.consts.val.drop b.c_lo.val).take (b.c_hi.val - b.c_lo.val)).drop i.val
          = ii1 :: ((tier.env.env.consts.val.drop b.c_lo.val).take
            (b.c_hi.val - b.c_lo.val)).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        congr 1
        rw [← hii1E]
        simp [List.getElem_take, List.getElem_drop, hsv]
      rw [hdw, hdb, List.map_cons, List.map_cons]
      simp only [listBeqBy]
      rw [← hbeq]
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        simpa using (Result.ok_injective h).symm
      | true =>
        simp only [↓reduceIte] at h
        obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi4v : i4.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi4
        have := ih (w.env.consts.val.length - i4.val) (by omega) i4 rfl h
        rw [hi4v] at this
        simpa using this

/-- `tables_agree` likewise. -/
theorem tables_agree_abs {tier : arena.store.PersTier} {w : arena.env.IFEnv}
    {b : arena.checker.BlockCheck}
    (hlen : w.env.tables.val.length = b.t_hi.val - b.t_lo.val)
    (hhi : b.t_hi.val ≤ tier.env.env.tables.val.length) (hlo : b.t_lo.val ≤ b.t_hi.val) (n : Nat) :
    ∀ (i : Std.Usize) {o : Bool}, w.env.tables.val.length - i.val = n →
      arena.checker.tables_agree tier w b i = ok o →
      o = listBeqBy IProjTable.beqP ((w.env.tables.val.drop i.val).map absIProjTable)
        (((tier.env.env.tables.val.drop b.t_lo.val).take (b.t_hi.val - b.t_lo.val)).drop i.val
          |>.map absIProjTable) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i o hn h
    rw [arena.checker.tables_agree.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val w.env.tables
    by_cases hge : i ≥ alloc.vec.Vec.len w.env.tables
    · have hle : w.env.tables.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hle, List.drop_eq_nil_of_le (by simp; omega)]
      rfl
    · have hlt : i.val < w.env.tables.val.length := by scalar_tac
      rw [ite_eq_right hge] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hfit : b.t_lo.val ≤ Std.Usize.max :=
        le_trans (le_trans hlo hhi) tier.env.env.tables.property
      have hi2v : i2.val = b.t_lo.val := by
        rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hfit]
        exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
      obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hsv : s.val = b.t_lo.val + i.val := by
        rw [ConRon.Refine.HashMap.uscalar_add_eq hs, hi2v]
      have hslt : s.val < tier.env.env.tables.val.length := by omega
      have hsb : s < alloc.vec.Vec.len tier.env.env.tables := by
        apply (Std.UScalar.lt_equiv _ _).mpr
        rw [alloc.vec.Vec.len_val]; exact hslt
      rw [ite_eq_left hsb] at h
      obtain ⟨tt, htt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨htb, httE⟩ := ConRon.Refine2.ExprOps.vecIndexAt htt
      obtain ⟨hitb, hitE⟩ := ConRon.Refine2.ExprOps.vecIndexAt hit
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hbeq := i_proj_table_beq_p_abs hb1
      have hdw : w.env.tables.val.drop i.val = it :: w.env.tables.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hitE]
      have hdb : ((tier.env.env.tables.val.drop b.t_lo.val).take (b.t_hi.val - b.t_lo.val)).drop i.val
          = tt :: ((tier.env.env.tables.val.drop b.t_lo.val).take
            (b.t_hi.val - b.t_lo.val)).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        congr 1
        rw [← httE]
        simp [List.getElem_take, List.getElem_drop, hsv]
      rw [hdw, hdb, List.map_cons, List.map_cons]
      simp only [listBeqBy]
      rw [← hbeq]
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        simpa using (Result.ok_injective h).symm
      | true =>
        simp only [↓reduceIte] at h
        obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi4v : i4.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi4
        have := ih (w.env.tables.val.length - i4.val) (by omega) i4 rfl h
        rw [hi4v] at this
        simpa using this

/-- `pushes_agree` ⊑ `pushesAgree`, at what the job's own layer holds. -/
theorem pushes_agree_abs {tier : arena.store.PersTier} {w : arena.env.IFEnv}
    {b : arena.checker.BlockCheck} {tb : BlockCheck} {W' : IFEnv} {o : Bool}
    (hJ : JobRel tier b tb) (hW : IFEnvRel tier tb.view.env w W')
    (hb : BaseOK tier) (h : arena.checker.pushes_agree tier w b = ok o) :
    o = pushesAgree tb.view W' tb.L tb.Q := by
  have hc : (W'.env.consts.take (W'.env.consts.length - tb.view.env.consts.length)).reverse
      = w.env.consts.val.map absIConstantInfo := by
    rw [hW.env]
    simp [overEnv]
  have ht : (W'.env.tables.take (W'.env.tables.length - tb.view.env.tables.length)).reverse
      = w.env.tables.val.map absIProjTable := by
    rw [hW.env]
    simp [overEnv]
  have hz0 : (0#usize : Std.Usize).val = 0 := by simp
  rw [pushesAgree, hc, ht, hJ.L, hJ.Q]
  rw [arena.checker.pushes_agree] at h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi1v : i1.val = w.env.consts.val.length := by
    simp only [lift, Result.ok.injEq] at hi1
    subst hi1
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  have hi2v : i2.val = b.c_hi.val - b.c_lo.val := ConRon.Refine.HashMap.uscalar_sub_eq hi2
  by_cases he1 : i1 = i2
  · rw [ite_eq_left he1] at h
    have hlc : w.env.consts.val.length = b.c_hi.val - b.c_lo.val := by rw [← hi1v, he1, hi2v]
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi3v : i3.val = w.env.tables.val.length := by
      simp only [lift, Result.ok.injEq] at hi3
      subst hi3
      rw [usize_cast_u64_val']
      simp [alloc.vec.Vec.len]
    have hi5v : i5.val = b.t_hi.val - b.t_lo.val := ConRon.Refine.HashMap.uscalar_sub_eq hi5
    by_cases he2 : i3 = i5
    · rw [ite_eq_left he2] at h
      have hlt : w.env.tables.val.length = b.t_hi.val - b.t_lo.val := by rw [← hi3v, he2, hi5v]
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h1 := consts_agree_abs hW.envWF hb.envWF hlc hJ.chi hJ.clo _ 0#usize rfl hb1
      simp only [hz0, List.drop_zero] at h1
      rw [← h1]
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        simpa using (Result.ok_injective h).symm
      | true =>
        simp only [↓reduceIte] at h
        have h2 := tables_agree_abs hlt hJ.thi hJ.tlo _ 0#usize rfl h
        simp only [hz0, List.drop_zero] at h2
        simpa using h2
    · rw [ite_eq_right he2] at h
      cases Result.ok_injective h
      have hne : w.env.tables.val.length ≠ b.t_hi.val - b.t_lo.val := by
        intro hc'
        exact he2 (UScalar.eq_imp _ _ (by rw [hi3v, hi5v, hc']))
      rw [listBeqBy_length (f := IProjTable.beqP) (by
        simp only [List.length_map, List.length_take, List.length_drop]
        have := hJ.thi
        omega)]
      simp
  · rw [ite_eq_right he1] at h
    cases Result.ok_injective h
    have hne : w.env.consts.val.length ≠ b.c_hi.val - b.c_lo.val := by
      intro hc'
      exact he1 (UScalar.eq_imp _ _ (by rw [hi1v, hi2v, hc']))
    rw [listBeqBy_length (f := IConstantInfo.beqP) (by
      simp only [List.length_map, List.length_take, List.length_drop]
      have := hJ.chi
      omega)]
    simp

/-- **`block_check` ⊑ `blockCheck`**: the block's checked install at an empty layer over
the frozen base, framed, and the comparison of its pushes with the stored install's.
A difference is an internal error on both sides.  Nothing the job builds outlives it. -/
theorem block_check_refines {tier st lst} {mode : kernel.env.CheckMode}
    {lpins : List INatOpPinSet} {b : arena.checker.BlockCheck} {tb : BlockCheck} {o}
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st) (htf : tier.frozen = true)
    (hJ : JobRel tier b tb)
    (hrun : arena.checker.block_check tier st mode b = ok o) :
    SimIdle tier lst o (blockCheck (ConRon.Refine.absMode mode) lpins tb) := by
  rw [arena.checker.block_check] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (enter_record_sim hidle hinv h1).apply
  obtain ⟨f, hf, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hfe := hJ.layer w0 hw0
  obtain ⟨⟨r, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := check_ind_decl_refines hrel1 hinv1 hfe.rel hfe.inv h2
  obtain ⟨st3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [SimRel₀, AOutRel₀] at hS
  have hbody : checkDecl (ConRon.Refine.absMode mode) lpins tb.view (.indDecl tb.block tb.nP)
      = checkIndDeclArmSpec (ConRon.Refine.absMode mode) tb.view (absICIL b.block) (absU b.n_p) := by
    rw [checkDecl_indDecl, hJ.block, hJ.nP]
    rfl
  simp only [SimIdle, blockCheck, am_run_bind, hx1, except_ok_bind, hbody]
  cases r with
  | Err e =>
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hv
    cases Result.ok_injective hrun
    exact AErrSim.bind (AErrSim.scratchRun hS) _
  | Ok wf =>
    obtain ⟨W', lst2a, hx2a, hW, hrel2a, hinv2a⟩ := hS
    obtain ⟨lst2, hx2, hrel2, hinv2⟩ :=
      stored_frame_ok htf hrel1 hinv1 hrel2a hinv2a hf h3 hx2a
    simp only [hx2, except_ok_bind]
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨b1, hb1, hv⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv
    have hag := pushes_agree_abs hJ hW.rel hfe.rel.base hb1
    rw [← hag]
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hv
      obtain ⟨sl, -, hv⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv
      obtain ⟨v1, -, hv⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv
      obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      obtain rfl : v = _ := (Result.ok_injective hv).symm
      exact AErrSim.internal rfl
    | true =>
      simp only [↓reduceIte] at hv
      cases Result.ok_injective hv
      obtain ⟨st4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      obtain ⟨lst3, hx3, hidle3, hinv3⟩ := leave_record_rel hrel2 hinv2 htf h4
      have hd : (dropScratch : AM Unit).run lst2
          = .ok ((), { lst2 with store := lst2.store.dropScratch, caches := Caches.empty }) := rfl
      rw [hd] at hx3
      cases hx3
      exact ⟨_, rfl, hidle3, hinv3, lst2.store, rfl⟩

/-! ## The jobs, and their order -/

/-- A job, as the twin's. -/
def absJob (j : Bool × Std.U64) : Job := (j.1, absU j.2)

/-- **What the driver hands the pool**: the check layer, the records, the block jobs. -/
structure JobsRel (tier : arena.store.PersTier) (layer : arena.env.IFEnv)
    (pend : alloc.vec.Vec arena.checker.PendingCheck)
    (d : alloc.vec.Vec arena.checker.BlockCheck) (lf : IFEnv) (lp : Array PendingCheck)
    (lD : Array BlockCheck) : Prop where
  rel : IFEnvRel tier lf.env layer (lf.restrictTo 0)
  inv : IFEnvInv layer
  pend : lp = (absPendingCheckL pend).toArray
  jobs : List.Forall₂ (JobRel tier) d.val lD.toList

theorem checkPending_restrict0 (mode : ConLeche.CheckMode) (lf : IFEnv) (pc : PendingCheck) :
    checkPending mode (lf.restrictTo 0) pc = checkPending mode lf pc := rfl

theorem forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h : i < l₁.length),
      ∃ y, l₂[i]? = some y ∧ R l₁[i] y
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hr _, 0, _ => ⟨_, rfl, hr⟩
  | _, _, .cons _ ht, i + 1, h => forall₂_get ht i (by simpa using h)

/-- A cast that fits, at an index read. -/
private theorem cast_val {i : Std.U64} {x : Std.Usize} (hi : i.val ≤ Std.Usize.max)
    (h : lift (UScalar.cast .Usize i) = (ok x : Result Std.Usize)) : x.val = i.val := by
  rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hi]
  exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective h).symm

/-- **`run_job` ⊑ `runJob`, accepting**: a job the Rust ran to `Ok` the twin ran to `.ok`,
between two idle states.  What a failing job answers is on a path no accept reaches.
`hj`: an index `job_order` handed out is a `usize` cast up. -/
theorem run_job_refines {tier layer pend d lf lp lD st lst st'}
    {mode : kernel.env.CheckMode} {lpins : List INatOpPinSet} {j : Bool × Std.U64}
    (hJ : JobsRel tier layer pend d lf lp lD)
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st) (htf : tier.frozen = true)
    (hj : j.2.val ≤ Std.Usize.max)
    (hrun : arena.checker.run_job tier st mode layer pend d j = ok (.Ok (), st')) :
    ∃ lst', runJob (ConRon.Refine.absMode mode) lpins lf lp lD (absJob j) lst = .ok (.ok (), lst') ∧
      AIdle tier st' lst' ∧ AStateInv tier st' := by
  obtain ⟨jb, ji⟩ := j
  simp only at hj
  rw [arena.checker.run_job] at hrun
  change (if jb = true then _ else _) = _ at hrun
  cases jb with
  | true =>
    simp only [↓reduceIte] at hrun
    obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi1v := cast_val hj hi1
    by_cases hb : i1 < alloc.vec.Vec.len d
    · rw [ite_eq_left hb] at hrun
      have hb' : ji.val < d.val.length := by
        have := (Std.UScalar.lt_equiv _ _).mp hb
        rw [hi1v] at this
        simpa using this
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi3v := cast_val hj hi3
      obtain ⟨bc, hbc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hb3, hbc'⟩ := ConRon.Refine2.ExprOps.vecIndexAt hbc
      have hbc2 : bc = d.val[ji.val] := by rw [← hbc']; simp only [hi3v]
      subst hbc2
      obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases r with
      | Err e =>
        obtain ⟨i4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨bc1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
      | Ok u =>
        cases Result.ok_injective hrun
        obtain ⟨tb, htb, hrel⟩ := forall₂_get hJ.jobs ji.val hb'
        have hS := block_check_refines (lpins := lpins) hidle hinv htf hrel h1
        obtain ⟨lst', hx, hi', hv', -⟩ := hS
        refine ⟨lst', ?_, hi', hv'⟩
        have hd : lD[absU ji]? = some tb := by
          simpa [absU] using htb
        have hx' : blockCheck (ConRon.Refine.absMode mode) lpins tb lst = .ok ((), lst') := hx
        simp [runJob, absJob, hd, hx']
    · rw [ite_eq_right hb] at hrun
      obtain ⟨_, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨_, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrun
    obtain ⟨i1, hi1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hi1v := cast_val hj hi1
    by_cases hb : i1 < alloc.vec.Vec.len pend
    · rw [ite_eq_left hb] at hrun
      have hb' : ji.val < pend.val.length := by
        have := (Std.UScalar.lt_equiv _ _).mp hb
        rw [hi1v] at this
        simpa using this
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi3v := cast_val hj hi3
      obtain ⟨pc, hpc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hb3, hpc'⟩ := ConRon.Refine2.ExprOps.vecIndexAt hpc
      have hpc2 : pc = pend.val[ji.val] := by rw [← hpc']; simp only [hi3v]
      subst hpc2
      obtain ⟨⟨r, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases r with
      | Err e =>
        obtain ⟨i4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨pc1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
      | Ok u =>
        cases Result.ok_injective hrun
        have hS := check_pending_refines hidle hinv htf hJ.rel hJ.inv h1
        obtain ⟨lst', hx, hi', hv', -⟩ := hS
        refine ⟨lst', ?_, hi', hv'⟩
        have hp : lp[absU ji]? = some (absPendingCheck pend.val[ji.val]) := by
          rw [hJ.pend]
          simp [absPendingCheckL, absU, hb']
        have hx' : checkPending (ConRon.Refine.absMode mode) lf (absPendingCheck pend.val[ji.val]) lst
            = .ok ((), lst') := hx
        simp only [runJob, absJob, hp, hx', Bool.false_eq_true, ↓reduceIte]
    · rw [ite_eq_right hb] at hrun
      obtain ⟨_, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨_, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun

/-- `job_order_go` is the twin's merge, on the abstracted arrays, and every index it hands
out is a `usize` cast up. -/
theorem job_order_go_abs {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {d : alloc.vec.Vec arena.checker.BlockCheck} {lD : Array BlockCheck}
    (hD : List.Forall₂ (fun (b : arena.checker.BlockCheck) (tb : BlockCheck) => tb.pos = absU b.pos)
      d.val lD.toList) (n : Nat) :
    ∀ (a b : Std.Usize) (acc : alloc.vec.Vec (Bool × Std.U64)) {r},
      pend.val.length - a.val + (d.val.length - b.val) = n →
      (∀ j ∈ acc.val, j.2.val ≤ Std.Usize.max) →
      arena.checker.job_order_go pend d a b acc = ok r →
      r.val.map absJob = (jobOrderGo (absPendingCheckL pend).toArray lD a.val b.val
        (acc.val.map absJob).toArray).toList ∧ ∀ j ∈ r.val, j.2.val ≤ Std.Usize.max := by
  have hlD : lD.size = d.val.length := by
    have := hD.length_eq
    simpa using this.symm
  have hlp : (absPendingCheckL pend).toArray.size = pend.val.length := by
    simp [absPendingCheckL]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b acc r hn hacc h
    rw [arena.checker.job_order_go.eq_def] at h
    dsimp only at h
    rw [jobOrderGo]
    have hpush : ∀ {x : Bool × Std.U64} {acc1 : alloc.vec.Vec (Bool × Std.U64)},
        alloc.vec.Vec.push acc x = ok acc1 →
        (acc1.val.map absJob).toArray = (acc.val.map absJob).toArray.push (absJob x) ∧
          (x.2.val ≤ Std.Usize.max → ∀ j ∈ acc1.val, j.2.val ≤ Std.Usize.max) := by
      intro x acc1 hp
      rw [show acc1.val = acc.val ++ [x] from ConRon.Refine.vec_push_val hp]
      refine ⟨by simp, fun hx j hj => ?_⟩
      rcases List.mem_append.mp hj with h1 | h1
      · exact hacc j h1
      · rw [List.mem_singleton.mp h1]; exact hx
    have hlpv := alloc.vec.Vec.len_val pend
    have hldv := alloc.vec.Vec.len_val d
    -- the record's arm, which three branches share
    have hpa : a.val < pend.val.length →
        (do
          let i2 ← lift (UScalar.cast .U64 a)
          let acc1 ← alloc.vec.Vec.push acc (false, i2)
          let i3 ← a + 1#usize
          arena.checker.job_order_go pend d i3 b acc1) = ok r →
        r.val.map absJob = (jobOrderGo (absPendingCheckL pend).toArray lD (a.val + 1) b.val
          ((acc.val.map absJob).toArray.push (false, a.val))).toList ∧
          ∀ j ∈ r.val, j.2.val ≤ Std.Usize.max := by
      intro ha' h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = a.val := by
        simp only [lift, Result.ok.injEq] at hi2
        rw [← hi2, usize_cast_u64_val]
      obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v : i3.val = a.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
      obtain ⟨he, hbd⟩ := hpush hacc1
      have hrec := ih _ (by omega) i3 b acc1 rfl (hbd (by
        simp only [hi2v]; scalar_tac)) h
      rw [he, hi3v] at hrec
      have hj : absJob (false, i2) = (false, a.val) := by simp [absJob, absU, hi2v]
      rw [hj] at hrec
      exact hrec
    by_cases ha : a < alloc.vec.Vec.len pend
    · have ha' : a.val < pend.val.length := by scalar_tac
      rw [ite_eq_left ha] at h
      rw [dite_eq_left (by rw [hlp]; exact ha')]
      by_cases hb : b < alloc.vec.Vec.len d
      · have hb' : b.val < d.val.length := by scalar_tac
        rw [ite_eq_left hb] at h
        rw [dite_eq_left (by rw [hlD]; exact hb')]
        obtain ⟨bc, hbc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨pc, hpc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb1, hbc'⟩ := ConRon.Refine2.ExprOps.vecIndexAt hbc
        obtain ⟨hb2, hpc'⟩ := ConRon.Refine2.ExprOps.vecIndexAt hpc
        subst hbc' hpc'
        obtain ⟨tb, htb, htp⟩ := forall₂_get hD b.val hb'
        have hgb : lD[b.val]'(by rw [hlD]; exact hb') = tb := by
          have : lD[b.val]? = some tb := by simpa using htb
          simpa [this] using (Array.getElem?_eq_getElem (by rw [hlD]; exact hb')).symm.trans this
        have hgp : ((absPendingCheckL pend).toArray[a.val]'(by rw [hlp]; exact ha')).pos
            = absU pend.val[a.val].pos := by
          simp [absPendingCheckL, absPendingCheck]
        by_cases hlt : d.val[b.val].pos < pend.val[a.val].pos
        · rw [ite_eq_left hlt] at h
          have hlt' : (lD[b.val]'(by rw [hlD]; exact hb')).pos
              < ((absPendingCheckL pend).toArray[a.val]'(by rw [hlp]; exact ha')).pos := by
            rw [hgb, htp, hgp]
            exact (Std.UScalar.lt_equiv _ _).mp hlt
          rw [ite_eq_left hlt']
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi2v : i2.val = b.val := by
            simp only [lift, Result.ok.injEq] at hi2
            rw [← hi2, usize_cast_u64_val]
          obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi3v : i3.val = b.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
          obtain ⟨he, hbd⟩ := hpush hacc1
          have hrec := ih _ (by omega) a i3 acc1 rfl (hbd (by
            simp only [hi2v]; scalar_tac)) h
          rw [he, hi3v] at hrec
          have hj : absJob (true, i2) = (true, b.val) := by simp [absJob, absU, hi2v]
          rw [hj] at hrec
          exact hrec
        · rw [ite_eq_right hlt] at h
          have hlt' : ¬ (lD[b.val]'(by rw [hlD]; exact hb')).pos
              < ((absPendingCheckL pend).toArray[a.val]'(by rw [hlp]; exact ha')).pos := by
            rw [hgb, htp, hgp]
            exact fun h' => hlt ((Std.UScalar.lt_equiv _ _).mpr h')
          rw [ite_eq_right hlt']
          exact hpa ha' h
      · have hb' : d.val.length ≤ b.val := by scalar_tac
        rw [ite_eq_right hb] at h
        rw [dite_eq_right (by rw [hlD]; omega)]
        exact hpa ha' h
    · have ha' : pend.val.length ≤ a.val := by scalar_tac
      rw [ite_eq_right ha] at h
      rw [dite_eq_right (by rw [hlp]; omega)]
      by_cases hb : b < alloc.vec.Vec.len d
      · have hb' : b.val < d.val.length := by scalar_tac
        rw [ite_eq_left hb] at h
        rw [ite_eq_left (by rw [hlD]; exact hb')]
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = b.val := by
          simp only [lift, Result.ok.injEq] at hi2
          rw [← hi2, usize_cast_u64_val]
        obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi3v : i3.val = b.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi3
        obtain ⟨he, hbd⟩ := hpush hacc1
        have hrec := ih _ (by omega) a i3 acc1 rfl (hbd (by
          simp only [hi2v]; scalar_tac)) h
        rw [he, hi3v] at hrec
        have hj : absJob (true, i2) = (true, b.val) := by simp [absJob, absU, hi2v]
        rw [hj] at hrec
        exact hrec
      · have hb' : d.val.length ≤ b.val := by scalar_tac
        rw [ite_eq_right hb] at h
        rw [ite_eq_right (by rw [hlD]; omega)]
        cases Result.ok_injective h
        exact ⟨by simp, hacc⟩

/-- **What the fold hands the pool, at the frozen tier**: every job related. -/
theorem jobs_rel {ar : arena.store.EStore} {fe layer : arena.env.IFEnv} {lf : IFEnv}
    {pend : alloc.vec.Vec arena.checker.PendingCheck} {d : alloc.vec.Vec arena.checker.BlockCheck}
    {lp : Array PendingCheck} {lD : Array BlockCheck} {order : alloc.vec.Vec (Bool × Std.U64)}
    (hown : IFEnvOwn fe lf) (hinv : IFEnvInv fe) (hok : EnvOK lf)
    (hD : List.Forall₂ (BlockAt lf) d.val lD.toList)
    (hL : arena.checker.check_layer = ok layer)
    (hO : arena.checker.job_order pend d = ok order)
    (hp : lp = (absPendingCheckL pend).toArray) :
    JobsRel (tierWith ar fe) layer pend d lf lp lD ∧
      (jobOrder lp lD).toList = order.val.map absJob ∧
      ∀ j ∈ order.val, j.2.val ≤ Std.Usize.max := by
  have hb : BaseOK (tierWith ar fe) := ⟨hinv, hown.envWF⟩
  have hown' : IFEnvOwn (tierWith ar fe).env lf := hown
  obtain ⟨hl, hli⟩ := check_layer_rel hb hown' hok hL
  have hrc : lf.env.consts.reverse = fe.env.consts.val.map absIConstantInfo := by
    rw [hown.env]; simp [absIEnv]
  have hrt : lf.env.tables.reverse = fe.env.tables.val.map absIProjTable := by
    rw [hown.env]; simp [absIEnv]
  refine ⟨⟨hl, hli, hp, ?_⟩, ?_⟩
  · refine hD.imp fun b tb h => ⟨fun w hw => ?_, h.block, h.nP, h.pos, h.clo, ?_, h.tlo, ?_, ?_, ?_⟩
    · obtain rfl := ifenv_layer_eq hw
      refine ⟨layer_rel hb hown' h.ext h.viewOK h.vis, ?_⟩
      have hnone := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
        (K := arena.handle.NIdx) (V := Std.U64 × Std.U64) (m' := layer00.idx) rfl
      have tnone := ConRon.Refine.HashMap2.new_refines
        (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable)
        (K := arena.handle.NIdx) (V := Std.U64) (m' := layer00.tbls) rfl
      refine ⟨hnone.1, by simp [layer00], fun n p hp => ?_, tnone.1, fun n q hq => ?_⟩
      · rw [show ConRon.Refine.HashMap2.toFun _ n = _ from hnone.2.2 n] at hp; cases hp
      · rw [show ConRon.Refine.HashMap2.toFun _ n = _ from tnone.2.2 n] at hq; cases hq
    · have := h.chi; rw [← List.length_reverse, hrc, List.length_map] at this; exact this
    · have := h.thi; rw [← List.length_reverse, hrt, List.length_map] at this; exact this
    · rw [h.L, hrc, List.map_take, List.map_drop]; rfl
    · rw [h.Q, hrt, List.map_take, List.map_drop]; rfl
  · rw [arena.checker.job_order] at hO
    obtain ⟨i2, -, hO⟩ := ConRon.Refine.bind_eq_ok_iff.mp hO
    have hposD : List.Forall₂ (fun (b : arena.checker.BlockCheck) (tb : BlockCheck) =>
        tb.pos = absU b.pos) d.val lD.toList := hD.imp fun _ _ h => h.pos
    obtain ⟨h1, h2⟩ := job_order_go_abs hposD _ 0#usize 0#usize _ rfl
      (by simp [alloc.vec.Vec.with_capacity]) hO
    rw [hp]
    refine ⟨?_, h2⟩
    rw [h1, jobOrder]
    simp [alloc.vec.Vec.with_capacity]

end ConRon.Refine2
