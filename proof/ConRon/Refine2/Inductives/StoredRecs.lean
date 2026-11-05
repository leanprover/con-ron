/-
# `ConRon.Refine2.Inductives.StoredRecs` — Theorem 2 for `arena::inductives::stored_recs`

`crates/con-ron-core/src/arena/inductives/stored_recs.rs` against
`proof/ConRon/Arena/Inductives/StoredRecs.lean`: the stored recursors against the
generated ones, one lockstep theorem per function.

## Shapes

* A Rust cursor against a twin that recurs on two lists: both lists at the cursor
  (`(xs.val.drop i.val).map …`), induction on the remaining length.
* `stored_nested_pins` and `stored_nested_bvars` are the twin's two `mapM`s.  The
  first is a cursor with a pushing accumulator over `pins.mapM`; the second
  counts down, and `bvarsDown` is the twin's `(List.range n).mapM` read as the same
  recursion (`bvarsDown_eq`).
* `stored_out` is pure, the twin's `List.zipWith`.
* The Rust passes `fe.visible_below` beside `fe`: the relation is `IFEnvRelI` with
  `hvis`, as in `GenRecCheck.lean`.
-/
import ConRon.Refine2.Inductives.GenRecCheck
import ConRon.Arena.Inductives.StoredRecs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] core_walk_fuel_abs Lockstep.core_walk_fuel_val

/-! ## The stored type: `rec_doms_at`, `rec_ty_opened`, `stored_closed`, `rec_ty_check` -/

theorem rec_doms_at_aux {E₀ : IEnv} {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers E₀ rf lf) (sfvs gfvs : alloc.vec.Vec arena.handle.EIdx) (n : Nat) :
    ∀ (j k : Std.U64) st lst, k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.stored_recs.rec_doms_at pers st mode rf sfvs gfvs j k) lst
        (recDomsAt (ConRon.Refine.absMode mode) lf (absEIdxL sfvs) (absEIdxL gfvs) (absU j) n) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  induction n with
  | zero =>
    intro j k st lst hk hrel hinv
    rw [arena.inductives.stored_recs.rec_doms_at.eq_def, ite_eq_left (by scalar_tac), recDomsAt]
    lockstep
  | succ n ih =>
    intro j k st lst hk hrel hinv
    rw [arena.inductives.stored_recs.rec_doms_at.eq_def, ite_eq_right (by scalar_tac), recDomsAt]
    lockstep
    rename_i j1 hj1
    refine LS.tail (ih j1 a st1 lst1 (by scalar_tac) hrel hinv) ?_ (fun _ _ h => h)
    rw [show absU j1 = j.val + 1 by simp [absU]; scalar_tac]
    rfl

@[lockstep] theorem rec_doms_at_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (sfvs gfvs : alloc.vec.Vec arena.handle.EIdx) (j k : Std.U64) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.rec_doms_at pers st mode rf sfvs gfvs j k) lst
      (recDomsAt (ConRon.Refine.absMode mode) lf (absEIdxL sfvs) (absEIdxL gfvs) (absU j)
        (absU k)) :=
  rec_doms_at_aux hfe sfvs gfvs _ j k st lst rfl hrel hinv

/-- The opened telescopes, as `open_pis_at_fvars_ls` abstracts them. -/
def absOpened (o : Option (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    Option (List EIdx × EIdx) :=
  o.map fun p => (absEIdxL p.1, absEIdx p.2)

@[lockstep] theorem rec_ty_opened_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (n : Std.U64)
    (s g : Option (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.rec_ty_opened pers st mode rf n s g) lst
      (recTyOpened (ConRon.Refine.absMode mode) lf (absU n) (absOpened s) (absOpened g)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.stored_recs.rec_ty_opened.eq_def]
  rcases s with _ | ⟨sfvs, srest⟩ <;> rcases g with _ | ⟨gfvs, grest⟩ <;>
    simp only [absOpened, Option.map, recTyOpened] <;> lockstep

@[lockstep] theorem stored_closed_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (s g : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_closed pers st s g) lst
      (storedClosed (absEIdx s) (absEIdx g)) := by
  rw [arena.inductives.stored_recs.stored_closed, storedClosed]
  lockstep

@[lockstep] theorem rec_ty_check_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (n : Std.U64)
    (s g : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.rec_ty_check pers st mode rf lps n s g) lst
      (recTyCheck (ConRon.Refine.absMode mode) lf (absNIdxL lps) (absU n) (absEIdx s)
        (absEIdx g)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.stored_recs.rec_ty_check, recTyCheck]
  lockstep

/-! ## One rule: `rule_agree` -/

@[lockstep] theorem rule_agree_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (s g : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.rule_agree pers st mode rf lps s g) lst
      (ruleAgree (ConRon.Refine.absMode mode) lf (absNIdxL lps) (absEIdx s) (absEIdx g)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.stored_recs.rule_agree, ruleAgree]
  lockstep

/-! ## The major's domain: `stored_nested_pins`, `stored_nested_bvars`, `stored_nested_dom`,
`stored_nested_ok`, `stored_fire_of` -/

/-- `stored_nested_pins` ⊑ the twin's `pins.mapM (liftLooseBVarsFast …)`, from the cursor on. -/
theorem stored_nested_pins_acc {pers} (amount : Std.U64) (pins : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.stored_recs.stored_nested_pins pers st amount pins i out) lst
        (do
          let r ← ((pins.val.drop i.val).map absEIdx).mapM
            (liftLooseBVarsFast coreWalkFuel (absU amount) 0)
          pure (absEIdxL out ++ r)) := by
  refine ls_cursor_acc pins absEIdx
    (fun out l => do
      let r ← l.mapM (liftLooseBVarsFast coreWalkFuel (absU amount) 0)
      pure (absEIdxL out ++ r))
    (fun st i out => arena.inductives.stored_recs.stored_nested_pins pers st amount pins i out)
    ?_ ?_
  · intro st lst i out hn hrel hinv
    rw [arena.inductives.stored_recs.stored_nested_pins.eq_def, ite_eq_left (by scalar_tac),
      List.mapM_nil]
    lockstep
  · intro st lst i out hb hrel hinv ih
    rw [arena.inductives.stored_recs.stored_nested_pins.eq_def, ite_eq_right (by scalar_tac),
      List.mapM_cons]
    lockstep

@[lockstep] theorem stored_nested_pins_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (amount : Std.U64) (pins : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.stored_recs.stored_nested_pins pers st amount pins 0#usize
        (alloc.vec.Vec.new _)) lst
      ((absEIdxL pins).mapM (liftLooseBVarsFast coreWalkFuel (absU amount) 0)) := by
  have h := stored_nested_pins_acc amount pins 0#usize st lst (alloc.vec.Vec.new _) hrel hinv
  simpa [absEIdxL, alloc.vec.Vec.new] using h

/-- The index variables `k-1, …, 0`, as the Rust's `stored_nested_bvars` builds them. -/
def bvarsDown : Nat → AM (List EIdx)
  | 0 => pure []
  | k + 1 => do
    let b ← internBVarE k
    let r ← bvarsDown k
    pure (b :: r)

theorem bvarsDown_range' (n : Nat) : ∀ (k s : Nat), s + k = n →
    (List.range' s k).mapM (fun i => internBVarE (n - 1 - i)) = bvarsDown k
  | 0, _, _ => by simp [bvarsDown]
  | k + 1, s, h => by
    rw [List.range'_succ, List.mapM_cons, bvarsDown,
      show n - 1 - s = k by omega, bvarsDown_range' n k (s + 1) (by omega)]

/-- The twin's `(List.range n).mapM` is the Rust's countdown. -/
theorem bvarsDown_eq (n : Nat) :
    (List.range n).mapM (fun i => internBVarE (n - 1 - i)) = bvarsDown n := by
  rw [List.range_eq_range']
  exact bvarsDown_range' n n 0 (by omega)

theorem stored_nested_bvars_aux {pers} (n : Nat) :
    ∀ (k : Std.U64) st lst (out : alloc.vec.Vec arena.handle.EIdx), k.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absEIdxL a = absEIdxL out ++ b)
        (arena.inductives.stored_recs.stored_nested_bvars pers st k out) lst
        (bvarsDown n) := by
  induction n with
  | zero =>
    intro k st lst out hk hrel hinv
    rw [arena.inductives.stored_recs.stored_nested_bvars.eq_def, ite_eq_left (by scalar_tac),
      bvarsDown]
    exact LS.pure (by simp) hrel hinv
  | succ n ih =>
    intro k st lst out hk hrel hinv
    rw [arena.inductives.stored_recs.stored_nested_bvars.eq_def, ite_eq_right (by scalar_tac),
      bvarsDown]
    lockstep
    rename_i k1 hk1 b
    exact ls_tail_cons (A := absEIdxL) (ih k1 st1 lst1 a (by scalar_tac) hrel hinv)
      (by simp [absEIdxL, hP])

@[lockstep] theorem stored_nested_bvars_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (out : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => absEIdxL a = absEIdxL out ++ b)
      (arena.inductives.stored_recs.stored_nested_bvars pers st k out) lst
      ((List.range (absU k)).mapM (fun i => internBVarE (absU k - 1 - i))) := by
  rw [bvarsDown_eq]
  exact stored_nested_bvars_aux _ k st lst out rfl hrel hinv

/-- `arena::canon::lidx_vec_beq` from `0` is `==` on the abstracted lists. -/
@[lockstep] theorem canon_lidx_vec_beq_twin (a b : alloc.vec.Vec arena.handle.LIdx) :
    LSP (arena.canon.lidx_vec_beq a b 0#usize)
      (fun o => o = (absLsNodeView a == absLsNodeView b)) := by
  intro o h
  rw [lidx_vec_beq_refines h]
  have e : ∀ v : alloc.vec.Vec arena.handle.LIdx, absLIdxLFrom v 0#usize = absLsNodeView v := by
    intro v; simp [absLIdxLFrom, absLsNodeView]
  rw [e, e]
  cases h' : decide (absLsNodeView a = absLsNodeView b) <;> simp_all

@[lockstep] theorem stored_nested_dom_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (dom : arena.handle.EIdx) (n : Std.U64)
    (lvls : alloc.vec.Vec arena.handle.LIdx) (pins : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_nested_dom pers st dom n lvls pins) lst
      (storedNestedDom (absEIdx dom) (absU n) (absLsNodeView lvls) (absEIdxL pins)) := by
  rw [arena.inductives.stored_recs.stored_nested_dom, storedNestedDom]
  lockstep

@[lockstep] theorem stored_nested_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (m_i r_p : Std.U64)
    (fire : arena.env.IRecRuleFire) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_nested_ok pers st ty m_i r_p fire) lst
      (storedNestedOk (absEIdx ty) (absU m_i) (absU r_p) (absIRecRuleFire fire)) := by
  rw [arena.inductives.stored_recs.stored_nested_ok.eq_def]
  cases fire <;> simp only [absIRecRuleFire, storedNestedOk] <;> lockstep

@[lockstep] theorem stored_fire_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m : arena.inductives.rec_check.TargetMajor) (r_p : Std.U64) :
    LS pers (fun a b => b = absIRecRuleFire a)
      (arena.inductives.stored_recs.stored_fire_of pers st m r_p) lst
      (storedFireOf (absTargetMajor m) (absU r_p)) := by
  rw [arena.inductives.stored_recs.stored_fire_of, storedFireOf,
    show (absTargetMajor m).member = m.member.map absU from rfl]
  rcases hm : m.member with _ | v
  · exact aux_rule_fire_ls hrel hinv m r_p
  · exact LS.pure rfl hrel hinv

/-! ## The rules: `stored_rules_shape`, `stored_rules_check` -/

theorem stored_rules_shape_aux {pers st lst} (rs : alloc.vec.Vec arena.env.IRecRule)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (n : Nat) :
    ∀ (i : Std.Usize), rs.val.length - i.val = n →
      LSR pers (fun a b => b = a)
        (arena.inductives.stored_recs.stored_rules_shape rs cs i) st lst
        (storedRulesShape ((rs.val.drop i.val).map absIRecRule) (absCtorsLFrom cs i)) := by
  induction n with
  | zero =>
    intro i hn
    apply LSR.of_LS
    rw [arena.inductives.stored_recs.stored_rules_shape.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil]
    by_cases hc : i.val < cs.val.length
    · rw [absCtorsLFrom, List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [storedRulesShape]
      lockstep
    · rw [absCtorsLFrom, List.drop_eq_nil_of_le (show cs.val.length ≤ i.val by omega), List.map_nil]
      simp only [storedRulesShape]
      lockstep
  | succ n ih =>
    intro i hn
    have hr : i.val < rs.val.length := by omega
    apply LSR.of_LS
    rw [arena.inductives.stored_recs.stored_rules_shape.eq_def, List.drop_eq_getElem_cons hr,
      List.map_cons]
    by_cases hc : i.val < cs.val.length
    · rw [absCtorsLFrom, List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [storedRulesShape]
      lockstep
    · rw [absCtorsLFrom, List.drop_eq_nil_of_le (show cs.val.length ≤ i.val by omega), List.map_nil]
      simp only [storedRulesShape]
      lockstep

@[lockstep] theorem stored_rules_shape_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rs : alloc.vec.Vec arena.env.IRecRule)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSR pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_rules_shape rs cs 0#usize) st lst
      (storedRulesShape (rs.val.map absIRecRule) (absCtorsL cs)) := by
  have h := stored_rules_shape_aux rs cs hrel hinv _ 0#usize rfl
  simpa [absCtorsLFrom, absCtorsL] using h

theorem stored_rules_check_aux {E₀ : IEnv} {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hfe : IFEnvRelI pers E₀ rf lf) (lps : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec arena.env.IRecRule) (gs : alloc.vec.Vec arena.handle.EIdx) (n : Nat) :
    ∀ (i : Std.Usize) st lst, rs.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.stored_recs.stored_rules_check pers st mode rf lps rs gs i) lst
        (storedRulesCheck (ConRon.Refine.absMode mode) lf (absNIdxL lps)
          ((rs.val.drop i.val).map absIRecRule) ((gs.val.drop i.val).map absEIdx)) := by
  induction n with
  | zero =>
    intro i st lst hn hrel hinv
    rw [arena.inductives.stored_recs.stored_rules_check.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [storedRulesCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [storedRulesCheck]
      lockstep
  | succ n ih =>
    intro i st lst hn hrel hinv
    have hr : i.val < rs.val.length := by omega
    rw [arena.inductives.stored_recs.stored_rules_check.eq_def, List.drop_eq_getElem_cons hr,
      List.map_cons]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [storedRulesCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [storedRulesCheck]
      lockstep

@[lockstep] theorem stored_rules_check_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (lps : alloc.vec.Vec arena.handle.NIdx)
    (rs : alloc.vec.Vec arena.env.IRecRule) (gs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_rules_check pers st mode rf lps rs gs 0#usize) lst
      (storedRulesCheck (ConRon.Refine.absMode mode) lf (absNIdxL lps)
        (rs.val.map absIRecRule) (absEIdxL gs)) := by
  have h := stored_rules_check_aux (mode := mode) hfe lps rs gs _ 0#usize st lst rfl hrel hinv
  simpa [absEIdxL] using h

/-! ## One recursor, and the family: `stored_rec_compare`, `stored_rec_check`,
`stored_recs_check`, `stored_out` -/

@[lockstep] theorem stored_rec_compare_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (rc : arena.inductives.block_parts.RecShape)
    (g : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_rec_compare pers st mode rf rc g) lst
      (storedRecCompare (ConRon.Refine.absMode mode) lf (absRecShape rc) (absRecOut g)) := by
  obtain ⟨cv, m, rhss⟩ := g
  rw [arena.inductives.stored_recs.stored_rec_compare, storedRecCompare]
  simp only [absRecOut, absRecShape, absIConstantVal]
  lockstep

@[lockstep] theorem stored_rec_check_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (rc : arena.inductives.block_parts.RecShape)
    (g : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_rec_check pers st mode rf rc g) lst
      (storedRecCheck (ConRon.Refine.absMode mode) lf (absRecShape rc) (absRecOut g)) := by
  obtain ⟨cv, m, rhss⟩ := g
  rw [arena.inductives.stored_recs.stored_rec_check, storedRecCheck]
  simp only [absRecOut, gr_absRecShape_rP, gr_absRecShape_mI, gr_absRecShape_cvR]
  lockstep

theorem stored_recs_check_aux {E₀ : IEnv} {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hfe : IFEnvRelI pers E₀ rf lf)
    (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) (n : Nat) :
    ∀ (i : Std.Usize) st lst, rcs.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.stored_recs.stored_recs_check pers st mode rf rcs gs i) lst
        (storedRecsCheck (ConRon.Refine.absMode mode) lf
          ((rcs.val.drop i.val).map absRecShape) ((gs.val.drop i.val).map absRecOut)) := by
  induction n with
  | zero =>
    intro i st lst hn hrel hinv
    rw [arena.inductives.stored_recs.stored_recs_check.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [storedRecsCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [storedRecsCheck]
      lockstep
  | succ n ih =>
    intro i st lst hn hrel hinv
    have hr : i.val < rcs.val.length := by omega
    rw [arena.inductives.stored_recs.stored_recs_check.eq_def, List.drop_eq_getElem_cons hr,
      List.map_cons]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [storedRecsCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [storedRecsCheck]
      lockstep

@[lockstep] theorem stored_recs_check_ls {E₀ : IEnv} {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (fun a b => b = a)
      (arena.inductives.stored_recs.stored_recs_check pers st mode rf rcs gs 0#usize) lst
      (storedRecsCheck (ConRon.Refine.absMode mode) lf (rcs.val.map absRecShape)
        (gs.val.map absRecOut)) := by
  have h := stored_recs_check_aux (mode := mode) hfe rcs gs _ 0#usize st lst rfl hrel hinv
  simpa using h

/-- `stored_out` from the cursor on: the Rust's two-list walk is the twin's `zipWith`. -/
theorem stored_out_abs (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) (n : Nat) :
    ∀ (i : Std.Usize) (acc o : alloc.vec.Vec (arena.env.IConstantVal ×
        arena.inductives.rec_check.TargetMajor × alloc.vec.Vec arena.handle.EIdx)),
      rcs.val.length - i.val = n →
      arena.inductives.stored_recs.stored_out rcs gs i acc = ok o →
      o.val.map absRecOut = acc.val.map absRecOut ++
        storedOut ((rcs.val.drop i.val).map absRecShape) ((gs.val.drop i.val).map absRecOut) := by
  induction n with
  | zero =>
    intro i acc o hn h
    rw [arena.inductives.stored_recs.stored_out.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len rcs by scalar_tac), Result.ok.injEq] at h
    rw [h, List.drop_eq_nil_of_le (by omega : rcs.val.length ≤ i.val)]
    simp [storedOut]
  | succ n ih =>
    intro i acc o hn h
    have hr : i.val < rcs.val.length := by omega
    rw [arena.inductives.stored_recs.stored_out.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rcs by scalar_tac)] at h
    by_cases hg : i.val < gs.val.length
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len gs by scalar_tac)] at h
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨iv, tm, x⟩ := p
      have hpx : gs.val[i.val] = (iv, tm, x) := by
        have h1 := vec_index_some hp; rw [List.getElem?_eq_getElem hg] at h1
        exact Option.some_inj.mp h1
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨rc, hrc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hrcx : rcs.val[i.val] = rc := by
        have h1 := vec_index_some hrc; rw [List.getElem?_eq_getElem hr] at h1
        exact Option.some_inj.mp h1
      obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨tm1, htm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v : i3.val = i.val + 1 := absSz_add_one hi3
      rw [ih i3 acc1 o (by omega) h, ConRon.Refine.vec_push_val hacc1, hi3v,
        List.drop_eq_getElem_cons hr, List.drop_eq_getElem_cons hg, List.map_cons, List.map_cons,
        dupId_nidx _ _ hn1, dupId_eidx _ _ he, target_major_dup_spec _ _ htm1, hpx, hrcx]
      have hv1v := rule_rhss_twin0 rc.rules v1 hv1
      simp only [TwinEq] at hv1v
      simp only [storedOut, List.zipWith_cons_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, absRecOut, absRecShape, absIConstantVal, ← hv1v,
        nidx_vec_dup_val hv]
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len gs by scalar_tac), Result.ok.injEq] at h
      rw [h, List.drop_eq_nil_of_le (by omega : gs.val.length ≤ i.val)]
      simp [storedOut]

@[lockstep] theorem stored_out_twin (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LSP (arena.inductives.stored_recs.stored_out rcs gs 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq (storedOut (rcs.val.map absRecShape) (gs.val.map absRecOut))
        (o.val.map absRecOut)) := by
  intro o h
  rw [TwinEq, stored_out_abs rcs gs _ 0#usize _ o rfl h]
  simp [alloc.vec.Vec.new]

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.rec_doms_at_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rec_doms_at_ls

/-- info: 'ConRon.Refine2.rec_ty_opened_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rec_ty_opened_ls

/-- info: 'ConRon.Refine2.stored_closed_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_closed_ls

/-- info: 'ConRon.Refine2.rec_ty_check_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rec_ty_check_ls

/-- info: 'ConRon.Refine2.rule_agree_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_agree_ls

/-- info: 'ConRon.Refine2.stored_nested_pins_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_nested_pins_ls

/-- info: 'ConRon.Refine2.stored_nested_bvars_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_nested_bvars_ls

/-- info: 'ConRon.Refine2.stored_nested_dom_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_nested_dom_ls

/-- info: 'ConRon.Refine2.stored_nested_ok_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_nested_ok_ls

/-- info: 'ConRon.Refine2.stored_fire_of_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_fire_of_ls

/-- info: 'ConRon.Refine2.stored_rules_shape_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_rules_shape_ls

/-- info: 'ConRon.Refine2.stored_rules_check_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_rules_check_ls

/-- info: 'ConRon.Refine2.stored_rec_compare_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_rec_compare_ls

/-- info: 'ConRon.Refine2.stored_rec_check_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_rec_check_ls

/-- info: 'ConRon.Refine2.stored_recs_check_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_recs_check_ls

/-- info: 'ConRon.Refine2.stored_out_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_out_twin

end ConRon.Refine2
