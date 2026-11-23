/-
# `ConRon.Refine2.Inductives.StreamRecs` — Theorem 2 for `arena::inductives::stored_recs`

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
import ConRon.Arena.Inductives.StreamRecs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] core_walk_fuel_abs Lockstep.core_walk_fuel_val

/-! ## The stored type: `rec_doms_at`, `rec_ty_opened`, `stored_closed`, `rec_ty_check` -/

theorem rec_doms_at_aux {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (sfvs gfvs : alloc.vec.Vec arena.handle.EIdx) (n : Nat) :
    ∀ (j k : Std.U64) st lst, k.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.stream_recs.rec_doms_at pers st mode rf sfvs gfvs j k) lst
        (recDomsAt (ConRon.Refine.absMode mode) lf (absEIdxL sfvs) (absEIdxL gfvs) (absU j) n) := by
  induction n with
  | zero =>
    intro j k st lst hk hrel hinv
    rw [arena.inductives.stream_recs.rec_doms_at.eq_def, ite_eq_left (by scalar_tac), recDomsAt]
    lockstep
  | succ n ih =>
    intro j k st lst hk hrel hinv
    rw [arena.inductives.stream_recs.rec_doms_at.eq_def, ite_eq_right (by scalar_tac), recDomsAt]
    lockstep

@[lockstep] theorem rec_doms_at_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (sfvs gfvs : alloc.vec.Vec arena.handle.EIdx) (j k : Std.U64) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.rec_doms_at pers st mode rf sfvs gfvs j k) lst
      (recDomsAt (ConRon.Refine.absMode mode) lf (absEIdxL sfvs) (absEIdxL gfvs) (absU j)
        (absU k)) :=
  rec_doms_at_aux hfe sfvs gfvs _ j k st lst rfl hrel hinv

/-- The opened telescopes, as `open_pis_at_fvars_ls` abstracts them. -/
def absOpened (o : Option (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    Option (List EIdx × EIdx) :=
  o.map fun p => (absEIdxL p.1, absEIdx p.2)

@[lockstep] theorem rec_ty_opened_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (n : Std.U64)
    (s g : Option (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.rec_ty_opened pers st mode rf n s g) lst
      (recTyOpened (ConRon.Refine.absMode mode) lf (absU n) (absOpened s) (absOpened g)) := by
  rw [arena.inductives.stream_recs.rec_ty_opened.eq_def]
  rcases s with _ | ⟨sfvs, srest⟩ <;> rcases g with _ | ⟨gfvs, grest⟩ <;>
    simp only [absOpened, Option.map, recTyOpened] <;> lockstep

@[lockstep] theorem stored_closed_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (s g : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_closed pers st s g) lst
      (streamClosed (absEIdx s) (absEIdx g)) := by
  rw [arena.inductives.stream_recs.stream_closed, streamClosed]
  lockstep

@[lockstep] theorem rec_ty_check_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (n : Std.U64)
    (s g : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.rec_ty_check pers st mode rf lps n s g) lst
      (recTyCheck (ConRon.Refine.absMode mode) lf (absNIdxL lps) (absU n) (absEIdx s)
        (absEIdx g)) := by
  rw [arena.inductives.stream_recs.rec_ty_check, recTyCheck]
  lockstep

/-! ## One rule: `rule_agree` -/

@[lockstep] theorem rule_agree_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (s g : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.rule_agree pers st mode rf lps s g) lst
      (ruleAgree (ConRon.Refine.absMode mode) lf (absNIdxL lps) (absEIdx s) (absEIdx g)) := by
  rw [arena.inductives.stream_recs.rule_agree, ruleAgree]
  lockstep

/-! ## The major's domain: `stored_nested_pins`, `stored_nested_bvars`, `stored_nested_dom`,
`stored_nested_ok`, `stored_fire_of` -/

/-- `stored_nested_pins` ⊑ the twin's `pins.mapM (liftLooseBVarsFast …)`, from the cursor on. -/
theorem stored_nested_pins_acc {pers} (amount : Std.U64) (pins : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.stream_recs.stream_nested_pins pers st amount pins i out) lst
        (do
          let r ← ((pins.val.drop i.val).map absEIdx).mapM
            (liftLooseBVarsFast coreWalkFuel (absU amount) 0)
          pure (absEIdxL out ++ r)) := by
  refine ls_cursor_acc pins absEIdx
    (fun out l => do
      let r ← l.mapM (liftLooseBVarsFast coreWalkFuel (absU amount) 0)
      pure (absEIdxL out ++ r))
    (fun st i out => arena.inductives.stream_recs.stream_nested_pins pers st amount pins i out)
    ?_ ?_
  · intro st lst i out hn hrel hinv
    rw [arena.inductives.stream_recs.stream_nested_pins.eq_def, ite_eq_left (by scalar_tac),
      List.mapM_nil]
    lockstep
  · intro st lst i out hb hrel hinv ih
    rw [arena.inductives.stream_recs.stream_nested_pins.eq_def, ite_eq_right (by scalar_tac),
      List.mapM_cons]
    lockstep

@[lockstep] theorem stored_nested_pins_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (amount : Std.U64) (pins : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.stream_recs.stream_nested_pins pers st amount pins 0#usize
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
        (arena.inductives.stream_recs.stream_nested_bvars pers st k out) lst
        (bvarsDown n) := by
  induction n with
  | zero =>
    intro k st lst out hk hrel hinv
    rw [arena.inductives.stream_recs.stream_nested_bvars.eq_def, ite_eq_left (by scalar_tac),
      bvarsDown]
    exact LS.pure (by simp) hrel hinv
  | succ n ih =>
    intro k st lst out hk hrel hinv
    rw [arena.inductives.stream_recs.stream_nested_bvars.eq_def, ite_eq_right (by scalar_tac),
      bvarsDown]
    lockstep
    rename_i k1 hk1 b
    exact ls_tail_cons (A := absEIdxL) (ih k1 st1 lst1 a (by scalar_tac) hrel hinv)
      (by simp [absEIdxL, hP])

@[lockstep] theorem stored_nested_bvars_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (out : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => absEIdxL a = absEIdxL out ++ b)
      (arena.inductives.stream_recs.stream_nested_bvars pers st k out) lst
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
      (arena.inductives.stream_recs.stream_nested_dom pers st dom n lvls pins) lst
      (streamNestedDom (absEIdx dom) (absU n) (absLsNodeView lvls) (absEIdxL pins)) := by
  rw [arena.inductives.stream_recs.stream_nested_dom, streamNestedDom]
  lockstep

@[lockstep] theorem stored_nested_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ty : arena.handle.EIdx) (m_i r_p : Std.U64)
    (fire : arena.env.IRecRuleFire) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_nested_ok pers st ty m_i r_p fire) lst
      (streamNestedOk (absEIdx ty) (absU m_i) (absU r_p) (absIRecRuleFire fire)) := by
  rw [arena.inductives.stream_recs.stream_nested_ok.eq_def]
  cases fire <;> simp only [absIRecRuleFire, streamNestedOk] <;> lockstep

@[lockstep] theorem generated_fire_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m : arena.inductives.rec_check.TargetMajor) (r_p : Std.U64) :
    LS pers (fun a b => b = absIRecRuleFire a)
      (arena.inductives.stream_recs.generated_fire pers st m r_p) lst
      (generatedFire (absTargetMajor m) (absU r_p)) := by
  rw [arena.inductives.stream_recs.generated_fire, generatedFire,
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
        (arena.inductives.stream_recs.stream_rules_shape rs cs i) st lst
        (streamRulesShape ((rs.val.drop i.val).map absIRecRule) (absCtorsLFrom cs i)) := by
  induction n with
  | zero =>
    intro i hn
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.stream_rules_shape.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil]
    by_cases hc : i.val < cs.val.length
    · rw [absCtorsLFrom, List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [streamRulesShape]
      lockstep
    · rw [absCtorsLFrom, List.drop_eq_nil_of_le (show cs.val.length ≤ i.val by omega), List.map_nil]
      simp only [streamRulesShape]
      lockstep
  | succ n ih =>
    intro i hn
    have hr : i.val < rs.val.length := by omega
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.stream_rules_shape.eq_def, List.drop_eq_getElem_cons hr,
      List.map_cons]
    by_cases hc : i.val < cs.val.length
    · rw [absCtorsLFrom, List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [streamRulesShape]
      lockstep
    · rw [absCtorsLFrom, List.drop_eq_nil_of_le (show cs.val.length ≤ i.val by omega), List.map_nil]
      simp only [streamRulesShape]
      lockstep

@[lockstep] theorem stored_rules_shape_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rs : alloc.vec.Vec arena.env.IRecRule)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LSR pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_rules_shape rs cs 0#usize) st lst
      (streamRulesShape (rs.val.map absIRecRule) (absCtorsL cs)) := by
  have h := stored_rules_shape_aux rs cs hrel hinv _ 0#usize rfl
  simpa [absCtorsLFrom, absCtorsL] using h

@[lockstep] theorem rule_binds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (r_p : Std.U64) (r : arena.env.IRecRule) :
    LSR pers (fun a b => b = a) (arena.inductives.rec_check.rule_binds pers st r_p r) st lst
      (ruleBinds (absU r_p) (absIRecRule r)) := by
  apply LSR.of_LS
  rw [arena.inductives.rec_check.rule_binds, ruleBinds]
  lockstep

theorem stored_rules_check_aux {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hfe : IFEnvRelI pers rf lf) (lps : alloc.vec.Vec arena.handle.NIdx)
    (r_p : Std.U64) (rs : alloc.vec.Vec arena.env.IRecRule) (gs : alloc.vec.Vec arena.handle.EIdx)
    (n : Nat) :
    ∀ (i : Std.Usize) st lst, rs.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.stream_recs.stream_rules_check pers st mode rf lps r_p rs gs i) lst
        (streamRulesCheck (ConRon.Refine.absMode mode) lf (absNIdxL lps) (absU r_p)
          ((rs.val.drop i.val).map absIRecRule) ((gs.val.drop i.val).map absEIdx)) := by
  induction n with
  | zero =>
    intro i st lst hn hrel hinv
    rw [arena.inductives.stream_recs.stream_rules_check.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [streamRulesCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [streamRulesCheck]
      lockstep
  | succ n ih =>
    intro i st lst hn hrel hinv
    have hr : i.val < rs.val.length := by omega
    rw [arena.inductives.stream_recs.stream_rules_check.eq_def, List.drop_eq_getElem_cons hr,
      List.map_cons]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [streamRulesCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [streamRulesCheck]
      lockstep

@[lockstep] theorem stored_rules_check_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (lps : alloc.vec.Vec arena.handle.NIdx) (r_p : Std.U64)
    (rs : alloc.vec.Vec arena.env.IRecRule) (gs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_rules_check pers st mode rf lps r_p rs gs 0#usize) lst
      (streamRulesCheck (ConRon.Refine.absMode mode) lf (absNIdxL lps) (absU r_p)
        (rs.val.map absIRecRule) (absEIdxL gs)) := by
  have h := stored_rules_check_aux (mode := mode) hfe lps r_p rs gs _ 0#usize st lst rfl hrel hinv
  simpa [absEIdxL] using h

/-! ## One recursor, and the family: `stored_rec_compare`, `stored_rec_check`,
`stored_recs_check`, `stored_out` -/

@[lockstep] theorem stored_rec_compare_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (rc : arena.inductives.block_shape.RecShape)
    (g : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_rec_compare pers st mode rf rc g) lst
      (streamRecCompare (ConRon.Refine.absMode mode) lf (absRecShape rc) (absRecOut g)) := by
  obtain ⟨cv, m, rhss⟩ := g
  rw [arena.inductives.stream_recs.stream_rec_compare, streamRecCompare]
  simp only [absRecOut, absRecShape, absIConstantVal]
  lockstep

@[lockstep] theorem stored_rec_check_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (rc : arena.inductives.block_shape.RecShape)
    (g : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_rec_check pers st mode rf rc g) lst
      (streamRecCheck (ConRon.Refine.absMode mode) lf (absRecShape rc) (absRecOut g)) := by
  obtain ⟨cv, m, rhss⟩ := g
  rw [arena.inductives.stream_recs.stream_rec_check, streamRecCheck]
  simp only [absRecOut, gr_absRecShape_rP, gr_absRecShape_mI, gr_absRecShape_cvR]
  lockstep

theorem stored_recs_check_aux {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hfe : IFEnvRelI pers rf lf)
    (rcs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) (n : Nat) :
    ∀ (i : Std.Usize) st lst, rcs.val.length - i.val = n →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.stream_recs.stream_recs_check pers st mode rf rcs gs i) lst
        (streamRecsCheck (ConRon.Refine.absMode mode) lf
          ((rcs.val.drop i.val).map absRecShape) ((gs.val.drop i.val).map absRecOut)) := by
  induction n with
  | zero =>
    intro i st lst hn hrel hinv
    rw [arena.inductives.stream_recs.stream_recs_check.eq_def,
      List.drop_eq_nil_of_le (by omega), List.map_nil]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [streamRecsCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [streamRecsCheck]
      lockstep
  | succ n ih =>
    intro i st lst hn hrel hinv
    have hr : i.val < rcs.val.length := by omega
    rw [arena.inductives.stream_recs.stream_recs_check.eq_def, List.drop_eq_getElem_cons hr,
      List.map_cons]
    by_cases hc : i.val < gs.val.length
    · rw [List.drop_eq_getElem_cons hc, List.map_cons]
      simp only [streamRecsCheck]
      lockstep
    · rw [List.drop_eq_nil_of_le (show gs.val.length ≤ i.val by omega), List.map_nil]
      simp only [streamRecsCheck]
      lockstep

@[lockstep] theorem stored_recs_check_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) (rcs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.stream_recs_check pers st mode rf rcs gs 0#usize) lst
      (streamRecsCheck (ConRon.Refine.absMode mode) lf (rcs.val.map absRecShape)
        (gs.val.map absRecOut)) := by
  have h := stored_recs_check_aux (mode := mode) hfe rcs gs _ 0#usize st lst rfl hrel hinv
  simpa using h

theorem streamKCheck_nil_left (p : BlockShape) (gs : List (IConstantVal × TargetMajor × List EIdx)) :
    streamKCheck p [] gs = pure () := by
  cases gs <;> rfl

theorem streamKCheck_nil_right (p : BlockShape) (rcs : List RecShape) :
    streamKCheck p rcs [] = pure () := by
  cases rcs <;> rfl

theorem sr_ite_band {α : Type} (a b : Bool) (x y : α) :
    (if (a && b) = true then x else y) = (if a = true then (if b = true then x else y) else y) := by
  cases a <;> cases b <;> rfl

/-- `no_rules` never fails: the twin's `noRules`. -/
theorem no_rules_eq (p : arena.inductives.block_shape.BlockShape) :
    arena.inductives.block_shape.no_rules p = ok (absBlockShape p).noRules := by
  unfold arena.inductives.block_shape.no_rules BlockShape.noRules
  simp only [absBlockShape]
  cases p.flags with
  | none => rfl
  | some fl =>
    simp only [Option.map]
    split <;> simp_all

/-- A record carries rules, as the Rust tests it. -/
theorem sr_rules_nonempty (r : arena.inductives.block_shape.RecShape) :
    (!(absRecShape r).rules.isEmpty) = (r.rules.len != 0#usize) := by
  have e2 : (r.rules.len = 0#usize) ↔ r.rules.val.length = 0 := by
    constructor
    · intro h; have := congrArg (·.val) h; simpa [alloc.vec.Vec.len] using this
    · intro h
      have : r.rules.len.val = 0 := by simp [alloc.vec.Vec.len, h]
      scalar_tac
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, e2]
  simp [absRecShape, List.length_eq_zero_iff]

theorem stream_k_check_aux {pers st} (p : arena.inductives.block_shape.BlockShape)
    (rcs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    ∀ (i : Std.Usize) lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun _ _ => True)
        (arena.inductives.stream_recs.stream_k_check p rcs gs i) st lst
        (streamKCheck (absBlockShape p) ((rcs.val.drop i.val).map absRecShape)
          ((gs.val.drop i.val).map absRecOut)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) rcs.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun _ _ => True)
        (arena.inductives.stream_recs.stream_k_check p rcs gs i) st lst
        (streamKCheck (absBlockShape p) ((rcs.val.drop i.val).map absRecShape)
          ((gs.val.drop i.val).map absRecOut))) ?_ ?_ i ()
  · intro i _ hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.stream_k_check.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len rcs by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, streamKCheck_nil_left]
    lockstep
  · intro i _ hlt ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.stream_k_check.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rcs by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons]
    by_cases hg : i.val < gs.val.length
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len gs by scalar_tac),
        List.drop_eq_getElem_cons hg, List.map_cons, streamKCheck, no_rules_eq, bind_ok]
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          arena.inductives.block_shape.RecShape) rcs i = ok rcs.val[i.val] := by
        rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
        simp [List.getElem?_eq_getElem hlt]
      by_cases hnr : (absBlockShape p).noRules = true
      · rw [ite_eq_left hnr, hidx, bind_ok]
        by_cases hr : (rcs.val[i.val].rules.len != 0#usize) = true
        · rw [ite_eq_left hr, ite_eq_left (by rw [hnr, sr_rules_nonempty, hr]; rfl)]
          lockstep
        · rw [ite_eq_right hr, ite_eq_right (by rw [hnr, sr_rules_nonempty]; simpa using hr)]
          lockstep
          · intro o st' hm
            obtain ⟨o', ho', hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
            cases Result.ok_injective hm
            have hj : a.val = i.val + 1 := by scalar_tac
            have := ih a () hj lst ‹_› ‹_› _ ho'
            rw [hj] at this
            rw [ite_eq_left (by simp_all [absRecShape, absRecOut, TwinEq])]
            exact this
          · rw [ite_eq_right (by simp_all [absRecShape, absRecOut, TwinEq])]
            lockstep
      · rw [ite_eq_right hnr, ite_eq_right (by simp [hnr])]
        lockstep
        · intro o st' hm
          obtain ⟨o', ho', hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
          cases Result.ok_injective hm
          have hj : a.val = i.val + 1 := by scalar_tac
          have := ih a () hj lst ‹_› ‹_› _ ho'
          rw [hj] at this
          rw [ite_eq_left (by simp_all [absRecShape, absRecOut, TwinEq])]
          exact this
        · rw [ite_eq_right (by simp_all [absRecShape, absRecOut, TwinEq])]
          lockstep
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len gs by scalar_tac),
        List.drop_eq_nil_of_le (by omega : gs.val.length ≤ i.val), List.map_nil,
        streamKCheck_nil_right]
      lockstep

/-- `stream_k_check` ⊑ `streamKCheck`: each record's K flag against the block's
(`recKExpected`). -/
@[lockstep] theorem stream_k_check_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (rcs : alloc.vec.Vec arena.inductives.block_shape.RecShape)
    (gs : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
      alloc.vec.Vec arena.handle.EIdx)) :
    LSR pers (fun _ _ => True)
      (arena.inductives.stream_recs.stream_k_check p rcs gs 0#usize) st lst
      (streamKCheck (absBlockShape p) (rcs.val.map absRecShape) (gs.val.map absRecOut)) := by
  have h := stream_k_check_aux (pers := pers) (st := st) p rcs gs 0#usize lst hrel hinv
  simpa using h

/-! ## The declared feature flags -/

/-- The twin's `memberFlagsCheck` with its three conditions inline, the K one
read without a match. -/
theorem memberFlagsCheck_eq (p : BlockShape) (isRec : Bool) (i : Nat) (ms : MemberShape)
    (f : ConLeche.IndFlags) :
    memberFlagsCheck p isRec i ms f = (
  if f.isK && !(if i == 0 && p.k == 1 && p.isProp then
      (ms.ctors.length == 1 && ms.ctors.all (fun c => c.2 == 0)) else false) then
    fail (.invalid "inductive type  is declared with K-like reduction (isK), but it is \
      not a proposition alone in its block with one constructor without fields")
  else if f.hasProjections && !(if ms.ctors.length == 1 && ms.nIdx == 0 then
      (if f.isImpredicative then false else true) else false) then
    fail (.invalid "inductive type  is declared with projections (hasProjections), but it \
      does not have exactly one constructor and no indices, or it is impredicative")
  else if f.hasEta && !(if f.hasProjections then (if isRec then false else true) else false) then
    fail (.invalid "inductive type  is declared with eta (hasEta), but it has no \
      projections or is recursive")
  else pure ()
      : AM Unit) := by
  unfold memberFlagsCheck
  rcases hc : ms.ctors with _ | ⟨c, _ | ⟨c2, rest⟩⟩
  · simp
  · simp only [List.length_singleton, beq_self_eq_true, List.all_cons, List.all_nil,
      Bool.and_true, Bool.true_and]
  · simp

/-- A message constant thrown as an invalid input: an `Invalid` error. -/
theorem sr_invalid_fail {n : Std.Usize} (M : Std.Array Std.U32 n) {r}
    (h : (do
      let s ← lift (Std.Array.to_slice M)
      let v ← kernel.core_types.code_points s
      let ce ← kernel.core_types.invalid v
      arena.monad.fail Unit ce) = ok r) :
    ∃ v, r = .Err (.Invalid v) := by
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [kernel.core_types.invalid, Result.ok.injEq] at hce
  exact ⟨v, by rw [fail_run h, ← hce]⟩

theorem sr_cast_len_eq_one {α : Type} (v : alloc.vec.Vec α) :
    (UScalar.cast .U64 (alloc.vec.Vec.len v) = 1#u64) ↔ v.val.length = 1 := by
  have := lift_cast_u64_of_usize (alloc.vec.Vec.len v) _ rfl
  simp only [alloc.vec.Vec.len] at this
  constructor
  · intro h; rw [h] at this; simp at this; omega
  · intro h; scalar_tac

theorem sr_len_eq_one {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v = 1#usize) ↔ v.val.length = 1 := by
  constructor
  · intro h; have := congrArg (·.val) h; simpa [alloc.vec.Vec.len] using this
  · intro h; have : (alloc.vec.Vec.len v).val = 1 := by simp [alloc.vec.Vec.len, h]
    scalar_tac

theorem sr_u64_eq_zero (x : Std.U64) : (x = 0#u64) ↔ absU x = 0 := by
  constructor
  · intro h; subst h; rfl
  · intro h; simp [absU] at h; scalar_tac

/-- `member_flags_check` ⊑ `memberFlagsCheck`: one member's flags. -/
@[lockstep] theorem member_flags_check_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool)
    (i : Std.U64) (ms : arena.inductives.block_shape.MemberShape) (f : kernel.env.IndFlags) :
    LSR pers (fun _ _ => True)
      (arena.inductives.stream_recs.member_flags_check p is_rec i ms f) st lst
      (memberFlagsCheck (absBlockShape p) is_rec (absU i) (absMemberShape ms)
        (ConRon.Refine.absIndFlags f)) := by
  apply LSR.of_LS
  intro o st' hm
  obtain ⟨r, hr, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  cases Result.ok_injective hm
  rw [arena.inductives.stream_recs.member_flags_check] at hr
  obtain ⟨kk, hkk, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  obtain ⟨⟨f1, pk⟩, hpk, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  obtain ⟨ek, hek, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  -- `IndFlags`' fields: impredicative, K, projections, η, large eliminator
  obtain ⟨b1, b2, b3, b4, b5⟩ := f
  -- the K condition
  have ekk : kk = (if absU i == 0 && (absBlockShape p).k == 1 && (absBlockShape p).isProp then
      ((absMemberShape ms).ctors.length == 1 &&
        (absMemberShape ms).ctors.all (fun c => c.2 == 0)) else false) := by
    have hK : (absBlockShape p).k = p.members.val.length := by
      simp [BlockShape.k, absBlockShape]
    simp only [arena.inductives.block_shape.shape_k, bind_ok] at hkk
    rw [hK]
    by_cases hi : i = 0#u64
    · rw [ite_eq_left hi] at hkk
      have hi' : absU i = 0 := (sr_u64_eq_zero i).mp hi
      by_cases hk : p.members.val.length = 1
      · rw [ite_eq_left ((sr_cast_len_eq_one _).mpr hk)] at hkk
        cases hp : p.is_prop
        · rw [hp] at hkk; simp only [Bool.false_eq_true, ↓reduceIte] at hkk
          cases Result.ok_injective hkk; simp [absBlockShape, hp]
        · rw [hp] at hkk; simp only [↓reduceIte] at hkk
          rcases hc : ms.ctors.val with _ | ⟨⟨cv, nf⟩, _ | ⟨c2, rest⟩⟩
          · rw [ite_eq_right (by rw [sr_len_eq_one, hc]; simp)] at hkk
            cases Result.ok_injective hkk; simp [absMemberShape, absCtorsL, hc]
          · have hidx0 : alloc.vec.Vec.index
                (core.slice.index.SliceIndexUsizeSlice (arena.env.IConstantVal × Std.U64))
                ms.ctors 0#usize = ok (cv, nf) := by
              rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
              simp [hc]
            rw [ite_eq_left (by rw [sr_len_eq_one, hc]; rfl), hidx0, bind_ok] at hkk
            cases Result.ok_injective hkk
            simp only [absMemberShape, absCtorsL, hc, List.map_cons, List.map_nil, hi', hk,
              absBlockShape, hp, List.length_singleton, List.all_cons, List.all_nil]
            simp [u64_eq_zero_decide]
          · rw [ite_eq_right (by rw [sr_len_eq_one, hc]; simp)] at hkk
            cases Result.ok_injective hkk; simp [absMemberShape, absCtorsL, hc]
      · rw [ite_eq_right (mt (sr_cast_len_eq_one _).mp hk)] at hkk
        cases Result.ok_injective hkk; simp [hk]
    · rw [ite_eq_right hi] at hkk
      cases Result.ok_injective hkk
      have hi' : absU i ≠ 0 := fun h => hi ((sr_u64_eq_zero i).mpr h)
      simp [hi']
  -- the projections' condition
  have epk : f1 = ⟨b1, b2, b3, b4, b5⟩ ∧ pk = (if (absMemberShape ms).ctors.length == 1 &&
      (absMemberShape ms).nIdx == 0 then (if b1 then false else true) else false) := by
    have hl : ((absMemberShape ms).ctors.length == 1) =
        decide (alloc.vec.Vec.len ms.ctors = 1#usize) := by
      simp only [absMemberShape, absCtorsL, List.length_map]
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, decide_eq_true_eq, sr_len_eq_one]
    have hn : ((absMemberShape ms).nIdx == 0) = decide (ms.n_idx = 0#u64) := by
      rw [u64_eq_zero_decide]; rfl
    rw [hl, hn]
    by_cases h1 : alloc.vec.Vec.len ms.ctors = 1#usize
    · by_cases h2 : ms.n_idx = 0#u64
      · rw [ite_eq_left h1, ite_eq_left h2] at hpk
        cases b1 <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at hpk <;>
          cases Result.ok_injective hpk <;> simp [h1, h2]
      · rw [ite_eq_left h1, ite_eq_right h2] at hpk
        cases Result.ok_injective hpk
        simp [h1, h2]
    · rw [ite_eq_right h1] at hpk
      cases Result.ok_injective hpk
      simp [h1]
  obtain ⟨rfl, rfl⟩ := epk
  -- the η condition
  have eek : ek = (if b3 then (if is_rec then false else true) else false) := by
    cases b3 <;> cases is_rec <;> simp only [Bool.false_eq_true, ↓reduceIte] at hek ⊢ <;>
      exact (Result.ok_injective hek).symm
  subst ekk eek
  dsimp only at hr
  rw [memberFlagsCheck_eq]
  simp only [ConRon.Refine.absIndFlags]
  generalize (if absU i == 0 && (absBlockShape p).k == 1 && (absBlockShape p).isProp then
      ((absMemberShape ms).ctors.length == 1 &&
        (absMemberShape ms).ctors.all (fun c => c.2 == 0)) else false) = K at hr ⊢
  generalize (if (absMemberShape ms).ctors.length == 1 && (absMemberShape ms).nIdx == 0 then
      (if b1 then false else true) else false) = P at hr ⊢
  cases b2 <;> cases b3 <;> cases b4 <;> cases K <;> cases P <;> cases is_rec <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true,
      Bool.not_false, Bool.and_false, Bool.and_true] at hr ⊢ <;>
    first
    | (cases Result.ok_injective hr; exact ⟨(), lst, rfl, trivial, hrel, hinv⟩)
    | (obtain ⟨v, rfl⟩ := sr_invalid_fail _ hr; exact AErrSim.mk rfl rfl)

theorem membersFlagsCheck_nil_left (p : BlockShape) (isRec : Bool) (i : Nat)
    (fs : List ConLeche.IndFlags) : membersFlagsCheck p isRec i [] fs = pure () := by
  cases fs <;> rfl

theorem membersFlagsCheck_nil_right (p : BlockShape) (isRec : Bool) (i : Nat)
    (ms : List MemberShape) : membersFlagsCheck p isRec i ms [] = pure () := by
  cases ms <;> rfl

/-- `members_flags_check` ⊑ `membersFlagsCheck`, from the cursor on. -/
theorem members_flags_check_aux {pers st} (p : arena.inductives.block_shape.BlockShape)
    (is_rec : Bool) (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape)
    (fl : alloc.vec.Vec kernel.env.IndFlags) :
    ∀ (i : Std.Usize) lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun _ _ => True)
        (arena.inductives.stream_recs.members_flags_check p is_rec i ms fl) st lst
        (membersFlagsCheck (absBlockShape p) is_rec i.val ((ms.val.drop i.val).map absMemberShape)
          ((fl.val.drop i.val).map ConRon.Refine.absIndFlags)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun _ _ => True)
        (arena.inductives.stream_recs.members_flags_check p is_rec i ms fl) st lst
        (membersFlagsCheck (absBlockShape p) is_rec i.val ((ms.val.drop i.val).map absMemberShape)
          ((fl.val.drop i.val).map ConRon.Refine.absIndFlags))) ?_ ?_ i ()
  · intro i _ hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.members_flags_check.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ms by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, membersFlagsCheck_nil_left]
    lockstep
  · intro i _ hlt ih lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.members_flags_check.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons]
    by_cases hg : i.val < fl.val.length
    · rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len fl by scalar_tac),
        List.drop_eq_getElem_cons hg, List.map_cons, membersFlagsCheck]
      lockstep
    · rw [ite_eq_left (show i ≥ alloc.vec.Vec.len fl by scalar_tac),
        List.drop_eq_nil_of_le (by omega : fl.val.length ≤ i.val), List.map_nil,
        membersFlagsCheck_nil_right]
      lockstep

/-- `members_flags_check` from `0` ⊑ `membersFlagsCheck`. -/
@[lockstep] theorem members_flags_check_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool)
    (ms : alloc.vec.Vec arena.inductives.block_shape.MemberShape)
    (fl : alloc.vec.Vec kernel.env.IndFlags) :
    LSR pers (fun _ _ => True)
      (arena.inductives.stream_recs.members_flags_check p is_rec 0#usize ms fl) st lst
      (membersFlagsCheck (absBlockShape p) is_rec 0 (ms.val.map absMemberShape)
        (fl.val.map ConRon.Refine.absIndFlags)) := by
  have h := members_flags_check_aux (pers := pers) (st := st) p is_rec ms fl 0#usize lst hrel hinv
  simpa using h

/-- `flags_uniform` ⊑ the cited `fl.all`. -/
theorem flags_uniform_abs {fl : alloc.vec.Vec kernel.env.IndFlags} {f0 : kernel.env.IndFlags} :
    ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.stream_recs.flags_uniform fl f0 i = ok o →
      o = ((fl.val.drop i.val).map ConRon.Refine.absIndFlags).all (fun f =>
        f.isImpredicative == (ConRon.Refine.absIndFlags f0).isImpredicative &&
        f.hasLargeElim == (ConRon.Refine.absIndFlags f0).hasLargeElim) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) fl.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.stream_recs.flags_uniform fl f0 i = ok o →
      o = ((fl.val.drop i.val).map ConRon.Refine.absIndFlags).all (fun f =>
        f.isImpredicative == (ConRon.Refine.absIndFlags f0).isImpredicative &&
        f.hasLargeElim == (ConRon.Refine.absIndFlags f0).hasLargeElim)) ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.stream_recs.flags_uniform.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len fl by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hn]; rfl
  · intro i _ hi ih o h
    rw [arena.inductives.stream_recs.flags_uniform.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len fl by scalar_tac)] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hxv := vec_index_some hx
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hxv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.all_cons, hxv]
    simp only [ConRon.Refine.absIndFlags]
    by_cases h1 : x.is_impredicative = f0.is_impredicative
    · rw [ite_eq_left h1] at h
      by_cases h2 : x.has_large_elim = f0.has_large_elim
      · rw [ite_eq_left h2] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2' : i2.val = i.val + 1 := absSz_add_one hi2
        rw [ih i2 () hi2' o h, hi2']
        simp [h1, h2, ConRon.Refine.absIndFlags]
      · rw [ite_eq_right h2] at h
        cases Result.ok_injective h
        simp [h1, h2]
    · rw [ite_eq_right h1] at h
      cases Result.ok_injective h
      simp [h1]

/-- `flags_uniform` from `0` ⊑ the cited `fl.all`. -/
@[lockstep] theorem flags_uniform_twin (fl : alloc.vec.Vec kernel.env.IndFlags)
    (f0 : kernel.env.IndFlags) :
    LSP (arena.inductives.stream_recs.flags_uniform fl f0 0#usize)
      (fun o => TwinEq ((fl.val.map ConRon.Refine.absIndFlags).all (fun f =>
        f.isImpredicative == (ConRon.Refine.absIndFlags f0).isImpredicative &&
        f.hasLargeElim == (ConRon.Refine.absIndFlags f0).hasLargeElim)) o) := by
  intro o h
  rw [TwinEq, flags_uniform_abs _ o h]; rfl

/-- `large_elim_flag_ok` ⊑ `largeElimFlagOk`. -/
@[lockstep] theorem large_elim_flag_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_shape.BlockShape)
    (f0 : kernel.env.IndFlags) :
    LS pers (fun a b => b = a)
      (arena.inductives.stream_recs.large_elim_flag_ok pers st p f0) lst
      (largeElimFlagOk (absBlockShape p) (ConRon.Refine.absIndFlags f0)) := by
  rw [arena.inductives.stream_recs.large_elim_flag_ok, largeElimFlagOk]
  lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp only [TwinEq] at *
    simp_all [absU, ConRon.Refine.absIndFlags]

set_option hygiene false in
/-- The outside classes' check past the K shape: the projection table at an
impredicative block, then the rest of the classes (`hrec`). -/
local macro "sr_rest" : tactic => `(tactic| (
  cases hi : f0.is_impredicative <;> simp only [hi, Bool.false_eq_true, ↓reduceIte] at hr ⊢
  · obtain ⟨i2, hi2, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    exact hrec i2 hi2 o hr
  · obtain ⟨ot, hot, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    have hT := ifenv_find_table_abs (IFEnvRelI.coreCtx hfe) hot
    rw [← hT]
    cases ot with
    | none =>
      simp only [Option.map_none] at hr ⊢
      obtain ⟨i2, hi2, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
      exact hrec i2 hi2 o hr
    | some t =>
      simp only [Option.map_some] at hr ⊢
      obtain ⟨v, rfl⟩ := sr_invalid_fail _ hr
      exact AErrSim.mk rfl rfl))

/-- `majors_flags_check` ⊑ `majorsFlagsCheck`, from the cursor on. -/
theorem majors_flags_check_aux {pers st} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI pers rf lf) (p : arena.inductives.block_shape.BlockShape)
    (f0 : kernel.env.IndFlags) (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    ∀ (i : Std.Usize) lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun _ _ => True)
        (arena.inductives.stream_recs.majors_flags_check pers p f0 ms rf i) st lst
        (majorsFlagsCheck (absBlockShape p) (ConRon.Refine.absIndFlags f0) lf
          ((ms.val.drop i.val).map absTargetMajor)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun _ _ => True)
        (arena.inductives.stream_recs.majors_flags_check pers p f0 ms rf i) st lst
        (majorsFlagsCheck (absBlockShape p) (ConRon.Refine.absIndFlags f0) lf
          ((ms.val.drop i.val).map absTargetMajor))) ?_ ?_ i ()
  · intro i _ hn lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.stream_recs.majors_flags_check.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ms by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, majorsFlagsCheck]
    lockstep
  · intro i _ hlt ih lst hrel hinv o hr
    rw [arena.inductives.stream_recs.majors_flags_check.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)] at hr
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, majorsFlagsCheck]
    obtain ⟨tm, htm, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    have htmv := vec_index_some htm
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at htmv
    subst htmv
    have hrec : ∀ (i2 : Std.Usize), (i + 1#usize) = ok i2 → ∀ r,
        arena.inductives.stream_recs.majors_flags_check pers p f0 ms rf i2 = ok r →
        LOut pers (fun _ _ => True) r st
          ((majorsFlagsCheck (absBlockShape p) (ConRon.Refine.absIndFlags f0) lf
            ((ms.val.drop (i.val + 1)).map absTargetMajor)).run lst) := by
      intro i2 hi2 r hr
      have hi2' : i2.val = i.val + 1 := absSz_add_one hi2
      have := ih i2 () hi2' lst hrel hinv r hr
      rw [hi2'] at this
      exact this
    cases hmem : (ms.val[i.val]).member with
    | some t =>
      simp only [hmem] at hr
      simp only [absTargetMajor, hmem, Option.map_some]
      obtain ⟨i2, hi2, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
      exact hrec i2 hi2 o hr
    | none =>
      simp only [hmem] at hr
      simp only [absTargetMajor, hmem, Option.map_none]
      obtain ⟨ks, hks, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
      have hP : (absBlockShape p).isProp = p.is_prop := rfl
      have hI : (ConRon.Refine.absIndFlags f0).isImpredicative = f0.is_impredicative := rfl
      rw [hP, hI]
      rcases hc : (ms.val[i.val]).ctors.val with _ | ⟨⟨cv, nf⟩, _ | ⟨c2, rest⟩⟩
      · simp only [absCtorsL, hc, List.map_nil]
        have hks' : ks = false := by
          cases hp : p.is_prop <;> rw [hp] at hks <;>
            simp only [Bool.false_eq_true, ↓reduceIte] at hks
          · exact (Result.ok_injective hks).symm
          · rw [ite_eq_right (by rw [sr_len_eq_one, hc]; simp)] at hks
            exact (Result.ok_injective hks).symm
        subst hks'
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hr ⊢
        sr_rest
      · simp only [absCtorsL, hc, List.map_cons, List.map_nil]
        cases hp : p.is_prop <;> rw [hp] at hks <;>
          simp only [Bool.false_eq_true, ↓reduceIte] at hks
        · cases Result.ok_injective hks
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr ⊢
          sr_rest
        · have hidx0 : alloc.vec.Vec.index
              (core.slice.index.SliceIndexUsizeSlice (arena.env.IConstantVal × Std.U64))
              (ms.val[i.val]).ctors 0#usize = ok (cv, nf) := by
            rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
            simp [hc]
          rw [ite_eq_left (by rw [sr_len_eq_one, hc]; rfl), hidx0, bind_ok] at hks
          cases Result.ok_injective hks
          rw [← u64_eq_zero_decide]
          by_cases hn : nf = 0#u64
          · simp only [hn, decide_true, Bool.true_and, ↓reduceIte] at hr ⊢
            obtain ⟨v, rfl⟩ := sr_invalid_fail _ hr
            exact AErrSim.mk rfl rfl
          · simp only [hn, decide_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hr ⊢
            sr_rest
      · simp only [absCtorsL, hc, List.map_cons]
        have hks' : ks = false := by
          cases hp : p.is_prop <;> rw [hp] at hks <;>
            simp only [Bool.false_eq_true, ↓reduceIte] at hks
          · exact (Result.ok_injective hks).symm
          · rw [ite_eq_right (by rw [sr_len_eq_one, hc]; simp)] at hks
            exact (Result.ok_injective hks).symm
        subst hks'
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hr ⊢
        sr_rest

/-- `majors_flags_check` from `0` ⊑ `majorsFlagsCheck`. -/
@[lockstep] theorem majors_flags_check_ls {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape) (f0 : kernel.env.IndFlags)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    LSR pers (fun _ _ => True)
      (arena.inductives.stream_recs.majors_flags_check pers p f0 ms rf 0#usize) st lst
      (majorsFlagsCheck (absBlockShape p) (ConRon.Refine.absIndFlags f0) lf
        (ms.val.map absTargetMajor)) := by
  have h := majors_flags_check_aux (st := st) hfe p f0 ms 0#usize lst hrel hinv
  simpa using h

/-- The Rust's `f0`: the first flag record, the default off the list. -/
theorem sr_f0_twin (fl : alloc.vec.Vec kernel.env.IndFlags) :
    LSP (if alloc.vec.Vec.len fl = 0#usize then
        ok (kernel.env.IndFlags.mk false false false false false)
      else do
        let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice kernel.env.IndFlags)
          fl 0#usize
        kernel.env.ind_flags_dup x)
      (fun o => (fl.val.map ConRon.Refine.absIndFlags).headD default = ConRon.Refine.absIndFlags o) := by
  intro o h
  rcases hv : fl.val with _ | ⟨x, xs⟩
  · have h0 : alloc.vec.Vec.len fl = 0#usize := by
      have : (alloc.vec.Vec.len fl).val = 0 := by simp [alloc.vec.Vec.len, hv]
      scalar_tac
    rw [ite_eq_left h0] at h
    cases Result.ok_injective h
    rfl
  · have h0 : ¬ alloc.vec.Vec.len fl = 0#usize := by
      intro h0; have := congrArg (·.val) h0; simp [alloc.vec.Vec.len, hv] at this
    rw [ite_eq_right h0] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [ind_flags_dup_eq] at h
    cases Result.ok_injective h
    have hyv := vec_index_some hy
    rw [Lockstep.usize_zero_val', hv] at hyv
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hyv
    subst hyv
    simp

set_option hygiene false in
/-- `block_flags_check` past the impredicativity test: the eliminator's flag
against the records', the large eliminator's allowance, the members, the
outside classes. -/
local macro "sr_large_rest" : tactic => `(tactic| (
  by_cases hle : (f0.has_large_elim != p.large) = true
  · rw [ite_eq_left hle, ite_eq_left hle]
    lockstep
  · rw [ite_eq_right hle, ite_eq_right hle]
    lockstep))

/-- `block_flags_check` ⊑ `blockFlagsCheck`: the block's declared flags. -/
@[lockstep] theorem block_flags_check_ls {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape) (is_rec : Bool)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    LS pers (fun _ _ => True)
      (arena.inductives.stream_recs.block_flags_check pers st p is_rec ms rf) lst
      (blockFlagsCheck (absBlockShape p) is_rec (absTargetMajorL ms) lf) := by
  rw [arena.inductives.stream_recs.block_flags_check, blockFlagsCheck, absBlockShape_flags]
  cases hf : p.flags with
  | none => exact LS.pure trivial hrel hinv
  | some fl =>
    simp only [Option.map_some]
    refine LS.bind_eq fun f0 hf0 => ?_
    have e := sr_f0_twin fl f0 hf0
    rw [e, absTargetMajorL, sr_ite_band]
    refine LS.bind_eq fun i2 hi2 => LS.bind_eq fun i3 hi3 => ?_
    have hi2' : i2.val = fl.val.length := by
      have := lift_cast_u64_of_usize _ i2 hi2
      simpa [alloc.vec.Vec.len] using this
    have hi3' := shape_k_twin p i3 hi3
    simp only [TwinEq] at hi3'
    have hcnt : (i2 != i3) = ((fl.val.map ConRon.Refine.absIndFlags).length != (absBlockShape p).k) := by
      rw [hi3', List.length_map, ← hi2']
      rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq]
      constructor
      · intro h hv; exact h (by simp [absU] at hv; scalar_tac)
      · intro h hv; exact h (by rw [hv])
    by_cases hc : (i2 != i3) = true
    · have hc' : ((fl.val.map ConRon.Refine.absIndFlags).length != (absBlockShape p).k) = true :=
        hcnt ▸ hc
      rw [ite_eq_left hc, ite_eq_left hc']
      lockstep
    · have hc' : ¬ ((fl.val.map ConRon.Refine.absIndFlags).length != (absBlockShape p).k) = true :=
        hcnt ▸ hc
      rw [ite_eq_right hc, ite_eq_right hc']
      refine LS.bind_eq fun b hb => ?_
      have hb' := flags_uniform_twin fl f0 b hb
      simp only [TwinEq] at hb'
      rw [hb']
      cases b
      · rw [ite_eq_right (show ¬ (false = true) by simp),
          ite_eq_left (show ((!false) = true) from rfl)]
        lockstep
      · rw [ite_eq_left (show true = true from rfl),
          ite_eq_right (show ¬ ((!true) = true) by simp)]
        have hI : (ConRon.Refine.absIndFlags f0).isImpredicative = f0.is_impredicative := rfl
        have hP : (absBlockShape p).isProp = p.is_prop := rfl
        have hL : (ConRon.Refine.absIndFlags f0).hasLargeElim = f0.has_large_elim := rfl
        have hLg : (absBlockShape p).large = p.large := rfl
        rw [hI, hP, hL, hLg]
        cases hi : f0.is_impredicative
        · rw [ite_eq_right (show ¬ (false = true) by simp),
            ite_eq_right (show ¬ (false = true) by simp)]
          sr_large_rest
        · rw [ite_eq_left (show true = true from rfl), ite_eq_left (show true = true from rfl)]
          cases hp : p.is_prop
          · rw [ite_eq_right (show ¬ (false = true) by simp),
              ite_eq_left (show ((!false) = true) from rfl)]
            lockstep
          · rw [ite_eq_left (show true = true from rfl),
              ite_eq_right (show ¬ ((!true) = true) by simp)]
            sr_large_rest

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

end ConRon.Refine2
