/-
# `ConRon.Refine2.Inductives.IotaRead` — Theorem 2 for `arena::inductives::iota_read`

**Task #164** (con-leche #622, DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/iota_read.rs` against
`proof/ConRon/Arena/Inductives/IotaRead.lean`: the ι reading rule, one
`lockstep` zip per function.  The fuel walks (`pi_tele`, `lvl_eq`, `ann_eq`)
are inductions on the fuel, the cursor walks inductions on the remaining
length, as in `Refine2/Checker/Install.lean`.
-/
import ConRon.Refine2.Inductives.BlockTail
import ConRon.Arena.Inductives.IotaRead

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The abstractions -/

/-- `IotaRec` over handles, as the twin's. -/
def absIotaRec (r : arena.inductives.iota_read.IotaRec) : IotaRec :=
  ⟨r.pre.val.map absEIdx, r.minors.val.map absU, absLsIdx r.us, r.params.val.map absEIdx⟩

/-- `IIotaParts` over handles, as the twin's. -/
def absIIotaParts (p : arena.inductives.iota_read.IIotaParts) : IIotaParts :=
  ⟨p.field_doms.val.map absEIdx, p.idx.val.map absEIdx, absLsIdx p.us,
    p.params.val.map absEIdx⟩

attribute [lockstep_simp] absIotaRec absIIotaParts

/-! ## `pi_tele` -/

open Lockstep in
theorem pi_tele_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = (absU a.1, absEIdx a.2))
        (arena.inductives.iota_read.pi_tele pers st fuel h) st lst
        (piTele n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.iota_read.pi_tele, piTele]
    lockstep
  | succ m ih =>
    intro pers st lst fuel h hn hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.iota_read.pi_tele, piTele]
    lockstep

open Lockstep in
@[lockstep] theorem pi_tele_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = (absU a.1, absEIdx a.2))
      (arena.inductives.iota_read.pi_tele pers st fuel h) st lst
      (piTele (absU fuel) (absEIdx h)) :=
  pi_tele_aux _ fuel h rfl hrel hinv

/-! ## The frame -/

open Lockstep in
@[lockstep] theorem motive_level_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pre : alloc.vec.Vec arena.handle.EIdx) (n_idx : Std.U64)
    (body : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absLIdx)
      (arena.inductives.iota_read.motive_level pers st pre n_idx body) lst
      (motiveLevel? (absEIdxL pre) (absU n_idx) (absEIdx body)) := by
  rw [arena.inductives.iota_read.motive_level, motiveLevel?]
  lockstep

/-- The frame's answer over handles. -/
def absFrame (o : Option (alloc.vec.Vec arena.handle.EIdx × alloc.vec.Vec arena.handle.EIdx ×
    arena.handle.EIdx × arena.handle.LIdx)) : Option (List EIdx × List EIdx × EIdx × LIdx) :=
  o.map fun t => (absEIdxL t.1, absEIdxL t.2.1, absEIdx t.2.2.1, absLIdx t.2.2.2)

attribute [lockstep_simp] absFrame

open Lockstep in
@[lockstep] theorem iota_frame_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cv : arena.env.IConstantVal) (m_i r_p : Std.U64) :
    LS pers (fun a b => b = absFrame a)
      (arena.inductives.iota_read.iota_frame pers st cv m_i r_p) lst
      (iotaFrame (absIConstantVal cv) (absU m_i) (absU r_p)) := by
  rw [arena.inductives.iota_read.iota_frame, iotaFrame]
  lockstep

/-! ## The minor premises -/

open Lockstep in
@[lockstep] theorem is_minor_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pre : alloc.vec.Vec arena.handle.EIdx) (mot q : Std.U64) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.is_minor_at pers st pre mot q) lst
      (isMinorAt (absEIdxL pre) (absU mot) (absU q)) := by
  rw [arena.inductives.iota_read.is_minor_at, isMinorAt]
  lockstep
  refine LS.pure ?_ ‹_› ‹_›
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor <;> intro h <;> scalar_tac

open Lockstep in
theorem minors_from_aux {pers} (pre : alloc.vec.Vec arena.handle.EIdx) (mot : Std.U64) (N : Nat) :
    ∀ (q : Std.U64) (out : alloc.vec.Vec Std.U64) st lst,
      pre.val.length - q.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absU = out.val.map absU ++ b)
        (arena.inductives.iota_read.minors_from pers st pre mot q out) lst
        (minorsFrom (absEIdxL pre) (absU mot) (absU q)) := by
  induction N with
  | zero =>
    intro q out st lst hN hrel hinv
    rw [arena.inductives.iota_read.minors_from.eq_def, minorsFrom]
    lockstep
  | succ N ih =>
    intro q out st lst hN hrel hinv
    rw [arena.inductives.iota_read.minors_from.eq_def, minorsFrom]
    lockstep
    rename_i out1 hout1
    have h := ih a out1 st1 lst1 (by scalar_tac) hrel hinv
    have ha : absU a = absU q + 1 := by simp only [absU]; scalar_tac
    rw [ha] at h
    refine LS.tail_bind_pure h ?_
    intro r b hb
    rw [hb, hout1]
    simp

open Lockstep in
@[lockstep] theorem minors_from_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pre : alloc.vec.Vec arena.handle.EIdx) (mot : Std.U64) :
    LS pers (fun a b => b = a.val.map absU)
      (arena.inductives.iota_read.minors_from pers st pre mot 0#u64 (alloc.vec.Vec.new _)) lst
      (minorsFrom (absEIdxL pre) (absU mot) 0) := by
  refine LS.tail (minors_from_aux pre mot _ 0#u64 _ st lst rfl hrel hinv) (by simp) ?_
  intro a b h
  simpa [alloc.vec.Vec.new] using h.symm

open Lockstep in
@[lockstep] theorem iota_rec_major_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (pre doms : alloc.vec.Vec arena.handle.EIdx)
    (n_idx r_p k : Std.U64) :
    LS pers (fun a b => b = a.map absIotaRec)
      (arena.inductives.iota_read.iota_rec_major pers st pre doms n_idx r_p k) lst
      (iotaRecMajor (absEIdxL pre) (absEIdxL doms) (absU n_idx) (absU r_p) (absU k)) := by
  rw [arena.inductives.iota_read.iota_rec_major, iotaRecMajor]
  lockstep
  rename_i args len hlen k hk
  have hl := absEIdxL_of_takeEidx hP
  have e2 : List.take ((List.map absEIdx args.val).length - absU n_idx) (List.map absEIdx args.val)
      = a.val.map absEIdx := by
    have hl' : a.val.map absEIdx = (args.val.map absEIdx).take k.val := by
      simpa [absEIdxL] using hl
    have hlenv : len.val = args.val.length := by rw [hlen]; simp [alloc.vec.Vec.len]
    rw [hl', List.length_map]
    congr 1
    simp only [absU]; omega
  rw [e2]
  lockstep

open Lockstep in
@[lockstep] theorem iota_rec_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cv : arena.env.IConstantVal) (m_i r_p : Std.U64) :
    LS pers (fun a b => b = a.map absIotaRec)
      (arena.inductives.iota_read.iota_rec_of pers st cv m_i r_p) lst
      (iotaRecOf (absIConstantVal cv) (absU m_i) (absU r_p)) := by
  rw [arena.inductives.iota_read.iota_rec_of, iotaRecOf]
  lockstep

/-! ## A rule's parts off the recursor's type -/

open Lockstep in
theorem lift_field_doms_aux {pers} (amt : Std.U64) (fd : alloc.vec.Vec arena.handle.EIdx)
    (N : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      fd.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absEIdx = out.val.map absEIdx ++ b)
        (arena.inductives.iota_read.lift_field_doms pers st amt fd i out) lst
        (liftFieldDoms (absU amt) ((fd.val.drop i.val).map absEIdx) i.val) := by
  induction N with
  | zero =>
    intro i out st lst hN hrel hinv
    rw [arena.inductives.iota_read.lift_field_doms.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, liftFieldDoms]
    lockstep
  | succ N ih =>
    intro i out st lst hN hrel hinv
    have hlt : i.val < fd.val.length := by omega
    rw [arena.inductives.iota_read.lift_field_doms.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, liftFieldDoms]
    lockstep
    rename_i x out1 hout1
    have h := ih a out1 st1 lst1 (by scalar_tac) hrel hinv
    rw [hP, show ((1#usize : Std.Usize)).val = 1 from rfl] at h
    refine LS.tail_bind_pure h ?_
    intro r b hb
    rw [hb, hout1]
    simp

open Lockstep in
@[lockstep] theorem lift_field_doms_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (amt : Std.U64) (fd : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a.val.map absEIdx)
      (arena.inductives.iota_read.lift_field_doms pers st amt fd 0#usize (alloc.vec.Vec.new _))
      lst (liftFieldDoms (absU amt) (absEIdxL fd) 0) := by
  refine LS.tail (lift_field_doms_aux amt fd _ 0#usize _ st lst rfl hrel hinv) (by
    simp [absEIdxL]) ?_
  intro a b h
  simpa [alloc.vec.Vec.new] using h.symm

open Lockstep in
theorem lift_idx_args_aux {pers} (amt n_t n_f : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx)
    (N : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      xs.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absEIdx = out.val.map absEIdx ++ b)
        (arena.inductives.iota_read.lift_idx_args pers st amt n_t n_f xs i out) lst
        (liftIdxArgs (absU amt) (absU n_t) (absU n_f) ((xs.val.drop i.val).map absEIdx)) := by
  induction N with
  | zero =>
    intro i out st lst hN hrel hinv
    rw [arena.inductives.iota_read.lift_idx_args.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, liftIdxArgs]
    lockstep
  | succ N ih =>
    intro i out st lst hN hrel hinv
    have hlt : i.val < xs.val.length := by omega
    rw [arena.inductives.iota_read.lift_idx_args.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, liftIdxArgs]
    lockstep
    rename_i x out1 hout1
    have h := ih a out1 st1 lst1 (by scalar_tac) hrel hinv
    rw [hP, show ((1#usize : Std.Usize)).val = 1 from rfl] at h
    refine LS.tail_bind_pure h ?_
    intro r b hb
    rw [hb, hout1]
    simp

open Lockstep in
@[lockstep] theorem lift_idx_args_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (amt n_t n_f : Std.U64) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a.val.map absEIdx)
      (arena.inductives.iota_read.lift_idx_args pers st amt n_t n_f xs 0#usize
        (alloc.vec.Vec.new _)) lst
      (liftIdxArgs (absU amt) (absU n_t) (absU n_f) (absEIdxL xs)) := by
  refine LS.tail (lift_idx_args_aux amt n_t n_f xs _ 0#usize _ st lst rfl hrel hinv) (by
    simp [absEIdxL]) ?_
  intro a b h
  simpa [alloc.vec.Vec.new] using h.symm

open Lockstep in
@[lockstep] theorem iota_parts_of_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rr : arena.inductives.iota_read.IotaRec) (r_p n_idx : Std.U64)
    (i : Std.Usize) (rl : arena.env.IRecRule) :
    LS pers (fun a b => b = a.map absIIotaParts)
      (arena.inductives.iota_read.iota_parts_of_at pers st rr r_p n_idx i rl) lst
      (iotaPartsOfAt (absIotaRec rr) (absU r_p) (absU n_idx) i.val (absIRecRule rl)) := by
  rw [arena.inductives.iota_read.iota_parts_of_at, iotaPartsOfAt]
  lockstep
  have hl := absEIdxL_of_takeEidx hP
  simp only [absEIdxL] at hl
  rw [← hl]
  lockstep

/-! ## A rule's parts through the constructor -/

open Lockstep in
@[lockstep] theorem ctor_levels_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rl : arena.env.IRecRule) (lps : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = absLsIdx a)
      (arena.inductives.iota_read.ctor_levels_at pers st rl lps) lst
      (ctorLevelsAt (absIRecRule rl) (absNIdxL lps)) := by
  obtain ⟨c, nf, fire, rhs⟩ := rl
  rw [arena.inductives.iota_read.ctor_levels_at, ctorLevelsAt]
  cases fire <;> simp only [absIRecRule, absIRecRuleFire] <;> lockstep

open Lockstep in
theorem iota_bvars_aux {pers} (r_p n : Std.U64) (N : Nat) :
    ∀ (i : Std.U64) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      n.val - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absEIdx = out.val.map absEIdx ++ b)
        (arena.inductives.iota_read.iota_bvars pers st r_p n i out) lst
        (iotaBVars (absU r_p) (absU n) (absU i)) := by
  induction N with
  | zero =>
    intro i out st lst hN hrel hinv
    rw [arena.inductives.iota_read.iota_bvars.eq_def, iotaBVars]
    lockstep
  | succ N ih =>
    intro i out st lst hN hrel hinv
    rw [arena.inductives.iota_read.iota_bvars.eq_def, iotaBVars]
    lockstep
    rename_i x out1 hout1
    have h := ih a out1 st1 lst1 (by scalar_tac) hrel hinv
    have ha : absU a = absU i + 1 := by simp only [absU]; scalar_tac
    rw [ha] at h
    refine LS.tail_bind_pure h ?_
    intro r b hb
    rw [hb, hout1]
    simp

open Lockstep in
@[lockstep] theorem iota_bvars_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (r_p n : Std.U64) :
    LS pers (fun a b => b = a.val.map absEIdx)
      (arena.inductives.iota_read.iota_bvars pers st r_p n 0#u64 (alloc.vec.Vec.new _)) lst
      (iotaBVars (absU r_p) (absU n) 0) := by
  refine LS.tail (iota_bvars_aux r_p n _ 0#u64 _ st lst rfl hrel hinv) (by simp) ?_
  intro a b h
  simpa [alloc.vec.Vec.new] using h.symm

open Lockstep in
@[lockstep] theorem iota_params_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rl : arena.env.IRecRule) (r_p cn_p : Std.U64) :
    LS pers (fun a b => b = a.val.map absEIdx)
      (arena.inductives.iota_read.iota_params_at pers st rl r_p cn_p) lst
      (iotaParamsAt (absIRecRule rl) (absU r_p) (absU cn_p)) := by
  obtain ⟨c, nf, fire, rhs⟩ := rl
  rw [arena.inductives.iota_read.iota_params_at, iotaParamsAt]
  cases fire <;> simp only [absIRecRule, absIRecRuleFire] <;> lockstep
  all_goals (rw [Nat.min_eq_right (by scalar_tac)]; lockstep)

/-- `iota_parts_at`'s answer over handles. -/
def absPartsAt (o : Option (arena.inductives.iota_read.IIotaParts ×
    alloc.vec.Vec arena.handle.EIdx)) : Option (IIotaParts × List EIdx) :=
  o.map fun t => (absIIotaParts t.1, absEIdxL t.2)

attribute [lockstep_simp] absPartsAt

open Lockstep in
@[lockstep] theorem iota_parts_at_body_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cn_p m_i r_p : Std.U64) (rl : arena.env.IRecRule)
    (lvls : arena.handle.LsIdx) (params pd : alloc.vec.Vec arena.handle.EIdx)
    (ctor_body : arena.handle.EIdx) :
    LS pers (fun a b => b = absPartsAt a)
      (arena.inductives.iota_read.iota_parts_at_body pers st cn_p m_i r_p rl lvls params pd
        ctor_body) lst
      (iotaPartsAtBody (absU cn_p) (absU m_i) (absU r_p) (absIRecRule rl) (absLsIdx lvls)
        (absEIdxL params) (absEIdxL pd) (absEIdx ctor_body)) := by
  rw [arena.inductives.iota_read.iota_parts_at_body, iotaPartsAtBody]
  lockstep
  all_goals
    obtain hd := ‹absEIdxList _ = List.drop _ _›
    simp only [absEIdxList] at hd
    rw [← hd]
    lockstep

open Lockstep in
@[lockstep] theorem iota_parts_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (cvj : arena.env.IConstantVal) (cn_p m_i r_p : Std.U64)
    (rl : arena.env.IRecRule) :
    LS pers (fun a b => b = absPartsAt a)
      (arena.inductives.iota_read.iota_parts_at pers st cvj cn_p m_i r_p rl) lst
      (iotaPartsAt (absIConstantVal cvj) (absU cn_p) (absU m_i) (absU r_p) (absIRecRule rl)) := by
  rw [arena.inductives.iota_read.iota_parts_at, iotaPartsAt]
  lockstep

/-! ## Equal up to levels -/

open Lockstep in
theorem lvl_eq_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (a b : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (arena.inductives.iota_read.lvl_eq pers st fuel a b) lst
        (lvlEq n (absEIdx a) (absEIdx b)) := by
  induction n with
  | zero =>
    intro pers st lst fuel a b hn hrel hinv
    rw [arena.inductives.iota_read.lvl_eq, lvlEq]
    lockstep
  | succ m ih =>
    intro pers st lst fuel a b hn hrel hinv
    rw [arena.inductives.iota_read.lvl_eq, lvlEq]
    lockstep

open Lockstep in
@[lockstep] theorem lvl_eq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (a b : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (arena.inductives.iota_read.lvl_eq pers st fuel a b) lst
      (lvlEq (absU fuel) (absEIdx a) (absEIdx b)) :=
  lvl_eq_aux _ fuel a b rfl hrel hinv

/-! ## The annotations -/

open Lockstep in
@[lockstep] theorem top_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (x : alloc.vec.Vec Std.U32) (hx : ConRon.Refine.StrWF x) :
    LS pers (fun a b => b = absNIdx a)
      (arena.inductives.iota_read.top_name pers st x) lst
      (topName (ConRon.Refine.absString x)) := by
  rw [arena.inductives.iota_read.top_name, topName]
  lockstep

open Lockstep in
@[lockstep] theorem ann_witness_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (d : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.ann_witness pers st fe d) lst
      (annWitness lfe (absEIdx d)) := by
  rw [arena.inductives.iota_read.ann_witness, annWitness]
  lockstep
  refine LS.pure ?_ ‹_› ‹_›
  simp only [List.length_map]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor <;> intro h <;> scalar_tac

open Lockstep in
@[lockstep] theorem ann_ident_body_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (p p2 : arena.handle.NIdx) (arity : Std.U64) (b : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.ann_ident_body pers st fe p p2 arity b) lst
      (annIdentBody lfe (absNIdx p) (absNIdx p2) (absU arity) (absEIdx b)) := by
  rw [arena.inductives.iota_read.ann_ident_body, annIdentBody]
  lockstep

open Lockstep in
@[lockstep] theorem ann_ident_val_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (lps : alloc.vec.Vec arena.handle.NIdx) (arity : Std.U64) (v : arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.ann_ident_val pers st fe lps arity v) lst
      (annIdentVal lfe (absNIdxL lps) (absU arity) (absEIdx v)) := by
  rw [arena.inductives.iota_read.ann_ident_val, annIdentVal]
  lockstep
  rw [show (List.map absNIdx lps.val).getD 0 default = absNIdx lps.val[0] by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simpa using ‹_ < _›)]
    rfl]
  lockstep

open Lockstep in
@[lockstep] theorem ann_ident_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (n : arena.handle.NIdx) (arity : Std.U64) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.ann_ident pers st fe n arity) lst
      (annIdent lfe (absNIdx n) (absU arity)) := by
  rw [arena.inductives.iota_read.ann_ident, annIdent]
  lockstep

open Lockstep in
theorem ann_eq_aux {fe : arena.env.IFEnv} {lfe : IFEnv} (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (fuel : Std.U64) (a b : arena.handle.EIdx),
      CoreCtx pers fe lfe →
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a) (arena.inductives.iota_read.ann_eq pers st fe fuel a b) lst
        (annEq lfe n (absEIdx a) (absEIdx b)) := by
  induction n with
  | zero =>
    intro pers st lst fuel a b hctx hn hrel hinv
    rw [arena.inductives.iota_read.ann_eq, annEq]
    lockstep
  | succ m ih =>
    intro pers st lst fuel a b hctx hn hrel hinv
    rw [arena.inductives.iota_read.ann_eq, annEq]
    lockstep

open Lockstep in
@[lockstep] theorem ann_eq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (fuel : Std.U64) (a b : arena.handle.EIdx) :
    LS pers (fun a b => b = a) (arena.inductives.iota_read.ann_eq pers st fe fuel a b) lst
      (annEq lfe (absU fuel) (absEIdx a) (absEIdx b)) :=
  ann_eq_aux _ fuel a b hctx rfl hrel hinv

open Lockstep in
theorem list_lvl_eq_aux {pers} (xs ys : alloc.vec.Vec arena.handle.EIdx) (N : Nat) :
    ∀ (i : Std.Usize) st lst,
      xs.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.iota_read.list_lvl_eq pers st xs ys i) lst
        (listLvlEq ((xs.val.drop i.val).map absEIdx) ((ys.val.drop i.val).map absEIdx)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i st lst hN hrel hinv
    rw [arena.inductives.iota_read.list_lvl_eq.eq_def]
    by_cases ha : i.val < xs.val.length <;> by_cases hb : i.val < ys.val.length
    · rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]
      simp only [List.map_cons, listLvlEq]
      lockstep
    · rw [List.drop_eq_getElem_cons ha, List.drop_eq_nil_of_le (Nat.le_of_not_lt hb)]
      simp only [List.map_cons, List.map_nil, listLvlEq]
      lockstep
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt ha), List.drop_eq_getElem_cons hb]
      simp only [List.map_cons, List.map_nil, listLvlEq]
      lockstep
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt ha), List.drop_eq_nil_of_le (Nat.le_of_not_lt hb)]
      simp only [List.map_nil, listLvlEq]
      lockstep

open Lockstep in
@[lockstep] theorem list_lvl_eq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.list_lvl_eq pers st xs ys 0#usize) lst
      (listLvlEq (absEIdxL xs) (absEIdxL ys)) := by
  simpa [absEIdxL] using list_lvl_eq_aux xs ys _ 0#usize st lst rfl hrel hinv

open Lockstep in
theorem list_ann_eq_aux {pers} {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (xs ys : alloc.vec.Vec arena.handle.EIdx) (N : Nat) :
    ∀ (i : Std.Usize) st lst,
      xs.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.iota_read.list_ann_eq pers st fe xs ys i) lst
        (listAnnEq lfe ((xs.val.drop i.val).map absEIdx) ((ys.val.drop i.val).map absEIdx)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i st lst hN hrel hinv
    rw [arena.inductives.iota_read.list_ann_eq.eq_def]
    by_cases ha : i.val < xs.val.length <;> by_cases hb : i.val < ys.val.length
    · rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]
      simp only [List.map_cons, listAnnEq]
      lockstep
    · rw [List.drop_eq_getElem_cons ha, List.drop_eq_nil_of_le (Nat.le_of_not_lt hb)]
      simp only [List.map_cons, List.map_nil, listAnnEq]
      lockstep
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt ha), List.drop_eq_getElem_cons hb]
      simp only [List.map_cons, List.map_nil, listAnnEq]
      lockstep
    · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt ha), List.drop_eq_nil_of_le (Nat.le_of_not_lt hb)]
      simp only [List.map_nil, listAnnEq]
      lockstep

open Lockstep in
@[lockstep] theorem list_ann_eq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.list_ann_eq pers st fe xs ys 0#usize) lst
      (listAnnEq lfe (absEIdxL xs) (absEIdxL ys)) := by
  simpa [absEIdxL] using list_ann_eq_aux hctx xs ys _ 0#usize st lst rfl hrel hinv

open Lockstep in
@[lockstep] theorem params_ann_eq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cn_p : Std.U64) (cv : arena.env.IConstantVal) (pd : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.params_ann_eq pers st fe cn_p cv pd) lst
      (paramsAnnEq lfe (absU cn_p) (absIConstantVal cv) (absEIdxL pd)) := by
  rw [arena.inductives.iota_read.params_ann_eq, paramsAnnEq]
  lockstep

open Lockstep in
@[lockstep] theorem iota_parts_rel_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cn_p : Std.U64) (cv : arena.env.IConstantVal) (rl : arena.env.IRecRule)
    (p2 p : arena.inductives.iota_read.IIotaParts) (pd : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.iota_parts_rel pers st fe cn_p cv rl p2 p pd) lst
      (iotaPartsRel lfe (absU cn_p) (absIConstantVal cv) (absIRecRule rl) (absIIotaParts p2)
        (absIIotaParts p) (absEIdxL pd)) := by
  obtain ⟨c, nf, fire, rhs⟩ := rl
  rw [arena.inductives.iota_read.iota_parts_rel, iotaPartsRel]
  cases fire <;> simp only [absIRecRule, absIRecRuleFire] <;> lockstep

/-! ## The rules, the recursors, the block -/

attribute [local lockstep_simp] Lockstep.absIRecRule_ctor

open Lockstep in
@[lockstep] theorem rule_reads_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cv : arena.env.IConstantVal) (rr : Option arena.inductives.iota_read.IotaRec)
    (m_i r_p : Std.U64) (i : Std.Usize) (rl : arena.env.IRecRule) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.rule_reads pers st fe cv rr m_i r_p i rl) lst
      (ruleReads lfe (absIConstantVal cv) (rr.map absIotaRec) (absU m_i) (absU r_p) i.val
        (absIRecRule rl)) := by
  cases rr <;> rw [arena.inductives.iota_read.rule_reads] <;> unfold ruleReads <;>
    simp only [Option.map_none, Option.map_some] <;> lockstep

open Lockstep in
theorem rules_read_aux {pers} {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cv : arena.env.IConstantVal) (rr : Option arena.inductives.iota_read.IotaRec)
    (m_i r_p : Std.U64) (rules : alloc.vec.Vec arena.env.IRecRule) (N : Nat) :
    ∀ (i : Std.Usize) st lst,
      rules.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.iota_read.rules_read pers st fe cv rr m_i r_p rules i) lst
        (rulesRead lfe (absIConstantVal cv) (rr.map absIotaRec) (absU m_i) (absU r_p)
          ((rules.val.drop i.val).map absIRecRule) i.val) := by
  induction N with
  | zero =>
    intro i st lst hN hrel hinv
    rw [arena.inductives.iota_read.rules_read.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, rulesRead]
    lockstep
  | succ N ih =>
    intro i st lst hN hrel hinv
    have hlt : i.val < rules.val.length := by omega
    rw [arena.inductives.iota_read.rules_read.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, rulesRead]
    lockstep

open Lockstep in
@[lockstep] theorem rules_read_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cv : arena.env.IConstantVal) (rr : Option arena.inductives.iota_read.IotaRec)
    (m_i r_p : Std.U64) (rules : alloc.vec.Vec arena.env.IRecRule) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.rules_read pers st fe cv rr m_i r_p rules 0#usize) lst
      (rulesRead lfe (absIConstantVal cv) (rr.map absIotaRec) (absU m_i) (absU r_p)
        (rules.val.map absIRecRule) 0) := by
  simpa using rules_read_aux hctx cv rr m_i r_p rules _ 0#usize st lst rfl hrel hinv

open Lockstep in
@[lockstep] theorem rec_reads_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (ci : arena.env.IConstantInfo) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.rec_reads pers st fe ci) lst
      (recReads lfe (absIConstantInfo ci)) := by
  cases ci <;> rw [arena.inductives.iota_read.rec_reads] <;>
    simp only [absIConstantInfo, recReads] <;> lockstep

open Lockstep in
theorem recs_read_aux {pers} {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cs : alloc.vec.Vec arena.env.IConstantInfo) (N : Nat) :
    ∀ (i : Std.Usize) st lst,
      cs.val.length - i.val = N → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.iota_read.recs_read pers st fe cs i) lst
        (recsRead lfe ((cs.val.drop i.val).map absIConstantInfo)) := by
  induction N with
  | zero =>
    intro i st lst hN hrel hinv
    rw [arena.inductives.iota_read.recs_read.eq_def, ite_eq_left (by scalar_tac),
      List.drop_eq_nil_of_le (by scalar_tac), List.map_nil, recsRead]
    lockstep
  | succ N ih =>
    intro i st lst hN hrel hinv
    have hlt : i.val < cs.val.length := by omega
    rw [arena.inductives.iota_read.recs_read.eq_def, ite_eq_right (by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, recsRead]
    lockstep

open Lockstep in
@[lockstep] theorem recs_read_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {fe : arena.env.IFEnv} {lfe : IFEnv} (hctx : CoreCtx pers fe lfe)
    (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => b = a)
      (arena.inductives.iota_read.recs_read pers st fe cs 0#usize) lst
      (recsRead lfe (cs.val.map absIConstantInfo)) := by
  simpa using recs_read_aux hctx cs _ 0#usize st lst rfl hrel hinv

attribute [local lockstep high] bt_block_recs_ls0

open Lockstep in
/-- `block_reads_at` ⊑ `blockReadsAt`: the verdict, and the index with the
pushes undone. -/
@[lockstep] theorem block_reads_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI pers rf lf)
    (p : arena.inductives.block_shape.BlockShape) :
    LS pers (fun a b => b.1 = a.1 ∧ IFEnvRelI pers a.2 b.2)
      (arena.inductives.iota_read.block_reads_at pers st rf p) lst
      (blockReadsAt lf (absBlockShape p)) := by
  rw [arena.inductives.iota_read.block_reads_at, blockReadsAt, absBlockShape_recs]
  lockstep
  obtain ⟨hR, hpop⟩ := ‹IFEnvRelI _ _ _ ∧ ∀ _ _, _›
  have hctx := hR.coreCtx
  lockstep
  have hpe := ‹arena.inductives.gen_rec.class_fe_r_pop _ _ _ = ok _›
  have hfe3 := hpop _ _ (by simp [alloc.vec.Vec.len]) hpe
  have hfe4 := ifenv_set_flags_refines hfe3 hfe.rel ‹arena.env.ifenv_set_flags _ _ _ = ok _›
  lockstep

end ConRon.Refine2
