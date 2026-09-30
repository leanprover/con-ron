/-
# `ConRon.Refine2.Inductives.GenRecCheck` — Theorem 2 for `gen_rec`'s stage

**Task #105** (DESIGN.md §8.2, Theorem 2).  The second half of
`crates/con-ron-core/src/arena/inductives/gen_rec.rs` against
`proof/ConRon/Arena/Inductives/GenRec.lean`: the classes read and checked
(`check_block_classes`), per class and constructor the datum and node
agreement (`class_ctor_of`), the generated types and rules checked and
installed, and `gen_rec_check`.  The generator is `GenRec.lean`.

## Shapes

* A Rust cursor with a pushing accumulator against a twin that conses after
  its recursive call: the statement puts the accumulator in front of the twin's
  answer (`A a = A out ++ b`), and the step's tail is `ls_tail_cons` /
  `lsr_tail_cons`.
* The Rust passes `vis` beside `fe`: the relation is `CoreCtx vis rf lf`, as in
  `RecCheck.lean`.
-/
import ConRon.Refine2.Inductives.GenRec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] pos_core_walk_fuel_abs pos_core_walk_fuel_val
  gr_absIConstantVal_name gr_absIConstantVal_levelParams gr_absIConstantVal_type
attribute [local lockstep] pos_zero_level_ls pos_i_constant_val_dup_spec rc_shape_member_names_twin

/-! ## The cons tails -/

theorem ls_tail_cons {β τ : Type} {A : τ → List β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result τ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM (List β)} {y : β} {out out1 : τ}
    (h : LS pers (fun a b => A a = A out1 ++ b) m lst x) (hout : A out1 = A out ++ [y]) :
    LS pers (fun a b => A a = A out ++ b) m lst (do let r ← x; pure (y :: r)) :=
  LS.twin_map h (fun a b h1 => by rw [h1, hout]; simp)

theorem lsr_tail_cons {β τ : Type} {A : τ → List β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result τ kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM (List β)} {y : β} {out out1 : τ}
    (h : LSR pers (fun a b => A a = A out1 ++ b) m st lst x) (hout : A out1 = A out ++ [y]) :
    LS pers (fun a b => A a = A out ++ b) (m >>= fun o => ok (o, st)) lst
      (do let r ← x; pure (y :: r)) :=
  ls_tail_cons (LSR.tail_ls h rfl (fun _ _ h => h)) hout

/-! ## `nfs_of_ctor`, `minor_hits`, `class_minor_slot` -/

@[lockstep] theorem nfs_of_ctor_twin (es : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (c : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.nfs_of_ctor es c 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((es.val.map absNestCtorNf).filter (·.ctor == absNIdx c))
        (o.val.map absNestCtorNf)) := by
  intro o h
  have := vec_cursor_filterMap es
    (fun e => if (absNestCtorNf e).ctor == absNIdx c then some (absNestCtorNf e) else none)
    (fun v => v.val.map absNestCtorNf)
    (arena.inductives.gen_rec.nfs_of_ctor es c) ?_ ?_ 0#usize _ o h
  · rw [TwinEq, this, filterMap_ite_eq absNestCtorNf (·.ctor == absNIdx c)]
    simp [alloc.vec.Vec.new]
  · intro i out o hn h
    rw [arena.inductives.gen_rec.nfs_of_ctor.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro k x out o hx h
    rw [arena.inductives.gen_rec.nfs_of_ctor.eq_def, if_neg (show ¬ k ≥ alloc.vec.Vec.len es by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := nidx_eq2_abs hb
    cases b
    · rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i2, out, absSz_add_one hi2, ?_, h⟩
      simp [absNestCtorNf, ← hbv]
    · rw [if_pos rfl] at h
      obtain ⟨q1, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i2, out1, absSz_add_one hi2, ?_, h⟩
      rw [nest_ctor_nf_dup_spec _ _ hq1] at hout1
      simp [ConRon.Refine.vec_push_val hout1, absNestCtorNf, ← hbv]

/-- `classMinorSlot`'s hit at slot `s` (its `match`-lambda, named). -/
def grMinorHit (slots : List ClassSlot) (c : Nat) (C : NIdx) (s : Nat) :
    Option (Nat × List (Nat × Nat)) :=
  match slots[s]? with
  | some (.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
  | _ => none

def classMinorSlot' (rd : ClassRead) (c : Nat) (C : NIdx) : AM (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap (grMinorHit rd.slots c C)
  match hits with
  | [h] => pure h
  | _ => fail (.invalid "generated recursor: the recursors' prefix does not have exactly one \
      minor premise for  (official: invalid recursor)")

theorem classMinorSlot_eq : classMinorSlot = classMinorSlot' := by
  funext rd c C
  simp only [classMinorSlot, classMinorSlot']
  congr 2

def absHit (p : Std.U64 × alloc.vec.Vec (Std.U64 × Std.U64)) : Nat × List (Nat × Nat) :=
  (absU p.1, p.2.val.map absNatPair)

theorem minor_hits_abs (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (c : Std.U64) (cn : arena.handle.NIdx) :
    ∀ (s : Std.Usize) out o, arena.inductives.gen_rec.minor_hits slots c cn s out = ok o →
      o.val.map absHit = out.val.map absHit ++
        (List.range' s.val (slots.val.length - s.val)).filterMap
          (grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn)) := by
  intro s
  refine cursor_induction (fun i : Std.Usize => i.val) slots.val.length
    (fun s (_ : Unit) => ∀ out o, arena.inductives.gen_rec.minor_hits slots c cn s out = ok o →
      o.val.map absHit = out.val.map absHit ++
        (List.range' s.val (slots.val.length - s.val)).filterMap
          (grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn))) ?_ ?_ s ()
  · intro s _ hn out o h
    rw [arena.inductives.gen_rec.minor_hits.eq_def,
      if_pos (show s ≥ alloc.vec.Vec.len slots by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [show slots.val.length - s.val = 0 by omega]; simp
  · intro s _ hs ih out o h
    rw [arena.inductives.gen_rec.minor_hits.eq_def,
      if_neg (show ¬ s ≥ alloc.vec.Vec.len slots by scalar_tac)] at h
    rw [show slots.val.length - s.val = (slots.val.length - (s.val + 1)) + 1 by omega,
      List.range'_succ, List.filterMap_cons]
    obtain ⟨cs, hcs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hcs
    cases cs with
    | Motive k =>
      have hg : grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn) s.val = none := by
        simp only [grMinorHit, List.getElem?_map, hx, Option.map_some, absClassSlot]
      rw [hg]
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = s.val + 1 := absSz_add_one hi1
      rw [ih i1 () hi1v out o h, hi1v]
    | Minor c2 n2 ihs =>
      have hg : grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn) s.val =
          if absU c2 == absU c && absNIdx n2 == absNIdx cn then
            some (s.val, ihs.val.map absNatPair) else none := by
        simp only [grMinorHit, List.getElem?_map, hx, Option.map_some, absClassSlot]
      rw [hg]
      dsimp only at h
      by_cases hc : c2 = c
      · rw [if_pos hc] at h
        obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hbv := nidx_eq2_abs hb
        subst hc
        cases b
        · rw [if_neg (by simp)] at h
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi1v : i1.val = s.val + 1 := absSz_add_one hi1
          rw [ih i1 () hi1v out o h, hi1v, ← hbv]
          simp
        · rw [if_pos rfl] at h
          obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi2v : i2.val = s.val + 1 := absSz_add_one hi2
          rw [ih i2 () hi2v out1 o h, hi2v, ← hbv,
            ConRon.Refine.vec_push_val hout1, pairs_dup_spec _ _ hv]
          have hkv : k.val = s.val := by
            simp only [lift, Result.ok.injEq] at hk; subst hk
            exact ConRon.Refine.ExprOps.usize_cast_u64_val s
          simp [absHit, absU, hkv]
      · rw [if_neg hc] at h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = s.val + 1 := absSz_add_one hi1
        rw [ih i1 () hi1v out o h, hi1v]
        have : (absU c2 == absU c) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; exact hc (u64_eq_iff_val.mpr h')
        simp [this]

@[lockstep] theorem minor_hits_twin (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (c : Std.U64) (cn : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.minor_hits slots c cn 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((List.range (slots.val.map absClassSlot).length).filterMap
          (grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn))) (o.val.map absHit)) := by
  intro o h
  rw [TwinEq, minor_hits_abs slots c cn 0#usize _ o h]
  simp [alloc.vec.Vec.new, List.range_eq_range']

theorem gr_absClassRead_slots (r : arena.inductives.class_read.ClassRead) :
    (absClassRead r).slots = r.slots.val.map absClassSlot := rfl
theorem gr_absClassRead_recCls (r : arena.inductives.class_read.ClassRead) :
    (absClassRead r).recCls = r.rec_cls.val.map absU := rfl
attribute [local lockstep_simp] gr_absClassRead_slots gr_absClassRead_recCls

/-- `class_minor_slot` ⊑ `classMinorSlot` (a pure read that may fail). -/
@[lockstep] theorem class_minor_slot_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rd : arena.inductives.class_read.ClassRead) (c : Std.U64)
    (cn : arena.handle.NIdx) :
    LSR pers (fun a b => b = absHit a) (arena.inductives.gen_rec.class_minor_slot rd c cn) st lst
      (classMinorSlot (absClassRead rd) (absU c) (absNIdx cn)) := by
  apply LSR.of_LS
  rw [arena.inductives.gen_rec.class_minor_slot, classMinorSlot_eq, classMinorSlot']
  lockstep
  · rename_i hw hd tl hdisc
    have hlen : a.val.length = 1 := by
      have := congrArg (fun x : Std.Usize => x.val) hc; simpa [alloc.vec.Vec.len] using this
    obtain ⟨h0, ha⟩ := List.length_eq_one_iff.mp hlen
    rw [ha] at hdisc
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hdisc
    obtain ⟨rfl, rfl⟩ := hdisc
    simp only [ha]
    exact LS.pure rfl hrel hinv
  · have hlen : (‹alloc.vec.Vec (Std.U64 × alloc.vec.Vec (Std.U64 × Std.U64))›).val.length ≠ 1 := by
      intro h1; apply hc; scalar_tac
    rcases ha : (‹alloc.vec.Vec (Std.U64 × alloc.vec.Vec (Std.U64 × Std.U64))›).val with
      _ | ⟨h0, _ | ⟨h1, t⟩⟩
    all_goals simp only [ha, List.map_nil, List.map_cons]
    all_goals first | (simp [ha] at hlen; done) | lockstep

/-! ## `class_leaf_at`, `class_nodes_agree`, `class_fields_of` -/

attribute [local lockstep_simp] Option.getD_some Option.getD_none

/-- `class_leaf_at` ⊑ `classLeafAt`. -/
@[lockstep] theorem class_leaf_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (m : arena.inductives.rec_check.TargetMajor)
    (leaf : arena.handle.EIdx) :
    LSR pers (fun a b => b = a) (arena.inductives.gen_rec.class_leaf_at pers st m leaf) st lst
      (classLeafAt (absTargetMajor m) (absEIdx leaf)) := by
  apply LSR.of_LS
  rw [arena.inductives.gen_rec.class_leaf_at, classLeafAt]
  lockstep

/-- `class_nodes_agree` ⊑ `classNodesAgree`, the entries from the cursor on. -/
@[lockstep] theorem class_nodes_agree_ls {pers} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (mc : arena.inductives.rec_check.TargetMajor)
    (tele : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (htele : TeleWF tele)
    (leaf : arena.handle.EIdx) (fvs : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64)
    (es : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    ∀ (j : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.gen_rec.class_nodes_agree pers st mode vis rf p former_tys mc tele leaf
          fvs i es j) lst
        (classNodesAgree (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (absTargetMajor mc) (absBinderL tele) (absEIdx leaf) (absEIdxL fvs) (absU i)
          ((es.val.drop j.val).map absNestCtorNf)) := by
  intro j st lst hrel hinv
  refine ls_cursor es absNestCtorNf
    (fun l => classNodesAgree (ConRon.Refine.absMode mode) lf (absBlockShape p)
      (absEIdxL former_tys) (absTargetMajor mc) (absBinderL tele) (absEIdx leaf) (absEIdxL fvs)
      (absU i) l)
    (fun st j => arena.inductives.gen_rec.class_nodes_agree pers st mode vis rf p former_tys mc
      tele leaf fvs i es j) ?_ ?_ j st lst hrel hinv
  · intro st lst j hn hrel hinv
    rw [arena.inductives.gen_rec.class_nodes_agree.eq_def,
      if_pos (show j ≥ alloc.vec.Vec.len es by scalar_tac), classNodesAgree]
    lockstep
  · intro st lst j hj hrel hinv ih
    rw [arena.inductives.gen_rec.class_nodes_agree.eq_def,
      if_neg (show ¬ j ≥ alloc.vec.Vec.len es by scalar_tac), classNodesAgree]
    lockstep
    all_goals simp [TwinEq, absEIdxL, alloc.vec.Vec.new] at hP

set_option maxHeartbeats 1000000 in
theorem class_fields_of_acc {pers st} (p : arena.inductives.block_parts.BlockShape)
    (ihs : alloc.vec.Vec (Std.U64 × Std.U64)) (fs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.U64) (out : alloc.vec.Vec arena.inductives.gen_rec.ClassField) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => a.val.map absClassField = out.val.map absClassField ++ b)
        (arena.inductives.gen_rec.class_fields_of pers st p ihs i fs out) st lst
        (classFieldsOf (absBlockShape p) (ihs.val.map absNatPair) i.val
          ((fs.val.drop i.val).map absEIdx)) := by
  intro i
  refine cursor_induction (fun i : Std.U64 => i.val) fs.val.length
    (fun i out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => a.val.map absClassField = out.val.map absClassField ++ b)
        (arena.inductives.gen_rec.class_fields_of pers st p ihs i fs out) st lst
        (classFieldsOf (absBlockShape p) (ihs.val.map absNatPair) i.val
          ((fs.val.drop i.val).map absEIdx))) ?_ ?_ i
  · intro i out hn lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classFieldsOf]
    apply LSR.of_LS
    rw [arena.inductives.gen_rec.class_fields_of.eq_def]
    lockstep
  · intro i out hi ih lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, classFieldsOf]
    apply LSR.of_LS
    rw [arena.inductives.gen_rec.class_fields_of.eq_def]
    lockstep
    all_goals
      refine LS.pure ?_ ‹_› ‹_›
      simp_all [absClassField, absBinderL]
    all_goals
      rw [List.getElem?_eq_getElem (show 0 < _ from ‹(0#usize : Std.Usize).val < _›)]
      rfl

/-- `class_fields_of` from field `0` into `Vec::new()` ⊑ `classFieldsOf … 0`. -/
@[lockstep] theorem class_fields_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape)
    (ihs : alloc.vec.Vec (Std.U64 × Std.U64)) (fs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = a.val.map absClassField)
      (arena.inductives.gen_rec.class_fields_of pers st p ihs 0#u64 fs (alloc.vec.Vec.new _)) st lst
      (classFieldsOf (absBlockShape p) (ihs.val.map absNatPair) 0 (absEIdxL fs)) := by
  have h := class_fields_of_acc (pers := pers) (st := st) p ihs fs 0#u64 (alloc.vec.Vec.new _) lst
    hrel hinv
  intro o ho
  have h1 := h o ho
  cases o with
  | Err e => simp only [LOut] at h1 ⊢; simpa [absEIdxL] using h1
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h2, h3⟩ := h1
    refine ⟨b, lst', by simpa [absEIdxL] using hx, ?_, h2, h3⟩
    simpa [alloc.vec.Vec.new] using hR.symm

/-! ## `class_fields_agree` -/

attribute [local lockstep high] rc_strip_pis_wf_ls

/-- The port's in-range kind read `class_field_dup(&ks[i])`, as one value. -/
theorem gr_kind_read_in {γ : Type} (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField)
    (i : Std.U64) (h : i.val < ks.val.length) (M : arena.inductives.gen_rec.ClassField → Result γ) :
    (do
      let cf ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        arena.inductives.gen_rec.ClassField) ks (UScalar.cast .Usize i)
      let cf1 ← arena.inductives.gen_rec.class_field_dup cf
      M cf1) = M ks.val[i.val] := by
  have hc : (UScalar.cast .Usize i).val = i.val :=
    ConRon.Refine.ExprOps.u64_cast_usize_val (by have := ks.property; scalar_tac)
  rw [gr_vec_index_eq (by rw [hc]; exact List.getElem?_eq_getElem h), bind_tc_ok]
  cases hk : ks.val[i.val] <;> simp [arena.inductives.gen_rec.class_field_dup]

theorem class_fields_agree_acc {pers} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor)
    (fvs : alloc.vec.Vec arena.handle.EIdx)
    (es : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField) :
    ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.gen_rec.class_fields_agree pers st mode vis rf p former_tys ms fvs es i ks)
        lst
        (classFieldsAgree (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (ms.val.map absTargetMajor) (absEIdxL fvs) (es.val.map absNestCtorNf) i.val
          ((ks.val.drop i.val).map absClassField)) := by
  intro i
  refine cursor_induction (fun i : Std.U64 => i.val) ks.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.gen_rec.class_fields_agree pers st mode vis rf p former_tys ms fvs es i ks)
        lst
        (classFieldsAgree (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (ms.val.map absTargetMajor) (absEIdxL fvs) (es.val.map absNestCtorNf) i.val
          ((ks.val.drop i.val).map absClassField))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classFieldsAgree,
      arena.inductives.gen_rec.class_fields_agree.eq_def]
    lockstep
  · intro i _ hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons,
      arena.inductives.gen_rec.class_fields_agree.eq_def]
    simp only [lift, bind_tc_ok]
    rw [if_neg (by
      have := ConRon.Refine.ExprOps.usize_cast_u64_val ks.len
      simp only [alloc.vec.Vec.len] at this; scalar_tac)]
    rw [gr_kind_read_in ks i hi]
    cases hk : ks.val[i.val] <;> simp only [absClassField, classFieldsAgree]
    all_goals lockstep

@[lockstep] theorem class_fields_agree_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor)
    (fvs : alloc.vec.Vec arena.handle.EIdx)
    (es : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField) :
    LS pers (fun _ _ => True)
      (arena.inductives.gen_rec.class_fields_agree pers st mode vis rf p former_tys ms fvs es 0#u64
        ks) lst
      (classFieldsAgree (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (ms.val.map absTargetMajor) (absEIdxL fvs) (es.val.map absNestCtorNf) 0
        (ks.val.map absClassField)) := by
  have h := class_fields_agree_acc (pers := pers) (mode := mode) hctx p former_tys ms fvs es ks
    0#u64 st lst hrel hinv
  simpa using h

/-! ## Helpers for Shape/Abs — `block_parts` readers (BlockParts' own lemmas once they land) -/

theorem gr_shape_k_twin (p : arena.inductives.block_parts.BlockShape) :
    LSP (arena.inductives.block_parts.shape_k p)
      (fun k => TwinEq (absBlockShape p).k (absU k)) := by
  intro k h
  rw [arena.inductives.block_parts.shape_k, Result.ok.injEq] at h
  subst h
  simp [TwinEq, absU, BlockShape.k, absBlockShape]

theorem gr_major_idx_at_twin (p : arena.inductives.block_parts.BlockShape) (r : Std.U64) :
    LSP (arena.inductives.block_parts.major_idx_at p r)
      (fun k => TwinEq ((absBlockShape p).majorIdxAt (absU r)) (absU k)) := by
  intro k h
  rw [arena.inductives.block_parts.major_idx_at] at h
  simp only [lift, bind_tc_ok] at h
  rw [TwinEq, BlockShape.majorIdxAt]
  have hl := ConRon.Refine.ExprOps.usize_cast_u64_val p.recs.len
  split at h
  · rename_i hr
    have hc : (UScalar.cast .Usize r).val = r.val :=
      ConRon.Refine.ExprOps.u64_cast_usize_val (by have := p.recs.property; scalar_tac)
    rw [gr_vec_index_eq (by rw [hc]; exact List.getElem?_eq_getElem (by
      simp only [alloc.vec.Vec.len] at hl; scalar_tac)), bind_tc_ok, Result.ok.injEq] at h
    subst h
    simp [absBlockShape, absU, List.getElem?_eq_getElem (show r.val < p.recs.val.length by
      simp only [alloc.vec.Vec.len] at hl; scalar_tac), absRecShape]
  · rw [Result.ok.injEq] at h
    subst h
    rw [List.getElem?_eq_none (by simp [absBlockShape, absU]; simp only [alloc.vec.Vec.len] at hl; scalar_tac)]
    rfl

theorem gr_rule_prefix_at_twin (p : arena.inductives.block_parts.BlockShape) (r : Std.U64) :
    LSP (arena.inductives.block_parts.rule_prefix_at p r)
      (fun k => TwinEq ((absBlockShape p).rulePrefixAt (absU r)) (absU k)) := by
  intro k h
  rw [arena.inductives.block_parts.rule_prefix_at] at h
  simp only [lift, bind_tc_ok] at h
  rw [TwinEq, BlockShape.rulePrefixAt]
  have hl := ConRon.Refine.ExprOps.usize_cast_u64_val p.recs.len
  split at h
  · rename_i hr
    have hc : (UScalar.cast .Usize r).val = r.val :=
      ConRon.Refine.ExprOps.u64_cast_usize_val (by have := p.recs.property; scalar_tac)
    rw [gr_vec_index_eq (by rw [hc]; exact List.getElem?_eq_getElem (by
      simp only [alloc.vec.Vec.len] at hl; scalar_tac)), bind_tc_ok, Result.ok.injEq] at h
    subst h
    simp [absBlockShape, absU, List.getElem?_eq_getElem (show r.val < p.recs.val.length by
      simp only [alloc.vec.Vec.len] at hl; scalar_tac), absRecShape]
  · rw [Result.ok.injEq] at h
    subst h
    rw [List.getElem?_eq_none (by simp [absBlockShape, absU]; simp only [alloc.vec.Vec.len] at hl; scalar_tac)]
    rfl

attribute [local lockstep] gr_shape_k_twin gr_major_idx_at_twin gr_rule_prefix_at_twin
attribute [local lockstep high] rc_ctors_dup_spec

/-! ## `class_ctor_of`, `class_ctors_of`, `classes_ctors` -/

theorem gr_usz0 : ((0#usize : Std.Usize)).val = 0 := rfl

/-- `class_ctor_of` ⊑ `classCtorOf`. -/
@[lockstep] theorem class_ctor_of_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (rd : arena.inductives.class_read.ClassRead)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) (c : Std.U64)
    (c_a : arena.env.IConstantVal × Std.U64) :
    LS pers (fun a b => b = absClassCtor a)
      (arena.inductives.gen_rec.class_ctor_of pers st mode vis rf p former_tys rd ms c c_a) lst
      (classCtorOf (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absClassRead rd) (ms.val.map absTargetMajor) (absU c) (absIConstantVal c_a.1, absU c_a.2)) := by
  rw [arena.inductives.gen_rec.class_ctor_of, classCtorOf]
  lockstep
  all_goals
    rcases hes : (‹alloc.vec.Vec arena.inductives.positivity.NestCtorNf›).val with _ | ⟨e0, tl⟩
    all_goals simp only [hes, List.map_nil, List.map_cons, gr_usz0, List.getElem_cons_zero]
  all_goals first | (exfalso; simp_all [alloc.vec.Vec.len]; done) | lockstep
  all_goals
    have hd := ‹List.map absNestCtorNf _ = _ :: _›
    rw [hes, List.map_cons, List.cons.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp only [absClassCtor, ‹absIConstantVal _ = absIConstantVal _›]
    rfl

def absClassCtorL (v : alloc.vec.Vec arena.inductives.gen_rec.ClassCtor) : List ClassCtor :=
  v.val.map absClassCtor

theorem class_ctors_of_acc {pers} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (rd : arena.inductives.class_read.ClassRead)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) (c : Std.U64)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.inductives.gen_rec.ClassCtor) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absClassCtorL a = absClassCtorL out ++ b)
        (arena.inductives.gen_rec.class_ctors_of pers st mode vis rf p former_tys rd ms c cs i out)
        lst
        (classCtorsOf (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (absClassRead rd) (ms.val.map absTargetMajor) (absU c) (absCtorsLFrom cs i)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absClassCtorL a = absClassCtorL out ++ b)
        (arena.inductives.gen_rec.class_ctors_of pers st mode vis rf p former_tys rd ms c cs i out)
        lst
        (classCtorsOf (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (absClassRead rd) (ms.val.map absTargetMajor) (absU c) (absCtorsLFrom cs i))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [absCtorsLFrom, List.drop_eq_nil_of_le hn, List.map_nil, classCtorsOf,
      arena.inductives.gen_rec.class_ctors_of.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [absCtorsLFrom, List.drop_eq_getElem_cons hi, List.map_cons, classCtorsOf,
      arena.inductives.gen_rec.class_ctors_of.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)]
    lockstep
    rename_i x out1 hout1
    have hjv : a.val = i.val + 1 := by simpa using hP
    have h1 := ih a out1 hjv _ _ ‹_› ‹_›
    simp only [absCtorsLFrom, hjv] at h1
    refine ls_tail_cons h1 ?_
    simp [absClassCtorL, hout1]

@[lockstep] theorem class_ctors_of_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (rd : arena.inductives.class_read.ClassRead)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) (c : Std.U64)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    LS pers (fun a b => b = absClassCtorL a)
      (arena.inductives.gen_rec.class_ctors_of pers st mode vis rf p former_tys rd ms c cs 0#usize
        (alloc.vec.Vec.new _)) lst
      (classCtorsOf (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absClassRead rd) (ms.val.map absTargetMajor) (absU c) (absCtorsL cs)) := by
  have h := class_ctors_of_acc (pers := pers) (mode := mode) hctx p former_tys rd ms c cs 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  rw [absCtorsLFrom_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absClassCtorL, alloc.vec.Vec.new] using h1.symm)

end ConRon.Refine2
