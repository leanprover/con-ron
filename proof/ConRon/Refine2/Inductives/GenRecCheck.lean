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
import ConRon.Refine2.Inductives.BlockRec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide
open scoped GenRecSide

attribute [local lockstep_simp] pos_core_walk_fuel_abs pos_core_walk_fuel_val
  gr_absIConstantVal_name gr_absIConstantVal_levelParams gr_absIConstantVal_type
attribute [local lockstep] pos_zero_level_ls pos_i_constant_val_dup_spec

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

def absClassCtorLL (v : alloc.vec.Vec (alloc.vec.Vec arena.inductives.gen_rec.ClassCtor)) :
    List (List ClassCtor) :=
  v.val.map absClassCtorL

theorem classes_ctors_acc {pers} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (rd : arena.inductives.class_read.ClassRead)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    ∀ (c : Std.Usize) (out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.gen_rec.ClassCtor)) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absClassCtorLL a = absClassCtorLL out ++ b)
        (arena.inductives.gen_rec.classes_ctors pers st mode vis rf p former_tys rd ms c out) lst
        (classesCtors (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (absClassRead rd) (ms.val.map absTargetMajor) c.val
          ((ms.val.drop c.val).map absTargetMajor)) := by
  intro c
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun c out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absClassCtorLL a = absClassCtorLL out ++ b)
        (arena.inductives.gen_rec.classes_ctors pers st mode vis rf p former_tys rd ms c out) lst
        (classesCtors (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (absClassRead rd) (ms.val.map absTargetMajor) c.val
          ((ms.val.drop c.val).map absTargetMajor))) ?_ ?_ c
  · intro c out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classesCtors,
      arena.inductives.gen_rec.classes_ctors.eq_def,
      if_pos (show c ≥ alloc.vec.Vec.len ms by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro c out hc ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hc, List.map_cons, classesCtors,
      arena.inductives.gen_rec.classes_ctors.eq_def,
      if_neg (show ¬ c ≥ alloc.vec.Vec.len ms by scalar_tac)]
    lockstep
    rename_i xs out1 hout1
    have hjv : a.val = c.val + 1 := by simpa using hP
    have h1 := ih a out1 hjv _ _ ‹_› ‹_›
    simp only [hjv] at h1
    refine ls_tail_cons h1 ?_
    simp [absClassCtorLL, hout1]

@[lockstep] theorem classes_ctors_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (rd : arena.inductives.class_read.ClassRead)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = absClassCtorLL a)
      (arena.inductives.gen_rec.classes_ctors pers st mode vis rf p former_tys rd ms 0#usize
        (alloc.vec.Vec.new _)) lst
      (classesCtors (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (absClassRead rd) (ms.val.map absTargetMajor) 0 (ms.val.map absTargetMajor)) := by
  have h := classes_ctors_acc (pers := pers) (mode := mode) hctx p former_tys rd ms 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absClassCtorLL, alloc.vec.Vec.new] using h1.symm)

/-! ## `class_majors`, `classes_nfs`, `class_former_ty(s)` -/

attribute [local lockstep_inline] arena.inductives.positivity.ind_cv_of

def absTargetMajorL (v : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    List TargetMajor :=
  v.val.map absTargetMajor

theorem class_majors_acc {pers} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape)
    (ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64)))
    (pfvs : alloc.vec.Vec arena.handle.EIdx)
    (keys : alloc.vec.Vec arena.inductives.class_read.ClassKey) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absTargetMajorL a = absTargetMajorL out ++ b)
        (arena.inductives.gen_rec.class_majors pers st mode rf p ctors_as pfvs keys i out) lst
        (classMajors (ConRon.Refine.absMode mode) lf (absBlockShape p) (absCtorsLL ctors_as)
          (absEIdxL pfvs) ((keys.val.drop i.val).map absClassKey)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) keys.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absTargetMajorL a = absTargetMajorL out ++ b)
        (arena.inductives.gen_rec.class_majors pers st mode rf p ctors_as pfvs keys i out) lst
        (classMajors (ConRon.Refine.absMode mode) lf (absBlockShape p) (absCtorsLL ctors_as)
          (absEIdxL pfvs) ((keys.val.drop i.val).map absClassKey))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classMajors,
      arena.inductives.gen_rec.class_majors.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len keys by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, classMajors,
      arena.inductives.gen_rec.class_majors.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len keys by scalar_tac)]
    lockstep
    rename_i x out1 hout1
    have hjv : a.val = i.val + 1 := by simpa using hP
    have h1 := ih a out1 hjv _ _ ‹_› ‹_›
    simp only [hjv] at h1
    refine ls_tail_cons h1 ?_
    simp [absTargetMajorL, hout1]

@[lockstep] theorem class_majors_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape)
    (ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64)))
    (pfvs : alloc.vec.Vec arena.handle.EIdx)
    (keys : alloc.vec.Vec arena.inductives.class_read.ClassKey) :
    LS pers (fun a b => b = absTargetMajorL a)
      (arena.inductives.gen_rec.class_majors pers st mode rf p ctors_as pfvs keys 0#usize
        (alloc.vec.Vec.new _)) lst
      (classMajors (ConRon.Refine.absMode mode) lf (absBlockShape p) (absCtorsLL ctors_as)
        (absEIdxL pfvs) (keys.val.map absClassKey)) := by
  have h := class_majors_acc (pers := pers) (mode := mode) hfe p ctors_as pfvs keys 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absTargetMajorL, alloc.vec.Vec.new] using h1.symm)

theorem classes_nfs_acc {pers} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absTargetMajorL a = absTargetMajorL out ++ b)
        (arena.inductives.gen_rec.classes_nfs pers st mode vis rf p former_tys tbl ms i out) lst
        (classesNfs (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (tbl.val.map absNestCtorNf) ((ms.val.drop i.val).map absTargetMajor)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absTargetMajorL a = absTargetMajorL out ++ b)
        (arena.inductives.gen_rec.classes_nfs pers st mode vis rf p former_tys tbl ms i out) lst
        (classesNfs (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
          (tbl.val.map absNestCtorNf) ((ms.val.drop i.val).map absTargetMajor))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classesNfs,
      arena.inductives.gen_rec.classes_nfs.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, classesNfs,
      arena.inductives.gen_rec.classes_nfs.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)]
    lockstep
    rename_i out1 hout1
    have hjv : a.val = i.val + 1 := by simpa using hP
    have h1 := ih a out1 hjv _ _ ‹_› ‹_›
    simp only [hjv] at h1
    refine ls_tail_cons h1 ?_
    simp [absTargetMajorL, hout1, absTargetMajor]

@[lockstep] theorem classes_nfs_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis rf lf)
    (p : arena.inductives.block_parts.BlockShape) (former_tys : alloc.vec.Vec arena.handle.EIdx)
    (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = absTargetMajorL a)
      (arena.inductives.gen_rec.classes_nfs pers st mode vis rf p former_tys tbl ms 0#usize
        (alloc.vec.Vec.new _)) lst
      (classesNfs (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL former_tys)
        (tbl.val.map absNestCtorNf) (ms.val.map absTargetMajor)) := by
  have h := classes_nfs_acc (pers := pers) (mode := mode) hctx p former_tys tbl ms 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absTargetMajorL, alloc.vec.Vec.new] using h1.symm)

/-- `class_former_ty` ⊑ `classFormerTy`. -/
@[lockstep] theorem class_former_ty_ls {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal) (m : arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.gen_rec.class_former_ty pers st rf cv_tas m) lst
      (classFormerTy lf (cv_tas.val.map absIConstantVal) (absTargetMajor m)) := by
  rw [arena.inductives.gen_rec.class_former_ty, classFormerTy]
  lockstep
  rename_i _ t hm n hn hkb v hd
  rw [hm, Option.map_some, Option.some.injEq] at hd
  subst hd
  rcases hP with hk | hk
  · have e : (List.map absIConstantVal cv_tas.val)[absU t]? =
        some (absIConstantVal (cv_tas.val[a.val]'hkb)) := by
      rw [List.getElem?_map, show absU t = a.val by simp [absU, hk],
        List.getElem?_eq_getElem hkb]
      rfl
    simp only [e]
    exact LS.pure (by simp [absIConstantVal]) ‹_› ‹_›
  · exfalso
    have := cv_tas.property
    scalar_tac

theorem class_former_tys_acc {pers} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.gen_rec.class_former_tys pers st rf cv_tas ms i out) lst
        (List.mapM.loop (classFormerTy lf (cv_tas.val.map absIConstantVal))
          ((ms.val.drop i.val).map absTargetMajor) (absEIdxL out).reverse) := by
  intro i out st lst hrel hinv
  refine ls_cursor_acc ms absTargetMajor
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l =>
      List.mapM.loop (classFormerTy lf (cv_tas.val.map absIConstantVal)) l (absEIdxL w).reverse)
    (fun st i w => arena.inductives.gen_rec.class_former_tys pers st rf cv_tas ms i w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.gen_rec.class_former_tys.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac)]
    simp only [List.mapM.loop, List.reverse_reverse]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.inductives.gen_rec.class_former_tys.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)]
    simp only [List.mapM.loop]
    lockstep

@[lockstep] theorem class_former_tys_ls {pers st lst} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.gen_rec.class_former_tys pers st rf cv_tas ms 0#usize (alloc.vec.Vec.new _))
      lst ((ms.val.map absTargetMajor).mapM (classFormerTy lf (cv_tas.val.map absIConstantVal))) := by
  have h := class_former_tys_acc (pers := pers) hfe cv_tas ms 0#usize (alloc.vec.Vec.new _) st lst
    hrel hinv
  simpa [absEIdxL, alloc.vec.Vec.new, List.mapM] using h

/-! ## The class keys: `class_key_canon`, `annotate_list`, `class_key_of`, `class_keys_of` -/

theorem class_key_canon_acc {pers} (params : alloc.vec.Vec arena.handle.EIdx)
    (k : arena.inductives.class_read.ClassKey) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absClassKey a)
        (arena.inductives.gen_rec.class_key_canon pers st params k i out) lst
        (do
          let ds ← List.mapM.loop (targetCanonParams (absEIdxL params))
            ((k.ds.val.drop i.val).map absEIdx) (absEIdxL out).reverse
          pure { absClassKey k with ds := ds }) := by
  intro i out st lst hrel hinv
  refine ls_cursor_acc k.ds absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l => do
      let ds ← List.mapM.loop (targetCanonParams (absEIdxL params)) l (absEIdxL w).reverse
      pure { absClassKey k with ds := ds })
    (fun st i w => arena.inductives.gen_rec.class_key_canon pers st params k i w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.gen_rec.class_key_canon.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len k.ds by scalar_tac)]
    simp only [List.mapM.loop, List.reverse_reverse]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.inductives.gen_rec.class_key_canon.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len k.ds by scalar_tac)]
    simp only [List.mapM.loop, bind_assoc]
    lockstep

@[lockstep] theorem class_key_canon_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (params : alloc.vec.Vec arena.handle.EIdx)
    (k : arena.inductives.class_read.ClassKey) :
    LS pers (fun a b => b = absClassKey a)
      (arena.inductives.gen_rec.class_key_canon pers st params k 0#usize (alloc.vec.Vec.new _)) lst
      (classKeyCanon (absEIdxL params) (absClassKey k)) := by
  have h := class_key_canon_acc (pers := pers) params k 0#usize (alloc.vec.Vec.new _) st lst
    hrel hinv
  simpa [absEIdxL, alloc.vec.Vec.new, List.mapM, classKeyCanon, absClassKey] using h

theorem annotate_list_acc {pers} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) (d : Std.U64)
    (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.gen_rec.annotate_list pers st mode rf d xs i out) lst
        (List.mapM.loop (fun x => annotateCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) x)
          ((xs.val.drop i.val).map absEIdx) (absEIdxL out).reverse) := by
  intro i out st lst hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l =>
      List.mapM.loop (fun x => annotateCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) x) l
        (absEIdxL w).reverse)
    (fun st i w => arena.inductives.gen_rec.annotate_list pers st mode rf d xs i w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.gen_rec.annotate_list.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.mapM.loop, List.reverse_reverse]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.inductives.gen_rec.annotate_list.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.mapM.loop]
    lockstep

@[lockstep] theorem annotate_list_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf) (d : Std.U64)
    (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.gen_rec.annotate_list pers st mode rf d xs 0#usize (alloc.vec.Vec.new _)) lst
      ((absEIdxL xs).mapM fun x => annotateCore (ConRon.Refine.absMode mode) lf checkFuel (absU d) x) := by
  have h := annotate_list_acc (pers := pers) (mode := mode) hfe d xs 0#usize (alloc.vec.Vec.new _)
    st lst hrel hinv
  simpa [absEIdxL, alloc.vec.Vec.new, List.mapM] using h

/-- `class_key_of` ⊑ `classKeyOf`. -/
@[lockstep] theorem class_key_of_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (params : alloc.vec.Vec arena.handle.EIdx) (k : arena.inductives.class_read.ClassKey) :
    LS pers (fun a b => b = absClassKey a)
      (arena.inductives.gen_rec.class_key_of pers st mode rf n_p params k) lst
      (classKeyOf (ConRon.Refine.absMode mode) lf (absU n_p) (absEIdxL params) (absClassKey k)) := by
  rw [arena.inductives.gen_rec.class_key_of, classKeyOf]
  lockstep

theorem class_keys_of_acc {pers} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (params : alloc.vec.Vec arena.handle.EIdx)
    (ks : alloc.vec.Vec arena.inductives.class_read.ClassKey) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.inductives.class_read.ClassKey) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.val.map absClassKey)
        (arena.inductives.gen_rec.class_keys_of pers st mode rf n_p params ks i out) lst
        (List.mapM.loop (classKeyOf (ConRon.Refine.absMode mode) lf (absU n_p) (absEIdxL params))
          ((ks.val.drop i.val).map absClassKey) (out.val.map absClassKey).reverse) := by
  intro i out st lst hrel hinv
  refine ls_cursor_acc ks absClassKey
    (fun (w : alloc.vec.Vec arena.inductives.class_read.ClassKey) l =>
      List.mapM.loop (classKeyOf (ConRon.Refine.absMode mode) lf (absU n_p) (absEIdxL params)) l
        (w.val.map absClassKey).reverse)
    (fun st i w => arena.inductives.gen_rec.class_keys_of pers st mode rf n_p params ks i w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.gen_rec.class_keys_of.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac)]
    simp only [List.mapM.loop, List.reverse_reverse]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [arena.inductives.gen_rec.class_keys_of.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)]
    simp only [List.mapM.loop]
    lockstep

@[lockstep] theorem class_keys_of_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (params : alloc.vec.Vec arena.handle.EIdx)
    (ks : alloc.vec.Vec arena.inductives.class_read.ClassKey) :
    LS pers (fun a b => b = a.val.map absClassKey)
      (arena.inductives.gen_rec.class_keys_of pers st mode rf n_p params ks 0#usize
        (alloc.vec.Vec.new _)) lst
      ((ks.val.map absClassKey).mapM
        (classKeyOf (ConRon.Refine.absMode mode) lf (absU n_p) (absEIdxL params))) := by
  have h := class_keys_of_acc (pers := pers) (mode := mode) hfe n_p params ks 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  simpa [alloc.vec.Vec.new, List.mapM] using h

/-! ## One class per member -/

theorem classes_at_member_abs (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor)
    (t : Std.U64) :
    ∀ (i : Std.Usize) (acc o : Std.U64),
      arena.inductives.gen_rec.classes_at_member ms t i acc = ok o →
      o.val = acc.val + (((ms.val.drop i.val).map absTargetMajor).filter
        (·.member == some (absU t))).length := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ acc o, arena.inductives.gen_rec.classes_at_member ms t i acc = ok o →
      o.val = acc.val + (((ms.val.drop i.val).map absTargetMajor).filter
        (·.member == some (absU t))).length) ?_ ?_ i ()
  · intro i _ hn acc o h
    rw [arena.inductives.gen_rec.classes_at_member.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), Result.ok.injEq] at h
    subst h; rw [List.drop_eq_nil_of_le hn]; simp
  · intro i _ hi ih acc o h
    rw [arena.inductives.gen_rec.classes_at_member.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)] at h
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.filter_cons]
    obtain ⟨tm, htm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some htm
    obtain ⟨hxb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hit, hhit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hhv : hit = ((absTargetMajor tm).member == some (absU t)) := by
      cases hm : tm.member with
      | none => rw [hm, Result.ok.injEq] at hhit; subst hhit; simp [absTargetMajor, hm]
      | some u =>
        rw [hm, Result.ok.injEq] at hhit; subst hhit
        simp only [absTargetMajor, hm, Option.map_some]
        by_cases hu : u = t
        · subst hu; simp
        · have : absU u ≠ absU t := fun h' => hu (u64_eq_iff_val.mpr h')
          simp [hu, this]
    rw [hxv, ← hhv]
    cases hit
    · rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 () hi2v acc o h, hi2v]; simp
    · rw [if_pos rfl] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨a2, ha2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      have ha2v : a2.val = acc.val + 1 := ConRon.Refine.Nat.uadd_val ha2
      rw [ih i2 () hi2v a2 o h, hi2v, ha2v]; simp; omega

theorem one_class_per_member_abs (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor)
    (k : Std.U64) :
    ∀ (m : Nat) (t : Std.U64) (o : Bool), k.val - t.val = m →
      arena.inductives.gen_rec.one_class_per_member ms k t = ok o →
      o = (List.range' t.val m).all (fun t =>
        ((ms.val.map absTargetMajor).filter (·.member == some t)).length == 1) := by
  intro m
  induction m with
  | zero =>
    intro t o hm h
    rw [arena.inductives.gen_rec.one_class_per_member.eq_def, if_pos (by scalar_tac),
      Result.ok.injEq] at h
    subst h; rfl
  | succ m ih =>
    intro t o hm h
    rw [arena.inductives.gen_rec.one_class_per_member.eq_def, if_neg (by scalar_tac)] at h
    rw [List.range'_succ, List.all_cons]
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnv := classes_at_member_abs ms t 0#usize 0#u64 n hn
    simp only [gr_usz0, List.drop_zero] at hnv
    by_cases h1 : n = 1#u64
    · rw [if_pos h1] at h
      obtain ⟨t2, ht2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ht2v : t2.val = t.val + 1 := ConRon.Refine.Nat.uadd_val ht2
      rw [ih t2 o (by omega) h, ht2v]
      have : ((List.map absTargetMajor ms.val).filter (·.member == some t.val)).length = 1 := by
        have h1v : n.val = 1 := by rw [h1]; rfl
        simp [absU] at hnv; omega
      simp [this]
    · rw [if_neg h1, Result.ok.injEq] at h
      subst h
      have : ((List.map absTargetMajor ms.val).filter (·.member == some t.val)).length ≠ 1 := by
        intro h2; apply h1; simp [absU] at hnv; scalar_tac
      simp [this]

@[lockstep] theorem one_class_per_member_twin
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) (k : Std.U64) :
    LSP (arena.inductives.gen_rec.one_class_per_member ms k 0#u64)
      (fun o => TwinEq ((List.range (absU k)).all (fun t =>
        ((ms.val.map absTargetMajor).filter (·.member == some t)).length == 1)) o) := by
  intro o h
  rw [TwinEq, one_class_per_member_abs ms k _ 0#u64 o rfl h]
  simp [List.range_eq_range', absU]

/-! ## `check_block_classes` -/

attribute [local lockstep_simp] absTargetMajorL absClassCtorL absClassCtorLL

theorem absClassCtorL_fun : absClassCtorL = fun cs => cs.val.map absClassCtor := rfl
attribute [local lockstep_simp] absClassCtorL_fun

/-- `check_block_classes` ⊑ `checkBlockClasses` — the export the block tail
reads. -/
@[lockstep] theorem check_block_classes_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (params : alloc.vec.Vec arena.handle.EIdx)
    (ctors_as : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    LS pers (fun a b => b = (absClassRead a.1, absTargetMajorL a.2))
      (arena.inductives.gen_rec.check_block_classes pers st mode rf p params ctors_as) lst
      (checkBlockClasses (ConRon.Refine.absMode mode) lf (absBlockShape p) (absEIdxL params)
        (absCtorsLL ctors_as)) := by
  rw [arena.inductives.gen_rec.check_block_classes, checkBlockClasses]
  lockstep

/-! ## The rules: `domains_resolve`, `domains_pw`, `class_rule_ok` (`_tail` inline) -/

theorem gr_strip_lams_wf {pers st} (hinv : AStateInv pers st) (n : Nat) :
    ∀ (k : Std.U64) (h : arena.handle.EIdx) bs leaf, k.val = n →
      arena.expr_ops.strip_lams pers st k h = ok (.Ok (some (bs, leaf))) → TeleWF bs := by
  induction n with
  | zero =>
    intro k h bs leaf hk hrun
    rw [arena.expr_ops.strip_lams, if_pos (by scalar_tac)] at hrun
    obtain ⟨e, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    exact TeleWF.new
  | succ n ih =>
    intro k h bs leaf hk hrun
    rw [arena.expr_ops.strip_lams, if_neg (by scalar_tac)] at hrun
    obtain ⟨tg, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    split at hrun
    · obtain ⟨o, hvb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases o with
      | none => simp [arena.monad.fail_dangling_e, arena.monad.fail] at hrun
      | some t =>
        obtain ⟨ty, b, m⟩ := t
        have hm := view_bind_meta_wf hinv hvb
        simp only at hrun
        obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases r with
        | Err _ => cases Result.ok_injective hrun
        | Ok o1 =>
          cases o1 with
          | none => cases Result.ok_injective hrun
          | some q =>
            obtain ⟨v, e⟩ := q
            simp only at hrun
            obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
            have hvr := ih k1 b v e
            cases Result.ok_injective hrun
            have hv := hvr (by have := ConRon.Refine.Nat.usub_val hk1; scalar_tac) hr
            intro p hp
            rw [rc_cons_binder_val hv1] at hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hm
            · exact hv p hp
    · cases Result.ok_injective hrun

/-- `strip_lams` with its telescope's well-formedness in the answer. -/
theorem gr_strip_lams_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absStrip a ∧ StripWF a)
      (arena.expr_ops.strip_lams pers st k h) st lst (stripLams (absU k) (absEIdx h)) := by
  intro o hrun
  have h1 := ExprOps.strip_lams_ls hrel hinv k h o hrun
  cases o with
  | Err e => exact h1
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h2, h3⟩ := h1
    refine ⟨b, lst', hx, ⟨hR, ?_⟩, h2, h3⟩
    cases a with
    | none => trivial
    | some q => exact gr_strip_lams_wf hinv _ k h q.1 q.2 rfl hrun

attribute [local lockstep high] gr_strip_lams_wf_ls

theorem domains_resolve_aux {pers} {vis_t : Std.U64}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (m : Nat) :
    ∀ (i : Std.Usize) st lst, rbs.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.gen_rec.domains_resolve pers vis_t st rf rbs i) lst
        (((rbs.val.drop i.val).map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).allM
          fun b => constsResolveFFast (lf.restrictTo (absU vis_t)) b.1) := by
  induction m with
  | zero =>
    intro i st lst hm hrel hinv
    rw [List.drop_eq_nil_of_le (by omega), List.map_nil, List.allM,
      arena.inductives.gen_rec.domains_resolve.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rbs by scalar_tac)]
    lockstep
  | succ m ih =>
    intro i st lst hm hrel hinv
    have hi : i.val < rbs.val.length := by omega
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.allM,
      arena.inductives.gen_rec.domains_resolve.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rbs by scalar_tac)]
    lockstep
    all_goals
      cases b
      · exact LS.pure rfl ‹_› ‹_›
      · exact absurd rfl hc

/-- `domains_resolve` ⊑ the rule's `rbs.allM (constsResolveFFast (feR.restrictTo visT) ·.1)`,
from the cursor on. -/
@[lockstep] theorem domains_resolve_ls {pers} {vis_t : Std.U64}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.gen_rec.domains_resolve pers vis_t st rf rbs i) lst
        (((rbs.val.drop i.val).map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).allM
          fun b => constsResolveFFast (lf.restrictTo (absU vis_t)) b.1) :=
  fun i st lst => domains_resolve_aux hfe rbs _ i st lst rfl

@[lockstep] theorem domains_resolve_zero_ls {pers st lst} {vis_t : Std.U64}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) (rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    LS pers (fun a b => b = a)
      (arena.inductives.gen_rec.domains_resolve pers vis_t st rf rbs 0#usize) lst
      ((rbs.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).allM
        fun b => constsResolveFFast (lf.restrictTo (absU vis_t)) b.1) := by
  have h := domains_resolve_ls (pers := pers) (vis_t := vis_t) hfe rbs 0#usize st lst hrel hinv
  simpa using h

/-- `domains_pw` is the rule's `rbs.all (·.2.pw == pw)`, at canonical data. -/
@[lockstep] theorem domains_pw_twin (rbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (pw : kernel.prop_when.PropWhen) (hrbs : TeleWF rbs) (hpw : ConRon.Refine.PropWhenWF pw) :
    LSP (arena.inductives.gen_rec.domains_pw rbs pw 0#usize)
      (fun o => TwinEq ((rbs.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).all
        fun b => b.2.pw == ConRon.Refine.absPropWhen pw) o) := by
  intro o h
  have := vec_cursor_all rbs
    (fun p => (ConRon.Refine.absBinderMeta p.2).pw == ConRon.Refine.absPropWhen pw)
    (fun i => arena.inductives.gen_rec.domains_pw rbs pw i) ?_ ?_ 0#usize o h
  · rw [TwinEq, this]; simp [List.all_map]; rfl
  · intro i o hn h
    rw [arena.inductives.gen_rec.domains_pw.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rbs by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  · intro i x o hx h
    rw [arena.inductives.gen_rec.domains_pw.eq_def, if_neg (show ¬ i ≥ alloc.vec.Vec.len rbs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    have hqwf : ConRon.Refine.PropWhenWF q.2.pw :=
      hrbs q (List.mem_of_getElem? hx)
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hcv : c = (ConRon.Refine.absPropWhen q.2.pw == ConRon.Refine.absPropWhen pw) := by
      have := ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape hqwf)
        (ConRon.Refine.PropWhen.wf_shape hpw) hc
      cases c <;> simp_all
    cases c
    · rw [if_neg (by simp)] at h
      rw [Result.ok.injEq] at h
      right; exact ⟨by simpa [ConRon.Refine.absBinderMeta] using hcv.symm, h.symm⟩
    · rw [if_pos rfl] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      left; exact ⟨by simpa [ConRon.Refine.absBinderMeta] using hcv.symm, i2, absSz_add_one hi2, h⟩

attribute [local lockstep_inline] arena.inductives.gen_rec.class_rule_ok_tail

/-- `class_rule_ok` (with `class_rule_ok_tail` inline) ⊑ `classRuleOk`. -/
@[lockstep] theorem class_rule_ok_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis_t vis_r : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf) (hvr : absU vis_r = lf.visibleBelow)
    (cv_r : arena.env.IConstantVal) (pw : kernel.prop_when.PropWhen)
    (hpw : ConRon.Refine.PropWhenWF pw) (n : Std.U64) (gen : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.gen_rec.class_rule_ok pers st mode vis_t vis_r rf cv_r pw n gen) lst
      (classRuleOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absIConstantVal cv_r)
        (ConRon.Refine.absPropWhen pw) (absU n) (absEIdx gen)) := by
  rw [arena.inductives.gen_rec.class_rule_ok, classRuleOk]
  lockstep

/-! ## `class_const_ok` (`_type` inline), `class_rec_ty_ok`, `class_rec_tys_ok` -/

attribute [local lockstep_inline] arena.inductives.gen_rec.class_const_ok_type

/-- `class_const_ok` (with `class_const_ok_type` inline) ⊑ `classConstOk`. -/
@[lockstep] theorem class_const_ok_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf) (cv : arena.env.IConstantVal) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.inductives.gen_rec.class_const_ok pers st mode rf cv) lst
      (classConstOk (ConRon.Refine.absMode mode) lf (absIConstantVal cv)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.gen_rec.class_const_ok, classConstOk]
  lockstep

theorem gr_absRecShape_tgt (r : arena.inductives.block_parts.RecShape) :
    (absRecShape r).tgt = absU r.tgt := rfl
theorem gr_absRecShape_rP (r : arena.inductives.block_parts.RecShape) :
    (absRecShape r).rP = absU r.r_p := rfl
theorem gr_absRecShape_mI (r : arena.inductives.block_parts.RecShape) :
    (absRecShape r).mI = absU r.m_i := rfl
theorem gr_absRecShape_cvR (r : arena.inductives.block_parts.RecShape) :
    (absRecShape r).cvR = absIConstantVal r.cv_r := rfl

theorem gr_absU_beq (a b : Std.U64) : (absU a == absU b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : absU a ≠ absU b := fun h' => h (u64_eq_iff_val.mpr h')
    simp [h, this]

attribute [local lockstep_simp] gr_absRecShape_tgt gr_absRecShape_rP gr_absRecShape_mI
  gr_absRecShape_cvR gr_absU_beq

/-- `class_rec_ty_ok` ⊑ `classRecTyOk`. -/
@[lockstep] theorem class_rec_ty_ok_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf) (g : arena.inductives.gen_rec.ClassGen)
    (hg : ClassGenWF g) (k : Std.U64) (rc : arena.inductives.block_parts.RecShape)
    (cv_ri : arena.env.IConstantVal) (c : Std.U64) :
    LS pers (fun a b => b = absIConstantVal a)
      (arena.inductives.gen_rec.class_rec_ty_ok pers st mode rf g k rc cv_ri c) lst
      (classRecTyOk (ConRon.Refine.absMode mode) lf (absClassGen g) (absU k) (absRecShape rc)
        (absIConstantVal cv_ri) (absU c)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.gen_rec.class_rec_ty_ok, classRecTyOk]
  lockstep

def absICVList (v : alloc.vec.Vec arena.env.IConstantVal) : List IConstantVal :=
  v.val.map absIConstantVal

attribute [local lockstep_simp] absICVList

theorem class_rec_tys_ok_acc {pers} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (g : arena.inductives.gen_rec.ClassGen) (hg : ClassGenWF g) (k : Std.U64)
    (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (cvs : alloc.vec.Vec arena.env.IConstantVal) (cs : alloc.vec.Vec Std.U64) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantVal) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absICVList a = absICVList out ++ b)
        (arena.inductives.gen_rec.class_rec_tys_ok pers st mode rf g k rcs cvs cs i out) lst
        (classRecTysOk (ConRon.Refine.absMode mode) lf (absClassGen g) (absU k)
          ((rcs.val.drop i.val).map absRecShape) ((cvs.val.drop i.val).map absIConstantVal)
          ((cs.val.drop i.val).map absU)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) rcs.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absICVList a = absICVList out ++ b)
        (arena.inductives.gen_rec.class_rec_tys_ok pers st mode rf g k rcs cvs cs i out) lst
        (classRecTysOk (ConRon.Refine.absMode mode) lf (absClassGen g) (absU k)
          ((rcs.val.drop i.val).map absRecShape) ((cvs.val.drop i.val).map absIConstantVal)
          ((cs.val.drop i.val).map absU))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil,
      arena.inductives.gen_rec.class_rec_tys_ok.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rcs by scalar_tac)]
    simp only [classRecTysOk]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons,
      arena.inductives.gen_rec.class_rec_tys_ok.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rcs by scalar_tac)]
    by_cases hv : i.val < cvs.val.length
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cvs by scalar_tac),
        List.drop_eq_getElem_cons hv, List.map_cons]
      by_cases hc : i.val < cs.val.length
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac),
          List.drop_eq_getElem_cons hc, List.map_cons, classRecTysOk]
        lockstep
        rename_i x out1 hout1
        have hjv : a.val = i.val + 1 := by simpa using hP
        have h1 := ih a out1 hjv _ _ ‹_› ‹_›
        simp only [hjv] at h1
        refine ls_tail_cons h1 ?_
        simp [absICVList, hout1]
      · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac),
          List.drop_eq_nil_of_le (show cs.val.length ≤ i.val by omega), List.map_nil]
        simp only [classRecTysOk]
        lockstep
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cvs by scalar_tac),
        List.drop_eq_nil_of_le (show cvs.val.length ≤ i.val by omega), List.map_nil]
      simp only [classRecTysOk]
      lockstep

@[lockstep] theorem class_rec_tys_ok_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (g : arena.inductives.gen_rec.ClassGen) (hg : ClassGenWF g) (k : Std.U64)
    (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (cvs : alloc.vec.Vec arena.env.IConstantVal) (cs : alloc.vec.Vec Std.U64) :
    LS pers (fun a b => b = absICVList a)
      (arena.inductives.gen_rec.class_rec_tys_ok pers st mode rf g k rcs cvs cs 0#usize
        (alloc.vec.Vec.new _)) lst
      (classRecTysOk (ConRon.Refine.absMode mode) lf (absClassGen g) (absU k)
        (rcs.val.map absRecShape) (cvs.val.map absIConstantVal) (cs.val.map absU)) := by
  have h := class_rec_tys_ok_acc (pers := pers) (mode := mode) hfe g hg k rcs cvs cs 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absICVList, alloc.vec.Vec.new] using h1.symm)

/-! ## `class_stream_recs`, `class_seeds` -/

theorem class_stream_recs_acc {pers} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantVal) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absICVList a = absICVList out ++ b)
        (arena.inductives.gen_rec.class_stream_recs pers st mode rf rcs i out) lst
        (classStreamRecs (ConRon.Refine.absMode mode) lf ((rcs.val.drop i.val).map absRecShape)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) rcs.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absICVList a = absICVList out ++ b)
        (arena.inductives.gen_rec.class_stream_recs pers st mode rf rcs i out) lst
        (classStreamRecs (ConRon.Refine.absMode mode) lf
          ((rcs.val.drop i.val).map absRecShape))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classStreamRecs,
      arena.inductives.gen_rec.class_stream_recs.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len rcs by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, classStreamRecs,
      arena.inductives.gen_rec.class_stream_recs.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len rcs by scalar_tac)]
    lockstep
    rename_i x out1 hout1
    have hjv : a.val = i.val + 1 := by simpa using hP
    have h1 := ih a out1 hjv _ _ ‹_› ‹_›
    simp only [hjv] at h1
    refine ls_tail_cons h1 ?_
    simp [absICVList, hout1]

@[lockstep] theorem class_stream_recs_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (rcs : alloc.vec.Vec arena.inductives.block_parts.RecShape) :
    LS pers (fun a b => b = absICVList a)
      (arena.inductives.gen_rec.class_stream_recs pers st mode rf rcs 0#usize (alloc.vec.Vec.new _))
      lst (classStreamRecs (ConRon.Refine.absMode mode) lf (rcs.val.map absRecShape)) := by
  have h := class_stream_recs_acc (pers := pers) (mode := mode) hfe rcs 0#usize
    (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absICVList, alloc.vec.Vec.new] using h1.symm)

def absSeedL (v : alloc.vec.Vec (arena.inductives.positivity.NestKey × Std.U64)) :
    List (NestKey × Nat) :=
  v.val.map fun p => (absNestKey p.1, absU p.2)

theorem class_seeds_acc {pers} (ctx : arena.inductives.positivity.NestCtx)
    (holes : alloc.vec.Vec arena.handle.EIdx)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (arena.inductives.positivity.NestKey × Std.U64)) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absSeedL a = absSeedL out ++ b)
        (arena.inductives.gen_rec.class_seeds pers st ctx holes ms i out) lst
        (classSeeds (absNestCtx ctx) (absEIdxL holes) ((ms.val.drop i.val).map absTargetMajor)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absSeedL a = absSeedL out ++ b)
        (arena.inductives.gen_rec.class_seeds pers st ctx holes ms i out) lst
        (classSeeds (absNestCtx ctx) (absEIdxL holes)
          ((ms.val.drop i.val).map absTargetMajor))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classSeeds,
      arena.inductives.gen_rec.class_seeds.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, classSeeds,
      arena.inductives.gen_rec.class_seeds.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac)]
    rw [gr_vec_index_eq (List.getElem?_eq_getElem hi), bind_tc_ok]
    cases hm : (ms.val[i.val]'hi).member <;>
      simp only [absTargetMajor_member, hm, Option.map_none, Option.map_some]
    · lockstep
      rename_i x out1 hout1
      have hjv : a.val = i.val + 1 := by simpa using hP
      have h1 := ih a out1 hjv _ _ ‹_› ‹_›
      simp only [hjv] at h1
      refine ls_tail_cons h1 ?_
      simp [absSeedL, hout1]
    · lockstep

/-- `class_seeds` ⊑ `classSeeds` — the export the block tail reads. -/
@[lockstep] theorem class_seeds_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    (holes : alloc.vec.Vec arena.handle.EIdx)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor) :
    LS pers (fun a b => b = absSeedL a)
      (arena.inductives.gen_rec.class_seeds pers st ctx holes ms 0#usize (alloc.vec.Vec.new _)) lst
      (classSeeds (absNestCtx ctx) (absEIdxL holes) (ms.val.map absTargetMajor)) := by
  have h := class_seeds_acc (pers := pers) ctx holes ms 0#usize (alloc.vec.Vec.new _) st lst
    hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absSeedL, alloc.vec.Vec.new] using h1.symm)

/-! ## `class_rules_ok`, `class_recs_rules_ok` -/

theorem class_rules_ok_acc {pers} {mode : kernel.env.CheckMode}
    {vis_t vis_r : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (hvr : absU vis_r = lf.visibleBelow) (g : arena.inductives.gen_rec.ClassGen)
    (hg : ClassGenWF g) (rec_cls : alloc.vec.Vec Std.U64)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (cv_r : arena.env.IConstantVal)
    (pw : kernel.prop_when.PropWhen) (hpw : ConRon.Refine.PropWhenWF pw) (c : Std.U64)
    (xs : alloc.vec.Vec arena.inductives.gen_rec.ClassCtor) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absEIdxL a = absEIdxL out ++ b)
        (arena.inductives.gen_rec.class_rules_ok pers st mode vis_t vis_r rf g rec_cls cv_gs cv_r pw
          c xs i out) lst
        (classRulesOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absClassGen g)
          (absNatL rec_cls) (cv_gs.val.map absIConstantVal) (absIConstantVal cv_r)
          (ConRon.Refine.absPropWhen pw) (absU c) ((xs.val.drop i.val).map absClassCtor)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absEIdxL a = absEIdxL out ++ b)
        (arena.inductives.gen_rec.class_rules_ok pers st mode vis_t vis_r rf g rec_cls cv_gs cv_r pw
          c xs i out) lst
        (classRulesOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absClassGen g)
          (absNatL rec_cls) (cv_gs.val.map absIConstantVal) (absIConstantVal cv_r)
          (ConRon.Refine.absPropWhen pw) (absU c) ((xs.val.drop i.val).map absClassCtor))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil, classRulesOk,
      arena.inductives.gen_rec.class_rules_ok.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons, classRulesOk,
      arena.inductives.gen_rec.class_rules_ok.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    lockstep
    rename_i x out1 hout1
    have hjv : a.val = i.val + 1 := by simpa using hP
    have h1 := ih a out1 hjv _ _ ‹_› ‹_›
    simp only [hjv] at h1
    refine ls_tail_cons h1 ?_
    simp [absEIdxL, hout1]

@[lockstep] theorem class_rules_ok_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis_t vis_r : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (hvr : absU vis_r = lf.visibleBelow) (g : arena.inductives.gen_rec.ClassGen)
    (hg : ClassGenWF g) (rec_cls : alloc.vec.Vec Std.U64)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (cv_r : arena.env.IConstantVal)
    (pw : kernel.prop_when.PropWhen) (hpw : ConRon.Refine.PropWhenWF pw) (c : Std.U64)
    (xs : alloc.vec.Vec arena.inductives.gen_rec.ClassCtor) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.gen_rec.class_rules_ok pers st mode vis_t vis_r rf g rec_cls cv_gs cv_r pw
        c xs 0#usize (alloc.vec.Vec.new _)) lst
      (classRulesOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absClassGen g)
        (absNatL rec_cls) (cv_gs.val.map absIConstantVal) (absIConstantVal cv_r)
        (ConRon.Refine.absPropWhen pw) (absU c) (xs.val.map absClassCtor)) := by
  have h := class_rules_ok_acc (pers := pers) (mode := mode) (vis_t := vis_t) hfe hvr g hg rec_cls cv_gs cv_r pw
    hpw c xs 0#usize (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absEIdxL, alloc.vec.Vec.new] using h1.symm)

def absRuleOut (t : arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
    alloc.vec.Vec arena.handle.EIdx) : IConstantVal × TargetMajor × List EIdx :=
  (absIConstantVal t.1, absTargetMajor t.2.1, absEIdxL t.2.2)

def absRuleOutL (v : alloc.vec.Vec (arena.env.IConstantVal × arena.inductives.rec_check.TargetMajor ×
    alloc.vec.Vec arena.handle.EIdx)) : List (IConstantVal × TargetMajor × List EIdx) :=
  v.val.map absRuleOut

theorem class_recs_rules_ok_acc {pers} {mode : kernel.env.CheckMode}
    {vis_t vis_r : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (hvr : absU vis_r = lf.visibleBelow) (g : arena.inductives.gen_rec.ClassGen)
    (hg : ClassGenWF g) (rec_cls : alloc.vec.Vec Std.U64) (pw : kernel.prop_when.PropWhen)
    (hpw : ConRon.Refine.PropWhenWF pw) (cv_gs : alloc.vec.Vec arena.env.IConstantVal) :
    ∀ (i : Std.Usize) out st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absRuleOutL a = absRuleOutL out ++ b)
        (arena.inductives.gen_rec.class_recs_rules_ok pers st mode vis_t vis_r rf g rec_cls pw cv_gs
          i out) lst
        (classRecsRulesOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absClassGen g)
          (absNatL rec_cls) (ConRon.Refine.absPropWhen pw) (cv_gs.val.map absIConstantVal)
          ((cv_gs.val.drop i.val).map absIConstantVal) ((rec_cls.val.drop i.val).map absU)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cv_gs.val.length
    (fun i out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => absRuleOutL a = absRuleOutL out ++ b)
        (arena.inductives.gen_rec.class_recs_rules_ok pers st mode vis_t vis_r rf g rec_cls pw cv_gs
          i out) lst
        (classRecsRulesOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absClassGen g)
          (absNatL rec_cls) (ConRon.Refine.absPropWhen pw) (cv_gs.val.map absIConstantVal)
          ((cv_gs.val.drop i.val).map absIConstantVal) ((rec_cls.val.drop i.val).map absU))) ?_ ?_ i
  · intro i out hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil,
      arena.inductives.gen_rec.class_recs_rules_ok.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cv_gs by scalar_tac)]
    simp only [classRecsRulesOk]
    exact LS.pure (by simp) hrel hinv
  · intro i out hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons,
      arena.inductives.gen_rec.class_recs_rules_ok.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cv_gs by scalar_tac)]
    by_cases hr : i.val < rec_cls.val.length
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rec_cls by scalar_tac),
        List.drop_eq_getElem_cons hr, List.map_cons, classRecsRulesOk]
      rw [gr_vec_index_eq (List.getElem?_eq_getElem hr), bind_tc_ok]
      rcases hcl : (g.ctors.val)[(rec_cls.val[i.val]).val]? with _ | v <;>
        simp only [absClassGen_ctors, List.getD_eq_getElem?_getD, List.getElem?_map, absU, hcl,
          Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
      all_goals lockstep
      all_goals first
        | (exfalso; rw [List.getElem?_eq_none_iff] at hcl
           have := g.ctors.property
           casesm* (_ : Nat) = _ ∨ Std.Usize.max < _ <;> scalar_tac)
        | (rename_i iv1 hiv1 out1 hout1
           have hjv : a.val = i.val + 1 := by simpa using hP
           have h1 := ih a out1 hjv _ _ ‹_› ‹_›
           simp only [hjv] at h1
           refine ls_tail_cons h1 ?_
           simp [absRuleOutL, absRuleOut, hout1, hiv1])
    · rw [if_pos (show i ≥ alloc.vec.Vec.len rec_cls by scalar_tac),
        List.drop_eq_nil_of_le (show rec_cls.val.length ≤ i.val by omega), List.map_nil]
      simp only [classRecsRulesOk]
      exact LS.pure (by simp) hrel hinv

@[lockstep] theorem class_recs_rules_ok_ls {pers st lst} {mode : kernel.env.CheckMode}
    {vis_t vis_r : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (hvr : absU vis_r = lf.visibleBelow) (g : arena.inductives.gen_rec.ClassGen)
    (hg : ClassGenWF g) (rec_cls : alloc.vec.Vec Std.U64) (pw : kernel.prop_when.PropWhen)
    (hpw : ConRon.Refine.PropWhenWF pw) (cv_gs : alloc.vec.Vec arena.env.IConstantVal) :
    LS pers (fun a b => b = absRuleOutL a)
      (arena.inductives.gen_rec.class_recs_rules_ok pers st mode vis_t vis_r rf g rec_cls pw cv_gs
        0#usize (alloc.vec.Vec.new _)) lst
      (classRecsRulesOk (ConRon.Refine.absMode mode) (absU vis_t) lf (absClassGen g)
        (absNatL rec_cls) (ConRon.Refine.absPropWhen pw) (cv_gs.val.map absIConstantVal)
        (cv_gs.val.map absIConstantVal) (rec_cls.val.map absU)) := by
  have h := class_recs_rules_ok_acc (pers := pers) (mode := mode) (vis_t := vis_t) hfe hvr g hg
    rec_cls pw hpw cv_gs 0#usize (alloc.vec.Vec.new _) st lst hrel hinv
  simp only [gr_usz0, List.drop_zero] at h
  exact LS.tail h rfl (fun a b h1 => by simpa [absRuleOutL, alloc.vec.Vec.new] using h1.symm)

/-! ## The temporary recursors: `class_fe_r_push` / `class_fe_r_pop`

The port pushes the rule-less recursors onto the index IN PLACE
(`ifenv_push_temp`, recording each displaced raw row `(counter, position)`) and
pops them in reverse (`ifenv_pop_temp`, `resize` and the row put back); the
twin pushes (`IFEnv.push`) recording the displaced `(counter, constant)` row and
pops by `foldr popTemp`.  The two records are not related row by row: each side
is shown to come back to an index that ANSWERS like the one it started from
(`RFEq` for the port — the same list, bound and row function, the `HashMap2`
itself is not structurally restored — and `TFEq` for the twin), and
`IFEnvRelI.transfer` carries the relation across. -/

/-- Two port indexes that answer alike. -/
def RFEq (a b : arena.env.IFEnv) : Prop :=
  a.env.consts.val = b.env.consts.val ∧
    ConRon.Refine.HashMap2.toFun a.idx = ConRon.Refine.HashMap2.toFun b.idx ∧
    a.visible_below = b.visible_below

theorem RFEq.refl (a : arena.env.IFEnv) : RFEq a a := ⟨rfl, rfl, rfl⟩

theorem RFEq.trans {a b c : arena.env.IFEnv} (h₁ : RFEq a b) (h₂ : RFEq b c) : RFEq a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/-- The port index's table invariant alone. -/
abbrev IdxInv (a : arena.env.IFEnv) : Prop :=
  ConRon.Refine.HashMap2.Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable a.idx

/-- Two twin indexes that answer alike (`Bridge/Inductives/GenRec.lean`'s
`GR.FEq`, restated below the bridge). -/
def TFEq (a b : IFEnv) : Prop :=
  a.env = b.env ∧ a.visibleBelow = b.visibleBelow ∧ ∀ n : NIdx, a.idx[n]? = b.idx[n]?

theorem TFEq.refl (a : IFEnv) : TFEq a a := ⟨rfl, rfl, fun _ => rfl⟩

theorem TFEq.trans {a b c : IFEnv} (h₁ : TFEq a b) (h₂ : TFEq b c) : TFEq a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun n => (h₁.2.2 n).trans (h₂.2.2 n)⟩

theorem TFEq.popTemp {a b : IFEnv} (h : TFEq a b) (n : NIdx)
    (prev : Option (Nat × IConstantInfo)) : TFEq (a.popTemp n prev) (b.popTemp n prev) := by
  refine ⟨by simp only [IFEnv.popTemp, h.1], by simp only [IFEnv.popTemp, h.2.1], fun k => ?_⟩
  simp only [IFEnv.popTemp]
  cases prev with
  | none =>
    simp only [Std.HashMap.getElem?_erase]
    split <;> simp [h.2.2 k]
  | some r =>
    simp only [Std.HashMap.getElem?_insert]
    split <;> simp [h.2.2 k]

theorem TFEq.popTemp_push (fe : IFEnv) (ci : IConstantInfo) :
    TFEq ((fe.push ci).popTemp ci.name fe.idx[ci.name]?) fe := by
  refine ⟨rfl, by simp only [IFEnv.popTemp, IFEnv.push]; omega, fun k => ?_⟩
  simp only [IFEnv.popTemp, IFEnv.push]
  cases hprev : fe.idx[ci.name]? with
  | none =>
    simp only [Std.HashMap.getElem?_erase, Std.HashMap.getElem?_insert]
    by_cases hk : (ci.name == k) = true
    · have : ci.name = k := eq_of_beq hk
      subst this
      simp [hprev]
    · simp [hk]
  | some r =>
    simp only [Std.HashMap.getElem?_insert]
    by_cases hk : (ci.name == k) = true
    · have : ci.name = k := eq_of_beq hk
      subst this
      simp [hprev]
    · simp [hk]

/-- **The relation survives answering-alike indexes on both sides.** -/
theorem IFEnvRelI.transfer {rf rf' : arena.env.IFEnv} {lf lf' : IFEnv} (h : IFEnvRelI rf lf)
    (hr : RFEq rf' rf) (hi : IdxInv rf') (hl : TFEq lf' lf) : IFEnvRelI rf' lf' := by
  obtain ⟨⟨henv, hidx, hvb, hwf, hkeys⟩, ⟨-, hbound, hrange⟩⟩ := h
  obtain ⟨hc, ht, hv⟩ := hr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hi, ?_, ?_⟩
  · rw [hl.1, henv]; simp only [absIEnv, hc]
  · intro n; rw [ht, hc, hl.2.2]; exact hidx n
  · rw [hl.2.1, hvb, hv]
  · intro ci hci; rw [hc] at hci; exact hwf ci hci
  · intro k p hp; rw [ht] at hp; rw [hc]; exact hkeys k p hp
  · rw [hv, hc]; exact hbound
  · intro n p hp; rw [ht] at hp; rw [hc]; exact hrange n p hp

/-- `ifenv_push_temp` is `ifenv_push` with the displaced row handed back. -/
theorem gr_ifenv_push_temp_spec {rf rf' : arena.env.IFEnv} {ci : arena.env.IConstantInfo}
    {prev : Option (Std.U64 × Std.U64)} (hfinv : IFEnvInv rf)
    (h : arena.env.ifenv_push_temp rf ci = ok (prev, rf')) :
    arena.env.ifenv_push rf ci = ok rf' ∧
    ∃ n, arena.env.i_constant_info_name ci = ok n ∧
      prev = ConRon.Refine.HashMap2.toFun rf.idx n ∧
      rf'.env.consts.val = rf.env.consts.val ++ [ci] ∧
      (∃ s : Std.U64, s.val = rf.env.consts.val.length ∧
        ConRon.Refine.HashMap2.toFun rf'.idx =
          Function.update (ConRon.Refine.HashMap2.toFun rf.idx) n (some (rf.visible_below, s))) ∧
      rf'.visible_below.val = rf.visible_below.val + 1 ∧ IdxInv rf' := by
  rw [arena.env.ifenv_push_temp] at h
  obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hinv', hold, hupd, -⟩ :=
    ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
      hfinv.idxInv ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have h' := Prod.mk.inj (Result.ok_injective h)
  obtain ⟨rfl, rfl⟩ := h'
  refine ⟨?_, n, hn, hold, ConRon.Refine.vec_push_val hv, ⟨s, ?_, hupd⟩, ?_, hinv'⟩
  · rw [arena.env.ifenv_push, hs]
    simp only [bind_tc_ok, hn, hq, hv, hc1]
    rfl
  · simp only [lift, Result.ok.injEq] at hs; subst hs
    simp
  · simpa using ConRon.Refine.Nat.uadd_val hc1

/-- `ifenv_pop_temp`: the last constant dropped, the row under `n` put back as
`prev`, the counter one down. -/
theorem gr_ifenv_pop_temp_spec {fe out : arena.env.IFEnv} {n : arena.handle.NIdx}
    {prev : Option (Std.U64 × Std.U64)} (hi : IdxInv fe)
    (h : arena.env.ifenv_pop_temp fe n prev = ok out) :
    out.env.consts.val = fe.env.consts.val.take (fe.env.consts.val.length - 1) ∧
      ConRon.Refine.HashMap2.toFun out.idx =
        Function.update (ConRon.Refine.HashMap2.toFun fe.idx) n prev ∧
      out.visible_below.val = fe.visible_below.val - 1 ∧ 1 ≤ fe.visible_below.val ∧
      IdxInv out := by
  unfold arena.env.ifenv_pop_temp at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hvv : v.val = fe.env.consts.val.take (fe.env.consts.val.length - 1) := by
    split at hv
    · rename_i h0
      rw [Result.ok.injEq] at hv; subst hv
      have : fe.env.consts.val.length = 0 := by
        have := congrArg (fun x : Std.Usize => x.val) h0; simpa using this
      rw [List.eq_nil_of_length_eq_zero this]; rfl
    · rename_i h0
      obtain ⟨i, hi', hv⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv
      obtain ⟨ii, -, hv⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv
      have hiv := ConRon.Refine.Nat.usub_val hi'
      rw [alloc.vec.Vec.resize, if_pos (by simp [alloc.vec.Vec.length] at *; omega),
        Result.ok.injEq] at hv
      subst hv
      simp only [List.resize, alloc.vec.Vec.len] at *
      simp [hiv.2]
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c1, hc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [Result.ok.injEq] at h
  subst h
  have hc1v := ConRon.Refine.Nat.usub_val hc1
  have hhmv : ConRon.Refine.HashMap2.Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable hm ∧
      ConRon.Refine.HashMap2.toFun hm =
        Function.update (ConRon.Refine.HashMap2.toFun fe.idx) n prev := by
    cases prev with
    | none =>
      obtain ⟨q, hq, hhm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hhm
      obtain ⟨q1, q2⟩ := q
      obtain rfl := Result.ok_injective (show ok q2 = ok hm from hhm)
      obtain ⟨hinv', -, hupd, -⟩ :=
        ConRon.Refine.HashMap2.remove_refines_wf (P := fun _ => True) nidx_eq2
          hi ConRon.Refine.HashMap2.KeysOk_true trivial hq
      exact ⟨hinv', hupd⟩
    | some row =>
      obtain ⟨n1, hn1, hhm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hhm
      obtain ⟨q, hq, hhm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hhm
      obtain ⟨q1, q2⟩ := q
      obtain rfl := Result.ok_injective (show ok q2 = ok hm from hhm)
      rw [dupId_nidx _ _ hn1] at hq
      obtain ⟨hinv', -, hupd, -⟩ :=
        ConRon.Refine.HashMap2.insert_refines_wf (P := fun _ => True) nidx_eq2
          hi ConRon.Refine.HashMap2.KeysOk_true trivial hq
      exact ⟨hinv', hupd⟩
  exact ⟨hvv, hhmv.2, by simpa using hc1v.2, by simpa using hc1v.1, hhmv.1⟩

/-- **A pop undoes its push** on the port side, from any index answering like
the pushed one. -/
theorem gr_pop_push {rf rf1 rfX out : arena.env.IFEnv} {ci : arena.env.IConstantInfo}
    {n : arena.handle.NIdx} {prev : Option (Std.U64 × Std.U64)} (hfinv : IFEnvInv rf)
    (hpush : arena.env.ifenv_push_temp rf ci = ok (prev, rf1))
    (hn : arena.env.i_constant_info_name ci = ok n)
    (hX : RFEq rfX rf1) (hXi : IdxInv rfX)
    (hpop : arena.env.ifenv_pop_temp rfX n prev = ok out) :
    RFEq out rf ∧ IdxInv out := by
  obtain ⟨-, n', hn', hprev, hc, ⟨s, -, ht⟩, hvb, -⟩ := gr_ifenv_push_temp_spec hfinv hpush
  rw [hn] at hn'; cases Result.ok_injective hn'
  obtain ⟨hoc, hot, hov, hov1, hoi⟩ := gr_ifenv_pop_temp_spec hXi hpop
  obtain ⟨hXc, hXt, hXv⟩ := hX
  refine ⟨⟨?_, ?_, ?_⟩, hoi⟩
  · rw [hoc, hXc, hc]; simp
  · rw [hot, hXt, ht, hprev]
    funext k
    by_cases hk : k = n
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  · apply UScalar.eq_imp
    rw [hov, hXv, hvb]; omega

/-- The twin's pops restore the index the pushes started from
(`Bridge/Inductives/GenRec.lean`'s `classFeR_go_pop`, restated). -/
theorem gr_classFeR_go_pop (p : BlockShape) :
    ∀ (l : List (IConstantVal × Nat)) (m : Nat) (fe : IFEnv)
      (prevs : List (NIdx × Option (Nat × IConstantInfo))),
      ∃ news, (classFeR.go p m l fe prevs).2 = prevs ++ news ∧
        TFEq (news.foldr (fun (x : NIdx × Option (Nat × IConstantInfo)) acc =>
          acc.popTemp x.1 x.2) (classFeR.go p m l fe prevs).1) fe
  | [], m, fe, prevs => ⟨[], by simp [classFeR.go], TFEq.refl _⟩
  | (cv, c) :: rest, m, fe, prevs => by
    simp only [classFeR.go]
    obtain ⟨news, hn, hf⟩ := gr_classFeR_go_pop p rest (m + 1)
      (fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) []))
      (prevs ++ [(cv.name, fe.idx[cv.name]?)])
    refine ⟨(cv.name, fe.idx[cv.name]?) :: news, by rw [hn]; simp, ?_⟩
    simp only [List.foldr_cons]
    exact (hf.popTemp _ _).trans (TFEq.popTemp_push fe (.recInfo cv _ _ []))

theorem gr_usize_ext {a b : Std.Usize} (h : a.val = b.val) : a = b := by scalar_tac

theorem gr_fe_r_push_aux (p : arena.inductives.block_parts.BlockShape)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (rec_cls : alloc.vec.Vec Std.U64) :
    ∀ (q : Nat) (m : Std.Usize) (rf : arena.env.IFEnv) (lf : IFEnv)
      (prevs : alloc.vec.Vec (arena.handle.NIdx × Option (Std.U64 × Std.U64)))
      (prevsL : List (NIdx × Option (Nat × IConstantInfo))) rfK prevsK,
      min cv_gs.val.length rec_cls.val.length - m.val = q →
      IFEnvRelI rf lf →
      arena.inductives.gen_rec.class_fe_r_push p cv_gs rec_cls m rf prevs = ok (rfK, prevsK) →
      IFEnvRelI rfK (classFeR.go (absBlockShape p) m.val
          (((cv_gs.val.map absIConstantVal).zip (rec_cls.val.map absU)).drop m.val) lf prevsL).1 ∧
      (∃ Q, prevsK.val = prevs.val ++ Q ∧ Q.length = q) ∧
      (∀ rfX, RFEq rfX rfK → IdxInv rfX → ∀ (j : Std.Usize) out,
        j.val = prevs.val.length + q →
        arena.inductives.gen_rec.class_fe_r_pop rfX prevsK j = ok out →
        ∃ rfY, RFEq rfY rf ∧ IdxInv rfY ∧ ∀ (j' : Std.Usize), j'.val = prevs.val.length →
          arena.inductives.gen_rec.class_fe_r_pop rfY prevsK j' = ok out) := by
  intro q
  induction q with
  | zero =>
    intro m rf lf prevs prevsL rfK prevsK hq hfe h
    rw [arena.inductives.gen_rec.class_fe_r_push.eq_def] at h
    have hmin : m.val ≥ cv_gs.val.length ∨ m.val ≥ rec_cls.val.length := by omega
    have hrfK : rfK = rf ∧ prevsK = prevs := by
      by_cases h1 : m ≥ alloc.vec.Vec.len cv_gs
      · rw [if_pos h1] at h
        exact Prod.mk.inj (Result.ok_injective h).symm
      · rw [if_neg h1, if_pos (by scalar_tac)] at h
        exact Prod.mk.inj (Result.ok_injective h).symm
    obtain ⟨rfl, rfl⟩ := hrfK
    have hnil : ((cv_gs.val.map absIConstantVal).zip (rec_cls.val.map absU)).drop m.val = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    refine ⟨?_, ⟨[], by simp, rfl⟩, ?_⟩
    · rw [hnil]; simpa [classFeR.go] using hfe
    · intro rfX hX hXi j out hj hpop
      refine ⟨rfX, hX, hXi, fun j' hj' => ?_⟩
      rw [gr_usize_ext (show j'.val = j.val by omega)]; exact hpop
  | succ q ih =>
    intro m rf lf prevs prevsL rfK prevsK hq hfe h
    have hm1 : m.val < cv_gs.val.length := by omega
    have hm2 : m.val < rec_cls.val.length := by omega
    rw [arena.inductives.gen_rec.class_fe_r_push.eq_def,
      if_neg (show ¬ m ≥ alloc.vec.Vec.len cv_gs by scalar_tac),
      if_neg (show ¬ m ≥ alloc.vec.Vec.len rec_cls by scalar_tac)] at h
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hivx := vec_index_some hiv
    rw [List.getElem?_eq_getElem hm1, Option.some.injEq] at hivx
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv1, hiv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [pos_i_constant_val_dup_spec _ _ hiv1] at h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨pq, hpq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨prev, rf1⟩ := pq
    simp only [Aeneas.Std.uncurry_apply_pair] at h
    obtain ⟨prevs1, hprevs1, hA⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨m1, hm1', hB⟩ := ConRon.Refine.bind_eq_ok_iff.mp hA
    have hm1v : m1.val = m.val + 1 := absSz_add_one hm1'
    have hi2v : i2.val = m.val := by
      simp only [lift, Result.ok.injEq] at hi2; subst hi2
      exact ConRon.Refine.ExprOps.usize_cast_u64_val m
    have hi4v : i4.val = m.val := by
      simp only [lift, Result.ok.injEq] at hi4; subst hi4
      exact ConRon.Refine.ExprOps.usize_cast_u64_val m
    have hi3v := major_idx_at_twin p i2 i3 hi3
    have hi5v := rule_prefix_at_twin p i4 i5 hi5
    simp only [TwinEq] at hi3v hi5v
    -- the pushed constant
    obtain ⟨hpush, n', hn', -, -, -, -, -⟩ := gr_ifenv_push_temp_spec hfe.inv hpq
    have hnn : n' = n := by
      simp only [arena.env.i_constant_info_name] at hn'
      rw [dupId_nidx _ _ hn', dupId_nidx _ _ hn]
    subst hnn
    obtain ⟨hrel1, hinv1⟩ := ifenv_push_refines hfe.rel hfe.inv
      (show IConstantInfoWF (arena.env.IConstantInfo.RecInfo _ _ _ _) from trivial) hpush
    have hdrop : ((cv_gs.val.map absIConstantVal).zip (rec_cls.val.map absU)).drop m.val =
        (absIConstantVal iv, absU rec_cls.val[m.val]) ::
          ((cv_gs.val.map absIConstantVal).zip (rec_cls.val.map absU)).drop (m.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp [hivx]
    obtain ⟨ih1, ⟨Q, hQ, hQl⟩, ih3⟩ := ih m1 rf1 _ prevs1
      (prevsL ++ [((absIConstantVal iv).name, lf.idx[(absIConstantVal iv).name]?)]) rfK prevsK
      (by omega) ⟨hrel1, hinv1⟩ hB
    have hprevs1v := ConRon.Refine.vec_push_val hprevs1
    refine ⟨?_, ⟨(n', prev) :: Q, by rw [hQ, hprevs1v]; simp, by simp [hQl]⟩, ?_⟩
    · rw [hdrop]
      simp only [classFeR.go]
      rw [hm1v] at ih1
      have hrec : absIConstantInfo (arena.env.IConstantInfo.RecInfo iv i3 i5
          (alloc.vec.Vec.new arena.env.IRecRule)) =
          .recInfo (absIConstantVal iv) ((absBlockShape p).majorIdxAt m.val)
            ((absBlockShape p).rulePrefixAt m.val) [] := by
        simp only [absIConstantInfo, ← hi3v, ← hi5v, absU, hi2v, hi4v]
        rfl
      rw [hrec] at ih1
      exact ih1
    · intro rfX hX hXi j out hj hpop
      obtain ⟨rfY', hY', hYi', hpop'⟩ := ih3 rfX hX hXi j out
        (by rw [hj, hprevs1v]; simp; omega) hpop
      -- one more pop: the row this push displaced
      obtain ⟨jj, hjj⟩ : ∃ jj : Std.Usize, jj.val = prevs.val.length + 1 :=
        ⟨UScalar.ofNatCore (ty := .Usize) (prevs.val.length + 1) (by
          have := prevsK.property; rw [hQ, hprevs1v] at this; simp at this
          scalar_tac), UScalar.ofNatCore_val_eq _⟩
      have hp2 := hpop' jj (by rw [hjj, hprevs1v]; simp)
      rw [arena.inductives.gen_rec.class_fe_r_pop.eq_def, if_neg (by scalar_tac)] at hp2
      obtain ⟨i1, hi1, hp2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp2
      have hi1v := ConRon.Refine.Nat.usub_val hi1
      have hget : prevsK.val[i1.val]? = some (n', prev) := by
        rw [hQ, hprevs1v, show i1.val = prevs.val.length by simp at hi1v; omega]
        simp
      rw [gr_vec_index_eq hget, bind_tc_ok] at hp2
      obtain ⟨pv, hpv, hp2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp2
      have hpvv : pv = prev := by
        cases prev <;> simp only [Result.ok.injEq] at hpv <;> exact hpv.symm
      subst hpvv
      simp only [bind_tc_ok] at hp2
      obtain ⟨fe1, hfe1, hp2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hp2
      obtain ⟨hR1, hI1⟩ := gr_pop_push hfe.inv hpq (by
        simp only [arena.env.i_constant_info_name]; exact hn') hY' hYi' hfe1
      refine ⟨fe1, hR1, hI1, fun j' hj' => ?_⟩
      rw [gr_usize_ext (show j'.val = i1.val by simp at hi1v; omega)]
      exact hp2

/-- **The rule-less recursors pushed, and popped again**: the pushed index is
the twin's `classFeR`, and whatever the pops return is related to the twin's
`foldr popTemp` (any `f` that is the twin's pop lambda). -/
theorem class_fe_r_push_spec (p : arena.inductives.block_parts.BlockShape)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (rec_cls : alloc.vec.Vec Std.U64)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf)
    (f : NIdx × Option (Nat × IConstantInfo) → IFEnv → IFEnv)
    (hf : ∀ x acc, f x acc = acc.popTemp x.1 x.2) :
    LSP (arena.inductives.gen_rec.class_fe_r_push p cv_gs rec_cls 0#usize rf (alloc.vec.Vec.new _))
      (fun r => IFEnvRelI r.1 (classFeR (absBlockShape p) (cv_gs.val.map absIConstantVal)
          (rec_cls.val.map absU) lf).1 ∧
        ∀ (j : Std.Usize) out, j.val = r.2.val.length →
          arena.inductives.gen_rec.class_fe_r_pop r.1 r.2 j = ok out →
          IFEnvRelI out ((classFeR (absBlockShape p) (cv_gs.val.map absIConstantVal)
            (rec_cls.val.map absU) lf).2.foldr f
            (classFeR (absBlockShape p) (cv_gs.val.map absIConstantVal)
              (rec_cls.val.map absU) lf).1)) := by
  intro r hr
  obtain ⟨rfK, prevsK⟩ := r
  obtain ⟨h1, ⟨Q, hQ, hQl⟩, h3⟩ := gr_fe_r_push_aux p cv_gs rec_cls _ 0#usize rf lf
    (alloc.vec.Vec.new _) [] rfK prevsK rfl hfe hr
  simp only [gr_usz0, List.drop_zero] at h1
  refine ⟨h1, fun j out hj hpop => ?_⟩
  obtain ⟨rfY, hY, hYi, hpopY⟩ := h3 rfK (RFEq.refl _) h1.inv.1 j out
    (by rw [hj, hQ]; simp [alloc.vec.Vec.new, hQl]) hpop
  have hout := hpopY 0#usize (by simp [alloc.vec.Vec.new])
  rw [arena.inductives.gen_rec.class_fe_r_pop.eq_def, if_pos rfl, Result.ok.injEq] at hout
  subst hout
  obtain ⟨news, hn, hT⟩ := gr_classFeR_go_pop (absBlockShape p)
    ((cv_gs.val.map absIConstantVal).zip (rec_cls.val.map absU)) 0 lf []
  have hfeq : f = fun (x : NIdx × Option (Nat × IConstantInfo)) acc => acc.popTemp x.1 x.2 := by
    funext x acc; exact hf x acc
  refine IFEnvRelI.transfer hfe hY hYi ?_
  simp only [classFeR]
  rw [hn, List.nil_append, hfeq]
  exact hT

/-! ## `gen_rec_check` (with `gen_rec_classes` and `gen_rec_generate` inline) -/


/-- The pop lambda, named (the twin's `fun (n, prev) acc => acc.popTemp n prev`). -/
def grPop (x : NIdx × Option (Nat × IConstantInfo)) (acc : IFEnv) : IFEnv :=
  acc.popTemp x.1 x.2

theorem class_fe_r_push_ls (p : arena.inductives.block_parts.BlockShape)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (rec_cls : alloc.vec.Vec Std.U64)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) :
    LSP (arena.inductives.gen_rec.class_fe_r_push p cv_gs rec_cls 0#usize rf (alloc.vec.Vec.new _))
      (fun r => IFEnvRelI r.1 (classFeR (absBlockShape p) (cv_gs.val.map absIConstantVal)
          (rec_cls.val.map absU) lf).1 ∧
        ∀ (j : Std.Usize) out, j.val = r.2.val.length →
          arena.inductives.gen_rec.class_fe_r_pop r.1 r.2 j = ok out →
          IFEnvRelI out ((classFeR (absBlockShape p) (cv_gs.val.map absIConstantVal)
            (rec_cls.val.map absU) lf).2.foldr grPop
            (classFeR (absBlockShape p) (cv_gs.val.map absIConstantVal)
              (rec_cls.val.map absU) lf).1)) :=
  class_fe_r_push_spec p cv_gs rec_cls hfe grPop (fun _ _ => rfl)

attribute [local lockstep] class_fe_r_push_ls
attribute [local lockstep_inline] arena.inductives.gen_rec.gen_rec_classes
  arena.inductives.gen_rec.gen_rec_generate

namespace GenRecSide

/-- The stage's side alternatives: a generator record's `ClassGenWF`. -/
scoped macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (refine ⟨?_, ?_⟩ <;> first
      | assumption
      | exact TeleWF.new
      | exact OptTeleWF.get (by assumption)
      | (simp only at *; assumption)))

end GenRecSide

set_option maxHeartbeats 4000000 in
/-- `gen_rec_check` ⊑ `genRecCheck` — the export the block tail reads: the
index handed back related to the twin's popped one, the rules alike. -/
@[lockstep] theorem gen_rec_check_ls {pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hfe : IFEnvRelI rf lf)
    (p : arena.inductives.block_parts.BlockShape) (nested_bit : Bool)
    (params : alloc.vec.Vec arena.handle.EIdx)
    (tbl : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (rd : arena.inductives.class_read.ClassRead)
    (ms : alloc.vec.Vec arena.inductives.rec_check.TargetMajor)
    (cv_tas : alloc.vec.Vec arena.env.IConstantVal)
    (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LS pers (fun a b => IFEnvRelI a.1 b.1 ∧ b.2 = absRuleOutL a.2)
      (arena.inductives.gen_rec.gen_rec_check pers st mode rf p nested_bit params tbl rd ms
        cv_tas block) lst
      (genRecCheck (ConRon.Refine.absMode mode) lf (absBlockShape p) nested_bit (absEIdxL params)
        (tbl.val.map absNestCtorNf) (absClassRead rd) (ms.val.map absTargetMajor)
        (cv_tas.val.map absIConstantVal) (block.val.map absIConstantInfo)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.gen_rec.gen_rec_check, genRecCheck]
  lockstep
  all_goals
    obtain ⟨hR, hpop⟩ := hP
    simp only at hR hpop
    have hvr := hR.rel.visibleBelow.symm
    lockstep
    refine LS.pure ⟨?_, rfl⟩ ‹_› ‹_›
    exact hpop _ _ (by simp [alloc.vec.Vec.len]) hf

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.gen_rec_check_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gen_rec_check_ls

/-- info: 'ConRon.Refine2.check_block_classes_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_block_classes_ls

/-- info: 'ConRon.Refine2.class_keys_of_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_keys_of_ls

/-- info: 'ConRon.Refine2.class_ctors_of_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_ctors_of_ls

/-- info: 'ConRon.Refine2.class_seeds_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_seeds_ls

/-- info: 'ConRon.Refine2.class_fe_r_push_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_fe_r_push_spec

/-- info: 'ConRon.Refine2.class_recs_rules_ok_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms class_recs_rules_ok_ls

end ConRon.Refine2
