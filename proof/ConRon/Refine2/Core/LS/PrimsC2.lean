/-
# `ConRon.Refine2.Core.LS.PrimsC2` — region C2's primitive pairs

Task #97-P5-Core round 5, region C2 (the stuck-major rescue `majorToCtor`, the
literal conversions, `prepareMajor`, the ι step `iotaRec`/`iotaRecAt` and the
projection certificate `projCert`/`projCertAt`).  The `@[lockstep]` pairs
those bodies step through that no earlier file supplies:

* the typed store projections `view_const`, `view_lit`, `view_ls`,
  `view_ls_len` over `AStateRel₀`;
* the pin `pin_and`, the handle `eq2`, the record copies (`i_*_dup`) as
  `TwinEq` facts, the mode bits;
* the state-free vector helpers (`take_eidx`, `take_eidx_n`, `drop_eidx_n`,
  `snoc_eidx`, `snoc2_eidx_of`, `append_eidx`, `append_eidx_of`,
  `get_d_eidx`) as `LSP` facts about the lists they denote;

Several of these are the same statements regions A2 and C1 add in their own
files (`PA2.nidx_eq2_ls`, `PC1.certs_ls` …); the coordinator deduplicates at
merge.
-/
import ConRon.Refine2.Core.LS.Prims
import ConRon.Refine.CoreKShapes

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PC2

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## Abstraction bridges -/

@[lockstep_simp] theorem exprOps_absEIdxList_eq (v : alloc.vec.Vec arena.handle.EIdx) :
    ExprOps.absEIdxList v = absEIdxList v := rfl

@[lockstep_simp] theorem absEIdxL_eq (v : alloc.vec.Vec arena.handle.EIdx) :
    ExprOps.absEIdxL v = absEIdxList v := rfl

@[lockstep_simp] theorem absEIdxListFrom_zero (v : alloc.vec.Vec arena.handle.EIdx) :
    absEIdxListFrom v 0#usize = absEIdxList v := by
  simp [absEIdxListFrom, absEIdxList]

attribute [lockstep_simp] absConstT

/-! ## Rust-only steps: the mode bits, handle comparisons, record copies -/

@[lockstep] theorem certs_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.certs m) (fun b => b = (ConRon.Refine.absMode m).certs) := by
  intro b h
  cases m <;> (simp only [kernel.env.certs, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem beta_gate_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.beta_gate m) (fun b => b = (ConRon.Refine.absMode m).betaGate) := by
  intro b h
  cases m <;> (simp only [kernel.env.beta_gate, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = decide (absNIdx a = absNIdx b)) := by
  intro o h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

@[lockstep] theorem dup2_nidx_ls (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun _ he => dupId_nidx _ _ he

@[lockstep] theorem dup2_lsidx_ls (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun _ he => dupId_lsidx _ _ he

theorem vec_eq_of_val {α : Type} {a b : alloc.vec.Vec α} (h : a.val = b.val) : a = b :=
  alloc.vec.Vec.ext _ _ h

/-- `i_constant_val_dup` is the identity (three `dup2`s and `nidx_vec_dup`). -/
theorem i_constant_val_dup_id {cv o : arena.env.IConstantVal}
    (h : arena.env.i_constant_val_dup cv = ok o) : o = cv := by
  rw [arena.env.i_constant_val_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    vec_eq_of_val (nidx_vec_dup_val hv)]

@[lockstep] theorem i_constant_val_dup_ls (cv : arena.env.IConstantVal) :
    LSP (arena.env.i_constant_val_dup cv) (fun o => o = cv) :=
  fun _ h => i_constant_val_dup_id h

@[lockstep] theorem i_ind_caps_dup_ls (c : arena.env.IIndCaps) :
    LSP (arena.env.i_ind_caps_dup c) (fun o => o = c) := by
  intro o h
  rw [arena.env.i_ind_caps_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, dupId_nidx _ _ hn, ConRon.Refine.PropWhen.dup_eq hpw]

theorem i_rec_rule_fire_dup_id {f o : arena.env.IRecRuleFire}
    (h : arena.env.i_rec_rule_fire_dup f = ok o) : o = f := by
  rw [arena.env.i_rec_rule_fire_dup.eq_def] at h
  cases f with
  | Inert => rw [Result.ok_injective h]
  | Plain => rw [Result.ok_injective h]
  | Nested lvls pins =>
    simp only [] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have e1 : v = lvls :=
      vec_eq_of_val (lidx_vec_dup_eq (by rw [arena.env.lidx_vec_dup] at hv; exact hv))
    have e2 : v1 = pins := vec_eq_of_val (eidx_vec_dup_val hv1)
    rw [← Result.ok_injective h, e1, e2]

theorem i_rec_rule_dup_id {r o : arena.env.IRecRule}
    (h : arena.env.i_rec_rule_dup r = ok o) : o = r := by
  rw [arena.env.i_rec_rule_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨irf, hirf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    i_rec_rule_fire_dup_id hirf]

@[lockstep] theorem i_rec_rule_dup_ls (r : arena.env.IRecRule) :
    LSP (arena.env.i_rec_rule_dup r) (fun o => o = r) :=
  fun _ h => i_rec_rule_dup_id h

theorem i_rec_rules_dup_from_id {rs : alloc.vec.Vec arena.env.IRecRule} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IRecRule),
      arena.env.i_rec_rules_dup_from rs i out = ok o →
      o.val.map id = out.val.map id ++ (rs.val.drop i.val).map id := by
  refine vec_cursor_copy rs id id (arena.env.i_rec_rules_dup_from rs) ?_ ?_
  · intro i out o hn h
    rw [arena.env.i_rec_rules_dup_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < rs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.env.i_rec_rules_dup_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ir1, hir1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : ir = x := by
      have h1 := vec_index_some hir; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    exact ⟨i2, ir1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [← hex, i_rec_rule_dup_id hir1], h⟩

@[lockstep] theorem i_rec_rules_dup_ls (rs : alloc.vec.Vec arena.env.IRecRule) :
    LSP (arena.env.i_rec_rules_dup rs) (fun o => o = rs) := by
  intro r h
  rw [arena.env.i_rec_rules_dup] at h
  have h2 := i_rec_rules_dup_from_id 0#usize _ r h
  apply vec_eq_of_val
  simpa [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

@[lockstep] theorem arc_deref_ls {T : Type} (A : Type) (x : T) :
    LSP (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x) (fun y => y = x) := by
  intro y h; cases Result.ok_injective h; rfl

@[lockstep] theorem str_copy_ls (s : alloc.vec.Vec Std.U32) :
    LSP (kernel.expr.str_copy s) (fun r => r = s) :=
  fun _ h => ConRon.Refine.Expr.str_copy_eq h

/-- `usize as u64`: a widening, so the value is kept. -/
@[lockstep] theorem cast_u64_usize_ls (i : Std.Usize) :
    LSP (lift (UScalar.cast .U64 i)) (fun r : Std.U64 => r.val = i.val) := by
  intro r h
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have := i.hBounds
  simp only [UScalarTy.numBits] at this ⊢
  cases System.Platform.numBits_eq with
  | inl h => rw [h] at this; omega
  | inr h => rw [h] at this; omega

@[lockstep] theorem fail_dangling_ls_spec (T : Type) :
    LSP (arena.monad.fail_dangling_ls T) (fun r => ∃ v, r = .Err (.Internal v)) := by
  intro r h
  rw [arena.monad.fail_dangling_ls] at h
  obtain ⟨s, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨v, fail_run h⟩

/-! ## The state-free vector helpers -/

theorem drop_eidx_from_aux (n : Nat) :
    ∀ (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize)
      (out r : alloc.vec.Vec arena.handle.EIdx),
      xs.val.length - k.val = n → arena.core.drop_eidx_from xs k out = ok r →
      r.val = out.val ++ xs.val.drop k.val := by
  induction n with
  | zero =>
    intro xs k out r hn h
    rw [arena.core.drop_eidx_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ m ih =>
    intro xs k out r hn h
    rw [arena.core.drop_eidx_from] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
    have hd := dupId_eidx _ _ he1
    have hp := ConRon.Refine.vec_push_val ho1
    have hk := ConRon.Refine.Nat.uadd_val hk1
    rw [ih xs k1 o1 r (by simp at hk; omega) h, hp, hd, ← hx, hk]
    rw [List.drop_eq_getElem_cons hb, List.append_assoc]; rfl

theorem drop_eidx_n_from_aux (m : Nat) :
    ∀ (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (i : Std.Usize)
      (r : alloc.vec.Vec arena.handle.EIdx),
      n.val = m → arena.core.drop_eidx_n_from xs n i = ok r →
      r.val = xs.val.drop (i.val + n.val) := by
  induction m with
  | zero =>
    intro xs n i r hn h
    rw [arena.core.drop_eidx_n_from] at h
    rw [if_pos (by scalar_tac)] at h
    rw [drop_eidx_from_aux _ xs i _ r rfl h, hn]; simp
  | succ m ih =>
    intro xs n i r hn h
    rw [arena.core.drop_eidx_n_from] at h
    rw [if_neg (by scalar_tac)] at h
    dsimp only at h
    split at h
    · cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h1 := ConRon.Refine.Nat.usub_val hn1
      have h2 := ConRon.Refine.Nat.uadd_val hi1
      rw [ih xs n1 i1 r (by simp at h1; omega) h]
      congr 1; simp at h1 h2; omega

@[lockstep] theorem drop_eidx_n_ls (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.core.drop_eidx_n xs n)
      (fun r => TwinEq ((absEIdxList xs).drop n.val) (absEIdxList r)) := by
  intro r h
  rw [arena.core.drop_eidx_n] at h
  have := drop_eidx_n_from_aux _ xs n 0#usize r rfl h
  show _ = _
  simp only [absEIdxList, this, List.map_drop]
  simp

/-- The whole of `xs`, copied onto `out`. -/
theorem eidx_copy_upto_all {xs out r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.eidx_copy_upto xs (alloc.vec.Vec.len xs) 0#usize out = ok r) :
    absEIdxList r = absEIdxList out ++ absEIdxList xs := by
  have hc := ExprOps.eidx_copy_upto_refines h
  rw [ExprOps.absEIdxArr_size_len xs, ExprOps.usize_zero_val, ExprOps.eidxCopyUpto_all] at hc
  have := hc.symm
  simpa [ExprOps.absEIdxArr, ExprOps.absEIdxL, absEIdxList] using this

theorem append_eidx_from_aux (n : Nat) :
    ∀ (xs ys : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
      (r : alloc.vec.Vec arena.handle.EIdx),
      ys.val.length - i.val = n → arena.core.append_eidx_from xs ys i = ok r →
      r.val = xs.val ++ ys.val.drop i.val := by
  induction n with
  | zero =>
    intro xs ys i r hn h
    rw [arena.core.append_eidx_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ m ih =>
    intro xs ys i r hn h
    rw [arena.core.append_eidx_from] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
    have hd := dupId_eidx _ _ he1
    have hp := ConRon.Refine.vec_push_val ho1
    have hk := ConRon.Refine.Nat.uadd_val hk1
    rw [ih o1 ys k1 r (by simp at hk; omega) h, hp, hd, ← hx, hk]
    rw [List.drop_eq_getElem_cons hb, List.append_assoc]; rfl

theorem append_eidx_from_abs {xs ys r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.core.append_eidx_from xs ys 0#usize = ok r) :
    absEIdxList r = absEIdxList xs ++ absEIdxList ys := by
  have := append_eidx_from_aux _ xs ys 0#usize r rfl h
  simp [absEIdxList, this]

@[lockstep] theorem append_eidx_ls (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.append_eidx xs ys)
      (fun r => TwinEq (absEIdxList xs ++ absEIdxList ys) (absEIdxList r)) := by
  intro r h
  rw [arena.core.append_eidx] at h
  exact (append_eidx_from_abs h).symm

@[lockstep] theorem append_eidx_of_ls (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.append_eidx_of xs ys)
      (fun r => TwinEq (absEIdxList xs ++ absEIdxList ys) (absEIdxList r)) := by
  intro r h
  rw [arena.core.append_eidx_of] at h
  obtain ⟨i2, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out2, hout2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := eidx_copy_upto_all hout2
  show _ = _
  rw [append_eidx_from_abs h, h1]
  simp [absEIdxList, alloc.vec.Vec.with_capacity]

@[lockstep] theorem snoc_eidx_ls (xs : alloc.vec.Vec arena.handle.EIdx) (y : arena.handle.EIdx) :
    LSP (arena.core.snoc_eidx xs y)
      (fun r => TwinEq (absEIdxList xs ++ [absEIdx y]) (absEIdxList r)) := by
  intro r h
  rw [arena.core.snoc_eidx] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hp := ConRon.Refine.vec_push_val h
  show _ = _
  simp [absEIdxList, hp, dupId_eidx _ _ he]

@[lockstep] theorem snoc2_eidx_of_ls (xs : alloc.vec.Vec arena.handle.EIdx)
    (y z : arena.handle.EIdx) :
    LSP (arena.core.snoc2_eidx_of xs y z)
      (fun r => TwinEq (absEIdxList xs ++ [absEIdx y, absEIdx z]) (absEIdxList r)) := by
  intro r h
  rw [arena.core.snoc2_eidx_of] at h
  obtain ⟨i1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out2, hout2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := eidx_copy_upto_all hout1
  have hp2 := ConRon.Refine.vec_push_val hout2
  have hp := ConRon.Refine.vec_push_val h
  show _ = _
  simp only [absEIdxList] at h1 ⊢
  rw [hp, hp2, dupId_eidx _ _ he, dupId_eidx _ _ he1]
  simp only [List.map_append, h1]
  simp [alloc.vec.Vec.with_capacity]

theorem take_eidx_n_from_aux (m : Nat) :
    ∀ (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (i : Std.Usize)
      (out r : alloc.vec.Vec arena.handle.EIdx),
      xs.val.length - i.val = m → arena.expr_ops.take_eidx_n_from xs n i out = ok r →
      r.val = out.val ++ (xs.val.drop i.val).take n.val := by
  induction m with
  | zero =>
    intro xs n i out r hn h
    rw [arena.expr_ops.take_eidx_n_from] at h
    split at h
    · cases Result.ok_injective h; rw [List.drop_eq_nil_of_le (by omega)]; simp
    · rw [if_pos (by scalar_tac)] at h
      cases Result.ok_injective h; rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ m ih =>
    intro xs n i out r hn h
    rw [arena.expr_ops.take_eidx_n_from] at h
    split at h
    · rename_i hn0
      cases Result.ok_injective h; subst hn0; simp
    · rename_i hn0
      rw [if_neg (by scalar_tac)] at h
      obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
      have hd := dupId_eidx _ _ he1
      have hp := ConRon.Refine.vec_push_val ho1
      have hk := ConRon.Refine.Nat.uadd_val hk1
      have hn1v := ConRon.Refine.Nat.usub_val hn1
      have hnpos : n.val ≠ 0 := by intro hc; apply hn0; scalar_tac
      rw [ih xs n1 k1 o1 r (by simp at hk; omega) h, hp, hd, ← hx, hk]
      rw [List.drop_eq_getElem_cons hb]
      obtain ⟨j, hj⟩ : ∃ j, n.val = j + 1 := ⟨n.val - 1, by omega⟩
      rw [hj, List.take_succ_cons, List.append_assoc]
      simp only [u64_one_val] at hn1v
      rw [show n1.val = j by omega]
      rfl

@[lockstep] theorem take_eidx_n_ls (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.expr_ops.take_eidx_n xs n)
      (fun r => TwinEq ((absEIdxList xs).take n.val) (absEIdxList r)) := by
  intro r h
  rw [arena.expr_ops.take_eidx_n] at h
  have := take_eidx_n_from_aux _ xs n 0#usize _ r rfl h
  show _ = _
  simp [absEIdxList, this, List.map_take]

theorem takeEidx_toList' (xs : Array EIdx) (k : Nat) :
    (takeEidx xs k).toList = xs.toList.take k := by
  rw [takeEidx, ExprOps.eidxCopyUpto_toList xs k k 0 #[] (by omega)]
  simp

@[lockstep_simp] theorem takeEidx_toList_eq (xs : alloc.vec.Vec arena.handle.EIdx) (k : Nat) :
    (takeEidx (absEIdxArr xs) k).toList = (absEIdxList xs).take k := by
  rw [takeEidx_toList']; simp [absEIdxArr, absEIdxList]

/-- `take_eidx` at a `usize` count: the twin's `List.take` (its `takeEidx` of
the push-order array is normalised to that by `takeEidx_toList_eq`). -/
@[lockstep] theorem take_eidx_ls (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize) :
    LSP (arena.expr_ops.take_eidx xs k)
      (fun r => TwinEq ((absEIdxList xs).take k.val) (absEIdxList r)) := by
  intro r h
  have h1 := ExprOps.take_eidx_refines h
  show _ = _
  rw [← takeEidx_toList_eq]; exact h1

/-- The value of a `u64 as usize` cast, when the `u64` fits.  Irreducible, so
that `apply` does not see the implication as more premises. -/
@[irreducible] def CastFits (x : Std.U64) (r : Std.Usize) : Prop :=
  x.val ≤ Usize.max → r.val = x.val

theorem CastFits.val {x : Std.U64} {r : Std.Usize} (h : CastFits x r) (hx : x.val ≤ Usize.max) :
    r.val = x.val := by
  unfold CastFits at h; exact h hx

/-- `x as usize` from a `u64`: the value, when it fits. -/
@[lockstep] theorem cast_usize_u64_ls (x : Std.U64) :
    LSP (lift (UScalar.cast .Usize x)) (fun r : Std.Usize => CastFits x r) := by
  intro r h
  unfold CastFits
  intro hx
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have h2 : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
    simp [Usize.max, Usize.numBits]
  have h3 : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  omega

/-- `args.getD i dflt`. -/
@[lockstep] theorem get_d_eidx_ls (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64)
    (d : arena.handle.EIdx) :
    LSP (arena.core.get_d_eidx xs i d)
      (fun r => TwinEq ((absEIdxList xs).getD i.val (absEIdx d)) (absEIdx r)) := by
  intro r h
  rw [arena.core.get_d_eidx] at h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi2v := (cast_u64_usize_ls _) i2 hi2
  show _ = _
  split at h
  · rename_i hlt
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [lift, Result.ok.injEq] at hi3
    subst hi3
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
    have hc : (UScalar.cast .Usize i).val = i.val := by
      rw [UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      have : i.val < xs.val.length := by scalar_tac
      have := alloc.vec.Vec.len_val xs
      scalar_tac
    rw [dupId_eidx _ _ h]
    have hs := List.getElem?_eq_getElem hb
    rw [hx] at hs
    simp only [hc] at hs
    simp only [absEIdxList, List.getD_eq_getElem?_getD, List.getElem?_map, hs]
    rfl
  · rename_i hge
    rw [dupId_eidx _ _ h]
    simp only [absEIdxList, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_none (by simp at hge; scalar_tac)]
    rfl

/-! ## The typed store projections -/

theorem etables_get_lit_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o : Option kernel.expr.Literal}
    (h : arena.store.ETables.get_lit rt i = ok o) :
    lt.getLit (absEIdx i) = o.map ConRon.Refine.absLiteral := by
  rw [arena.store.ETables.get_lit] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.lits hp
  rw [ETables.getLit, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    cases Result.ok_injective h
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.literal_dup_eq hx]
    rfl

theorem estore_view_lit_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o : Option kernel.expr.Literal}
    (h : arena.store.EStore.view_lit rs pers i = ok o) :
    ls.viewLit (absEIdx i) = o.map ConRon.Refine.absLiteral := by
  rw [arena.store.EStore.view_lit] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewLit]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetLit]
    rw [arena.store.EStore.pers_get_lit] at h
    have h3 : arena.store.ETables.get_lit (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_lit_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_lit_abs hrel.scrt h
    · rw [if_neg hs]
      cases Result.ok_injective h
      rfl

@[lockstep] theorem view_lit_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map ConRon.Refine.absLiteral a)
      (arena.monad.view_lit pers st h) st lst (Arena.viewLit (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewLit (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_lit] at hr; exact estore_view_lit_abs hrel.store hr)
    hrel hinv

@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a)
      (arena.monad.view_const pers st h) st lst (Arena.viewConst (absEIdx h)) := by
  intro o hrun
  exact ⟨_, lst, view_const_run₀ hrel hrun, rfl, hrel, hinv⟩

@[lockstep] theorem view_ls_len_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LSV pers (fun a b => b = Option.map absSz a)
      (arena.monad.view_ls_len pers st h) st lst (Arena.viewLsLen (absLsIdx h)) := by
  intro o hrun
  exact ⟨_, lst, view_ls_len_run₀ hrel hrun, rfl, hrel, hinv⟩

@[lockstep] theorem view_ls_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LSR pers (fun a b => b = absLsNodeView a)
      (arena.monad.view_ls pers st h) st lst (Arena.viewLs (absLsIdx h)) := by
  intro o hrun
  rw [arena.monad.view_ls] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ls_s] at hn
  have hn2 : n = st.store.lss := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hview := lsstore_view_abs hrel.store.lss hv
  have hrunl : (Arena.viewLs (absLsIdx h)).run lst
      = match lst.store.lss.view (absLsIdx h) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling level-list handle") := by
    show (match lst.store.lss.view (absLsIdx h) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling level-list handle")).run lst = _
    cases lst.store.lss.view (absLsIdx h) <;> rfl
  cases hvc : v with
  | none =>
    rw [hvc] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho := fail_run hrun
    subst ho
    rw [hvc] at hview
    show AErrSim _ _
    rw [hrunl, hview]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hrun
    have ho := Result.ok_injective hrun
    subst ho
    rw [hvc] at hview
    refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
    rw [hrunl, hview]
    rfl

@[lockstep] theorem pin_and_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_and st) st lst pinAnd := by
  intro o hrun
  rw [arena.pins.pin_and, arena.pins.pin_at] at hrun
  have hc : absSz arena.pins.PIN_AND = Arena.PIN_AND := by
    show (arena.pins.PIN_AND).val = _
    rw [arena.pins.PIN_AND]
    rfl
  show LOut pers _ o st ((Arena.pinAt Arena.PIN_AND).run lst)
  rw [← hc]
  generalize arena.pins.PIN_AND = i at hrun
  have hnames := hrel.pins.names
  have hlen : lst.pins.names.size = st.pins.names.val.length := by
    have h := congrArg List.length hnames
    simpa using h
  have hrun2 : (Arena.pinAt (absSz i)).run lst
      = (if h : absSz i < lst.pins.names.size
         then Except.ok (lst.pins.names[absSz i], lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : absSz i < lst.pins.names.size
    · rw [dif_pos h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos h]
    · rw [dif_neg h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, dif_neg h,
        Arena.fail, throwThe, MonadExceptOf.throw,
        Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hge =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 : core.result.Result.Err (T := arena.handle.NIdx)
        (kernel.core_types.CheckError.Internal cps) = o := Result.ok_injective hrun
    subst h2
    have hnl : ¬ (absSz i < lst.pins.names.size) := by
      rw [hlen]
      have hle : st.pins.names.val.length ≤ i.val := by scalar_tac
      show ¬ (i.val < st.pins.names.val.length)
      omega
    exact AErrSim.internal (s := "arena: reserved-name pins not interned")
      (by rw [hrun2, dif_neg hnl])
  case isFalse hlt =>
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : core.result.Result.Ok n1 = o := Result.ok_injective hrun
    subst h2
    rw [dupId_nidx _ _ hn1]
    obtain ⟨hlt2, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn
    have hlt3 : absSz i < lst.pins.names.size := by rw [hlen]; exact hlt2
    refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
    rw [hrun2, dif_pos hlt3]
    have hi : lst.pins.names.toList[absSz i]? =
        (st.pins.names.val.map absNIdx)[absSz i]? := by rw [hnames]
    simp only [List.getElem?_map, Array.getElem?_toList] at hi
    have hsome : lst.pins.names[absSz i]? = some (absNIdx st.pins.names.val[absSz i]) := by
      simpa [hlt2] using hi
    rw [Array.getElem?_eq_getElem hlt3] at hsome
    rw [Option.some_inj.mp hsome]

/-! ## The projection-function shape test -/

@[lockstep] theorem name_is_proj_fn_shape_ls {n : kernel.name.Name} (hn : ConRon.Refine.NameWF n) :
    LSP (kernel.level.name_is_proj_fn_shape n)
      (fun b => b = ConLeche.Name.isProjFnShape (ConRon.Refine.absName n)) :=
  fun _ h => ConRon.Refine.CoreK.name_is_proj_fn_shape_refines hn h

@[lockstep] theorem i_rec_rule_compare_params_ls (rl : arena.env.IRecRule) :
    LSP (arena.env.i_rec_rule_compare_params rl) (fun b => b = (absIRecRule rl).compareParams) := by
  intro b h
  rw [arena.env.i_rec_rule_compare_params] at h
  cases hf : rl.fire <;> rw [hf] at h <;> cases Result.ok_injective h <;>
    simp [IRecRule.compareParams, absIRecRule, absIRecRuleFire, hf]

end ConRon.Refine2.Lockstep.PC2
