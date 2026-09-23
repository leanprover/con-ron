/-
# `ConRon.Refine2.Core.LS.PrimsC1` — region C1's primitive pairs

Task #97-P5-Core round 5, region C1 (the certificates: `iotaCerts`,
`defEqList`, `iotaIndexOk`, `proofIrrel`, `propIrrel`, the structure-eta and
unit certificates, `etaCert`, `stuckIrrel`).  The `@[lockstep]` pairs those
bodies step through that no earlier file supplies: Rust-only mode gates, the
state-free vector helpers, and the store reads.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PC1

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## Bridges between the two `Vec<EIdx>` readings -/

@[lockstep_simp] theorem exprOps_absEIdxList_eq (v : alloc.vec.Vec arena.handle.EIdx) :
    ExprOps.absEIdxList v = absEIdxList v := rfl

@[lockstep_simp] theorem absEIdxListFrom_zero (v : alloc.vec.Vec arena.handle.EIdx) :
    absEIdxListFrom v 0#usize = absEIdxList v := by
  simp [absEIdxListFrom, absEIdxList]

/-! ## `drop_eidx_from` / `drop_eidx_n_from` / `drop_eidx_n` (the twin's `List.drop`) -/

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

@[lockstep] theorem drop_eidx_from_ls (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize)
    (out : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.drop_eidx_from xs k out)
      (fun r => r.val = out.val ++ xs.val.drop k.val) :=
  fun r h => drop_eidx_from_aux _ xs k out r rfl h

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
      (fun r => absEIdxList r = (absEIdxList xs).drop (absU n)) := by
  intro r h
  rw [arena.core.drop_eidx_n] at h
  have := drop_eidx_n_from_aux _ xs n 0#usize r rfl h
  simp only [absEIdxList, this, List.map_drop, absU]
  simp

/-! ## The vector helpers (`take_eidx_n`, `append_eidx*`, `snoc*`) -/

theorem take_eidx_n_from_aux (m : Nat) :
    ∀ (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (i : Std.Usize)
      (out r : alloc.vec.Vec arena.handle.EIdx),
      n.val = m → arena.expr_ops.take_eidx_n_from xs n i out = ok r →
      r.val = out.val ++ (xs.val.drop i.val).take n.val := by
  induction m with
  | zero =>
    intro xs n i out r hn h
    rw [arena.expr_ops.take_eidx_n_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [hn]; simp
  | succ m ih =>
    intro xs n i out r hn h
    rw [arena.expr_ops.take_eidx_n_from] at h
    rw [if_neg (by scalar_tac)] at h
    dsimp only at h
    split at h
    · cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
    · rename_i hlt
      obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
      have hd := dupId_eidx _ _ he1
      have hp := ConRon.Refine.vec_push_val ho1
      have h1 := ConRon.Refine.Nat.usub_val hn1
      have h2 := ConRon.Refine.Nat.uadd_val hi1
      rw [ih xs n1 i1 o1 r (by simp at h1; omega) h, hp, hd, ← hx]
      rw [List.drop_eq_getElem_cons hb, show n.val = n1.val + 1 by simp at h1; omega,
        List.take_succ_cons, show i1.val = i.val + 1 by simpa using h2]
      simp

@[lockstep] theorem take_eidx_n_ls (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.expr_ops.take_eidx_n xs n)
      (fun r => absEIdxList r = (absEIdxList xs).take (absU n)) := by
  intro r h
  rw [arena.expr_ops.take_eidx_n] at h
  have := take_eidx_n_from_aux _ xs n 0#usize _ r rfl h
  simp only [absEIdxList, this, absU]
  simp [alloc.vec.Vec.new]

theorem append_eidx_from_aux (k : Nat) :
    ∀ (xs ys : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) (r : alloc.vec.Vec arena.handle.EIdx),
      ys.val.length - i.val = k → arena.core.append_eidx_from xs ys i = ok r →
      r.val = xs.val ++ ys.val.drop i.val := by
  induction k with
  | zero =>
    intro xs ys i r hk h
    rw [arena.core.append_eidx_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ k ih =>
    intro xs ys i r hk h
    rw [arena.core.append_eidx_from] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
    have hd := dupId_eidx _ _ he1
    have hp := ConRon.Refine.vec_push_val ho1
    have h2 := ConRon.Refine.Nat.uadd_val hi1
    rw [ih o1 ys i1 r (by simp at h2; omega) h, hp, hd, ← hx,
      show i1.val = i.val + 1 by simpa using h2, List.drop_eq_getElem_cons hb]
    simp

@[lockstep] theorem append_eidx_from_ls (xs ys : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LSP (arena.core.append_eidx_from xs ys i) (fun r => r.val = xs.val ++ ys.val.drop i.val) :=
  fun r h => append_eidx_from_aux _ xs ys i r rfl h

@[lockstep] theorem append_eidx_ls (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.append_eidx xs ys)
      (fun r => absEIdxList r = absEIdxList xs ++ absEIdxList ys) := by
  intro r h
  rw [arena.core.append_eidx] at h
  have := append_eidx_from_aux _ xs ys 0#usize r rfl h
  simp [absEIdxList, this]

/-- The whole-vector copy `eidx_copy_upto xs (len xs) 0 out` at an empty `out`. -/
theorem eidx_copy_all_map {xs : alloc.vec.Vec arena.handle.EIdx} {n : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.eidx_copy_upto xs (alloc.vec.Vec.len xs) 0#usize
      (alloc.vec.Vec.with_capacity arena.handle.EIdx n) = ok out) :
    out.val.map absEIdx = xs.val.map absEIdx := by
  have hc := ExprOps.eidx_copy_upto_refines h
  rw [ExprOps.absEIdxArr_size_len xs, ExprOps.usize_zero_val, ExprOps.absEIdxArr_with_capacity,
    ExprOps.eidxCopyUpto_all] at hc
  simpa [ExprOps.absEIdxArr, ExprOps.absEIdxL] using hc.symm

@[lockstep] theorem append_eidx_of_ls (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.append_eidx_of xs ys)
      (fun r => absEIdxList r = absEIdxList xs ++ absEIdxList ys) := by
  intro r h
  rw [arena.core.append_eidx_of] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨o2, ho2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hc := eidx_copy_all_map ho2
  have := append_eidx_from_aux _ o2 ys 0#usize r rfl h
  simp [absEIdxList, this, hc]

@[lockstep] theorem snoc2_eidx_of_ls (xs : alloc.vec.Vec arena.handle.EIdx) (y z : arena.handle.EIdx) :
    LSP (arena.core.snoc2_eidx_of xs y z)
      (fun r => absEIdxList r = absEIdxList xs ++ [absEIdx y, absEIdx z]) := by
  intro r h
  rw [arena.core.snoc2_eidx_of] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨o2, ho2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hc := eidx_copy_all_map ho1
  have hp2 := ConRon.Refine.vec_push_val ho2
  have hp := ConRon.Refine.vec_push_val h
  simp [absEIdxList, hp, hp2, hc, dupId_eidx _ _ he, dupId_eidx _ _ he1]

@[lockstep] theorem snoc_eidx_ls (xs : alloc.vec.Vec arena.handle.EIdx) (y : arena.handle.EIdx) :
    LSP (arena.core.snoc_eidx xs y) (fun r => absEIdxList r = absEIdxList xs ++ [absEIdx y]) := by
  intro r h
  rw [arena.core.snoc_eidx] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hp := ConRon.Refine.vec_push_val h
  simp [absEIdxList, hp, dupId_eidx _ _ he]

/-! ## Rust-only mode and `PropWhen` gates -/

@[lockstep] theorem is_never_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.is_never pw)
      (fun b => b = ConLeche.PropWhen.isNever (ConRon.Refine.absPropWhen pw)) :=
  fun _ h => ConRon.Refine.PropWhen.is_never_refines h

@[lockstep] theorem certs_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.certs m) (fun b => b = (ConRon.Refine.absMode m).certs) := by
  intro b h
  cases m <;> (simp only [kernel.env.certs, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem tt_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.tt_checks m) (fun b => b = (ConRon.Refine.absMode m).ttChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.tt_checks, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem verified_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m)
      (fun b => b = (ConRon.Refine.absMode m).verifiedChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

attribute [lockstep_simp] ConRon.Refine.absBinderMeta ExprOps.absStrip Option.isSome_some
  Option.isSome_none

/-! ## `PropWhen` comparison and the binder datum's well-formedness -/

/-- `prop_when::beq` against the twin's `==` on the abstraction: exact on
well-formed data (`Refine/PropWhen.lean`'s `beq_refines`). -/
@[lockstep] theorem prop_when_beq_ls (a b : kernel.prop_when.PropWhen)
    (ha : ConRon.Refine.PropWhenWF a) (hb : ConRon.Refine.PropWhenWF b) :
    LSP (kernel.prop_when.beq a b)
      (fun c => c = (ConRon.Refine.absPropWhen a == ConRon.Refine.absPropWhen b)) :=
  fun _ h => ConRon.Refine.PropWhen.beq_refines ha hb h

/-- `view_bind` with the datum's well-formedness (`AStateInv`'s `bms` clause)
carried in the answer relation.  Not `@[lockstep]`: a body that needs the
fact takes it as a local hypothesis, which `lockstep` tries first. -/
theorem view_bind_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => (∀ t, a = some t → ConRon.Refine.PropWhenWF t.2.2.pw) ∧
        b = Option.map absBindM a)
      (arena.monad.view_bind pers st h) st lst (Arena.viewBind (absEIdx h)) := by
  intro o hrun
  obtain ⟨b, lst', hx, hR, h1, h2⟩ := view_bind_ls hrel hinv h hbind o hrun
  refine ⟨b, lst', hx, ⟨fun t ht => ?_, hR⟩, h1, h2⟩
  subst ht
  obtain ⟨ty, bo, m⟩ := t
  exact view_bind_meta_wf hinv hrun

/-- `view_bind_wf_ls` as a proposition, for a body to take into its context
(`have hvb := viewBindWF_holds pers; unfold ViewBindWF at hvb`). -/
def ViewBindWF (pers : arena.store.PersTier) : Prop :=
  ∀ {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (h : arena.handle.EIdx), ETag.isBind (absEIdx h).tag = true →
    LSV pers (fun a b => (∀ t, a = some t → ConRon.Refine.PropWhenWF t.2.2.pw) ∧
        b = Option.map absBindM a)
      (arena.monad.view_bind pers st h) st lst (Arena.viewBind (absEIdx h))

theorem viewBindWF_holds (pers : arena.store.PersTier) : ViewBindWF pers :=
  fun hrel hinv h hb => view_bind_wf_ls hrel hinv h hb

/-! ## Rust-only scalar and handle steps -/

@[lockstep] theorem usize_cast_u64_ls (i : Std.Usize) :
    LSP (lift (Std.UScalar.cast .U64 i)) (fun r => r.val = i.val) := by
  intro r h
  simp only [lift, Result.ok.injEq] at h
  subst h
  exact usize_cast_u64_val' i

/-- `Checker/Shape.lean`'s `nidx_eq2_abs` (not in this file's imports). -/
theorem nidx_eq2_abs {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absNIdx a == absNIdx b) := by
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

@[lockstep] theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = decide (absNIdx a = absNIdx b)) := by
  intro o h
  rw [nidx_eq2_abs h]
  by_cases hab : absNIdx a = absNIdx b
  · rw [hab]; simp
  · simp [hab]

theorem nidx_vec_contains_from_aux (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) (k : Nat) :
    ∀ (i : Std.Usize) (o : Bool), ns.val.length - i.val = k →
      arena.env.nidx_vec_contains_from ns i n = ok o →
      o = ((ns.val.drop i.val).map absNIdx).contains (absNIdx n) := by
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.env.nidx_vec_contains_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro i o hk h
    rw [arena.env.nidx_vec_contains_from] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
    obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn1)
    rw [List.drop_eq_getElem_cons hlt, hx, List.map_cons, List.contains_cons]
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi := ConRon.Refine.Nat.uadd_val hi2
      rw [ih i2 o (by simp at hi; omega) h]
      have : (absNIdx n == absNIdx n1) = false := by
        rw [BEq.comm]; exact hbv.symm
      simp [this, hi]
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      subst h
      have : (absNIdx n == absNIdx n1) = true := by
        rw [BEq.comm]; exact hbv.symm
      simp [this]

@[lockstep] theorem nidx_vec_contains_ls (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.env.nidx_vec_contains ns n)
      (fun o => o = (absNIdxList ns).contains (absNIdx n)) := by
  intro o h
  rw [arena.env.nidx_vec_contains] at h
  have := nidx_vec_contains_from_aux ns n _ 0#usize o rfl h
  simpa [absNIdxList] using this

@[lockstep] theorem i_constant_val_dup_ls (cv : arena.env.IConstantVal) :
    LSP (arena.env.i_constant_val_dup cv) (fun o => o = cv) := by
  intro o h
  rw [arena.env.i_constant_val_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hvv := nidx_vec_dup_val hv
  rw [← Result.ok_injective h, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    alloc.vec.Vec.ext _ _ hvv]

@[lockstep] theorem i_ind_caps_dup_ls (c : arena.env.IIndCaps) :
    LSP (arena.env.i_ind_caps_dup c) (fun o => c.eta = o.eta ∧ c.eta_ctor = o.eta_ctor ∧
      c.eta_params = o.eta_params ∧ c.eta_fields = o.eta_fields ∧ c.unitlike = o.unitlike ∧
      c.unit_params = o.unit_params ∧ c.rule_k = o.rule_k ∧ absIIndCaps c = absIIndCaps o) := by
  intro o h
  have habs := (i_ind_caps_dup_abs h).symm
  rw [arena.env.i_ind_caps_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ho := Result.ok_injective h
  subst ho
  rw [dupId_nidx _ _ hn] at habs ⊢
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, habs⟩

/-! ### The abstractions' field projections (`lockstep_simp`)

Stated as projection lemmas rather than by unfolding the abstraction, so that
a dup's `absIIndCaps c = absIIndCaps o` rewrites the twin's record first. -/

@[lockstep_simp] theorem absIIndCaps_eta (c) : (absIIndCaps c).eta = c.eta := rfl
@[lockstep_simp] theorem absIIndCaps_etaCtor (c) : (absIIndCaps c).etaCtor = absNIdx c.eta_ctor := rfl
@[lockstep_simp] theorem absIIndCaps_etaParams (c) : (absIIndCaps c).etaParams = absU c.eta_params := rfl
@[lockstep_simp] theorem absIIndCaps_etaFields (c) : (absIIndCaps c).etaFields = absU c.eta_fields := rfl
@[lockstep_simp] theorem absIIndCaps_unitlike (c) : (absIIndCaps c).unitlike = c.unitlike := rfl
@[lockstep_simp] theorem absIIndCaps_unitParams (c) :
    (absIIndCaps c).unitParams = absU c.unit_params := rfl
@[lockstep_simp] theorem absIConstantVal_name (c) : (absIConstantVal c).name = absNIdx c.name := rfl
@[lockstep_simp] theorem absIConstantVal_levelParams (c) :
    (absIConstantVal c).levelParams = absNIdxList c.level_params := rfl
@[lockstep_simp] theorem absIConstantVal_type (c) : (absIConstantVal c).type = absEIdx c.ty := rfl

@[lockstep_simp] theorem absEIdxList_length (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxList v).length = v.val.length := by simp [absEIdxList]
@[lockstep_simp] theorem absNIdxList_length (v : alloc.vec.Vec arena.handle.NIdx) :
    (absNIdxList v).length = v.val.length := by simp [absNIdxList]

@[lockstep] theorem dup2_nidx_ls (n : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 n) (fun r => r = n) :=
  fun r h => dupId_nidx _ _ h

@[lockstep] theorem nidx_vec_dup_ls (ns : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.env.nidx_vec_dup ns) (fun r => r = ns) :=
  fun _ h => alloc.vec.Vec.ext _ _ (nidx_vec_dup_val h)

@[lockstep] theorem snoc_eidx_of_ls (xs : alloc.vec.Vec arena.handle.EIdx) (y : arena.handle.EIdx) :
    LSP (arena.expr_ops.snoc_eidx_of xs y)
      (fun r => absEIdxList r = absEIdxList xs ++ [absEIdx y]) :=
  fun _ h => ExprOps.snoc_eidx_of_refines h

/-- `nidx_vec_beq_from`: the cursor comparison of two name-handle vectors. -/
theorem nidx_vec_beq_from_aux (a b : alloc.vec.Vec arena.handle.NIdx) (k : Nat) :
    ∀ (i : Std.Usize) (o : Bool), a.val.length - i.val = k → a.val.length = b.val.length →
      arena.core.nidx_vec_beq_from a b i = ok o →
      o = decide ((a.val.drop i.val).map absNIdx = (b.val.drop i.val).map absNIdx) := by
  induction k with
  | zero =>
    intro i o hk hl h
    rw [arena.core.nidx_vec_beq_from] at h
    rw [if_pos (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro i o hk hl h
    rw [arena.core.nidx_vec_beq_from] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b1 = (absNIdx n == absNIdx n1) := nidx_eq2_abs hb1
    obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn)
    obtain ⟨hlt1, hx1⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn1)
    rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hlt1, hx, hx1,
      List.map_cons, List.map_cons]
    cases hbb : b1
    · rw [hbb] at h hbv
      rw [if_neg (by simp), Result.ok.injEq] at h
      subst h
      have : absNIdx n ≠ absNIdx n1 := by
        intro hc; rw [hc] at hbv; simp at hbv
      simp [this]
    · rw [hbb] at h hbv
      rw [if_pos rfl] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi := ConRon.Refine.Nat.uadd_val hi2
      rw [ih i2 o (by simp at hi; omega) hl h]
      have : absNIdx n = absNIdx n1 := by simpa using hbv.symm
      simp [this, hi]

@[lockstep] theorem nidx_vec_beq_ls (a b : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.core.nidx_vec_beq a b) (fun o => o = decide (absNIdxList a = absNIdxList b)) := by
  intro o h
  rw [arena.core.nidx_vec_beq] at h
  split at h
  · have hl : a.val.length = b.val.length := by scalar_tac
    have := nidx_vec_beq_from_aux a b _ 0#usize o rfl hl h
    simpa [absNIdxList] using this
  · cases Result.ok_injective h
    have hl : a.val.length ≠ b.val.length := by scalar_tac
    have : absNIdxList a ≠ absNIdxList b := fun hc => hl (by
      have := congrArg List.length hc; simpa [absNIdxList] using this)
    exact (decide_eq_false this).symm

/-! ## Store reads -/

@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewConst (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_const] at hr; exact estore_view_const_abs hrel.store hr)
    hrel hinv

attribute [lockstep_simp] absConstT

/-- **`view_ls` against the twin's `match ← viewLsLen h with | none =>
failDanglingLs | some n => …`.**  The port reads the whole level list and
fails on a dangling handle; the twin reads the length and fails in the
continuation's `none` arm.  Not a bind rule `lockstep` can find (the twin's
failure is in `g`, not in the read), so a body applies it by hand. -/
theorem LS.view_ls_len_bind {γ δ : Type} {pers st lst} {h : arena.handle.LsIdx}
    {R : γ → δ → Prop}
    {k : core.result.Result (alloc.vec.Vec arena.handle.LIdx) kernel.core_types.CheckError →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {g : Option Nat → AM δ}
    (hrel : AStateRel₀ pers st lst)
    (hg : g none = failDanglingLs)
    (he : ∀ e, ErrArm (k (.Err e)) e)
    (hk : ∀ v : alloc.vec.Vec arena.handle.LIdx, LS pers R (k (.Ok v)) lst (g (some v.val.length))) :
    LS pers R (arena.monad.view_ls pers st h >>= k) lst (Arena.viewLsLen (absLsIdx h) >>= g) := by
  intro o st' hm
  obtain ⟨r, hr, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have htw : (Arena.viewLsLen (absLsIdx h) >>= g).run lst
      = (g (lst.store.lss.viewLen (absLsIdx h))).run lst := rfl
  rw [htw]
  rw [arena.monad.view_ls] at hr
  obtain ⟨n, hn, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  rw [arena.store.EStore.ls_s] at hn
  have hn2 : n = st.store.lss := (Result.ok_injective hn).symm
  subst hn2
  obtain ⟨v, hv, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
  have hview := lsstore_view_abs hrel.store.lss hv
  rw [LsStore_viewLen_eq, hview]
  cases hvc : v with
  | none =>
    rw [hvc] at hr
    obtain ⟨s, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    obtain ⟨w, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    have ho := fail_run hr
    subst ho
    have := he _ o st' hk1
    subst this
    rw [Option.map_none, Option.map_none, hg]
    exact AErrSim.internal rfl
  | some w =>
    rw [hvc] at hr
    have ho := Result.ok_injective hr
    subst ho
    have := hk w o st' hk1
    simpa [absLsNodeView] using this


theorem code_points_from_val' (N : Nat) :
    ∀ (codes : Slice Std.U32) (i : Std.Usize) (out r : alloc.vec.Vec Std.U32),
      codes.val.length - i.val = N →
      kernel.core_types.code_points_from codes i out = ok r →
      r.val = out.val ++ codes.val.drop i.val := by
  induction N with
  | zero =>
    intro codes i out r hN h
    rw [kernel.core_types.code_points_from] at h
    rw [if_pos (by have := Slice.len_val codes; scalar_tac)] at h
    rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by omega)]; simp
  | succ N ih =>
    intro codes i out r hN h
    rw [kernel.core_types.code_points_from] at h
    rw [if_neg (by have := Slice.len_val codes; scalar_tac)] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hlt : i.val < codes.val.length := by omega
    have hxv : codes.val[i.val] = x := by
      simp only [Slice.index_usize] at hx
      cases hq : codes[i]? with
      | none => rw [hq] at hx; simp at hx
      | some y =>
        rw [hq] at hx
        have hyx : y = x := Result.ok_injective hx
        subst hyx
        have : codes.val[i.val]? = some y := hq
        rw [List.getElem?_eq_getElem hlt] at this
        exact Option.some_injective _ this
    have h2 := ConRon.Refine.Nat.uadd_val hi1
    rw [ih codes i1 o1 r (by simp at h2; omega) h, ConRon.Refine.vec_push_val ho1,
      show i1.val = i.val + 1 by simpa using h2, List.drop_eq_getElem_cons hlt, hxv]
    simp

theorem code_points_val' {codes : Slice Std.U32} {r : alloc.vec.Vec Std.U32}
    (h : kernel.core_types.code_points codes = ok r) : r.val = codes.val := by
  rw [kernel.core_types.code_points] at h
  rw [code_points_from_val' _ codes 0#usize _ r rfl h]
  simp [alloc.vec.Vec.with_capacity]

theorem proj_fn_name_str_abs {v : alloc.vec.Vec Std.U32}
    (h : kernel.core_types.code_points (Array.to_slice arena.env.proj_fn_name.S) = ok v) :
    ConRon.Refine.absString v = "proj" ∧ ConRon.Refine.StrWF v := by
  have hv : v.val = [112#u32, 114#u32, 111#u32, 106#u32] := by
    rw [code_points_val' h, Array.val_to_slice, arena.env.proj_fn_name.S,
      Array.make_val]
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absString, hv]; rfl
  · intro c hc; rw [hv] at hc; fin_cases hc <;> decide

theorem intern_n_node_of_estore {pers : arena.store.PersTier} {st : arena.monad.AState}
    {v : arena.store.NNodeView} {r e}
    (h : arena.store.EStore.intern_name st.store pers v = ok (r, e)) :
    arena.monad.intern_n_node pers st v = ok (r, { st with store := e }) := by
  rw [arena.monad.intern_n_node, h]; simp

/-- `arena::env::proj_fn_name` (two name interns on the bare store) against
`projFnName`. -/
@[lockstep] theorem proj_fn_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : arena.handle.NIdx) (j : Std.U64) :
    LSS pers (fun a b => b = absNIdx a) (arena.env.proj_fn_name pers st.store t j) st lst
      (projFnName (absNIdx t) (absU j)) := by
  intro o s' hm
  rw [arena.env.proj_fn_name] at hm
  obtain ⟨n, hn, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨sl, hsl, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨v, hv, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨⟨r1, ar1⟩, h1, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  simp only [lift, Result.ok.injEq] at hsl
  subst hsl
  have hnt : n = t := dupId_nidx _ _ hn
  subst hnt
  obtain ⟨hstr, hwf⟩ := proj_fn_name_str_abs hv
  have sim1 := intern_n_node_run₀ hrel hinv _ (by exact hwf) (intern_n_node_of_estore h1)
  have htw : projFnName (absNIdx n) (absU j)
      = (Arena.internNNode (absNNodeView (.Str n v)) >>= fun s =>
          Arena.internNNode (.num s (absU j))) := by
    rw [projFnName, absNNodeView, hstr]
  rw [htw]
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hm
    cases ho
    exact errSim_bind sim1
  | Ok s1 =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := sim1.apply
    rw [run_bind_ok hx1]
    have sim2 := intern_n_node_run₀ (st := { st with store := ar1 }) hrel1 hinv1
      (.Num s1 j) trivial (intern_n_node_of_estore hm)
    show LOut pers _ o { st with store := s' } _
    cases o with
    | Err e => exact sim2
    | Ok a =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := sim2.apply
      exact ⟨_, lst2, hx2, rfl, hrel2, hinv2⟩

/-! ## Twin-side shapes -/

/-- The twin's `if ← x then pure true else pure false` is `x`: the port tail-calls. -/
@[lockstep_simp] theorem bind_if_pure_true_false (x : AM Bool) :
    (x >>= fun b => if b = true then pure true else pure false) = x := by
  conv => rhs; rw [← bind_pure x]
  congr 1; funext b; cases b <;> rfl

end ConRon.Refine2.Lockstep.PC1
