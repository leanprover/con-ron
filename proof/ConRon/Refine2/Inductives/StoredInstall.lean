/-
# `ConRon.Refine2.Inductives.StoredInstall` — Theorem 2 for `arena::inductives::stored_install`

`crates/con-ron-core/src/arena/inductives/stored_install.rs` against
`proof/ConRon/Arena/Inductives/StoredInstall.lean`: the stored install of a block, one
lockstep theorem per function.

## Shapes

* The `beqP` family is pure: a `Bool` against a `Bool`, exact on canonical data (the
  capability record's `PropWhen`, `IConstantInfoWF`).
* **A failed inference is a value.**  The Rust's `Err` of a stored inference maps to
  the twin's `.error` through `AErrSim`, for each of the four kinds, so the twin's
  `storedTry` takes its `.error` arm whatever the Rust's error was.  `stored_abandon`
  writes the state from the tier, the saved pins and fresh tables, so nothing is owed
  about what the failed run left (`stored_abandon_rel`).
* Phase A's reader has an empty environment base (`PersEnvEmpty`), and so does the tier
  a bracket freezes out of the store, so the relation moves across a bracket
  (`IFEnvRelI.rebase`).
* What leaves a bracket through the promotion keeps its names (`KeptC`, `KeptT`), so
  `stored_tail` and its callers carry `EnvExt` of what the block found: the fold's
  fact that no install overwrites a row.
-/
import ConRon.Refine2.Inductives.Top
import ConRon.Refine2.Checker.EnvExt
import ConRon.Refine2.Core.Frame
import ConRon.Refine2.Checker.Init
import ConRon.Arena.Inductives.StoredInstall

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] core_walk_fuel_abs Lockstep.core_walk_fuel_val

/-- `basis_pin_hit` in `LS` form. -/
@[lockstep] theorem basis_pin_hit_ls {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map ConRon.Refine.absBasisKind a)
      (arena.basis.basis_pin_hit pers st block) lst (basisPinHit (absICIL block)) :=
  LS.ofSim₀ fun _ h => basis_pin_hit_refines hrel hinv h

/-! ## The comparison of what an install pushes -/

/-- `eq2` on handles is `==` on their abstractions. -/
theorem nidx_beq_abs {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absNIdx a == absNIdx b) := by
  have := nidx_eq2_abs h
  cases o <;> simp_all

theorem eidx_beq_abs {a b : arena.handle.EIdx} {o : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absEIdx a == absEIdx b) := by
  have := eidx_eq2_abs h
  cases o <;> simp_all

/-- A step of a Rust `&&`: an `if` on a test that is the twin's left conjunct. -/
private theorem and_step {t : Bool} {r : Result Bool} {T : Bool} {o : Bool}
    (hrun : (if t then r else ok false) = ok o)
    (hr : t = true → r = ok o → o = T) : o = (t && T) := by
  cases t with
  | true =>
    simp only [↓reduceIte] at hrun
    simpa using hr rfl hrun
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrun
    simpa using (Result.ok_injective hrun).symm

/-- A scalar test, as the twin's `==` on naturals. -/
private theorem u64_beq_abs (a b : Std.U64) :
    decide (a = b) = (absU a == absU b) := by
  by_cases h : a = b
  · subst h; simp
  · have : absU a ≠ absU b := fun e => h (UScalar.eq_imp _ _ e)
    simp [h, this]

private theorem vec_nidx_beq {a b : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (h : arena.canon.nidx_vec_beq a b 0#usize = ok o) :
    o = (a.val.map absNIdx == b.val.map absNIdx) := by
  rw [nidx_vec_beq_refines h, beq_eq_decide]
  simp [absNIdxLFrom]

private theorem vec_lidx_beq {a b : alloc.vec.Vec arena.handle.LIdx} {o : Bool}
    (h : arena.canon.lidx_vec_beq a b 0#usize = ok o) :
    o = (a.val.map absLIdx == b.val.map absLIdx) := by
  rw [lidx_vec_beq_refines h, beq_eq_decide]
  simp [absLIdxLFrom]

private theorem vec_eidx_beq {a b : alloc.vec.Vec arena.handle.EIdx} {o : Bool}
    (h : arena.canon.eidx_vec_beq a b 0#usize = ok o) :
    o = (a.val.map absEIdx == b.val.map absEIdx) := by
  rw [eidx_vec_beq_refines h, beq_eq_decide]
  simp [absEIdxLFrom]

theorem i_constant_val_beq_p_abs {a b : arena.env.IConstantVal} {o : Bool}
    (h : arena.inductives.stored_install.i_constant_val_beq_p a b = ok o) :
    o = (absIConstantVal a).beqP (absIConstantVal b) := by
  rw [arena.inductives.stored_install.i_constant_val_beq_p] at h
  obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [IConstantVal.beqP, absIConstantVal, Bool.and_assoc]
  rw [← nidx_beq_abs h1]
  refine and_step h fun _ h => ?_
  obtain ⟨b2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← vec_nidx_beq h2]
  refine and_step h fun _ h => ?_
  exact eidx_beq_abs h

theorem i_rec_rule_fire_beq_p_abs {a b : arena.env.IRecRuleFire} {o : Bool}
    (h : arena.inductives.stored_install.i_rec_rule_fire_beq_p a b = ok o) :
    o = (absIRecRuleFire a).beqP (absIRecRuleFire b) := by
  unfold arena.inductives.stored_install.i_rec_rule_fire_beq_p at h
  cases a <;> cases b <;> simp only [absIRecRuleFire, IRecRuleFire.beqP] at h ⊢
  · exact (Result.ok_injective h).symm
  · exact (Result.ok_injective h).symm
  · exact (Result.ok_injective h).symm
  · obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← vec_lidx_beq h1]
    refine and_step h fun _ h => ?_
    exact vec_eidx_beq h

theorem i_rec_rule_beq_p_abs {a b : arena.env.IRecRule} {o : Bool}
    (h : arena.inductives.stored_install.i_rec_rule_beq_p a b = ok o) :
    o = (absIRecRule a).beqP (absIRecRule b) := by
  rw [arena.inductives.stored_install.i_rec_rule_beq_p] at h
  obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [IRecRule.beqP, absIRecRule, Bool.and_assoc]
  rw [← nidx_beq_abs h1]
  refine and_step h fun _ h => ?_
  rw [← u64_beq_abs]
  refine and_step (t := decide (a.nfields = b.nfields)) (by simpa using h) fun _ h => ?_
  rw [← u64_beq_abs]
  refine and_step (t := decide (a.ctor_params = b.ctor_params)) (by simpa using h) fun _ h => ?_
  obtain ⟨b2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← i_rec_rule_fire_beq_p_abs h2]
  refine and_step h fun _ h => ?_
  obtain ⟨b3, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← eidx_beq_abs h3]
  refine and_step h fun _ h => ?_
  refine and_step (t := decide (a.k = b.k)) (by simpa using h) fun _ h => ?_
  rw [beq_eq_decide]
  exact (Result.ok_injective h).symm

theorem i_rec_rules_beq_p_aux {a b : alloc.vec.Vec arena.env.IRecRule} (n : Nat) :
    ∀ (i : Std.Usize) {o : Bool}, a.val.length - i.val + (b.val.length - i.val) = n →
      arena.inductives.stored_install.i_rec_rules_beq_p a b i = ok o →
      o = listBeqBy IRecRule.beqP ((a.val.drop i.val).map absIRecRule)
        ((b.val.drop i.val).map absIRecRule) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i o hn h
    rw [arena.inductives.stored_install.i_rec_rules_beq_p.eq_def] at h
    dsimp only at h
    have ha := alloc.vec.Vec.len_val a
    have hb := alloc.vec.Vec.len_val b
    by_cases hga : i ≥ alloc.vec.Vec.len a
    · have hal : a.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hga, List.drop_eq_nil_of_le hal, List.map_nil] at *
      by_cases hgb : i ≥ alloc.vec.Vec.len b
      · have hbl : b.val.length ≤ i.val := by scalar_tac
        rw [ite_eq_left hgb] at h
        rw [List.drop_eq_nil_of_le hbl]
        exact (Result.ok_injective h).symm
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [ite_eq_right hgb, ite_eq_left hga] at h
        rw [List.drop_eq_getElem_cons hbl]
        exact (Result.ok_injective h).symm
    · have hal : i.val < a.val.length := by scalar_tac
      rw [ite_eq_right hga, ite_eq_right hga] at h
      rw [List.drop_eq_getElem_cons hal]
      by_cases hgb : i ≥ alloc.vec.Vec.len b
      · have hbl : b.val.length ≤ i.val := by scalar_tac
        rw [ite_eq_left hgb] at h
        rw [List.drop_eq_nil_of_le hbl]
        exact (Result.ok_injective h).symm
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [ite_eq_right hgb] at h
        rw [List.drop_eq_getElem_cons hbl]
        obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hbx, hx'⟩ := ExprOps.vecIndexAt hx
        obtain ⟨hby, hy'⟩ := ExprOps.vecIndexAt hy
        subst hx' hy'
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        simp only [List.map_cons, listBeqBy]
        rw [← i_rec_rule_beq_p_abs hb1]
        refine and_step h fun _ h => ?_
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have := ih (a.val.length - i2.val + (b.val.length - i2.val)) (by omega) i2 rfl h
        rwa [hi2v] at this

theorem i_ind_caps_beq_abs {a b : arena.env.IIndCaps} {o : Bool}
    (ha : ConRon.Refine.PropWhenWF a.sort_z) (hb : ConRon.Refine.PropWhenWF b.sort_z)
    (h : arena.inductives.stored_install.i_ind_caps_beq a b = ok o) :
    o = decide (absIIndCaps a = absIIndCaps b) :=
  i_ind_caps_beq_refines ha hb h

/-- **`i_constant_info_beq_p` ⊑ `IConstantInfo.beqP`**, at canonical Rust data. -/
theorem i_constant_info_beq_p_abs {a b : arena.env.IConstantInfo} {o : Bool}
    (ha : IConstantInfoWF a) (hb : IConstantInfoWF b)
    (h : arena.inductives.stored_install.i_constant_info_beq_p a b = ok o) :
    o = (absIConstantInfo a).beqP (absIConstantInfo b) := by
  unfold arena.inductives.stored_install.i_constant_info_beq_p at h
  cases a <;> cases b <;> simp only [absIConstantInfo, IConstantInfo.beqP] at h ⊢ <;>
    try first
      | exact (Result.ok_injective h).symm
      | exact i_constant_val_beq_p_abs h
  case DefnInfo.DefnInfo x v hh y w hh2 =>
    simp only [Bool.and_assoc]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← i_constant_val_beq_p_abs hb1]
    refine and_step h fun _ h => ?_
    obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← eidx_beq_abs hb2]
    refine and_step h fun _ h => ?_
    exact ConRon.Refine.Env.reducibility_hint_beq_refines h
  case IndInfo.IndInfo x c y c2 =>
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← i_constant_val_beq_p_abs hb1]
    refine and_step h fun _ h => ?_
    exact i_ind_caps_beq_abs ha hb h
  case CtorInfo.CtorInfo x p q y p2 q2 =>
    simp only [Bool.and_assoc]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← i_constant_val_beq_p_abs hb1]
    refine and_step h fun _ h => ?_
    rw [← u64_beq_abs]
    refine and_step (t := decide (p = p2)) (by simpa using h) fun _ h => ?_
    rw [← u64_beq_abs]
    simpa using (Result.ok_injective h).symm
  case RecInfo.RecInfo x p q rs y p2 q2 rs2 =>
    simp only [Bool.and_assoc]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← i_constant_val_beq_p_abs hb1]
    refine and_step h fun _ h => ?_
    rw [← u64_beq_abs]
    refine and_step (t := decide (p = p2)) (by simpa using h) fun _ h => ?_
    rw [← u64_beq_abs]
    refine and_step (t := decide (q = q2)) (by simpa using h) fun _ h => ?_
    simpa using i_rec_rules_beq_p_aux _ 0#usize rfl h

/-- **`i_proj_table_beq_p` ⊑ `IProjTable.beqP`.** -/
theorem i_proj_table_beq_p_abs {a b : arena.env.IProjTable} {o : Bool}
    (h : arena.inductives.stored_install.i_proj_table_beq_p a b = ok o) :
    o = (absIProjTable a).beqP (absIProjTable b) := by
  rw [arena.inductives.stored_install.i_proj_table_beq_p] at h
  simp only [IProjTable.beqP, absIProjTable, Bool.and_assoc]
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← nidx_beq_abs hb1]
  refine and_step h fun _ h => ?_
  obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← vec_nidx_beq hb2]
  refine and_step h fun _ h => ?_
  rw [← u64_beq_abs]
  refine and_step (t := decide (a.num_params = b.num_params)) (by simpa using h) fun _ h => ?_
  obtain ⟨b3, hb3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← nidx_beq_abs hb3]
  refine and_step h fun _ h => ?_
  rw [← u64_beq_abs]
  refine and_step (t := decide (a.num_fields = b.num_fields)) (by simpa using h) fun _ h => ?_
  obtain ⟨b4, hb4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h4 : b4 = (absLIdx a.struct_sort == absLIdx b.struct_sort) := by
    rw [arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at hb4
    rw [← Result.ok_injective hb4]
    by_cases hab : a.struct_sort = b.struct_sort
    · rw [hab]; simp
    · have h1 : a.struct_sort.word ≠ b.struct_sort.word := by
        intro hc
        apply hab
        cases ha : a.struct_sort
        cases hb' : b.struct_sort
        simp_all
      have h2 : absLIdx a.struct_sort ≠ absLIdx b.struct_sort :=
        fun hc => hab (absLIdx_inj hc)
      simp [h1, h2]
  rw [← h4]
  refine and_step h fun _ h => ?_
  obtain ⟨b5, hb5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h5 : b5 = ((a.bodies.val.map absEIdx).toArray == (b.bodies.val.map absEIdx).toArray) := by
    rw [vec_eidx_beq hb5, beq_eq_decide, beq_eq_decide]
    simp
  rw [← h5]
  refine and_step h fun _ h => ?_
  exact vec_lidx_beq h

/-! ## The state a failed inference leaves -/

theorem estore_of_tier_rel {tier P : arena.store.PersTier} {e : arena.store.EStore} {ls : EStore}
    {r : arena.store.EStore} (htf : tier.frozen = true) (hP : P.frozen = false)
    (hr : StoreRel tier r ls) (hi : StoreInv tier r)
    (h : arena.store.EStore.of_tier tier = ok e) :
    StoreRel P e ls.dropScratch ∧ StoreInv P e := by
  rw [arena.store.EStore.of_tier] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨lt, hlt, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨et, het, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := (Result.ok_injective h).symm
  obtain ⟨rN, iN⟩ := ntables_empty hn
  obtain ⟨rL, iL⟩ := ltables_empty hl
  obtain ⟨rLs, iLs⟩ := lstables_empty hlt
  obtain ⟨rE, iE⟩ := etables_empty het
  have e1 := hr.perst
  have e2 := hr.lss.perst
  have e3 := hr.lss.lvl.perst
  have e4 := hr.lss.lvl.ns.perst
  have i1 := hi.perst
  have i2 := hi.lss.perst
  have i3 := hi.lss.lvl.perst
  have i4 := hi.lss.lvl.ns.perst
  simp only [rPersE, rPersLs, rPersL, rPersN, htf, ite_true] at e1 e2 e3 e4 i1 i2 i3 i4
  refine ⟨⟨⟨⟨⟨?_, rN, rfl⟩, ?_, rL, rfl⟩, ?_, rLs, rfl⟩, ?_, rE, rfl⟩,
    ⟨⟨⟨⟨?_, iN, fun h' => absurd h' (by simp [hP])⟩, ?_, iL, fun h' => absurd h' (by simp [hP])⟩,
      ?_, iLs, fun h' => absurd h' (by simp [hP])⟩, ?_, iE, fun h' => absurd h' (by simp [hP])⟩⟩
  all_goals simp only [rPersE, rPersLs, rPersL, rPersN, hP, Bool.false_eq_true, ite_false]
  all_goals first | exact e4 | exact e3 | exact e2 | exact e1 | exact i4 | exact i3 | exact i2 | exact i1

/-- **`stored_abandon` ⊑ the `.error` arm of `storedTry`**: `dropScratch` at the state
the bracket opened at, whose memos and caches are empty.  What the failed run left is
not read: only the tier, the saved pins, and fresh tables. -/
theorem stored_abandon_rel {tier P : arena.store.PersTier} {st₀ st st' : arena.monad.AState}
    {f : arena.promote.ScratchFrame} {lst₀ : AState} (htf : tier.frozen = true)
    (hP : P.frozen = false) (h₀ : AStateRel₀ tier st₀ lst₀) (hi₀ : AStateInv tier st₀)
    (hm : lst₀.memos = Memos.empty)
    (hsave : arena.promote.scratch_save st₀ = ok f)
    (h : arena.inductives.stored_install.stored_abandon st tier f = ok st') :
    SimS₀ P lst₀ st' dropScratch := by
  rw [arena.promote.scratch_save] at hsave
  obtain ⟨p, hp, hsave⟩ := ConRon.Refine.bind_eq_ok_iff.mp hsave
  obtain rfl := pins_dup_val hp
  obtain rfl := (Result.ok_injective hsave).symm
  rw [arena.inductives.stored_install.stored_abandon] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m, hm', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := (Result.ok_injective h).symm
  obtain ⟨hsr, hsi⟩ := estore_of_tier_rel htf hP h₀.store hi₀.store he
  obtain ⟨hMR, hMI⟩ := memos_empty hm'
  obtain ⟨hCR, hCI⟩ := caches_empty hc
  refine SimS₀.mk (lst' := { lst₀ with store := lst₀.store.dropScratch, caches := Caches.empty })
    rfl ⟨hsr, ?_, hCR, h₀.pins⟩ ⟨hsi, hMI, hCI⟩
  show MemosRel m lst₀.memos
  rw [hm]
  exact hMR

/-! ## The bracket's tail: the flags and the pins kept -/

/-- A stored inference's successful run, read at the bracket: the state it ended in,
framed. -/
theorem stored_frame_ok {α : Type} {tier : arena.store.PersTier} {st₀ st₁ st₂ : arena.monad.AState}
    {f : arena.promote.ScratchFrame} {lst₀ lst₁ : AState} {c : AM α} {a : α}
    (htf : tier.frozen = true) (h₀ : AStateRel₀ tier st₀ lst₀) (hi₀ : AStateInv tier st₀)
    (h₁ : AStateRel₀ tier st₁ lst₁) (hi₁ : AStateInv tier st₁)
    (hsave : arena.promote.scratch_save st₀ = ok f)
    (hres : arena.promote.scratch_restore st₁ f = ok st₂)
    (hc : c.run lst₀ = .ok (a, lst₁)) :
    ∃ lst₂, (scratchRun c).run lst₀ = .ok (a, lst₂) ∧ AStateRel₀ tier st₂ lst₂ ∧
      AStateInv tier st₂ := by
  obtain ⟨h1, h2⟩ := scratch_frame htf h₀ hi₀ h₁ hi₁ hsave hres
  exact ⟨_, scratchRun_ok htf h₀ h₁ hc, h1, h2⟩

/-! ## The promotion, at a frozen tier

A promotion's `LST` outcome, read back at the tier it returned: the glued state through
a stand-in is the frozen state through its tier. -/

/-- A promotion's `LST` outcome, read back at the tier it returned. -/
theorem LST.glue_out {α β : Type} {P t' : arena.store.PersTier}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.PersTier)}
    {x : AM β} {o : core.result.Result α kernel.core_types.CheckError}
    (hP : P.frozen = false) (hsc : ScratchOn st.store)
    (h : Lockstep.LST P (fun p v => R p.1 v ∧ p.2.frozen = true) (fun t' => glue t' st) m lst x)
    (hm : m = ok (o, t')) :
    Lockstep.LOut t' (fun a b => R a b ∧ t'.frozen = true) o st (x.run lst) := by
  have hp : Lockstep.packT (fun t' => glue t' st) m
      = ok (Lockstep.packTOut (fun t' => glue t' st) (o, t')) := by
    simp only [Lockstep.packT, hm, bind_ok]
  cases o with
  | Err e => exact h _ _ hp
  | Ok a =>
    obtain ⟨b, lst', hx, ⟨hR, hf⟩, hrel, hinv⟩ := h _ _ hp
    exact ⟨b, lst', hx, ⟨hR, hf⟩, (glue_rel hP).mp hrel, (glue_inv hP hsc).mp hinv⟩

/-- A stand-in reader: the tier's tables, not frozen. -/
def standIn (t : arena.store.PersTier) : arena.store.PersTier := { t with frozen := false }

/-- **`promote_new` at a frozen tier**, read back at the tier it returns: the promotion
every phase-A bracket ends in, before its `drop_scratch`.  What it hands back keeps the
names it was given (`KeptC`, `KeptT`). -/
theorem promote_new_drop {tier st lst rm lm rf lf} {fuel k kt : Std.U64} {r1 tier1}
    (htf : tier.frozen = true)
    (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (hm : PMemoRel rm lm) (hfe : IFEnvOwn rf lf) (hfinv : IFEnvInv rf)
    (hk : absU k ≤ rf.env.consts.val.length) (hkt : absU kt ≤ rf.env.tables.val.length)
    (hrun : arena.promote.promote_new tier st rm fuel k kt rf = ok (r1, tier1)) :
    Lockstep.LOut tier1 (fun a b => (PMemoRel a.1 b.1 ∧ IFEnvOwnI a.2 b.2 ∧ KeptC rf a.2 ∧
        KeptT rf a.2) ∧ tier1.frozen = true) r1 st
      ((promoteNew lm (absU fuel) (absU k) (absU kt) lf).run lst) := by
  have hsc := ScratchOn.of_inv hinv htf
  have hP : (standIn tier).frozen = false := rfl
  exact LST.glue_out hP hsc
    (promote_new_ls hP htf hsc ((glue_rel (t := tier) hP).mpr hrel)
      ((glue_inv (t := tier) hP hsc).mpr hinv) hm hfe hfinv hk hkt) hrun

/-- `promote_e` at a frozen tier. -/
theorem promote_e_frozen {tier st lst rm lm} {fuel : Std.U64} {e r1 tier1}
    (htf : tier.frozen = true) (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (hm : PMemoRel rm lm) (hrun : arena.promote.promote_e tier st rm fuel e = ok (r1, tier1)) :
    Lockstep.LOut tier1 (fun a b => (PMemoRel a.1 b.1 ∧ b.2 = absEIdx a.2) ∧
        tier1.frozen = true) r1 st ((promoteE lm (absU fuel) (absEIdx e)).run lst) := by
  have hsc := ScratchOn.of_inv hinv htf
  have hP : (standIn tier).frozen = false := rfl
  exact LST.glue_out hP hsc
    (promote_e_ls hP htf hsc ((glue_rel (t := tier) hP).mpr hrel)
      ((glue_inv (t := tier) hP hsc).mpr hinv) hm fuel e) hrun

/-- `promote_l` at a frozen tier. -/
theorem promote_l_frozen {tier st lst rm lm} {fuel : Std.U64} {e r1 tier1}
    (htf : tier.frozen = true) (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (hm : PMemoRel rm lm) (hrun : arena.promote.promote_l tier st rm fuel e = ok (r1, tier1)) :
    Lockstep.LOut tier1 (fun a b => (PMemoRel a.1 b.1 ∧ b.2 = absLIdx a.2) ∧
        tier1.frozen = true) r1 st ((promoteL lm (absU fuel) (absLIdx e)).run lst) := by
  have hsc := ScratchOn.of_inv hinv htf
  have hP : (standIn tier).frozen = false := rfl
  exact LST.glue_out hP hsc
    (promote_l_ls hP htf hsc ((glue_rel (t := tier) hP).mpr hrel)
      ((glue_inv (t := tier) hP hsc).mpr hinv) hm fuel e) hrun

/-- `promote_l_list` at a frozen tier. -/
theorem promote_l_list_frozen {tier st lst rm lm} {fuel : Std.U64} {us r1 tier1}
    (htf : tier.frozen = true) (hrel : AStateRel₀ tier st lst) (hinv : AStateInv tier st)
    (hm : PMemoRel rm lm)
    (hrun : arena.promote.promote_l_list tier st rm fuel us = ok (r1, tier1)) :
    Lockstep.LOut tier1 (fun a b => (PMemoRel a.1 b.1 ∧ b.2 = absLIdxL a.2) ∧
        tier1.frozen = true) r1 st ((promoteLList lm (absU fuel) (absLIdxL us)).run lst) := by
  have hsc := ScratchOn.of_inv hinv htf
  have hP : (standIn tier).frozen = false := rfl
  exact LST.glue_out hP hsc
    (promote_l_list_ls hP htf hsc ((glue_rel (t := tier) hP).mpr hrel)
      ((glue_inv (t := tier) hP hsc).mpr hinv) hm fuel us) hrun

/-- **The promotion keeps `EnvExt`**: a bracket's end, at the relation.  `rf₁` is what
the bracket pushed, `rf₂` what it promoted, and the names did not move. -/
theorem envExt_promoted {a b c : IFEnv} {rf₁ rf₂ : arena.env.IFEnv}
    {tier : arena.store.PersTier} (hext : EnvExt a b) (ha : EnvOK a)
    (hb : IFEnvRel tier IEnv.empty rf₁ b) (hc : IFEnvOwn rf₂ c)
    (hK : KeptC rf₁ rf₂) (hT : KeptT rf₁ rf₂) {m m' : PMemo} {fuel k kt : Nat} {s s' : AState}
    (hk : k = b.visibleBelow - a.visibleBelow)
    (hkt : kt = b.env.tables.length - a.env.tables.length)
    (hrun : promoteNew m fuel k kt b s = .ok ((m', c), s')) : EnvExt a c := by
  have hbe : b.env = absIEnv rf₁.env := by rw [hb.env, overEnv_empty]
  refine hext.promoteNew ha hk hkt hrun ?_ ?_
  · rw [hc.env, hbe]
    simp only [absIEnv, List.map_reverse, List.map_map]
    congr 1
  · rw [hc.env, hbe]
    simp only [absIEnv, List.map_reverse, List.map_map]
    congr 1

/-- `AOutRel₀` at a weaker relation. -/
theorem AOutRel₀.mono {α β : Type} {R R' : α → β → Prop} {pers : arena.store.PersTier}
    {o : core.result.Result α kernel.core_types.CheckError} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (hR : ∀ a b, R a b → R' a b)
    (h : AOutRel₀ R pers o st' x) : AOutRel₀ R' pers o st' x := by
  cases o with
  | Err e => exact h
  | Ok a =>
    obtain ⟨v, lst', hx, hr, hrel, hinv⟩ := h
    exact ⟨v, lst', hx, hR _ _ hr, hrel, hinv⟩

/-! ## A failing run, as the twin sees it -/

/-- A failure of a bind's left side, through its `run`. -/
theorem AErrSim.bind_run {α β : Type} {e : kernel.core_types.CheckError} {m : AM α} {lst : AState}
    (h : AErrSim e (m.run lst)) (k : α → AM β) : AErrSim e ((m >>= k).run lst) := by
  rw [am_run_bind]
  exact AErrSim.bind h _

/-- A Rust failure is a twin failure, whichever of the four kinds. -/
theorem AErrSim.exists_err {γ : Type} {e : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} (h : AErrSim e x) : ∃ le, x = .error le := by
  cases e with
  | NotImplemented m => obtain ⟨le, hx, -⟩ := h _ rfl; exact ⟨le, hx⟩
  | Invalid m => obtain ⟨le, hx, -⟩ := h _ rfl; exact ⟨le, hx⟩
  | Internal m => obtain ⟨le, hx, -⟩ := h _ rfl; exact ⟨le, hx⟩
  | Native m => obtain ⟨le, hx, -⟩ := h _ rfl; exact ⟨le, hx⟩

/-- `storedTry` on a run the twin rejects: the bracket's state, dropped, and `none`. -/
theorem storedTry_err {α β : Type} {run : AM α} {keep : α → AM β} {lst lst₁ lst₂ : AState}
    {le : Arena.CheckError}
    (hx1 : (flushCaches : AM Unit).run lst = .ok ((), lst₁))
    (hx2 : (enterScratch : AM Unit).run lst₁ = .ok ((), lst₂))
    (hrun : run.run lst₂ = .error le) :
    (storedTry run keep).run lst = (dropScratch.run lst₂).map fun p => (none, p.2) := by
  have hs := scratchRun_err hrun
  have hs' : scratchRun run lst₂ = .error le := hs
  simp only [storedTry, am_run_bind, hx1, except_ok_bind, hx2]
  show (match scratchRun run lst₂ with
    | .ok (a, s₁) => _
    | .error _ => _) = _
  rw [hs']
  show (dropScratch >>= fun _ => pure none : AM (Option β)).run lst₂ = _
  rw [am_run_bind]
  cases hd : dropScratch.run lst₂ with
  | error e => rfl
  | ok q => rfl

/-- `storedTry` on a run the twin accepts: `keep` at the framed state, the drop, `some`. -/
theorem storedTry_ok {α β : Type} {run : AM α} {keep : α → AM β} {lst lst₁ lst₂ lst₃ : AState}
    {a : α}
    (hx1 : (flushCaches : AM Unit).run lst = .ok ((), lst₁))
    (hx2 : (enterScratch : AM Unit).run lst₁ = .ok ((), lst₂))
    (hrun : (scratchRun run).run lst₂ = .ok (a, lst₃)) :
    (storedTry run keep).run lst =
      (do let b ← keep a; dropScratch; pure (some b) : AM (Option β)).run lst₃ := by
  have hs' : scratchRun run lst₂ = .ok (a, lst₃) := hrun
  simp only [storedTry, am_run_bind, hx1, except_ok_bind, hx2]
  show (match scratchRun run lst₂ with
    | .ok (a, s₁) => _
    | .error _ => _) = _
  rw [hs']
  rfl

theorem enterScratch_memos {lst lst' : AState}
    (h : (enterScratch : AM Unit).run lst = .ok ((), lst')) : lst'.memos = Memos.empty := by
  have : (enterScratch : AM Unit).run lst =
      .ok ((), { lst with store := lst.store.enableScratch, memos := Memos.empty }) := rfl
  rw [this] at h
  cases h
  rfl

/-! ## A former's telescope -/

@[lockstep] theorem stored_tele_run_ls {E₀ pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (cv : arena.env.IConstantVal) (n : Std.U64) :
    LS pers (fun a b => b = (absEIdx a.1, absLIdx a.2))
      (arena.inductives.stored_install.stored_tele_run pers st mode rf cv n) lst
      (storedTeleRun (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.stored_install.stored_tele_run, storedTeleRun]
  lockstep

/-- What a telescope read leaves. -/
def absTeleOpt (o : Option (arena.env.IConstantVal × arena.handle.LIdx)) :
    Option (IConstantVal × LIdx) :=
  o.map fun q => (absIConstantVal q.1, absLIdx q.2)

/-- `stored_tele_slow`: the telescope in a scratch bracket of its own.  An `Err` of the
run is the twin's `.error`, whichever kind, and the run goes on from the bracket's state. -/
theorem stored_tele_slow_refines {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} {cv : arena.env.IConstantVal} {n : Std.U64} {o}
    (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st) (hP : P.frozen = false)
    (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (hrun : arena.inductives.stored_install.stored_tele_slow st mode rf cv n = ok o) :
    SimRel₀ (fun a b => b = absTeleOpt a) P lst o
      (storedTry (storedTeleRun (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n))
        fun q => do
          let (m, ty) ← promoteE PMemo.empty coreWalkFuel q.1
          let (_, s) ← promoteL m coreWalkFuel q.2
          pure (({ absIConstantVal cv with type := ty } : IConstantVal), s)) := by
  rw [arena.inductives.stored_install.stored_tele_slow] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (flush_caches_sim₀ hrel hinv h1).apply
  obtain ⟨⟨tier, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨htier, lst2, hx2, hrel2, hinv2⟩ := enter_scratch_rel hrel1 hinv1 hP h2
  have htf : tier.frozen = true := by rw [htier]; rfl
  have hpeT : PersEnvEmpty tier := by rw [htier]; exact persEnvEmpty_tierOf _
  have hfeT := IFEnvRelI.rebase hpe hpeT hfe
  obtain ⟨f, hf, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨⟨r, st3⟩, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := stored_tele_run_ls hrel2 hinv2 hfeT cv n _ _ h3
  cases r with
  | Err e =>
    obtain ⟨le, hle⟩ := AErrSim.exists_err hS
    obtain ⟨st4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    obtain ⟨lst3, hx3, hrel3, hinv3⟩ :=
      (stored_abandon_rel htf hP hrel2 hinv2 (enterScratch_memos hx2) hf h4).apply
    refine ⟨none, lst3, ?_, rfl, hrel3, hinv3⟩
    rw [storedTry_err hx1 hx2 hle, hx3]
    rfl
  | Ok q =>
    obtain ⟨v, lst3, hx3, hv, hrel3, hinv3⟩ := hS
    subst hv
    obtain ⟨ty, s⟩ := q
    obtain ⟨st4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨lst4, hx4, hrel4, hinv4⟩ := stored_frame_ok htf hrel2 hinv2 hrel3 hinv3 hf h4 hx3
    simp only [SimRel₀, AOutRel₀]
    rw [storedTry_ok hx1 hx2 hx4]
    obtain ⟨pm, hpm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨⟨r1, tier1⟩, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hE := promote_e_frozen (lm := PMemo.empty) htf hrel4 hinv4 (pmemo_empty_refines hpm) h5
    rw [core_walk_fuel_abs] at hE
    generalize hF : coreWalkFuel = F at hE ⊢
    cases r1 with
    | Err e =>
      obtain ⟨st5, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      show AErrSim e _
      exact AErrSim.bind_run (AErrSim.bind_run hE _) _
    | Ok p1 =>
      obtain ⟨m, ty2⟩ := p1
      obtain ⟨⟨vm, vty⟩, lst5, hx5, ⟨⟨hvm, hvty⟩, htf1⟩, hrel5, hinv5⟩ := hE
      obtain ⟨⟨r2, tier2⟩, h6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hL := promote_l_frozen htf1 hrel5 hinv5 hvm h6
      rw [core_walk_fuel_abs, hF] at hL
      cases r2 with
      | Err e =>
        obtain ⟨st6, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        show AErrSim e _
        refine AErrSim.bind_run ?_ _
        rw [run_bind_ok hx5 _]
        exact AErrSim.bind_run hL _
      | Ok p2 =>
        obtain ⟨_, s2⟩ := p2
        obtain ⟨⟨vm2, vs⟩, lst6, hx6, ⟨⟨-, hvs⟩, htf2⟩, hrel6, hinv6⟩ := hL
        simp only at hvs hvty
        obtain ⟨st7, h7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨lst7, hx7, hrel7, hinv7⟩ := (drop_scratch_rel hrel6 hinv6 htf2 h7 hP).apply
        obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨lp1, hlp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain rfl := dupId_nidx _ _ hn1
        have hlpv : lp1 = cv.level_params := alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hlp1)
        subst hlpv
        cases Result.ok_injective hrun
        refine ⟨some (({ absIConstantVal cv with type := vty } : IConstantVal), vs), lst7, ?_,
          ?_, hrel7, hinv7⟩
        · refine (run_bind_ok (v := (({ absIConstantVal cv with type := vty } : IConstantVal), vs))
            (lst1 := lst6) ?_ _).trans ((run_bind_ok hx7 _).trans rfl)
          refine (run_bind_ok hx5 _).trans ?_
          exact (run_bind_ok hx6 _).trans rfl
        · simp only [absTeleOpt, Option.map, absIConstantVal, hvty, hvs]

/-- `stored_tele` ⊑ `storedTele`. -/
@[lockstep] theorem stored_tele_ls {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st)
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (cv : arena.env.IConstantVal) (n : Std.U64) :
    LS P (fun a b => b = absTeleOpt a)
      (arena.inductives.stored_install.stored_tele P st mode rf cv n) lst
      (storedTele (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n)) := by
  have hslow : ∀ {st lst}, AStateRel₀ P st lst → AStateInv P st →
      LS P (fun a b => b = absTeleOpt a)
        (arena.inductives.stored_install.stored_tele_slow st mode rf cv n) lst
        (storedTry (storedTeleRun (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n))
          fun q => do
            let (m, ty) ← promoteE PMemo.empty coreWalkFuel q.1
            let (_, s) ← promoteL m coreWalkFuel q.2
            pure (({ absIConstantVal cv with type := ty } : IConstantVal), s)) :=
    fun hr hi => LS.ofSimRel₀ fun _ h => stored_tele_slow_refines hr hi hP hpe hfe h
  rw [arena.inductives.stored_install.stored_tele, storedTele]
  lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp only [absTeleOpt, Option.map, *]

/-! ## The formers -/

theorem stored_formers_aux {P} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (p : arena.inductives.block_parts.BlockShape) (n : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.env.IConstantVal) (s0 : arena.handle.LIdx)
      st lst, p.members.val.length - i.val = n → AStateRel₀ P st lst → AStateInv P st →
      LS P (fun a b => b.1 = absICVL a.1 ∧ b.2 = absLIdx a.2)
        (arena.inductives.stored_install.stored_formers P st mode rf p i out s0) lst
        (storedFormers (ConRon.Refine.absMode mode) lf (absU p.n_p)
          ((p.members.val.drop i.val).map absMemberShape) i.val (absICVL out).reverse
          (absLIdx s0)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i out s0 st lst hn hrel hinv
    have hl := alloc.vec.Vec.len_val p.members
    rw [arena.inductives.stored_install.stored_formers.eq_def]
    dsimp only
    by_cases hge : i ≥ alloc.vec.Vec.len p.members
    · have hle : p.members.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge, List.drop_eq_nil_of_le hle, List.map_nil, storedFormers]
      exact LS.pure (by simp) hrel hinv
    · have hlt : i.val < p.members.val.length := by scalar_tac
      rw [ite_eq_right hge, List.drop_eq_getElem_cons hlt, List.map_cons, storedFormers]
      refine LS.bind_eq fun ms hms => ?_
      obtain ⟨hb', hms'⟩ := ExprOps.vecIndexAt hms
      subst hms'
      refine LS.bind_eq fun k hk => ?_
      have hkv : absU k = absU p.n_p + absU p.members.val[i.val].n_idx := by
        simpa [absU] using ConRon.Refine.HashMap.uscalar_add_eq hk
      refine LS.bind (stored_tele_ls hrel hinv hP hpe hfe _ k) (by
        simp only [absMemberShape]; rw [hkv]) (fun _ _ => errArm_ok) ?_
      rintro a b st1 lst1 hab hrel1 hinv1
      subst hab
      simp only [absMemberShape]
      have hrest : p.members.val.length - (i.val + 1) < n := by omega
      have hrecur : ∀ (i3 : Std.Usize) (out1 : alloc.vec.Vec arena.env.IConstantVal)
          (s1 : arena.handle.LIdx), i3.val = i.val + 1 →
          LS P (fun a b => b.1 = absICVL a.1 ∧ b.2 = absLIdx a.2)
            (arena.inductives.stored_install.stored_formers P st1 mode rf p i3 out1 s1) lst1
            (storedFormers (ConRon.Refine.absMode mode) lf (absU p.n_p)
              ((p.members.val.drop (i.val + 1)).map absMemberShape) (i.val + 1)
              (absICVL out1).reverse (absLIdx s1)) := by
        intro i3 out1 s1 hi3
        have := ih _ hrest i3 out1 s1 st1 lst1 (by omega) hrel1 hinv1
        rwa [hi3] at this
      cases a with
      | none =>
        simp only [absTeleOpt, Option.map]
        refine LS.bind_eq fun iv hiv => ?_
        refine LS.bind_eq fun out1 hout1 => ?_
        refine LS.bind_eq fun i3 hi3 => ?_
        refine LS.tail (hrecur i3 out1 s0 (ConRon.Refine.HashMap.uscalar_add_eq hi3)) ?_
          (fun _ _ h => h)
        have hv : absICVL out1 = absICVL out ++ [absIConstantVal p.members.val[i.val].cv_t] := by
          rw [absICVL, ConRon.Refine.vec_push_val hout1, List.map_append]
          simp [i_constant_val_dup_abs hiv, absICVL]
        simp [hv]
      | some q =>
        obtain ⟨cv, s⟩ := q
        simp only [absTeleOpt, Option.map]
        refine LS.bind_eq fun out1 hout1 => ?_
        refine LS.bind_eq fun s1 hs1 => ?_
        refine LS.bind_eq fun i3 hi3 => ?_
        refine LS.tail (hrecur i3 out1 s1 (ConRon.Refine.HashMap.uscalar_add_eq hi3)) ?_
          (fun _ _ h => h)
        have hv : absICVL out1 = absICVL out ++ [absIConstantVal cv] := by
          rw [absICVL, ConRon.Refine.vec_push_val hout1, List.map_append]
          rfl
        have hsv : absLIdx s1 = if (i.val == 0) = true then absLIdx s else absLIdx s0 := by
          by_cases h0 : i = 0#usize
          · rw [ite_eq_left h0] at hs1
            cases Result.ok_injective hs1
            have : i.val = 0 := by rw [h0]; rfl
            simp [this]
          · rw [ite_eq_right h0] at hs1
            cases Result.ok_injective hs1
            have : i.val ≠ 0 := fun h => h0 (UScalar.eq_imp _ _ (by simpa using h))
            simp [this]
        simp [hv, hsv]

@[lockstep] theorem stored_formers_ls {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st)
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (p : arena.inductives.block_parts.BlockShape) (s0 : arena.handle.LIdx) :
    LS P (fun a b => b.1 = absICVL a.1 ∧ b.2 = absLIdx a.2)
      (arena.inductives.stored_install.stored_formers P st mode rf p 0#usize
        (alloc.vec.Vec.new _) s0) lst
      (storedFormers (ConRon.Refine.absMode mode) lf (absBlockShape p).nP (absBlockShape p).members
        0 [] (absLIdx s0)) := by
  have h := stored_formers_aux (mode := mode) hP hpe hfe p _ 0#usize (alloc.vec.Vec.new _) s0 st lst rfl hrel hinv
  simpa [absICVL, alloc.vec.Vec.new, absBlockShape] using h

/-! ## The recursors -/

/-- `stored_take` is the twin's `take`, from the cursor on. -/
theorem stored_take_abs (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (k : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) {o}, xs.val.length - i.val = k →
      arena.inductives.stored_install.stored_take xs n i out = ok o →
      absEIdxL o = absEIdxL out ++ ((xs.val.drop i.val).take (n.val - i.val)).map absEIdx := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i out o hk h
    rw [arena.inductives.stored_install.stored_take.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val xs
    by_cases hge : i ≥ alloc.vec.Vec.len xs
    · rw [ite_eq_left hge] at h
      have hle : xs.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      simp [List.drop_eq_nil_of_le hle]
    · rw [ite_eq_right hge] at h
      have hlt : i.val < xs.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hcv : c.val = i.val := by
        simp only [lift, Result.ok.injEq] at hc
        rw [← hc, usize_cast_u64_val]
      by_cases hn : c ≥ n
      · rw [ite_eq_left hn] at h
        have hle : n.val ≤ i.val := by scalar_tac
        cases Result.ok_injective h
        simp [show n.val - i.val = 0 by omega]
      · rw [ite_eq_right hn] at h
        have hin : i.val < n.val := by scalar_tac
        obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt hx
        subst hx
        obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi1
        have hrec := ih (xs.val.length - i1.val) (by omega) i1 o1 rfl h
        rw [hrec, hi1v]
        have hyv : y = xs.val[i.val] := dupId_eidx _ _ hy
        rw [absEIdxL, ConRon.Refine.vec_push_val ho1, hyv, List.drop_eq_getElem_cons hlt,
          show n.val - i.val = (n.val - (i.val + 1)) + 1 by omega, List.take_succ_cons]
        simp [absEIdxL]

@[lockstep] theorem stored_take_spec (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.inductives.stored_install.stored_take xs n 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((absEIdxL xs).take (absU n)) (absEIdxL o)) := by
  intro o h
  have := stored_take_abs xs n _ 0#usize _ rfl h
  rw [TwinEq, this]
  simp [absEIdxL, alloc.vec.Vec.new, absU, List.map_take]

@[lockstep] theorem stored_major_dom_ls {P st lst} (hrel : AStateRel₀ P st lst)
    (hinv : AStateInv P st) {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hctx : CoreCtx P vis rf lf) (dom : arena.handle.EIdx) :
    LS P (fun a b => b = a.map absTargetMajor)
      (arena.inductives.stored_install.stored_major_dom P vis st rf dom) lst
      (storedMajorDom lf (absEIdx dom)) := by
  rw [arena.inductives.stored_install.stored_major_dom, storedMajorDom]
  lockstep

@[lockstep] theorem stored_major_ls {P st lst} (hrel : AStateRel₀ P st lst)
    (hinv : AStateInv P st) {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hctx : CoreCtx P vis rf lf) (p : arena.inductives.block_parts.BlockShape)
    (rc : arena.inductives.block_parts.RecShape) :
    LS P (fun a b => b = a.map absTargetMajor)
      (arena.inductives.stored_install.stored_major P vis st rf p rc) lst
      (storedMajor lf (absBlockShape p) (absRecShape rc)) := by
  rw [arena.inductives.stored_install.stored_major, storedMajor]
  simp only [absRecShape, absBlockShape_members, List.getElem?_map]
  refine LS.bind_eq fun k hk => ?_
  have hkv : k.val = p.members.val.length := by
    rw [arena.inductives.block_parts.shape_k] at hk
    simp only [Result.ok.injEq] at hk
    subst hk
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  by_cases hlt : rc.tgt < k
  · rw [ite_eq_left hlt]
    have hl : rc.tgt.val < p.members.val.length := by
      rw [← hkv]; exact (Std.UScalar.lt_equiv _ _).mp hlt
    have hg : p.members.val[absU rc.tgt]? = some p.members.val[rc.tgt.val] :=
      List.getElem?_eq_getElem hl
    rw [hg]
    simp only [Option.map_some]
    refine LS.bind_eq fun ri hri => ?_
    have hriv : ri.val = rc.tgt.val := by
      rw [← ConRon.Refine.ExprOps.u64_cast_usize_val
        (le_of_lt (lt_of_lt_of_le hl p.members.property))]
      exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hri).symm
    refine LS.bind_eq fun ms hms => ?_
    obtain ⟨hb', hms'⟩ := ExprOps.vecIndexAt hms
    have hms2 : ms = p.members.val[rc.tgt.val] := by rw [← hms']; simp only [hriv]
    subst hms2
    lockstep
  · rw [ite_eq_right hlt]
    have hl : p.members.val.length ≤ absU rc.tgt := by
      have : ¬ rc.tgt.val < k.val := fun h => hlt ((Std.UScalar.lt_equiv _ _).mpr h)
      simp only [absU]
      omega
    rw [List.getElem?_eq_none hl]
    simp only [Option.map_none]
    lockstep

theorem stored_recs_aux {P} (vis2 : Std.U64)
    (p : arena.inductives.block_parts.BlockShape) (n : Nat) :
    ∀ (r : Std.U64) (fe : arena.env.IFEnv) (lf : IFEnv) st lst,
      p.recs.val.length - r.val = n → IFEnvRelI P IEnv.empty fe lf →
      AStateRel₀ P st lst → AStateInv P st →
      LS P (IFEnvRelI P IEnv.empty)
        (arena.inductives.stored_install.stored_recs P vis2 st p r fe) lst
        (storedRecs (absU vis2) (absBlockShape p) (absU r)
          ((p.recs.val.drop r.val).map absRecShape) lf) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r fe lf st lst hn hfe hrel hinv
    have hl := alloc.vec.Vec.len_val p.recs
    have hctx := IFEnvInv.coreCtxAt vis2 hfe.rel hfe.inv
    rw [arena.inductives.stored_install.stored_recs.eq_def]
    dsimp only
    refine LS.bind_eq fun k hk => ?_
    have hkv : k.val = p.recs.val.length := by
      simp only [lift, Result.ok.injEq] at hk
      subst hk
      rw [usize_cast_u64_val']
      simp [alloc.vec.Vec.len]
    by_cases hge : r ≥ k
    · have hle : p.recs.val.length ≤ r.val := by scalar_tac
      rw [ite_eq_left hge, List.drop_eq_nil_of_le hle, List.map_nil, storedRecs]
      exact LS.pure hfe hrel hinv
    · have hlt : r.val < p.recs.val.length := by scalar_tac
      rw [ite_eq_right hge, List.drop_eq_getElem_cons hlt, List.map_cons, storedRecs]
      refine LS.bind_eq fun ri hri => ?_
      have hriv : ri.val = r.val := by
        rw [← ConRon.Refine.ExprOps.u64_cast_usize_val
          (le_of_lt (lt_of_lt_of_le hlt p.recs.property))]
        exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hri).symm
      refine LS.bind_eq fun rc hrc => ?_
      obtain ⟨hb', hrc'⟩ := ExprOps.vecIndexAt hrc
      have hrc2 : rc = p.recs.val[r.val] := by rw [← hrc']; simp only [hriv]
      subst hrc2
      simp only [absRecShape]
      lockstep

@[lockstep] theorem stored_recs_ls {P st lst} (vis2 : Std.U64) (p : arena.inductives.block_parts.BlockShape)
    {fe : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI P IEnv.empty fe lf)
    (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st) :
    LS P (IFEnvRelI P IEnv.empty)
      (arena.inductives.stored_install.stored_recs P vis2 st p 0#u64 fe) lst
      (storedRecs (absU vis2) (absBlockShape p) 0 (absBlockShape p).recs lf) := by
  have h := stored_recs_aux (P := P) vis2 p _ 0#u64 fe lf st lst rfl hfe hrel hinv
  simpa [absU, absBlockShape] using h

/-! ## The guards -/

/-- `stored_drop` is the twin's `drop`, from the cursor on. -/
theorem stored_drop_abs (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) (k : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) {o}, xs.val.length - i.val = k →
      n.val ≤ i.val ∨ out.val = [] →
      arena.inductives.stored_install.stored_drop xs n i out = ok o →
      absEIdxL o = absEIdxL out ++ ((xs.val.drop i.val).drop (n.val - i.val)).map absEIdx := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i out o hk hout h
    rw [arena.inductives.stored_install.stored_drop.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val xs
    by_cases hge : i ≥ alloc.vec.Vec.len xs
    · rw [ite_eq_left hge] at h
      have hle : xs.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      simp [List.drop_eq_nil_of_le hle]
    · rw [ite_eq_right hge] at h
      have hlt : i.val < xs.val.length := by scalar_tac
      obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hcv : c.val = i.val := by
        simp only [lift, Result.ok.injEq] at hc
        rw [← hc, usize_cast_u64_val]
      by_cases hn : c < n
      · rw [ite_eq_left hn] at h
        have hin : i.val < n.val := by rw [← hcv]; exact (Std.UScalar.lt_equiv _ _).mp hn
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi1
        have hrec := ih (xs.val.length - i1.val) (by omega) i1 out rfl (by
          rcases hout with h1 | h1
          · omega
          · exact Or.inr h1) h
        rw [hrec, hi1v, List.drop_drop, List.drop_drop,
          show i.val + 1 + (n.val - (i.val + 1)) = i.val + (n.val - i.val) by omega]
      · rw [ite_eq_right hn] at h
        have hin : n.val ≤ i.val := by
          have : ¬ c.val < n.val := fun h' => hn ((Std.UScalar.lt_equiv _ _).mpr h')
          omega
        obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt hx
        subst hx
        obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi1
        have hrec := ih (xs.val.length - i1.val) (by omega) i1 o1 rfl (Or.inl (by omega)) h
        rw [hrec, hi1v]
        have hyv : y = xs.val[i.val] := dupId_eidx _ _ hy
        rw [absEIdxL, ConRon.Refine.vec_push_val ho1, hyv, show n.val - i.val = 0 by omega,
          List.drop_zero, List.drop_eq_getElem_cons hlt, show n.val - (i.val + 1) = 0 by omega,
          List.drop_zero]
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append, absEIdxL]

@[lockstep] theorem stored_drop_spec (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.inductives.stored_install.stored_drop xs n 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((absEIdxL xs).drop (absU n)) (absEIdxL o)) := by
  intro o h
  have := stored_drop_abs xs n _ 0#usize _ rfl (Or.inr rfl) h
  rw [TwinEq, this]
  simp [absEIdxL, alloc.vec.Vec.new, absU, List.map_drop]

attribute [local lockstep_simp] IndInstPrims.unwrapOr_some' IndInstPrims.unwrapOr_none'

@[lockstep] theorem stored_guards_run_ls {E₀ pers st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers E₀ rf lf) (p : arena.inductives.block_parts.BlockShape)
    (c : arena.env.IConstantVal × Std.U64) :
    LS pers (fun a b => b = absLIdxL a)
      (arena.inductives.stored_install.stored_guards_run pers st mode rf p c) lst
      (storedGuardsRun (ConRon.Refine.absMode mode) lf (absBlockShape p)
        (absIConstantVal c.1, absU c.2)) := by
  have hvis : absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm
  rw [arena.inductives.stored_install.stored_guards_run, storedGuardsRun]
  lockstep

/-- `stored_guards`: the walk in a scratch bracket of its own; a failure is no guards. -/
theorem stored_guards_refines {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} {p : arena.inductives.block_parts.BlockShape}
    {c : arena.env.IConstantVal × Std.U64} {o}
    (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st) (hP : P.frozen = false)
    (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (hrun : arena.inductives.stored_install.stored_guards st mode rf p c = ok o) :
    SimRel₀ (fun a b => b = absLIdxL a) P lst o
      (storedGuards (ConRon.Refine.absMode mode) lf (absBlockShape p)
        (absIConstantVal c.1, absU c.2)) := by
  rw [arena.inductives.stored_install.stored_guards] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (flush_caches_sim₀ hrel hinv h1).apply
  obtain ⟨⟨tier, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨htier, lst2, hx2, hrel2, hinv2⟩ := enter_scratch_rel hrel1 hinv1 hP h2
  have htf : tier.frozen = true := by rw [htier]; rfl
  have hpeT : PersEnvEmpty tier := by rw [htier]; exact persEnvEmpty_tierOf _
  have hfeT := IFEnvRelI.rebase hpe hpeT hfe
  obtain ⟨f, hf, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨⟨r, st3⟩, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS := stored_guards_run_ls hrel2 hinv2 hfeT p c _ _ h3
  simp only [storedGuards]
  cases r with
  | Err e =>
    obtain ⟨le, hle⟩ := AErrSim.exists_err hS
    obtain ⟨st4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    obtain ⟨lst3, hx3, hrel3, hinv3⟩ :=
      (stored_abandon_rel htf hP hrel2 hinv2 (enterScratch_memos hx2) hf h4).apply
    refine ⟨[], lst3, ?_, rfl, hrel3, hinv3⟩
    refine (run_bind_ok (v := none) (lst1 := lst3) ?_ _).trans rfl
    rw [storedTry_err hx1 hx2 hle, hx3]
    rfl
  | Ok gs =>
    obtain ⟨v, lst3, hx3, hv, hrel3, hinv3⟩ := hS
    subst hv
    obtain ⟨st4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨lst4, hx4, hrel4, hinv4⟩ := stored_frame_ok htf hrel2 hinv2 hrel3 hinv3 hf h4 hx3
    obtain ⟨pm, hpm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨⟨r1, tier1⟩, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hE := promote_l_list_frozen (lm := PMemo.empty) htf hrel4 hinv4
      (pmemo_empty_refines hpm) h5
    rw [core_walk_fuel_abs] at hE
    simp only [SimRel₀, AOutRel₀]
    cases r1 with
    | Err e =>
      obtain ⟨st5, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      show AErrSim e _
      refine AErrSim.bind_run ?_ _
      rw [storedTry_ok hx1 hx2 hx4]
      exact AErrSim.bind_run (AErrSim.bind_run hE _) _
    | Ok p1 =>
      obtain ⟨_, gs2⟩ := p1
      obtain ⟨⟨vm, vg⟩, lst5, hx5, ⟨⟨-, hvg⟩, htf1⟩, hrel5, hinv5⟩ := hE
      simp only at hvg
      obtain ⟨st6, h6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨lst6, hx6, hrel6, hinv6⟩ := (drop_scratch_rel hrel5 hinv5 htf1 h6 hP).apply
      cases Result.ok_injective hrun
      refine ⟨vg, lst6, ?_, hvg, hrel6, hinv6⟩
      refine (run_bind_ok (v := some vg) (lst1 := lst6) ?_ _).trans rfl
      rw [storedTry_ok hx1 hx2 hx4]
      refine (run_bind_ok (v := vg) (lst1 := lst5) ?_ _).trans ((run_bind_ok hx6 _).trans rfl)
      exact (run_bind_ok hx5 _).trans rfl

/-- What the guards list reads, at the twin's `List (List LIdx)`. -/
def absGuardsL (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)) : List (List LIdx) :=
  v.val.map absLIdxL

/-- A member with one constructor, at the twin's list. -/
theorem absCtorsL_one {cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    (h : alloc.vec.Vec.len cs = 1#usize) :
    ∃ c, cs.val = [c] ∧ absCtorsL cs = [(absIConstantVal c.1, absU c.2)] := by
  have hl : cs.val.length = 1 := by
    have := congrArg UScalar.val h
    simpa using this
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hl
  exact ⟨c, hc, by simp [absCtorsL, hc]⟩

/-- `do let r ← x; pure (f r)` from `x`, the Rust's answer the twin's up to `f`. -/
theorem LS.twin_map {α β γ : Type} {pers : arena.store.PersTier} {R₁ : α → β → Prop}
    {R : α → γ → Prop} {m : Result (core.result.Result α kernel.core_types.CheckError ×
      arena.monad.AState)} {lst : AState} {x : AM β} (f : β → γ)
    (h : LS pers R₁ m lst x) (hR : ∀ a b, R₁ a b → R a (f b)) :
    LS pers R m lst (do let r ← x; pure (f r)) := by
  intro o st' hm
  have h1 := h o st' hm
  cases o with
  | Err e => exact AErrSim.bind_run h1 _
  | Ok a =>
    obtain ⟨b, lst', hx, h2, h3, h4⟩ := h1
    exact ⟨f b, lst', (run_bind_ok hx _).trans rfl, hR _ _ h2, h3, h4⟩

theorem stored_guards_all_aux {P} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (p : arena.inductives.block_parts.BlockShape) (n : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)) st lst,
      p.members.val.length - i.val = n → AStateRel₀ P st lst → AStateInv P st →
      LS P (fun a b => absGuardsL a = absGuardsL out ++ b)
        (arena.inductives.stored_install.stored_guards_all st mode rf p i out) lst
        (storedGuardsAll (ConRon.Refine.absMode mode) lf (absBlockShape p)
          ((p.members.val.drop i.val).map absMemberShape)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i out st lst hn hrel hinv
    have hl := alloc.vec.Vec.len_val p.members
    rw [arena.inductives.stored_install.stored_guards_all.eq_def]
    dsimp only
    by_cases hge : i ≥ alloc.vec.Vec.len p.members
    · have hle : p.members.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge, List.drop_eq_nil_of_le hle, List.map_nil, storedGuardsAll]
      exact LS.pure (by simp) hrel hinv
    · have hlt : i.val < p.members.val.length := by scalar_tac
      rw [ite_eq_right hge, List.drop_eq_getElem_cons hlt, List.map_cons, storedGuardsAll]
      refine LS.bind_eq fun ms hms => ?_
      obtain ⟨hb', hms'⟩ := ExprOps.vecIndexAt hms
      subst hms'
      have hrest : p.members.val.length - (i.val + 1) < n := by omega
      -- the twin's tail after one guard list, whichever the arm
      have htail : ∀ (x : List LIdx) (gsv : alloc.vec.Vec arena.handle.LIdx) (out1 : _) (st1 lst1)
          (i3 : Std.Usize), absLIdxL gsv = x → i3.val = i.val + 1 →
          alloc.vec.Vec.push out gsv = ok out1 → AStateRel₀ P st1 lst1 → AStateInv P st1 →
          LS P (fun a b => absGuardsL a = absGuardsL out ++ b)
            (arena.inductives.stored_install.stored_guards_all st1 mode rf p i3 out1) lst1
            (do
              let r ← storedGuardsAll (ConRon.Refine.absMode mode) lf (absBlockShape p)
                ((p.members.val.drop (i.val + 1)).map absMemberShape)
              pure (x :: r)) := by
        intro x gsv out1 st1 lst1 i3 hx hi3 ho hr hin
        have hrec := ih _ hrest i3 out1 st1 lst1 (by omega) hr hin
        rw [hi3] at hrec
        refine LS.twin_map (fun r => x :: r) hrec fun a b hb => ?_
        rw [hb, absGuardsL, ConRon.Refine.vec_push_val ho, ← hx]
        simp [absGuardsL]
      have hMc : (absMemberShape p.members.val[i.val]).ctors
          = absCtorsL p.members.val[i.val].ctors := rfl
      have hMi : (absMemberShape p.members.val[i.val]).nIdx
          = absU p.members.val[i.val].n_idx := rfl
      generalize absMemberShape p.members.val[i.val] = M at hMc hMi ⊢
      by_cases h1 : alloc.vec.Vec.len (p.members.val[i.val]).ctors = 1#usize
      · rw [ite_eq_left h1]
        obtain ⟨c, hc, hca⟩ := absCtorsL_one h1
        rw [hMc, hca]
        by_cases h0 : (p.members.val[i.val]).n_idx = 0#u64
        · have h0' : (M.nIdx == 0) = true := by
            rw [hMi]; simp [h0, absU]
          rw [ite_eq_left h0]
          simp only [h0', ↓reduceIte]
          refine LS.bind_eq fun c' hc' => ?_
          obtain ⟨hb0, hc''⟩ := ExprOps.vecIndexAt hc'
          have hcc : c' = c := by rw [← hc'']; simp [hc]
          subst hcc
          refine LS.bind (LS.ofSimRel₀ fun _ h => stored_guards_refines hrel hinv hP hpe hfe h)
            rfl (fun _ _ => errArm_ok) ?_
          rintro a b st1 lst1 hab hrel1 hinv1
          subst hab
          refine LS.bind_eq fun out1 hout1 => ?_
          refine LS.bind_eq fun i3 hi3 => ?_
          exact htail _ a out1 st1 lst1 i3 rfl (ConRon.Refine.HashMap.uscalar_add_eq hi3) hout1
            hrel1 hinv1
        · have h0' : ¬ (M.nIdx == 0) = true := by
            rw [hMi]
            simp only [beq_iff_eq, absU]
            intro hv
            exact h0 (UScalar.eq_imp _ _ (by simpa using hv))
          rw [ite_eq_right h0]
          simp only [h0']
          refine LS.bind_eq fun out1 hout1 => ?_
          refine LS.bind_eq fun i3 hi3 => ?_
          exact htail _ (alloc.vec.Vec.new _) out1 st lst i3 rfl
            (ConRon.Refine.HashMap.uscalar_add_eq hi3) hout1 hrel hinv
      · rw [ite_eq_right h1]
        rw [hMc]
        split
        · rename_i c hc
          have hl : p.members.val[i.val].ctors.val.length = 1 := by
            simpa [absCtorsL] using congrArg List.length hc
          exact absurd (UScalar.eq_imp _ _ (by simpa using hl)) h1
        · refine LS.bind_eq fun out1 hout1 => ?_
          refine LS.bind_eq fun i3 hi3 => ?_
          exact htail _ (alloc.vec.Vec.new _) out1 st lst i3 rfl
            (ConRon.Refine.HashMap.uscalar_add_eq hi3) hout1 hrel hinv

@[lockstep] theorem stored_guards_all_ls {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st)
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (p : arena.inductives.block_parts.BlockShape) :
    LS P (fun a b => b = absGuardsL a)
      (arena.inductives.stored_install.stored_guards_all st mode rf p 0#usize
        (alloc.vec.Vec.new _)) lst
      (storedGuardsAll (ConRon.Refine.absMode mode) lf (absBlockShape p) (absBlockShape p).members) := by
  have h := stored_guards_all_aux (mode := mode) hP hpe hfe p _ 0#usize (alloc.vec.Vec.new _) st lst
    rfl hrel hinv
  refine LS.tail h (by simp [absBlockShape]) (fun a b hb => ?_)
  rw [hb]
  simp [absGuardsL, alloc.vec.Vec.new]

/-! ## The tables -/

theorem stored_tables_aux {P} (p : arena.inductives.block_parts.BlockShape)
    (guards : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)) (n : Nat) :
    ∀ (i : Std.Usize) (fe : arena.env.IFEnv) (lf : IFEnv) st lst,
      p.members.val.length - i.val = n → IFEnvRelI P IEnv.empty fe lf →
      AStateRel₀ P st lst → AStateInv P st →
      LS P (IFEnvRelI P IEnv.empty)
        (arena.inductives.stored_install.stored_tables P st p guards i fe) lst
        (storedTables (absBlockShape p) ((p.members.val.drop i.val).map absMemberShape)
          ((guards.val.drop i.val).map absLIdxL) lf) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i fe lf st lst hn hfe hrel hinv
    have hl := alloc.vec.Vec.len_val p.members
    rw [arena.inductives.stored_install.stored_tables.eq_def]
    dsimp only
    by_cases hge : i ≥ alloc.vec.Vec.len p.members
    · have hle : p.members.val.length ≤ i.val := by scalar_tac
      rw [ite_eq_left hge, List.drop_eq_nil_of_le hle, List.map_nil, storedTables]
      exact LS.pure hfe hrel hinv
    · have hlt : i.val < p.members.val.length := by scalar_tac
      rw [ite_eq_right hge, List.drop_eq_getElem_cons hlt, List.map_cons, storedTables]
      refine LS.bind_eq fun ms hms => ?_
      obtain ⟨hb', hms'⟩ := ExprOps.vecIndexAt hms
      subst hms'
      have hrest : p.members.val.length - (i.val + 1) < n := by omega
      have htailg : ((guards.val.drop i.val).map absLIdxL).tail
          = (guards.val.drop (i.val + 1)).map absLIdxL := by
        rw [← List.map_tail, List.tail_drop]
      have hstep : ∀ (fe' : arena.env.IFEnv) (lf' : IFEnv) st1 lst1 (i3 : Std.Usize),
          i3.val = i.val + 1 → IFEnvRelI P IEnv.empty fe' lf' →
          AStateRel₀ P st1 lst1 → AStateInv P st1 →
          LS P (IFEnvRelI P IEnv.empty)
            (arena.inductives.stored_install.stored_tables P st1 p guards i3 fe') lst1
            (storedTables (absBlockShape p)
              ((p.members.val.drop (i.val + 1)).map absMemberShape)
              ((guards.val.drop i.val).map absLIdxL).tail lf') := by
        intro fe' lf' st1 lst1 i3 hi3 hf hr hin
        have := ih _ hrest i3 fe' lf' st1 lst1 (by omega) hf hr hin
        rw [hi3] at this
        rw [htailg]
        exact this
      have hMc : (absMemberShape p.members.val[i.val]).ctors
          = absCtorsL p.members.val[i.val].ctors := rfl
      have hMi : (absMemberShape p.members.val[i.val]).nIdx
          = absU p.members.val[i.val].n_idx := rfl
      have hMn : (absMemberShape p.members.val[i.val]).cvT
          = absIConstantVal p.members.val[i.val].cv_t := rfl
      generalize absMemberShape p.members.val[i.val] = M at hMc hMi hMn ⊢
      by_cases h1 : alloc.vec.Vec.len (p.members.val[i.val]).ctors = 1#usize
      · rw [ite_eq_left h1]
        obtain ⟨c, hc, hca⟩ := absCtorsL_one h1
        rw [hMc, hca]
        by_cases h0 : (p.members.val[i.val]).n_idx = 0#u64
        · have h0' : (M.nIdx == 0) = true := by
            rw [hMi]; simp [h0, absU]
          rw [ite_eq_left h0]
          simp only [h0', ↓reduceIte]
          refine LS.bind_eq fun c' hc' => ?_
          obtain ⟨hb0, hc''⟩ := ExprOps.vecIndexAt hc'
          have hcc : c' = c := by rw [← hc'']; simp [hc]
          subst hcc
          obtain ⟨civ, cin⟩ := c'
          rw [hMn]
          refine LS.bind (struct_proj_bodies_ls hrel hinv) rfl (fun _ _ => errArm_ok) ?_
          rintro a b st1 lst1 hab hrel1 hinv1
          subst hab
          cases a with
          | none =>
            simp only [Option.map]
            refine LS.bind_eq fun i3 hi3 => ?_
            exact hstep fe lf st1 lst1 i3 (ConRon.Refine.HashMap.uscalar_add_eq hi3) hfe hrel1 hinv1
          | some bodies =>
            simp only [Option.map]
            refine LS.bind_eq fun gs hgs => ?_
            have hgsv : absLIdxL gs = ((guards.val.drop i.val).map absLIdxL).headD [] := by
              by_cases hg : i < alloc.vec.Vec.len guards
              · rw [ite_eq_left hg] at hgs
                obtain ⟨g0, hg0, hgs⟩ := ConRon.Refine.bind_eq_ok_iff.mp hgs
                obtain ⟨hgb, hg0'⟩ := ExprOps.vecIndexAt hg0
                have hgd := Lockstep.PA1.lidx_vec_dup_ls g0 _ hgs
                rw [hgd, ← hg0', List.drop_eq_getElem_cons hgb]
                rfl
              · rw [ite_eq_right hg] at hgs
                cases Result.ok_injective hgs
                have hgl : guards.val.length ≤ i.val := by
                  have := alloc.vec.Vec.len_val guards
                  scalar_tac
                rw [List.drop_eq_nil_of_le hgl]
                rfl
            refine LS.bind_eq fun nm hnm => ?_
            refine LS.bind_eq fun lps hlps => ?_
            refine LS.bind_eq fun n1 hn1 => ?_
            refine LS.bind_eq fun l hl' => ?_
            refine LS.bind_eq fun fe2 hfe2 => ?_
            refine LS.bind_eq fun i5 hi5 => ?_
            obtain rfl := dupId_nidx _ _ hnm
            obtain rfl := dupId_nidx _ _ hn1
            obtain rfl := dupId_lidx _ _ hl'
            obtain ⟨hR, -⟩ := ifenv_push_table_spec hfe _ _ hfe2
            refine LS.tail (hstep fe2 _ st1 lst1 i5 (ConRon.Refine.HashMap.uscalar_add_eq hi5) hR
              hrel1 hinv1) ?_ (fun _ _ h => h)
            have hlpse : (absBlockShape p).lps = absNIdxL lps := shape_lps_twin p _ hlps
            rw [← hgsv, hlpse]
            rfl
        · have h0' : ¬ (M.nIdx == 0) = true := by
            rw [hMi]
            simp only [beq_iff_eq, absU]
            intro hv
            exact h0 (UScalar.eq_imp _ _ (by simpa using hv))
          rw [ite_eq_right h0]
          simp only [h0']
          refine LS.bind_eq fun i3 hi3 => ?_
          exact hstep fe lf st lst i3 (ConRon.Refine.HashMap.uscalar_add_eq hi3) hfe hrel hinv
      · rw [ite_eq_right h1, hMc]
        split
        · rename_i c hc
          have hl : p.members.val[i.val].ctors.val.length = 1 := by
            simpa [absCtorsL] using congrArg List.length hc
          exact absurd (UScalar.eq_imp _ _ (by simpa using hl)) h1
        · refine LS.bind_eq fun i3 hi3 => ?_
          exact hstep fe lf st lst i3 (ConRon.Refine.HashMap.uscalar_add_eq hi3) hfe hrel hinv

@[lockstep] theorem stored_tables_ls {P st lst} (p : arena.inductives.block_parts.BlockShape)
    (guards : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))
    {fe : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI P IEnv.empty fe lf)
    (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st) :
    LS P (IFEnvRelI P IEnv.empty)
      (arena.inductives.stored_install.stored_tables P st p guards 0#usize fe) lst
      (storedTables (absBlockShape p) (absBlockShape p).members (absGuardsL guards) lf) := by
  have h := stored_tables_aux (P := P) p guards _ 0#usize fe lf st lst rfl hfe hrel hinv
  simpa [absBlockShape, absGuardsL] using h

/-! ## The constructors, and the last bracket -/

theorem stored_ctors_rel {E₀ : IEnv} {P} (n_p : Std.U64)
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (n : Nat) :
    ∀ (i : Std.Usize) (fe : arena.env.IFEnv) (lf : IFEnv) {o},
      ms.val.length - i.val = n → IFEnvRelI P E₀ fe lf →
      arena.inductives.stored_install.stored_ctors n_p ms i fe = ok o →
      IFEnvRelI P E₀ o (storedCtors (absU n_p) ((ms.val.drop i.val).map absMemberShape) lf) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i fe lf o hn hfe h
    rw [arena.inductives.stored_install.stored_ctors.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val ms
    by_cases hge : i ≥ alloc.vec.Vec.len ms
    · rw [ite_eq_left hge] at h
      have hle : ms.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hle, List.map_nil, storedCtors]
      exact hfe
    · rw [ite_eq_right hge] at h
      have hlt : i.val < ms.val.length := by scalar_tac
      obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb', hm'⟩ := ExprOps.vecIndexAt hm
      subst hm'
      obtain ⟨fe2, hfe2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have h1 := cons_sum_ctors_refines hfe.rel hfe.inv hfe2
      have hrec := ih (ms.val.length - i2.val) (by omega) i2 fe2 _ rfl h1 h
      rw [hi2v] at hrec
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, storedCtors]
      exact hrec

theorem stored_ctors_ls {E₀ : IEnv} {P} {fe : arena.env.IFEnv} {lf : IFEnv} {n_p : Std.U64}
    {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape}
    (hfe : IFEnvRelI P E₀ fe lf) {o}
    (h : arena.inductives.stored_install.stored_ctors n_p ms 0#usize fe = ok o) :
    IFEnvRelI P E₀ o (storedCtors (absU n_p) (ms.val.map absMemberShape) lf) := by
  simpa using stored_ctors_rel n_p ms _ 0#usize fe lf rfl hfe h

/-- **`stored_tail` ⊑ `storedTail`**: the constructors, the recursors and the tables pushed
in a bracket, and everything new promoted; what comes back extends what the block found,
provided the block's names were free there. -/
theorem stored_tail_refines {P st lst} {p : arena.inductives.block_parts.BlockShape}
    {guards : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {vis nt : Std.U64}
    {fe₁ : arena.env.IFEnv} {lf₁ A : IFEnv} {o}
    (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st) (hP : P.frozen = false)
    (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty fe₁ lf₁)
    (hA : EnvOK A) (hfree : BlockFree A (absBlockShape p))
    (hext : ExtR A ((absBlockShape p).members.map (·.cvT.name)) lf₁)
    (hvis : absU vis = A.visibleBelow) (hnt : absU nt = A.env.tables.length)
    (hrun : arena.inductives.stored_install.stored_tail st p guards vis nt fe₁ = ok o) :
    SimRel₀ (fun r v => IFEnvRelI P IEnv.empty r v ∧ EnvExt A v) P lst o
      (storedTail (absBlockShape p) (absGuardsL guards) (absU vis) (absU nt) lf₁) := by
  rw [arena.inductives.stored_install.stored_tail] at hrun
  obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (flush_caches_sim₀ hrel hinv h1).apply
  obtain ⟨⟨tier, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨htier, lst2, hx2, hrel2, hinv2⟩ := enter_scratch_rel hrel1 hinv1 hP h2
  have htf : tier.frozen = true := by rw [htier]; rfl
  have hpeT : PersEnvEmpty tier := by rw [htier]; exact persEnvEmpty_tierOf _
  have hfeT := IFEnvRelI.rebase hpe hpeT hfe
  obtain ⟨f, hf, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨fe2, hfe2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hR2 := stored_ctors_ls hfeT hfe2
  obtain ⟨⟨r3, st3⟩, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hS3 := stored_recs_ls fe2.visible_below p hR2 hrel2 hinv2 _ _ h3
  have hvis2 : absU fe2.visible_below = (storedCtors (absU p.n_p)
      (p.members.val.map absMemberShape) lf₁).visibleBelow := hR2.rel.visibleBelow.symm
  rw [hvis2] at hS3
  change Lockstep.LOut tier _ r3 st3 (StateT.run (storedRecs
    (storedCtors (absBlockShape p).nP (absBlockShape p).members lf₁).visibleBelow (absBlockShape p) 0
    (absBlockShape p).recs (storedCtors (absBlockShape p).nP (absBlockShape p).members lf₁)) lst2) at hS3
  simp only [SimRel₀, AOutRel₀]
  rw [storedTail, run_bind_ok hx1 _, run_bind_ok hx2 _]
  cases r3 with
  | Err e =>
    obtain ⟨st4, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    show AErrSim e _
    refine AErrSim.bind_run (AErrSim.scratchRun ?_) _
    exact AErrSim.bind_run hS3 _
  | Ok fe3 =>
    obtain ⟨v3, lst3, hx3, hv3, hrel3, hinv3⟩ := hS3
    obtain ⟨⟨r4, st4⟩, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hS4 := stored_tables_ls p guards hv3 hrel3 hinv3 _ _ h4
    cases r4 with
    | Err e =>
      obtain ⟨st5, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      show AErrSim e _
      refine AErrSim.bind_run (AErrSim.scratchRun ?_) _
      show AErrSim e (StateT.run (_ >>= _) lst2)
      rw [run_bind_ok hx3 _]
      exact hS4
    | Ok fe4 =>
      obtain ⟨v4, lst4, hx4, hv4, hrel4, hinv4⟩ := hS4
      have hxc : StateT.run (do
          let fe₂ := storedCtors (absBlockShape p).nP (absBlockShape p).members lf₁
          let vis₂ := fe₂.visibleBelow
          let fe₃ ← storedRecs vis₂ (absBlockShape p) 0 (absBlockShape p).recs fe₂
          storedTables (absBlockShape p) (absBlockShape p).members (absGuardsL guards) fe₃
          : AM IFEnv) lst2 = .ok (v4, lst4) := by
        show StateT.run (_ >>= _) lst2 = _
        rw [run_bind_ok hx3 _]
        exact hx4
      have hpush := storedTail_pushes hA (absBlockShape p) (absGuardsL guards) hfree hext lst2 _ _ hxc
      obtain ⟨st5, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨lst5, hx5, hrel5, hinv5⟩ := stored_frame_ok htf hrel2 hinv2 hrel4 hinv4 hf h5 hxc
      rw [run_bind_ok hx5 _]
      obtain ⟨kk, hkk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hkv : kk.val = fe4.visible_below.val - vis.val :=
        ConRon.Refine.HashMap.uscalar_sub_eq hkk
      obtain ⟨i3, hi3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi3v : i3.val = fe4.env.tables.val.length := by
        simp only [lift, Result.ok.injEq] at hi3
        subst hi3
        rw [usize_cast_u64_val']
        simp [alloc.vec.Vec.len]
      obtain ⟨kt, hkt, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hktv : kt.val = fe4.env.tables.val.length - nt.val := by
        rw [ConRon.Refine.HashMap.uscalar_sub_eq hkt, hi3v]
      have hkabs : v4.visibleBelow - absU vis = absU kk := by
        rw [hv4.rel.visibleBelow]; simp only [absU]; omega
      have hv4t : v4.env.tables.length = fe4.env.tables.val.length := by
        rw [hv4.rel.env]; simp [overEnv, IEnv.empty]
      have hktabs : v4.env.tables.length - absU nt = absU kt := by
        rw [hv4t]; simp only [absU]; omega
      have hk : absU kk ≤ fe4.env.consts.val.length := by
        obtain ⟨new, e₁, l₁, -⟩ := hpush.ext.newC
        have hl : v4.env.consts.length = fe4.env.consts.val.length := by
          rw [hv4.rel.env]; simp [overEnv, IEnv.empty]
        rw [← hkabs, hvis, ← l₁, ← hl, e₁]
        simp
      have hktle : absU kt ≤ fe4.env.tables.val.length := by simp only [absU]; omega
      obtain ⟨pm, hpm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨⟨r6, tier1⟩, h6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hPr := promote_new_drop (lm := PMemo.empty) htf hrel5 hinv5
        (pmemo_empty_refines hpm) (hv4.rel.toOwn hpeT) hv4.inv hk hktle h6
      rw [core_walk_fuel_abs, ← hkabs, ← hktabs] at hPr
      cases r6 with
      | Err e =>
        obtain ⟨st7, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        show AErrSim e _
        exact AErrSim.bind_run hPr _
      | Ok q6 =>
        obtain ⟨_, fe5⟩ := q6
        obtain ⟨st7, h7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        obtain ⟨w, lst6, hx6, ⟨⟨-, hw, hkc, hkt'⟩, htf1⟩, hrel6, hinv6⟩ := hPr
        obtain ⟨lst7, hx7, hrel7, hinv7⟩ := (drop_scratch_rel hrel6 hinv6 htf1 h7 hP).apply
        refine ⟨w.2, lst7, ?_, ⟨⟨hw.1.toRel hpe, hw.2⟩, ?_⟩, hrel7, hinv7⟩
        · refine (run_bind_ok hx6 _).trans ((run_bind_ok hx7 _).trans rfl)
        · refine envExt_promoted hpush.ext hA hv4.rel hw.1 hkc hkt' ?_ ?_ (s := lst5) (s' := lst6) hx6
          · rw [hvis]
          · rw [hnt]

/-! ## The names of a block -/

theorem stored_names_free_abs {P : arena.store.PersTier} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hctx : CoreCtx P vis rf lf) (ns : alloc.vec.Vec arena.handle.NIdx) (n : Nat) :
    ∀ (i : Std.Usize) {o : Bool}, ns.val.length - i.val = n →
      arena.inductives.stored_install.stored_names_free P vis rf ns i = ok o →
      o = namesFree lf ((ns.val.drop i.val).map absNIdx) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i o hn h
    rw [arena.inductives.stored_install.stored_names_free.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val ns
    by_cases hge : i ≥ alloc.vec.Vec.len ns
    · rw [ite_eq_left hge] at h
      have hle : ns.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hle]
      rfl
    · rw [ite_eq_right hge] at h
      have hlt : i.val < ns.val.length := by scalar_tac
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb', hx'⟩ := ExprOps.vecIndexAt hx
      subst hx'
      obtain ⟨oc, hoc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hf := ifenv_find_abs hctx hoc
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, namesFree, List.all_cons, ← namesFree,
        ← hf]
      cases oc with
      | some ci =>
        simp only [core.option.Option.is_some, Option.isSome_some, ↓reduceIte] at h
        cases Result.ok_injective h
        rfl
      | none =>
        simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hrec := ih (ns.val.length - i2.val) (by omega) i2 rfl h
        rw [hi2v] at hrec
        simpa using hrec

/-- `rec_names` appends the recursors' names. -/
theorem stored_rec_names_abs (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape) (n : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) {o}, rs.val.length - i.val = n →
      arena.inductives.stored_install.rec_names rs i out = ok o →
      absNIdxL o = absNIdxL out ++ ((rs.val.drop i.val).map absRecShape).map (·.cvR.name) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i out o hn h
    rw [arena.inductives.stored_install.rec_names.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val rs
    by_cases hge : i ≥ alloc.vec.Vec.len rs
    · rw [ite_eq_left hge] at h
      have hle : rs.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      simp [List.drop_eq_nil_of_le hle]
    · rw [ite_eq_right hge] at h
      have hlt : i.val < rs.val.length := by scalar_tac
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb', hx'⟩ := ExprOps.vecIndexAt hx
      subst hx'
      obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi1
      have hrec := ih (rs.val.length - i1.val) (by omega) i1 o1 rfl h
      rw [hrec, hi1v]
      obtain rfl := dupId_nidx _ _ hy
      rw [absNIdxL, ConRon.Refine.vec_push_val ho1, List.drop_eq_getElem_cons hlt]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, absNIdxL]
      rfl

@[lockstep] theorem rec_names_spec (rs : alloc.vec.Vec arena.inductives.block_parts.RecShape)
    (out : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.inductives.stored_install.rec_names rs 0#usize out)
      (fun o => absNIdxL o = absNIdxL out ++ (rs.val.map absRecShape).map (·.cvR.name)) := by
  intro o h
  simpa using stored_rec_names_abs rs _ 0#usize out rfl h

/-- `LS` with what the twin's `Post` says of its answer. -/
theorem LS.post {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop} {Q : β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R m lst x) (hp : Post x Q) :
    LS pers (fun a b => R a b ∧ Q b) m lst x := by
  intro o st' hm
  have h1 := h o st' hm
  cases o with
  | Err e => exact h1
  | Ok a =>
    obtain ⟨b, lst', hx, h2, h3, h4⟩ := h1
    exact ⟨b, lst', hx, ⟨h2, hp lst b lst' hx⟩, h3, h4⟩

/-- `withSort` keeps the members and the recursors. -/
theorem withSort_post (p : BlockShape) (s : LIdx) :
    Post (p.withSort s) (fun q => q.members = p.members ∧ q.recs = p.recs) := by
  rw [BlockShape.withSort]
  exact Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ =>
    Post.pure ⟨rfl, rfl⟩

/-- **What a block's names' test gives**. -/
theorem blockFree_of_names {A : IFEnv} (hA : EnvOK A) (p : BlockShape)
    (h : namesFree A (p.memberNames ++ p.allCtors.map (·.1.name) ++ p.recs.map (·.cvR.name)) = true) :
    BlockFree A p := by
  have hall : ∀ n ∈ p.memberNames ++ p.allCtors.map (·.1.name) ++ p.recs.map (·.cvR.name),
      A.idx[n]? = none := by
    intro n hn
    have := List.all_eq_true.mp h n hn
    exact hA.free (by simpa using this)
  refine ⟨fun m hm => hall _ ?_, fun m hm c hc => hall _ ?_, fun rc hrc => hall _ ?_⟩
  · simp only [List.mem_append]
    exact Or.inl (Or.inl (List.mem_map_of_mem hm))
  · simp only [List.mem_append]
    refine Or.inl (Or.inr (List.mem_map.mpr ⟨c, ?_, rfl⟩))
    simp only [BlockShape.allCtors, List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨m, hm, rfl⟩, hc⟩
  · simp only [List.mem_append]
    exact Or.inr (List.mem_map_of_mem hrc)

/-- `stored_parts_push`: past the formers' reading, pushed with their capability records,
the guards, and the last bracket. -/
theorem stored_parts_push_refines {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} {p : arena.inductives.block_parts.BlockShape}
    {is_rec : Bool} {cv_ts : alloc.vec.Vec arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st) (hP : P.frozen = false)
    (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf) (hok : EnvOK lf)
    (hfree : BlockFree lf (absBlockShape p))
    (hnames : (absICVL cv_ts).map (·.name) = (absBlockShape p).members.map (·.cvT.name))
    (hrun : arena.inductives.stored_install.stored_parts_push P st mode rf p is_rec cv_ts = ok o) :
    SimRel₀ (fun r v => IFEnvRelI P IEnv.empty r v ∧ EnvExt lf v) P lst o
      (do
        let fe₁ ← consBlockInds (absBlockShape p) is_rec (absICVL cv_ts) 0 lf
        let guards ← storedGuardsAll (ConRon.Refine.absMode mode) fe₁ (absBlockShape p)
          (absBlockShape p).members
        storedTail (absBlockShape p) guards lf.visibleBelow lf.env.tables.length fe₁) := by
  rw [arena.inductives.stored_install.stored_parts_push] at hrun
  obtain ⟨nt, hnt, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hntv : nt.val = rf.env.tables.val.length := by
    simp only [lift, Result.ok.injEq] at hnt
    subst hnt
    rw [usize_cast_u64_val']
    simp [alloc.vec.Vec.len]
  have hlt : lf.env.tables.length = rf.env.tables.val.length := by
    rw [hfe.rel.env]; simp [overEnv, IEnv.empty]
  obtain ⟨⟨r1, st1⟩, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hC := cons_block_inds_ls (pers := P) (E₀ := IEnv.empty) p is_rec cv_ts 0#usize rf lf st lst
    hfe hrel hinv _ _ h1
  simp only [absICVLFrom_zero] at hC
  simp only [SimRel₀, AOutRel₀]
  cases r1 with
  | Err e =>
    cases Result.ok_injective hrun
    exact AErrSim.bind_run hC _
  | Ok fe1 =>
    obtain ⟨v1, lst1, hx1a, hv1, hrel1, hinv1⟩ := hC
    have hx1 : StateT.run (consBlockInds (absBlockShape p) is_rec (absICVL cv_ts) 0 lf) lst
        = .ok (v1, lst1) := hx1a
    have hE0 : ExtR lf [] lf := ⟨EnvExt.refl hok, by simp⟩
    have hE1 := consBlockInds_ext (A := lf) (absBlockShape p) is_rec (absICVL cv_ts) 0 [] lf hE0
      (fun cv hcv => by
        have hm : cv.name ∈ (absICVL cv_ts).map (·.name) := List.mem_map_of_mem hcv
        rw [hnames] at hm
        obtain ⟨m, hm', he⟩ := List.mem_map.mp hm
        rw [← he]
        exact hfree.members m hm') lst _ _ hx1
    have hE1' : ExtR lf ((absBlockShape p).members.map (·.cvT.name)) v1 := by
      refine ⟨hE1.ext, fun T hT => hE1.rows T ?_⟩
      rw [List.append_nil, hnames]
      exact hT
    obtain ⟨⟨r2, st2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hG := stored_guards_all_ls hrel1 hinv1 hP hpe hv1 p _ _ h2
    rw [run_bind_ok hx1 _]
    cases r2 with
    | Err e =>
      cases Result.ok_injective hrun
      exact AErrSim.bind_run hG _
    | Ok guards =>
      obtain ⟨g, lst2, hx2, hg, hrel2, hinv2⟩ := hG
      subst hg
      rw [run_bind_ok hx2 _]
      have hT := stored_tail_refines hrel2 hinv2 hP hpe hv1 hok hfree hE1'
        hfe.rel.visibleBelow.symm (by rw [hlt, ← hntv]) hrun
      rw [hfe.rel.visibleBelow, show lf.env.tables.length = absU nt by rw [hlt, ← hntv]]
      exact hT

/-- **`stored_parts` ⊑ `storedParts`**: the scratch flag, the names' test, the formers. -/
theorem stored_parts_ls {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st)
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (hok : EnvOK lf) (p0 : arena.inductives.block_parts.BlockParts) :
    LS P (fun r v => IFEnvRelI P IEnv.empty r v ∧ EnvExt lf v)
      (arena.inductives.stored_install.stored_parts P st mode rf p0) lst
      (storedParts (ConRon.Refine.absMode mode) lf (absBlockParts p0)) := by
  have hflag : lst.store.scratchOn = st.store.scratch_on := hrel.store.scratchOn
  have hctx := IFEnvInv.coreCtxSelf hfe.rel hfe.inv
  rw [arena.inductives.stored_install.stored_parts, storedParts]
  refine LS.twin_get_bind ?_
  cases hf : st.store.scratch_on with
  | true =>
    simp only [↓reduceIte]
    refine LS.bind_eq fun _ _ => LS.bind_eq fun _ _ => LS.bind_eq fun r hr => ?_
    simp only [arena.monad.fail, Result.ok.injEq] at hr
    subst hr
    refine LS.err ?_
    simp only [hflag, hf, ↓reduceIte]
    exact AErrSim.bind_run (AErrSim.internal rfl) _
  | false =>
    simp only [hflag, hf, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine LS.bind_eq fun v hv => ?_
    refine LS.bind_eq fun v1 hv1 => ?_
    refine LS.bind_eq fun v2 hv2 => ?_
    refine LS.bind_eq fun names hnames => ?_
    have e0 : absCtorsL v = (absBlockShape p0.shape).allCtors := by
      have := all_ctors_twin0 p0.shape _ hv
      exact this.symm
    have e1 : absNIdxL v1 = (absBlockShape p0.shape).memberNames :=
      (shape_member_names_twin p0.shape _ hv1).symm
    have e2 : absNIdxL v2 = absNIdxL v1 ++ (absCtorsL v).map (·.1.name) := by
      rw [ctor_name_list_abs _ _ _ hv2]
      simp [absCtorsL, absIConstantVal]
    have e3 := rec_names_spec _ _ _ hnames
    have hn : names.val.map absNIdx = (absBlockParts p0).shape.memberNames ++
        (absBlockParts p0).shape.allCtors.map (·.1.name) ++
        (absBlockParts p0).shape.recs.map (·.cvR.name) := by
      have : absNIdxL names = _ := e3
      rw [e2, e1, e0] at this
      exact this
    refine LS.bind_eq fun b hb => ?_
    have hbe := name_nodup_refines hb
    simp only [absNIdxL] at hbe
    rw [hn] at hbe
    generalize hL : (absBlockParts p0).shape.memberNames ++
        (absBlockParts p0).shape.allCtors.map (·.1.name) ++
        (absBlockParts p0).shape.recs.map (·.cvR.name) = L at hn hbe ⊢
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine LS.bind_eq fun _ _ => LS.bind_eq fun _ _ => LS.bind_eq fun r hr => ?_
      simp only [arena.monad.fail, Result.ok.injEq] at hr
      subst hr
      refine LS.err ?_
      rw [← hbe]
      exact AErrSim.internal rfl
    | true =>
      simp only [↓reduceIte]
      refine LS.bind_eq fun b1 hb1 => ?_
      have hb1e : b1 = namesFree lf L := by
        have := stored_names_free_abs hctx names _ 0#usize rfl hb1
        rw [← hn]
        simpa using this
      cases b1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine LS.bind_eq fun _ _ => LS.bind_eq fun _ _ => LS.bind_eq fun r hr => ?_
        simp only [arena.monad.fail, Result.ok.injEq] at hr
        subst hr
        refine LS.err ?_
        rw [← hbe, ← hb1e]
        exact AErrSim.internal rfl
      | true =>
        simp only [↓reduceIte]
        rw [← hbe, ← hb1e]
        simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        have hfree : BlockFree lf (absBlockShape p0.shape) := by
          refine blockFree_of_names hok _ ?_
          show namesFree lf ((absBlockParts p0).shape.memberNames ++
            (absBlockParts p0).shape.allCtors.map (·.1.name) ++
            (absBlockParts p0).shape.recs.map (·.cvR.name)) = true
          rw [hL, ← hb1e]
        refine LS.bind_eq fun l hl => ?_
        obtain rfl := dupId_lidx _ _ hl
        refine LS.bind (LS.post (stored_formers_ls hrel hinv hP hpe hfe p0.shape p0.shape.res_sort)
          (storedFormers_names _ _ _ _ _ _ _)) rfl (fun _ _ => errArm_ok) ?_
        rintro ⟨cv_ts, s0⟩ ⟨lcv, ls0⟩ st1 lst1 ⟨⟨hc1, hc2⟩, hc3⟩ hrel1 hinv1
        simp only at hc1 hc2 hc3
        subst hc1 hc2
        refine LS.bind_eq fun bs hbs => ?_
        have hbse : absBlockShape p0.shape = absBlockShape bs := block_shape_dup_twin p0.shape _ hbs
        refine LS.bind (LS.post (with_sort_ls hrel1 hinv1 bs s0) (withSort_post _ _))
          (by rw [← hbse]; rfl) (fun _ _ => errArm_ok) ?_
        rintro p1 lp st2 lst2 ⟨hp1, hm1, hrc1⟩ hrel2 hinv2
        subst hp1
        rw [← hbse] at hm1 hrc1
        refine LS.bind_eq fun r2 hr2 => ?_
        have hR := block_raw_rec_ls hrel2 hinv2 p0 r2 hr2
        cases r2 with
        | Err e => exact LS.err (AErrSim.bind_run hR _)
        | Ok is_rec =>
          obtain ⟨b', lst3, hx3, hb', hrel3, hinv3⟩ := hR
          subst hb'
          have hfree' : BlockFree lf (absBlockShape p1) := by
            refine ⟨?_, ?_, ?_⟩
            · rw [hm1]; exact hfree.members
            · rw [hm1]; exact hfree.ctors
            · rw [hrc1]; exact hfree.recs
          have hnames' : (absICVL cv_ts).map (·.name)
              = (absBlockShape p1).members.map (·.cvT.name) := by
            rw [hm1]
            simpa using hc3
          intro o st' hm
          have hT := stored_parts_push_refines hrel3 hinv3 hP hpe hfe hok hfree' hnames' hm
          simp only [SimRel₀] at hT
          show Lockstep.LOut P _ o st' (StateT.run (_ >>= _) lst2)
          rw [run_bind_ok hx3 _]
          cases o with
          | Err e => exact hT
          | Ok a =>
            obtain ⟨v, lst', hx, hrR, hr1, hr2⟩ := hT
            exact ⟨v, lst', hx, hrR, hr1, hr2⟩

/-- `stored_push_all`: a pinned block's constants, pushed in order. -/
theorem stored_push_all_rel {P} (decls : alloc.vec.Vec arena.env.IConstantInfo)
    (hwf : ∀ c ∈ decls.val, IConstantInfoWF c) (n : Nat) :
    ∀ (i : Std.Usize) (fe : arena.env.IFEnv) (lf : IFEnv) {o},
      decls.val.length - i.val = n → IFEnvRelI P IEnv.empty fe lf →
      arena.inductives.stored_install.stored_push_all decls i fe = ok o →
      IFEnvRelI P IEnv.empty o (((decls.val.drop i.val).map absIConstantInfo).foldl IFEnv.push lf) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i fe lf o hn hfe h
    rw [arena.inductives.stored_install.stored_push_all.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val decls
    by_cases hge : i ≥ alloc.vec.Vec.len decls
    · rw [ite_eq_left hge] at h
      have hle : decls.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hle]
      exact hfe
    · rw [ite_eq_right hge] at h
      have hlt : i.val < decls.val.length := by scalar_tac
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb', hx'⟩ := ExprOps.vecIndexAt hx
      subst hx'
      obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨fe2, hfe2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hdv := i_constant_info_dup_abs hd
      have hdwf := i_constant_info_dup_wf hd (hwf _ (List.getElem_mem _))
      have h1 := ifenv_push_refines hfe.rel hfe.inv hdwf hfe2
      have hrec := ih (decls.val.length - i2.val) (by omega) i2 fe2 _ rfl h1 h
      rw [hi2v, hdv] at hrec
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldl_cons]
      exact hrec

/-- The pinned install's extension: every name checked free. -/
theorem foldl_push_ext {A : IFEnv} : ∀ (L : List IConstantInfo) (b : IFEnv), EnvExt A b →
    (∀ c ∈ L, A.idx[c.name]? = none) → EnvExt A (L.foldl IFEnv.push b)
  | [], _, h, _ => h
  | c :: cs, b, h, hf =>
    foldl_push_ext cs _ (h.push (hf c (by simp))) (fun x hx => hf x (List.mem_cons_of_mem _ hx))

/-- `i_constant_info_names_from`, the block's names. -/
theorem names_from_abs (block : alloc.vec.Vec arena.env.IConstantInfo) (n : Nat) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.handle.NIdx) {o}, block.val.length - i.val = n →
      arena.env.i_constant_info_names_from block i out = ok o →
      absNIdxL o = absNIdxL out ++ ((block.val.drop i.val).map absIConstantInfo).map (·.name) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i out o hn h
    rw [arena.env.i_constant_info_names_from.eq_def] at h
    dsimp only at h
    have hl := alloc.vec.Vec.len_val block
    by_cases hge : i ≥ alloc.vec.Vec.len block
    · rw [ite_eq_left hge] at h
      have hle : block.val.length ≤ i.val := by scalar_tac
      cases Result.ok_injective h
      simp [List.drop_eq_nil_of_le hle]
    · rw [ite_eq_right hge] at h
      have hlt : i.val < block.val.length := by scalar_tac
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb', hx'⟩ := ExprOps.vecIndexAt hx
      subst hx'
      obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi1
      have hrec := ih (block.val.length - i1.val) (by omega) i1 o1 rfl h
      rw [hrec, hi1v, absNIdxL, ConRon.Refine.vec_push_val ho1, List.drop_eq_getElem_cons hlt]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, absNIdxL, i_constant_info_name_abs hy]

/-- **`stored_install` ⊑ `storedInstall`**, with what the fold carries: the install extends
what the block found. -/
@[lockstep] theorem stored_install_ls {P st lst} {mode : kernel.env.CheckMode}
    {rf : arena.env.IFEnv} {lf : IFEnv} (hrel : AStateRel₀ P st lst) (hinv : AStateInv P st)
    (hP : P.frozen = false) (hpe : PersEnvEmpty P) (hfe : IFEnvRelI P IEnv.empty rf lf)
    (hok : EnvOK lf) (block : alloc.vec.Vec arena.env.IConstantInfo) (n_p : Std.U64) :
    LS P (fun r v => IFEnvRelI P IEnv.empty r v ∧ EnvExt lf v)
      (arena.inductives.stored_install.stored_install P st mode rf block n_p) lst
      (storedInstall (ConRon.Refine.absMode mode) lf (absICIL block) (absU n_p)) := by
  rw [arena.inductives.stored_install.stored_install, storedInstall]
  have hctx := IFEnvInv.coreCtxSelf hfe.rel hfe.inv
  lockstep
  · exact LS.pure ⟨hfe, EnvExt.refl hok⟩ ‹_› ‹_›
  · exact stored_parts_ls ‹_› ‹_› hP hpe hfe hok _
  · rename_i kind
    intro o st' hm
    obtain ⟨⟨r1, st2⟩, h1, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hS := basis_kind_decls_a_refines hrel hinv h1
    simp only [Sim₀, AOut₀] at hS
    show Lockstep.LOut P _ o st' (StateT.run (_ >>= _) lst1)
    cases r1 with
    | Err e =>
      cases Result.ok_injective hm
      exact AErrSim.bind_run hS _
    | Ok decls =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hS
      rw [run_bind_ok hx2 _]
      have hflag : lst2.store.scratchOn = st2.store.scratch_on := hrel2.store.scratchOn
      have hw := basis_kind_decls_a_wf h1
      change (if st2.store.scratch_on = true then _ else _) = _ at hm
      change Lockstep.LOut P _ o st' (StateT.run
        (if lst2.store.scratchOn = true then _ else _) lst2)
      rw [hflag]
      cases hf : st2.store.scratch_on with
      | true =>
        simp only [hf, ↓reduceIte] at hm ⊢
        obtain ⟨_, -, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
        obtain ⟨_, -, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
        obtain ⟨r, hr, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
        simp only [arena.monad.fail, Result.ok.injEq] at hr
        subst hr
        cases Result.ok_injective hm
        exact AErrSim.bind_run (AErrSim.internal rfl) _
      | false =>
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hm ⊢
        obtain ⟨names, hnames, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
        obtain ⟨b, hb, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
        have hna : names.val.map absNIdx = (absICIL decls).map (·.name) := by
          have := names_from_abs decls _ 0#usize _ rfl hnames
          simpa [absNIdxL, absICIL, alloc.vec.Vec.new] using this
        have hbe : b = namesFree lf ((absICIL decls).map (·.name)) := by
          have := stored_names_free_abs hctx names _ 0#usize rfl hb
          rw [← hna]
          simpa using this
        rw [← hbe]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hm ⊢
          obtain ⟨_, -, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
          obtain ⟨_, -, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
          obtain ⟨r, hr, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
          simp only [arena.monad.fail, Result.ok.injEq] at hr
          subst hr
          cases Result.ok_injective hm
          exact AErrSim.internal rfl
        | true =>
          simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true] at hm ⊢
          obtain ⟨i, hi, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
          cases Result.ok_injective hm
          have hR := stored_push_all_rel decls hw _ 0#usize rf lf rfl hfe hi
          simp only [Std.UScalar.val] at hR
          refine ⟨_, lst2, rfl, ⟨?_, ?_⟩, hrel2, hinv2⟩
          · simpa [absICIL] using hR
          · refine foldl_push_ext _ _ (EnvExt.refl hok) fun c hc => hok.free ?_
            have := List.all_eq_true.mp hbe.symm c.name (List.mem_map_of_mem hc)
            simpa using this

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.stored_install_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stored_install_ls

end ConRon.Refine2
