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

private theorem nidx_vec_beq_abs {a b : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (h : arena.canon.nidx_vec_beq a b 0#usize = ok o) :
    o = (a.val.map absNIdx == b.val.map absNIdx) := by
  rw [nidx_vec_beq_refines h]
  simp [absNIdxLFrom]

private theorem lidx_vec_beq_abs {a b : alloc.vec.Vec arena.handle.LIdx} {o : Bool}
    (h : arena.canon.lidx_vec_beq a b 0#usize = ok o) :
    o = (a.val.map absLIdx == b.val.map absLIdx) := by
  rw [lidx_vec_beq_refines h]
  simp [absLIdxLFrom]

private theorem eidx_vec_beq_abs {a b : alloc.vec.Vec arena.handle.EIdx} {o : Bool}
    (h : arena.canon.eidx_vec_beq a b 0#usize = ok o) :
    o = (a.val.map absEIdx == b.val.map absEIdx) := by
  rw [eidx_vec_beq_refines h]
  simp [absEIdxLFrom]

theorem i_constant_val_beq_p_abs {a b : arena.env.IConstantVal} {o : Bool}
    (h : arena.inductives.stored_install.i_constant_val_beq_p a b = ok o) :
    o = (absIConstantVal a).beqP (absIConstantVal b) := by
  rw [arena.inductives.stored_install.i_constant_val_beq_p] at h
  obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [IConstantVal.beqP, absIConstantVal]
  rw [← nidx_beq_abs h1]
  refine and_step h fun _ h => ?_
  obtain ⟨b2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← nidx_vec_beq_abs h2]
  refine and_step h fun _ h => ?_
  exact eidx_beq_abs h

theorem i_rec_rule_fire_beq_p_abs {a b : arena.env.IRecRuleFire} {o : Bool}
    (h : arena.inductives.stored_install.i_rec_rule_fire_beq_p a b = ok o) :
    o = (absIRecRuleFire a).beqP (absIRecRuleFire b) := by
  rw [arena.inductives.stored_install.i_rec_rule_fire_beq_p] at h
  cases a <;> cases b <;> simp only [absIRecRuleFire, IRecRuleFire.beqP] at h ⊢
  · exact (Result.ok_injective h).symm
  · exact (Result.ok_injective h).symm
  · exact (Result.ok_injective h).symm
  · obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← lidx_vec_beq_abs h1]
    refine and_step h fun _ h => ?_
    exact eidx_vec_beq_abs h

theorem i_rec_rule_beq_p_abs {a b : arena.env.IRecRule} {o : Bool}
    (h : arena.inductives.stored_install.i_rec_rule_beq_p a b = ok o) :
    o = (absIRecRule a).beqP (absIRecRule b) := by
  rw [arena.inductives.stored_install.i_rec_rule_beq_p] at h
  obtain ⟨b1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [IRecRule.beqP, absIRecRule]
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
  simpa using (Result.ok_injective h).symm

theorem listBeqBy_map {α β : Type} (f : β → β → Bool) (g : α → β) :
    ∀ (xs ys : List α), listBeqBy f (xs.map g) (ys.map g) =
      listBeqBy (fun a b => f (g a) (g b)) xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp [listBeqBy, listBeqBy_map f g xs ys]

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
    exact hK
  · rw [hc.env, hbe]
    simp only [absIEnv, List.map_reverse, List.map_map]
    congr 1
    exact hT

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
    simp only [am_run_bind]
    cases r1 with
    | Err e =>
      obtain ⟨st5, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      exact AErrSim.bind hE _
    | Ok p1 =>
      obtain ⟨m, ty2⟩ := p1
      obtain ⟨⟨vm, vty⟩, lst5, hx5, ⟨⟨hvm, hvty⟩, htf1⟩, hrel5, hinv5⟩ := hE
      simp only [hx5, except_ok_bind]
      obtain ⟨⟨r2, tier2⟩, h6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hL := promote_l_frozen htf1 hrel5 hinv5 hvm h6
      rw [core_walk_fuel_abs] at hL
      cases r2 with
      | Err e =>
        obtain ⟨st6, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        exact AErrSim.bind hL _
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
        · simp only [hx6, except_ok_bind, am_run_bind, hx7]
          rfl
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
  all_goals first
    | exact hslow ‹_› ‹_›
    | (refine LS.pure ?_ ‹_› ‹_›; simp [absTeleOpt, absIConstantVal])

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
      obtain ⟨-, hms⟩ := ExprOps.vecIndexAt hms
      subst hms
      refine LS.bind_eq fun k hk => ?_
      have hkv : k.val = p.n_p.val + p.members.val[i.val].n_idx.val :=
        ConRon.Refine.HashMap.uscalar_add_eq hk
      refine LS.bind (stored_tele_ls hrel hinv hP hpe hfe _ k) ?_ ?_
      · sorry
      · sorry

end ConRon.Refine2
