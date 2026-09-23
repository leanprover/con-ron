/-
# `ConRon.Refine2.Core.LS.Leaves` — region A1: the environment / level / name leaves

Task #97-P5-Core round 5, region A1.  The Theorem-2 lockstep lemmas of the
leaves every Core body calls: the pinned constants (`emptyLevels`,
`zeroLevel`, `sortOne`, `constE`), the cached level verdicts (`lvlEq?`,
`lvlsEq?`), the instantiated-constant caches (`constTyAt`, `ruleRhsAt`), the
error at an unknown constant, and the small head / name predicates.

Statement convention: the brief's (`LS pers (fun a b => b = <abs> a) (rust) lst
(twin)`); a Rust reader that returns no state (`empty_levels`, `zero_level`,
…) is stated in `LSR`, a pure Rust function (`quick_pair`, `rec_rule_k`,
`find_rule`) as an equation.
-/
import ConRon.Refine2.Core.LS.PrimsA1

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PA1

/-! ## Local condition correspondences -/

theorem bne_eq_not_beq' {α : Type} [BEq α] (a b : α) : (a != b) = !(a == b) := rfl

attribute [local lockstep_simp] bne_eq_not_beq' Bool.not_eq_true' Bool.not_true Bool.not_false
  ite_self

/-- A `usize` compared with a `Vec`'s length is the twin's `==` on the
abstracted length. -/
theorem decide_usize_eq_len {α : Type} (u : Std.Usize) (v : alloc.vec.Vec α) :
    decide (u = alloc.vec.Vec.len v) = (absSz u == v.val.length) := by
  by_cases h : u = alloc.vec.Vec.len v
  · subst h; simp [absSz, alloc.vec.Vec.len_val]
  · have : absSz u ≠ v.val.length := by
      intro hc; apply h; apply Aeneas.Std.UScalar.eq_imp
      rw [alloc.vec.Vec.len_val]; exact hc
    simp [h, this]

theorem absIConstantVal_levelParams_length (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams.length = cv.level_params.val.length := by
  simp [absIConstantVal]

attribute [local lockstep_simp] decide_usize_eq_len absIConstantVal_levelParams_length

/-! ## The pinned constants -/

@[lockstep] theorem empty_levels_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a) (arena.core.empty_levels st) st lst emptyLevels := by
  rw [arena.core.empty_levels, emptyLevels]; exact pin_empty_levels_ls hrel hinv

@[lockstep] theorem zero_level_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.core.zero_level st) st lst zeroLevel := by
  rw [arena.core.zero_level, zeroLevel]; exact pin_zero_level_ls hrel hinv

@[lockstep] theorem sort_one_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a) (arena.core.sort_one st) st lst sortOne := by
  rw [arena.core.sort_one, sortOne]; exact pin_sort_one_ls hrel hinv

@[lockstep] theorem const_e_ls {pers st n lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.const_e pers st n) lst
      (constE (absNIdx n)) := by
  rw [arena.core.const_e, constE]
  lockstep_core

/-! ## The error at an unknown constant

The answer is a `CheckError` on both sides; messages are never compared
(DESIGN §3.1), so the relation is the error KIND. -/

@[lockstep] theorem unknown_const_error_ls {pers st n lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => absAErrKind a = lAErrKind b) (arena.core.unknown_const_error st n) lst
      (unknownConstError (absNIdx n)) := by
  rw [arena.core.unknown_const_error, unknownConstError]
  lockstep_core
  all_goals trace_state
  all_goals sorry

/-! ## The bodies' small helpers -/

/-- `lift_fueled` is monomorphic at `Option Bool` with the message baked in;
the twin's `what` is free (messages are never compared). -/
@[lockstep] theorem lift_fueled_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (o : Option Bool) (what : String) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst (liftFueled what o) := by
  intro r hr
  cases o with
  | some a =>
    simp only [arena.core.lift_fueled] at hr
    cases Result.ok_injective hr
    exact ⟨a, lst, rfl, rfl, hrel, hinv⟩
  | none =>
    simp only [arena.core.lift_fueled] at hr
    obtain ⟨s, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    obtain ⟨v, -, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    rw [fail_run hr]
    exact AErrSim.internal rfl

@[lockstep] theorem is_ctor_app_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.is_ctor_app pers vis st fe e) lst
      (isCtorApp lfe (absEIdx e)) := by
  rw [arena.core.is_ctor_app, isCtorApp]
  lockstep_core

/-- `quick_pair` is pure on both sides: four tag comparisons. -/
@[lockstep] theorem quick_pair_ls (a b : arena.handle.EIdx) :
    LSP (arena.core.quick_pair a b) (fun r => r = quickPair (absEIdx a) (absEIdx b)) := by
  intro r h
  rw [arena.core.quick_pair] at h
  obtain ⟨ta, hta, h'⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  clear h
  obtain ⟨tb, htb⟩ : ∃ tb, arena.handle.EIdx.tag b = ok tb := by
    rw [arena.handle.EIdx.tag, arena.handle.word_tag]
    obtain ⟨z, hz, -⟩ := Aeneas.Std.UScalar.div_spec b.word
      (y := arena.handle.TAG_SPAN) (by rw [arena.handle.TAG_SPAN]; decide)
    exact ⟨z, hz⟩
  have ha := eidx_tag_abs hta
  have hb := eidx_tag_abs htb
  simp only [htb, bind_tc_ok] at h'
  simp only [quickPair, ha, hb, absU32_beq_sort, absU32_beq_lit, absU32_beq_forallE,
    absU32_beq_lam]
  split_ifs at h' <;> (cases Result.ok_injective h') <;>
    simp_all (config := {decide := true}) [arena.handle.ETAG_SORT, arena.handle.ETAG_LIT,
      arena.handle.ETAG_FORALL_E, arena.handle.ETAG_LAM]

@[lockstep] theorem bool_true_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_true_name st) lst boolTrueName := by
  rw [arena.core.bool_true_name, boolTrueName, ← bind_pure pinBoolTrue]
  lockstep_core

@[lockstep] theorem bool_false_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_false_name st) lst boolFalseName := by
  rw [arena.core.bool_false_name, boolFalseName, ← bind_pure pinBoolFalse]
  lockstep_core

@[lockstep] theorem reserved_basis_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.core.reserved_basis_names st) st lst
      reservedBasisNames :=
  pinRE_lsr hrel hinv fun _ h => reserved_basis_names_run₀ hrel hinv h

@[lockstep] theorem is_bool_true_ls {pers st h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.is_bool_true pers st h) lst
      (isBoolTrue (absEIdx h)) := by
  rw [arena.core.is_bool_true, isBoolTrue]
  lockstep_core
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem head_hint_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = ConRon.Refine.absHint a) (arena.core.head_hint pers vis st fe e) lst
      (headHint lfe (absEIdx e)) := by
  rw [arena.core.head_hint, headHint]
  lockstep_core
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem unfoldable_head_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.unfoldable_head pers vis st fe e) lst
      (unfoldableHead lfe (absEIdx e)) := by
  rw [arena.core.unfoldable_head, unfoldableHead]
  lockstep_core
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem same_const_heads_ls {pers st a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun x y => y = x) (arena.core.same_const_heads pers st a b) lst
      (sameConstHeads (absEIdx a) (absEIdx b)) := by
  rw [arena.core.same_const_heads, sameConstHeads]
  lockstep_core
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem is_unit_like_ty_ls {pers vis st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.is_unit_like_ty pers vis st fe h) lst
      (isUnitLikeTy lfe (absEIdx h)) := by
  rw [arena.core.is_unit_like_ty, isUnitLikeTy]
  lockstep_core
  all_goals trace_state
  all_goals sorry

end ConRon.Refine2.Lockstep
