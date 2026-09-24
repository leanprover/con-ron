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

theorem uscalar_eq_iff_val {ty} (a b : Std.UScalar ty) : a = b ↔ a.val = b.val :=
  ⟨fun h => h ▸ rfl, fun h => Aeneas.Std.UScalar.eq_imp a b h⟩

theorem nat_beq_eq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

attribute [local lockstep_simp] decide_usize_eq_len absIConstantVal_levelParams_length

attribute [local lockstep_simp] absIConstantVal absIIndCaps

-- region A1's rec-rule abstraction, unfolded here only (region C2 reads it
-- through projection lemmas)
attribute [local lockstep_simp] absIRecRule absIRecRuleFire

open Lean Elab Tactic in
/-- Rewrite the twin side with the context's `TwinEq` facts; fails when
nothing changes. -/
elab "a1_twin_eqs" : tactic => do
  let g ← getMainGoal
  let g' ← simpTwinEqs g
  if g' == g then throwError "a1_twin_eqs: no progress"
  replaceMainGoal [g']

/-- `lockstep_core`, and a conjunction in the context split whenever it
stops: a constructed level's fact is `WF u ∧ TwinEq …` (`PrimsA1.lean`), which
the tidy step leaves whole. -/
macro "lockstep_a1" : tactic =>
  `(tactic| repeat' (first | lockstep_step | (casesm* _ ∧ _) | a1_twin_eqs))

theorem some_beq_some_true (b : Bool) : (some b == some true) = b := by cases b <;> rfl

attribute [local lockstep_simp] some_beq_some_true Bool.not_eq_true

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

@[lockstep] theorem head_hint_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = ConRon.Refine.absHint a) (arena.core.head_hint pers vis st fe e) lst
      (headHint lfe (absEIdx e)) := by
  rw [arena.core.head_hint, headHint]
  lockstep_core

@[lockstep] theorem unfoldable_head_ls {pers vis st fe lfe e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.unfoldable_head pers vis st fe e) lst
      (unfoldableHead lfe (absEIdx e)) := by
  rw [arena.core.unfoldable_head, unfoldableHead]
  lockstep_core

@[lockstep] theorem same_const_heads_ls {pers st a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun x y => y = x) (arena.core.same_const_heads pers st a b) lst
      (sameConstHeads (absEIdx a) (absEIdx b)) := by
  rw [arena.core.same_const_heads, sameConstHeads]
  lockstep_core

@[lockstep] theorem is_unit_like_ty_ls {pers vis st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.is_unit_like_ty pers vis st fe h) lst
      (isUnitLikeTy lfe (absEIdx h)) := by
  rw [arena.core.is_unit_like_ty, isUnitLikeTy]
  lockstep_core
  -- glue: the port tests `rules.len() == 1` and reads `rules[0]`, the twin
  -- matches the singleton pattern `[r]`
  all_goals
    split
    all_goals rename_i heq
    all_goals
      refine LS.pure ?_ ‹_› ‹_›
      simp only [Option.some.injEq, IConstantInfo.recInfo.injEq, List.map_eq_singleton_iff] at heq
      first
      | rfl
      | (obtain ⟨-, rfl, rfl, x, hx, rfl⟩ := heq
         simp_all [absIRecRule, uscalar_eq_iff_val, alloc.vec.Vec.len_val, absU,
           nat_beq_eq_decide]
         done)
      | (exfalso
         have hl := congrArg (fun u : Std.Usize => u.val) ‹alloc.vec.Vec.len _ = 1#usize›
         simp only [alloc.vec.Vec.len_val] at hl
         obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hl
         exact heq _ _ _ _ ⟨rfl, rfl, rfl, y, hy, rfl⟩)


/-! ## The level verdicts, cached -/

-- The ExprOps lane unfolds `absLevels`/`absNames` globally (`Tactic/Prims`);
-- the level verdicts' `TwinEq`s are stated at the folded spelling
attribute [-lockstep_simp] ConRon.Refine.absLevels ConRon.Refine.absNames

@[lockstep] theorem lvl_eq_ls {pers st u v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.lvl_eq pers st u v) lst
      (lvlEq? (absLIdx u) (absLIdx v)) := by
  rw [arena.core.lvl_eq, lvlEq?]
  lockstep_core

@[lockstep] theorem lvls_eq_ls {pers st us vs lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.lvls_eq pers st us vs) lst
      (lvlsEq? (absLsIdx us) (absLsIdx vs)) := by
  rw [arena.core.lvls_eq, lvlsEq?]
  lockstep_core

/-! ## The instantiated-constant caches -/

@[lockstep] theorem const_ty_at_ls {pers st cv us lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.const_ty_at pers st cv us) lst
      (constTyAt (absIConstantVal cv) (absLsIdx us)) := by
  rw [arena.core.const_ty_at, constTyAt]
  lockstep_a1

@[lockstep] theorem rule_rhs_at_ls {pers st rec_name ctor lps rhs us lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.rule_rhs_at pers st rec_name ctor lps rhs us) lst
      (ruleRhsAt (absNIdx rec_name) (absNIdx ctor) (lps.val.map absNIdx) (absEIdx rhs)
        (absLsIdx us)) := by
  rw [arena.core.rule_rhs_at, ruleRhsAt]
  lockstep_a1

/-! ## The level predicates -/

@[lockstep] theorem proj_entry_fire_ok_ls {pers st entry us lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.proj_entry_fire_ok pers st entry us) lst
      ((absIProjEntry entry).fireOk (absLsIdx us)) := by
  rw [arena.core.proj_entry_fire_ok, IProjEntry.fireOk]
  lockstep_a1

/-- `hcaps`: the stored zero-ness datum is a well-formed `PropWhen` (a
representation fact about the Rust input `caps`; `level::subst_pw`'s
refinement needs it). -/
@[lockstep] theorem caps_never_zero_ls {pers st lps us caps lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hcaps : ConRon.Refine.PropWhenWF caps.sort_z) :
    LS pers (fun a b => b = a) (arena.core.caps_never_zero pers st lps us caps) lst
      (capsNeverZero (lps.val.map absNIdx) (absLsIdx us) (absIIndCaps caps)) := by
  rw [arena.core.caps_never_zero, capsNeverZero]
  lockstep_a1

@[lockstep] theorem proj_entry_type_at_ls {pers st entry us targs pe lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.proj_entry_type_at pers st entry us targs pe) lst
      ((absIProjEntry entry).typeAt (absLsIdx us) (absEIdxList targs) (absEIdx pe)) := by
  rw [arena.core.proj_entry_type_at, IProjEntry.typeAt]
  lockstep_a1

/-! ## The comparand walks (cursor loops against list recursions)

The port walks a `Vec` with a cursor and an accumulator; the twin recurses on
the list and conses on the way back.  So the recursive call is a TAIL call on
the port's side and a bind-then-`pure` on the twin's: `LS.tail_bind_pure` is
that one step, and the statement carries the accumulator
(`a.val.map abs = out.val.map abs ++ b`). -/

theorem LS.tail_bind_pure {α β γ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : α → γ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} {f : β → γ}
    (hf : LS pers R₁ m lst x) (hR : ∀ a b, R₁ a b → R a (f b)) :
    LS pers R m lst (x >>= fun b => Pure.pure (f b)) := by
  intro o st' hm
  have h := hf o st' hm
  cases o with
  | Err e => exact errSim_bind h
  | Ok a =>
    obtain ⟨b, lst', hx, hr, h1, h2⟩ := h
    exact ⟨f b, lst', by rw [run_bind_ok hx]; rfl, hR _ _ hr, h1, h2⟩

attribute [local lockstep_simp] substLevelsAt substParamLevels instSpinePins
  List.map_cons List.map_nil

theorem subst_levels_at_aux {pers} (ks : alloc.vec.Vec kernel.name.Name)
    (vs : alloc.vec.Vec kernel.level.Level) (us : alloc.vec.Vec arena.handle.LIdx)
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs) :
    ∀ n (i : Std.Usize) (out : alloc.vec.Vec arena.handle.LIdx) {st lst},
      us.length - i.val ≤ n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absLIdx = out.val.map absLIdx ++ b)
        (arena.core.subst_levels_at pers st ks vs us i out) lst
        (substLevelsAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels vs)
          ((us.val.drop i.val).map absLIdx)) := by
  intro n
  induction n with
  | zero =>
    intro i out st lst hk hrel hinv
    rw [arena.core.subst_levels_at, List.drop_eq_nil_of_le (by scalar_tac)]
    lockstep_a1
  | succ n ih =>
    intro i out st lst hk hrel hinv
    rw [arena.core.subst_levels_at]
    by_cases hlt : i.val < us.val.length
    · rw [List.drop_eq_getElem_cons hlt]
      lockstep_a1
      -- glue: the port's tail call against the twin's bind-then-cons
      rw [show i.val + 1 = a.val by scalar_tac]
      refine LS.tail_bind_pure (ih _ _ (by scalar_tac) hrel hinv) ?_
      · intro x y hxy
        rw [hxy]
        simp [*]
    · rw [List.drop_eq_nil_of_le (by omega)]
      lockstep_a1

@[lockstep] theorem subst_levels_at_ls {pers st ks vs us lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs) :
    LS pers (fun a b => b = a.val.map absLIdx)
      (arena.core.subst_levels_at pers st ks vs us 0#usize (alloc.vec.Vec.new _)) lst
      (substLevelsAt (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels vs)
        (us.val.map absLIdx)) := by
  have h := subst_levels_at_aux ks vs us hks hvs _ 0#usize (alloc.vec.Vec.new _)
    (Nat.le_refl _) hrel hinv
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at h
  exact LS.tail h rfl (fun a b hab => by simp [hab, alloc.vec.Vec.new])

theorem subst_param_levels_aux {pers} (ks : alloc.vec.Vec kernel.name.Name)
    (vs : alloc.vec.Vec kernel.level.Level) (ps : alloc.vec.Vec arena.handle.NIdx)
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs) :
    ∀ n (i : Std.Usize) (out : alloc.vec.Vec arena.handle.LIdx) {st lst},
      ps.length - i.val ≤ n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absLIdx = out.val.map absLIdx ++ b)
        (arena.core.subst_param_levels pers st ks vs ps i out) lst
        (substParamLevels (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels vs)
          ((ps.val.drop i.val).map absNIdx)) := by
  intro n
  induction n with
  | zero =>
    intro i out st lst hk hrel hinv
    rw [arena.core.subst_param_levels, List.drop_eq_nil_of_le (by scalar_tac)]
    lockstep_a1
  | succ n ih =>
    intro i out st lst hk hrel hinv
    rw [arena.core.subst_param_levels]
    by_cases hlt : i.val < ps.val.length
    · rw [List.drop_eq_getElem_cons hlt]
      lockstep_a1
      -- glue: the port's tail call against the twin's bind-then-cons
      rw [show i.val + 1 = a.val by scalar_tac]
      refine LS.tail_bind_pure (ih _ _ (by scalar_tac) hrel hinv) ?_
      · intro x y hxy
        rw [hxy]
        simp [*]
    · rw [List.drop_eq_nil_of_le (by omega)]
      lockstep_a1

@[lockstep] theorem subst_param_levels_ls {pers st ks vs ps lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs) :
    LS pers (fun a b => b = a.val.map absLIdx)
      (arena.core.subst_param_levels pers st ks vs ps 0#usize (alloc.vec.Vec.new _)) lst
      (substParamLevels (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels vs)
        (ps.val.map absNIdx)) := by
  have h := subst_param_levels_aux ks vs ps hks hvs _ 0#usize (alloc.vec.Vec.new _)
    (Nat.le_refl _) hrel hinv
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at h
  exact LS.tail h rfl (fun a b hab => by simp [hab, alloc.vec.Vec.new])

theorem inst_spine_pins_aux {pers} (hx : ExprOpsHyp pers) (lps : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (args : alloc.vec.Vec arena.handle.EIdx) (r_p : Std.U64)
    (pins : alloc.vec.Vec arena.handle.EIdx) :
    ∀ n (i : Std.Usize) (out : alloc.vec.Vec arena.handle.EIdx) {st lst},
      pins.length - i.val ≤ n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => a.val.map absEIdx = out.val.map absEIdx ++ b)
        (arena.core.inst_spine_pins pers st lps us args r_p pins i out) lst
        (instSpinePins (lps.val.map absNIdx) (absLsIdx us) (absEIdxList args) (absU r_p)
          ((pins.val.drop i.val).map absEIdx)) := by
  intro n
  induction n with
  | zero =>
    intro i out st lst hk hrel hinv
    rw [arena.core.inst_spine_pins, List.drop_eq_nil_of_le (by scalar_tac)]
    lockstep_a1
  | succ n ih =>
    intro i out st lst hk hrel hinv
    rw [arena.core.inst_spine_pins]
    by_cases hlt : i.val < pins.val.length
    · rw [List.drop_eq_getElem_cons hlt]
      lockstep_a1
      -- glue: the port's tail call against the twin's bind-then-cons
      rw [show i.val + 1 = a.val by scalar_tac]
      refine LS.tail_bind_pure (ih _ _ (by scalar_tac) hrel hinv) ?_
      · intro x y hxy
        rw [hxy]
        simp [*]
    · rw [List.drop_eq_nil_of_le (by omega)]
      lockstep_a1

@[lockstep] theorem inst_spine_pins_ls {pers st lps us args r_p pins lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a.val.map absEIdx)
      (arena.core.inst_spine_pins pers st lps us args r_p pins 0#usize (alloc.vec.Vec.new _)) lst
      (instSpinePins (lps.val.map absNIdx) (absLsIdx us) (absEIdxList args) (absU r_p)
        (pins.val.map absEIdx)) := by
  have h := inst_spine_pins_aux hx lps us args r_p pins _ 0#usize (alloc.vec.Vec.new _)
    (Nat.le_refl _) hrel hinv
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at h
  exact LS.tail h rfl (fun a b hab => by simp [hab, alloc.vec.Vec.new])

attribute [lockstep_inline] arena.core.rec_fire_comparands_plain

@[lockstep] theorem rec_fire_comparands_ls {pers st rl lps us cvj_lps args r_p lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (absLsIdx a.1, absEIdxList a.2))
      (arena.core.rec_fire_comparands pers st rl lps us cvj_lps args r_p) lst
      (recFireComparands (absIRecRule rl) (lps.val.map absNIdx) (absLsIdx us)
        (cvj_lps.val.map absNIdx) (absEIdxList args) (absU r_p)) := by
  rw [arena.core.rec_fire_comparands, recFireComparands]
  -- glue: both sides match on the rule's `fire`; split it once for both
  simp only [absIRecRule]
  cases hf : rl.fire <;> simp only [absIRecRuleFire] <;> lockstep_a1

end ConRon.Refine2.Lockstep
