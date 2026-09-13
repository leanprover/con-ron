/-
# `Refine/IndIngredients.lean` — the inductive tier's ingredients, discharged (task #59)

`CORE_PLAN.md` step 7, the seam task #57 left open.

The ten `Refine/Ind*.lean` files were written **in parallel**, so whatever a
sibling module owned could not be `import`ed: it travelled as an explicit named
`Prop` *ingredient hypothesis* (`structure CheckerBaseSpec`,
`def StructFamRefines : Prop`, `def ConsSumCtorsRefines : Prop`, …), each
stated in the exact-result shape of DESIGN.md §3.5 so that no conclusion of the
tier was ever weakened.  Every such `Prop` is, by construction, the exact
refinement statement that some *other* file of the tier proves.

This file is the tier's **leaf**: it imports all of them at once and discharges
each ingredient from its owner's lemma.  Nothing here is a new refinement — each
theorem is an application, sometimes with a `Prod`/`Option` bridge or a
re-association of conjuncts.  `structGens` — the twelve `struct_parts`
generators `native_parts` asks for — is here too, and `Refine/IndC.lean`, the
tier's driver file, imports this one.

## What is discharged, from where

| ingredient | owner |
|---|---|
| `CheckerBase.ConstsResolveFSpec`, `StructInstall.ConstsResolveFFastRefines`, `SumInstall.ConstsResolveFFastRefines` | `Refine/DeclCheck.lean` (`consts_resolve_f_fast_refines`) + `Refine/CoreKPinned.lean` |
| `Modeled.CheckerBaseSpec` (eleven of twelve fields) | `Refine/CheckerBase.lean` |
| `SumInstall.CheckConstantValRefines`, `NativeInstall.CheckConstantValRefines` | `Refine/CheckerBase.lean` (`check_constant_val_refines`) |
| `SumInstall.OpenPisAtFvarsFRefines`, `NativeInstall.OpenPisAtFvarsFRefines` | `Refine/CheckerBase.lean` (`open_pis_at_fvars_f_refines`; the second reading through con-leche's `openPisAtFvarsF_eq`) |
| `SumInstall.FvarTypesRefines` | `Refine/CheckerBase.lean` (`fvar_types_refines`) |
| `Modeled.StructFamRefines`, `Modeled.StructSpinesRefine`, `StructInstall.StructProjBodiesRefines`, both `MentionsConstRefines`, both `ParamsOfRefines`, `SumInstall.StructCtorResidOkRefines`, `NativeInstall.StructProjGuardsRefines` | `Refine/IndStructParts.lean` |
| `SumInstall.CheckStructDomsAtRefines` | `Refine/IndStructInstall.lean` |
| `NativeInstall`'s eleven `native_parts` ingredients | `Refine/IndNativeParts.lean` |
| `NativeInstall`'s five `sum_install` ingredients | `Refine/IndSumInstall.lean` |

## The one hypothesis this file takes

**The knot.**  Every `mode`-indexed ingredient is about a stage that reaches
the core, and the owner proves it from `Core.Wrappers mode IndAbs.checkFuelU`
(task #55).  So do the discharges: `hw` is an argument, exactly the knot the
whole tier assumes.  `Refine/CheckerBase.lean` spells the same hypothesis as
`core_k.check_fuel = ok fuel` plus `Core.Wrappers mode fuel`;
`IndAbs.check_fuel_eq` is the bridge, and `TypeChecker.lops mode lfe` is a
*reducible* abbreviation of `ConLeche.Cached.sharedOpsC (absMode mode) lfe`,
so the two spellings of the operations record are the same term and no
translation is needed.

Nothing else is assumed.  In particular **no platform assumption**: the two
`Vec`-indexing ingredients (`NativeInstall.KindGetDRefines`,
`NativeInstall.StructProjGuardsRefines`) carry a `≤ Std.Usize.max` side
condition in their own statements — `Refine/Scalars.lean`'s fact that the
port's `v[i as usize]` and con-leche's `v[i]?` genuinely disagree on a 32-bit
target — and this file passes it through rather than discharging it from
`Usize.max = U64.max`.

No `sorry` in this file, and no `axiom`: every theorem is an application of a
lemma of the file the ingredient's own doc comment names.  Several of those
lemmas still carry `sorry`s of their own while their files are being finished —
that is by design, the tier's layering, and closing them closes these.
-/
import ConRon.Refine.IndStructParts
import ConRon.Refine.IndNativeParts
import ConRon.Refine.IndModeled
import ConRon.Refine.IndNativeInstall
import ConRon.Refine.IndSumInstall
import ConRon.Refine.CheckerBase
import ConRon.Refine.DeclCheck
import ConRon.Refine.CoreKPinned
import ConLeche.Verify.FastOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.IndIngredients

/-! ## `kernel::inductives::struct_parts` — `Refine/IndNativeParts.lean`'s
`StructGens`

`native_parts`'s generators call twelve `struct_parts` items; task #57 bundled
them as one hypothesis because the two files were written in parallel.  Each
field is `Refine/IndStructParts.lean`'s exact refinement statement, so the
discharge is twelve applications and nothing else. -/

/-- **`Refine/IndNativeParts.lean`'s `StructGens`**, from
`Refine/IndStructParts.lean`. -/
theorem structGens : NativeParts.StructGens where
  params_of := fun _ _ hlps h => StructParts.params_of_refines hlps h
  level_is_prop := fun _ _ hs h => StructParts.level_is_prop_refines hs h
  struct_ps_at := fun _ _ _ h => StructParts.struct_ps_at_refines h
  field_spine := fun _ _ h => StructParts.field_spine_refines h
  struct_ctor_spine_at := fun _ _ _ _ _ _ hc hlps h =>
    StructParts.struct_ctor_spine_at_refines hc hlps h
  struct_elim_level := fun _ _ _ he h => StructParts.struct_elim_level_refines he h
  replace_pis_pw := fun _ _ _ _ _ hpw he hb h =>
    StructParts.replace_pis_pw_refines hpw he hb h
  pis_to_lams_pw := fun _ _ _ _ _ hpw he hb h =>
    StructParts.pis_to_lams_pw_refines hpw he hb h
  struct_fam_i := fun _ _ _ _ _ _ _ ht hlps h =>
    StructParts.struct_fam_i_refines ht hlps h
  struct_motive_ty_i := fun _ _ _ _ _ _ _ ht hlps hl hitele h =>
    StructParts.struct_motive_ty_i_refines ht hlps hl hitele h
  mentions_const := fun _ _ _ ht he h => StructParts.mentions_const_refines ht he h
  struct_used_later := fun _ _ _ _ hcty h => StructParts.struct_used_later_refines hcty h

/-! ## `decl_check::consts_resolve_f_fast`

`Refine/DeclCheck.lean` proves it against `FindAgree` — the find-agreement
projection of `FEnvRel`/`FEnvWF` (`Refine/CoreKBase.lean`) — and the pinned
basis names, which `Refine/CoreKPinned.lean` discharges outright.  Three files
name the same fact: `Refine/CheckerBase.lean` as `ConstsResolveFSpec`, and the
two install modules as `ConstsResolveFFastRefines`. -/

/-- `Refine/CheckerBase.lean`'s `ConstsResolveFSpec`, discharged. -/
theorem constsResolveFSpec : CheckerBase.ConstsResolveFSpec := by
  intro fe lfe e b hrel hwf he h
  exact DeclCheck.consts_resolve_f_fast_refines CoreK.pinnedBasisNames
    (FindAgree.of_rel hrel hwf) he h

/-- `Refine/IndStructInstall.lean`'s copy. -/
theorem structInstallConstsResolveFFast : StructInstall.ConstsResolveFFastRefines := by
  intro fe lfe e b hrel hwf he h
  exact DeclCheck.consts_resolve_f_fast_refines CoreK.pinnedBasisNames
    (FindAgree.of_rel hrel hwf) he h

/-- `Refine/IndSumInstall.lean`'s copy. -/
theorem sumInstallConstsResolveFFast : SumInstall.ConstsResolveFFastRefines := by
  intro fe lfe e b hrel hwf he h
  exact DeclCheck.consts_resolve_f_fast_refines CoreK.pinnedBasisNames
    (FindAgree.of_rel hrel hwf) he h

/-! ## `kernel::checker_base` — `Refine/IndModeled.lean`'s `CheckerBaseSpec`

Each of the twelve fields is the named lemma of `Refine/CheckerBase.lean`,
applied — `domsMatchAux` included: its owner states
`doms_match_aux_view_refines` at an abstract `DomView` dictionary and an
abstract binder view `gl`, which is exactly the field's shape. -/

/-- **`Refine/IndModeled.lean`'s `CheckerBaseSpec`**, all twelve fields, from
`Refine/CheckerBase.lean` under the knot. -/
theorem checkerBaseSpec {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    Modeled.CheckerBaseSpec mode where
  checkConstantVal := fun _ _ _ _ _ hsw hfw hcv h =>
    CheckerBase.check_constant_val_refines IndAbs.check_fuel_eq hw constsResolveFSpec
      hsw hfw hcv h
  openPisAtFvarsF := fun _ _ _ _ he h => CheckerBase.open_pis_at_fvars_f_refines he h
  domsMatchAux := fun inst g gl hgl _ _ _ _ _ _ hb1 hb2 h =>
    CheckerBase.doms_match_aux_view_refines inst g gl hgl hb1 hb2 h
  checkDefEqList := fun _ _ _ _ _ _ hsw hfw hxs hys h =>
    CheckerBase.check_def_eq_list_refines IndAbs.check_fuel_eq hw hsw hfw hxs hys h
  checkAnnotList := fun _ _ _ _ _ hsw hfw hxs h =>
    CheckerBase.check_annot_list_refines IndAbs.check_fuel_eq hw hsw hfw hxs h
  checkTypedList := fun _ _ _ _ _ _ hsw hfw hxs hts h =>
    CheckerBase.check_typed_list_refines IndAbs.check_fuel_eq hw hsw hfw hxs hts h
  isEqHead := fun _ _ he h => CheckerBase.is_eq_head_refines he h
  eqHeadLevel := fun _ _ he h => CheckerBase.eq_head_level_refines he h
  findCv := fun _ _ _ _ hrel hwf hn h => CheckerBase.find_cv_refines hrel hwf hn h
  fvarTypes := fun _ _ hfvs h => CheckerBase.fvar_types_refines hfvs h
  checkProjShape := fun _ _ _ _ hp hc h => by
    funext lst; exact CheckerBase.check_proj_shape_refines hp hc h lst
  checkProjRule := fun _ _ _ _ _ _ _ _ _ _ hsw hfw hpty hcvj hlps h =>
    CheckerBase.check_proj_rule_refines IndAbs.check_fuel_eq hw constsResolveFSpec
      hsw hfw hpty hcvj hlps h
  -- The six failure halves (task #67 continued).  Each is the `.Err ce`
  -- instance of the very `Refine/CheckerBase.lean` lemma the accept field
  -- above already uses, where its full-outcome `match` reduces.
  checkConstantValErr := fun _ _ _ _ _ hsw hfw hcv h =>
    CheckerBase.check_constant_val_refines IndAbs.check_fuel_eq hw
      constsResolveFSpec hsw hfw hcv h
  checkDefEqListErr := fun _ _ _ _ _ _ _ hsw hfw hxs hys h =>
    CheckerBase.check_def_eq_list_refines IndAbs.check_fuel_eq hw hsw hfw hxs hys h
  checkAnnotListErr := fun _ _ _ _ _ _ hsw hfw hxs h =>
    CheckerBase.check_annot_list_refines IndAbs.check_fuel_eq hw hsw hfw hxs h
  checkTypedListErr := fun _ _ _ _ _ _ _ hsw hfw hxs hts h =>
    CheckerBase.check_typed_list_refines IndAbs.check_fuel_eq hw hsw hfw hxs hts h
  checkProjShapeErr := fun _ _ _ _ _ hp hc h =>
    CheckerBase.check_proj_shape_refines hp hc h
  checkProjRuleErr := fun _ _ _ _ _ _ _ _ _ _ hsw hfw hpty hcvj hlps h =>
    CheckerBase.check_proj_rule_refines IndAbs.check_fuel_eq hw
      constsResolveFSpec hsw hfw hpty hcvj hlps h

/-! ### The same items, as the two install modules spell them -/

/-- `Refine/IndSumInstall.lean`'s `CheckConstantValRefines`. -/
theorem sumInstallCheckConstantVal {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    SumInstall.CheckConstantValRefines mode := by
  intro _ _ _ _ o hsw hfw hcv h
  cases o <;>
    exact CheckerBase.check_constant_val_refines IndAbs.check_fuel_eq hw
      constsResolveFSpec hsw hfw hcv h

/-- `Refine/IndNativeInstall.lean`'s `CheckConstantValRefines`. -/
theorem nativeInstallCheckConstantVal {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckConstantValRefines mode := by
  intro _ _ _ _ _ hsw hfw hcv h
  exact CheckerBase.check_constant_val_refines IndAbs.check_fuel_eq hw
    constsResolveFSpec hsw hfw hcv h

/-- `Refine/IndSumInstall.lean`'s `OpenPisAtFvarsFRefines`, against the one-pass
`openPisAtFvarsF` the port runs. -/
theorem sumInstallOpenPisAtFvarsF : SumInstall.OpenPisAtFvarsFRefines := by
  intro _ _ _ _ he h
  exact CheckerBase.open_pis_at_fvars_f_refines he h

/-- `Refine/IndNativeInstall.lean`'s `OpenPisAtFvarsFRefines`: the *same*
function read against the specification `openPisAtFvars`, which con-leche's own
`openPisAtFvarsF_eq` (`ConLeche/Verify/FastOps.lean:101-108`) identifies with
the one-pass member. -/
theorem nativeInstallOpenPisAtFvarsF : NativeInstall.OpenPisAtFvarsFRefines := by
  intro n e i o he h
  obtain ⟨habs, hwf⟩ := CheckerBase.open_pis_at_fvars_f_refines he h
  exact ⟨habs.trans (ConLeche.openPisAtFvarsF_eq n.val (absExpr e) i.val), hwf⟩

/-- `Refine/IndSumInstall.lean`'s `FvarTypesRefines`. -/
theorem sumInstallFvarTypes : SumInstall.FvarTypesRefines := by
  intro _ _ hfvs h
  exact CheckerBase.fvar_types_refines hfvs h

/-! ## `kernel::inductives::struct_parts` — `Refine/IndStructParts.lean`

The recogniser's generators and readers.  `Refine/IndC.lean`'s
`structGens` already bundles the twelve `native_parts` asks for;
these are the ones the three *install* modules and the modeled route ask for
separately. -/

/-- `Refine/IndModeled.lean`'s `StructFamRefines`. -/
theorem structFamRefines : Modeled.StructFamRefines := by
  intro _ _ _ _ _ ht hlps h
  exact StructParts.struct_fam_refines ht hlps h

/-- `Refine/IndModeled.lean`'s `StructSpinesRefine` — `params_of` and
`struct_proj_ps`.  The second conjunct is `ConLeche.structProjPs` written out
(`StructParts.lean:336-337`). -/
theorem structSpinesRefine : Modeled.StructSpinesRefine :=
  ⟨fun _ _ hlps h => StructParts.params_of_refines hlps h,
   fun _ _ h => StructParts.struct_proj_ps_refines h,
   fun _ _ h => StructParts.field_spine_refines h,
   fun _ _ _ h => StructParts.struct_ps_at_refines h⟩

/-- `Refine/IndStructInstall.lean`'s `StructProjBodiesRefines`, the second of
`StructWalkers.plain`'s two walkers. -/
theorem structProjBodiesRefines : StructInstall.StructProjBodiesRefines := by
  intro _ _ _ _ _ ht hcty h
  exact StructParts.struct_proj_bodies_refines ht hcty h

/-- `Refine/IndSumInstall.lean`'s `MentionsConstRefines`. -/
theorem sumInstallMentionsConst : SumInstall.MentionsConstRefines := by
  intro _ _ _ ht he h
  exact StructParts.mentions_const_refines ht he h

/-- `Refine/IndNativeInstall.lean`'s `MentionsConstRefines`. -/
theorem nativeInstallMentionsConst : NativeInstall.MentionsConstRefines := by
  intro _ _ _ ht he h
  exact StructParts.mentions_const_refines ht he h

/-- `Refine/IndSumInstall.lean`'s `StructCtorResidOkRefines`. -/
theorem structCtorResidOkRefines : SumInstall.StructCtorResidOkRefines := by
  intro _ _ _ _ _ _ _ ht hlps hcbody h
  exact StructParts.struct_ctor_resid_ok_refines ht hlps hcbody h

/-- `Refine/IndSumInstall.lean`'s `ParamsOfRefines`. -/
theorem sumInstallParamsOf : SumInstall.ParamsOfRefines := by
  intro _ _ hlps h
  exact StructParts.params_of_refines hlps h

/-- `Refine/IndNativeInstall.lean`'s `ParamsOfRefines`. -/
theorem nativeInstallParamsOf : NativeInstall.ParamsOfRefines := by
  intro _ _ hlps h
  exact StructParts.params_of_refines hlps h

/-! ## `kernel::inductives::struct_install` — `Refine/IndStructInstall.lean` -/

/-- `Refine/IndSumInstall.lean`'s `CheckStructDomsAtRefines`. -/
theorem checkStructDomsAtRefines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    SumInstall.CheckStructDomsAtRefines mode := by
  intro _ _ _ _ _ _ _ o hst hfe hfvs hdoms hjmax h
  cases o <;>
    exact StructInstall.check_struct_doms_at_refines hw hst hfe hfvs hdoms hjmax h

/-! ## `kernel::inductives::native_parts` — `Refine/IndNativeParts.lean`

Eleven ingredients of `Refine/IndNativeInstall.lean`.  Six of the owner's
lemmas take `NativeParts.StructGens`, which `Refine/IndC.lean` already
discharges (`structGens`). -/

/-- con-leche compares `RecFieldKind`s with `==`; `Refine/IndNativeParts.lean`
states the port's `rec_field_kind_beq` with `decide`.  The two agree
(`RecFieldKind` derives `DecidableEq`). -/
theorem decide_eq_beq_kind (a b : ConLeche.RecFieldKind) :
    decide (a = b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

/-- `Refine/IndNativeInstall.lean`'s `RecFieldKindBeqRefines`. -/
theorem recFieldKindBeqRefines : NativeInstall.RecFieldKindBeqRefines := by
  intro a b c h
  rw [NativeParts.rec_field_kind_beq_refines h, decide_eq_beq_kind]

/-- `Refine/IndNativeInstall.lean`'s `PiBindersRefines`. -/
theorem piBindersRefines : NativeInstall.PiBindersRefines := by
  intro e q he h
  obtain ⟨h1, h2, h3, h4⟩ := NativeParts.pi_binders_refines he h
  exact ⟨by rw [h1, h2], h3, h4⟩

/-- `Refine/IndNativeInstall.lean`'s `RecCtorKindsRefines`. -/
theorem recCtorKindsRefines : NativeInstall.RecCtorKindsRefines := by
  intro _ _ _ _ _ _ ht hlps hc h
  exact NativeParts.rec_ctor_kinds_refines structGens ht hlps hc h

/-- `native_parts::complete` replaces the record's shape wholesale
(`native_parts.rs:501-507`), so the completed record's `NativePartsWF` is the
*argument* shape's `InductiveShapeWF` — the ingredient's second hypothesis. -/
theorem complete_shape {p0 p' : native_parts.NativeParts}
    {p1 : sum_parts.InductiveShape} (h : native_parts.complete p0 p1 = ok p') :
    p'.shape = p1 := by
  rw [native_parts.complete] at h
  obtain ⟨v, _, h⟩ := bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]

/-- `native_parts::with_kinds` touches only the kinds (`native_parts.rs:513-517`),
so it preserves `NativePartsWF`. -/
theorem with_kinds_shape {p p' : native_parts.NativeParts}
    {ks : alloc.vec.Vec (alloc.vec.Vec native_parts.RecFieldKind)}
    (h : native_parts.with_kinds p ks = ok p') : p'.shape = p.shape := by
  rw [native_parts.with_kinds] at h
  rw [← Result.ok_injective h]

/-- `Refine/IndNativeInstall.lean`'s `CompleteRefines`. -/
theorem completeRefines : NativeInstall.CompleteRefines := by
  intro p0 p1 p _ hp1 h
  refine ⟨NativeParts.complete_refines h, ?_⟩
  show IndAbs.InductiveShapeWF p.shape
  rw [complete_shape h]; exact hp1

/-- `Refine/IndNativeInstall.lean`'s `WithKindsRefines`. -/
theorem withKindsRefines : NativeInstall.WithKindsRefines := by
  intro p ks p' hp h
  refine ⟨NativeParts.with_kinds_refines h, ?_⟩
  show IndAbs.InductiveShapeWF p'.shape
  rw [with_kinds_shape h]; exact hp

/-- `Refine/IndNativeInstall.lean`'s `NativeCtors4Refines`. -/
theorem nativeCtors4Refines : NativeInstall.NativeCtors4Refines := by
  intro _ _ _ hctors hkf h
  exact NativeParts.native_ctors4_refines hctors hkf h

/-- `Refine/IndNativeInstall.lean`'s `StructRecTyRRefines`. -/
theorem structRecTyRRefines : NativeInstall.StructRecTyRRefines := by
  intro _ _ _ _ _ _ _ _ _ ht hlps helim htty hctors hcpos h
  exact NativeParts.struct_rec_ty_r_refines structGens ht hlps helim
    htty hctors hcpos h

/-- `Refine/IndNativeInstall.lean`'s `StructRecRhsRRefines`. -/
theorem structRecRhsRRefines : NativeInstall.StructRecRhsRRefines := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ ht hlps helim htty hctors hcpos hj hrec hrlvls h
  exact NativeParts.struct_rec_rhs_r_refines structGens ht hlps helim
    htty hctors hcpos hj hrec hrlvls h

/-- `Refine/IndNativeInstall.lean`'s `NativeRulesOkRefines`. -/
theorem nativeRulesOkRefines : NativeInstall.NativeRulesOkRefines := by
  intro _ _ _ _ _ _ _ _ _ _ hrec hrlvls hpw hcs hrhss hrecty h
  exact NativeParts.native_rules_ok_refines structGens hrec hrlvls hpw
    hcs hrhss hrecty h

/-- `Refine/IndNativeInstall.lean`'s `NativeRecLpsOkRefines`. -/
theorem nativeRecLpsOkRefines : NativeInstall.NativeRecLpsOkRefines := by
  intro _ _ hp h
  exact NativeParts.native_rec_lps_ok_refines hp h

/-! ## `kernel::inductives::sum_install` — `Refine/IndSumInstall.lean` -/

/-- `Refine/IndNativeInstall.lean`'s `ConsSumCtorsRefines`. -/
theorem consSumCtorsRefines : NativeInstall.ConsSumCtorsRefines := by
  intro _ _ _ _ _ _ hfe hcs hrel h
  exact SumInstall.cons_sum_ctors_refines hrel hfe hcs h

/-- `Refine/IndNativeInstall.lean`'s `SumRulesRefines`. -/
theorem sumRulesRefines : NativeInstall.SumRulesRefines := by
  intro _ _ _ _ _ _ _ _ _ _ hrel hfe hrec hty hcs hrhss h
  exact SumInstall.sum_rules_refines hrel hfe hrec hty hcs hrhss h

/-- `Refine/IndNativeInstall.lean`'s `CheckStructFieldSortsIRefines`. -/
theorem checkStructFieldSortsIRefines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckStructFieldSortsIRefines mode := by
  intro _ _ _ _ _ _ _ _ _ _ _ hst hfe hs hfvs hidx hj h
  exact SumInstall.check_struct_field_sorts_i_refines hw hst hfe hs hfvs hidx hj h

/-- `Refine/IndNativeInstall.lean`'s `CheckSumIndCanon`: `check_sum_ind` keeps
the canonical pair, because the type former it installs is one `fenv::push`. -/
theorem checkSumIndCanon {mode : env.CheckMode} :
    NativeInstall.CheckSumIndCanon mode := by
  intro _ _ _ _ _ _ _ r hfe hcan hfull h hfe2
  obtain ⟨fe2, cv_ta, p2⟩ := r
  exact SumInstall.check_sum_ind_canon hfe hcan hfull h hfe2

/-- `Refine/IndNativeInstall.lean`'s `CheckSumIndRefines`, at **any** `CapsOf`
dictionary whose `caps_of` refines the Lean closure.  The dictionary's own
hypothesis is `SumInstall.CapsOfRefines` with the equation the other way
round. -/
theorem checkSumIndRefines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckSumIndRefines mode := by
  intro C inst d capsOf hcaps st st' fe p r hst hfe hp h lst lfe hsr hfr
  obtain ⟨fe2, cv_ta, p2⟩ := r
  obtain ⟨lst', lfe', hrun, hrel', hfe', hsr', hst', hcv', hp'⟩ :=
    SumInstall.check_sum_ind_refines hw (sumInstallCheckConstantVal hw)
      (fun q c hq hcq => ⟨(hcaps q c hq hcq).1.symm, (hcaps q c hq hcq).2⟩)
      hst hfe hp h lst lfe hsr hfr
  exact ⟨lst', lfe', hrun, hsr', hrel', hst', hfe', hcv', hp'⟩

/-- `Refine/IndNativeInstall.lean`'s `CheckSumCtorsRefines`, at the entry
reading `check_native_pass_ctors` spells: index `0`, both accumulators
empty. -/
theorem checkSumCtorsRefines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckSumCtorsRefines mode := by
  intro st st' fe0 fe t lps n_p n_idx res_sort is_prop large cv_ta cs r
    hst hfe0 hfe ht hlps hsort hcvta hcs h lst lfe0 lfe hsr hrel0 hrel
  obtain ⟨r1, r2⟩ := r
  obtain ⟨lst', lcs, lss, hrun, hcsr, hssr, hsr', hst', hr1, hr2⟩ :=
    SumInstall.check_sum_ctors_refines hw (sumInstallCheckConstantVal hw)
      sumInstallMentionsConst sumInstallOpenPisAtFvarsF sumInstallFvarTypes
      (checkStructDomsAtRefines hw) structCtorResidOkRefines sumInstallParamsOf
      sumInstallConstsResolveFFast hst hfe0 hfe hrel0 ht hlps hsort hcvta hcs
      (by intro c hc; simp [alloc.vec.Vec.new] at hc)
      (by intro us hus; simp [alloc.vec.Vec.new] at hus) h lst lfe hsr hrel
  refine ⟨lst', ?_, hsr', hst', hr1, hr2⟩
  have he1 : IndAbs.absCtors r1 = lcs := by
    simpa [IndAbs.absCtors, alloc.vec.Vec.new] using hcsr
  have he2 : IndAbs.absLevelss r2 = lss := by
    simpa [IndAbs.absLevelss, alloc.vec.Vec.new] using hssr
  rw [he1, he2]
  simpa using hrun

/-! ### The four failure halves the direct route asks for separately

Task #67's restatement reached `Refine/IndNativeInstall.lean` before this
file, so that file states four of its ingredients' `.Err` halves as *separate*
`Prop`s beside the accept ones rather than folding them in.  Each is
discharged here from the very lemma the accept ingredient already uses, at
`.Err ce`, where that lemma's full-outcome `match` reduces.  They fold into
their accept siblings whenever `Refine/IndNativeInstall.lean` is next
touched. -/

/-- `Refine/IndNativeInstall.lean`'s `CheckConstantValErr`. -/
theorem nativeInstallCheckConstantValErr {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckConstantValErr mode := by
  intro _ _ _ _ _ hsw hfw hcv h
  exact CheckerBase.check_constant_val_refines IndAbs.check_fuel_eq hw
    constsResolveFSpec hsw hfw hcv h

/-- `Refine/IndNativeInstall.lean`'s `CheckStructFieldSortsIErr`. -/
theorem checkStructFieldSortsIErr {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckStructFieldSortsIErr mode := by
  intro _ _ _ _ _ _ _ _ _ _ _ hst hfe hs hfvs hidx hj h
  exact SumInstall.check_struct_field_sorts_i_refines hw hst hfe hs hfvs hidx hj h

/-- `Refine/IndNativeInstall.lean`'s `CheckSumIndErr`. -/
theorem checkSumIndErr {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckSumIndErr mode := by
  intro C inst d capsOf hcaps st st' fe p ce hst hfe hp h lst lfe hsr hfr
  exact SumInstall.check_sum_ind_refines hw (sumInstallCheckConstantVal hw)
    (fun q c hq hcq => ⟨(hcaps q c hq hcq).1.symm, (hcaps q c hq hcq).2⟩)
    hst hfe hp h lst lfe hsr hfr

/-- `Refine/IndNativeInstall.lean`'s `CheckSumCtorsErr`. -/
theorem checkSumCtorsErr {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) :
    NativeInstall.CheckSumCtorsErr mode := by
  intro st st' fe0 fe t lps n_p n_idx res_sort is_prop large cv_ta cs ce
    hst hfe0 hfe ht hlps hsort hcvta hcs h lst lfe0 lfe hsr hrel0 hrel
  exact SumInstall.check_sum_ctors_refines hw (sumInstallCheckConstantVal hw)
    sumInstallMentionsConst sumInstallOpenPisAtFvarsF sumInstallFvarTypes
    (checkStructDomsAtRefines hw) structCtorResidOkRefines sumInstallParamsOf
    sumInstallConstsResolveFFast hst hfe0 hfe hrel0 ht hlps hsort hcvta hcs
    (by intro c hc; simp [alloc.vec.Vec.new] at hc)
    (by intro us hus; simp [alloc.vec.Vec.new] at hus) h lst lfe hsr hrel

/-! ## The two `Vec`-indexing discharges

Both ingredients carry a `≤ Std.Usize.max` side condition in their own
statement (`Refine/Scalars.lean`: the port reads `v[i as usize]` off a `u64`
counter and the cast wraps on a 32-bit target), so neither discharge assumes
anything about the platform.  `kind_get_d_refines` still needs the bound — the
index is the caller's.  `struct_proj_guards_refines` no longer does:
`Refine/IndStructParts.lean` discharges it internally, off the `nF`-long `used`
table its own walk builds, and `NativeInstall.StructProjGuardsRefines` dropped
the bound with it (`native_install::check_native_table` has no `Vec` of the
single constructor's field count in hand and so could not have supplied one). -/

/-- `Refine/IndNativeInstall.lean`'s `KindGetDRefines`. -/
theorem kindGetDRefines : NativeInstall.KindGetDRefines := by
  intro _ _ _ hi h
  exact NativeParts.kind_get_d_refines hi h

/-- `Refine/IndNativeInstall.lean`'s `StructProjGuardsRefines`. -/
theorem structProjGuardsRefines : NativeInstall.StructProjGuardsRefines := by
  intro _ _ _ _ _ hcty hsorts h
  exact StructParts.struct_proj_guards_refines hcty hsorts h


end ConRon.Refine.IndIngredients
