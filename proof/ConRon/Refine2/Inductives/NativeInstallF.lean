/-
# `ConRon.Refine2.Inductives.NativeInstallF` — Theorem 2 for `arena::inductives::native_install_f`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/native_install_f.rs` against
`proof/ConRon/Arena/Inductives/NativeInstallF.lean`.

**Five one-line delegations against five `abbrev`s.**  con-leche's
`NativeInstallF.lean` is `NativeInstall.lean`'s five `StructWalkers`-taking
functions over an `FEnv`; the arena has ONE environment type and no
`StructWalkers` seam, so the `F` twins ARE `Arena/Inductives/NativeInstall.lean`'s
and this module is the `F`-suffixed NAMES.
-/
import ConRon.Refine2.Inductives.NativeInstall

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- `native_opened_ok_f` ⊑ `nativeOpenedOkF`. -/
theorem native_opened_ok_f_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64} {cty : arena.handle.EIdx} {n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install_f.native_opened_ok_f pers vis st rf0 t
      lps n_p n_idx cty n_f ks = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeOpenedOkF lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx cty) (absU n_f) (absKindL ks)) := by
  sorry

/-- `native_fields_ok_f` ⊑ `nativeFieldsOkF`. -/
theorem native_fields_ok_f_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install_f.native_fields_ok_f pers vis st rf0 t
      lps n_p n_idx ctors_a kinds = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldsOkF lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a) (absKindLL kinds)) := by
  sorry

/-- `check_native_rules_f` ⊑ `checkNativeRulesF` from the `j`-th rule on. -/
theorem check_native_rules_f_refines {pers st lst} {vis : Std.U64} {rfR lfR}
    {rlps : alloc.vec.Vec arena.handle.NIdx} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_idx : Std.U64} {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx} {rlvls : arena.handle.LsIdx} {k j : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rfR lfR) (hfinv : IFEnvInv rfR)
    (hvis : absU vis = lfR.visibleBelow)
    (hrun : arena.inductives.native_install_f.check_native_rules_f pers vis st rfR
      rlps t lps elim large n_p n_idx tty ctors rec_c rlvls k j out = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (do pure (absEIdxL out ++
        (← checkNativeRulesF lfR (absNIdxL rlps) (absNIdx t) (absNIdxL lps)
          (absNIdx elim) large (absU n_p) (absU n_idx) (absEIdx tty)
          (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU k)
          (absU j)))) := by
  sorry

/-- `check_native_rec_f` ⊑ `checkNativeRecF` — finding 19's bracket carries
over: `o.2.2` is the pre-call environment. -/
theorem check_native_rec_f_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {p : arena.inductives.native_parts.NativeParts}
    {cv_ta : arena.env.IConstantVal}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install_f.check_native_rec_f pers st mode rf p
      cv_ta ctors_a = ok o) :
    Sim (fun r => (absIConstantVal r.1, absEIdxL r.2)) (fun _ => True) pers lst
      (o.1, o.2.1)
      (checkNativeRecF (ConRon.Refine.absMode mode) lf (absNativeParts p)
        (absIConstantVal cv_ta) (absCtorsL ctors_a)) ∧
      IFEnvRel o.2.2 lf := by
  sorry

/-- `check_native_table_f` ⊑ `checkNativeTableF`. -/
theorem check_native_table_f_refines {pers st lst}
    {p : arena.inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {rf lf} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.native_install_f.check_native_table_f pers st p ctors_a
      sortss rf = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNativeTableF (absNativeParts p) (absCtorsL ctors_a) (absLIdxLL sortss)
        lf) := by
  sorry

end ConRon.Refine2
