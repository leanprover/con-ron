/-
# `ConRon.Refine2.Inductives.SumInstallF` — Theorem 2 for `arena::inductives::sum_install_f`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/sum_install_f.rs` against
`proof/ConRon/Arena/Inductives/SumInstallF.lean`.

**Nine one-line delegations against eight `abbrev`s.**  con-leche's
`SumInstallF.lean` is `SumInstall.lean`'s stages over an `FEnv`; the arena has
ONE environment type (task #97c's deviation 1), so the `F` twins ARE
`Arena/Inductives/SumInstall.lean`'s and this module is the `F`-suffixed
NAMES.  The ninth is `native_caps_at`, re-exported here under the name
`arena::inductives::native_install` looks for — its twin is
`SumInstall.lean`'s, one module earlier than con-leche places it, and its
statement is `Refine2/Inductives/SumInstall.lean`'s under the same twin.
-/
import ConRon.Refine2.Inductives.SumInstall

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- `check_sum_tele_f` ⊑ `checkSumTeleF`. -/
theorem check_sum_tele_f_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {cv : arena.env.IConstantVal} {n : Std.U64}
    {cv_ta0 : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.check_sum_tele_f pers vis st mode rf cv n
      cv_ta0 = ok o) :
    Sim (fun r => (absIConstantVal r.1, absLIdx r.2)) (fun _ => True) pers lst o
      (checkSumTeleF (ConRon.Refine.absMode mode) lf (absIConstantVal cv) (absU n)
        (absIConstantVal cv_ta0)) := by
  sorry

/-- `check_sum_ind_f` ⊑ `checkSumIndF`.  con-leche's `capsOf` argument became
`isRec : Bool` at the twin (`Arena/Inductives/SumInstall.lean`'s module note
says why), and the `abbrev` has that signature. -/
theorem check_sum_ind_f_refines {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p : arena.inductives.sum_parts.InductiveShape} {is_rec : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.check_sum_ind_f pers st mode rf p is_rec
      = ok o) :
    SimRel (fun r v => IFEnvRel r.1 v.1 ∧ v.2.1 = absIConstantVal r.2.1 ∧
        v.2.2 = absInductiveShape r.2.2)
      pers lst o
      (checkSumIndF (ConRon.Refine.absMode mode) lf (absInductiveShape p)
        is_rec) := by
  sorry

/-- `check_struct_field_sorts_i_f` ⊑ `checkStructFieldSortsIF`. -/
theorem check_struct_field_sorts_i_f_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {is_prop large : Bool} {s : arena.handle.LIdx}
    {n_p : Std.U64} {fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.check_struct_field_sorts_i_f pers vis st
      mode rf is_prop large s n_p fvs idx_args k = ok o) :
    Sim absLIdxL (fun _ => True) pers lst o
      (checkStructFieldSortsIF (ConRon.Refine.absMode mode) lf is_prop large
        (absLIdx s) (absU n_p) (absEIdxL fvs) (absEIdxL idx_args) (absU k)) := by
  sorry

/-- `check_struct_field_sorts_i_fa` ⊑ `checkStructFieldSortsIFA` — con-leche's
`Array` spelling of the same walk. -/
theorem check_struct_field_sorts_i_fa_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {is_prop large : Bool} {s : arena.handle.LIdx}
    {n_p : Std.U64} {fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.check_struct_field_sorts_i_fa pers vis st
      mode rf is_prop large s n_p fvs idx_args k = ok o) :
    Sim absLIdxL (fun _ => True) pers lst o
      (checkStructFieldSortsIFA (ConRon.Refine.absMode mode) lf is_prop large
        (absLIdx s) (absU n_p) (absEIdxL fvs) (absEIdxL idx_args) (absU k)) := by
  sorry

/-- `norm_ctor_val_f` ⊑ `normCtorValF`. -/
theorem norm_ctor_val_f_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {t : arena.handle.NIdx} {n_p n_f : Std.U64}
    {cv_c cv_ca : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.norm_ctor_val_f pers vis st mode rf t n_p
      n_f cv_c cv_ca = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (normCtorValF (ConRon.Refine.absMode mode) lf (absNIdx t) (absU n_p)
        (absU n_f) (absIConstantVal cv_c) (absIConstantVal cv_ca)) := by
  sorry

/-- `check_sum_ctor_f` ⊑ `checkSumCtorF`. -/
theorem check_sum_ctor_f_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx} {is_prop large : Bool}
    {cv_c : arena.env.IConstantVal} {n_f : Std.U64}
    {cv_ta : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.check_sum_ctor_f pers st mode rf0 rf t lps
      n_p n_idx res_sort is_prop large cv_c n_f cv_ta = ok o) :
    Sim (fun r => (absIConstantVal r.1, absLIdxL r.2)) (fun _ => True) pers lst o
      (checkSumCtorF (ConRon.Refine.absMode mode) lf0 lf (absNIdx t) (absNIdxL lps)
        (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
        (absIConstantVal cv_c) (absU n_f) (absIConstantVal cv_ta)) := by
  sorry

/-- `check_sum_ctors_f` ⊑ `checkSumCtorsF` from the cursor on, with the
accumulated constructors and sort lists in front. -/
theorem check_sum_ctors_f_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf0 lf0} {rf lf} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {res_sort : arena.handle.LIdx} {is_prop large : Bool}
    {cv_ta : arena.env.IConstantVal}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sout : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe0 : IFEnvRel rf0 lf0) (hfinv0 : IFEnvInv rf0)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.sum_install_f.check_sum_ctors_f pers st mode rf0 rf t
      lps n_p n_idx res_sort is_prop large cv_ta ctors i out sout = ok o) :
    Sim (fun r => (absCtorsL r.1, absLIdxLL r.2)) (fun _ => True) pers lst o
      (do
        let q ← checkSumCtorsF (ConRon.Refine.absMode mode) lf0 lf (absNIdx t)
          (absNIdxL lps) (absU n_p) (absU n_idx) (absLIdx res_sort) is_prop large
          (absIConstantVal cv_ta) (absCtorsLFrom ctors i)
        pure (absCtorsL out ++ q.1, absLIdxLL sout ++ q.2)) := by
  sorry

/-- `cons_sum_ctors_f` ⊑ `consSumCtorsF` — pure on both sides. -/
theorem cons_sum_ctors_f_refines {n_p : Std.U64}
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {rf lf} {o}
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.sum_install_f.cons_sum_ctors_f n_p ctors i rf = ok o) :
    IFEnvRel o (consSumCtorsF (absU n_p) (absCtorsLFrom ctors i) lf) ∧
      IFEnvInv o := by
  sorry

/-- `sum_install_f::native_caps_at` ⊑ `nativeCapsAt` — the re-export under the
name `arena::inductives::native_install` looks for. -/
theorem native_caps_at_f_refines {pers st lst}
    {p : arena.inductives.sum_parts.InductiveShape} {is_rec : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.sum_install_f.native_caps_at pers st p is_rec = ok o) :
    Sim absIIndCaps (fun _ => True) pers lst o
      (nativeCapsAt (absInductiveShape p) is_rec) := by
  sorry

end ConRon.Refine2
