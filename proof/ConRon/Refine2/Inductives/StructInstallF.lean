/-
# `ConRon.Refine2.Inductives.StructInstallF` — Theorem 2 for `arena::inductives::struct_install_f`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/struct_install_f.rs` against
`proof/ConRon/Arena/Inductives/StructInstallF.lean`.

**Three one-line delegations against three `abbrev`s.**  con-leche carries
each of `StructInstall.lean`'s two functions twice — once over `Env` and once
over `FEnv` — and `checkStructDomsAtFA` a third time over `Array`; the arena
has ONE environment type (task #97c's deviation 1), so the `F` twins ARE
`Arena/Inductives/StructInstall.lean`'s and this module is the `F`-suffixed
NAMES.  The port does the same: each `…_f` is one call of the function the
`abbrev` abbreviates.

So each statement below is the corresponding
`Refine2/Inductives/StructInstall.lean` statement with the twin spelled under
its `F` name — which is what makes the two sides' provenance readable from
con-leche's cached tier, and costs one `rfl` of proof beyond the delegate.
-/
import ConRon.Refine2.Inductives.StructInstall

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- `check_struct_doms_at_f` ⊑ `checkStructDomsAtF`. -/
theorem check_struct_doms_at_f_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {off : Std.U64}
    {fvs doms : alloc.vec.Vec arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.struct_install_f.check_struct_doms_at_f pers vis st mode
      rf off fvs doms k = ok o) :
    Sim (fun _ => ()) (fun _ => True) pers lst o
      (checkStructDomsAtF (ConRon.Refine.absMode mode) lf (absU off) (absEIdxL fvs)
        (absEIdxL doms) (absU k)) := by
  sorry

/-- `check_struct_doms_at_fa` ⊑ `checkStructDomsAtFA` — con-leche's `Array`
spelling of the same walk; over handles the container is the caller's and the
function is the one above. -/
theorem check_struct_doms_at_fa_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {off : Std.U64}
    {fvs doms : alloc.vec.Vec arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hvis : absU vis = lf.visibleBelow) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.struct_install_f.check_struct_doms_at_fa pers vis st
      mode rf off fvs doms k = ok o) :
    Sim (fun _ => ()) (fun _ => True) pers lst o
      (checkStructDomsAtFA (ConRon.Refine.absMode mode) lf (absU off)
        (absEIdxL fvs) (absEIdxL doms) (absU k)) := by
  sorry

/-- `check_struct_proj_table_f` ⊑ `checkStructProjTableF`. -/
theorem check_struct_proj_table_f_refines {pers st lst}
    {t c : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {res_sort : arena.handle.LIdx}
    {guards : alloc.vec.Vec arena.handle.LIdx} {off : Std.U64}
    {cv_ca : arena.env.IConstantVal} {rf lf} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.struct_install_f.check_struct_proj_table_f pers st t c
      lps n_p n_f res_sort guards off cv_ca rf = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkStructProjTableF (absNIdx t) (absNIdx c) (absNIdxL lps) (absU n_p)
        (absU n_f) (absLIdx res_sort) (absLIdxL guards) (absU off)
        (absIConstantVal cv_ca) lf) := by
  sorry

end ConRon.Refine2
