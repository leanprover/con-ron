/-
# `ConRon.Refine2.Inductives.StructInstall` — Theorem 2 for `arena::inductives::struct_install`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/struct_install.rs` against
`proof/ConRon/Arena/Inductives/StructInstall.lean`: the binder-domain walk
and the projection TABLE the fixpoint route stores at a structure-like block.

**Five `pub fn`s against two twin `def`s**, and the three extra are DESIGN
§3.4's rules at `checkStructProjTable`'s two `allM`s and its `let`-boundary.
`Refine2/Inductives/Spec.lean` carries all three transcriptions.

**Finding 10 reaches this module.**  `check_struct_doms_at`,
`proj_bodies_scoped` and `proj_fn_family_free` take `vis : u64` beside `fe`
(task #97-P6-6b), so each carries `hvis : absU vis = lf.visibleBelow`.
`check_struct_proj_table` and its `_names` tail do NOT: they take `fe` by
value and read `fe.visible_below` themselves, which `IFEnvRel.visibleBelow`
settles inside the proof.

**`KnotRel` reaches it too**, at one site: `check_struct_doms_at` calls
`is_def_eq_core`, which is the Core tier's.
-/
import ConRon.Refine2.Inductives.StructParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

/-! ## The binder-domain walk -/

/-- `check_struct_doms_at` ⊑ `checkStructDomsAt` — the reference kernels'
binder-domain comparisons, run binder by binder at its own frame.  Walks from
the last binder to the first, which is why the counter is the twin's `j + 1`
recursion and not a cursor. -/
theorem check_struct_doms_at_refines {pers st lst} {vis : Std.U64} {rf lf}
    {mode : kernel.env.CheckMode} {off : Std.U64}
    {fvs doms : alloc.vec.Vec arena.handle.EIdx} {k : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.struct_install.check_struct_doms_at pers vis st mode rf
      off fvs doms k = ok o) :
    Sim₀ (fun _ => ()) pers lst o
      (checkStructDomsAt (ConRon.Refine.absMode mode) lf (absU off) (absEIdxL fvs)
        (absEIdxL doms) (absU k)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_struct_doms_at_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {off : Std.U64}
    {fvs doms : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.struct_install.check_struct_doms_at pers vis st mode rf off fvs doms k) lst
      (checkStructDomsAt (ConRon.Refine.absMode mode) lf (absU off) (absEIdxL fvs)
        (absEIdxL doms) (absU k)) :=
  LS.ofSim₀ fun _ h => check_struct_doms_at_refines hrel hinv hfe hvis h

/-! ## The projection table -/

/-- `proj_bodies_scoped` ⊑ `checkStructProjTable`'s `scopedOk` `let`, from the
cursor on. -/
theorem proj_bodies_scoped_refines {pers st lst} {vis : Std.U64} {rf lf}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p : Std.U64}
    {bodies : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.struct_install.proj_bodies_scoped pers vis st rf lps n_p
      bodies i = ok o) :
    Sim₀ id pers lst o
      (projBodiesScopedSpec lf (absNIdxL lps) (absU n_p)
        (absEIdxLFrom bodies i)) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_bodies_scoped_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {bodies : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_install.proj_bodies_scoped pers vis st rf lps n_p bodies i) lst
      (projBodiesScopedSpec lf (absNIdxL lps) (absU n_p)
        (absEIdxLFrom bodies i)) :=
  LS.ofSim₀ fun _ h => proj_bodies_scoped_refines hrel hinv hfe hvis h

/-- `proj_fn_family_free` ⊑ the projection-function name family's freeness
from field `j` on — the twin's `(List.range nF).allM`. -/
theorem proj_fn_family_free_refines {pers st lst} {vis : Std.U64} {rf lf}
    {t : arena.handle.NIdx} {n_f j : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow)
    (hrun : arena.inductives.struct_install.proj_fn_family_free pers vis st rf t n_f
      j = ok o) :
    Sim₀ id pers lst o
      (projFnFamilyFreeSpec lf (absNIdx t) (absU n_f - absU j) (absU j)) := by
  sorry

open Lockstep in
@[lockstep] theorem proj_fn_family_free_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {t : arena.handle.NIdx}
    {n_f j : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_install.proj_fn_family_free pers vis st rf t n_f j) lst
      (projFnFamilyFreeSpec lf (absNIdx t) (absU n_f - absU j) (absU j)) :=
  LS.ofSim₀ fun _ h => proj_fn_family_free_refines hrel hinv hfe hvis h

/-- `check_struct_proj_table_names` ⊑ `checkStructProjTable`'s tail. -/
theorem check_struct_proj_table_names_refines {pers st lst}
    {t c : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {res_sort : arena.handle.LIdx}
    {guards : alloc.vec.Vec arena.handle.LIdx} {off : Std.U64}
    {bodies : alloc.vec.Vec arena.handle.EIdx} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.struct_install.check_struct_proj_table_names pers st t c
      lps n_p n_f res_sort guards off bodies rf = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkStructProjTableNamesSpec (absNIdx t) (absNIdx c) (absNIdxL lps)
        (absU n_p) (absU n_f) (absLIdx res_sort) (absLIdxL guards) (absU off)
        (absEIdxL bodies).toArray lf) := by
  sorry

open Lockstep in
@[lockstep] theorem check_struct_proj_table_names_ls
    {pers st lst}
    {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {res_sort : arena.handle.LIdx}
    {guards : alloc.vec.Vec arena.handle.LIdx}
    {off : Std.U64}
    {bodies : alloc.vec.Vec arena.handle.EIdx}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.inductives.struct_install.check_struct_proj_table_names pers st t c lps n_p n_f res_sort guards off bodies rf) lst
      (checkStructProjTableNamesSpec (absNIdx t) (absNIdx c) (absNIdxL lps)
        (absU n_p) (absU n_f) (absLIdx res_sort) (absLIdxL guards) (absU off)
        (absEIdxL bodies).toArray lf) :=
  LS.ofSimRel₀ fun _ h => check_struct_proj_table_names_refines hrel hinv hfe h

/-- `check_struct_proj_table` ⊑ `checkStructProjTable` — stage 5, the
projection table.  `IProjTable.tableName` is the reserved name the install
interned, kept rather than recomputed (`Arena/Env.lean`'s one added field). -/
theorem check_struct_proj_table_refines {pers st lst}
    {t c : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64} {res_sort : arena.handle.LIdx}
    {guards : alloc.vec.Vec arena.handle.LIdx} {off : Std.U64}
    {cv_ca : arena.env.IConstantVal} {rf lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.struct_install.check_struct_proj_table pers st t c lps
      n_p n_f res_sort guards off cv_ca rf = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkStructProjTable (absNIdx t) (absNIdx c) (absNIdxL lps) (absU n_p)
        (absU n_f) (absLIdx res_sort) (absLIdxL guards) (absU off)
        (absIConstantVal cv_ca) lf) := by
  sorry

open Lockstep in
@[lockstep] theorem check_struct_proj_table_ls
    {pers st lst}
    {t c : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {res_sort : arena.handle.LIdx}
    {guards : alloc.vec.Vec arena.handle.LIdx}
    {off : Std.U64}
    {cv_ca : arena.env.IConstantVal}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.inductives.struct_install.check_struct_proj_table pers st t c lps n_p n_f res_sort guards off cv_ca rf) lst
      (checkStructProjTable (absNIdx t) (absNIdx c) (absNIdxL lps) (absU n_p)
        (absU n_f) (absLIdx res_sort) (absLIdxL guards) (absU off)
        (absIConstantVal cv_ca) lf) :=
  LS.ofSimRel₀ fun _ h => check_struct_proj_table_refines hrel hinv hfe h

end ConRon.Refine2
