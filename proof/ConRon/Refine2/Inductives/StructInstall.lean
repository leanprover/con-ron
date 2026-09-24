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

/-! ## `unwrap_or` at the handle types this lane's walks unwrap

`checker_base::unwrap_or` against `unwrapOr` (the checker tier's
`unwrap_or_refines` was `sorry` when this was written, and
`PrimsModeled.lean`'s proved copy is downstream of this file).  One `@[lockstep]` lemma per element abstraction
and error kind: the tactic applies a spec before it matches the twin, so the
abstraction cannot be left to unification; the twin's message is free. -/

namespace IndInstPrims

open Lockstep

theorem unwrap_or_lsr {T β : Type} {A : T → β} {pers st lst} {o : Option T}
    {err : kernel.core_types.CheckError} {lerr : Arena.CheckError}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (herr : absAErrKind err = lAErrKind lerr) :
    LSR pers (fun a b => b = A a) (arena.checker_base.unwrap_or o err) st lst
      (unwrapOr (o.map A) lerr) := by
  refine LSR.ofSimRE hrel hinv fun r hrun => ?_
  cases o with
  | none =>
    simp only [arena.checker_base.unwrap_or, Result.ok.injEq] at hrun
    subst hrun
    exact errSim_fail herr
  | some a =>
    simp only [arena.checker_base.unwrap_or, Result.ok.injEq] at hrun
    subst hrun
    rfl

@[lockstep] theorem unwrap_or_eidx_int {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {o : Option arena.handle.EIdx} {m : alloc.vec.Vec Std.U32} {s : String} :
    LSR pers (fun a b => b = absEIdx a)
      (arena.checker_base.unwrap_or o (kernel.core_types.CheckError.Internal m)) st lst
      (unwrapOr (o.map absEIdx) (.internal s)) :=
  unwrap_or_lsr hrel hinv rfl

@[lockstep] theorem unwrap_or_eidx_vec_int {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {o : Option (alloc.vec.Vec arena.handle.EIdx)} {m : alloc.vec.Vec Std.U32} {s : String} :
    LSR pers (fun a b => b = (absEIdxL a).toArray)
      (arena.checker_base.unwrap_or o (kernel.core_types.CheckError.Internal m)) st lst
      (unwrapOr ((o.map absEIdxL).map List.toArray) (.internal s)) := by
  rw [Option.map_map]
  exact unwrap_or_lsr hrel hinv rfl

/-- `kernel::level::leq` against `Level.leq` (the pure comparison; the
`liftFueled` around it is the checker tier's `lift_fueled_ls`). -/
@[lockstep] theorem level_leq_ls (l r : kernel.level.Level) (hl : ConRon.Refine.LevelWF l)
    (hr : ConRon.Refine.LevelWF r) :
    LSP (kernel.level.leq l r)
      (fun o => TwinEq (ConLeche.Level.leq (ConRon.Refine.absLevel l)
        (ConRon.Refine.absLevel r)) o) :=
  fun _ h => ConRon.Refine.Level.leq_refines hl hr h

/-- `checker_base::fvar_type_ds` ⊑ `List.mapM fvarTypeD` from the cursor on,
with the accumulator in front (the checker tier's statement was `sorry` when
this was written — `Checker/Base.lean`'s `fvar_type_ds_ls` now;
`PrimsModeled.lean` carries the same induction downstream of this file). -/
theorem fvar_type_ds_aux (n : Nat) :
    ∀ {pers st lst} {hs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
      {out : alloc.vec.Vec arena.handle.EIdx},
      hs.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absEIdxL a) (arena.checker_base.fvar_type_ds pers st hs i out)
        st lst (do pure (absEIdxL out ++ (← List.mapM fvarTypeD (absEIdxLFrom hs i)))) := by
  induction n with
  | zero =>
    intro pers st lst hs i out hn hrel hinv
    apply LSR.of_LS
    rw [arena.checker_base.fvar_type_ds, if_pos (by scalar_tac), absEIdxLFrom,
      vecFrom_nil _ _ _ (by omega), List.mapM_nil]
    lockstep
  | succ m ih =>
    intro pers st lst hs i out hn hrel hinv
    apply LSR.of_LS
    rw [arena.checker_base.fvar_type_ds, if_neg (by scalar_tac), absEIdxLFrom,
      vecFrom_cons _ _ _ (by omega), List.mapM_cons]
    lockstep

/-- `fvar_type_ds` from the cursor `0` and an empty accumulator: the twin's
`xs.mapM fvarTypeD`. -/
@[lockstep] theorem fvar_type_ds_mapM_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdxL a)
      (arena.checker_base.fvar_type_ds pers st hs 0#usize (alloc.vec.Vec.new _)) st lst
      (List.mapM fvarTypeD (hs.val.map absEIdx)) := by
  have h := fvar_type_ds_aux (hs := hs) (i := 0#usize) (out := alloc.vec.Vec.new _) _ rfl hrel hinv
  simpa [absEIdxL, absEIdxLFrom, alloc.vec.Vec.new] using h

/-- The twin's `unwrapOr` at a constructor (the port matches the `Option`
itself).  Scoped: `open scoped ConRon.Refine2.IndInstPrims`. -/
@[scoped lockstep_simp] theorem unwrapOr_some' {α : Type} (a : α) (e : Arena.CheckError) :
    unwrapOr (some a) e = pure a := rfl

@[scoped lockstep_simp] theorem unwrapOr_none' {α : Type} (e : Arena.CheckError) :
    unwrapOr (none : Option α) e = Arena.fail e := rfl

end IndInstPrims

/-! ## The binder-domain walk -/

set_option maxHeartbeats 1000000 in
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
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  induction hk : k.val generalizing k st lst with
  | zero =>
    rw [arena.inductives.struct_install.check_struct_doms_at.eq_def,
      if_pos (by scalar_tac), show absU k = 0 from hk, checkStructDomsAt]
    lockstep
  | succ m ih =>
    rw [arena.inductives.struct_install.check_struct_doms_at.eq_def,
      if_neg (by scalar_tac), show absU k = m + 1 from hk, checkStructDomsAt]
    have hk1 : 1 ≤ k.val := by omega
    obtain rfl : m = k.val - 1 := by omega
    clear hk
    dsimp only
    simp only [absEIdxL]
    by_cases hf : k.val - 1 < fvs.val.length
    · rw [List.getElem?_map, List.getElem?_eq_getElem hf, Option.map_some]
      by_cases hd : k.val - 1 < doms.val.length
      · rw [List.getElem?_map (l := doms.val), List.getElem?_eq_getElem hd, Option.map_some]
        lockstep
      · rw [List.getElem?_map (l := doms.val), List.getElem?_eq_none (by omega), Option.map_none]
        lockstep
    · rw [List.getElem?_map, List.getElem?_eq_none (by omega), Option.map_none]
      lockstep

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
  refine Lockstep.LS.toSim₀ ?_ hrun
  revert st lst hrel hinv hrun
  simp only [absEIdxLFrom]
  intro st lst hrel hinv _
  refine ls_cursor bodies absEIdx (projBodiesScopedSpec lf (absNIdxL lps) (absU n_p))
    (fun st i => arena.inductives.struct_install.proj_bodies_scoped pers vis st rf lps n_p bodies i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.struct_install.proj_bodies_scoped.eq_def, projBodiesScopedSpec]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.struct_install.proj_bodies_scoped.eq_def, projBodiesScopedSpec]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

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
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  induction hk : n_f.val - j.val generalizing j st lst with
  | zero =>
    rw [arena.inductives.struct_install.proj_fn_family_free.eq_def,
      if_pos (by scalar_tac), projFnFamilyFreeSpec]
    lockstep
  | succ m ih =>
    rw [arena.inductives.struct_install.proj_fn_family_free.eq_def,
      if_neg (by scalar_tac), projFnFamilyFreeSpec]
    lockstep

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
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.struct_install.check_struct_proj_table_names,
    checkStructProjTableNamesSpec]
  lockstep
  all_goals
    simp only [absIConstantInfo, absIProjTable] at *
    lockstep

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
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.struct_install.check_struct_proj_table,
    checkStructProjTable_unfold]
  lockstep

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
