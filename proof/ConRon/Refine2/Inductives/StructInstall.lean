/-
# `ConRon.Refine2.Inductives.StructInstall` — Theorem 2 for `arena::inductives::struct_install`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/struct_install.rs` against
`proof/ConRon/Arena/Inductives/StructInstall.lean`: the binder-domain walk
and the checks of the projection TABLE a structure-like member installs (the
table itself is read off the block, `Refine2/Checker/Install.lean`), and the
per-field universe bound (`check_struct_field_sorts_i`; `field_sort_bound` is
`Spec.lean`'s `fieldSortBoundSpec`, `eidx_contains` is `List.contains`, a
`TwinEq`).

**Three `pub fn`s against two twin `def`s**, the extra one DESIGN §3.4's rule
at `checkStructProjTable`'s `allM`.  `Refine2/Inductives/Spec.lean` carries the
transcriptions.

The Core tier reaches it at two sites: `check_struct_doms_at` calls
`is_def_eq_core` (`Refine2/Checker/KnotHyp.lean`'s `is_def_eq_core_ls`), and
`check_struct_field_sorts_i` calls `infer_type_core` and `ensure_sort_core`.
-/
import ConRon.Refine2.Inductives.StructParts
import ConRon.Refine2.Inductives.Env
import ConRon.Refine2.Core.LS.Prims
import ConRon.Refine2.Checker.Base
import ConRon.Refine2.Inductives.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

/-! ## `unwrap_or` at the handle types this lane's walks unwrap

`checker_base::unwrap_or` against `unwrapOr` (no other tier states it).  One `@[lockstep]` lemma per element abstraction
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
  intro r hrun
  cases o with
  | none =>
    simp only [arena.checker_base.unwrap_or, Result.ok.injEq] at hrun
    subst hrun
    exact errSim_fail herr
  | some a =>
    simp only [arena.checker_base.unwrap_or, Result.ok.injEq] at hrun
    subst hrun
    exact ⟨A a, lst, rfl, rfl, hrel, hinv⟩

@[lockstep] theorem unwrap_or_eidx_int {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {o : Option arena.handle.EIdx} {m : alloc.vec.Vec Std.U32} {s : String} :
    LSR pers (fun a b => b = absEIdx a)
      (arena.checker_base.unwrap_or o (kernel.core_types.CheckError.Internal m)) st lst
      (unwrapOr (o.map absEIdx) (.internal s)) :=
  unwrap_or_lsr hrel hinv rfl

/-- `kernel::level::leq` against `Level.leq` (the pure comparison; the
`liftFueled` around it is the checker tier's `lift_fueled_ls`). -/
@[lockstep] theorem level_leq_ls (l r : kernel.level.Level) (hl : ConRon.Refine.LevelWF l)
    (hr : ConRon.Refine.LevelWF r) :
    LSP (kernel.level.leq l r)
      (fun o => TwinEq (ConLeche.Level.leq (ConRon.Refine.absLevel l)
        (ConRon.Refine.absLevel r)) o) :=
  fun _ h => ConRon.Refine.Level.leq_refines hl hr h

end IndInstPrims

/-! ## The binder-domain walk -/

open Lockstep in
set_option maxHeartbeats 1000000 in
/-- `check_struct_doms_at` ⊑ `checkStructDomsAt` — the reference kernels'
binder-domain comparisons, run binder by binder at its own frame.  Walks from
the last binder to the first, which is why the counter is the twin's `j + 1`
recursion and not a cursor. -/
@[lockstep] theorem check_struct_doms_at_ls
    {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {off : Std.U64}
    {fvs doms : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.struct_install.check_struct_doms_at pers st mode rf off fvs doms k) lst
      (checkStructDomsAt (ConRon.Refine.absMode mode) lf (absU off) (absEIdxL fvs)
        (absEIdxL doms) (absU k)) := by
  induction hk : k.val generalizing k st lst with
  | zero =>
    rw [arena.inductives.struct_install.check_struct_doms_at.eq_def,
      ite_eq_left (by scalar_tac), show absU k = 0 from hk, checkStructDomsAt]
    lockstep
  | succ m ih =>
    rw [arena.inductives.struct_install.check_struct_doms_at.eq_def,
      ite_eq_right (by scalar_tac), show absU k = m + 1 from hk, checkStructDomsAt]
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

/-! ## The projection table -/

open Lockstep in
/-- `proj_bodies_scoped` ⊑ `checkStructProjTable`'s `scopedOk` `let`, from the
cursor on. -/
@[lockstep] theorem proj_bodies_scoped_ls
    {pers st lst}
    {rf lf}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p : Std.U64}
    {bodies : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun a b => b = id a) (arena.inductives.struct_install.proj_bodies_scoped pers st rf lps n_p bodies i) lst
      (projBodiesScopedSpec lf (absNIdxL lps) (absU n_p)
        (absEIdxLFrom bodies i)) := by
  revert st lst hrel hinv
  simp only [absEIdxLFrom]
  intro st lst hrel hinv
  refine ls_cursor bodies absEIdx (projBodiesScopedSpec lf (absNIdxL lps) (absU n_p))
    (fun st i => arena.inductives.struct_install.proj_bodies_scoped pers st rf lps n_p bodies i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.struct_install.proj_bodies_scoped.eq_def, projBodiesScopedSpec]
    rw [ite_eq_left (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.struct_install.proj_bodies_scoped.eq_def, projBodiesScopedSpec]
    rw [ite_eq_right (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
/-- `check_struct_proj_table` ⊑ `checkStructProjTable` — stage 5, the projection
table's checks at the table the block installs: its bodies' scoping, the
structure stored and its table free.  Nothing is pushed. -/
@[lockstep] theorem check_struct_proj_table_ls
    {pers st lst}
    {t : arena.env.IProjTable}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.struct_install.check_struct_proj_table pers st t rf) lst
      (checkStructProjTable (absIProjTable t) lf) := by
  rw [arena.inductives.struct_install.check_struct_proj_table,
    checkStructProjTable_unfold, checkStructProjTableTailSpec]
  simp only [absIProjTable]
  lockstep

/-! ## The per-field universe bound -/

/-- `eidx_contains` ⊑ `idxArgs.contains fv` from the cursor on — handles, so
`==` is word equality and the test transfers by `absEIdx`'s injectivity. -/
theorem eidx_contains_refines {xs : alloc.vec.Vec arena.handle.EIdx}
    {x : arena.handle.EIdx} {i : Std.Usize} {o}
    (hrun : arena.inductives.struct_install.eidx_contains xs x i = ok o) :
    o = (absEIdxLFrom xs i).contains (absEIdx x) := by
  simp only [absEIdxLFrom, List.contains_eq_any_beq, List.any_map, Function.comp_def]
  refine vec_cursor_any xs _
    (arena.inductives.struct_install.eidx_contains xs x) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.struct_install.eidx_contains.eq_def] at h
    rw [ite_eq_left (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i y o hy h
    have hlt : i.val < xs.val.length := (List.getElem?_eq_some_iff.mp hy).1
    rw [arena.inductives.struct_install.eidx_contains.eq_def] at h
    rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hey : e = y := by
      have h1 := vec_index_some he; rw [hy] at h1; exact (Option.some_inj.mp h1).symm
    subst hey
    have hbv : b = (absEIdx x == absEIdx e) := by
      rw [eidx_eq2_abs hb]
      by_cases hcc : absEIdx e = absEIdx x
      · simp [hcc]
      · have hcc' : ¬ absEIdx x = absEIdx e := fun z => hcc z.symm
        simp [hcc, hcc']
    cases hbb : b
    · rw [hbb] at h hbv
      rw [ite_eq_right (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [ite_eq_left (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

open Lockstep in
/-- `eidx_contains_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem eidx_contains_twin0
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {x : arena.handle.EIdx} :
    LSP (arena.inductives.struct_install.eidx_contains xs x 0#usize) (fun o => TwinEq ((absEIdxL xs).contains (absEIdx x)) (o)) := by
  intro o h
  have h' := (eidx_contains_refines h).symm
  simpa [Lockstep.TwinEq, absEIdxLFrom, absEIdxL, alloc.vec.Vec.new] using h'

open Lockstep in
/-- `field_sort_bound` ⊑ `checkStructFieldSortsI`'s per-field universe
bound. -/
@[lockstep] theorem field_sort_bound_ls
    {pers st lst}
    {is_prop large : Bool}
    {s u : arena.handle.LIdx}
    {fv : arena.handle.EIdx}
    {idx_args : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ => ()) a) (arena.inductives.struct_install.field_sort_bound pers st is_prop large s u fv idx_args) lst
      (fieldSortBoundSpec is_prop large (absLIdx s) (absLIdx u) (absEIdx fv)
        (absEIdxL idx_args)) := by
  rw [arena.inductives.struct_install.field_sort_bound, fieldSortBoundSpec]
  lockstep

/-- `checkStructFieldSortsI`'s step with the per-field bound named as the
port's `field_sort_bound` (`fieldSortBoundSpec`). -/
theorem checkStructFieldSortsI_succ_port (mode : ConLeche.CheckMode) (fe : IFEnv)
    (isProp large : Bool) (s : LIdx) (nP : Nat) (fvs idxArgs : List EIdx) (j : Nat) :
    checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs (j + 1) = (do
      let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
      let ty ← inferTypeCore mode fe checkFuel (nP + j) (← fvarTypeD fv)
      let u ← ensureSortCore mode fe checkFuel (nP + j) ty
      fieldSortBoundSpec isProp large s u fv idxArgs
      checkStructFieldSortsI mode fe isProp large s nP fvs idxArgs j) := by
  rw [checkStructFieldSortsI]
  simp only [fieldSortBoundSpec]
  congr 1; funext fv; congr 1; funext d; congr 1; funext ty; congr 1; funext u
  split
  · simp only [bind_assoc]
    congr 1; funext lu; congr 1; funext ls; congr 1; funext b
    split <;> simp
  · split
    · simp only [bind_assoc]
      congr 1; funext z; congr 1; funext b
      split <;> simp
    · simp

open Lockstep in
/-- `check_struct_field_sorts_i` ⊑ `checkStructFieldSortsI` — the fields'
domains have sorts over the opened constructor telescope, under the official
per-field universe bound unless the family is propositional.  Walks the fields
from the last to the first, which is why the counter is the twin's `j + 1`
recursion. -/
@[lockstep] theorem check_struct_field_sorts_i_ls
    {pers st lst}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {is_prop large : Bool}
    {s : arena.handle.LIdx}
    {n_p : Std.U64}
    {fvs idx_args : alloc.vec.Vec arena.handle.EIdx}
    {k : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI pers rf lf) :
    LS pers (fun _ _ => True) (arena.inductives.struct_install.check_struct_field_sorts_i pers st mode rf is_prop large s n_p fvs idx_args k) lst
      (checkStructFieldSortsI (ConRon.Refine.absMode mode) lf is_prop large
        (absLIdx s) (absU n_p) (absEIdxL fvs) (absEIdxL idx_args) (absU k)) := by
  induction hk : k.val generalizing k st lst with
  | zero =>
    rw [arena.inductives.struct_install.check_struct_field_sorts_i.eq_def,
      ite_eq_left (by scalar_tac), show absU k = 0 from hk, checkStructFieldSortsI]
    lockstep
  | succ m ih =>
    rw [arena.inductives.struct_install.check_struct_field_sorts_i.eq_def,
      ite_eq_right (by scalar_tac), show absU k = m + 1 from hk, checkStructFieldSortsI_succ_port]
    have hk1 : 1 ≤ k.val := by omega
    obtain rfl : m = k.val - 1 := by omega
    clear hk
    dsimp only
    simp only [absEIdxL]
    by_cases hf : k.val - 1 < fvs.val.length
    · rw [List.getElem?_map, List.getElem?_eq_getElem hf, Option.map_some]
      lockstep
    · rw [List.getElem?_map, List.getElem?_eq_none (by omega), Option.map_none]
      lockstep

end ConRon.Refine2
