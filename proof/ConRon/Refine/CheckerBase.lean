import ConRon.Refine.TypeChecker
import ConRon.Refine.CoreKShapes
import ConLeche.Kernel.DeclCheck

/-! # `kernel::checker_base` — the declaration checker's common ground (task #56)

`CORE_PLAN.md` step 7.  `ConLeche/Kernel/CheckerBase.lean` (292 lines) holds
the one check every declaration kind runs first (`checkConstantVal`), the
strategy-independent telescope helpers every install path shares
(`domsMatchAux`, `openPisAtFvars`, `checkTypedList`, `checkAnnotList`,
`checkDefEqList`, `piResultSort`, `isEqHead`, `eqHeadLevel`, `unwrapOr`,
`Env.findCV?`) and the projection-rule stages (`checkProjShape`,
`checkProjRule`).  This file is its refinement.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.CheckerBase

/-! ## `level::name_nodup` — the one leaf `Refine/Level.lean` left

`Name.nodup` (`ConLeche/Kernel/Level.lean:213-216`) is spelled in `level.rs`
but was not needed before `checkConstantVal`; its index recursion tests the
*tail*, which is `name::contains_from` at `i + 1`. -/

/-- `ConLeche/Kernel/Level.lean:213-216` — `level::name_nodup_from` refines
`Name.nodup` of the suffix from `i`. -/
theorem name_nodup_from_refines {ns : alloc.vec.Vec name.Name} (hns : NamesWF ns) :
    ∀ k (i : Std.Usize), ns.val.length - i.val ≤ k → ∀ b : Bool,
      level.name_nodup_from ns i = ok b →
      b = ConLeche.Name.nodup ((absNames ns).drop i.val) := by
  intro k
  induction k with
  | zero =>
    intro i h b hb
    rw [level.name_nodup_from.eq_def] at hb; simp only [] at hb
    rw [if_pos (by scalar_tac)] at hb
    rw [absNames, ← List.map_drop, List.drop_eq_nil_of_le (by scalar_tac)]
    simp only [List.map_nil, show ConLeche.Name.nodup ([] : List ConLeche.Name) = true from rfl]
    simpa using hb.symm
  | succ k ih =>
    intro i h b hb
    rw [level.name_nodup_from.eq_def] at hb; simp only [] at hb
    split at hb
    · rw [absNames, ← List.map_drop, List.drop_eq_nil_of_le (by scalar_tac)]
      simp only [List.map_nil, show ConLeche.Name.nodup ([] : List ConLeche.Name) = true from rfl]
      simpa using hb.symm
    · rename_i hlt
      have hb2 : i.val < ns.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ns.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff] at hb
      obtain ⟨i2, hi2, y, hy, c, hc, hb⟩ := hb
      have hi2v : i2.val = i.val + 1 := by
        rw [hw] at hi2; simp only [Result.ok.injEq] at hi2; rw [← hi2, hwv]
      have hyv : y = ns.val[i.val] := by
        obtain ⟨y', hy', hy'v⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ns i hb2)
        rw [hy'] at hy; simp only [Result.ok.injEq] at hy; rw [← hy, hy'v]
      subst hyv
      have hyWF : NameWF ns.val[i.val] := hns _ (List.getElem_mem hb2)
      have hcabs := Name.contains_from_refines hns hyWF ns.val.length i2 (by scalar_tac) c hc
      rw [hi2v] at hcabs
      have hcc : (List.map absName (List.drop (i.val + 1) ns.val)).contains
            (absName ns.val[i.val]) = c := by
        rw [hcabs, Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem]
      rw [absNames, ← List.map_drop, List.drop_eq_getElem_cons hb2]
      simp only [List.map_cons, ConLeche.Name.nodup]
      rw [hcc]
      cases c with
      | true => simp only [Bool.not_true, Bool.false_and]; simpa using hb.symm
      | false =>
        simp only [Bool.false_eq_true, if_false] at hb
        have hih := ih i2 (by scalar_tac) b hb
        rw [hi2v, absNames, ← List.map_drop] at hih
        simpa using hih

/-- `ConLeche/Kernel/Level.lean:213-216` — `level::name_nodup` refines
`Name.nodup`. -/
theorem name_nodup_refines {ns : alloc.vec.Vec name.Name} {b : Bool}
    (hns : NamesWF ns) (h : level.name_nodup ns = ok b) :
    b = ConLeche.Name.nodup (absNames ns) := by
  rw [level.name_nodup] at h
  have hh := name_nodup_from_refines hns ns.val.length 0#usize (by scalar_tac) b h
  simpa using hh

end ConRon.Refine.CheckerBase
