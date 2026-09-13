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
    simp only [ConLeche.Name.nodup]
    simpa using hb.symm
  | succ k ih =>
    intro i h b hb
    rw [level.name_nodup_from.eq_def] at hb; simp only [] at hb
    split at hb
    · rw [absNames, ← List.map_drop, List.drop_eq_nil_of_le (by scalar_tac)]
      simp only [ConLeche.Name.nodup]
      simpa using hb.symm
    · rename_i hlt
      have hb2 : i.val < ns.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ns.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ns i hb2)
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw] at hb
      obtain ⟨c, hc, hb⟩ := hb
      subst hyv
      have hyWF : NameWF ns.val[i.val] := hns _ (List.getElem_mem hb2)
      have hcabs := Name.contains_from_refines hns hyWF ns.val.length w (by scalar_tac) c hc
      rw [hwv] at hcabs
      rw [absNames, ← List.map_drop, List.drop_eq_getElem_cons hb2]
      simp only [List.map_cons, ConLeche.Name.nodup]
      cases c with
      | true =>
        simp only [reduceIte, Result.ok.injEq] at hb
        rw [← hb]
        have hm : (absName ns.val[i.val]) ∈ (ns.val.drop (i.val + 1)).map absName :=
          of_decide_eq_true hcabs.symm
        simp only [Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true]
        intro _
        simpa [List.map_drop] using hm
      | false =>
        simp only [Bool.false_eq_true, reduceIte, bind_tc_ok] at hb
        have hih := ih w (by scalar_tac) b hb
        rw [hwv, absNames, ← List.map_drop] at hih
        have hm : ¬ (absName ns.val[i.val]) ∈ (ns.val.drop (i.val + 1)).map absName :=
          of_decide_eq_false hcabs.symm
        rw [hih]
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        simp [List.map_drop, hm]

/-- `ConLeche/Kernel/Level.lean:213-216` — `level::name_nodup` refines
`Name.nodup`. -/
theorem name_nodup_refines {ns : alloc.vec.Vec name.Name} {b : Bool}
    (hns : NamesWF ns) (h : level.name_nodup ns = ok b) :
    b = ConLeche.Name.nodup (absNames ns) := by
  rw [level.name_nodup] at h
  have hh := name_nodup_from_refines hns ns.val.length 0#usize (by scalar_tac) b h
  simpa using hh

end ConRon.Refine.CheckerBase
