import ConRon.Refine.TypeChecker
import ConRon.Refine.CoreKShapes
import ConRon.Refine.PropRead
import ConRon.Refine.BasisNames
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

/-! ## A missing `Expr` inversion

**To be moved to `Refine/Expr.lean`** beside the other `*_inv` lemmas, exactly
as `Refine/CoreKGuards.lean`'s three are: `openPisAtFvars` cases on a node's
kind, which throws the `ExprWF` derivation away. -/

/-- A well-formed `ForallE` node has well-formed parts. -/
theorem wf_forall_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty bo : expr.Expr} {m : expr.BinderMeta} (hk : e = .mk (.mk d (.ForallE ty bo m))) :
    ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty1 _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f1 a1 _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty1 bo1 m1 _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty1 bo1 m1 _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.ForallE.injEq] at hk
    obtain ⟨-, rfl, rfl, rfl⟩ := hk
    exact ⟨hty, hbo, hm⟩
  | @let_e ty1 v1 bo1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-! ## The state-free readers

`unwrapOr`, `Env.findCV?`/`FEnv.findCV?`, `piResultSort`, `isEqHead` and
`eqHeadLevel` touch neither the state nor the core, so each is a plain
equality (DESIGN.md §3.5's pure shape). -/

/-- `ConLeche/Kernel/CheckerBase.lean:211-217 unwrapOr` — the port's
`Result`-valued spelling: an `.Ok a` says the option *was* `some a`, which is
the clause con-leche's `pure a` reads.  (The port is generic in the payload,
so this is the statement at every abstraction at once: `unwrapOr (o.map f)`
is `pure (f a)` as soon as `o = some a`.)  Its call sites are
`DeclCheck.lean`'s iota-theorem mirrors, which the port does not have yet. -/
theorem unwrap_or_refines {T : Type} {o : Option T} {err : core_types.CheckError} {a : T}
    (h : checker_base.unwrap_or o err = ok (.Ok a)) : o = some a := by
  cases o with
  | none => simp [checker_base.unwrap_or] at h
  | some x => simp only [checker_base.unwrap_or, Result.ok.injEq,
      core.result.Result.Ok.injEq] at h; rw [h]

/-- `ConLeche/Kernel/CheckerBase.lean:219-225 Env.findCV?`,
`ConLeche/Kernel/DeclCheck.lean:33-35 FEnv.findCV?` — the stored constant as a
`ConstantVal`.  Stated against the indexed twin, which is what the port reads
(task #18's deviation 3). -/
theorem find_cv_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option env.ConstantVal} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (hn : NameWF n) (h : checker_base.find_cv fe n = ok o) :
    o.map absConstantVal = ConLeche.FEnv.findCV? lfe (absName n) ∧
      ∀ cv, o = some cv → ConstantValWF cv := by
  rw [checker_base.find_cv] at h
  obtain ⟨oi, hoi, h⟩ := bind_eq_ok_iff.mp h
  have hfind := FEnv.find_refines hrel hwf hn hoi
  cases oi with
  | none =>
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by simp⟩
    rw [ConLeche.FEnv.findCV?, ← hfind]; simp
  | some ci =>
    obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    have hciwf : ConstantInfoWF ci := FEnv.find_wf hwf hn hoi ci rfl
    obtain ⟨habs, hwfcv⟩ := PropRead.to_constant_val_refines hciwf hcv
    refine ⟨?_, ?_⟩
    · rw [ConLeche.FEnv.findCV?, ← hfind]
      simp only [Option.map_some, habs]
    · intro cv' hcv'; simp only [Option.some.injEq] at hcv'; rw [← hcv']; exact hwfcv

/-- `ConLeche/Kernel/CheckerBase.lean:227-232 piResultSort` — the result sort
of a syntactic pi telescope. -/
theorem pi_result_sort_refines {e : expr.Expr} {o : Option level.Level}
    (he : ExprWF e) (h : checker_base.pi_result_sort e = ok o) :
    o.map absLevel = ConLeche.piResultSort (absExpr e) ∧
      ∀ u, o = some u → LevelWF u := by
  rw [checker_base.pi_result_sort] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hrwf⟩ := ExprOps.pi_result_refines he hr
  obtain ⟨nd⟩ := r
  obtain ⟨d, k⟩ := nd
  rw [ConLeche.piResultSort, ← habs]
  cases k with
  | «Sort» u =>
    simp only [arc_deref_eq, ExprOps.node_kind, level_dup_eq, bind_tc_ok,
      Result.ok.injEq] at h
    subst h
    refine ⟨by simp, ?_⟩
    intro u' hu'
    simp only [Option.some.injEq] at hu'
    rw [← hu']
    exact CoreK.wf_sort_inv hrwf rfl
  | _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    subst h
    exact ⟨by simp, by simp⟩

/-- `ConLeche/Kernel/CheckerBase.lean:186-189 isEqHead` — the pinned equality
former at one level. -/
theorem is_eq_head_refines {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (h : checker_base.is_eq_head e = ok b) : b = ConLeche.isEqHead (absExpr e) := by
  obtain ⟨nd⟩ := e
  obtain ⟨d, k⟩ := nd
  rw [checker_base.is_eq_head] at h
  cases k with
  | Const c us =>
    obtain ⟨hcwf, huswf⟩ := CoreK.wf_const_inv he rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    rw [absExpr_mk, absExprKind, absLevels]
    split at h
    · rename_i hlen
      have hl1 : us.val.length = 1 := by scalar_tac
      obtain ⟨m, hm, hb⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hmabs, hmwf⟩ := BasisNames.eq_name_refines hm
      rcases hv : us.val with _ | ⟨u0, us'⟩
      · rw [hv] at hl1; simp at hl1
      · cases us' with
        | cons v vs => rw [hv] at hl1; simp at hl1
        | nil =>
          rw [Name.beq_refines hcwf hmwf hb, hmabs]
          simp [ConLeche.isEqHead]
    · rename_i hlen
      have hl1 : us.val.length ≠ 1 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      rcases hv : us.val with _ | ⟨u0, us'⟩
      · simp [ConLeche.isEqHead]
      · cases us' with
        | nil => rw [hv] at hl1; simp at hl1
        | cons v vs => simp [ConLeche.isEqHead]
  | _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.isEqHead]

/-- `ConLeche/Kernel/CheckerBase.lean:191-198 eqHeadLevel` — the level an
equality head carries; off shape it is `.zero`. -/
theorem eq_head_level_refines {e : expr.Expr} {u : level.Level} (he : ExprWF e)
    (h : checker_base.eq_head_level e = ok u) :
    absLevel u = ConLeche.eqHeadLevel (absExpr e) ∧ LevelWF u := by
  obtain ⟨nd⟩ := e
  obtain ⟨d, k⟩ := nd
  rw [checker_base.eq_head_level] at h
  cases k with
  | Const c us =>
    obtain ⟨hcwf, huswf⟩ := CoreK.wf_const_inv he rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    rw [absExpr_mk, absExprKind, absLevels]
    split at h
    · rename_i hlen
      have hl1 : us.val.length = 1 := by scalar_tac
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec us 0#usize (by scalar_tac))
      simp only [alloc.vec.Vec.index_slice_index, hy, level_dup_eq, bind_tc_ok,
        Result.ok.injEq] at h
      subst h
      have hywf : LevelWF y := by
        rw [hyv]; exact huswf _ (List.getElem_mem (by scalar_tac))
      obtain ⟨u0, hv⟩ : ∃ u0, us.val = [u0] := by
        rcases hh : us.val with _ | ⟨x, t⟩
        · rw [hh] at hl1; simp at hl1
        · cases t with
          | nil => exact ⟨x, rfl⟩
          | cons z zs => rw [hh] at hl1; simp at hl1
      have hy0 : y = u0 := by
        have h1 : us.val[0]? = some y := by
          rw [hyv, List.getElem?_eq_getElem (by scalar_tac)]; simp
        rw [hv] at h1; simpa using h1.symm
      subst hy0
      rw [hv]
      exact ⟨by simp [ConLeche.eqHeadLevel], hywf⟩
    · rename_i hlen
      have hl1 : us.val.length ≠ 1 := by scalar_tac
      refine ⟨?_, Level.zero_wf h⟩
      rw [Level.zero_refines h]
      rcases hv : us.val with _ | ⟨u0, us'⟩
      · simp [ConLeche.eqHeadLevel]
      · cases us' with
        | nil => rw [hv] at hl1; simp at hl1
        | cons v vs => simp [ConLeche.eqHeadLevel]
  | _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    exact ⟨by rw [Level.zero_refines h]; simp [ConLeche.eqHeadLevel], Level.zero_wf h⟩

end ConRon.Refine.CheckerBase
