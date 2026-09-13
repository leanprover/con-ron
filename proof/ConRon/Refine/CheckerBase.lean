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

/-- `expr::dup` is the identity in the model (DESIGN.md §3.2); `Refine/State.lean`
has the same lemma `@[local simp]`. -/
@[local simp] theorem expr_dup_eq (e : expr.Expr) : expr.dup e = ok e := by
  obtain ⟨r⟩ := e; simp [expr.dup]

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

/-- con-leche compares names with `==`; `Refine/Name.lean` states `name::beq`
with `decide`.  The two agree (`Name`'s `BEq` is lawful). -/
theorem decide_eq_beq_name (a b : ConLeche.Name) : decide (a = b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

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
          simp [ConLeche.isEqHead, decide_eq_beq_name]
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

/-! ## `domsMatchAux` at the identity view, and its `Array` twin

Task #24's deviation 1: the cited `g : Nat → Expr → Expr` is a closure §3.4
forbids, so the port replaces it with a `DomView` dictionary and passes
`DomIdent` — `fun _ e => e` — at every call site in this scope.  The cited
`Array` twin `domsMatchAuxA` (`CheckerBase.lean:120-129`) is the *same* Rust
function, and `domsMatchAuxA_eq` is the equation between them; both readings
are stated below. -/

/-- con-leche compares terms with `==`; `Refine/Expr.lean` states `expr::beq`
with `decide`.  The two agree. -/
theorem decide_eq_beq_expr (a b : ConLeche.Expr) : decide (a = b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

/-- The cited `(List.range n).all` body, at the identity view. -/
def domsStep (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta)) (o₁ o₂ i : Nat) : Bool :=
  match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
  | some b₁, some b₂ => b₁.1 == b₂.1
  | _, _ => false

/-- `domsMatchAux` at the identity view *is* `domsStep`'s `List.range` fold. -/
theorem domsMatchAux_ident (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta))
    (o₁ o₂ n : Nat) :
    ConLeche.domsMatchAux (fun _ e => e) bs₁ bs₂ o₁ o₂ n
      = (List.range n).all (domsStep bs₁ bs₂ o₁ o₂) := rfl

/-- `domsMatchAuxA` at the identity view is the same fold over the arrays. -/
theorem domsMatchAuxA_ident (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta))
    (o₁ o₂ n : Nat) :
    ConLeche.domsMatchAuxA (fun _ e => e) bs₁.toArray bs₂.toArray o₁ o₂ n
      = (List.range n).all (domsStep bs₁ bs₂ o₁ o₂) := by
  rw [ConLeche.domsMatchAuxA]
  simp only [List.getElem?_toArray]
  rfl

/-- `DomIdent`'s one method is the cited `fun _ e => e` (`expr::dup` is the
identity in the model, DESIGN.md §3.2). -/
theorem dom_ident_view_refines {i : Std.U64} {e r : expr.Expr}
    (h : checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view () i e = ok r) :
    r = e := by
  rw [checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view] at h
  exact Expr.dup_eq h

/-- Indexing a binder vector: the abstracted list agrees at the same index. -/
theorem vec_index_binder {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {i : Std.Usize} {p : expr.Expr × expr.BinderMeta} (hbs : ExprOps.BindersWF bs)
    (h : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (expr.Expr × expr.BinderMeta)) bs i = ok p) :
    ExprWF p.1 ∧ (ExprOps.absBinders bs)[i.val]?
      = some (absExpr p.1, absBinderMeta p.2) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < bs.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : bs.val[i.val] = p := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨(hbs p (by rw [← hx]; exact List.getElem_mem hlt)).1, ?_⟩
  rw [ExprOps.absBinders, List.getElem?_map, hg]
  rfl

/-- `ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux` — the index
recursion behind `doms_match_aux`, at the positions from `i` on. -/
theorem doms_match_aux_from_refines
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2) :
    ∀ (N : Nat) (o1 o2 n i : Std.U64), n.val - i.val ≤ N → ∀ b : Bool,
      checker_base.doms_match_aux_from
        checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView () bs1 bs2 o1 o2 n i
        = ok b →
      b = (List.range' i.val (n.val - i.val)).all
            (domsStep (ExprOps.absBinders bs1) (ExprOps.absBinders bs2) o1.val o2.val) := by
  have hlen1 : (ExprOps.absBinders bs1).length = bs1.val.length := by simp [ExprOps.absBinders]
  have hlen2 : (ExprOps.absBinders bs2).length = bs2.val.length := by simp [ExprOps.absBinders]
  intro N
  induction N with
  | zero =>
    intro o1 o2 n i hN b h
    rw [checker_base.doms_match_aux_from.eq_def] at h
    simp only [] at h
    rw [if_pos (by scalar_tac)] at h
    rw [show n.val - i.val = 0 by omega]
    simpa using h.symm
  | succ N ih =>
    intro o1 o2 n i hN b h
    rw [checker_base.doms_match_aux_from.eq_def] at h
    simp only [] at h
    split at h
    · rw [show n.val - i.val = 0 by scalar_tac]
      simpa using h.symm
    · rename_i hlt
      have hltv : i.val < n.val := by scalar_tac
      simp only [lift_eq, bind_tc_ok] at h
      obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
      have hj1v : j1.val = o1.val + i.val := HashMap.uscalar_add_eq hj1
      have hj2v : j2.val = o2.val + i.val := HashMap.uscalar_add_eq hj2
      have hc1 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs1) : Std.U64).val
          = bs1.val.length := by rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      have hc2 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs2) : Std.U64).val
          = bs2.val.length := by rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      rw [show n.val - i.val = (n.val - i.val - 1) + 1 by omega, List.range'_succ,
        List.all_cons]
      split at h
      · rename_i hge
        have hnone : (ExprOps.absBinders bs1)[o1.val + i.val]? = none :=
          List.getElem?_eq_none (by rw [hlen1]; scalar_tac)
        simp only [domsStep, hnone]
        simpa using h.symm
      · rename_i hlt1
        split at h
        · rename_i hge
          have hnone : (ExprOps.absBinders bs2)[o2.val + i.val]? = none :=
            List.getElem?_eq_none (by rw [hlen2]; scalar_tac)
          simp only [domsStep, hnone]
          rcases hs : (ExprOps.absBinders bs1)[o1.val + i.val]? with _ | q <;>
            simpa using h.symm
        · rename_i hlt2
          obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e2, m2⟩ := p2
          obtain ⟨viewed, hview, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e1, m1⟩ := p1
          obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
          have hi5 : ((Std.UScalar.cast .Usize j2 : Std.Usize)).val = j2.val :=
            ExprOps.u64_cast_usize_val_of_lt (n := bs2.val.length)
              (by have := bs2.slice.property; scalar_tac) (by scalar_tac)
          have hi6 : ((Std.UScalar.cast .Usize j1 : Std.Usize)).val = j1.val :=
            ExprOps.u64_cast_usize_val_of_lt (n := bs1.val.length)
              (by have := bs1.slice.property; scalar_tac) (by scalar_tac)
          obtain ⟨hw2, hg2⟩ := vec_index_binder hb2 hp2
          obtain ⟨hw1, hg1⟩ := vec_index_binder hb1 hp1
          rw [hi5, hj2v] at hg2
          rw [hi6, hj1v] at hg1
          rw [dom_ident_view_refines hview] at hc
          have hcv := Expr.beq_refines hw1 hw2 hc
          simp only [domsStep, hg1, hg2, ← decide_eq_beq_expr, ← hcv]
          cases c with
          | false =>
            simp only [Bool.false_eq_true, if_false] at h
            simpa using h.symm
          | true =>
            simp only [reduceIte] at h
            obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
            have hi7v : i7.val = i.val + 1 := HashMap.uscalar_add_eq hi7
            have hih := ih o1 o2 n i7 (by omega) b h
            rw [hi7v, show n.val - (i.val + 1) = n.val - i.val - 1 by omega] at hih
            simpa using hih

/-- `ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux` — the wrapper, at
the identity view. -/
theorem doms_match_aux_refines
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {o1 o2 n : Std.U64} {b : Bool}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2)
    (h : checker_base.doms_match_aux
      checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView () bs1 bs2 o1 o2 n
      = ok b) :
    b = ConLeche.domsMatchAux (fun _ e => e)
      (ExprOps.absBinders bs1) (ExprOps.absBinders bs2) o1.val o2.val n.val := by
  rw [checker_base.doms_match_aux] at h
  have hh := doms_match_aux_from_refines hb1 hb2 n.val o1 o2 n 0#u64 (by scalar_tac) b h
  rw [domsMatchAux_ident, List.range_eq_range']
  simpa using hh

/-- `ConLeche/Kernel/CheckerBase.lean:120-129 domsMatchAuxA` — the `Array`
twin is the same Rust function (task #24's `F`/`Array` collapse); this is the
reading `checkProjRuleF` consumes. -/
theorem doms_match_aux_refines_array
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {o1 o2 n : Std.U64} {b : Bool}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2)
    (h : checker_base.doms_match_aux
      checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView () bs1 bs2 o1 o2 n
      = ok b) :
    b = ConLeche.domsMatchAuxA (fun _ e => e)
      (ExprOps.absBinders bs1).toArray (ExprOps.absBinders bs2).toArray
      o1.val o2.val n.val := by
  rw [domsMatchAuxA_ident, ← domsMatchAux_ident]
  exact doms_match_aux_refines hb1 hb2 h

/-! ## `fvs.map Expr.fvarTypeD`

con-leche writes the map inline in `checkProjRule`/`checkIotaThm`; §3.4 forbids
the closure, so the port has `fvar_types`. -/

/-- `checker_base::fvar_types_from` — the accumulating index recursion. -/
theorem fvar_types_from_refines {fvs : alloc.vec.Vec expr.Expr} (hfvs : ExprsWF fvs) :
    ∀ (N : Nat) (i : Std.Usize) (out r : alloc.vec.Vec expr.Expr),
      fvs.val.length - i.val ≤ N → ExprsWF out →
      checker_base.fvar_types_from fvs i out = ok r →
      absExprs r = absExprs out ++ ((absExprs fvs).drop i.val).map ConLeche.Expr.fvarTypeD
        ∧ ExprsWF r := by
  intro N
  induction N with
  | zero =>
    intro i out r hN hout h
    rw [checker_base.fvar_types_from.eq_def] at h
    simp only [] at h
    rw [if_pos (by scalar_tac)] at h
    rw [← Result.ok_injective h]
    refine ⟨?_, hout⟩
    rw [show (absExprs fvs).drop i.val = [] from
      List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
    simp
  | succ N ih =>
    intro i out r hN hout h
    rw [checker_base.fvar_types_from.eq_def] at h
    simp only [] at h
    split at h
    · rw [← Result.ok_injective h]
      refine ⟨?_, hout⟩
      rw [show (absExprs fvs).drop i.val = [] from
        List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
      simp
    · rename_i hlt
      obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hlti, hxwf, hdrop⟩ := ExprOps.vec_index_expr hfvs hx
      obtain ⟨htabs, htwf⟩ := ExprOps.fvar_type_d_refines hxwf ht
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1v : absExprs out1 = absExprs out ++ [absExpr t] := by
        rw [absExprs, absExprs, vec_push_val hout1]; simp
      have hout1wf : ExprsWF out1 := by
        intro y hy
        rw [vec_push_val hout1] at hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact hout y h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact htwf
      obtain ⟨habs, hwf⟩ := ih i2 out1 r (by omega) hout1wf h
      refine ⟨?_, hwf⟩
      rw [habs, hout1v, hi2v, hdrop]
      simp [htabs]

/-- `checker_base::fvar_types` — `fvs.map Expr.fvarTypeD`. -/
theorem fvar_types_refines {fvs r : alloc.vec.Vec expr.Expr} (hfvs : ExprsWF fvs)
    (h : checker_base.fvar_types fvs = ok r) :
    absExprs r = (absExprs fvs).map ConLeche.Expr.fvarTypeD ∧ ExprsWF r := by
  rw [checker_base.fvar_types] at h
  obtain ⟨habs, hwf⟩ := fvar_types_from_refines hfvs fvs.val.length 0#usize _ r
    (by scalar_tac) ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [absExprs, alloc.vec.Vec.new]

/-! ## `openPisAtFvars` and its one-pass twin

Task #24's deviation 6: `fv :: fvs` is `expr_ops::cons_expr`, a fresh vector
filled front to back (`O(width)` where Lean's cons is `O(1)`), and the `acc`
of the one-pass walk is copied on the way down for the same reason. -/

/-- `ConLeche/Kernel/CheckerBase.lean:108-118 openPisAtFvars` — open the first
`n` `∀`-binders at fresh free variables. -/
theorem open_pis_at_fvars_refines :
    ∀ (N : Nat) (n : Std.U64) (e : expr.Expr) (i : Std.U64)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      n.val = N → ExprWF e →
      checker_base.open_pis_at_fvars n e i = ok r →
      (Option.map (fun p => (absExprs p.1, absExpr p.2)) r
        = ConLeche.openPisAtFvars n.val (absExpr e) i.val)
      ∧ (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  intro N
  induction N with
  | zero =>
    intro n e i r hN he h
    rw [checker_base.open_pis_at_fvars.eq_def] at h
    rw [if_pos (by scalar_tac)] at h
    simp only [expr_dup_eq, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, hN]
    refine ⟨by simp [ConLeche.openPisAtFvars, absExprs, alloc.vec.Vec.new], ?_⟩
    intro p hp
    simp only [Option.some.injEq] at hp
    rw [← hp]
    exact ⟨ExprOps.exprsWF_new, he⟩
  | succ N ih =>
    intro n e i r hN he h
    rw [checker_base.open_pis_at_fvars.eq_def] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨nd⟩ := e
    obtain ⟨d, k⟩ := nd
    rw [hN, absExpr_mk]
    cases k with
    | ForallE dom body m =>
      obtain ⟨hdom, hbody, hm⟩ := wf_forall_inv he rfl
      simp only [arc_deref_eq, ExprOps.node_kind, expr_dup_eq, bind_tc_ok] at h
      obtain ⟨fv, hfv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨opened, hopened, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hfvwf : ExprWF fv := Expr.fvar_wf hdom hfv
      have hfvabs : absExpr fv = .fvar i.val (absExpr dom) := Expr.fvar_refines hfv
      obtain ⟨hoabs, howf⟩ := ExprOps.instantiate1_refines hbody hfvwf hopened
      have hn1v : n1.val = n.val - 1 := HashMap.uscalar_sub_eq hn1
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih n1 opened i2 o (by omega) howf ho
      rw [hn1v, hi2v, hoabs, show ((0#u64 : Std.U64)).val = 0 from rfl,
        show n.val - 1 = N by omega] at habs
      simp only [absExprKind, ConLeche.openPisAtFvars, ← hfvabs, ← habs]
      cases o with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ⟨by simp, by simp⟩
      | some q =>
        obtain ⟨fvs, b⟩ := q
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq] at h
        obtain ⟨hfvswf, hbwf⟩ := hwf (fvs, b) rfl
        obtain ⟨hvabs, hvwf⟩ := ExprOps.cons_expr_refines hfvwf hfvswf hv
        rw [← h]
        refine ⟨by simp [hvabs], ?_⟩
        intro p hp
        simp only [Option.some.injEq] at hp
        rw [← hp]
        exact ⟨hvwf, hbwf⟩
    | _ =>
      simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [absExprKind, ConLeche.openPisAtFvars], by simp⟩

/-- `ConLeche/Kernel/CheckerBase.lean:131-145 openPisAtFvarsFGo` — the one-pass
core: one `instantiateList` per domain instead of one whole-telescope
`instantiate1` per binder.  `acc` holds the already-created fvars, innermost
binder first. -/
theorem open_pis_at_fvars_f_go_refines :
    ∀ (N : Nat) (acc : alloc.vec.Vec expr.Expr) (n : Std.U64) (e : expr.Expr) (i : Std.U64)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      n.val = N → ExprsWF acc → ExprWF e →
      checker_base.open_pis_at_fvars_f_go acc n e i = ok r →
      (Option.map (fun p => (absExprs p.1, absExpr p.2)) r
        = ConLeche.openPisAtFvarsFGo (absExprs acc) n.val (absExpr e) i.val)
      ∧ (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  intro N
  induction N with
  | zero =>
    intro acc n e i r hN hacc he h
    rw [checker_base.open_pis_at_fvars_f_go.eq_def] at h
    rw [if_pos (by scalar_tac)] at h
    obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habs1, hwf1⟩ := ExprOps.instantiate_list_fast_refines he hacc he1
    simp only [Result.ok.injEq] at h
    rw [← h, hN]
    refine ⟨?_, ?_⟩
    · simp only [ConLeche.openPisAtFvarsFGo, Option.map_some, habs1,
        show ((0#u64 : Std.U64)).val = 0 from rfl]
      simp [absExprs, alloc.vec.Vec.new]
    · intro p hp
      simp only [Option.some.injEq] at hp
      rw [← hp]
      exact ⟨ExprOps.exprsWF_new, hwf1⟩
  | succ N ih =>
    intro acc n e i r hN hacc he h
    rw [checker_base.open_pis_at_fvars_f_go.eq_def] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨nd⟩ := e
    obtain ⟨d, k⟩ := nd
    rw [hN, absExpr_mk]
    cases k with
    | ForallE dom body m =>
      obtain ⟨hdom, hbody, hm⟩ := wf_forall_inv he rfl
      simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨fv, hfv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨acc2, hacc2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habs1, hwf1⟩ := ExprOps.instantiate_list_fast_refines hdom hacc he1
      have hfvwf : ExprWF fv := Expr.fvar_wf hwf1 hfv
      have hfvabs : absExpr fv = .fvar i.val (absExpr e1) := Expr.fvar_refines hfv
      obtain ⟨hacc2abs, hacc2wf⟩ := ExprOps.cons_expr_refines hfvwf hacc hacc2
      have hn1v : n1.val = n.val - 1 := HashMap.uscalar_sub_eq hn1
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih acc2 n1 body i2 o (by omega) hacc2wf hbody ho
      rw [hn1v, hi2v, hacc2abs, show n.val - 1 = N by omega] at habs
      rw [habs1, show ((0#u64 : Std.U64)).val = 0 from rfl] at hfvabs
      simp only [absExprKind, ConLeche.openPisAtFvarsFGo, ← hfvabs, ← habs]
      cases o with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ⟨by simp, by simp⟩
      | some q =>
        obtain ⟨fvs, b⟩ := q
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq] at h
        obtain ⟨hfvswf, hbwf⟩ := hwf (fvs, b) rfl
        obtain ⟨hvabs, hvwf⟩ := ExprOps.cons_expr_refines hfvwf hfvswf hv
        rw [← h]
        refine ⟨by simp [hvabs], ?_⟩
        intro p hp
        simp only [Option.some.injEq] at hp
        rw [← hp]
        exact ⟨hvwf, hbwf⟩
    | _ =>
      simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [absExprKind, ConLeche.openPisAtFvarsFGo], by simp⟩

/-- `ConLeche/Kernel/CheckerBase.lean:147-154 openPisAtFvarsF` — **the executed
one**: the one-pass walk with the cited fallback. -/
theorem open_pis_at_fvars_f_refines {n : Std.U64} {e : expr.Expr} {i : Std.U64}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)} (he : ExprWF e)
    (h : checker_base.open_pis_at_fvars_f n e i = ok r) :
    (Option.map (fun p => (absExprs p.1, absExpr p.2)) r
      = ConLeche.openPisAtFvarsF n.val (absExpr e) i.val)
    ∧ (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  rw [checker_base.open_pis_at_fvars_f] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    open_pis_at_fvars_f_go_refines n.val _ n e i o rfl ExprOps.exprsWF_new he ho
  rw [ConLeche.openPisAtFvarsF]
  rw [show absExprs (alloc.vec.Vec.new expr.Expr) = [] from rfl] at hoabs
  rw [← hoabs]
  cases o with
  | none =>
    simp only [Option.map_none]
    exact open_pis_at_fvars_refines n.val n e i r rfl he h
  | some q =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ⟨by simp, howf⟩

/-! ## `checkProjShape` — stage 2b, and state-free

The cited definition is monad-polymorphic but touches neither the state nor
the core, so it is run here at `ConLeche.Cached.CheckCM` — the monad the
executed checker uses — and leaves the state where it found it. -/

/-- `ConLeche/Kernel/CheckerBase.lean:235-250 checkProjShape` — the projection
type's parameter telescope is syntactically the constructor's, and the
constructor's residual is the family applied to exactly the parameters. -/
theorem check_proj_shape_refines {pty ctor_ty : expr.Expr} {n_p n_f : Std.U64}
    (hp : ExprWF pty) (hc : ExprWF ctor_ty)
    (h : checker_base.check_proj_shape pty ctor_ty n_p n_f = ok (.Ok ())) :
    ∀ lst : ConLeche.Cached.CState,
      (ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM)
        (absExpr pty) (absExpr ctor_ty) n_p.val n_f.val).run lst = .ok ((), lst) := by
  intro lst
  rw [checker_base.check_proj_shape] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs1, -⟩ := ExprOps.strip_pis_refines hp ho
  cases o with
  | none => simp at h
  | some q1 =>
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habs2, hwf2⟩ := ExprOps.strip_pis_refines hc ho1
    rw [hi1v] at habs2
    cases o1 with
    | none => simp at h
    | some q2 =>
      obtain ⟨cbinders, cbody⟩ := q2
      obtain ⟨-, hcbodywf⟩ := hwf2 (cbinders, cbody) rfl
      obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines hcbodywf hargs
      simp only [lift_eq, bind_tc_ok] at h
      split at h
      · simp at h
      · rename_i hne
        have hlen : args.val.length = n_p.val := by
          have hcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len args) : Std.U64).val
              = args.val.length := by
            rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
          rw [← hcast, hne]
        obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines hcbodywf hf
        obtain ⟨nd⟩ := f
        obtain ⟨df, kf⟩ := nd
        rw [ConLeche.checkProjShape]
        simp only [← habs1, ← habs2, Option.map_some]
        cases kf with
        | Const cn cus =>
          rw [absExpr_mk, absExprKind] at hfabs
          simp only [← hargsabs, ← hfabs]
          have : (absExprs args).length = n_p.val := by
            simp only [absExprs, List.length_map]; exact hlen
          simp [this]
          rfl
        | _ =>
          simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
          simp at h

/-! ## The three list walks

Task #24's deviation 5: the cited two-`List` recursions became one index
recursion with three arms (both exhausted, both in range, or the arity throw),
so each is refined against the cited recursion run on the two `drop i`
suffixes.  The `ops` record is `sharedOpsC` (`Refine/TypeChecker.lean`'s
`lops`), and the `Env` argument every slot ignores is `lfe.env` — which is
exactly why the port can pass the index alone (task #24's note 3).

Each walk needs one *run* lemma per arm of the cited definition, in the
`Refine/StateC.lean` style: the state monad's `do` is unfolded once, against a
known first step. -/

open ConLeche.Cached in
/-- `checkDefEqList` on two exhausted lists. -/
theorem checkDefEqList_nil {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {lst : CState} :
    (ConLeche.checkDefEqList ops lenv d [] []).run lst = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkDefEqList`'s step, at a comparison that succeeded. -/
theorem checkDefEqList_cons {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {a b : ConLeche.Expr} {xs ys : List ConLeche.Expr} {lst lst' : CState}
    (hstep : (ops.isDefEq lenv d a b).run lst = .ok (true, lst')) :
    (ConLeche.checkDefEqList ops lenv d (a :: xs) (b :: ys)).run lst
      = (ConLeche.checkDefEqList ops lenv d xs ys).run lst' := by
  rw [ConLeche.checkDefEqList]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ops.isDefEq lenv d a b) lst = Except.ok (true, lst') from hstep]
  rfl

open ConLeche.Cached in
/-- `checkTypedList` on two exhausted lists. -/
theorem checkTypedList_nil {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {lst : CState} :
    (ConLeche.checkTypedList ops lenv d [] []).run lst = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkTypedList`'s step, at an inference and a comparison that succeeded. -/
theorem checkTypedList_cons {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {a t ty : ConLeche.Expr} {xs ts : List ConLeche.Expr}
    {lst lst1 lst2 : CState}
    (hinf : (ops.inferType lenv d a).run lst = .ok (ty, lst1))
    (hdef : (ops.isDefEq lenv d ty t).run lst1 = .ok (true, lst2)) :
    (ConLeche.checkTypedList ops lenv d (a :: xs) (t :: ts)).run lst
      = (ConLeche.checkTypedList ops lenv d xs ts).run lst2 := by
  rw [ConLeche.checkTypedList]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ops.inferType lenv d a) lst = Except.ok (ty, lst1) from hinf]
  simp only [Except.bind]
  rw [show (ops.isDefEq lenv d ty t) lst1 = Except.ok (true, lst2) from hdef]
  rfl

open ConLeche.Cached in
/-- `checkAnnotList` on an exhausted list. -/
theorem checkAnnotList_nil {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {lst : CState} :
    (ConLeche.checkAnnotList ops lenv d []).run lst = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkAnnotList`'s step, at an annotation that reproduced its input. -/
theorem checkAnnotList_cons {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {a aA : ConLeche.Expr} {xs : List ConLeche.Expr} {lst lst1 : CState}
    (hann : (ops.annotate lenv d a).run lst = .ok (aA, lst1)) (heq : (aA == a) = true) :
    (ConLeche.checkAnnotList ops lenv d (a :: xs)).run lst
      = (ConLeche.checkAnnotList ops lenv d xs).run lst1 := by
  rw [ConLeche.checkAnnotList]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ops.annotate lenv d a) lst = Except.ok (aA, lst1) from hann]
  simp only [Except.bind, heq]
  rfl

/-- A `drop` past the end is the empty list, on the abstracted side. -/
theorem absExprs_drop_nil {xs : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    (h : xs.val.length ≤ i.val) : (absExprs xs).drop i.val = [] :=
  List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; omega)

/-- `ConLeche/Kernel/CheckerBase.lean:200-209 checkDefEqList` — the index
recursion, on the two suffixes at the cursor. -/
theorem check_def_eq_list_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {xs ys : alloc.vec.Vec expr.Expr} (hxs : ExprsWF xs) (hys : ExprsWF ys) :
    ∀ (N : Nat) (i : Std.Usize) (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (depth : Std.U64),
      xs.val.length - i.val ≤ N → StateWF st → FEnvWF fe →
      checker_base.check_def_eq_list_from mode st fe depth xs ys i = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkDefEqList (TypeChecker.lops mode lfe) lfe.env depth.val
            ((absExprs xs).drop i.val) ((absExprs ys).drop i.val)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_def_eq_list_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
    split at h
    · rename_i hy
      simp only [Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
      exact checkDefEqList_nil
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      simp [bind_eq_ok_iff] at h
  | succ N ih =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_def_eq_list_from.eq_def] at h
    simp only [] at h
    by_cases hix : i.val ≥ xs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · rename_i hy
        simp only [Result.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨lst, ?_, hsr, hsw⟩
        rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
        exact checkDefEqList_nil
      · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
        simp [bind_eq_ok_iff] at h
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac),
        if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hy
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨rr, st1⟩ := q
        obtain ⟨hltx, hewf, hdropx⟩ := ExprOps.vec_index_expr hxs he
        obtain ⟨hlty, he1wf, hdropy⟩ := ExprOps.vec_index_expr hys he1
        cases rr with
        | Err er => simp at h
        | Ok ok1 =>
          cases ok1 with
          | false => simp [bind_eq_ok_iff] at h
          | true =>
            simp only [reduceIte] at h
            obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
            have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
            obtain ⟨lst1, hrun, hsr1, hsw1⟩ :=
              TypeChecker.is_def_eq_core_refines hfuel hk st fe depth e e1 true st1
                hsw hfw hewf he1wf hq lst lfe hsr hfr
            have hstep : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
                (absExpr e) (absExpr e1)).run lst = .ok (true, lst1) := by
              rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun
            obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
              ih i4 st1 st' fe depth (by omega) hsw1 hfw h lst1 lfe hsr1 hfr
            refine ⟨lst2, ?_, hsr2, hsw2⟩
            rw [hdropx, hdropy, checkDefEqList_cons hstep, ← hi4v]
            exact hrun2

/-- `ConLeche/Kernel/CheckerBase.lean:200-209 checkDefEqList` — the pairwise
definitional-equality check of two spines. -/
theorem check_def_eq_list_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {xs ys : alloc.vec.Vec expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hxs : ExprsWF xs) (hys : ExprsWF ys)
    (h : checker_base.check_def_eq_list mode st fe depth xs ys = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDefEqList (TypeChecker.lops mode lfe) lfe.env depth.val
          (absExprs xs) (absExprs ys)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_base.check_def_eq_list] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_def_eq_list_from_refines hfuel hk hxs hys xs.val.length 0#usize st st' fe depth
      (by scalar_tac) hsw hfw h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

/-- `ConLeche/Kernel/CheckerBase.lean:156-168 checkTypedList` — the index
recursion, on the two suffixes at the cursor. -/
theorem check_typed_list_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {xs ts : alloc.vec.Vec expr.Expr} (hxs : ExprsWF xs) (hts : ExprsWF ts) :
    ∀ (N : Nat) (i : Std.Usize) (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (depth : Std.U64),
      xs.val.length - i.val ≤ N → StateWF st → FEnvWF fe →
      checker_base.check_typed_list_from mode st fe depth xs ts i = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkTypedList (TypeChecker.lops mode lfe) lfe.env depth.val
            ((absExprs xs).drop i.val) ((absExprs ts).drop i.val)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_typed_list_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
    split at h
    · rename_i hy
      simp only [Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
      exact checkTypedList_nil
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      simp [bind_eq_ok_iff] at h
  | succ N ih =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_typed_list_from.eq_def] at h
    simp only [] at h
    by_cases hix : i.val ≥ xs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · rename_i hy
        simp only [Result.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨lst, ?_, hsr, hsw⟩
        rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
        exact checkTypedList_nil
      · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
        simp [bind_eq_ok_iff] at h
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac),
        if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hy
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨rr, st1⟩ := q
        obtain ⟨hltx, hewf, hdropx⟩ := ExprOps.vec_index_expr hxs he
        cases rr with
        | Err er => simp at h
        | Ok ty =>
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨rr2, st2⟩ := q2
          obtain ⟨hltt, he1wf, hdropt⟩ := ExprOps.vec_index_expr hts he1
          obtain ⟨lst1, hrun, hsr1, hsw1, htywf⟩ :=
            TypeChecker.infer_type_core_refines hfuel hk st fe depth e ty st1
              hsw hfw hewf hq lst lfe hsr hfr
          cases rr2 with
          | Err er => simp at h
          | Ok ok1 =>
            cases ok1 with
            | false => simp [bind_eq_ok_iff] at h
            | true =>
              simp only [reduceIte] at h
              obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
              have hi5v : i5.val = i.val + 1 := HashMap.uscalar_add_eq hi5
              obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
                TypeChecker.is_def_eq_core_refines hfuel hk st1 fe depth ty e1 true st2
                  hsw1 hfw htywf he1wf hq2 lst1 lfe hsr1 hfr
              have hinf : ((TypeChecker.lops mode lfe).inferType lfe.env depth.val
                  (absExpr e)).run lst = .ok (absExpr ty, lst1) := by
                rw [TypeChecker.sharedOpsC_inferType]; exact hrun
              have hdef : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
                  (absExpr ty) (absExpr e1)).run lst1 = .ok (true, lst2) := by
                rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun2
              obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
                ih i5 st2 st' fe depth (by omega) hsw2 hfw h lst2 lfe hsr2 hfr
              refine ⟨lst3, ?_, hsr3, hsw3⟩
              rw [hdropx, hdropt, checkTypedList_cons hinf hdef, ← hi5v]
              exact hrun3

/-- `ConLeche/Kernel/CheckerBase.lean:156-168 checkTypedList` — each
expression's inferred type against the corresponding expected type. -/
theorem check_typed_list_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {xs ts : alloc.vec.Vec expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hxs : ExprsWF xs) (hts : ExprsWF ts)
    (h : checker_base.check_typed_list mode st fe depth xs ts = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkTypedList (TypeChecker.lops mode lfe) lfe.env depth.val
          (absExprs xs) (absExprs ts)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_base.check_typed_list] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_typed_list_from_refines hfuel hk hxs hts xs.val.length 0#usize st st' fe depth
      (by scalar_tac) hsw hfw h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

/-- `ConLeche/Kernel/CheckerBase.lean:170-184 checkAnnotList` — the index
recursion, on the suffix at the cursor. -/
theorem check_annot_list_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {xs : alloc.vec.Vec expr.Expr} (hxs : ExprsWF xs) :
    ∀ (N : Nat) (i : Std.Usize) (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (depth : Std.U64),
      xs.val.length - i.val ≤ N → StateWF st → FEnvWF fe →
      checker_base.check_annot_list_from mode st fe depth xs i = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkAnnotList (TypeChecker.lops mode lfe) lfe.env depth.val
            ((absExprs xs).drop i.val)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_annot_list_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨lst, ?_, hsr, hsw⟩
    rw [absExprs_drop_nil (by scalar_tac)]
    exact checkAnnotList_nil
  | succ N ih =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_annot_list_from.eq_def] at h
    simp only [] at h
    split at h
    · simp only [Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [absExprs_drop_nil (by scalar_tac)]
      exact checkAnnotList_nil
    · rename_i hlt
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨rr, st1⟩ := q
      obtain ⟨hltx, hewf, hdropx⟩ := ExprOps.vec_index_expr hxs he
      cases rr with
      | Err er => simp at h
      | Ok aA =>
        obtain ⟨lst1, hrun, hsr1, hsw1, hawf⟩ :=
          TypeChecker.annotate_core_refines hfuel hk st fe depth e aA st1
            hsw hfw hewf hq lst lfe hsr hfr
        obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
        have hcv := Expr.beq_refines hawf hewf hc
        cases c with
        | false => simp [bind_eq_ok_iff] at h
        | true =>
          simp only [reduceIte] at h
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          have hann : ((TypeChecker.lops mode lfe).annotate lfe.env depth.val
              (absExpr e)).run lst = .ok (absExpr aA, lst1) := by
            rw [TypeChecker.sharedOpsC_annotate]; exact hrun
          have heq : (absExpr aA == absExpr e) = true := by
            rw [← decide_eq_beq_expr, ← hcv]
          obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
            ih i2 st1 st' fe depth (by omega) hsw1 hfw h lst1 lfe hsr1 hfr
          refine ⟨lst2, ?_, hsr2, hsw2⟩
          rw [hdropx, checkAnnotList_cons hann heq, ← hi2v]
          exact hrun2

/-- `ConLeche/Kernel/CheckerBase.lean:170-184 checkAnnotList` — each
expression is a fixed point of the annotation pass. -/
theorem check_annot_list_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {xs : alloc.vec.Vec expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hxs : ExprsWF xs)
    (h : checker_base.check_annot_list mode st fe depth xs = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkAnnotList (TypeChecker.lops mode lfe) lfe.env depth.val
          (absExprs xs)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_base.check_annot_list] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_annot_list_from_refines hfuel hk hxs xs.val.length 0#usize st st' fe depth
      (by scalar_tac) hsw hfw h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

end ConRon.Refine.CheckerBase
