/-
Task #21, the derived-field part: the *exact* accessors `bvar_b`/`fvar_b`, the
two memoized walks behind their saturated branch, and the two `O(1)` readers
`loose_bvars_bounded` and `has_fvar` that con-leche's `@[csimp]` substitutes
for the tree walks (`ExprOps.lean:1286-1723`).

This is the first consumer of task #20's `wf_data`: the port's packed 15-bit
field is con-leche's `bvarBRaw`/`fvarBRaw` (`Expr.bvar_b_raw_refines`), which
*is* `bvarBound`/`fvarRange` wherever it did not saturate
(`bvarBRaw_exact`/`fvarBRaw_exact`, proved upstream), and on the saturated
branch alone the port recomputes the same recurrence with a memo -- so the
lemma per accessor is con-leche's own `bvarB_eq`/`fvarB_eq` argument with the
memoized walk's soundness (`MemoBInv`/`MemoFInv`, `ExprOps.lean:1495`/`:1616`)
in place of `bvarBoundGo_spec`/`fvarRangeGo_spec`.

The two walks are keyed by the **node alone**, so they use
`expr_key_exact`/`memo_n_get_hit`, and -- unlike `instantiate1_go` -- they probe
the memo at *every* constructor, which makes each case one memo prologue, one
arithmetic step and one `MemoInv.set`.  The `none` branch is inverted with the
task-#5 idiom (`rw [f.eq_def] at h`, then a plain `simp at h`, `bind_eq_ok_iff`
being a global `simp` lemma): plain `simp` is what reduces the generated
*tuple* binds, which `simp only` leaves as an irreducible `let (a, b) := _`.
-/
import ConRon.Refine.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-- `expr_ops::sub_nat` is Lean's truncated `Nat` subtraction on the
abstraction (task #13's one new helper; con-leche has no such function -- the
`-` it stands for is `Nat`'s). -/
theorem sub_nat_val {a b r : Std.U64} (h : expr_ops.sub_nat a b = ok r) :
    r.val = a.val - b.val := by
  rw [expr_ops.sub_nat] at h
  split at h
  · rw [HashMap.uscalar_sub_eq h]
  · rename_i hge
    have hlt : a.val < b.val := by scalar_tac
    rw [← Result.ok_injective h, Expr.val_zero]
    omega

/-- con-leche's `MemoBInv` (`ExprOps.lean:1495`), as the `Q` of `MemoInv`. -/
def BoundQ : ConLeche.Expr → Std.U64 → Prop := fun k r => r.val = k.bvarBound

/-- con-leche's `MemoFInv` (`ExprOps.lean:1616`), as the `Q` of `MemoInv`. -/
def RangeQ : ConLeche.Expr → Std.U64 → Prop := fun k r => r.val = k.fvarRange


/-- `expr_ops::bvar_bound_go` refines `Expr.bvarBound` (con-leche's `bvarBoundGo`
`ExprOps.lean:1368-1392`, whose soundness is `bvarBoundGo_spec` `:1514`).  One
case per `ExprWF` constructor; the memo is probed at every one, so each case is
either a hit (`MemoInv.hit`) or a compute-and-record (`MemoInv.set`). -/
theorem bvar_bound_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Std.U64) (r : Std.U64),
      MemoInv ExprWF absExpr BoundQ memo →
      expr_ops.bvar_bound_go memo e = ok (r, memo') →
      r.val = (absExpr e).bvarBound ∧ MemoInv ExprWF absExpr BoundQ memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨hr1, x, hdup, x1, hins⟩ := h
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)))) r := by
        show r.val = _
        rw [HashMap.uscalar_add_eq hr1]
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Sort u)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n us)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rf, memo2, hgf, memo3, ⟨ra, hga, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvf, hm2⟩ := ihf memo memo2 rf hm hgf
      obtain ⟨hva, hm3⟩ := iha memo2 memo3 ra hm2 hga
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, hvf, hva]
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm3 hwfe hval hins⟩
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rt, memo2, hgt, memo3, ⟨rb, hgb, i1, hsub, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvt, hm2⟩ := ihty memo memo2 rt hm hgt
      obtain ⟨hvb, hm3⟩ := ihbo memo2 memo3 rb hm2 hgb
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, sub_nat_val hsub, hvt, hvb]
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm3 hwfe hval hins⟩
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rt, memo2, hgt, memo3, ⟨rb, hgb, i1, hsub, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvt, hm2⟩ := ihty memo memo2 rt hm hgt
      obtain ⟨hvb, hm3⟩ := ihbo memo2 memo3 rb hm2 hgb
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, sub_nat_val hsub, hvt, hvb]
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm3 hwfe hval hins⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w' =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w' := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rt, memo2, hgt, memo4,
        ⟨rv, memo3, hgv, rb, hgb, i0, hmax0, i1, hsub, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvt, hm2⟩ := ihty memo memo2 rt hm hgt
      obtain ⟨hvv, hm3⟩ := ihw memo2 memo3 rv hm2 hgv
      obtain ⟨hvb, hm4⟩ := ihbo memo3 memo4 rb hm3 hgb
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, Expr.max_u64_val hmax0, sub_nat_val hsub,
          hvt, hvv, hvb]
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm4 hwfe hval hins⟩
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' r hm h
    rw [expr_ops.bvar_bound_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := BoundQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨memo2, hgs, xd, hdup, xi, hins⟩ := h
      obtain ⟨hvs, hm2⟩ := ih memo memo2 r hm hgs
      have hval : BoundQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)))) r := by
        show r.val = _
        rw [hvs]
        simp [ConLeche.Expr.bvarBound]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm2 hwfe hval hins⟩


/-- `expr_ops::fvar_range_go` refines `Expr.fvarRange` (con-leche's `fvarRangeGo`
`ExprOps.lean:1397-1422`, soundness `fvarRangeGo_spec` `:1635`); the `fvar` twin
of `bvar_bound_go_refines`, with `fvar` annotations not descended into. -/
theorem fvar_range_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Std.U64) (r : Std.U64),
      MemoInv ExprWF absExpr RangeQ memo →
      expr_ops.fvar_range_go memo e = ok (r, memo') →
      r.val = (absExpr e).fvarRange ∧ MemoInv ExprWF absExpr RangeQ memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨hr1, x, hdup, x1, hins⟩ := h
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) r := by
        show r.val = _
        rw [HashMap.uscalar_add_eq hr1]
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Sort u)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n us)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨x, hdup, ⟨x1, hins⟩, hr0⟩ := h
      subst hr0
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)))) 0#u64 := by
        show (0#u64 : Std.U64).val = _
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm hwfe hval hins⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rf, memo2, hgf, memo3, ⟨ra, hga, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvf, hm2⟩ := ihf memo memo2 rf hm hgf
      obtain ⟨hva, hm3⟩ := iha memo2 memo3 ra hm2 hga
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, hvf, hva]
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm3 hwfe hval hins⟩
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rf, memo2, hgf, memo3, ⟨ra, hga, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvf, hm2⟩ := ihty memo memo2 rf hm hgf
      obtain ⟨hva, hm3⟩ := ihbo memo2 memo3 ra hm2 hga
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, hvf, hva]
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm3 hwfe hval hins⟩
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rf, memo2, hgf, memo3, ⟨ra, hga, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvf, hm2⟩ := ihty memo memo2 rf hm hgf
      obtain ⟨hva, hm3⟩ := ihbo memo2 memo3 ra hm2 hga
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, hvf, hva]
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm3 hwfe hval hins⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w' =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w' := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨rt, memo2, hgt, memo4,
        ⟨rv, memo3, hgv, rb, hgb, i0, hmax0, hop⟩, x, hdup, x1, hins⟩ := h
      obtain ⟨hvt, hm2⟩ := ihty memo memo2 rt hm hgt
      obtain ⟨hvv, hm3⟩ := ihw memo2 memo3 rv hm2 hgv
      obtain ⟨hvb, hm4⟩ := ihbo memo3 memo4 rb hm3 hgb
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)))) r := by
        show r.val = _
        rw [Expr.max_u64_val hop, Expr.max_u64_val hmax0, hvt, hvv, hvb]
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm4 hwfe hval hins⟩
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' r hm h
    rw [expr_ops.fvar_range_go.eq_def] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := Std.U64 × _) h
      have er : r = w := (congrArg Prod.fst e0).symm
      have em : memo' = memo := (congrArg Prod.snd e0).symm
      subst er; subst em
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RangeQ)
        expr_key_exact hm hwfe (memo_n_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp at h
      obtain ⟨memo2, hgs, xd, hdup, xi, hins⟩ := h
      obtain ⟨hvs, hm2⟩ := ih memo memo2 r hm hgs
      have hval : RangeQ (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)))) r := by
        show r.val = _
        rw [hvs]
        simp [ConLeche.Expr.fvarRange]
      rw [Expr.dup_eq hdup] at hins
      exact ⟨hval, MemoInv.set expr_key_exact hm2 hwfe hval hins⟩


/-- `expr_ops::bvar_bound_memo` refines `Expr.bvarBound` (con-leche's
`bvarBoundMemo_eq`, `ExprOps.lean:1569-1572`): the memo starts empty, so the
walk's own lemma is the answer. -/
theorem bvar_bound_memo_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : expr_ops.bvar_bound_memo e = ok r) : r.val = (absExpr e).bvarBound := by
  rw [expr_ops.bvar_bound_memo] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  exact (bvar_bound_go_refines he memo memo' r0 (new_memo_inv hnew) hgo).1

/-- `expr_ops::fvar_range_memo` refines `Expr.fvarRange` (`fvarRangeMemo_eq`,
`ExprOps.lean:1690-1693`). -/
theorem fvar_range_memo_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : expr_ops.fvar_range_memo e = ok r) : r.val = (absExpr e).fvarRange := by
  rw [expr_ops.fvar_range_memo] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  exact (fvar_range_go_refines he memo memo' r0 (new_memo_inv hnew) hgo).1

/-! ### The two exact accessors

`bvar_b`/`fvar_b` read the packed field and fall back to the memoized walk on
the *saturated* value alone.  con-leche's `bvarB_eq`/`fvarB_eq` is the same
two-branch argument, and `bvarBRaw_exact`/`fvarBRaw_exact` is what makes the
unsaturated branch exact -- so each lemma is: the field read (`wf_data`, task
#20), the saturation test, and one of the two upstream theorems. -/

/-- **`expr_ops::bvar_b` refines `Expr.bvarB`** (`ExprOps.lean:1427-1432`), and
therefore `Expr.bvarBound` (`bvarB_eq`, `:1574`). -/
theorem bvar_b_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : expr_ops.bvar_b e = ok r) : r.val = (absExpr e).bvarB := by
  rw [expr_ops.bvar_b] at h
  obtain ⟨r0, hraw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨sr, hsr, h⟩ := bind_eq_ok_iff.mp h
  have hraw' : r0.val = (absExpr e).bvarBRaw := Expr.bvar_b_raw_refines he hraw
  have hsr' : sr.val = ConLeche.satRange := Expr.sat_range_val hsr
  rw [ConLeche.Expr.bvarB_eq]
  split at h
  · exact bvar_bound_memo_refines he h
  · rename_i hne
    have hne' : r0.val ≠ ConLeche.satRange := by
      rw [← hsr']
      intro hc
      exact hne (Std.UScalar.eq_of_val_eq hc)
    have hlt : (absExpr e).bvarBRaw < ConLeche.satRange := by
      have := ConLeche.Expr.bvarBRaw_lt (absExpr e)
      rw [← hraw'] at this ⊢
      simp only [ConLeche.satRange] at hne' ⊢
      omega
    rw [← Result.ok_injective h, hraw']
    exact ConLeche.Expr.bvarBRaw_exact _ hlt

/-- **`expr_ops::fvar_b` refines `Expr.fvarB`** (`ExprOps.lean:1434-1439`), and
therefore `Expr.fvarRange` (`fvarB_eq`, `:1695`). -/
theorem fvar_b_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : expr_ops.fvar_b e = ok r) : r.val = (absExpr e).fvarB := by
  rw [expr_ops.fvar_b] at h
  obtain ⟨r0, hraw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨sr, hsr, h⟩ := bind_eq_ok_iff.mp h
  have hraw' : r0.val = (absExpr e).fvarBRaw := Expr.fvar_b_raw_refines he hraw
  have hsr' : sr.val = ConLeche.satRange := Expr.sat_range_val hsr
  rw [ConLeche.Expr.fvarB_eq]
  split at h
  · exact fvar_range_memo_refines he h
  · rename_i hne
    have hne' : r0.val ≠ ConLeche.satRange := by
      rw [← hsr']
      intro hc
      exact hne (Std.UScalar.eq_of_val_eq hc)
    have hlt : (absExpr e).fvarBRaw < ConLeche.satRange := by
      have := ConLeche.Expr.fvarBRaw_lt (absExpr e)
      rw [← hraw'] at this ⊢
      simp only [ConLeche.satRange] at hne' ⊢
      omega
    rw [← Result.ok_injective h, hraw']
    exact ConLeche.Expr.fvarBRaw_exact _ hlt

/-- **`expr_ops::loose_bvars_bounded` refines `Expr.looseBVarsBounded`**
(`ExprOps.lean:868`): the port implements the `@[csimp]` member
`looseBVarsBoundedFast` (`:1717`), whose equation with the logical walk is
`looseBVarsBounded_iff` (`:1306`) through `bvarB_eq`. -/
theorem loose_bvars_bounded_refines {e : expr.Expr} {k : Std.U64} {b : Bool}
    (he : ExprWF e) (h : expr_ops.loose_bvars_bounded k e = ok b) :
    b = (absExpr e).looseBVarsBounded k.val := by
  rw [expr_ops.loose_bvars_bounded] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = (absExpr e).bvarBound := by
    rw [bvar_b_refines he hi, ConLeche.Expr.bvarB_eq]
  rw [← Result.ok_injective h]
  by_cases hc : (absExpr e).bvarBound ≤ k.val
  · rw [ConLeche.Expr.looseBVarsBounded_iff.mpr hc]
    have : i.val ≤ k.val := by rw [hiv]; exact hc
    simp only [decide_eq_true_eq]
    scalar_tac
  · have hb : (absExpr e).looseBVarsBounded k.val = false := by
      cases hb : (absExpr e).looseBVarsBounded k.val with
      | false => rfl
      | true => exact absurd (ConLeche.Expr.looseBVarsBounded_iff.mp hb) hc
    rw [hb]
    have : ¬ (i.val ≤ k.val) := by rw [hiv]; exact hc
    simp only [decide_eq_false_iff_not]
    scalar_tac

/-- **`expr_ops::has_fvar` refines `Expr.hasFvar`** (`ExprOps.lean:907`): the
port implements the `@[csimp]` member `hasFvarFast` (`:1708`), whose equation
with the logical walk is `fvarRange_bne_zero` (`:1333`) through `fvarB_eq`. -/
theorem has_fvar_refines {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (h : expr_ops.has_fvar e = ok b) : b = (absExpr e).hasFvar := by
  rw [expr_ops.has_fvar] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  have hiv : i.val = (absExpr e).fvarRange := by
    rw [fvar_b_refines he hi, ConLeche.Expr.fvarB_eq]
  rw [← Result.ok_injective h, ← ConLeche.Expr.fvarRange_bne_zero, ← hiv]
  by_cases hc : i.val = 0
  · have h0 : i = 0#u64 := Std.UScalar.eq_of_val_eq (by rw [hc, Expr.val_zero])
    have hl : (i != 0#u64) = false := by simp [h0]
    have hr : ((i.val : Nat) != 0) = false := by simp [hc]
    rw [hl, hr]
  · have hne : i ≠ 0#u64 := by
      intro hcc
      exact hc (by rw [hcc, Expr.val_zero])
    have hl : (i != 0#u64) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact hne
    have hr : ((i.val : Nat) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact hc
    rw [hl, hr]

end ConRon.Refine.ExprOps
