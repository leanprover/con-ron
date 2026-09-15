/-
The substitution half of `crates/con-ron-core/src/cached/expr_ops_c.rs`
(task #26), refined against `ConLeche/Cached/ExprOpsC.lean` (task #51; see
`ConRon/Refine/ExprOpsC.lean` for the module note that covers all four files).

`instantiate1`, `instantiate1Lift`, `instantiateList` and `instantiateRev`: the
memoised DAG walks the executed checker runs, each behind the derived-field
cutoff `bvarB ≤ d` that returns the node *itself*.  Statements are against the
cited `Expr` definitions; the bridge to `ConLeche.Expr`'s logical functions is
con-leche's `Verify/Cached/OpsC.lean` (`instantiate1_spec`,
`instantiate1Lift_spec`, `instantiateList_spec`, `instantiateRev_spec`).

The memo is task #47's `MemoInv` at the `(node, cursor)` key: policy-agnostic,
so the same `hit`/`set` pair serves the cached walks' "compound nodes only"
policy and `expr_ops`' unconditional one.  What is new here is the cutoff, one
lemma per `Q` (`instantiate1_cutoff`, `instantiate_list_cutoff`,
`instantiate1_lift_cutoff` -- the last one is task #47's, reused verbatim: the
`Q` is the same `Inst1LQ`).
-/
import ConRon.Refine.ExprOpsC

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOpsC

open ConRon.Refine.ExprOps

/-! ## `instantiate1` (`ExprOpsC.lean:97-151`, wrapper `:275-277`)

The cutoff and the compound-only memo, against `Expr.instantiate1C`.  The `Q`
of the memo is task #47's `Inst1Q` -- the recorded answers are the same answers,
because `instantiate1_spec` says the two walks compute the same function. -/

/-- The cutoff branch of `instantiate1_go`, shared by all ten constructors:
a node whose loose-`bvar` bound is at or below the cursor has no `bvar d` to
replace, so the walk returns it unchanged (`Expr.instantiate1_eq_self` through
`looseBVarsBounded_iff`, which is con-leche's own `Expr.bvarB_le`). -/
theorem instantiate1_cutoff {v : expr.Expr} {d bb : Std.U64} {e r : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo)
    (hbb : expr_ops.bvar_b e = ok bb) (hle : bb.val ≤ d.val)
    (h : (do let c ← expr.dup e; ok (c, memo)) = ok (r, memo')) :
    (ExprWF r ∧
        absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val) ∧
      MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo' := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨c, hdup, hr, hmm⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr; subst hmm
  refine ⟨⟨hwfe, ?_⟩, hm⟩
  have hbnd : ConLeche.Expr.looseBVarsBounded d.val (absExpr e) = true :=
    ConLeche.Expr.looseBVarsBounded_iff.mpr
      (by rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines hwfe hbb]; exact hle)
  rw [ConLeche.Expr.instantiate1_eq_self hbnd]

/-- **`expr_ops_c::instantiate1_go` refines `Expr.instantiate1`** (con-leche's
`instantiate1Go`, `ExprOpsC.lean:97-151`, soundness `instantiate1Go_spec`,
`Verify/Cached/OpsC.lean:181`): the `bvar_b` cutoff first, then the memo keyed
by the node and the cursor, probed *only* in the five compound arms (the
module's memo-discipline note 2 -- an atom is answered on the spot and never
recorded). -/
theorem instantiate1_go_refines {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr) (d : Std.U64)
      (r : expr.Expr),
      MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo →
      cached.expr_ops_c.instantiate1_go v memo e d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r = ConLeche.Expr.instantiate1 (absExpr e) (absExpr v) d.val) ∧
        MemoInv KeyWF absKey (Inst1Q (absExpr v)) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · rename_i hid
        have hv' : i.val = d.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨c, hdup, hr, hmm⟩ := h
        rw [Expr.dup_eq hdup] at hr
        subst hr; subst hmm
        refine ⟨⟨hv, ?_⟩, hm⟩
        simp [ConLeche.Expr.instantiate1, hv']
      · rename_i hid
        have hne : i.val ≠ d.val := fun hc => hid (Std.UScalar.eq_of_val_eq hc)
        split at h
        · rename_i hgt
          have hgt' : d.val < i.val := by scalar_tac
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨i1, hi1, c, hc, hr, hmm⟩ := h
          subst hr; subst hmm
          refine ⟨⟨Expr.mk_bvar_wf hc, ?_⟩, hm⟩
          rw [Expr.mk_bvar_refines hc, ConLeche.Expr.mkBvar_eq,
            HashMap.uscalar_sub_eq hi1]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1]
          rw [if_neg hne, if_pos (by omega)]
          congr 1
        · rename_i hgt
          have hgt' : ¬ (d.val < i.val) := fun hc => hgt (by scalar_tac)
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨c, hdup, hr, hmm⟩ := h
          rw [Expr.dup_eq hdup] at hr
          subst hr; subst hmm
          refine ⟨⟨hwfe, ?_⟩, hm⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1]
          rw [if_neg hne, if_neg (by omega)]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hk
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hf2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨f2, memo2⟩ := p1
        obtain ⟨p2, ha2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨a2, memo3⟩ := p2
        obtain ⟨r1, happ, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 d f2 hm hf2
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 d a2 hm2 ha2
        obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : Inst1Q (absExpr v)
            (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), d⟩) r := by
          refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
          rw [Expr.app_refines happ, habs2, habs3]
          simp [ConLeche.Expr.instantiate1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hk
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b, memo3⟩ := p2
        obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm ht
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 dd b hm2 hb
        obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : Inst1Q (absExpr v)
            (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), d⟩) r := by
          refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
          rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hdd]
          simp [ConLeche.Expr.instantiate1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hk
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b, memo3⟩ := p2
        obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm ht
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 dd b hm2 hb
        obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : Inst1Q (absExpr v)
            (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), d⟩) r := by
          refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
          rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hdd]
          simp [ConLeche.Expr.instantiate1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hk
      subst hkk
      cases o with
      | some w' =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w' := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hv2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨w2, memo3⟩ := p2
        obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨p3, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b, memo4⟩ := p3
        obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
        have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm ht
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 d w2 hm2 hv2
        obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 dd b hm3 hb
        obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p4, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo5⟩ := p4
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo5 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : Inst1Q (absExpr v)
            (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), d⟩) r := by
          refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
          rw [Expr.let_e_refines hlet, habs2, habs3, habs4, HashMap.uscalar_add_eq hdd]
          simp [ConLeche.Expr.instantiate1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_go.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_cutoff hwfe hm hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hk
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1Q (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hu, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨u, memo2⟩ := p1
        obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
        have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 d u hm hu
        obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
        subst hsn
        have hans : Inst1Q (absExpr v)
            (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)), d⟩) r := by
          refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
          rw [Expr.proj_refines hproj, habs2]
          simp [ConLeche.Expr.instantiate1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins

/-- **`expr_ops_c::instantiate1` refines `Expr.instantiate1C`**
(`ExprOpsC.lean:275-277`): the cutoff, then the walk under a fresh table.  The
cited `instantiate1_spec` (`Verify/Cached/OpsC.lean:332`) is what turns the
logical answer the walk's lemma gives into the `Expr` function the checker's
callers name. -/
theorem instantiate1_refines {e v r : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hv : ExprWF v) (h : cached.expr_ops_c.instantiate1 e v d = ok r) :
    absExpr r = ConLeche.Expr.instantiate1C (absExpr e) (absExpr v) d.val ∧
      ExprWF r := by
  rw [ConLeche.Expr.instantiate1C_spec]
  rw [cached.expr_ops_c.instantiate1] at h
  obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · rename_i hle
    have hbnd : ConLeche.Expr.looseBVarsBounded d.val (absExpr e) = true :=
      ConLeche.Expr.looseBVarsBounded_iff.mpr
        (by rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines he hbb]; scalar_tac)
    rw [Expr.dup_eq h, ConLeche.Expr.instantiate1_eq_self hbnd]
    exact ⟨rfl, he⟩
  · obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r0, memo'⟩ := p
    have hr : r0 = r := Result.ok_injective h
    subst hr
    obtain ⟨⟨hwf, habs⟩, -⟩ :=
      instantiate1_go_refines hv he memo memo' d r0 (new_memo_inv hnew) hgo
    exact ⟨habs, hwf⟩

/-! ## `instantiate1Lift` (`ExprOpsC.lean:167-273`)

The capture-avoiding substitution, and the one operation of this module with
*three* layers: the `bvarB` cutoff, a **budgeted plain descent** at 4096 nodes
(no memo -- a table would be a tax on the small terms that are the common
case), and the memoised walk past the budget.  The memoised layer is
`expr_ops::instantiate1_lift_go` node for node, so its lemma is task #47's with
the `.bvar` arm's two constructors changed (`expr::mk_bvar` and `expr::dup`
where `expr_ops` writes `expr::bvar`); the budgeted layer is new.

`instantiate1_lift_b_compound` is entered only from the budget test in
`instantiate1_lift_b`, i.e. never at a `.bvar` node (whose arm answers on the
spot).  Its catch-all `_ =>` arm returns the node itself, which *is*
`instantiate1Lift`'s value at every other kind, so `NotBvar` is the one
hypothesis its lemma needs -- and the two lemmas are proved **together**: the
`_b` clause at a node needs the `_b_compound` clause at the *same* node (the
budget test is a tail call into it), and the `_b_compound` clause needs the
`_b` clause at the node's *children*, which is what the `ExprWF` induction
supplies. -/

/-- The node kinds `instantiate1_lift_b_compound` is reachable at: everything
but `.bvar`. -/
def NotBvar (e : expr.Expr) : Prop := ∀ i : Std.U64, e._0.kind ≠ expr.ExprKind.Bvar i

/-- The budgeted descent's cutoff branch: a node bounded at or below the cursor
is returned itself (`Expr.instantiate1Lift_of_bvarBound_le`). -/
theorem lift_b_cutoff {v : expr.Expr} {d bb fuel fuel' : Std.U64} {e r : expr.Expr}
    (hwfe : ExprWF e) (hbb : expr_ops.bvar_b e = ok bb) (hle : bb.val ≤ d.val)
    (h : (do let c ← expr.dup e; ok (some c, fuel)) = ok (some r, fuel')) :
    ExprWF r ∧
      absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨c, hdup, hr, -⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr
  refine ⟨hwfe, ?_⟩
  have hbnd : (absExpr e).bvarBound ≤ d.val := by
    rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines hwfe hbb]; exact hle
  rw [ConLeche.Expr.instantiate1Lift_of_bvarBound_le _ _ _ hbnd]

/-- The catch-all arm of `instantiate1_lift_b_compound` at a non-`.bvar` atom:
the node itself, which is what `instantiate1Lift` gives there. -/
theorem lift_b_self {v : expr.Expr} {d fuel fuel' : Std.U64} {e r : expr.Expr}
    (hwfe : ExprWF e)
    (hself : ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val = absExpr e)
    (h : (do let c ← expr.dup e; ok (some c, fuel)) = ok (some r, fuel')) :
    ExprWF r ∧
      absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨c, hdup, hr, -⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr
  exact ⟨hwfe, hself.symm⟩

/-- **`expr_ops_c::instantiate1_lift_b` and
`expr_ops_c::instantiate1_lift_b_compound` refine `Expr.instantiate1Lift`**
(con-leche's `instantiate1LiftB`, `ExprOpsC.lean:167-211`, soundness
`instantiate1LiftB_spec`, `Verify/Cached/OpsC.lean:2066`): *wherever the budget
suffices*, the plain rebuild is the substitution.  Nothing is claimed when the
budget runs out -- the cited `(none, 0)` keeps nothing it built, and the
wrapper falls back to the memoised walk. -/
theorem instantiate1_lift_b_pair {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr}
    (he : ExprWF e) :
    (∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b v fuel e d = ok (some r, fuel') →
        ExprWF r ∧
          absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val) ∧
      (NotBvar e → ∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b_compound v fuel e d = ok (some r, fuel') →
        ExprWF r ∧
          absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val) := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    refine ⟨?_, fun hc => absurd (node_kind d1 (expr.ExprKind.Bvar i)) (hc i)⟩
    intro fuel d fuel' r h
    rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · rename_i hid
        have hid2 : i.val = d.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          Option.some.injEq] at h
        obtain ⟨x, hx, hr, -⟩ := h
        subst hr
        obtain ⟨habs, hwf⟩ := lift_loose_bvars_refines hv hx
        refine ⟨hwf, ?_⟩
        rw [habs]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
        rw [if_pos hid2, Expr.val_zero]
      · rename_i hid
        have hid2 : i.val ≠ d.val := fun hc => hid (Std.UScalar.eq_of_val_eq hc)
        split at h
        · rename_i hgt
          have hgt2 : d.val < i.val := by scalar_tac
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
            Option.some.injEq] at h
          obtain ⟨i2, hi2, x, hx, hr, -⟩ := h
          subst hr
          refine ⟨Expr.mk_bvar_wf hx, ?_⟩
          rw [Expr.mk_bvar_refines hx, ConLeche.Expr.mkBvar_eq,
            HashMap.uscalar_sub_eq hi2]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
          rw [if_neg hid2, if_pos (by omega)]
          congr 1
        · rename_i hgt
          have hgt2 : ¬ (d.val < i.val) := fun hc => hgt (by scalar_tac)
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
            Option.some.injEq] at h
          obtain ⟨x, hx, hr, -⟩ := h
          rw [Expr.dup_eq hx] at hr
          subst hr
          refine ⟨hwfe, ?_⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
          rw [if_neg hid2, if_neg (by omega)]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    have hself : ∀ (d : Std.U64),
        ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty))))
          (absExpr v) d.val
        = absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty))) := by
      intro d; simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, ?_⟩
    · intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
      · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact lift_b_self hwfe (hself d) h
    · intro _ fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      exact lift_b_self hwfe (hself d) h
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    have hself : ∀ (d : Std.U64),
        ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Sort u))))
          (absExpr v) d.val
        = absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Sort u))) := by
      intro d; simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, ?_⟩
    · intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
      · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact lift_b_self hwfe (hself d) h
    · intro _ fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      exact lift_b_self hwfe (hself d) h
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    have hself : ∀ (d : Std.U64),
        ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n us))))
          (absExpr v) d.val
        = absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n us))) := by
      intro d; simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, ?_⟩
    · intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
      · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact lift_b_self hwfe (hself d) h
    · intro _ fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      exact lift_b_self hwfe (hself d) h
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    have hself : ∀ (d : Std.U64),
        ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l))))
          (absExpr v) d.val
        = absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l))) := by
      intro d; simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, ?_⟩
    · intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
      · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact lift_b_self hwfe (hself d) h
    · intro _ fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      exact lift_b_self hwfe (hself d) h
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    have hcomp : ∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b_compound v fuel
            (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a))) d
          = ok (some r, fuel') →
        ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a))))
          (absExpr v) d.val := by
      intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o1, fu1⟩ := p1
      cases o1 with
      | none => simp at h
      | some f2 =>
        obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o2, fu2⟩ := p2
        cases o2 with
        | none => simp at h
        | some a2 =>
          obtain ⟨x, happ, h⟩ := bind_eq_ok_iff.mp h
          have hxr : x = r := Option.some_injective _ (congrArg Prod.fst
            (Result.ok_injective (α := Option expr.Expr × Std.U64) h))
          subst hxr
          obtain ⟨hwf2, habs2⟩ := ihf.1 fuel d fu1 f2 hp1
          obtain ⟨hwf3, habs3⟩ := iha.1 fu1 d fu2 a2 hp2
          refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
          rw [Expr.app_refines happ, habs2, habs3]
          simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, fun _ => hcomp⟩
    intro fuel d fuel' r h
    rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · simp at h
      · obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
        exact hcomp f1 d fuel' r h
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    have hcomp : ∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b_compound v fuel
            (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m))) d
          = ok (some r, fuel') →
        ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m))))
          (absExpr v) d.val := by
      intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o1, fu1⟩ := p1
      cases o1 with
      | none => simp at h
      | some t =>
        obtain ⟨dd, hdd, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o2, fu2⟩ := p2
        cases o2 with
        | none => simp at h
        | some b =>
          obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨x, hlam, h⟩ := bind_eq_ok_iff.mp h
          have hxr : x = r := Option.some_injective _ (congrArg Prod.fst
            (Result.ok_injective (α := Option expr.Expr × Std.U64) h))
          subst hxr
          obtain ⟨hwf2, habs2⟩ := ihty.1 fuel d fu1 t hp1
          obtain ⟨hwf3, habs3⟩ := ihbo.1 fu1 dd fu2 b hp2
          refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
          rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hdd]
          simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, fun _ => hcomp⟩
    intro fuel d fuel' r h
    rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · simp at h
      · obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
        exact hcomp f1 d fuel' r h
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    have hcomp : ∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b_compound v fuel
            (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m))) d
          = ok (some r, fuel') →
        ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m))))
          (absExpr v) d.val := by
      intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o1, fu1⟩ := p1
      cases o1 with
      | none => simp at h
      | some t =>
        obtain ⟨dd, hdd, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o2, fu2⟩ := p2
        cases o2 with
        | none => simp at h
        | some b =>
          obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨x, hfa, h⟩ := bind_eq_ok_iff.mp h
          have hxr : x = r := Option.some_injective _ (congrArg Prod.fst
            (Result.ok_injective (α := Option expr.Expr × Std.U64) h))
          subst hxr
          obtain ⟨hwf2, habs2⟩ := ihty.1 fuel d fu1 t hp1
          obtain ⟨hwf3, habs3⟩ := ihbo.1 fu1 dd fu2 b hp2
          refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
          rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hdd]
          simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, fun _ => hcomp⟩
    intro fuel d fuel' r h
    rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · simp at h
      · obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
        exact hcomp f1 d fuel' r h
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    have hcomp : ∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b_compound v fuel
            (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo))) d
          = ok (some r, fuel') →
        ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo))))
          (absExpr v) d.val := by
      intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o1, fu1⟩ := p1
      cases o1 with
      | none => simp at h
      | some t =>
        obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o2, fu2⟩ := p2
        cases o2 with
        | none => simp at h
        | some w2 =>
          obtain ⟨dd, hdd, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨p3, hp3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o3, fu3⟩ := p3
          cases o3 with
          | none => simp at h
          | some b =>
            obtain ⟨x, hlet, h⟩ := bind_eq_ok_iff.mp h
            have hxr : x = r := Option.some_injective _ (congrArg Prod.fst
            (Result.ok_injective (α := Option expr.Expr × Std.U64) h))
            subst hxr
            obtain ⟨hwf2, habs2⟩ := ihty.1 fuel d fu1 t hp1
            obtain ⟨hwf3, habs3⟩ := ihw.1 fu1 d fu2 w2 hp2
            obtain ⟨hwf4, habs4⟩ := ihbo.1 fu2 dd fu3 b hp3
            refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
            rw [Expr.let_e_refines hlet, habs2, habs3, habs4,
              HashMap.uscalar_add_eq hdd]
            simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, fun _ => hcomp⟩
    intro fuel d fuel' r h
    rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · simp at h
      · obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
        exact hcomp f1 d fuel' r h
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    have hcomp : ∀ (fuel d fuel' : Std.U64) (r : expr.Expr),
        cached.expr_ops_c.instantiate1_lift_b_compound v fuel
            (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x))) d
          = ok (some r, fuel') →
        ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x))))
          (absExpr v) d.val := by
      intro fuel d fuel' r h
      rw [cached.expr_ops_c.instantiate1_lift_b_compound.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o1, fu1⟩ := p1
      cases o1 with
      | none => simp at h
      | some s2 =>
        obtain ⟨n2, hn2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨x2, hproj, h⟩ := bind_eq_ok_iff.mp h
        have hxr : x2 = r := Option.some_injective _ (congrArg Prod.fst
            (Result.ok_injective (α := Option expr.Expr × Std.U64) h))
        subst hxr
        have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
        subst hsn
        obtain ⟨hwf2, habs2⟩ := ih.1 fuel d fu1 s2 hp1
        refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
        rw [Expr.proj_refines hproj, habs2]
        simp [ConLeche.Expr.instantiate1Lift]
    refine ⟨?_, fun _ => hcomp⟩
    intro fuel d fuel' r h
    rw [cached.expr_ops_c.instantiate1_lift_b.eq_def] at h
    obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact lift_b_cutoff hwfe hbb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · simp at h
      · obtain ⟨f1, hf1, h⟩ := bind_eq_ok_iff.mp h
        exact hcomp f1 d fuel' r h

/-- **`expr_ops_c::instantiate1_lift_b` refines `Expr.instantiate1Lift`** where
the budget suffices (the first half of `instantiate1_lift_b_pair`). -/
theorem instantiate1_lift_b_refines {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr}
    (he : ExprWF e) {fuel d fuel' : Std.U64} {r : expr.Expr}
    (h : cached.expr_ops_c.instantiate1_lift_b v fuel e d = ok (some r, fuel')) :
    ExprWF r ∧
      absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val :=
  (instantiate1_lift_b_pair hv he).1 fuel d fuel' r h

/-- **`expr_ops_c::instantiate1_lift_b_compound` refines
`Expr.instantiate1Lift`** at the five compound kinds it is reachable at (the
second half of `instantiate1_lift_b_pair`). -/
theorem instantiate1_lift_b_compound_refines {v : expr.Expr} (hv : ExprWF v)
    {e : expr.Expr} (he : ExprWF e) (hnb : NotBvar e) {fuel d fuel' : Std.U64}
    {r : expr.Expr}
    (h : cached.expr_ops_c.instantiate1_lift_b_compound v fuel e d
      = ok (some r, fuel')) :
    ExprWF r ∧
      absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val :=
  (instantiate1_lift_b_pair hv he).2 hnb fuel d fuel' r h

/-- **`expr_ops_c::instantiate1_lift_go` refines `Expr.instantiate1Lift`**
(con-leche's `instantiate1LiftGo`, `ExprOpsC.lean:213-265`, soundness
`instantiate1LiftGo_spec`, `Verify/Cached/OpsC.lean:1919`): the `bvar_b` cutoff,
then the memo keyed by the node and the cursor; the `.bvar` arm at the cursor
lifts `v`'s own loose variables past the binders crossed on the way, which is
what `instantiate1` may not do. -/
theorem instantiate1_lift_go_refines {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (d : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (Inst1LQ (absExpr v)) memo →
      cached.expr_ops_c.instantiate1_lift_go v memo e d = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val) ∧
        MemoInv KeyWF absKey (Inst1LQ (absExpr v)) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      split at h
      · rename_i hid
        have hid2 : i.val = d.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, hx, hr, hmm⟩ := h
        subst hr; subst hmm
        obtain ⟨habs, hwf⟩ := lift_loose_bvars_refines hv hx
        refine ⟨⟨hwf, ?_⟩, hm⟩
        rw [habs]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
        rw [if_pos hid2, Expr.val_zero]
      · rename_i hid
        have hid2 : i.val ≠ d.val := fun hc => hid (Std.UScalar.eq_of_val_eq hc)
        split at h
        · rename_i hgt
          have hgt2 : d.val < i.val := by scalar_tac
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨i2, hi2, x, hx, hr, hmm⟩ := h
          subst hr; subst hmm
          refine ⟨⟨Expr.mk_bvar_wf hx, ?_⟩, hm⟩
          rw [Expr.mk_bvar_refines hx, ConLeche.Expr.mkBvar_eq,
            HashMap.uscalar_sub_eq hi2]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
          rw [if_neg hid2, if_pos (by omega)]
          simp
        · rename_i hgt
          have hgt2 : ¬ (d.val < i.val) := fun hc => hgt (by scalar_tac)
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨x, hx, hr, hmm⟩ := h
          rw [Expr.dup_eq hx] at hr
          subst hr; subst hmm
          refine ⟨⟨hwfe, ?_⟩, hm⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
          rw [if_neg hid2, if_neg (by omega)]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1LQ (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hgf, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨f2, memo2⟩ := p1
        obtain ⟨p2, hga, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨a2, memo3⟩ := p2
        obtain ⟨r1, hbuild, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective
          (α := ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 d f2 hm hgf
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 d a2 hm2 hga
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Inst1LQ (absExpr v) (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), d⟩) r := by
          refine ⟨Expr.app_wf hwf2 hwf3 hbuild, ?_⟩
          rw [Expr.app_refines hbuild, habs2, habs3]
          simp [ConLeche.Expr.instantiate1Lift]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1LQ (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hgt, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨cc, hcc, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨p2, hgb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b, memo3⟩ := p2
        obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hbuild, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective
          (α := ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Inst1LQ (absExpr v) (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), d⟩) r := by
          refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.lam_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.instantiate1Lift]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1LQ (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hgt, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨cc, hcc, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨p2, hgb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b, memo3⟩ := p2
        obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hbuild, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective
          (α := ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Inst1LQ (absExpr v) (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), d⟩) r := by
          refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.forall_e_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.instantiate1Lift]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some w2 =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w2 := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1LQ (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hgt, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hgv, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨w3, memo3⟩ := p2
        obtain ⟨cc, hcc, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨p3, hgb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b, memo4⟩ := p3
        obtain ⟨r1, hbuild, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective
          (α := ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr × _) hgo
        have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 d t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 d w3 hm2 hgv
        obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 cc b hm3 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Inst1LQ (absExpr v) (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), d⟩) r := by
          refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hbuild, ?_⟩
          rw [Expr.let_e_refines hbuild, habs2, habs3, habs4,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.instantiate1Lift]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' d r hm h
    rw [cached.expr_ops_c.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Inst1LQ (absExpr v))
          key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hgs, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨uu, memo2⟩ := p1
        obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hbuild, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective
          (α := ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr × _) hgo
        have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 d uu hm hgs
        have hsn : s = n2 :=
          (Result.ok_injective (hn2.symm.trans (name_dup_eq s))).symm
        subst hsn
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Inst1LQ (absExpr v) (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)), d⟩) r := by
          refine ⟨Expr.proj_wf hs hwf2 hbuild, ?_⟩
          rw [Expr.proj_refines hbuild, habs2]
          simp [ConLeche.Expr.instantiate1Lift]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins



/-- **`expr_ops_c::instantiate1_lift` refines `Expr.instantiate1LiftC`**
(`ExprOpsC.lean:267-273`): the cutoff, the budgeted descent at 4096 nodes, the
memoised walk when the budget runs out.  `instantiate1Lift_spec`
(`Verify/Cached/OpsC.lean:2256`) is the same three-way split on the Lean side. -/
theorem instantiate1_lift_refines {e v r : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hv : ExprWF v) (h : cached.expr_ops_c.instantiate1_lift e v d = ok r) :
    absExpr r = ConLeche.Expr.instantiate1LiftC (absExpr e) (absExpr v) d.val ∧
      ExprWF r := by
  rw [ConLeche.Expr.instantiate1LiftC_spec]
  rw [cached.expr_ops_c.instantiate1_lift] at h
  obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · rename_i hle
    have hbnd : (absExpr e).bvarBound ≤ d.val := by
      rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines he hbb]; scalar_tac
    rw [Expr.dup_eq h, ConLeche.Expr.instantiate1Lift_of_bvarBound_le _ _ _ hbnd]
    exact ⟨rfl, he⟩
  · obtain ⟨p, hb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, fu⟩ := p
    cases o with
    | some w =>
      have hr : w = r := Result.ok_injective h
      subst hr
      obtain ⟨hwf, habs⟩ := instantiate1_lift_b_refines hv he hb
      exact ⟨habs, hwf⟩
    | none =>
      obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, memo'⟩ := q
      have hr : r0 = r := Result.ok_injective h
      subst hr
      obtain ⟨⟨hwf, habs⟩, -⟩ :=
        instantiate1_lift_go_refines hv he memo memo' d r0 (new_memo_inv hnew) hgo
      exact ⟨habs, hwf⟩

/-! ## The bulk substitutions (`ExprOpsC.lean:279-445`)

`instantiateList` and `instantiateRev` share the memo discipline the module's
note 3 describes: the key is `(node, cursor)` and the **live prefix `k` is not
part of it**, because `k` is invariant over the life of one table -- the one
place it shrinks is the `bvar` arm's re-entry at a replacement, and that runs
under a *fresh* table (`instantiate_list_bvar`/`instantiate_rev_bvar` allocate
there and nowhere else).  So the invariant is parameterised by `k`
(con-leche's `MemoLInv ws k memo`) and the walk's lemma is a strong induction on
`k` *outside* the induction on the `ExprWF` derivation, exactly as
`instantiateListGo_spec` (`Verify/Cached/OpsC.lean:419`) is and as task #47's
`instantiate_list_refines_aux` is.

Discharged in task #54.  The proof is `instantiate1_go_refines`' case analysis
with the live prefix threaded through, under one extra layer: the `GoLP`/`GoRP`
propositions below package "the walk's statement at *one* live prefix `K`", and
`instantiate_list_go_aux`/`instantiate_rev_go_aux` prove `∀ K, GoLP vs K` by
`Nat.strong_induction_on`, so that the `.bvar` arm may apply the walk's own
lemma at the strictly smaller prefix `i - d` under the fresh table
`instantiate_list_bvar` allocates.

`instantiate_rev_bvar_refines` carries one hypothesis the task-#51 statement
did not: `j.val < vs.val.length`.  It has to -- `vs.val[vs.val.length - 1 -
j.val]? = some w` does *not* bound `j`, because `Nat` subtraction saturates at
`0`, so without the bound the statement is false for `j ≥ vs.len`, where the
port returns the node itself while the conclusion still speaks about `vs[0]`.
The forward twin needs no such hypothesis: `vs.val[j.val]? = some w` bounds `j`
by itself.  Every caller has the bound (the `.bvar` arm reaches the callee
under `i - d < k ≤ vs.len`). -/

/-- con-leche's `MemoLInv` (`Verify/Cached/OpsC.lean:349`), as the `Q` of
`MemoInv`: every recorded answer is the bulk substitution of the **live prefix**
at the key's cursor.  `k` is a parameter of the invariant, not of the key. -/
def MemoLQ (ws : List ConLeche.Expr) (k : Nat) :
    ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun key r => ExprWF r ∧ absExpr r = ConLeche.Expr.instantiateList key.1 (ws.take k) key.2

/-- The `dup e` return shared by the `k = 0` branch, the `bvarB ≤ d` cutoff and
the four atom arms of both bulk walks: the node is its own instantiation. -/
theorem instL_dup_ret {Q : ConLeche.Expr × Nat → expr.Expr → Prop}
    {e r : expr.Expr} {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    {ws : List ConLeche.Expr} {d : Std.U64}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey Q memo)
    (hself : ConLeche.Expr.instantiateList (absExpr e) ws d.val = absExpr e)
    (h : (do let c ← expr.dup e; ok (c, memo)) = ok (r, memo')) :
    (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiateList (absExpr e) ws d.val) ∧
      MemoInv KeyWF absKey Q memo' := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨c, hdup, hr, hmm⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr; subst hmm
  exact ⟨⟨hwfe, hself.symm⟩, hm⟩

/-- The `bvarB ≤ d` cutoff of the bulk walks: at or above the loose-`bvar`
bound there is nothing to replace. -/
theorem instL_cutoff_self {e : expr.Expr} {bb d : Std.U64} {ws : List ConLeche.Expr}
    (hwfe : ExprWF e) (hbb : expr_ops.bvar_b e = ok bb) (hle : bb.val ≤ d.val) :
    ConLeche.Expr.instantiateList (absExpr e) ws d.val = absExpr e := by
  have hbnd : ConLeche.Expr.looseBVarsBounded d.val (absExpr e) = true :=
    ConLeche.Expr.looseBVarsBounded_iff.mpr
      (by rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines hwfe hbb]; exact hle)
  exact ConLeche.Expr.instantiateList_eq_self hbnd

/-- The statement of `instantiate_list_go` at one fixed live prefix `K`: the
proposition the strong induction on the prefix runs over. -/
def GoLP (vs : alloc.vec.Vec expr.Expr) (K : Nat) : Prop :=
  ∀ (e : expr.Expr), ExprWF e →
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (k d : Std.U64) (r : expr.Expr),
      k.val = K → k.val ≤ vs.val.length →
      MemoInv KeyWF absKey (MemoLQ (absExprs vs) k.val) memo →
      cached.expr_ops_c.instantiate_list_go vs memo e k d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r
            = ConLeche.Expr.instantiateList (absExpr e) ((absExprs vs).take k.val) d.val) ∧
        MemoInv KeyWF absKey (MemoLQ (absExprs vs) k.val) memo'

/-- `instantiate_list_bvar` from the walk's lemma at the *shorter* prefix `j`. -/
theorem instantiate_list_bvar_aux {vs : alloc.vec.Vec expr.Expr} {j : Std.U64}
    (hgo : GoLP vs j.val) {e r w : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hj : vs.val[j.val]? = some w) (hwfw : ExprWF w)
    (h : cached.expr_ops_c.instantiate_list_bvar vs e j d = ok r) :
    absExpr r
        = ConLeche.Expr.instantiateList (absExpr w) ((absExprs vs).take j.val) d.val ∧
      ExprWF r := by
  have hjlt : j.val < vs.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj; simp at hj
  rw [cached.expr_ops_c.instantiate_list_bvar] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  have hiv : i.val = j.val := by
    rw [← Result.ok_injective hi,
      u64_cast_usize_val_of_lt (n := vs.val.length) (alloc.vec.Vec.property vs) hjlt]
  split at h
  · obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = j.val := by
      rw [← Result.ok_injective hi2,
        u64_cast_usize_val_of_lt (n := vs.val.length) (alloc.vec.Vec.property vs) hjlt]
    obtain ⟨w0, hidx, h⟩ := bind_eq_ok_iff.mp h
    have hw0 : w = w0 := by
      have hg := vec_index_getElem? hidx
      rw [hi2v, hj] at hg
      exact Option.some.inj hg
    subst hw0
    split at h
    · rename_i hz
      have hz' : j.val = 0 := by rw [hz]; scalar_tac
      rw [Expr.dup_eq h, hz']
      simp only [List.take_zero]
      exact ⟨(ConLeche.Expr.instantiateList_nil _ _).symm, hwfw⟩
    · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rename_i hle
        rw [Expr.dup_eq h]
        exact ⟨(instL_cutoff_self hwfw hbb (by scalar_tac)).symm, hwfw⟩
      · obtain ⟨fresh, hnew, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hgo2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r0, fresh'⟩ := p
        have hr : r0 = r := Result.ok_injective h
        subst hr
        obtain ⟨⟨hwf, habs⟩, -⟩ :=
          hgo w hwfw fresh fresh' j d r0 rfl (by omega) (new_memo_inv hnew) hgo2
        exact ⟨habs, hwf⟩
  · rename_i hlt
    exact absurd (show i < alloc.vec.Vec.len vs by
      have := alloc.vec.Vec.len_val vs; scalar_tac) hlt

/-- The two-level induction: strong on the live prefix, structural on the
`ExprWF` derivation inside it. -/
theorem instantiate_list_go_aux {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs) :
    ∀ K, GoLP vs K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
    intro e he
    induction he with
    | @bvar i e h1 =>
      have hwfe : ExprWF e := ExprWF.bvar h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]
        simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · have hlen : ((absExprs vs).take k.val).length = k.val := by
            rw [List.length_take, absExprs, List.length_map]; omega
          simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          split at h
          · rename_i hid
            have hid' : i.val < d.val := by scalar_tac
            refine instL_dup_ret hwfe hm ?_ h
            simp only [absExpr_mk, absExprKind]
            rw [ConLeche.Expr.instantiateList, if_pos hid']
          · rename_i hid
            have hid' : d.val ≤ i.val := by scalar_tac
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            have hi2v : i2.val = i.val - d.val := HashMap.uscalar_sub_eq hi2
            split at h
            · rename_i hik
              have hik' : i2.val < k.val := by scalar_tac
              obtain ⟨r0, hbv, h⟩ := bind_eq_ok_iff.mp h
              have e0 := Result.ok_injective (α := expr.Expr × _) h
              have e1 : r = r0 := (congrArg Prod.fst e0).symm
              have e2 : memo' = memo := (congrArg Prod.snd e0).symm
              subst e1; subst e2
              have hlt2 : i.val - d.val < vs.val.length := by omega
              have hget : vs.val[i2.val]? = some vs.val[i.val - d.val] := by
                rw [hi2v]; exact List.getElem?_eq_getElem hlt2
              obtain ⟨habs, hwf⟩ :=
                instantiate_list_bvar_aux (ihK i2.val (by omega)) hwfe hget
                  (hvs _ (List.getElem_mem hlt2)) hbv
              refine ⟨⟨hwf, ?_⟩, hm⟩
              rw [habs]
              have hidx : i.val - d.val < ((absExprs vs).take k.val).length := by
                rw [hlen]; omega
              have hgetl : ((absExprs vs).take k.val)[i.val - d.val]'hidx
                  = absExpr vs.val[i.val - d.val] := by
                rw [List.getElem_take]
                simp [absExprs]
              have htk : ((absExprs vs).take k.val).take (i.val - d.val)
                  = (absExprs vs).take i2.val := by
                rw [List.take_take, hi2v]
                congr 1
                omega
              simp only [absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList, if_neg (by omega), dif_pos hidx,
                hgetl, htk]
            · rename_i hik
              have hik' : ¬ (i2.val < k.val) := by scalar_tac
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              have hi3v : i3.val = i.val - k.val := HashMap.uscalar_sub_eq hi3
              obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
              have e0 := Result.ok_injective (α := expr.Expr × _) h
              have e1 : r = c := (congrArg Prod.fst e0).symm
              have e2 : memo' = memo := (congrArg Prod.snd e0).symm
              subst e1; subst e2
              refine ⟨⟨Expr.mk_bvar_wf hc, ?_⟩, hm⟩
              rw [Expr.mk_bvar_refines hc, ConLeche.Expr.mkBvar_eq, hi3v]
              simp only [absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList, if_neg (by omega),
                dif_neg (by rw [hlen]; omega), hlen]
    | @fvar idx ty e hty h1 ih =>
      have hwfe : ExprWF e := ExprWF.fvar hty h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @sort u e hu h1 =>
      have hwfe : ExprWF e := ExprWF.sort hu h1
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @mk_const n us e hn hus h1 =>
      have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @lit l e hl h1 =>
      have hwfe : ExprWF e := ExprWF.lit hl h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @app f a e hf ha h1 ihf iha =>
      have hwfe : ExprWF e := ExprWF.app hf ha h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs) k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, hf2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨f2, memo2⟩ := p1
            obtain ⟨p2, ha2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨a2, memo3⟩ := p2
            obtain ⟨r1, happ, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 k d f2 hK hk hm hf2
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 k d a2 hK hk hm2 ha2
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs) k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), d⟩) r := by
              refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
              rw [Expr.app_refines happ, habs2, habs3]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
    | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
      have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs) k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨t, memo2⟩ := p1
            obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨b, memo3⟩ := p2
            obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k d t hK hk hm ht
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 k dd b hK hk hm2 hb
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs) k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.Lam ty bo m)), d⟩) r := by
              refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
              rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
                HashMap.uscalar_add_eq hdd, Expr.val_one]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
    | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
      have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs) k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨t, memo2⟩ := p1
            obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨b, memo3⟩ := p2
            obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k d t hK hk hm ht
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 k dd b hK hk hm2 hb
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs) k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.ForallE ty bo m)), d⟩) r := by
              refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
              rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
                HashMap.uscalar_add_eq hdd, Expr.val_one]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
    | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo =>
      have hwfe : ExprWF e := ExprWF.let_e hty hvv hbo h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs) k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨t, memo2⟩ := p1
            obtain ⟨p2, hw2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨w2, memo3⟩ := p2
            obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨p4, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨b, memo5⟩ := p4
            obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo5 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k d t hK hk hm ht
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihvv memo2 memo3 k d w2 hK hk hm2 hw2
            obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 k dd b hK hk hm3 hb
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo6⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo6 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs) k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.LetE ty vv bo)), d⟩) r := by
              refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
              rw [Expr.let_e_refines hlet, habs2, habs3, habs4,
                HashMap.uscalar_add_eq hdd, Expr.val_one]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
    | @proj s i x e hs hx h1 ih =>
      have hwfe : ExprWF e := ExprWF.proj hs hx h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_list_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs) k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, hu, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨u, memo2⟩ := p1
            obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 k d u hK hk hm hu
            have hsn : s = n2 :=
              (Result.ok_injective (hn2.symm.trans (name_dup_eq s))).symm
            subst hsn
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs) k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.Proj s i x)), d⟩) r := by
              refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
              rw [Expr.proj_refines hproj, habs2]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins

/-! ### The three public statements of the forward walk -/

/-- **`expr_ops_c::instantiate_list_go` refines `Expr.instantiateList`** at the
live prefix (con-leche's `instantiateListGo`, `ExprOpsC.lean:279-360`). -/
theorem instantiate_list_go_refines {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (k d : Std.U64) (r : expr.Expr),
      k.val ≤ vs.val.length →
      MemoInv KeyWF absKey (MemoLQ (absExprs vs) k.val) memo →
      cached.expr_ops_c.instantiate_list_go vs memo e k d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r
            = ConLeche.Expr.instantiateList (absExpr e) ((absExprs vs).take k.val) d.val) ∧
        MemoInv KeyWF absKey (MemoLQ (absExprs vs) k.val) memo' := by
  intro memo memo' k d r hk hm h
  exact instantiate_list_go_aux hvs k.val e he memo memo' k d r rfl hk hm h

/-- **`expr_ops_c::instantiate_list_bvar` refines `Expr.instantiateList`** at a
`.bvar` the live prefix reaches: the replacement, guarded, re-entered under a
fresh table at the shorter prefix `j`. -/
theorem instantiate_list_bvar_refines {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs)
    {e r w : expr.Expr} {j d : Std.U64} (he : ExprWF e)
    (hj : vs.val[j.val]? = some w)
    (h : cached.expr_ops_c.instantiate_list_bvar vs e j d = ok r) :
    absExpr r
        = ConLeche.Expr.instantiateList (absExpr w) ((absExprs vs).take j.val) d.val ∧
      ExprWF r := by
  have hjlt : j.val < vs.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj; simp at hj
  have hwv : w = vs.val[j.val] := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact (Option.some.inj hj).symm
  exact instantiate_list_bvar_aux (instantiate_list_go_aux hvs j.val) he hj
    (by rw [hwv]; exact hvs _ (List.getElem_mem hjlt)) h

/-- **`expr_ops_c::instantiate_list` refines `Expr.instantiateListC`**
(`ExprOpsC.lean:362-368`): the empty-list shortcut, then one memoised DAG pass
at the full prefix. -/
theorem instantiate_list_refines {e r : expr.Expr} {vs : alloc.vec.Vec expr.Expr}
    {d : Std.U64} (he : ExprWF e) (hvs : ExprsWF vs)
    (h : cached.expr_ops_c.instantiate_list e vs d = ok r) :
    absExpr r
        = ConLeche.Expr.instantiateListC (absExpr e) (absExprs vs) d.val ∧
      ExprWF r := by
  rw [ConLeche.Expr.instantiateListC_spec]
  have hlenv := alloc.vec.Vec.len_val vs
  rw [cached.expr_ops_c.instantiate_list] at h
  dsimp only at h
  split at h
  · rename_i hz
    have hz' : vs.val.length = 0 := by scalar_tac
    have hnil : absExprs vs = [] := by
      have hl : (absExprs vs).length = 0 := by
        rw [absExprs, List.length_map]; exact hz'
      simpa using hl
    rw [Expr.dup_eq h, hnil, ConLeche.Expr.instantiateList_nil]
    exact ⟨rfl, he⟩
  · obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r0, memo'⟩ := p
    have hr : r0 = r := Result.ok_injective h
    subst hr
    have hi2v : i2.val = vs.val.length := by
      rw [← Result.ok_injective hi2, usize_cast_u64_val, hlenv]
    have hall : (absExprs vs).take i2.val = absExprs vs := by
      rw [hi2v, absExprs]; simp
    obtain ⟨⟨hwf, habs⟩, -⟩ :=
      instantiate_list_go_aux hvs i2.val e he memo memo' i2 d r0 rfl (by omega)
        (new_memo_inv hnew) hgo
    exact ⟨by rw [habs, hall], hwf⟩

/-- The statement of `instantiate_list_go` at one fixed live prefix `K`: the
proposition the strong induction on the prefix runs over. -/
def GoRP (vs : alloc.vec.Vec expr.Expr) (K : Nat) : Prop :=
  ∀ (e : expr.Expr), ExprWF e →
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (k d : Std.U64) (r : expr.Expr),
      k.val = K → k.val ≤ vs.val.length →
      MemoInv KeyWF absKey (MemoLQ (absExprs vs).reverse k.val) memo →
      cached.expr_ops_c.instantiate_rev_go vs memo e k d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r
            = ConLeche.Expr.instantiateList (absExpr e) ((absExprs vs).reverse.take k.val) d.val) ∧
        MemoInv KeyWF absKey (MemoLQ (absExprs vs).reverse k.val) memo'

/-- `instantiate_rev_bvar` from the walk's lemma at the shorter prefix `j`: the
replacement is read from the *end* of the array. -/
theorem instantiate_rev_bvar_aux {vs : alloc.vec.Vec expr.Expr} {j : Std.U64}
    (hgo : GoRP vs j.val) {e r w : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hjlt : j.val < vs.val.length)
    (hj : vs.val[vs.val.length - 1 - j.val]? = some w) (hwfw : ExprWF w)
    (h : cached.expr_ops_c.instantiate_rev_bvar vs e j d = ok r) :
    absExpr r
        = ConLeche.Expr.instantiateList (absExpr w)
            ((absExprs vs).reverse.take j.val) d.val ∧
      ExprWF r := by
  have hlenv := alloc.vec.Vec.len_val vs
  rw [cached.expr_ops_c.instantiate_rev_bvar] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  have hiv : i.val = j.val := by
    rw [← Result.ok_injective hi,
      u64_cast_usize_val_of_lt (n := vs.val.length) (alloc.vec.Vec.property vs) hjlt]
  split at h
  · obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    have hi3v : i3.val = vs.val.length - 1 := by
      rw [HashMap.uscalar_sub_eq hi3, hlenv]; scalar_tac
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
    have hi4v : i4.val = j.val := by
      rw [← Result.ok_injective hi4,
        u64_cast_usize_val_of_lt (n := vs.val.length) (alloc.vec.Vec.property vs) hjlt]
    obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
    have hi5v : i5.val = vs.val.length - 1 - j.val := by
      rw [HashMap.uscalar_sub_eq hi5, hi3v, hi4v]
    obtain ⟨w0, hidx, h⟩ := bind_eq_ok_iff.mp h
    have hw0 : w = w0 := by
      have hg := vec_index_getElem? hidx
      rw [hi5v, hj] at hg
      exact Option.some.inj hg
    subst hw0
    split at h
    · rename_i hz
      have hz' : j.val = 0 := by rw [hz]; scalar_tac
      rw [Expr.dup_eq h, hz']
      simp only [List.take_zero]
      exact ⟨(ConLeche.Expr.instantiateList_nil _ _).symm, hwfw⟩
    · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · rename_i hle
        rw [Expr.dup_eq h]
        exact ⟨(instL_cutoff_self hwfw hbb (by scalar_tac)).symm, hwfw⟩
      · obtain ⟨fresh, hnew, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hgo2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r0, fresh'⟩ := p
        have hr : r0 = r := Result.ok_injective h
        subst hr
        obtain ⟨⟨hwf, habs⟩, -⟩ :=
          hgo w hwfw fresh fresh' j d r0 rfl (by omega) (new_memo_inv hnew) hgo2
        exact ⟨habs, hwf⟩
  · rename_i hlt
    exact absurd (show i < alloc.vec.Vec.len vs by scalar_tac) hlt

/-- `instantiate_list_go_aux`'s twin on the reversed array. -/
theorem instantiate_rev_go_aux {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs) :
    ∀ K, GoRP vs K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
    intro e he
    induction he with
    | @bvar i e h1 =>
      have hwfe : ExprWF e := ExprWF.bvar h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]
        simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · have hlen : ((absExprs vs).reverse.take k.val).length = k.val := by
            rw [List.length_take, List.length_reverse, absExprs, List.length_map]; omega
          simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          split at h
          · rename_i hid
            have hid' : i.val < d.val := by scalar_tac
            refine instL_dup_ret hwfe hm ?_ h
            simp only [absExpr_mk, absExprKind]
            rw [ConLeche.Expr.instantiateList, if_pos hid']
          · rename_i hid
            have hid' : d.val ≤ i.val := by scalar_tac
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            have hi2v : i2.val = i.val - d.val := HashMap.uscalar_sub_eq hi2
            split at h
            · rename_i hik
              have hik' : i2.val < k.val := by scalar_tac
              obtain ⟨r0, hbv, h⟩ := bind_eq_ok_iff.mp h
              have e0 := Result.ok_injective (α := expr.Expr × _) h
              have e1 : r = r0 := (congrArg Prod.fst e0).symm
              have e2 : memo' = memo := (congrArg Prod.snd e0).symm
              subst e1; subst e2
              have hlt2 : vs.val.length - 1 - (i.val - d.val) < vs.val.length := by omega
              have hget : vs.val[vs.val.length - 1 - i2.val]?
                  = some vs.val[vs.val.length - 1 - (i.val - d.val)] := by
                rw [hi2v]; exact List.getElem?_eq_getElem hlt2
              obtain ⟨habs, hwf⟩ :=
                instantiate_rev_bvar_aux (ihK i2.val (by omega)) hwfe (by omega) hget
                  (hvs _ (List.getElem_mem hlt2)) hbv
              refine ⟨⟨hwf, ?_⟩, hm⟩
              rw [habs]
              have hidx : i.val - d.val < ((absExprs vs).reverse.take k.val).length := by
                rw [hlen]; omega
              have hgetl : ((absExprs vs).reverse.take k.val)[i.val - d.val]'hidx
                  = absExpr vs.val[vs.val.length - 1 - (i.val - d.val)] := by
                rw [List.getElem_take, List.getElem_reverse]
                simp [absExprs]
              have htk : ((absExprs vs).reverse.take k.val).take (i.val - d.val)
                  = (absExprs vs).reverse.take i2.val := by
                rw [List.take_take, hi2v]
                congr 1
                omega
              simp only [absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList, if_neg (by omega), dif_pos hidx,
                hgetl, htk]
            · rename_i hik
              have hik' : ¬ (i2.val < k.val) := by scalar_tac
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              have hi3v : i3.val = i.val - k.val := HashMap.uscalar_sub_eq hi3
              obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
              have e0 := Result.ok_injective (α := expr.Expr × _) h
              have e1 : r = c := (congrArg Prod.fst e0).symm
              have e2 : memo' = memo := (congrArg Prod.snd e0).symm
              subst e1; subst e2
              refine ⟨⟨Expr.mk_bvar_wf hc, ?_⟩, hm⟩
              rw [Expr.mk_bvar_refines hc, ConLeche.Expr.mkBvar_eq, hi3v]
              simp only [absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList, if_neg (by omega),
                dif_neg (by rw [hlen]; omega), hlen]
    | @fvar idx ty e hty h1 ih =>
      have hwfe : ExprWF e := ExprWF.fvar hty h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @sort u e hu h1 =>
      have hwfe : ExprWF e := ExprWF.sort hu h1
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @mk_const n us e hn hus h1 =>
      have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @lit l e hl h1 =>
      have hwfe : ExprWF e := ExprWF.lit hl h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          refine instL_dup_ret hwfe hm ?_ h
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList]
    | @app f a e hf ha h1 ihf iha =>
      have hwfe : ExprWF e := ExprWF.app hf ha h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs).reverse k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, hf2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨f2, memo2⟩ := p1
            obtain ⟨p2, ha2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨a2, memo3⟩ := p2
            obtain ⟨r1, happ, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 k d f2 hK hk hm hf2
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 k d a2 hK hk hm2 ha2
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs).reverse k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), d⟩) r := by
              refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
              rw [Expr.app_refines happ, habs2, habs3]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
    | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
      have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs).reverse k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨t, memo2⟩ := p1
            obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨b, memo3⟩ := p2
            obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k d t hK hk hm ht
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 k dd b hK hk hm2 hb
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs).reverse k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.Lam ty bo m)), d⟩) r := by
              refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
              rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
                HashMap.uscalar_add_eq hdd, Expr.val_one]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
    | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
      have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs).reverse k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨t, memo2⟩ := p1
            obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨b, memo3⟩ := p2
            obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k d t hK hk hm ht
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 k dd b hK hk hm2 hb
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs).reverse k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.ForallE ty bo m)), d⟩) r := by
              refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
              rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
                HashMap.uscalar_add_eq hdd, Expr.val_one]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
    | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo =>
      have hwfe : ExprWF e := ExprWF.let_e hty hvv hbo h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs).reverse k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨t, memo2⟩ := p1
            obtain ⟨p2, hw2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨w2, memo3⟩ := p2
            obtain ⟨dd, hdd, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨p4, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨b, memo5⟩ := p4
            obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo5 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k d t hK hk hm ht
            obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihvv memo2 memo3 k d w2 hK hk hm2 hw2
            obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 k dd b hK hk hm3 hb
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo6⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo6 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs).reverse k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.LetE ty vv bo)), d⟩) r := by
              refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
              rw [Expr.let_e_refines hlet, habs2, habs3, habs4,
                HashMap.uscalar_add_eq hdd, Expr.val_one]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
    | @proj s i x e hs hx h1 ih =>
      have hwfe : ExprWF e := ExprWF.proj hs hx h1
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
      intro memo memo' k d r hK hk hm h
      rw [cached.expr_ops_c.instantiate_rev_go.eq_def] at h
      split at h
      · rename_i hk0
        have hk0v : k.val = 0 := by rw [hk0]; scalar_tac
        refine instL_dup_ret hwfe hm ?_ h
        rw [hk0v]; simp only [List.take_zero]
        exact ConLeche.Expr.instantiateList_nil _ _
      · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · exact instL_dup_ret hwfe hm (instL_cutoff_self hwfe hbb (by scalar_tac)) h
        · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
          obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
          have hkk := expr_nat_key_eq hkey
          subst hkk
          cases o with
          | some w =>
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1 : r = w := (congrArg Prod.fst e0).symm
            have e2 : memo' = memo := (congrArg Prod.snd e0).symm
            subst e1; subst e2
            exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey)
              (Q := MemoLQ (absExprs vs).reverse k.val) key_exact hm (keyWF_mk hwfe)
              (memo1_get_hit ho), hm⟩
          | none =>
            obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨memo1, r0⟩ := q
            obtain ⟨p1, hu, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨u, memo2⟩ := p1
            obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
            obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
            have eg := Result.ok_injective
              (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
            have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
            have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
            subst eg1; subst eg2
            obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 k d u hK hk hm hu
            have hsn : s = n2 :=
              (Result.ok_injective (hn2.symm.trans (name_dup_eq s))).symm
            subst hsn
            obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨oldv, memo4⟩ := p3
            have e0 := Result.ok_injective (α := expr.Expr × _) h
            have e1' : r = r0 := (congrArg Prod.fst e0).symm
            have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
            subst e1'; subst e2'
            have hans : MemoLQ (absExprs vs).reverse k.val
                (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1
                  (expr.ExprKind.Proj s i x)), d⟩) r := by
              refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
              rw [Expr.proj_refines hproj, habs2]
              simp only [absKey_mk, absExpr_mk, absExprKind]
              rw [ConLeche.Expr.instantiateList]
            refine ⟨hans, ?_⟩
            rw [Expr.dup_eq hdup] at hins
            exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins

/-! ### The three public statements of the reversed walk -/

/-- **`expr_ops_c::instantiate_rev_go` refines `Expr.instantiateList`** on the
*reversed* replacement array (con-leche's `instantiateRevGo`,
`ExprOpsC.lean:370-439`; `instantiateRevGo_eq` is the pointwise equation with
the forward walk). -/
theorem instantiate_rev_go_refines {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (k d : Std.U64) (r : expr.Expr),
      k.val ≤ vs.val.length →
      MemoInv KeyWF absKey (MemoLQ (absExprs vs).reverse k.val) memo →
      cached.expr_ops_c.instantiate_rev_go vs memo e k d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r
            = ConLeche.Expr.instantiateList (absExpr e)
                (((absExprs vs).reverse).take k.val) d.val) ∧
        MemoInv KeyWF absKey (MemoLQ (absExprs vs).reverse k.val) memo' := by
  intro memo memo' k d r hk hm h
  exact instantiate_rev_go_aux hvs k.val e he memo memo' k d r rfl hk hm h

/-- **`expr_ops_c::instantiate_rev_bvar` refines `Expr.instantiateList`** at a
`.bvar`, reading the replacement from the *end* of the array.  `j.val <
vs.val.length` is a hypothesis and not a consequence of `hj`: `Nat` subtraction
saturates, so `vs.val[vs.val.length - 1 - j.val]?` says nothing about `j` once
`j` runs past the end (task #54). -/
theorem instantiate_rev_bvar_refines {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs)
    {e r w : expr.Expr} {j d : Std.U64} (he : ExprWF e)
    (hjlt : j.val < vs.val.length)
    (hj : vs.val[vs.val.length - 1 - j.val]? = some w)
    (h : cached.expr_ops_c.instantiate_rev_bvar vs e j d = ok r) :
    absExpr r
        = ConLeche.Expr.instantiateList (absExpr w)
            (((absExprs vs).reverse).take j.val) d.val ∧
      ExprWF r := by
  have hilt : vs.val.length - 1 - j.val < vs.val.length := by omega
  have hwv : w = vs.val[vs.val.length - 1 - j.val] := by
    rw [List.getElem?_eq_getElem hilt] at hj
    exact (Option.some.inj hj).symm
  exact instantiate_rev_bvar_aux (instantiate_rev_go_aux hvs j.val) he hjlt hj
    (by rw [hwv]; exact hvs _ (List.getElem_mem hilt)) h

/-- **`expr_ops_c::instantiate_rev` refines `Expr.instantiateRev`**
(`ExprOpsC.lean:441-445`); `instantiateRev_spec` reads the cited definition as
`Expr.instantiateList` on the reversed list. -/
theorem instantiate_rev_refines {e r : expr.Expr} {vs : alloc.vec.Vec expr.Expr}
    {d : Std.U64} (he : ExprWF e) (hvs : ExprsWF vs)
    (h : cached.expr_ops_c.instantiate_rev e vs d = ok r) :
    absExpr r
        = ConLeche.Expr.instantiateList (absExpr e) (absExprs vs).reverse d.val ∧
      ExprWF r := by
  have hlenv := alloc.vec.Vec.len_val vs
  rw [cached.expr_ops_c.instantiate_rev] at h
  dsimp only at h
  split at h
  · rename_i hz
    have hz' : vs.val.length = 0 := by scalar_tac
    have hnil : absExprs vs = [] := by
      have hl : (absExprs vs).length = 0 := by
        rw [absExprs, List.length_map]; exact hz'
      simpa using hl
    rw [Expr.dup_eq h, hnil]
    simp only [List.reverse_nil]
    exact ⟨(ConLeche.Expr.instantiateList_nil _ _).symm, he⟩
  · obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rw [Expr.dup_eq h]
      exact ⟨(instL_cutoff_self he hbb (by scalar_tac)).symm, he⟩
    · obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, memo'⟩ := p
      have hr : r0 = r := Result.ok_injective h
      subst hr
      have hi3v : i3.val = vs.val.length := by
        rw [← Result.ok_injective hi3, usize_cast_u64_val, hlenv]
      have hall : (absExprs vs).reverse.take i3.val = (absExprs vs).reverse := by
        rw [hi3v, absExprs]; simp
      obtain ⟨⟨hwf, habs⟩, -⟩ :=
        instantiate_rev_go_aux hvs i3.val e he memo memo' i3 d r0 rfl (by omega)
          (new_memo_inv hnew) hgo
      exact ⟨by rw [habs, hall], hwf⟩

end ConRon.Refine.ExprOpsC
