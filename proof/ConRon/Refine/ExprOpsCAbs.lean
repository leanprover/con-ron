/-
The abstraction and level-instantiation half of
`crates/con-ron-core/src/cached/expr_ops_c.rs` (task #26), refined against
`ConLeche/Cached/ExprOpsC.lean` (task #51; the module note is in
`ConRon/Refine/ExprOpsC.lean`).

`abstract1`, `abstractRange`, `instLevelParams` and `ProjEntry.typeAtI`.  All
three walks sit behind a derived-field cutoff -- `fvarB ≤ d` for the two
abstractions (a node whose fvar range is at or below `d` cannot contain
`fvar d`), `!hasLP` for the level substitution -- and all three memoise, but
with *different policies*: the abstractions record only the five compound
kinds, `instLevelParamsGo` records **every** node kind, because its probe sits
before the match rather than inside the arms.  §3.1 makes both binding, and
task #47's `MemoInv` is policy-agnostic, so the same `hit`/`set` pair serves
both; what changes is where in the generated body the probe is inverted.
-/
import ConRon.Refine.ExprOpsCSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOpsC

open ConRon.Refine.ExprOps

/-! ## `abstract1` (`ExprOpsC.lean:449-512`)

`expr_ops::abstract1_go` node for node -- the cited cutoff is the same, the memo
is the same, and the two arms that differ (`.bvar`, which the port answers with
`expr::dup` instead of rebuilding, and `.fvar` at `d`, which goes through
`expr::mk_bvar`) are the same *value*.  So the `Q` is task #47's `Abs1Q` and
its `abstract1_cutoff` is reused verbatim. -/

/-- **`expr_ops_c::abstract1_go` refines `Expr.abstract1`** (con-leche's
`abstract1Go`, `ExprOpsC.lean:449-508`, soundness `abstract1Go_spec`,
`Verify/Cached/OpsC.lean:911`). -/
theorem abstract1_go_refines {d : Std.U64} {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (k : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (Abs1Q d.val) memo →
      cached.expr_ops_c.abstract1_go d memo e k = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.abstract1 (absExpr e) d.val k.val) ∧
        MemoInv KeyWF absKey (Abs1Q d.val) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hx, hr, hmm⟩ := h
      rw [Expr.dup_eq hx] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      split at h
      · rename_i hid
        have hid2 : idx.val = d.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, hx, hr, hmm⟩ := h
        subst hr; subst hmm
        refine ⟨⟨Expr.mk_bvar_wf hx, ?_⟩, hm⟩
        rw [Expr.mk_bvar_refines hx, ConLeche.Expr.mkBvar_eq]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstract1]
        rw [if_pos hid2]
      · rename_i hid
        have hid2 : idx.val ≠ d.val := fun hc => hid (Std.UScalar.eq_of_val_eq hc)
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, hdup, hr, hmm⟩ := h
        rw [Expr.dup_eq hdup] at hr
        subst hr; subst hmm
        refine ⟨⟨hwfe, ?_⟩, hm⟩
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstract1]
        rw [if_neg hid2]
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Abs1Q d.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 k f2 hm hgf
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 k a2 hm2 hga
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Abs1Q d.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), k⟩) r := by
          refine ⟨Expr.app_wf hwf2 hwf3 hbuild, ?_⟩
          rw [Expr.app_refines hbuild, habs2, habs3]
          simp [ConLeche.Expr.abstract1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Abs1Q d.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Abs1Q d.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), k⟩) r := by
          refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.lam_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.abstract1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Abs1Q d.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Abs1Q d.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), k⟩) r := by
          refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.forall_e_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.abstract1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Abs1Q d.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 k t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 k w3 hm2 hgv
        obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 cc b hm3 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : Abs1Q d.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), k⟩) r := by
          refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hbuild, ?_⟩
          rw [Expr.let_e_refines hbuild, habs2, habs3, habs4,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.abstract1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' k r hm h
    rw [cached.expr_ops_c.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := Abs1Q d.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 k uu hm hgs
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
        have hans : Abs1Q d.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)), k⟩) r := by
          refine ⟨Expr.proj_wf hs hwf2 hbuild, ?_⟩
          rw [Expr.proj_refines hbuild, habs2]
          simp [ConLeche.Expr.abstract1]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins



/-- **`expr_ops_c::abstract1` refines `ExprC.abstract1`**
(`ExprOpsC.lean:510-512`): the `fvar_b` cutoff, then the walk under a fresh
table.  `abstract1_spec` (`Verify/Cached/OpsC.lean:1059`) is the same split on
the Lean side. -/
theorem abstract1_refines {e r : expr.Expr} {d k : Std.U64} (he : ExprWF e)
    (h : cached.expr_ops_c.abstract1 e d k = ok r) :
    absExpr r = ConLeche.Cached.ExprC.abstract1 (absExpr e) d.val k.val ∧ ExprWF r := by
  rw [ConLeche.Cached.ExprC.abstract1_spec]
  rw [cached.expr_ops_c.abstract1] at h
  obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · rename_i hle
    have hfr : (absExpr e).fvarRange ≤ d.val := by
      rw [← ConLeche.Expr.fvarB_eq, ← fvar_b_refines he hfb]; scalar_tac
    rw [Expr.dup_eq h, ConLeche.Expr.abstract1_of_fvarRange_le _ _ _ hfr]
    exact ⟨rfl, he⟩
  · obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r0, memo'⟩ := p
    have hr : r0 = r := Result.ok_injective h
    subst hr
    obtain ⟨⟨hwf, habs⟩, -⟩ :=
      abstract1_go_refines he memo memo' k r0 (new_memo_inv hnew) hgo
    exact ⟨habs, hwf⟩

/-! ## `abstractRange` (`ExprOpsC.lean:514-574`)

The bulk abstraction: close the block `fvar d … fvar (d + k - 1)` in one pass,
outermost first.  Unlike `expr_ops::abstract_range` (task #47's unmemoised
walk) this one is **memoised** at the binder cursor and carries the `fvarB`
cutoff, which is the cited shape; so it needs its own `Q` and its own cutoff
lemma, off `Expr.abstractRange_eq_self` through con-leche's `ExprC.fvarB_le`. -/

/-- con-leche's `MemoARInv` (`Verify/Cached/OpsC.lean:1076`), as the `Q` of
`MemoInv`: every recorded answer is the real one, and it is well formed. -/
def AbsRQ (d k : Nat) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun key r => ExprWF r ∧ absExpr r = ConLeche.Expr.abstractRange key.1 d k key.2

/-- The cutoff branch of `abstract_range_go`, shared by all ten constructors: a
node whose fvar range is at or below `d` contains none of the abstracted block,
so the walk returns it unchanged (`Expr.abstractRange_eq_self` through
`ExprC.fvarB_le`). -/
theorem abstract_range_cutoff {d k c fb : Std.U64} {e r : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey (AbsRQ d.val k.val) memo)
    (hfb : expr_ops.fvar_b e = ok fb) (hle : fb.val ≤ d.val)
    (h : (do let x ← expr.dup e; ok (x, memo)) = ok (r, memo')) :
    (ExprWF r ∧
        absExpr r = ConLeche.Expr.abstractRange (absExpr e) d.val k.val c.val) ∧
      MemoInv KeyWF absKey (AbsRQ d.val k.val) memo' := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨x, hdup, hr, hmm⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr; subst hmm
  refine ⟨⟨hwfe, ?_⟩, hm⟩
  have hbelow : ConLeche.Expr.fvarsBelow d.val (absExpr e) :=
    ConLeche.Cached.ExprC.fvarB_le
      (by rw [← fvar_b_refines hwfe hfb]; exact hle)
  rw [ConLeche.abstractRange_eq_self hbelow]

/-- **`expr_ops_c::abstract_range_go` refines `Expr.abstractRange`** (con-leche's
`abstractRangeGo`, `ExprOpsC.lean:514-567`, soundness `abstractRangeGo_spec`,
`Verify/Cached/OpsC.lean:1099`). -/
theorem abstract_range_go_refines {d k : Std.U64} {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (c : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (AbsRQ d.val k.val) memo →
      cached.expr_ops_c.abstract_range_go d k memo e c = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.abstractRange (absExpr e) d.val k.val c.val) ∧
        MemoInv KeyWF absKey (AbsRQ d.val k.val) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hx, hr, hmm⟩ := h
      rw [Expr.dup_eq hx] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstractRange]⟩, hm⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      split at h
      · rename_i hle
        have hle' : d.val ≤ idx.val := by scalar_tac
        obtain ⟨i0, hi0, h⟩ := bind_eq_ok_iff.mp h
        have hi0v : i0.val = d.val + k.val := HashMap.uscalar_add_eq hi0
        split at h
        · rename_i hlt
          have hlt' : idx.val < d.val + k.val := by rw [← hi0v]; scalar_tac
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨i1, hi1, i2, hi2, i3, hi3, x, hx, hr, hmm⟩ := h
          subst hr; subst hmm
          have h1v : i1.val = i0.val - 1 := by
            rw [HashMap.uscalar_sub_eq hi1, Expr.val_one]
          have h2v : i2.val = i1.val - idx.val := HashMap.uscalar_sub_eq hi2
          have h3v : i3.val = c.val + i2.val := HashMap.uscalar_add_eq hi3
          refine ⟨⟨Expr.mk_bvar_wf hx, ?_⟩, hm⟩
          rw [Expr.mk_bvar_refines hx, ConLeche.Expr.mkBvar_eq]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstractRange,
            if_pos (show d.val ≤ idx.val ∧ idx.val < d.val + k.val from ⟨hle', hlt'⟩)]
          congr 1
          omega
        · rename_i hlt
          have hlt' : ¬ (idx.val < d.val + k.val) := by rw [← hi0v]; scalar_tac
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨x, hdup, hr, hmm⟩ := h
          rw [Expr.dup_eq hdup] at hr
          subst hr; subst hmm
          refine ⟨⟨hwfe, ?_⟩, hm⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstractRange,
            if_neg (show ¬ (d.val ≤ idx.val ∧ idx.val < d.val + k.val) from
              fun hc => hlt' hc.2)]
      · rename_i hle
        have hle' : ¬ (d.val ≤ idx.val) := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, hdup, hr, hmm⟩ := h
        rw [Expr.dup_eq hdup] at hr
        subst hr; subst hmm
        refine ⟨⟨hwfe, ?_⟩, hm⟩
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstractRange,
          if_neg (show ¬ (d.val ≤ idx.val ∧ idx.val < d.val + k.val) from
            fun hc => hle' hc.1)]
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstractRange]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstractRange]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstractRange]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := AbsRQ d.val k.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 c f2 hm hgf
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 c a2 hm2 hga
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : AbsRQ d.val k.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), c⟩) r := by
          refine ⟨Expr.app_wf hwf2 hwf3 hbuild, ?_⟩
          rw [Expr.app_refines hbuild, habs2, habs3]
          simp [ConLeche.Expr.abstractRange]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := AbsRQ d.val k.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 c t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : AbsRQ d.val k.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), c⟩) r := by
          refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.lam_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.abstractRange]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := AbsRQ d.val k.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 c t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : AbsRQ d.val k.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), c⟩) r := by
          refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.forall_e_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.abstractRange]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := AbsRQ d.val k.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 c t hm hgt
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 c w3 hm2 hgv
        obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 cc b hm3 hgb
        obtain ⟨x1, hdup, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e0).symm
        have em : memo' = memoZ := (congrArg Prod.snd e0).symm
        subst er; subst em
        have hans : AbsRQ d.val k.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), c⟩) r := by
          refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hbuild, ?_⟩
          rw [Expr.let_e_refines hbuild, habs2, habs3, habs4,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.abstractRange]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' c r hm h
    rw [cached.expr_ops_c.abstract_range_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract_range_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := AbsRQ d.val k.val)
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
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 c uu hm hgs
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
        have hans : AbsRQ d.val k.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)), c⟩) r := by
          refine ⟨Expr.proj_wf hs hwf2 hbuild, ?_⟩
          rw [Expr.proj_refines hbuild, habs2]
          simp [ConLeche.Expr.abstractRange]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins



/-- **`expr_ops_c::abstract_range` refines `ExprC.abstractRange`**
(`ExprOpsC.lean:569-574`): `k = 0` is the identity and skips the traversal, then
the `fvar_b` cutoff, then the walk under a fresh table. -/
theorem abstract_range_refines {e r : expr.Expr} {d k c : Std.U64} (he : ExprWF e)
    (h : cached.expr_ops_c.abstract_range e d k c = ok r) :
    absExpr r = ConLeche.Cached.ExprC.abstractRange (absExpr e) d.val k.val c.val ∧
      ExprWF r := by
  rw [cached.expr_ops_c.abstract_range] at h
  split at h
  · -- `k = 0`: the cited definition's own first clause
    rename_i hk0
    have hk0' : k.val = 0 := by rw [hk0]; scalar_tac
    rw [Expr.dup_eq h, hk0']
    refine ⟨?_, he⟩
    rw [ConLeche.Cached.ExprC.abstractRange]
  · rw [ConLeche.Cached.ExprC.abstractRange_spec]
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hle
      have hbelow : ConLeche.Expr.fvarsBelow d.val (absExpr e) :=
        ConLeche.Cached.ExprC.fvarB_le
          (by rw [← fvar_b_refines he hfb]; scalar_tac)
      rw [Expr.dup_eq h, ConLeche.abstractRange_eq_self hbelow]
      exact ⟨rfl, he⟩
    · obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, memo'⟩ := p
      have hr : r0 = r := Result.ok_injective h
      subst hr
      obtain ⟨⟨hwf, habs⟩, -⟩ :=
        abstract_range_go_refines he memo memo' c r0 (new_memo_inv hnew) hgo
      exact ⟨habs, hwf⟩

/-! ## `instantiateLevelParams` (`ExprOpsC.lean:581-621`)

The *one* walk of this module whose probe sits **before** the match, so that
every node kind gets an entry -- an atom is recorded here where
`instantiate1Go` would answer it on the spot.  The cited header's
memo-discipline section makes that binding and §3.1 forbids changing it, so the
proof inverts the probe first and the node's arm second, which is the mirror
image of task #47's `instantiate_level_params_go_refines`.  The `Q` and the
cutoff are task #47's (`ILPQ`, `ilp_cutoff`): the *value* is the same
substitution. -/

/-- **`expr_ops_c::inst_level_params_go` refines
`Expr.instantiateLevelParams`** (con-leche's `instLevelParamsGo`,
`ExprOpsC.lean:581-617`, soundness `instLevelParamsGo_spec`,
`Verify/Cached/OpsC.lean:1290`). -/
theorem inst_level_params_go_refines {ks : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr) (r : expr.Expr),
      MemoInv ExprWF absExpr (ILPQ (absNames ks) (absLevels us)) memo →
      cached.expr_ops_c.inst_level_params_go ks us memo e = ok (r, memo') →
      (ExprWF r ∧
          absExpr r = (absExpr e).instantiateLevelParams (absNames ks) (absLevels us)) ∧
        MemoInv ExprWF absExpr (ILPQ (absNames ks) (absLevels us)) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hgo
        obtain ⟨c0, hc0, hmm1, hr0⟩ := hgo
        subst hmm1
        obtain ⟨x1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨x2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e1 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e1).symm
        have em : memo' = memoZ := (congrArg Prod.snd e1).symm
        subst er; subst em
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)))) r := by
          rw [← hr0, Expr.dup_eq hc0]
          exact ⟨hwfe, by simp [ConLeche.Expr.instantiateLevelParams]⟩
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm hwfe hans hins
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hgo
        obtain ⟨c0, hc0, hmm1, hr0⟩ := hgo
        subst hmm1
        obtain ⟨x1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨x2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e1 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e1).symm
        have em : memo' = memoZ := (congrArg Prod.snd e1).symm
        subst er; subst em
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)))) r := by
          rw [← hr0, Expr.dup_eq hc0]
          exact ⟨hwfe, by simp [ConLeche.Expr.instantiateLevelParams]⟩
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm hwfe hans hins
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hgo
        obtain ⟨l0, hl0, c0, hc0, hmm1, hr0⟩ := hgo
        subst hmm1
        obtain ⟨habsl, hwfl⟩ := Level.subst_refines hu hks hus hl0
        obtain ⟨x1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨x2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e1 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e1).symm
        have em : memo' = memoZ := (congrArg Prod.snd e1).symm
        subst er; subst em
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.«Sort» u)))) r := by
          rw [← hr0]
          refine ⟨Expr.sort_wf hwfl hc0, ?_⟩
          rw [Expr.sort_refines hc0, habsl]
          unfold absNames absLevels
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm hwfe hans hins
  | @mk_const n vs e hn hvs h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hvs h1
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = w := (congrArg Prod.fst e0).symm
        have em : memo' = memo := (congrArg Prod.snd e0).symm
        subst er; subst em
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        simp only [bind_eq_ok_iff, name_dup_eq, bind_tc_ok, Result.ok.injEq,
          Prod.mk.injEq] at hgo
        obtain ⟨v0, hv0, c0, hc0, hmm1, hr0⟩ := hgo
        subst hmm1
        obtain ⟨habsv, hwfv⟩ := levels_subst_refines hks hus hvs hv0
        obtain ⟨x1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨x2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e1 := Result.ok_injective (α := expr.Expr × _) h
        have er : r = r0 := (congrArg Prod.fst e1).symm
        have em : memo' = memoZ := (congrArg Prod.snd e1).symm
        subst er; subst em
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n vs)))) r := by
          rw [← hr0]
          refine ⟨Expr.mk_const_wf hn hwfv hc0, ?_⟩
          rw [Expr.mk_const_refines hc0, habsv]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm hwfe hans hins
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨r1, hfv, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
        have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 t hm ht
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo3⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo3 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) r := by
          refine ⟨Expr.fvar_wf hwf2 hfv, ?_⟩
          rw [Expr.fvar_refines hfv, habs2]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm2 hwfe hans hins
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hf2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨f2, memo2⟩ := p1
        obtain ⟨p2, ha2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨a2, memo3⟩ := p2
        obtain ⟨r1, happ, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 f2 hm hf2
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 a2 hm2 ha2
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) r := by
          refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
          rw [Expr.app_refines happ, habs2, habs3]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hbb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b1, memo3⟩ := p2
        obtain ⟨pw, hpw, hgo⟩ := bind_eq_ok_iff.mp hgo
        -- task #38: the binder datum goes through `expr::binder_meta`.
        simp only [binder_meta_eq, bind_tc_ok] at hgo
        obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 b1 hm2 hbb
        obtain ⟨habspw, hwfpw⟩ := subst_pw_refines hks hus hm0 hpw
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r := by
          refine ⟨Expr.lam_wf hwf2 hwf3 hwfpw hlam, ?_⟩
          rw [Expr.lam_refines hlam, habs2, habs3, absBinderMeta, habspw]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hbb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b1, memo3⟩ := p2
        obtain ⟨pw, hpw, hgo⟩ := bind_eq_ok_iff.mp hgo
        -- task #38: the binder datum goes through `expr::binder_meta`.
        simp only [binder_meta_eq, bind_tc_ok] at hgo
        obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
        have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 b1 hm2 hbb
        obtain ⟨habspw, hwfpw⟩ := subst_pw_refines hks hus hm0 hpw
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo4⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r := by
          refine ⟨Expr.forall_e_wf hwf2 hwf3 hwfpw hfa, ?_⟩
          rw [Expr.forall_e_refines hfa, habs2, habs3, absBinderMeta, habspw]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w' =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w' := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hv2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨w2, memo3⟩ := p2
        obtain ⟨p3, hbb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b1, memo4⟩ := p3
        obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
        have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
        obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 w2 hm2 hv2
        obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 b1 hm3 hbb
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p4, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo5⟩ := p4
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo5 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)))) r := by
          refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
          rw [Expr.let_e_refines hlet, habs2, habs3, habs4]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm4 hwfe hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' r hm h
    rw [cached.expr_ops_c.inst_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w =>
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1 : r = w := (congrArg Prod.fst e0).symm
        have e2 : memo' = memo := (congrArg Prod.snd e0).symm
        subst e1; subst e2
        have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := ILPQ (absNames ks) (absLevels us))
          expr_key_exact hm hwfe (memo_e_get_hit ho)
        exact ⟨hhit, hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, hu2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨u2, memo2⟩ := p1
        obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
        have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
        have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
        have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
        subst eg1; subst eg2
        obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 u2 hm hu2
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memo3⟩ := p3
        have e0 := Result.ok_injective (α := expr.Expr × _) h
        have e1' : r = r0 := (congrArg Prod.fst e0).symm
        have e2' : memo' = memo3 := (congrArg Prod.snd e0).symm
        subst e1'; subst e2'
        have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
        subst hsn
        have hans : ILPQ (absNames ks) (absLevels us)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)))) r := by
          refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
          rw [Expr.proj_refines hproj, habs2]
          simp [ConLeche.Expr.instantiateLevelParams]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
        exact MemoInv.set expr_key_exact hm2 hwfe hans hins


/-- **`expr_ops_c::inst_level_params` refines `ExprC.instLevelParams`**
(`ExprOpsC.lean:619-621`): the `hasLP` cutoff, then the walk under a fresh
table.  `instLevelParams_spec` (`Verify/Cached/OpsC.lean:1463`) reads the cited
definition as `Expr.instantiateLevelParams`. -/
theorem inst_level_params_refines {ks : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {e r : expr.Expr} (hks : NamesWF ks)
    (hus : LevelsWF us) (he : ExprWF e)
    (h : cached.expr_ops_c.inst_level_params ks us e = ok r) :
    absExpr r
        = ConLeche.Cached.ExprC.instLevelParams (absNames ks) (absLevels us) (absExpr e) ∧
      ExprWF r := by
  rw [ConLeche.Cached.ExprC.instLevelParams_spec]
  rw [cached.expr_ops_c.inst_level_params] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨hwf, habs⟩ := ilp_cutoff he hb h
    exact ⟨habs, hwf⟩
  | true =>
    simp only [if_true] at h
    obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r0, memo'⟩ := p
    have hr : r0 = r := Result.ok_injective h
    subst hr
    obtain ⟨⟨hwf, habs⟩, -⟩ :=
      inst_level_params_go_refines hks hus he memo memo' r0 (new_memo_inv hnew) hgo
    exact ⟨habs, hwf⟩

/-! ## `ProjEntry.typeAtI` (`ExprOpsC.lean:623-642`)

The projection field type: the entry's body with its level parameters
instantiated, then the subject and the type arguments substituted in **one
memoised pass** through the operations above -- which is the whole point of the
cited definition, and the reason `core_k::proj_entry_type_at`'s unmemoised twin
was the out-of-memory of DESIGN.md's "affine frontier".  `typeAtI_eq`
(`Verify/Cached/OpsC.lean:1474`) is the equation with the spec's
`ProjEntry.typeAt`, so the value is the same either way. -/

/-- **`expr_ops_c::proj_entry_type_at_i` refines `ProjEntry.typeAtI`**
(`ExprOpsC.lean:623-642`).  The `targs.reverse` of the cited code is
`rev_append_exprs` at the full length (the helper with no Lean counterpart),
and the subject is consed on the front -- so the replacement list is
`absExpr pe :: (absExprs targs).reverse`, which is what the cited
`pe :: targs.reverse` abstracts to. -/
theorem proj_entry_type_at_i_refines {entry : env.ProjEntry}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {pe r : expr.Expr} (hentry : ProjEntryWF entry) (hus : LevelsWF us)
    (htargs : ExprsWF targs) (hpe : ExprWF pe)
    (h : cached.expr_ops_c.proj_entry_type_at_i entry us targs pe = ok r) :
    absExpr r
        = ConLeche.ProjEntry.typeAtI (absProjEntry entry) (absLevels us)
            (absExprs targs) (absExpr pe) ∧
      ExprWF r := by
  rw [cached.expr_ops_c.proj_entry_type_at_i] at h
  dsimp only at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨body, hbody, c, hdup, vs, hpush, vs1, hrev, h⟩ := h
  obtain ⟨hbabs, hbwf⟩ :=
    inst_level_params_refines hentry.2.1 hus hentry.2.2.2.1 hbody
  rw [Expr.dup_eq hdup] at hpush
  have hvsval : vs.val = [pe] := by
    rw [vec_push_val hpush]; simp [alloc.vec.Vec.new]
  have hlen : (alloc.vec.Vec.len targs).val = targs.val.length :=
    alloc.vec.Vec.len_val targs
  have hvs1val : vs1.val = pe :: targs.val.reverse := by
    rw [rev_append_exprs_val _ vs targs vs1 (alloc.vec.Vec.len targs) rfl
      (by omega) hrev, hvsval, hlen, List.take_length]
    rfl
  have hvs1wf : ExprsWF vs1 := by
    intro y hy
    rw [hvs1val] at hy
    rcases List.mem_cons.1 hy with hy | hy
    · rw [hy]; exact hpe
    · exact htargs y (List.mem_reverse.1 hy)
  have hvs1abs : absExprs vs1 = absExpr pe :: (absExprs targs).reverse := by
    rw [absExprs, hvs1val, List.map_cons, List.map_reverse, absExprs]
  obtain ⟨habs, hwf⟩ := instantiate_list_refines hbwf hvs1wf h
  refine ⟨?_, hwf⟩
  rw [habs, hvs1abs, show ((0#u64 : Std.U64)).val = 0 by scalar_tac,
    ConLeche.ProjEntry.typeAtI, hbabs]
  rfl

end ConRon.Refine.ExprOpsC
