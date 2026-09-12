/-
Task #21, the three cutoff-and-memo walks of `kernel::expr_ops`: `abstract1`
(`ExprOps.lean:760-1934`), `lowerBVars` (`:694-2151`) and `instantiate1Lift`
(`:718-2363`), plus `instPisAtLift` (`:2375`), which folds the last of them
over a `∀`-telescope's open arguments.

Each of the three is con-leche's `*Fast` member and carries **both** remedies
of its family (task #233, quoted in the Rust): an `O(1)` cutoff on the packed
range field -- `fvar_b(e) <= d` for `abstract1`, `bvar_b(e) <= c + amount` for
`lowerBVars`, `bvar_b(e) <= d` for `instantiate1Lift` -- and, behind it, a memo
keyed by the node and the *cursor*.  So each walk's lemma needs two extra
ingredients over `instantiate1_go_refines`: the accessor lemma
(`fvar_b_refines`/`bvar_b_refines` of `ExprOpsBvarB.lean`, through
`ConLeche.Expr.fvarB_eq`/`bvarB_eq`) and con-leche's own cutoff theorem
(`abstract1_of_fvarRange_le` `:1763`, `lowerBVars_of_bvarBound_le` `:1957`,
`instantiate1Lift_of_bvarBound_le` `:2167`) -- which is exactly why those
theorems exist upstream.  The cutoff branch is the same three lines in all ten
constructors, so it is factored into one `*_cutoff` lemma per walk and each
case discharges it with a single `exact`.

`instantiate1_lift_go`'s `.bvar` arm calls `lift_loose_bvars`, so this part
imports `ExprOpsLift.lean` for `lift_loose_bvars_refines`; in the merged file
that part must come first.
-/
import ConRon.Refine.ExprOpsBvarB
import ConRon.Refine.ExprOpsLift

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps


/-- con-leche's `Abs1MemoInv` (`ExprOps.lean:1770`), as the `Q` of `MemoInv`:
every recorded answer is the real one, and it is well formed. -/
def Abs1Q (d : Nat) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun key r => ExprWF r ∧ absExpr r = ConLeche.Expr.abstract1 key.1 d key.2


/-- The cutoff branch of `abstract1_go`, shared by all ten constructors: a node
whose fvar range is at or below `d` cannot contain `fvar d`, so the walk returns
it unchanged (`abstract1_of_fvarRange_le`). -/
theorem abstract1_cutoff {d k fb : Std.U64} {e r : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey (Abs1Q d.val) memo)
    (hfb : expr_ops.fvar_b e = ok fb) (hle : fb.val ≤ d.val)
    (h : (do let c ← expr.dup e; ok (c, memo)) = ok (r, memo')) :
    (ExprWF r ∧ absExpr r = ConLeche.Expr.abstract1 (absExpr e) d.val k.val) ∧
      MemoInv KeyWF absKey (Abs1Q d.val) memo' := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨c, hdup, hr, hmm⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr; subst hmm
  refine ⟨⟨hwfe, ?_⟩, hm⟩
  have hfr : (absExpr e).fvarRange ≤ d.val := by
    rw [← ConLeche.Expr.fvarB_eq, ← fvar_b_refines hwfe hfb]; exact hle
  rw [ConLeche.Expr.abstract1_of_fvarRange_le _ _ _ hfr]


/-- **`expr_ops::abstract1_go` refines `Expr.abstract1`** (con-leche's
`abstract1Go` `ExprOps.lean:1797-1833`, soundness `abstract1Go_spec` `:1836`):
the `fvar_b` cutoff first, then the memo keyed by the node and the binder
cursor. -/
theorem abstract1_go_refines {d : Std.U64} {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (k : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (Abs1Q d.val) memo →
      expr_ops.abstract1_go d memo e k = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.abstract1 (absExpr e) d.val k.val) ∧
        MemoInv KeyWF absKey (Abs1Q d.val) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' k r hm h
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hx, hr, hmm⟩ := h
      subst hr; subst hmm
      refine ⟨⟨Expr.bvar_wf hx, ?_⟩, hm⟩
      rw [Expr.bvar_refines hx]
      simp [ConLeche.Expr.abstract1]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' k r hm h
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      split at h
      · rename_i hid
        have hid2 : idx.val = d.val := by scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, hx, hr, hmm⟩ := h
        subst hr; subst hmm
        refine ⟨⟨Expr.bvar_wf hx, ?_⟩, hm⟩
        rw [Expr.bvar_refines hx]
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
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' k r hm h
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' k r hm h
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.abstract1]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' k r hm h
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.abstract1_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact abstract1_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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


/-- con-leche's `LowerMemoInv` (`ExprOps.lean:1993`), as the `Q` of `MemoInv`. -/
def LowerQ (amount : Nat) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun key r => ExprWF r ∧ absExpr r = ConLeche.Expr.lowerBVars amount key.2 key.1


/-- The cutoff branch of `lower_bvars_go`: a node whose loose-bvar bound is at
or below the top of the window holds no variable the lowering moves
(`lowerBVars_of_bvarBound_le`). -/
theorem lower_bvars_cutoff {amount c fb lim : Std.U64} {e r : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey (LowerQ amount.val) memo)
    (hfb : expr_ops.bvar_b e = ok fb) (hlim : c + amount = ok lim)
    (hle : fb.val ≤ lim.val)
    (h : (do let x ← expr.dup e; ok (x, memo)) = ok (r, memo')) :
    (ExprWF r ∧ absExpr r = ConLeche.Expr.lowerBVars amount.val c.val (absExpr e)) ∧
      MemoInv KeyWF absKey (LowerQ amount.val) memo' := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨x, hdup, hr, hmm⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr; subst hmm
  refine ⟨⟨hwfe, ?_⟩, hm⟩
  have hbb : (absExpr e).bvarBound ≤ c.val + amount.val := by
    rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines hwfe hfb,
      ← HashMap.uscalar_add_eq hlim]
    exact hle
  rw [ConLeche.Expr.lowerBVars_of_bvarBound_le _ _ _ hbb]


/-- **`expr_ops::lower_bvars_go` refines `Expr.lowerBVars`** (con-leche's
`lowerBVarsGo` `ExprOps.lean:2013-2049`, soundness `lowerBVarsGo_spec` `:2052`):
the `bvar_b` cutoff first, then the memo keyed by the node and the cutoff. -/
theorem lower_bvars_go_refines {amount : Std.U64} {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (c : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (LowerQ amount.val) memo →
      expr_ops.lower_bvars_go amount memo e c = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.lowerBVars amount.val c.val (absExpr e)) ∧
        MemoInv KeyWF absKey (LowerQ amount.val) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      split at h
      · rename_i hge
        have hge2 : i.val ≥ c.val + amount.val := by rw [← hlimv]; scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨i3, hi3, x, hx, hr, hmm⟩ := h
        subst hr; subst hmm
        refine ⟨⟨Expr.bvar_wf hx, ?_⟩, hm⟩
        rw [Expr.bvar_refines hx, HashMap.uscalar_sub_eq hi3]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.lowerBVars]
        rw [if_pos hge2]
      · rename_i hge
        have hge2 : ¬ (i.val ≥ c.val + amount.val) := by rw [← hlimv]; scalar_tac
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, hx, hr, hmm⟩ := h
        subst hr; subst hmm
        refine ⟨⟨Expr.bvar_wf hx, ?_⟩, hm⟩
        rw [Expr.bvar_refines hx]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.lowerBVars]
        rw [if_neg hge2]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.lowerBVars]⟩, hm⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.lowerBVars]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.lowerBVars]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.lowerBVars]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LowerQ amount.val)
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
        have hans : LowerQ amount.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), c⟩) r := by
          refine ⟨Expr.app_wf hwf2 hwf3 hbuild, ?_⟩
          rw [Expr.app_refines hbuild, habs2, habs3]
          simp [ConLeche.Expr.lowerBVars]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LowerQ amount.val)
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
        have hans : LowerQ amount.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), c⟩) r := by
          refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.lam_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.lowerBVars]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LowerQ amount.val)
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
        have hans : LowerQ amount.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), c⟩) r := by
          refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hbuild, ?_⟩
          rw [Expr.forall_e_refines hbuild, habs2, habs3, Expr.binder_meta_dup_eq hbm,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.lowerBVars]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LowerQ amount.val)
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
        have hans : LowerQ amount.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), c⟩) r := by
          refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hbuild, ?_⟩
          rw [Expr.let_e_refines hbuild, habs2, habs3, habs4,
            HashMap.uscalar_add_eq hcc]
          simp [ConLeche.Expr.lowerBVars]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lower_bvars_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨lim, hlim, h⟩ := bind_eq_ok_iff.mp h
    have hlimv : lim.val = c.val + amount.val := HashMap.uscalar_add_eq hlim
    split at h
    · exact lower_bvars_cutoff hwfe hm hfb hlim (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
        have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LowerQ amount.val)
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
        have hans : LowerQ amount.val (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)), c⟩) r := by
          refine ⟨Expr.proj_wf hs hwf2 hbuild, ?_⟩
          rw [Expr.proj_refines hbuild, habs2]
          simp [ConLeche.Expr.lowerBVars]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hdup] at hins
        exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins


/-- con-leche's `Inst1LMemoInv` (`ExprOps.lean:2203`), as the `Q` of `MemoInv`. -/
def Inst1LQ (v : ConLeche.Expr) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun key r => ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift key.1 v key.2


/-- The cutoff branch of `instantiate1_lift_go`: substituting for a variable no
loose variable of the node reaches is the identity
(`instantiate1Lift_of_bvarBound_le`). -/
theorem instantiate1_lift_cutoff {v : expr.Expr} {d fb : Std.U64} {e r : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey (Inst1LQ (absExpr v)) memo)
    (hfb : expr_ops.bvar_b e = ok fb) (hle : fb.val ≤ d.val)
    (h : (do let x ← expr.dup e; ok (x, memo)) = ok (r, memo')) :
    (ExprWF r ∧
        absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val) ∧
      MemoInv KeyWF absKey (Inst1LQ (absExpr v)) memo' := by
  simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨x, hdup, hr, hmm⟩ := h
  rw [Expr.dup_eq hdup] at hr
  subst hr; subst hmm
  refine ⟨⟨hwfe, ?_⟩, hm⟩
  have hbb : (absExpr e).bvarBound ≤ d.val := by
    rw [← ConLeche.Expr.bvarB_eq, ← bvar_b_refines hwfe hfb]; exact hle
  rw [ConLeche.Expr.instantiate1Lift_of_bvarBound_le _ _ _ hbb]


/-- **`expr_ops::instantiate1_lift_go` refines `Expr.instantiate1Lift`**
(con-leche's `instantiate1LiftGo` `ExprOps.lean:2223-2261`, soundness
`instantiate1LiftGo_spec` `:2264`): the `bvar_b` cutoff, then the memo keyed by
the node and the cursor; the `.bvar` arm at the cursor lifts `v`'s own loose
variables (`lift_loose_bvars_refines`). -/
theorem instantiate1_lift_go_refines {v : expr.Expr} (hv : ExprWF v) {e : expr.Expr}
    (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
      (d : Std.U64) (r : expr.Expr),
      MemoInv KeyWF absKey (Inst1LQ (absExpr v)) memo →
      expr_ops.instantiate1_lift_go v memo e d = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val) ∧
        MemoInv KeyWF absKey (Inst1LQ (absExpr v)) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
          refine ⟨⟨Expr.bvar_wf hx, ?_⟩, hm⟩
          rw [Expr.bvar_refines hx, HashMap.uscalar_sub_eq hi2]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
          rw [if_neg hid2, if_pos (by omega)]
          simp
        · rename_i hgt
          have hgt2 : ¬ (d.val < i.val) := fun hc => hgt (by scalar_tac)
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨x, hx, hr, hmm⟩ := h
          subst hr; subst hmm
          refine ⟨⟨Expr.bvar_wf hx, ?_⟩, hm⟩
          rw [Expr.bvar_refines hx]
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.instantiate1Lift]
          rw [if_neg hid2, if_neg (by omega)]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hdup, hr, hmm⟩ := h
      rw [Expr.dup_eq hdup] at hr
      subst hr; subst hmm
      exact ⟨⟨hwfe, by simp [ConLeche.Expr.instantiate1Lift]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate1_lift_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact instantiate1_lift_cutoff hwfe hm hfb (by scalar_tac) h
    · simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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


/-! ## `instPisAtLift` (`ExprOps.lean:2365-2378`)

The one telescope walk that uses the *general* substitution, so it belongs with
`instantiate1Lift` rather than with the rest of the spine family.  Its
recursion is on the argument *index* (task #13's deviation 3: Lean's list
recursion becomes an index recursion over a `Vec`), and the expression changes
at every step, so the induction is a strong induction on the number of
arguments left -- not on an `ExprWF` derivation, which only supplies the node's
shape here (through `cases`). -/

/-- `Vec::index` lands on the list element, as a `getElem?` fact: `expr.Expr`
has no `Inhabited` instance, so `HashMap.vec_index_eq`'s `l[i]!` form is not
available at this type. -/
theorem vec_index_expr_getElem? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    {x : α} (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    rw [hi, Result.ok_injective h]

/-- The abstracted argument list, one step of the index recursion. -/
theorem absExprs_drop_cons {args : alloc.vec.Vec expr.Expr} {i : Nat} {x : expr.Expr}
    (hx : args.val[i]? = some x) :
    (absExprs args).drop i = absExpr x :: (absExprs args).drop (i + 1) := by
  have hlt : i < args.val.length := by
    rw [List.getElem?_eq_some_iff] at hx; exact hx.1
  have hget : args.val[i] = x := by
    rw [List.getElem?_eq_getElem hlt] at hx; exact Option.some_injective _ hx
  rw [absExprs, List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_map, hget]

/-- **`expr_ops::inst_pis_at_lift_from` refines `Expr.instPisAtLift`** at the
suffix `args.drop i`: the `Option` result maps onto con-leche's, and a `some`
carries a well-formed term. -/
theorem inst_pis_at_lift_from_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (o : Option expr.Expr),
      args.val.length - i.val = N → ExprsWF args → ExprWF e →
      expr_ops.inst_pis_at_lift_from args i e = ok o →
      o.map absExpr =
          ConLeche.Expr.instPisAtLift ((absExprs args).drop i.val) (absExpr e) ∧
        ∀ r, o = some r → ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i e o hN hargs he h
    rw [expr_ops.inst_pis_at_lift_from.eq_def] at h
    split at h
    · have hlenv := alloc.vec.Vec.len_val args
      have hlen : args.val.length ≤ i.val := by scalar_tac
      have hd : (absExprs args).drop i.val = [] :=
        List.drop_eq_nil_of_le (by rw [absExprs, List.length_map]; exact hlen)
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨c, hdup, ho⟩ := h
      rw [Expr.dup_eq hdup] at ho
      subst ho
      rw [hd]
      refine ⟨by simp [ConLeche.Expr.instPisAtLift], ?_⟩
      intro r hr
      rw [Option.some.injEq] at hr
      subst hr
      exact he
    · have hlenv := alloc.vec.Vec.len_val args
      have hlt : i.val < args.val.length := by scalar_tac
      simp only [rc_deref_eq, bind_tc_ok] at h
      cases he with
      | @bvar i1 e h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @fvar idx ty e hty h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @sort u e hu h1 =>
        obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @app f a e hf ha h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @lam ty bo m e hty hbo hm0 h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @lit l e hl h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @proj s i1 x e hs hx h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [node_kind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨y, hy⟩ : ∃ y, args.val[i.val]? = some y :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hy]
        simp [ConLeche.Expr.instPisAtLift]
      | @forall_e ty bo m e hty hbo hm0 h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [node_kind] at h
        obtain ⟨a, hidx, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hx := vec_index_expr_getElem? hidx
        have hawf : ExprWF a := hargs a (by
          rw [List.getElem?_eq_some_iff] at hx
          obtain ⟨hlt2, hget⟩ := hx
          rw [← hget]
          exact List.getElem_mem hlt2)
        obtain ⟨habs, hbwf⟩ := instantiate1_lift_refines hbo hawf hb
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec, hwfrec⟩ :=
          ih (args.val.length - i2.val) (by omega) args i2 b o (by omega) hargs hbwf h
        refine ⟨?_, hwfrec⟩
        rw [absExprs_drop_cons hx, hrec, hi2v]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instPisAtLift]
        rw [habs, Expr.val_zero]

/-- **`expr_ops::inst_pis_at_lift` refines `Expr.instPisAtLift`**: the `i = 0`
wrapper of the index recursion. -/
theorem inst_pis_at_lift_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {o : Option expr.Expr} (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_pis_at_lift args e = ok o) :
    o.map absExpr = ConLeche.Expr.instPisAtLift (absExprs args) (absExpr e) ∧
      ∀ r, o = some r → ExprWF r := by
  rw [expr_ops.inst_pis_at_lift] at h
  obtain ⟨h1, h2⟩ :=
    inst_pis_at_lift_from_refines (args.val.length - (0#usize : Std.Usize).val) args
      0#usize e o rfl hargs he h
  refine ⟨?_, h2⟩
  rw [h1, show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero]

end ConRon.Refine.ExprOps
