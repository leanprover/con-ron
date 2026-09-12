/-
Part of task #21 (`ConRon/Refine/ExprOps.lean`'s group): the *metadata* half of
`crates/con-ron-core/src/kernel/expr_ops.rs` -- the two node-keyed memoized
walks (`reset_meta`, `rename_consts`), the level-parameter substitution
(`levels_subst`, `instantiate_level_params`, with the `level::zeroness_of` and
`level::subst_pw` bridge task #13 added to `level.rs`), and the leaf readers
(`is_lam`, `lam_pw`, `forall_pw`, `has_level_param`, `expr_ptr_beq`,
`fvar_leaves`).

Statements are against the **logical** con-leche definitions, exact result on
success, abstraction equation first and well-formedness second, exactly as
`ConRon/Refine/ExprOps.lean`'s `instantiate1_refines`.  The two walks here are
keyed by the *node alone*, so they instantiate the foundation's `MemoInv` at
`KWF := ExprWF`, `absK := absExpr`, `A := ConLeche.Expr` and use
`expr_key_exact`/`memo_e_get_hit`.

Three things cost time and are worth recording.  (1) `reset_meta_go`'s
memo-skipping leaves are `Bvar`/`Sort`/`Const`/`Lit` -- **`Fvar` is a
*memoized* case here**, because the walk descends into the annotation, unlike
`instantiate1`'s; the same is true of `rename_consts_go`, where `Const` is the
interesting case and therefore not a leaf.  (2) The higher-order arguments are
one-method dictionaries (task #9's pattern 1): `expr_ops::NameToName` and
`level::SubstZ`, so their lemmas carry a hypothesis relating the dictionary to
the Lean function, as `Refine/PropWhen.lean` does for `bind_z`.  (3)
`has_level_param` is *not* a walk in the port: it is the `O(1)` packed-word
read, so its lemma is task #20's `Expr.has_lp_refines` composed with
con-leche's `Expr.hasLP_eq` (`ExprOps.lean:2538`) -- the `@[csimp]`-free member
of the family.
-/
import ConRon.Refine.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## `resetMeta` (`ExprOps.lean:540-692`) -/

/-- con-leche's `ResetMemoInv` (`ExprOps.lean:562`), as the `Q` of `MemoInv`. -/
def ResetQ : ConLeche.Expr → expr.Expr → Prop :=
  fun k r => ExprWF r ∧ absExpr r = ConLeche.Expr.resetMeta k

/-- The binder datum `reset_meta` puts on every binder: the parse placeholder
`⟨.never⟩` (`prop_when::never` is a constant, so this is total). -/
theorem never_meta {pw : prop_when.PropWhen} (h : prop_when.never = ok pw) :
    BinderMetaWF { pw := pw } ∧
      absBinderMeta { pw := pw } = (⟨.never⟩ : ConLeche.BinderMeta) := by
  refine ⟨PropWhen.never_wf h, ?_⟩
  rw [absBinderMeta, PropWhen.never_refines h]

/-- **`expr_ops::reset_meta_go` refines `Expr.resetMeta`** (`ExprOps.lean:580`,
the memoized walk of the `@[csimp]` family at `:690`).  con-leche's
`resetMetaGo_spec` (`:618`) is the proof plan; the induction is on the `ExprWF`
derivation, which is what gives both the node's shape and the children's
well-formedness. -/
theorem reset_meta_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr) (r : expr.Expr),
      MemoInv ExprWF absExpr ResetQ memo →
      expr_ops.reset_meta_go memo e = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.resetMeta (absExpr e)) ∧
        MemoInv ExprWF absExpr ResetQ memo' := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.bvar h1, by simp [ConLeche.Expr.resetMeta]⟩, hm⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.sort hu h1, by simp [ConLeche.Expr.resetMeta]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.mk_const hn hus h1, by simp [ConLeche.Expr.resetMeta]⟩, hm⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.lit hl h1, by simp [ConLeche.Expr.resetMeta]⟩, hm⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ResetQ)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
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
      have hans : ResetQ
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) r := by
        refine ⟨Expr.fvar_wf hwf2 hfv, ?_⟩
        rw [Expr.fvar_refines hfv, habs2]
        simp [ConLeche.Expr.resetMeta]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm2 hwfe hans hins
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ResetQ)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
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
      have hans : ResetQ
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) r := by
        refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
        rw [Expr.app_refines happ, habs2, habs3]
        simp [ConLeche.Expr.resetMeta]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ResetQ)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨pw, hpw, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 b hm2 hb
      obtain ⟨hmwf, hmabs⟩ := never_meta hpw
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : ResetQ
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r := by
        refine ⟨Expr.lam_wf hwf2 hwf3 hmwf hlam, ?_⟩
        rw [Expr.lam_refines hlam, habs2, habs3, hmabs]
        simp [ConLeche.Expr.resetMeta]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ResetQ)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨pw, hpw, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 b hm2 hb
      obtain ⟨hmwf, hmabs⟩ := never_meta hpw
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : ResetQ
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r := by
        refine ⟨Expr.forall_e_wf hwf2 hwf3 hmwf hfa, ?_⟩
        rw [Expr.forall_e_refines hfa, habs2, habs3, hmabs]
        simp [ConLeche.Expr.resetMeta]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w' =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w' := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ResetQ)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hv2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨w2, memo3⟩ := p2
      obtain ⟨p3, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo4⟩ := p3
      obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 w2 hm2 hv2
      obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 b hm3 hb
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p4, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo5⟩ := p4
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo5 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : ResetQ
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)))) r := by
        refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
        rw [Expr.let_e_refines hlet, habs2, habs3, habs4]
        simp [ConLeche.Expr.resetMeta]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm4 hwfe hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' r hm h
    rw [expr_ops.reset_meta_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ResetQ)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, hu, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨u, memo2⟩ := p1
      obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 u hm hu
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
      have hans : ResetQ
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)))) r := by
        refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
        rw [Expr.proj_refines hproj, habs2]
        simp [ConLeche.Expr.resetMeta]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm2 hwfe hans hins

/-- **`expr_ops::reset_meta` refines `Expr.resetMeta`** (`ExprOps.lean:687`,
`@[csimp]` at `:690`): the fresh memo satisfies `ResetMemoInv` vacuously. -/
theorem reset_meta_refines {e r : expr.Expr} (he : ExprWF e)
    (h : expr_ops.reset_meta e = ok r) :
    absExpr r = ConLeche.Expr.resetMeta (absExpr e) ∧ ExprWF r := by
  rw [expr_ops.reset_meta] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ := reset_meta_go_refines he memo memo' r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

/-! ## `renameConsts` (`ExprOps.lean:930-1116`)

`levels_copy` is the port's stand-in for "the `us` a rebuilt `.const` node
carries over unchanged"; in the model a `Vec` copy is the *same list*, because
`level::dup` is the identity (`Rc::clone`, DESIGN.md §3.2), so the helper below
is an equation between vectors rather than a refinement lemma. -/

/-- `expr_ops::levels_copy_from` appends the rest of the levels: the `Vec`
copy of task #13's deviation 2, in the model the identity (`level::dup` is
`Rc::clone`).  Same shape and proof as `PropWhen.append_from_val`. -/
theorem levels_copy_from_val (us : alloc.vec.Vec level.Level) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out r : alloc.vec.Vec level.Level),
      us.length - i.val ≤ k → expr_ops.levels_copy_from us i out = ok r →
      r.val = out.val ++ us.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out r hk h
    rw [expr_ops.levels_copy_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len us by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le (show us.val.length ≤ i.val by scalar_tac)]
    simp
  | succ k ih =>
    intro i out r hk h
    rw [expr_ops.levels_copy_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ us.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len us by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show us.val.length ≤ i.val by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len us by scalar_tac)] at h
      have hi : i.val < us.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := us.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec us i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw, level_dup_eq,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨out1, hout1, h⟩ := h
      rw [ih w out1 r (by scalar_tac) h, vec_push_val hout1,
        List.drop_eq_getElem_cons hi, hwv]
      simp

/-- `expr_ops::levels_copy` is the identity in the model. -/
theorem levels_copy_val {us r : alloc.vec.Vec level.Level}
    (h : expr_ops.levels_copy us = ok r) : r.val = us.val := by
  rw [expr_ops.levels_copy] at h
  have hv := levels_copy_from_val us us.length 0#usize (alloc.vec.Vec.new level.Level) r
    (by scalar_tac) h
  simpa [alloc.vec.Vec.new] using hv

/-- con-leche's `RenameMemoInv` (`ExprOps.lean:981`), as the `Q` of `MemoInv`:
it mentions the *abstract* renaming `g`, which is what the dictionary
hypothesis ties the port's `F` to. -/
def RenameQ (g : ConLeche.Name → ConLeche.Name) : ConLeche.Expr → expr.Expr → Prop :=
  fun k r => ExprWF r ∧ absExpr r = ConLeche.Expr.renameConsts g k

/-- **`expr_ops::rename_consts_go` refines `Expr.renameConsts`**
(`ExprOps.lean:1000`, the memoized walk of the `@[csimp]` family at `:1113`;
plan `renameConstsGo_spec` `:1039`).  The `f : Name → Name` argument is the
one-method dictionary `expr_ops::NameToName` (task #9's pattern 1), so the
lemma carries `hf`, the hypothesis that the dictionary computes `g` -- the same
shape as `PropWhen.bind_z_refines`.  `.const` is a memo-skipping *leaf* here
(the rename happens there and nowhere else), and `.proj`'s structure name is
deliberately not renamed on either side (task #175 W5). -/
theorem rename_consts_go_refines {F : Type} {inst : expr_ops.NameToName F} {f : F}
    (g : ConLeche.Name → ConLeche.Name)
    (hf : ∀ n, NameWF n → ∀ r, inst.rename f n = ok r →
      absName r = g (absName n) ∧ NameWF r)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr) (r : expr.Expr),
      MemoInv ExprWF absExpr (RenameQ g) memo →
      expr_ops.rename_consts_go inst f memo e = ok (r, memo') →
      (ExprWF r ∧ absExpr r = ConLeche.Expr.renameConsts g (absExpr e)) ∧
        MemoInv ExprWF absExpr (RenameQ g) memo' := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.bvar h1, by simp [ConLeche.Expr.renameConsts]⟩, hm⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.sort hu h1, by simp [ConLeche.Expr.renameConsts]⟩, hm⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.lit hl h1, by simp [ConLeche.Expr.renameConsts]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨n2, hn2, us2, hus2, r0, hmk, hr, hmm⟩ := h
    subst hr; subst hmm
    obtain ⟨hnabs, hnwf⟩ := hf n hn n2 hn2
    have husv : us2.val = us.val := levels_copy_val hus2
    have husw : LevelsWF us2 := by
      intro u hu; exact hus u (husv ▸ hu)
    have hlv : absLevels us2 = absLevels us := by unfold absLevels; rw [husv]
    refine ⟨⟨Expr.mk_const_wf hnwf husw hmk, ?_⟩, hm⟩
    rw [Expr.mk_const_refines hmk, hnabs, hlv]
    simp [ConLeche.Expr.renameConsts]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RenameQ g)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
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
      have hans : RenameQ g
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) r := by
        refine ⟨Expr.fvar_wf hwf2 hfv, ?_⟩
        rw [Expr.fvar_refines hfv, habs2]
        simp [ConLeche.Expr.renameConsts]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm2 hwfe hans hins
  | @app a b e ha hb h1 iha ihb =>
    have hwfe : ExprWF e := ExprWF.app ha hb h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RenameQ g)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ha2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨a2, memo2⟩ := p1
      obtain ⟨p2, hb2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b2, memo3⟩ := p2
      obtain ⟨r1, happ, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := iha memo memo2 a2 hm ha2
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihb memo2 memo1 b2 hm2 hb2
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : RenameQ g
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App a b)))) r := by
        refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
        rw [Expr.app_refines happ, habs2, habs3]
        simp [ConLeche.Expr.renameConsts]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RenameQ g)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 b hm2 hb
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : RenameQ g
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r := by
        refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
        rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm]
        simp [ConLeche.Expr.renameConsts]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RenameQ g)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 b hm2 hb
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : RenameQ g
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r := by
        refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
        rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm]
        simp [ConLeche.Expr.renameConsts]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm3 hwfe hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w' =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w' := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RenameQ g)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hv2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨w2, memo3⟩ := p2
      obtain ⟨p3, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo4⟩ := p3
      obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 w2 hm2 hv2
      obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 b hm3 hb
      obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p4, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo5⟩ := p4
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo5 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : RenameQ g
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)))) r := by
        refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
        rw [Expr.let_e_refines hlet, habs2, habs3, habs4]
        simp [ConLeche.Expr.renameConsts]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm4 hwfe hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' r hm h
    rw [expr_ops.rename_consts_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | some w =>
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1 : r = w := (congrArg Prod.fst e0).symm
      have e2 : memo' = memo := (congrArg Prod.snd e0).symm
      subst e1; subst e2
      have hhit := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := RenameQ g)
        expr_key_exact hm hwfe (memo_e_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, hu, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨u, memo2⟩ := p1
      obtain ⟨n2, hn2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hproj, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr.Expr _ × _) hgo
      have eg1 : memo1 = memo2 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 u hm hu
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
      have hans : RenameQ g
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)))) r := by
        refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
        rw [Expr.proj_refines hproj, habs2]
        simp [ConLeche.Expr.renameConsts]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hd1, Expr.dup_eq hd2] at hins
      exact MemoInv.set expr_key_exact hm2 hwfe hans hins

/-- **`expr_ops::rename_consts` refines `Expr.renameConsts`**
(`ExprOps.lean:1109`, `@[csimp]` at `:1113`). -/
theorem rename_consts_refines {F : Type} {inst : expr_ops.NameToName F} {f : F}
    (g : ConLeche.Name → ConLeche.Name)
    (hf : ∀ n, NameWF n → ∀ r, inst.rename f n = ok r →
      absName r = g (absName n) ∧ NameWF r)
    {e r : expr.Expr} (he : ExprWF e) (h : expr_ops.rename_consts inst f e = ok r) :
    absExpr r = ConLeche.Expr.renameConsts g (absExpr e) ∧ ExprWF r := by
  rw [expr_ops.rename_consts] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    rename_consts_go_refines g hf he memo memo' r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

/-! ## The `Level`-to-`PropWhen` bridge (`level.rs`, task #13)

`level::zeroness_of` and `level::subst_pw` were filled into `level.rs` at task
#13 (the two blocks task #3 deferred until `PropWhen` existed).  Their lemmas
live *here*, next to their one consumer `instantiate_level_params`, rather than
in `ConRon/Refine/Level.lean`: `zeronessOf` produces a `PropWhen`, so the proof
needs `Refine/PropWhen.lean`, which `Refine/Level.lean` does not import. -/

/-- The `Level` twin of the foundation's `node_kind`. -/
theorem level_node_kind (h : Std.U64) (k : level.LevelKind) :
    (level.Level.mk (level.LevelNode.mk h k))._0.kind = k := rfl

/-- **`level::zeroness_of` refines `Level.zeronessOf`**
(`ConLeche/Kernel/Level.lean:185-195`). -/
theorem zeroness_of_refines {l : level.Level} (hl : LevelWF l) :
    ∀ pw, level.zeroness_of l = ok pw →
      absPropWhen pw = ConLeche.Level.zeronessOf (absLevel l) ∧ PropWhenWF pw := by
  induction hl with
  | @zero u h1 =>
    have hu := level_zero_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, level_node_kind] at h
    refine ⟨?_, PropWhen.if_all_zero_wf (fun n hn => by simp at hn) h⟩
    rw [PropWhen.if_all_zero_refines (fun n hn => by simp at hn) h]
    simp [ConLeche.Level.zeronessOf, absNames, alloc.vec.Vec.new]
  | @succ a u ha h1 _ =>
    obtain ⟨hh, hu⟩ := level_succ_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, level_node_kind] at h
    exact ⟨by rw [PropWhen.never_refines h]; simp [ConLeche.Level.zeronessOf],
      PropWhen.never_wf h⟩
  | @max a b u ha hb h1 iha ihb =>
    obtain ⟨hh, hu⟩ := level_max_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, level_node_kind, bind_eq_ok_iff] at h
    obtain ⟨pa, hpa, pb, hpb, hinter⟩ := h
    obtain ⟨habsa, hwfa⟩ := iha pa hpa
    obtain ⟨habsb, hwfb⟩ := ihb pb hpb
    obtain ⟨habs, hwf⟩ := PropWhen.inter_refines hwfa hwfb hinter
    exact ⟨by rw [habs, habsa, habsb]; simp [ConLeche.Level.zeronessOf], hwf⟩
  | @imax a b u ha hb h1 _ ihb =>
    obtain ⟨hh, hu⟩ := level_imax_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, level_node_kind] at h
    obtain ⟨habsb, hwfb⟩ := ihb pw h
    exact ⟨by rw [habsb]; simp [ConLeche.Level.zeronessOf], hwfb⟩
  | @param n u hn h1 =>
    obtain ⟨hh, hu⟩ := level_param_inv h1
    subst hu
    intro pw h
    rw [level.zeroness_of.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, level_node_kind, bind_eq_ok_iff, name_dup_eq] at h
    obtain ⟨ps, hps, h⟩ := h
    have hpsv : ps.val = [n] := by
      rw [vec_push_val hps]; simp [alloc.vec.Vec.new]
    have hnames : NamesWF ps := by
      intro k hk; rw [hpsv] at hk; simp at hk; rw [hk]; exact hn
    refine ⟨?_, PropWhen.if_all_zero_wf hnames h⟩
    rw [PropWhen.if_all_zero_refines hnames h]
    have : absNames ps = [absName n] := by unfold absNames; rw [hpsv]; simp
    rw [this]
    simp [ConLeche.Level.zeronessOf]

/-- **`level::subst_pw` refines `Level.substPW`**
(`ConLeche/Kernel/Level.lean:197-207`): `prop_when::bind_z` at the dictionary
`level::SubstZ`, whose `apply` is `zeroness_of ∘ subst_go` -- exactly the
closure con-leche writes.  The `Φ` of `PropWhen.bind_z_refines` is therefore
`fun n => zeronessOf (Level.subst.go ks vs n)`, and `hf` is
`Level.subst_go_refines` followed by `zeroness_of_refines`. -/
theorem subst_pw_refines {ks : alloc.vec.Vec name.Name} {vs : alloc.vec.Vec level.Level}
    {pw r : prop_when.PropWhen} (hks : NamesWF ks) (hvs : LevelsWF vs)
    (hpw : PropWhenWF pw) (h : level.subst_pw ks vs pw = ok r) :
    absPropWhen r = ConLeche.Level.substPW (absNames ks) (absLevels vs) (absPropWhen pw)
      ∧ PropWhenWF r := by
  rw [level.subst_pw] at h
  have hf : ∀ n, NameWF n → ∀ c,
      (prop_when.NameToPw.apply
        level.SubstZ.Insts.Con_ron_coreKernelProp_whenNameToPw) { ks := ks, vs := vs } n
        = ok c →
      absPropWhen c =
        ConLeche.Level.zeronessOf
          (ConLeche.Level.subst.go (absNames ks) (absLevels vs) (absName n)) ∧
        PropWhenWF c := by
    intro n hn c hc
    have hc' : (do
          let l ← level.subst_go ks vs 0#usize n
          level.zeroness_of l) = ok c := hc
    obtain ⟨u, hu, hz⟩ := bind_eq_ok_iff.mp hc'
    obtain ⟨habsu, hwfu⟩ := Level.subst_go_refines hks hvs hn ks.length 0#usize
      (by scalar_tac) u hu
    obtain ⟨habsc, hwfc⟩ := zeroness_of_refines hwfu c hz
    refine ⟨?_, hwfc⟩
    have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
    rw [habsc, habsu, h0]
    simp only [List.drop_zero]
    rfl
  obtain ⟨habs, hwf⟩ := PropWhen.bind_z_refines
    (fun n => ConLeche.Level.zeronessOf
      (ConLeche.Level.subst.go (absNames ks) (absLevels vs) n)) hf hpw h
  exact ⟨by rw [habs, ConLeche.Level.substPW], hwf⟩

/-! ## `instantiateLevelParams` (`Kernel/Level.lean:232-249`, memoized at
`ExprOps.lean:2564-2724`)

`levels_subst` is `vs.map (Level.subst ks us)`, the closure DESIGN.md §3.4
forbids, as an index recursion; the `absLevels` of the result is therefore the
`List.map` con-leche writes. -/

/-- `expr_ops::levels_subst_from` maps `Level.subst` over the rest of the
levels. -/
theorem levels_subst_from_refines {ks : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    (vs : alloc.vec.Vec level.Level) (hvs : LevelsWF vs) :
    ∀ k : Nat, ∀ (i : Std.Usize) (out r : alloc.vec.Vec level.Level),
      vs.length - i.val ≤ k → LevelsWF out →
      expr_ops.levels_subst_from ks us vs i out = ok r →
      r.val.map absLevel = out.val.map absLevel ++
          (vs.val.drop i.val).map (fun l =>
            ConLeche.Level.subst (absNames ks) (absLevels us) (absLevel l)) ∧
        LevelsWF r := by
  intro k
  induction k with
  | zero =>
    intro i out r hk hout h
    rw [expr_ops.levels_subst_from.eq_def] at h; simp only [] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len vs by scalar_tac)] at h
    simp only [Result.ok.injEq] at h; subst h
    rw [List.drop_eq_nil_of_le (show vs.val.length ≤ i.val by scalar_tac)]
    exact ⟨by simp, hout⟩
  | succ k ih =>
    intro i out r hk hout h
    rw [expr_ops.levels_subst_from.eq_def] at h; simp only [] at h
    by_cases hle : i.val ≥ vs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len vs by scalar_tac)] at h
      simp only [Result.ok.injEq] at h; subst h
      rw [List.drop_eq_nil_of_le (show vs.val.length ≤ i.val by scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len vs by scalar_tac)] at h
      have hi : i.val < vs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := vs.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec vs i hi)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff, hy, hw,
        Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨l1, hl1, out1, hout1, h⟩ := h
      have hywf : LevelWF vs.val[i.val] := hvs _ (List.getElem_mem hi)
      obtain ⟨habs1, hwf1⟩ := Level.subst_refines hywf hks hus hl1
      have hout1wf : LevelsWF out1 := by
        intro v hv
        rw [vec_push_val hout1] at hv
        rcases List.mem_append.1 hv with hv | hv
        · exact hout v hv
        · simp only [List.mem_singleton] at hv; rw [hv]; exact hwf1
      obtain ⟨hr, hrwf⟩ := ih w out1 r (by scalar_tac) hout1wf h
      refine ⟨?_, hrwf⟩
      have hsub : absLevel l1 =
          ConLeche.Level.subst (absNames ks) (absLevels us) (absLevel vs.val[i.val]) := by
        rw [habs1]; unfold absNames absLevels; rfl
      have hml : i.val < (vs.val.map (fun l =>
          ConLeche.Level.subst (absNames ks) (absLevels us) (absLevel l))).length := by
        simpa using hi
      rw [hr, vec_push_val hout1, hwv]
      simp [hsub, List.drop_eq_getElem_cons hml]

/-- **`expr_ops::levels_subst` refines `vs.map (Level.subst ks us)`**, the
`.const` arm of `Expr.instantiateLevelParams`. -/
theorem levels_subst_refines {ks : alloc.vec.Vec name.Name}
    {us vs r : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    (hvs : LevelsWF vs) (h : expr_ops.levels_subst ks us vs = ok r) :
    absLevels r = (absLevels vs).map (ConLeche.Level.subst (absNames ks) (absLevels us)) ∧
      LevelsWF r := by
  rw [expr_ops.levels_subst] at h
  obtain ⟨hr, hrwf⟩ := levels_subst_from_refines hks hus vs hvs vs.length 0#usize
    (alloc.vec.Vec.new level.Level) r (by scalar_tac) (by intro v hv; simp [alloc.vec.Vec.new] at hv) h
  refine ⟨?_, hrwf⟩
  unfold absLevels
  rw [hr]
  simp [alloc.vec.Vec.new, List.map_map, Function.comp, absLevels]

/-- con-leche's `ILPMemoInv` (`ExprOps.lean:2544`), as the `Q` of `MemoInv`. -/
def ILPQ (ks : List ConLeche.Name) (us : List ConLeche.Level) :
    ConLeche.Expr → expr.Expr → Prop :=
  fun k r => ExprWF r ∧ absExpr r = k.instantiateLevelParams ks us

/-- The `!hasLP` cutoff at the top of `instantiate_level_params_go`: the
packed word's bit says the node mentions no level parameter, and then the
substitution is the identity -- con-leche's own
`Expr.instantiateLevelParams_eq_self` (`ExprOps.lean:2463`) through
`Expr.hasLP_eq` (`:2538`).  Task #20's `wf_data` is what makes the *bit* the
`hasLP` of the abstraction. -/
theorem ilp_cutoff {e r : expr.Expr} {ks : List ConLeche.Name} {us : List ConLeche.Level}
    (he : ExprWF e) (hb : expr.has_lp e = ok false) (hdup : expr.dup e = ok r) :
    ExprWF r ∧ absExpr r = (absExpr e).instantiateLevelParams ks us := by
  have hlp : (absExpr e).hasLP = false := (Expr.has_lp_refines he hb).symm
  rw [ConLeche.Expr.Expr.hasLP_eq] at hlp
  rw [Expr.dup_eq hdup]
  exact ⟨he, (ConLeche.Expr.instantiateLevelParams_eq_self hlp).symm⟩

/-- **`expr_ops::instantiate_level_params_go` refines
`Expr.instantiateLevelParams`** (`Kernel/Level.lean:232`; the memoized walk is
`Expr.instLPGo`, `ExprOps.lean:2564`, and the `@[csimp]` equation `:2721`).
Plan: `Expr.instLPGo_spec` (`:2605`).  Every case starts with the `hasLP`
cutoff (`ilp_cutoff`); `.bvar`, `.lit`, `.sort` and `.const` then skip the
memo, and the six rebuilding kinds probe it. -/
theorem instantiate_level_params_go_refines {ks : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} (hks : NamesWF ks) (hus : LevelsWF us)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr) (r : expr.Expr),
      MemoInv ExprWF absExpr (ILPQ (absNames ks) (absLevels us)) memo →
      expr_ops.instantiate_level_params_go ks us memo e = ok (r, memo') →
      (ExprWF r ∧
          absExpr r = (absExpr e).instantiateLevelParams (absNames ks) (absLevels us)) ∧
        MemoInv ExprWF absExpr (ILPQ (absNames ks) (absLevels us)) memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hc, hr, hmm⟩ := h
      subst hr; subst hmm
      refine ⟨⟨Expr.bvar_wf hc, ?_⟩, hm⟩
      rw [Expr.bvar_refines hc]
      simp [ConLeche.Expr.instantiateLevelParams]
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' r hm h
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨l1, hl1, c, hc, hr, hmm⟩ := h
      subst hr; subst hmm
      have hll : l1 = l := Expr.literal_dup_eq hl1
      subst hll
      refine ⟨⟨Expr.lit_wf hl hc, ?_⟩, hm⟩
      rw [Expr.lit_refines hc]
      simp [ConLeche.Expr.instantiateLevelParams]
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' r hm h
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨l, hl, c, hc, hr, hmm⟩ := h
      subst hr; subst hmm
      obtain ⟨habsl, hwfl⟩ := Level.subst_refines hu hks hus hl
      refine ⟨⟨Expr.sort_wf hwfl hc, ?_⟩, hm⟩
      rw [Expr.sort_refines hc, habsl]
      unfold absNames absLevels
      simp [ConLeche.Expr.instantiateLevelParams]
  | @mk_const n vs e hn hvs h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hvs h1
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' r hm h
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff,
        name_dup_eq, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨v, hv, c, hc, hr, hmm⟩ := h
      subst hr; subst hmm
      obtain ⟨habsv, hwfv⟩ := levels_subst_refines hks hus hvs hv
      refine ⟨⟨Expr.mk_const_wf hn hwfv hc, ?_⟩, hm⟩
      rw [Expr.mk_const_refines hc, habsv]
      simp [ConLeche.Expr.instantiateLevelParams]
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' r hm h
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind] at h
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
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hbb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b1, memo3⟩ := p2
        obtain ⟨pw, hpw, hgo⟩ := bind_eq_ok_iff.mp hgo
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
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind] at h
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
        obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨t, memo2⟩ := p1
        obtain ⟨p2, hbb, hgo⟩ := bind_eq_ok_iff.mp hgo
        obtain ⟨b1, memo3⟩ := p2
        obtain ⟨pw, hpw, hgo⟩ := bind_eq_ok_iff.mp hgo
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
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind] at h
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
    rw [expr_ops.instantiate_level_params_go.eq_def] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff, Result.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨c, hdup, hr, hmm⟩ := h
      subst hr; subst hmm
      exact ⟨ilp_cutoff hwfe hb hdup, hm⟩
    | true =>
      simp only [if_true, rc_deref_eq, bind_tc_ok, node_kind] at h
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

/-- **`expr_ops::instantiate_level_params` refines
`Expr.instantiateLevelParams`** (`Kernel/Level.lean:232`, `@[csimp]` at
`ExprOps.lean:2721`). -/
theorem instantiate_level_params_refines {ks : alloc.vec.Vec name.Name}
    {us : alloc.vec.Vec level.Level} {e r : expr.Expr} (hks : NamesWF ks)
    (hus : LevelsWF us) (he : ExprWF e)
    (h : expr_ops.instantiate_level_params ks us e = ok r) :
    absExpr r = (absExpr e).instantiateLevelParams (absNames ks) (absLevels us) ∧
      ExprWF r := by
  rw [expr_ops.instantiate_level_params] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ := instantiate_level_params_go_refines hks hus he memo memo' r0
    (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

/-! ## The leaf readers

`is_lam`, `lam_pw` and `forall_pw` need no well-formedness: they read the
node's kind, and a `PropWhen` they hand out is the node's own (`prop_when::dup`
is the identity), so its `PropWhenWF` is not a *new* obligation -- a caller who
has `ExprWF e` gets it by inverting that derivation.  The statements are
therefore plain abstraction equations, `Option.map`-shaped where the result is
an `Option`. -/

/-- **`expr_ops::is_lam` refines `Expr.isLam`** (`ExprOps.lean:883`). -/
theorem is_lam_refines {e : expr.Expr} {b : Bool} (h : expr_ops.is_lam e = ok b) :
    b = ConLeche.Expr.isLam (absExpr e) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [expr_ops.is_lam.eq_def] at h
  simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
  cases k <;>
    simp only [Result.ok.injEq] at h <;>
    rw [← h] <;>
    simp [ConLeche.Expr.isLam]

/-- **`expr_ops::lam_pw` refines `Expr.lamPw`** (`ExprOps.lean:892`). -/
theorem lam_pw_refines {e : expr.Expr} {o : Option prop_when.PropWhen}
    (h : expr_ops.lam_pw e = ok o) :
    o.map absPropWhen = ConLeche.Expr.lamPw (absExpr e) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [expr_ops.lam_pw.eq_def] at h
  simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
  cases k with
  | Lam ty bo m =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨pw, hpw, ho⟩ := h
    rw [PropWhen.dup_eq hpw] at ho
    have ho' : o = some m.pw := (Result.ok_injective ho).symm
    rw [ho']
    simp [ConLeche.Expr.lamPw, absBinderMeta]
  | _ =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.lamPw]

/-- **`expr_ops::forall_pw` refines `Expr.forallPw`** (`ExprOps.lean:900`). -/
theorem forall_pw_refines {e : expr.Expr} {o : Option prop_when.PropWhen}
    (h : expr_ops.forall_pw e = ok o) :
    o.map absPropWhen = ConLeche.Expr.forallPw (absExpr e) := by
  obtain ⟨⟨d, k⟩⟩ := e
  rw [expr_ops.forall_pw.eq_def] at h
  simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
  cases k with
  | ForallE ty bo m =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨pw, hpw, ho⟩ := h
    rw [PropWhen.dup_eq hpw] at ho
    have ho' : o = some m.pw := (Result.ok_injective ho).symm
    rw [ho']
    simp [ConLeche.Expr.forallPw, absBinderMeta]
  | _ =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.forallPw]

/-- **`expr_ops::expr_ptr_beq` refines `Expr.exprPtrBEq`** (`ExprOps.lean:2387`).
DESIGN.md §3.2: `ptr_eq` is `false` in the model, so the port takes the slow
path and the obligation left is `Expr.beq`'s exactness -- which is also what
`withPtrEq`'s own proof argument (`fun h => by subst h; simp`) discharges on
the con-leche side.  `withPtrEq` is *definitionally* `k ()`, so con-leche's
`exprPtrBEq` is its `Expr.beq`. -/
theorem expr_ptr_beq_refines {a b : expr.Expr} {c : Bool} (ha : ExprWF a) (hb : ExprWF b)
    (h : expr_ops.expr_ptr_beq a b = ok c) :
    c = ConLeche.Expr.exprPtrBEq (absExpr a) (absExpr b) := by
  rw [expr_ops.expr_ptr_beq] at h
  simp only [Expr.ptr_eq_eq, bind_tc_ok, Bool.false_eq_true, if_false] at h
  rw [Expr.beq_exact ha hb h]
  rfl

/-- **`expr_ops::has_level_param` refines `Expr.hasLevelParam`**
(`ExprOps.lean:2425`).  The port's item is the *walk*, not the packed-word
read (that is `expr::has_lp`, task #20's `Expr.has_lp_refines`), so the proof
is an induction on the `ExprWF` derivation with `level::level_has_param` and
`level::levels_have_param` at the two level arms and `prop_when::has_params` at
the binders; con-leche's `Expr.levelHasParam_eq`/`levelsHaveParam_eq`
(`:2524`, `:2529`) bridge its level walkers to `Level.hasParam`. -/
theorem has_level_param_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ b, expr_ops.has_level_param e = ok b → b = (absExpr e).hasLevelParam := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.hasLevelParam]
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.hasLevelParam]
  | @sort u e hu h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Level.level_has_param_refines h, ConLeche.Expr.Expr.levelHasParam_eq]
    simp [ConLeche.Expr.hasLevelParam]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Level.levels_have_param_refines h, ConLeche.Expr.Expr.levelsHaveParam_eq]
    simp [ConLeche.Expr.hasLevelParam]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [ih b h]
    simp [ConLeche.Expr.hasLevelParam]
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    rw [ihf b1 hb1] at h
    cases hc : (absExpr f).hasLevelParam with
    | true =>
      rw [hc] at h
      simp only [if_true, Result.ok.injEq] at h
      rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc]
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, if_false] at h
      rw [iha b h]; simp [ConLeche.Expr.hasLevelParam, hc]
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    rw [ihty b1 hb1] at h
    cases hc : (absExpr ty).hasLevelParam with
    | true =>
      rw [hc] at h
      simp only [if_true, Result.ok.injEq] at h
      rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc]
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      rw [ihbo b2 hb2] at h
      cases hc2 : (absExpr bo).hasLevelParam with
      | true =>
        rw [hc2] at h
        simp only [if_true, Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc, hc2]
      | false =>
        rw [hc2] at h
        simp only [Bool.false_eq_true, if_false] at h
        rw [PropWhen.has_params_refines hm0 h]
        simp [ConLeche.Expr.hasLevelParam, hc, hc2, absBinderMeta]
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    rw [ihty b1 hb1] at h
    cases hc : (absExpr ty).hasLevelParam with
    | true =>
      rw [hc] at h
      simp only [if_true, Result.ok.injEq] at h
      rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc]
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      rw [ihbo b2 hb2] at h
      cases hc2 : (absExpr bo).hasLevelParam with
      | true =>
        rw [hc2] at h
        simp only [if_true, Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc, hc2]
      | false =>
        rw [hc2] at h
        simp only [Bool.false_eq_true, if_false] at h
        rw [PropWhen.has_params_refines hm0 h]
        simp [ConLeche.Expr.hasLevelParam, hc, hc2, absBinderMeta]
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨b1, hb1, h⟩ := h
    rw [ihty b1 hb1] at h
    cases hc : (absExpr ty).hasLevelParam with
    | true =>
      rw [hc] at h
      simp only [if_true, Result.ok.injEq] at h
      rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc]
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
      obtain ⟨b2, hb2, h⟩ := h
      rw [ihw b2 hb2] at h
      cases hc2 : (absExpr w).hasLevelParam with
      | true =>
        rw [hc2] at h
        simp only [if_true, Result.ok.injEq] at h
        rw [← h]; simp [ConLeche.Expr.hasLevelParam, hc, hc2]
      | false =>
        rw [hc2] at h
        simp only [Bool.false_eq_true, if_false] at h
        rw [ihbo b h]
        simp [ConLeche.Expr.hasLevelParam, hc, hc2]
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro b h
    rw [expr_ops.has_level_param.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [ih b h]
    simp [ConLeche.Expr.hasLevelParam]

/-! ## `fvarLeaves` (`ExprOps.lean:823`)

The result is a `Vec<(u64, Expr)>` where con-leche has a `List (Nat × Expr)`,
so the abstraction is the pointwise one; the port accumulates where Lean `++`s
(task #13's deviation 3), which is what the `*_go` lemma's `out ++` shape
records. -/

/-- A `Vec<(u64, Expr)>` as con-leche's `List (Nat × Expr)`. -/
def absLeaves (v : alloc.vec.Vec (Std.U64 × expr.Expr)) : List (Nat × ConLeche.Expr) :=
  v.val.map (fun p => (p.1.val, absExpr p.2))

/-- Every expression in a leaf list is well formed. -/
def LeavesWF (v : alloc.vec.Vec (Std.U64 × expr.Expr)) : Prop := ∀ p ∈ v.val, ExprWF p.2

/-- **`expr_ops::fvar_leaves_go` refines `Expr.fvarLeaves`** with an
accumulator. -/
theorem fvar_leaves_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (out r : alloc.vec.Vec (Std.U64 × expr.Expr)), LeavesWF out →
      expr_ops.fvar_leaves_go e out = ok r →
      absLeaves r = absLeaves out ++ ConLeche.Expr.fvarLeaves (absExpr e) ∧ LeavesWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    subst h
    exact ⟨by simp [ConLeche.Expr.fvarLeaves], hout⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    subst h
    exact ⟨by simp [ConLeche.Expr.fvarLeaves], hout⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    subst h
    exact ⟨by simp [ConLeche.Expr.fvarLeaves], hout⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    subst h
    exact ⟨by simp [ConLeche.Expr.fvarLeaves], hout⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨e1, hd1, out1, hpush, hrec⟩ := h
    rw [Expr.dup_eq hd1] at hpush
    have hout1 : LeavesWF out1 := by
      intro p hp
      rw [vec_push_val hpush] at hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hout p hp
      · simp only [List.mem_singleton] at hp; rw [hp]; exact hty
    obtain ⟨habs, hwf⟩ := ih out1 r hout1 hrec
    refine ⟨?_, hwf⟩
    have hl1 : absLeaves out1 = absLeaves out ++ [(idx.val, absExpr ty)] := by
      unfold absLeaves; rw [vec_push_val hpush]; simp
    rw [habs, hl1]
    simp [ConLeche.Expr.fvarLeaves]
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨out2, h2, hrec⟩ := h
    obtain ⟨habs2, hwf2⟩ := ihf out out2 hout h2
    obtain ⟨habs3, hwf3⟩ := iha out2 r hwf2 hrec
    refine ⟨?_, hwf3⟩
    rw [habs3, habs2]
    simp [ConLeche.Expr.fvarLeaves]
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨out2, h2, hrec⟩ := h
    obtain ⟨habs2, hwf2⟩ := ihty out out2 hout h2
    obtain ⟨habs3, hwf3⟩ := ihbo out2 r hwf2 hrec
    refine ⟨?_, hwf3⟩
    rw [habs3, habs2]
    simp [ConLeche.Expr.fvarLeaves]
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨out2, h2, hrec⟩ := h
    obtain ⟨habs2, hwf2⟩ := ihty out out2 hout h2
    obtain ⟨habs3, hwf3⟩ := ihbo out2 r hwf2 hrec
    refine ⟨?_, hwf3⟩
    rw [habs3, habs2]
    simp [ConLeche.Expr.fvarLeaves]
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨out2, h2, out3, h3, hrec⟩ := h
    obtain ⟨habs2, hwf2⟩ := ihty out out2 hout h2
    obtain ⟨habs3, hwf3⟩ := ihw out2 out3 hwf2 h3
    obtain ⟨habs4, hwf4⟩ := ihbo out3 r hwf3 hrec
    refine ⟨?_, hwf4⟩
    rw [habs4, habs3, habs2]
    simp [ConLeche.Expr.fvarLeaves]
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro out r hout h
    rw [expr_ops.fvar_leaves_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨habs, hwf⟩ := ih out r hout h
    refine ⟨?_, hwf⟩
    rw [habs]
    simp [ConLeche.Expr.fvarLeaves]

/-- **`expr_ops::fvar_leaves` refines `Expr.fvarLeaves`**
(`ExprOps.lean:823`). -/
theorem fvar_leaves_refines {e : expr.Expr} {r : alloc.vec.Vec (Std.U64 × expr.Expr)}
    (he : ExprWF e) (h : expr_ops.fvar_leaves e = ok r) :
    absLeaves r = ConLeche.Expr.fvarLeaves (absExpr e) ∧ LeavesWF r := by
  rw [expr_ops.fvar_leaves] at h
  obtain ⟨habs, hwf⟩ := fvar_leaves_go_refines he _ r
    (by intro p hp; simp [alloc.vec.Vec.new] at hp) h
  exact ⟨by rw [habs]; simp [absLeaves, alloc.vec.Vec.new], hwf⟩

end ConRon.Refine.ExprOps

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`instantiate_level_params_refines` is the deepest chain in this part -- the
node-keyed memo, `levels_subst`, `level::subst_pw` through `PropWhen.bindZ`,
and the `hasLP` cutoff -- so it is the one worth pinning. -/

/--
info: 'ConRon.Refine.ExprOps.instantiate_level_params_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOps.instantiate_level_params_refines
