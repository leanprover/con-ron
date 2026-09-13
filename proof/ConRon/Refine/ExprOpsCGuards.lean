/-
The scope queries, the fabrication leaf guard, the telescopes and the
level-parameter definedness of
`crates/con-ron-core/src/cached/expr_ops_c.rs` (task #26), refined against
`ConLeche/Cached/ExprOpsC.lean` (task #51; the module note is in
`ConRon/Refine/ExprOpsC.lean`).

Four `Bool`-valued memoised walks live here, and they share a shape the
substitution walks do not have: **the memo is probed before the match**, so
every node kind gets an entry, and **the conjunctions short-circuit**, which is
memo policy -- they write *fewer* entries than an unconditional `&&` would, so
task #24's `expr_ops::bool_and` is deliberately not applied to them and each
branching arm is lifted into a one-line callee (`wscoped_b_pair` and friends).
Those callees are mutually recursive with the walk in the generated model, so
each is inverted *inside* the walk's own `ExprWF` induction (there is no
separate induction to run: the callee's arguments are the node's children) and
then restated as a corollary of the walk's lemma, which is what a caller wants.

Two mechanical notes that shaped the proofs:

* the generated callees bind their first child's answer in a **pattern `let`**
  (`let (b, memo1) ← …`), which `split` and `simp` do not see through, so each
  is inverted once and for all by an `*_inv` lemma whose disjunction is the
  short-circuit;
* con-leche's cutoff consequence `wscopedB_of_fvarsBelow_zero`
  (`Verify/Cached/OpsC.lean:1528`) is `private`, so its one-line induction is
  repeated here under its own name.
-/
import ConRon.Refine.ExprOpsCAbs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOpsC

open ConRon.Refine.ExprOps

/-! ## `wscopedB` (`ExprOpsC.lean:650-679`)

Every reachable `fvar` index is below `d`, hereditarily through the `fvar` type
annotations -- so the cached fvar range does *not* decide it (the annotations are
descended) and the only thing it decides is the `fvarB == 0` shortcut.  The memo
is keyed by `(node, cursor)` and probed before the match. -/

/-- A node with no `fvar` at all is well-scoped at every base.  con-leche's
`wscopedB_of_fvarsBelow_zero` (`Verify/Cached/OpsC.lean:1528`) is `private`, so
its one-line induction is repeated here. -/
theorem wscopedB_of_fvarsBelow_zero : ∀ (x : ConLeche.Expr),
    ConLeche.Expr.fvarsBelow 0 x → ∀ d, ConLeche.Expr.wscopedB d x = true := by
  intro x
  induction x <;> intro hb d <;>
    simp_all [ConLeche.Expr.fvarsBelow, ConLeche.Expr.wscopedB]

/-- con-leche's `MemoWInv` (`Verify/Cached/OpsC.lean:1534`), as the `Q` of
`MemoInv`: every recorded answer is the real one. -/
def WScQ : ConLeche.Expr × Nat → Bool → Prop :=
  fun key r => r = ConLeche.Expr.wscopedB key.2 key.1

/-- The `fvarB == 0` shortcut at the head of `wscoped_b_go`. -/
theorem wscoped_b_cutoff {d fb : Std.U64} {e : expr.Expr} {b : Bool}
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    (hwfe : ExprWF e) (hm : MemoInv KeyWF absKey WScQ memo)
    (hfb : expr_ops.fvar_b e = ok fb) (hz : fb.val = 0)
    (h : (ok (true, memo) :
        Result (Bool × ron.hashmap.HashMap expr_ops.ExprNatKey Bool))
      = ok (b, memo')) :
    b = ConLeche.Expr.wscopedB d.val (absExpr e) ∧ MemoInv KeyWF absKey WScQ memo' := by
  have e0 := Result.ok_injective (α := Bool × _) h
  have ea : true = b := congrArg Prod.fst e0
  have eb : memo = memo' := congrArg Prod.snd e0
  rw [← ea, ← eb]
  refine ⟨?_, hm⟩
  have hz' : (absExpr e).fvarB ≤ 0 := by
    rw [← fvar_b_refines hwfe hfb]; omega
  exact (wscopedB_of_fvarsBelow_zero _ (ConLeche.Cached.ExprC.fvarB_le hz') d.val).symm

/-- Inverting `wscoped_b_pair`: the first child is always walked, and the second
only when it answered `true`.  The generated body binds the first answer in a
pattern `let`, which no tactic sees through, so the inversion is done here by
`exact` (definitional unfolding) rather than by `split`. -/
theorem wscoped_b_pair_inv
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool} {d : Std.U64}
    {x y : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.wscoped_b_pair memo d x y = ok (b, memo')) :
    ∃ bx memoX, cached.expr_ops_c.wscoped_b_go memo d x = ok (bx, memoX) ∧
      (bx = true ∧ cached.expr_ops_c.wscoped_b_go memoX d y = ok (b, memo')
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.wscoped_b_pair] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr_ops.ExprNatKey Bool))
      = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-- Inverting `wscoped_b_triple`, the `.letE` arm's three-child short-circuit:
the first child, then the remaining two as a `wscoped_b_pair`. -/
theorem wscoped_b_triple_inv
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool} {d : Std.U64}
    {x y z : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.wscoped_b_triple memo d x y z = ok (b, memo')) :
    ∃ bx memoX, cached.expr_ops_c.wscoped_b_go memo d x = ok (bx, memoX) ∧
      (bx = true ∧ cached.expr_ops_c.wscoped_b_pair memoX d y z = ok (b, memo')
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.wscoped_b_triple] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr_ops.ExprNatKey Bool))
      = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-- **`expr_ops_c::wscoped_b_go` refines `Expr.wscopedB`** (con-leche's
`wscopedBGo`, `ExprOpsC.lean:650-676`, soundness `wscopedBGo_spec`,
`Verify/Cached/OpsC.lean:1556`).  The three branching callees are inverted
inline: their arguments are this node's children, so the `ExprWF` induction's
hypotheses are exactly what they need. -/
theorem wscoped_b_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool) (d : Std.U64)
      (b : Bool),
      MemoInv KeyWF absKey WScQ memo →
      cached.expr_ops_c.wscoped_b_go memo d e = ok (b, memo') →
      b = ConLeche.Expr.wscopedB d.val (absExpr e) ∧
        MemoInv KeyWF absKey WScQ memo' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : true = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)), d⟩) true := by
          simp [WScQ, ConLeche.Expr.wscopedB]
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hm (keyWF_mk hwfe) hans hins⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.wscoped_b_fvar memo d idx ty = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr_ops.ExprNatKey Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1
          have eb : v1 = r0 := congrArg Prod.snd e1
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)), d⟩) r0 ∧ MemoInv KeyWF absKey WScQ memo1 := by
          rw [cached.expr_ops_c.wscoped_b_fvar] at hfix
          split at hfix
          · rename_i hlt
            have hlt' : idx.val < d.val := by scalar_tac
            obtain ⟨hb1, hmF⟩ := ih memo memo1 idx r0 hm hfix
            refine ⟨?_, hmF⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hb1]
            simp [ConLeche.Expr.wscopedB, hlt']
          · rename_i hlt
            have hlt' : ¬ (idx.val < d.val) := by scalar_tac
            have e2 := Result.ok_injective (α := Bool × _) hfix
            have ea : false = r0 := congrArg Prod.fst e2
            have eb : memo = memo1 := congrArg Prod.snd e2
            rw [← ea, ← eb]
            refine ⟨?_, hm⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            simp [ConLeche.Expr.wscopedB, hlt']

        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hmF (keyWF_mk hwfe) hans hins⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : true = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.«Sort» u)), d⟩) true := by
          simp [WScQ, ConLeche.Expr.wscopedB]
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hm (keyWF_mk hwfe) hans hins⟩
  | @mk_const n vs e hn hvs h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hvs h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : true = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n vs)), d⟩) true := by
          simp [WScQ, ConLeche.Expr.wscopedB]
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hm (keyWF_mk hwfe) hans hins⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : true = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)), d⟩) true := by
          simp [WScQ, ConLeche.Expr.wscopedB]
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hm (keyWF_mk hwfe) hans hins⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.wscoped_b_pair memo d f a = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr_ops.ExprNatKey Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1
          have eb : v1 = r0 := congrArg Prod.snd e1
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), d⟩) r0 ∧ MemoInv KeyWF absKey WScQ memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := wscoped_b_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihf memo memoX d bx hm hx
          rcases hrest with ⟨rfl, hy⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨hby, hmY⟩ := iha memoX memo1 d r0 hmX hy
            refine ⟨?_, hmY⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hby]
            simp [ConLeche.Expr.wscopedB, ← hbx]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hb0]
            simp [ConLeche.Expr.wscopedB, ← hbx]

        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hmF (keyWF_mk hwfe) hans hins⟩
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.wscoped_b_pair memo d ty bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr_ops.ExprNatKey Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1
          have eb : v1 = r0 := congrArg Prod.snd e1
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), d⟩) r0 ∧ MemoInv KeyWF absKey WScQ memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := wscoped_b_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX d bx hm hx
          rcases hrest with ⟨rfl, hy⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨hby, hmY⟩ := ihbo memoX memo1 d r0 hmX hy
            refine ⟨?_, hmY⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hby]
            simp [ConLeche.Expr.wscopedB, ← hbx]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hb0]
            simp [ConLeche.Expr.wscopedB, ← hbx]

        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hmF (keyWF_mk hwfe) hans hins⟩
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.wscoped_b_pair memo d ty bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr_ops.ExprNatKey Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1
          have eb : v1 = r0 := congrArg Prod.snd e1
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), d⟩) r0 ∧ MemoInv KeyWF absKey WScQ memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := wscoped_b_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX d bx hm hx
          rcases hrest with ⟨rfl, hy⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨hby, hmY⟩ := ihbo memoX memo1 d r0 hmX hy
            refine ⟨?_, hmY⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hby]
            simp [ConLeche.Expr.wscopedB, ← hbx]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hb0]
            simp [ConLeche.Expr.wscopedB, ← hbx]

        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hmF (keyWF_mk hwfe) hans hins⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.wscoped_b_triple memo d ty w bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr_ops.ExprNatKey Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1
          have eb : v1 = r0 := congrArg Prod.snd e1
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), d⟩) r0 ∧ MemoInv KeyWF absKey WScQ memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := wscoped_b_triple_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX d bx hm hx
          rcases hrest with ⟨rfl, hyz⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨by0, memoY, hy, hrest2⟩ := wscoped_b_pair_inv hyz
            obtain ⟨hby, hmY⟩ := ihw memoX memoY d by0 hmX hy
            rcases hrest2 with ⟨rfl, hz2⟩ | ⟨rfl, hb1, hmm1⟩
            · obtain ⟨hbz, hmZ⟩ := ihbo memoY memo1 d r0 hmY hz2
              refine ⟨?_, hmZ⟩
              simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
              rw [hbz]
              simp [ConLeche.Expr.wscopedB, ← hbx, ← hby]
            · rw [← hmm1] at *
              refine ⟨?_, hmY⟩
              simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
              rw [hb1]
              simp [ConLeche.Expr.wscopedB, ← hbx, ← hby]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
            rw [hb0]
            simp [ConLeche.Expr.wscopedB, ← hbx]

        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hmF (keyWF_mk hwfe) hans hins⟩
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hkk := expr_nat_key_eq hkey
      subst hkk
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := WScQ)
          key_exact hm (keyWF_mk hwfe) (memo_b1_get_hit ho), hm⟩
      | none =>
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨p9, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, memoZ⟩ := p9
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.wscoped_b_go memo d x = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr_ops.ExprNatKey Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1
          have eb : v1 = r0 := congrArg Prod.snd e1
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)), d⟩) r0 ∧ MemoInv KeyWF absKey WScQ memo1 := by
          obtain ⟨hb1, hmF⟩ := ih memo memo1 d r0 hm hfix
          refine ⟨?_, hmF⟩
          simp only [WScQ, absKey_mk, absExpr_mk, absExprKind]
          rw [hb1]
          simp [ConLeche.Expr.wscopedB]

        rw [← er, ← em]
        exact ⟨hans, MemoInv.set key_exact hmF (keyWF_mk hwfe) hans hins⟩

/-- **`expr_ops_c::wscoped_b_fvar` refines the `.fvar` arm of `Expr.wscopedB`**
(`ExprOpsC.lean:650-676`): an index in scope licenses its annotation, which is
checked at the *index's own* bound.  A corollary of the walk's lemma -- the
callee is what the arm was lifted into, so there is nothing new to induct on. -/
theorem wscoped_b_fvar_refines {ty : expr.Expr} (hty : ExprWF ty)
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool} {d idx : Std.U64}
    {b : Bool} (hm : MemoInv KeyWF absKey WScQ memo)
    (h : cached.expr_ops_c.wscoped_b_fvar memo d idx ty = ok (b, memo')) :
    b = (decide (idx.val < d.val) &&
          ConLeche.Expr.wscopedB idx.val (absExpr ty)) ∧
      MemoInv KeyWF absKey WScQ memo' := by
  rw [cached.expr_ops_c.wscoped_b_fvar] at h
  split at h
  · rename_i hlt
    have hlt' : idx.val < d.val := by scalar_tac
    obtain ⟨hb, hmF⟩ := wscoped_b_go_refines hty memo memo' idx b hm h
    exact ⟨by rw [hb]; simp [hlt'], hmF⟩
  · rename_i hlt
    have hlt' : ¬ (idx.val < d.val) := by scalar_tac
    have e0 := Result.ok_injective (α := Bool × _) h
    have ea : false = b := congrArg Prod.fst e0
    have eb : memo = memo' := congrArg Prod.snd e0
    rw [← ea, ← eb]
    exact ⟨by simp [hlt'], hm⟩

/-- **`expr_ops_c::wscoped_b_pair` refines the two-child arms' short-circuit**
(`ExprOpsC.lean:650-676`): the second child is walked only when the first
answered `true`, which is `&&` on the answers. -/
theorem wscoped_b_pair_refines {x y : expr.Expr} (hx : ExprWF x) (hy : ExprWF y)
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool} {d : Std.U64}
    {b : Bool} (hm : MemoInv KeyWF absKey WScQ memo)
    (h : cached.expr_ops_c.wscoped_b_pair memo d x y = ok (b, memo')) :
    b = (ConLeche.Expr.wscopedB d.val (absExpr x) &&
          ConLeche.Expr.wscopedB d.val (absExpr y)) ∧
      MemoInv KeyWF absKey WScQ memo' := by
  obtain ⟨bx, memoX, hxr, hrest⟩ := wscoped_b_pair_inv h
  obtain ⟨hbx, hmX⟩ := wscoped_b_go_refines hx memo memoX d bx hm hxr
  rcases hrest with ⟨rfl, hyr⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hby, hmY⟩ := wscoped_b_go_refines hy memoX memo' d b hmX hyr
    exact ⟨by rw [hby, ← hbx]; simp, hmY⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

/-- **`expr_ops_c::wscoped_b_triple` refines the `.letE` arm's three-child
short-circuit** (`ExprOpsC.lean:650-676`). -/
theorem wscoped_b_triple_refines {x y z : expr.Expr} (hx : ExprWF x) (hy : ExprWF y)
    (hz : ExprWF z) {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {d : Std.U64} {b : Bool} (hm : MemoInv KeyWF absKey WScQ memo)
    (h : cached.expr_ops_c.wscoped_b_triple memo d x y z = ok (b, memo')) :
    b = (ConLeche.Expr.wscopedB d.val (absExpr x) &&
          (ConLeche.Expr.wscopedB d.val (absExpr y) &&
            ConLeche.Expr.wscopedB d.val (absExpr z))) ∧
      MemoInv KeyWF absKey WScQ memo' := by
  obtain ⟨bx, memoX, hxr, hrest⟩ := wscoped_b_triple_inv h
  obtain ⟨hbx, hmX⟩ := wscoped_b_go_refines hx memo memoX d bx hm hxr
  rcases hrest with ⟨rfl, hyz⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hbyz, hmYZ⟩ := wscoped_b_pair_refines hy hz hmX hyz
    exact ⟨by rw [hbyz, ← hbx]; simp, hmYZ⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

/-- **`expr_ops_c::wscoped_b` refines `ExprC.wscopedB`**
(`ExprOpsC.lean:678-679`): one memoised DAG walk under a fresh table.
`wscopedB_spec` (`Verify/Cached/OpsC.lean:1782`) is the same statement on the
Lean side. -/
theorem wscoped_b_refines {e : expr.Expr} {d : Std.U64} {b : Bool} (he : ExprWF e)
    (h : cached.expr_ops_c.wscoped_b d e = ok b) :
    b = ConLeche.Cached.ExprC.wscopedB d.val (absExpr e) := by
  rw [ConLeche.Cached.ExprC.wscopedB_spec]
  rw [cached.expr_ops_c.wscoped_b] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, memo'⟩ := p
  have hb : b0 = b := Result.ok_injective h
  subst hb
  exact (wscoped_b_go_refines he memo memo' d b0 (new_memo_inv hnew) hgo).1

/-! ## `fvarLeaves` (`ExprOpsC.lean:681-707`)

The reachable `fvar` leaves, hereditarily through the annotations, each node
visited once: the `seen` set is inserted into *before* the match, so a shared
sub-DAG is walked once.  The port accumulates where the cited code conses, so
the list comes out in the reverse order -- and because `seen` makes it
duplicate-free and its only consumer is `leafMem`, a membership test, the claim
is a claim about the **set**, which is what the cited `leafGuard` reads.  That
is the port's own documented deviation.

**One `sorry` here** (two declarations): the general statement of the walk needs
the port-side analogue of con-leche's `SeenInv` (`Verify/Cached/GuardsC.lean:409`)
-- a *gray set* invariant recording which nodes the enclosing calls are still
inside, measured on `sizeF` because `Expr.fvarLeaves` descends annotations -- and
that invariant is the file's one piece of genuinely new design.  The statements
below are the final ones; only the discharge is owed. -/

/-- **`expr_ops_c::fvar_leaves_go` refines `Expr.fvarLeaves`** with an
accumulator, at a *fresh* `seen` set -- which is how `fvar_leaves`, its only
caller, enters it. -/
theorem fvar_leaves_go_refines {e : expr.Expr} (he : ExprWF e)
    {acc r : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {seen seen' : ron.hashmap.HashMap expr.Expr Unit} (hacc : LeavesWF acc)
    (hseen : HashMap.al_v seen = [])
    (h : cached.expr_ops_c.fvar_leaves_go acc seen e = ok (r, seen')) :
    (∀ l, l ∈ absLeaves r ↔
        l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr e)) ∧
      LeavesWF r := by
  sorry

/-- **`expr_ops_c::fvar_leaves` refines `ExprC.fvarLeaves`**
(`ExprOpsC.lean:705-707`) as a set: the port's list is the cited list reversed
and duplicate-free. -/
theorem fvar_leaves_refines {e : expr.Expr} {r : alloc.vec.Vec (Std.U64 × expr.Expr)}
    (he : ExprWF e) (h : cached.expr_ops_c.fvar_leaves e = ok r) :
    (∀ l, l ∈ absLeaves r ↔ l ∈ ConLeche.Expr.fvarLeaves (absExpr e)) ∧
      LeavesWF r := by
  rw [cached.expr_ops_c.fvar_leaves] at h
  obtain ⟨seen, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, seen'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨hset, hwf⟩ := fvar_leaves_go_refines he
    (by intro q hq; simp [alloc.vec.Vec.new] at hq) (new_al_v hnew) hgo
  refine ⟨fun l => ?_, hwf⟩
  rw [hset l]
  simp [absLeaves, alloc.vec.Vec.new]

/-! ## The fabrication leaf guard (`ExprOpsC.lean:716-748`)

Every `fvar` leaf of the fabricated term is one of the subject's: con-leche task
#86's side condition on the η/ι fabrications.  Same walk shape as `wscopedB`'s
-- probe before the match, short-circuiting conjunctions lifted into callees --
but keyed by the node alone, and with `leafMem` in the `.fvar` arm.

**Four `sorry`s here.**  The walk is `wscoped_b_go_refines` node for node with
`leaf_mem_refines` in place of the scope test; what is owed is the same case
analysis, and `leaf_guard_refines` additionally needs the set-invariance of
`List.all (B.contains ·)`, which is where `fvar_leaves_refines`' set claim meets
it. -/

/-- con-leche's `MemoSubInv` (`Verify/Cached/GuardsC.lean:857`), as the `Q` of
`MemoInv`: every recorded answer is the real subset test. -/
def LeafSubQ (B : List (Nat × ConLeche.Expr)) : ConLeche.Expr → Bool → Prop :=
  fun key r => r = (ConLeche.Expr.fvarLeaves key).all (fun l => B.contains l)

/-- **`expr_ops_c::leaves_sub_go` refines the leaf-subset test**
(`ExprOpsC.lean:716-742`, soundness `leavesSubGo_spec`,
`Verify/Cached/GuardsC.lean:879`). -/
theorem leaves_sub_go_refines {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    (hbl : LeavesWF bl) {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (b : Bool),
      MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo →
      cached.expr_ops_c.leaves_sub_go bl memo e = ok (b, memo') →
      b = (ConLeche.Expr.fvarLeaves (absExpr e)).all
            (fun l => (absLeaves bl).contains l) ∧
        MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo' := by
  sorry

/-- **`expr_ops_c::leaves_sub_fvar` refines the `.fvar` arm**: a leaf in the base
list licenses its annotation (`leaf_mem_refines`). -/
theorem leaves_sub_fvar_refines {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    (hbl : LeavesWF bl) {ty : expr.Expr} (hty : ExprWF ty) {idx : Std.U64}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo)
    (h : cached.expr_ops_c.leaves_sub_fvar bl memo idx ty = ok (b, memo')) :
    b = ((absLeaves bl).contains (idx.val, absExpr ty) &&
          (ConLeche.Expr.fvarLeaves (absExpr ty)).all
            (fun l => (absLeaves bl).contains l)) ∧
      MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo' := by
  sorry

/-- **`expr_ops_c::leaves_sub_pair` refines the two-child short-circuit**. -/
theorem leaves_sub_pair_refines {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    (hbl : LeavesWF bl) {x y : expr.Expr} (hx : ExprWF x) (hy : ExprWF y)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo)
    (h : cached.expr_ops_c.leaves_sub_pair bl memo x y = ok (b, memo')) :
    b = ((ConLeche.Expr.fvarLeaves (absExpr x)).all
            (fun l => (absLeaves bl).contains l) &&
          (ConLeche.Expr.fvarLeaves (absExpr y)).all
            (fun l => (absLeaves bl).contains l)) ∧
      MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo' := by
  sorry

/-- **`expr_ops_c::leaves_sub_triple` refines the `.letE` arm's three-child
short-circuit**. -/
theorem leaves_sub_triple_refines {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    (hbl : LeavesWF bl) {x y z : expr.Expr} (hx : ExprWF x) (hy : ExprWF y)
    (hz : ExprWF z) {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo)
    (h : cached.expr_ops_c.leaves_sub_triple bl memo x y z = ok (b, memo')) :
    b = ((ConLeche.Expr.fvarLeaves (absExpr x)).all
            (fun l => (absLeaves bl).contains l) &&
          ((ConLeche.Expr.fvarLeaves (absExpr y)).all
              (fun l => (absLeaves bl).contains l) &&
            (ConLeche.Expr.fvarLeaves (absExpr z)).all
              (fun l => (absLeaves bl).contains l))) ∧
      MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo' := by
  sorry

/-- **`expr_ops_c::leaf_guard` refines `ExprC.leafGuard`**
(`ExprOpsC.lean:744-748`): `O(1)` true off the cached range on an `fvar`-free
fabrication, otherwise the leaf walk of the subject and the subset walk of the
fabrication (`leafGuard_spec`, `Verify/Cached/GuardsC.lean:1136`). -/
theorem leaf_guard_refines {fab base : expr.Expr} {b : Bool} (hfab : ExprWF fab)
    (hbase : ExprWF base) (h : cached.expr_ops_c.leaf_guard fab base = ok b) :
    b = ConLeche.Cached.ExprC.leafGuard (absExpr fab) (absExpr base) := by
  sorry

/-! ## Level-parameter definedness (`ExprOpsC.lean:791-828`)

`wscopedB`'s shape again -- probe before the match, short-circuiting callees --
with one documented exception: the two binder arms conjoin the body's answer with
the binder datum's through `expr_ops::bool_and`, *not* a short-circuit, because
the cited `(rb && m.pw.paramsDefined params, memo)` has already computed both
(task #24's rule, the module's note 4).

**Five `sorry`s here**: the walk is `wscoped_b_go_refines` node for node, at the
node-only key, with `level::all_params_defined` /
`expr_ops::levels_all_params_defined` / `prop_when::params_defined` in the leaf
and binder arms (all three already refined, in `Refine/ExprOpsMeta.lean` and
`Refine/PropWhen.lean`). -/

/-- con-leche's `MemoLPDInv` (`Verify/Cached/GuardsC.lean:70`), as the `Q` of
`MemoInv`. -/
def ALPDQ (ps : List ConLeche.Name) : ConLeche.Expr → Bool → Prop :=
  fun key r => r = ConLeche.Expr.allLevelParamsDefined ps key

/-- **`expr_ops_c::all_level_params_defined_go` refines
`Expr.allLevelParamsDefined`** (`ExprOpsC.lean:791-823`, soundness
`allLevelParamsDefinedGo_spec`, `Verify/Cached/GuardsC.lean:95`). -/
theorem all_level_params_defined_go_refines {params : alloc.vec.Vec name.Name}
    (hps : NamesWF params) {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr.Expr Bool) (b : Bool),
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo →
      cached.expr_ops_c.all_level_params_defined_go params memo e = ok (b, memo') →
      b = ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr e) ∧
        MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  sorry

/-- **`expr_ops_c::alpd_pair` refines the `.app` arm's short-circuit**. -/
theorem alpd_pair_refines {params : alloc.vec.Vec name.Name} (hps : NamesWF params)
    {x y : expr.Expr} (hx : ExprWF x) (hy : ExprWF y)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo)
    (h : cached.expr_ops_c.alpd_pair params memo x y = ok (b, memo')) :
    b = (ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr x) &&
          ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr y)) ∧
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  sorry

/-- **`expr_ops_c::alpd_binder` refines the two binder arms**: the domain
short-circuits, the body's answer is conjoined with the binder datum's
*without* short-circuiting (`expr_ops::bool_and`, the module's note 4). -/
theorem alpd_binder_refines {params : alloc.vec.Vec name.Name} (hps : NamesWF params)
    {ty bo : expr.Expr} {pw : prop_when.PropWhen} (hty : ExprWF ty)
    (hbo : ExprWF bo) (hpw : PropWhenWF pw)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo)
    (h : cached.expr_ops_c.alpd_binder params memo ty bo pw = ok (b, memo')) :
    b = (ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr ty) &&
          (ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr bo) &&
            (absPropWhen pw).paramsDefined (absNames params))) ∧
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  sorry

/-- **`expr_ops_c::alpd_triple` refines the `.letE` arm's three-child
short-circuit**. -/
theorem alpd_triple_refines {params : alloc.vec.Vec name.Name} (hps : NamesWF params)
    {x y z : expr.Expr} (hx : ExprWF x) (hy : ExprWF y) (hz : ExprWF z)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo)
    (h : cached.expr_ops_c.alpd_triple params memo x y z = ok (b, memo')) :
    b = (ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr x) &&
          (ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr y) &&
            ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr z))) ∧
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  sorry

/-- **`expr_ops_c::all_level_params_defined` refines
`ExprC.allLevelParamsDefined`** (`ExprOpsC.lean:825-828`): one memoised DAG walk
under a fresh table (`allLevelParamsDefined_spec`,
`Verify/Cached/GuardsC.lean:320`). -/
theorem all_level_params_defined_refines {params : alloc.vec.Vec name.Name}
    {e : expr.Expr} {b : Bool} (hps : NamesWF params) (he : ExprWF e)
    (h : cached.expr_ops_c.all_level_params_defined params e = ok b) :
    b = ConLeche.Cached.ExprC.allLevelParamsDefined (absNames params) (absExpr e) := by
  rw [ConLeche.Cached.ExprC.allLevelParamsDefined_spec]
  rw [cached.expr_ops_c.all_level_params_defined] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b0, memo'⟩ := p
  have hb : b0 = b := Result.ok_injective h
  subst hb
  exact (all_level_params_defined_go_refines hps he memo memo' b0
    (new_memo_inv hnew) hgo).1

/-! ## The telescope operations (`ExprOpsC.lean:752-787`)

`instSpine` and `piResidual`, both built on the memoised substitutions above.
`instSpine` takes the one bulk pass when the spine spans the telescope context
and the `instantiate1` chain otherwise; `piResidual` peels one `∀`-binder per
argument and substitutes in one pass at the end, re-entering on the same
argument list with the accumulator flushed -- the cited non-structural recursion,
whose `termination_by (as.length, acc.length)` has no counterpart here because
Aeneas's `partial_fixpoint` carries no measure.

**Five `sorry`s here**: all five are consequences of
`instantiate_list_refines`, which is itself one of task #51's owed proofs, plus
(for `piResidualAcc`) the cited two-component measure. -/

/-- **`expr_ops_c::inst_spine_chain_from` refines `Expr.instSpine`** at the
arguments from `i` on. -/
theorem inst_spine_chain_from_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (t : Std.U64)
      (e r : expr.Expr),
      args.val.length - i.val = N → ExprsWF args → ExprWF e →
      cached.expr_ops_c.inst_spine_chain_from args i t e = ok r →
      absExpr r
          = ConLeche.Expr.instSpine ((absExprs args).drop i.val) t.val (absExpr e) ∧
        ExprWF r := by
  sorry

/-- **`expr_ops_c::inst_spine_chain` refines `ExprC.instSpineChain`**
(`ExprOpsC.lean:752-755`): the `i = 0` wrapper. -/
theorem inst_spine_chain_refines {args : alloc.vec.Vec expr.Expr} {t : Std.U64}
    {e r : expr.Expr} (hargs : ExprsWF args) (he : ExprWF e)
    (h : cached.expr_ops_c.inst_spine_chain args t e = ok r) :
    absExpr r
        = ConLeche.Cached.ExprC.instSpineChain (absExprs args) t.val (absExpr e) ∧
      ExprWF r := by
  sorry

/-- **`expr_ops_c::inst_spine` refines `ExprC.instSpine`**
(`ExprOpsC.lean:757-761`): the one bulk pass when the spine spans the telescope
context, the `instantiate1` chain otherwise. -/
theorem inst_spine_refines {args : alloc.vec.Vec expr.Expr} {t : Std.U64}
    {e r : expr.Expr} (hargs : ExprsWF args) (he : ExprWF e)
    (h : cached.expr_ops_c.inst_spine args t e = ok r) :
    absExpr r = ConLeche.Cached.ExprC.instSpine (absExprs args) t.val (absExpr e) ∧
      ExprWF r := by
  sorry

/-- **`expr_ops_c::pi_residual_acc` refines `ExprC.piResidualAcc`**
(`ExprOpsC.lean:763-783`) at the arguments from `i` on. -/
theorem pi_residual_acc_refines {acc args : alloc.vec.Vec expr.Expr}
    {e : expr.Expr} {i : Std.Usize} {o : Option expr.Expr} (hacc : ExprsWF acc)
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : cached.expr_ops_c.pi_residual_acc acc e args i = ok o) :
    o.map absExpr
        = ConLeche.Cached.ExprC.piResidualAcc (absExprs acc) (absExpr e)
            ((absExprs args).drop i.val) ∧
      ∀ x ∈ o, ExprWF x := by
  sorry

/-- **`expr_ops_c::pi_residual` refines `ExprC.piResidual`**
(`ExprOpsC.lean:785-787`): the residual of a `∀`-telescope at an argument
spine. -/
theorem pi_residual_refines {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {o : Option expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : cached.expr_ops_c.pi_residual e args = ok o) :
    o.map absExpr = ConLeche.Cached.ExprC.piResidual (absExpr e) (absExprs args) ∧
      ∀ x ∈ o, ExprWF x := by
  rw [cached.expr_ops_c.pi_residual] at h
  obtain ⟨hmap, hwf⟩ := pi_residual_acc_refines
    (by intro x hx; simp [alloc.vec.Vec.new] at hx) hargs he h
  refine ⟨?_, hwf⟩
  rw [hmap, ConLeche.Cached.ExprC.piResidual,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]
  simp [absExprs, alloc.vec.Vec.new]

end ConRon.Refine.ExprOpsC

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Three representative lemmas of the four files: the memoised substitution behind
every executed `instantiate1` call site, the memoised abstraction behind every
binder close, and the memoised scope walk that gates the η/ι fabrications.  Each
must depend on the three standard axioms and nothing else -- in particular
nothing may reach `ConRon.Refine.Pins.PINS_TEXT`. -/

/--
info: 'ConRon.Refine.ExprOpsC.instantiate1_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOpsC.instantiate1_refines

/--
info: 'ConRon.Refine.ExprOpsC.abstract1_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOpsC.abstract1_refines

/--
info: 'ConRon.Refine.ExprOpsC.wscoped_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOpsC.wscoped_b_refines
