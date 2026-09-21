/-
The scope queries, the fabrication leaf guard, the telescopes and the
level-parameter definedness of
`crates/con-ron-core/src/cached/expr_ops_c.rs` (task #26), refined against
`ConLeche/Cached/ExprOpsC.lean` (task #51; the module note is in
`ConRon/Refine/ExprOpsC.lean`).

Four `Bool`-valued memoised walks live here, and they share a shape the
substitution walks do not have: **the memo is probed before the match**, and
**the conjunctions short-circuit**, which is
memo policy -- they write *fewer* entries than an unconditional `&&` would, so
task #24's `expr_ops::bool_and` is deliberately not applied to them and each
branching arm is lifted into a one-line callee (`wscoped_b_pair` and friends).
Those callees are mutually recursive with the walk in the generated model, so
each is inverted *inside* the walk's own `ExprWF` induction (there is no
separate induction to run: the callee's arguments are the node's children) and
then restated as a corollary of the walk's lemma, which is what a caller wants.

Since con-leche's tasks #317/#319 the probe and the record are *gated*
(`cached::expr_ops_c::memo_skip`, task #98): a node is memoised only when a
reference-count read reports it SHARED, and a `Bool` walk additionally skips
the LEAVES, which it decides on the spot.  `ron::node::is_exclusive` is a hole
modelled `ok false`, so in the model the leaf test is the whole gate: the
compound arms below open with `memo_skip_eq`/`is_compound_f` reducing `skip` to
`false` and read exactly as they did, while `.bvar`/`.sort`/`.const`/`.lit`
lose their memo-hit case entirely -- the probe is `ok none` and the record
hands the table straight back, so the invariant travels on `hm` rather than on
`MemoInv.set`.  `fvar_leaves_go` is untouched: its table is a visited *set*,
which con-leche deliberately left out of the idiom.

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
  exact (wscopedB_of_fvarsBelow_zero _ (ConLeche.Expr.fvarB_le hz') d.val).symm

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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b1_get_if_true, memo_b1_insert_if_true] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)), d⟩) true := by
        simp [WScQ, ConLeche.Expr.wscopedB]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b1_get_if_false] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
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
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, hins⟩ := memo_b1_insert_if_inv hrec
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b1_get_if_true, memo_b1_insert_if_true] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.«Sort» u)), d⟩) true := by
        simp [WScQ, ConLeche.Expr.wscopedB]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @mk_const n vs e hn hvs h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hvs h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b1_get_if_true, memo_b1_insert_if_true] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n vs)), d⟩) true := by
        simp [WScQ, ConLeche.Expr.wscopedB]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b1_get_if_true, memo_b1_insert_if_true] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : WScQ (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)), d⟩) true := by
        simp [WScQ, ConLeche.Expr.wscopedB]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d b hm h
    rw [cached.expr_ops_c.wscoped_b_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact wscoped_b_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b1_get_if_false] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
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
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, hins⟩ := memo_b1_insert_if_inv hrec
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b1_get_if_false] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
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
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, hins⟩ := memo_b1_insert_if_inv hrec
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b1_get_if_false] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
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
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, hins⟩ := memo_b1_insert_if_inv hrec
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b1_get_if_false] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
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
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, hins⟩ := memo_b1_insert_if_inv hrec
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b1_get_if_false] at h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok_iff.mp h
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
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, hins⟩ := memo_b1_insert_if_inv hrec
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

/-- **`expr_ops_c::wscoped_b` refines `Expr.wscopedBC`**
(`ExprOpsC.lean:678-679`): one memoised DAG walk under a fresh table.
`wscopedB_spec` (`Verify/Cached/OpsC.lean:1782`) is the same statement on the
Lean side. -/
theorem wscoped_b_refines {e : expr.Expr} {d : Std.U64} {b : Bool} (he : ExprWF e)
    (h : cached.expr_ops_c.wscoped_b d e = ok b) :
    b = ConLeche.Expr.wscopedBC d.val (absExpr e) := by
  rw [ConLeche.Expr.wscopedBC_spec]
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

Discharged in task #54: the port-side analogue of con-leche's `SeenInv`
(`Verify/Cached/GuardsC.lean:409`) is task #47's `MemoInv` at `V := Unit`, whose
`Q` is `SeenQ` below -- "a recorded node's leaves are already in the
accumulator, *or* the node is gray".  The gray set is what makes the invariant
true of the node the call is inside and of its ancestors; the call's
precondition is that every gray node is strictly bigger in `sizeF` (which is
what rules a `seen` hit at the node itself out), descending pushes the node into
it (`SeenQ_insertGray`) and the call's post-condition pops it again
(`SeenQ_dropGray`), by which time the node's leaves *are* in the accumulator.
`MemoInv`'s own clause "every recorded key is well formed" is what lets
`expr::eq2`'s exactness apply at the pairs `seen_get` compares, exactly as in
the memoised walks. -/

/-- Weakening the answer predicate of a memo invariant. -/
theorem MemoInv_monoQ {K V A : Type} {KWF : K → Prop} {absK : K → A}
    {Q Q' : A → V → Prop} {m : ron.hashmap.HashMap K V}
    (hm : MemoInv KWF absK Q m) (hQ : ∀ a v, Q a v → Q' a v) :
    MemoInv KWF absK Q' m :=
  fun k r hmem => ⟨(hm k r hmem).1, hQ _ _ (hm k r hmem).2⟩

/-- con-leche's `fvarLeaves_nil_of_fvarsBelow_zero`
(`Verify/Cached/GuardsC.lean:370`) is `private`, so its one-line induction is
repeated here: a node with no `fvar` below the cursor `0` has no reachable
leaf. -/
theorem fvarLeaves_nil_of_fvarsBelow_zero : ∀ (x : ConLeche.Expr),
    ConLeche.Expr.fvarsBelow 0 x → ConLeche.Expr.fvarLeaves x = [] := by
  intro x
  induction x <;> intro hb <;>
    simp_all [ConLeche.Expr.fvarsBelow, ConLeche.Expr.fvarLeaves]

/-- The `fvarB == 0` shortcut at the head of `fvar_leaves_go`. -/
theorem fvar_leaves_cutoff {e : expr.Expr} {fb : Std.U64} (hwfe : ExprWF e)
    (hfb : expr_ops.fvar_b e = ok fb) (hz : fb.val = 0) :
    ConLeche.Expr.fvarLeaves (absExpr e) = [] := by
  have hz' : (absExpr e).fvarB ≤ 0 := by rw [← fvar_b_refines hwfe hfb]; omega
  exact fvarLeaves_nil_of_fvarsBelow_zero _ (ConLeche.Expr.fvarB_le hz')

/-! ## The gray-set invariant

`fvar_leaves_go` marks a node **before** descending into it, so "every recorded
node's leaves are already in the accumulator" is false for the node being
processed and for its ancestors.  con-leche's `SeenInv`
(`Verify/Cached/GuardsC.lean:409`) relaxes it by a *gray* predicate `G` on
erasures and requires every gray node to be strictly bigger (in `sizeF`) than
the node the call is at -- which is exactly what rules out a `seen` hit at the
node itself.  Descending pushes the node into `G` (`insertGray`); the call's
post-condition pops it again (`dropGray`), because by then its leaves *are* in
the accumulator.

On the port's side the invariant is task #47's `MemoInv` at `V := Unit`: the
`seen` table's values carry no information, and what `MemoInv` adds --
"every recorded key is well formed" -- is what makes `expr::eq2`'s exactness
apply at the pairs `seen_get` compares. -/

/-- con-leche's `SeenInv` (`Verify/Cached/GuardsC.lean:409`) as the `Q` of
`MemoInv`: a recorded node's leaves are in the accumulator, *or* the node is
gray. -/
def SeenQ (G : ConLeche.Expr → Prop) (acc : alloc.vec.Vec (Std.U64 × expr.Expr)) :
    ConLeche.Expr → Unit → Prop :=
  fun a _ => (∀ l ∈ ConLeche.Expr.fvarLeaves a, l ∈ absLeaves acc) ∨ G a

/-- `SeenInv.mono`: a bigger accumulator and a bigger gray predicate keep the
invariant. -/
theorem SeenQ_mono {G G' : ConLeche.Expr → Prop}
    {acc acc' : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {seen : ron.hashmap.HashMap expr.Expr Unit}
    (hm : MemoInv ExprWF absExpr (SeenQ G acc) seen)
    (hacc : ∀ l, l ∈ absLeaves acc → l ∈ absLeaves acc')
    (hG : ∀ y, G y → G' y) : MemoInv ExprWF absExpr (SeenQ G' acc') seen :=
  MemoInv_monoQ hm (fun a v hq => by
    rcases hq with hsub | hgray
    · exact Or.inl fun l hl => hacc l (hsub l hl)
    · exact Or.inr (hG _ hgray))

/-- `SeenInv.dropGray`: once the descent is finished and the node's leaves are
in the accumulator, the node leaves the gray set again. -/
theorem SeenQ_dropGray {G : ConLeche.Expr → Prop} {a : ConLeche.Expr}
    {acc : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {seen : ron.hashmap.HashMap expr.Expr Unit}
    (hm : MemoInv ExprWF absExpr (SeenQ (fun y => G y ∨ y = a) acc) seen)
    (ha : ∀ l ∈ ConLeche.Expr.fvarLeaves a, l ∈ absLeaves acc) :
    MemoInv ExprWF absExpr (SeenQ G acc) seen :=
  MemoInv_monoQ hm (fun b v hq => by
    rcases hq with hsub | hgray
    · exact Or.inl hsub
    · rcases hgray with hg | heq
      · exact Or.inr hg
      · exact Or.inl (by rw [heq]; exact ha))

/-- `SeenInv.insertGray`: marking the node about to be descended into. -/
theorem SeenQ_insertGray {G : ConLeche.Expr → Prop} {e e1 : expr.Expr}
    {acc : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {seen seen1 : ron.hashmap.HashMap expr.Expr Unit} {oldv : Option Unit}
    (hm : MemoInv ExprWF absExpr (SeenQ G acc) seen) (hwfe : ExprWF e)
    (hd1 : expr.dup e = ok e1)
    (hins : ron.hashmap.HashMap.insert
        expr.Expr.Insts.Con_ron_coreRonHashmapHashable
        expr.Expr.Insts.Con_ron_coreRonHashmapEq2 seen e1 () = ok (oldv, seen1)) :
    MemoInv ExprWF absExpr (SeenQ (fun y => G y ∨ y = absExpr e) acc) seen1 := by
  rw [Expr.dup_eq hd1] at hins
  refine MemoInv.set expr_key_exact (SeenQ_mono hm (fun _ h => h) (fun _ h => Or.inl h))
    hwfe ?_ hins
  exact Or.inr (Or.inr rfl)

/-- `absLeaves` of a push. -/
theorem absLeaves_push {acc acc1 : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {idx : Std.U64} {ty : expr.Expr}
    (h : alloc.vec.Vec.push acc (idx, ty) = ok acc1) :
    absLeaves acc1 = absLeaves acc ++ [(idx.val, absExpr ty)] := by
  unfold absLeaves; rw [vec_push_val h]; simp

/-- The branches that return the accumulator untouched because the node has no
reachable leaf at all: the `fvarB == 0` cutoff and the four atom arms. -/
theorem leaves_ret_nil {G : ConLeche.Expr → Prop} {a : ConLeche.Expr}
    {acc r : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {seenX seen' : ron.hashmap.HashMap expr.Expr Unit}
    (hacc : LeavesWF acc) (hm : MemoInv ExprWF absExpr (SeenQ G acc) seenX)
    (hnil : ConLeche.Expr.fvarLeaves a = [])
    (h : (ok (acc, seenX) : Result (alloc.vec.Vec (Std.U64 × expr.Expr)
        × ron.hashmap.HashMap expr.Expr Unit)) = ok (r, seen')) :
    (∀ l, l ∈ absLeaves r ↔ l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves a) ∧
      LeavesWF r ∧ MemoInv ExprWF absExpr (SeenQ G r) seen' := by
  have e0 := Result.ok_injective (α := alloc.vec.Vec (Std.U64 × expr.Expr) × _) h
  have ea : acc = r := congrArg Prod.fst e0
  have eb : seenX = seen' := congrArg Prod.snd e0
  subst ea; subst eb
  exact ⟨fun l => by rw [hnil]; simp, hacc, hm⟩

/-- The `seen` hit: the node is recorded, and it cannot be gray, because every
gray node is strictly bigger than the node this call is at. -/
theorem leaves_ret_hit {G : ConLeche.Expr → Prop} {e : expr.Expr}
    {acc r : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {seen seen' : ron.hashmap.HashMap expr.Expr Unit}
    (hacc : LeavesWF acc) (hm : MemoInv ExprWF absExpr (SeenQ G acc) seen)
    (hG : ∀ y, G y → (absExpr e).sizeF < y.sizeF)
    (hget : ∃ u, ron.hashmap.HashMap.get expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 seen e = ok (some u))
    (hwfe : ExprWF e)
    (h : (ok (acc, seen) : Result (alloc.vec.Vec (Std.U64 × expr.Expr)
        × ron.hashmap.HashMap expr.Expr Unit)) = ok (r, seen')) :
    (∀ l, l ∈ absLeaves r ↔
        l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr e)) ∧
      LeavesWF r ∧ MemoInv ExprWF absExpr (SeenQ G r) seen' := by
  have e0 := Result.ok_injective (α := alloc.vec.Vec (Std.U64 × expr.Expr) × _) h
  have ea : acc = r := congrArg Prod.fst e0
  have eb : seen = seen' := congrArg Prod.snd e0
  subst ea; subst eb
  obtain ⟨u, hget⟩ := hget
  have hq := MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := SeenQ G acc)
    expr_key_exact hm hwfe hget
  rcases hq with hsub | hgray
  · exact ⟨fun l => ⟨Or.inl, fun hl => hl.elim id (hsub l)⟩, hacc, hm⟩
  · exact absurd (hG _ hgray) (Nat.lt_irrefl _)

/-- The general statement of the leaf walk: it accumulates exactly the
reachable leaves *as a set* (the `seen` dedup makes the list itself shorter
than `Expr.fvarLeaves`), and restores the `seen` invariant at the caller's gray
predicate.  The induction is the port's own tree: structural on the `ExprWF`
derivation, with `G` and the accumulator generalised. -/
theorem fvar_leaves_go_aux {e : expr.Expr} (he : ExprWF e) :
    ∀ (G : ConLeche.Expr → Prop) (acc r : alloc.vec.Vec (Std.U64 × expr.Expr))
      (seen seen' : ron.hashmap.HashMap expr.Expr Unit),
      LeavesWF acc →
      MemoInv ExprWF absExpr (SeenQ G acc) seen →
      (∀ y, G y → (absExpr e).sizeF < y.sizeF) →
      cached.expr_ops_c.fvar_leaves_go acc seen e = ok (r, seen') →
      (∀ l, l ∈ absLeaves r ↔
          l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr e)) ∧
        LeavesWF r ∧ MemoInv ExprWF absExpr (SeenQ G r) seen' := by
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro G acc r seen seen' hacc hm hG h
    have hnil : ConLeche.Expr.fvarLeaves (absExpr
        (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)))) = [] := by
      simp [absExpr_mk, absExprKind, ConLeche.Expr.fvarLeaves]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact leaves_ret_nil hacc hm hnil h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some u =>
        cases u
        exact leaves_ret_nil hacc hm hnil h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact leaves_ret_nil hacc
          (SeenQ_dropGray hm1 (by rw [hnil]; simp)) hnil h
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro G acc r seen seen' hacc hm hG h
    have hnil : ConLeche.Expr.fvarLeaves (absExpr
        (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.«Sort» u)))) = [] := by
      simp [absExpr_mk, absExprKind, ConLeche.Expr.fvarLeaves]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact leaves_ret_nil hacc hm hnil h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v => cases v; exact leaves_ret_nil hacc hm hnil h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact leaves_ret_nil hacc
          (SeenQ_dropGray hm1 (by rw [hnil]; simp)) hnil h
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro G acc r seen seen' hacc hm hG h
    have hnil : ConLeche.Expr.fvarLeaves (absExpr
        (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n us)))) = [] := by
      simp [absExpr_mk, absExprKind, ConLeche.Expr.fvarLeaves]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact leaves_ret_nil hacc hm hnil h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v => cases v; exact leaves_ret_nil hacc hm hnil h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact leaves_ret_nil hacc
          (SeenQ_dropGray hm1 (by rw [hnil]; simp)) hnil h
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro G acc r seen seen' hacc hm hG h
    have hnil : ConLeche.Expr.fvarLeaves (absExpr
        (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)))) = [] := by
      simp [absExpr_mk, absExprKind, ConLeche.Expr.fvarLeaves]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · exact leaves_ret_nil hacc hm hnil h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v => cases v; exact leaves_ret_nil hacc hm hnil h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        exact leaves_ret_nil hacc
          (SeenQ_dropGray hm1 (by rw [hnil]; simp)) hnil h
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro G acc r seen seen' hacc hm hG h
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))
        = ConLeche.Expr.fvar idx.val (absExpr ty) := by
      simp only [absExpr_mk, absExprKind]
    have hlv : ConLeche.Expr.fvarLeaves (absExpr
          (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty))))
        = (idx.val, absExpr ty) :: ConLeche.Expr.fvarLeaves (absExpr ty) := by
      rw [habse, ConLeche.Expr.fvarLeaves]
    have hsz : (absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.Fvar idx ty)))).sizeF = (absExpr ty).sizeF + 1 := by
      rw [habse, ConLeche.Expr.sizeF]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_ret_nil hacc hm
        (fvar_leaves_cutoff hwfe hfb (by rw [hzc]; scalar_tac)) h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v =>
        cases v
        exact leaves_ret_hit hacc hm hG (seen_get_hit ho) hwfe h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨e2, hd2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨acc1, hpush, h⟩ := bind_eq_ok_iff.mp h
        rw [Expr.dup_eq hd2] at hpush
        have hacc1 : absLeaves acc1 = absLeaves acc ++ [(idx.val, absExpr ty)] :=
          absLeaves_push hpush
        have hwfacc1 : LeavesWF acc1 := by
          intro q hq
          rw [vec_push_val hpush] at hq
          rcases List.mem_append.1 hq with hq | hq
          · exact hacc q hq
          · simp only [List.mem_singleton] at hq; rw [hq]; exact hty
        have hm2 : MemoInv ExprWF absExpr
            (SeenQ (fun y => G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.Fvar idx ty)))) acc1) seen1 :=
          SeenQ_mono hm1 (fun l hl => by rw [hacc1]; exact List.mem_append_left _ hl)
            (fun _ hy => hy)
        have hGty : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.Fvar idx ty)))) → (absExpr ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem2, hwf2, hm3⟩ := ih _ acc1 r seen1 seen' hwfacc1 hm2 hGty h
        have hmem : ∀ l, l ∈ absLeaves r ↔
            l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr
              (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) := by
          intro l
          rw [hmem2 l, hacc1, hlv]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          tauto
        exact ⟨hmem, hwf2, SeenQ_dropGray hm3 (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro G acc r seen seen' hacc hm hG h
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))
        = ConLeche.Expr.app (absExpr f) (absExpr a) := by
      simp only [absExpr_mk, absExprKind]
    have hlv : ConLeche.Expr.fvarLeaves (absExpr
          (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a))))
        = ConLeche.Expr.fvarLeaves (absExpr f) ++ ConLeche.Expr.fvarLeaves (absExpr a) := by
      rw [habse, ConLeche.Expr.fvarLeaves]
    have hsz : (absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.App f a)))).sizeF
        = (absExpr f).sizeF + (absExpr a).sizeF + 1 := by
      rw [habse, ConLeche.Expr.sizeF]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_ret_nil hacc hm
        (fvar_leaves_cutoff hwfe hfb (by rw [hzc]; scalar_tac)) h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v =>
        cases v
        exact leaves_ret_hit hacc hm hG (seen_get_hit ho) hwfe h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨q, h2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨acc2, seen2⟩ := q
        have hGf : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.App f a)))) → (absExpr f).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem2, hwf2, hm2⟩ := ihf _ acc acc2 seen1 seen2 hacc hm1 hGf h2
        have hGa : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.App f a)))) → (absExpr a).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem3, hwf3, hm3⟩ := iha _ acc2 r seen2 seen' hwf2 hm2 hGa h
        have hmem : ∀ l, l ∈ absLeaves r ↔
            l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr
              (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) := by
          intro l
          rw [hmem3 l, hmem2 l, hlv, List.mem_append]
          tauto
        exact ⟨hmem, hwf3, SeenQ_dropGray hm3 (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro G acc r seen seen' hacc hm hG h
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))
        = ConLeche.Expr.lam (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      simp only [absExpr_mk, absExprKind]
    have hlv : ConLeche.Expr.fvarLeaves (absExpr
          (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m))))
        = ConLeche.Expr.fvarLeaves (absExpr ty)
            ++ ConLeche.Expr.fvarLeaves (absExpr bo) := by
      rw [habse, ConLeche.Expr.fvarLeaves]
    have hsz : (absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.Lam ty bo m)))).sizeF
        = (absExpr ty).sizeF + (absExpr bo).sizeF + 1 := by
      rw [habse, ConLeche.Expr.sizeF]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_ret_nil hacc hm
        (fvar_leaves_cutoff hwfe hfb (by rw [hzc]; scalar_tac)) h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v =>
        cases v
        exact leaves_ret_hit hacc hm hG (seen_get_hit ho) hwfe h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨q, h2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨acc2, seen2⟩ := q
        have hGf : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.Lam ty bo m)))) → (absExpr ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem2, hwf2, hm2⟩ := ihty _ acc acc2 seen1 seen2 hacc hm1 hGf h2
        have hGa : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.Lam ty bo m)))) → (absExpr bo).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem3, hwf3, hm3⟩ := ihbo _ acc2 r seen2 seen' hwf2 hm2 hGa h
        have hmem : ∀ l, l ∈ absLeaves r ↔
            l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr
              (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) := by
          intro l
          rw [hmem3 l, hmem2 l, hlv, List.mem_append]
          tauto
        exact ⟨hmem, hwf3, SeenQ_dropGray hm3 (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro G acc r seen seen' hacc hm hG h
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.ForallE ty bo m)))
        = ConLeche.Expr.forallE (absExpr ty) (absExpr bo) (absBinderMeta m) := by
      simp only [absExpr_mk, absExprKind]
    have hlv : ConLeche.Expr.fvarLeaves (absExpr
          (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m))))
        = ConLeche.Expr.fvarLeaves (absExpr ty)
            ++ ConLeche.Expr.fvarLeaves (absExpr bo) := by
      rw [habse, ConLeche.Expr.fvarLeaves]
    have hsz : (absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.ForallE ty bo m)))).sizeF
        = (absExpr ty).sizeF + (absExpr bo).sizeF + 1 := by
      rw [habse, ConLeche.Expr.sizeF]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_ret_nil hacc hm
        (fvar_leaves_cutoff hwfe hfb (by rw [hzc]; scalar_tac)) h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v =>
        cases v
        exact leaves_ret_hit hacc hm hG (seen_get_hit ho) hwfe h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨q, h2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨acc2, seen2⟩ := q
        have hGf : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.ForallE ty bo m)))) → (absExpr ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem2, hwf2, hm2⟩ := ihty _ acc acc2 seen1 seen2 hacc hm1 hGf h2
        have hGa : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.ForallE ty bo m)))) → (absExpr bo).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem3, hwf3, hm3⟩ := ihbo _ acc2 r seen2 seen' hwf2 hm2 hGa h
        have hmem : ∀ l, l ∈ absLeaves r ↔
            l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr
              (expr.Expr.mk (expr.ExprNode.mk d1
                (expr.ExprKind.ForallE ty bo m)))) := by
          intro l
          rw [hmem3 l, hmem2 l, hlv, List.mem_append]
          tauto
        exact ⟨hmem, hwf3, SeenQ_dropGray hm3 (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | @let_e ty vv bo e hty hvv hbo h1 ihty ihvv ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hvv hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro G acc r seen seen' hacc hm hG h
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.LetE ty vv bo)))
        = ConLeche.Expr.letE (absExpr ty) (absExpr vv) (absExpr bo) := by
      simp only [absExpr_mk, absExprKind]
    have hlv : ConLeche.Expr.fvarLeaves (absExpr
          (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty vv bo))))
        = ConLeche.Expr.fvarLeaves (absExpr ty)
            ++ ConLeche.Expr.fvarLeaves (absExpr vv)
            ++ ConLeche.Expr.fvarLeaves (absExpr bo) := by
      rw [habse, ConLeche.Expr.fvarLeaves]
    have hsz : (absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.LetE ty vv bo)))).sizeF
        = (absExpr ty).sizeF + (absExpr vv).sizeF + (absExpr bo).sizeF + 1 := by
      rw [habse, ConLeche.Expr.sizeF]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_ret_nil hacc hm
        (fvar_leaves_cutoff hwfe hfb (by rw [hzc]; scalar_tac)) h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v =>
        cases v
        exact leaves_ret_hit hacc hm hG (seen_get_hit ho) hwfe h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        obtain ⟨q, h2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨acc2, seen2⟩ := q
        obtain ⟨q3, h3, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨acc3, seen3⟩ := q3
        have hG1 : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.LetE ty vv bo)))) → (absExpr ty).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem2, hwf2, hm2⟩ := ihty _ acc acc2 seen1 seen2 hacc hm1 hG1 h2
        have hG2 : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.LetE ty vv bo)))) → (absExpr vv).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem3, hwf3, hm3⟩ := ihvv _ acc2 acc3 seen2 seen3 hwf2 hm2 hG2 h3
        have hG3 : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.LetE ty vv bo)))) → (absExpr bo).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem4, hwf4, hm4⟩ := ihbo _ acc3 r seen3 seen' hwf3 hm3 hG3 h
        have hmem : ∀ l, l ∈ absLeaves r ↔
            l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr
              (expr.Expr.mk (expr.ExprNode.mk d1
                (expr.ExprKind.LetE ty vv bo)))) := by
          intro l
          rw [hmem4 l, hmem3 l, hmem2 l, hlv]
          simp only [List.mem_append]
          tauto
        exact ⟨hmem, hwf4, SeenQ_dropGray hm4 (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro G acc r seen seen' hacc hm hG h
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)))
        = ConLeche.Expr.proj (absName s) i.val (absExpr x) := by
      simp only [absExpr_mk, absExprKind]
    have hlv : ConLeche.Expr.fvarLeaves (absExpr
          (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x))))
        = ConLeche.Expr.fvarLeaves (absExpr x) := by
      rw [habse, ConLeche.Expr.fvarLeaves]
    have hsz : (absExpr (expr.Expr.mk (expr.ExprNode.mk d1
          (expr.ExprKind.Proj s i x)))).sizeF = (absExpr x).sizeF + 1 := by
      rw [habse, ConLeche.Expr.sizeF]
    rw [cached.expr_ops_c.fvar_leaves_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_ret_nil hacc hm
        (fvar_leaves_cutoff hwfe hfb (by rw [hzc]; scalar_tac)) h
    · obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some v =>
        cases v
        exact leaves_ret_hit hacc hm hG (seen_get_hit ho) hwfe h
      | none =>
        obtain ⟨e1, hd1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨oldv, seen1⟩ := p
        have hm1 := SeenQ_insertGray hm hwfe hd1 hins
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        have hGx : ∀ y, (G y ∨ y = absExpr (expr.Expr.mk (expr.ExprNode.mk d1
              (expr.ExprKind.Proj s i x)))) → (absExpr x).sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy, hsz]; omega
        obtain ⟨hmem2, hwf2, hm2⟩ := ih _ acc r seen1 seen' hacc hm1 hGx h
        have hmem : ∀ l, l ∈ absLeaves r ↔
            l ∈ absLeaves acc ∨ l ∈ ConLeche.Expr.fvarLeaves (absExpr
              (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)))) := by
          intro l
          rw [hmem2 l, hlv]
        exact ⟨hmem, hwf2, SeenQ_dropGray hm2 (fun l hl => (hmem l).mpr (Or.inr hl))⟩

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
  obtain ⟨hmem, hwf, -⟩ :=
    fvar_leaves_go_aux he (fun _ => False) acc r seen seen' hacc
      (MemoInv.empty hseen) (fun _ hy => hy.elim) h
  exact ⟨hmem, hwf⟩

/-- **`expr_ops_c::fvar_leaves` refines `Expr.fvarLeavesC`**
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

Discharged in task #54: the walk *is* `wscoped_b_go_refines` node for node, with
`leaf_mem_refines` in place of the scope test and the node-only key
(`expr_key_exact`), and the three short-circuiting callees are inverted by the
same `*_inv` idiom.  `leaf_guard_refines` additionally needs the set-invariance
of `List.all (B.contains ·)` (`all_contains_congr` below), which is where
`fvar_leaves_refines`' membership-only claim meets a cited definition that folds
over the list, and `leafMem_contains`, which reads `leaf_mem_refines`' `leafMem`
as the statements' `List.contains`.  `Expr.fvarLeaves` is a well-founded
recursion, so its arm equations have to be named (`fvl_*`; con-leche's own are
`private`). -/

/-- con-leche's `MemoSubInv` (`Verify/Cached/GuardsC.lean:857`), as the `Q` of
`MemoInv`: every recorded answer is the real subset test. -/
def LeafSubQ (B : List (Nat × ConLeche.Expr)) : ConLeche.Expr → Bool → Prop :=
  fun key r => r = (ConLeche.Expr.fvarLeaves key).all (fun l => B.contains l)

/-! ### The `fvarLeaves` arm equations

`Expr.fvarLeaves` is defined by well-founded recursion (it descends the `fvar`
annotations), so its arms are named here the way con-leche's `private`
`fvarLeaves_*` do. -/

theorem fvl_bvar (i : Nat) : ConLeche.Expr.fvarLeaves (.bvar i) = [] := by
  simp [ConLeche.Expr.fvarLeaves]

theorem fvl_sort (u : ConLeche.Level) : ConLeche.Expr.fvarLeaves (.sort u) = [] := by
  simp [ConLeche.Expr.fvarLeaves]

theorem fvl_const (n : ConLeche.Name) (us : List ConLeche.Level) :
    ConLeche.Expr.fvarLeaves (.const n us) = [] := by simp [ConLeche.Expr.fvarLeaves]

theorem fvl_lit (l : ConLeche.Literal) : ConLeche.Expr.fvarLeaves (.lit l) = [] := by
  simp [ConLeche.Expr.fvarLeaves]

theorem fvl_fvar (idx : Nat) (ty : ConLeche.Expr) :
    ConLeche.Expr.fvarLeaves (.fvar idx ty)
      = (idx, ty) :: ConLeche.Expr.fvarLeaves ty := by rw [ConLeche.Expr.fvarLeaves]

theorem fvl_app (f a : ConLeche.Expr) :
    ConLeche.Expr.fvarLeaves (.app f a)
      = ConLeche.Expr.fvarLeaves f ++ ConLeche.Expr.fvarLeaves a := by
  rw [ConLeche.Expr.fvarLeaves]

theorem fvl_lam (ty b : ConLeche.Expr) (m : ConLeche.BinderMeta) :
    ConLeche.Expr.fvarLeaves (.lam ty b m)
      = ConLeche.Expr.fvarLeaves ty ++ ConLeche.Expr.fvarLeaves b := by
  rw [ConLeche.Expr.fvarLeaves]

theorem fvl_forallE (ty b : ConLeche.Expr) (m : ConLeche.BinderMeta) :
    ConLeche.Expr.fvarLeaves (.forallE ty b m)
      = ConLeche.Expr.fvarLeaves ty ++ ConLeche.Expr.fvarLeaves b := by
  rw [ConLeche.Expr.fvarLeaves]

theorem fvl_letE (ty v b : ConLeche.Expr) :
    ConLeche.Expr.fvarLeaves (.letE ty v b)
      = ConLeche.Expr.fvarLeaves ty ++ ConLeche.Expr.fvarLeaves v
          ++ ConLeche.Expr.fvarLeaves b := by rw [ConLeche.Expr.fvarLeaves]

theorem fvl_proj (s : ConLeche.Name) (i : Nat) (e : ConLeche.Expr) :
    ConLeche.Expr.fvarLeaves (.proj s i e) = ConLeche.Expr.fvarLeaves e := by
  rw [ConLeche.Expr.fvarLeaves]

/-- `leafMem` on one list *is* that list's `contains`: con-leche's `leafMem_spec`
at the reflexive `LeafBase` (`Expr` and `Expr` are the one type since its task
#172, so the erasure of a leaf list is the list). -/
theorem leafMem_contains (L : List (Nat × ConLeche.Expr)) (idx : Nat)
    (ty : ConLeche.Expr) :
    ConLeche.Expr.leafMem L idx ty = L.contains (idx, ty) :=
  ConLeche.Expr.leafMem_spec (B' := L)
    (by intro l; simp [ConLeche.Expr.leavesEr])

/-- **The set-invariance of `List.all (B.contains ·)`**: two base lists with the
same members accept the same leaf lists.  This is what turns
`fvar_leaves_refines`' membership-only claim into the cited `leafGuard`'s
`List.all`. -/
theorem all_contains_congr {A B : List (Nat × ConLeche.Expr)}
    (h : ∀ l, l ∈ A ↔ l ∈ B) (L : List (Nat × ConLeche.Expr)) :
    (L.all fun l => A.contains l) = (L.all fun l => B.contains l) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.all_cons, List.all_cons, ih]
    congr 1
    simp only [List.contains_eq_mem, decide_eq_decide]
    exact h x

/-! ### The cutoff and the three callee inversions -/

/-- The `fvarB == 0` shortcut at the head of `leaves_sub_go`. -/
theorem leaves_sub_cutoff {bl : alloc.vec.Vec (Std.U64 × expr.Expr)} {fb : Std.U64}
    {e : expr.Expr} {b : Bool}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool}
    (hwfe : ExprWF e) (hm : MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo)
    (hfb : expr_ops.fvar_b e = ok fb) (hz : fb.val = 0)
    (h : (ok (true, memo) : Result (Bool × ron.hashmap.HashMap expr.Expr Bool))
      = ok (b, memo')) :
    b = (ConLeche.Expr.fvarLeaves (absExpr e)).all
          (fun l => (absLeaves bl).contains l) ∧
      MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo' := by
  have e0 := Result.ok_injective (α := Bool × _) h
  have ea : true = b := congrArg Prod.fst e0
  have eb : memo = memo' := congrArg Prod.snd e0
  rw [← ea, ← eb]
  refine ⟨?_, hm⟩
  have hz' : (absExpr e).fvarB ≤ 0 := by
    rw [← fvar_b_refines hwfe hfb]; omega
  rw [fvarLeaves_nil_of_fvarsBelow_zero _ (ConLeche.Expr.fvarB_le hz')]
  rfl

/-- Inverting `leaves_sub_fvar`: the annotation is walked only when the leaf is
in the base list. -/
theorem leaves_sub_fvar_inv {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {idx : Std.U64}
    {ty : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.leaves_sub_fvar bl memo idx ty = ok (b, memo')) :
    ∃ lm, cached.expr_ops_c.leaf_mem bl idx ty = ok lm ∧
      (lm = true ∧ cached.expr_ops_c.leaves_sub_go bl memo ty = ok (b, memo')
        ∨ lm = false ∧ b = false ∧ memo = memo') := by
  rw [cached.expr_ops_c.leaves_sub_fvar] at h
  obtain ⟨lm, hlm, h⟩ := bind_eq_ok_iff.mp h
  refine ⟨lm, hlm, ?_⟩
  cases lm with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memo) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memo = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-- Inverting `leaves_sub_pair`: the first child is always walked, the second
only when it answered `true`.  The generated body binds the first answer in a
pattern `let`, which no tactic sees through, so the inversion is done by `exact`
(definitional unfolding). -/
theorem leaves_sub_pair_inv {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {x y : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.leaves_sub_pair bl memo x y = ok (b, memo')) :
    ∃ bx memoX, cached.expr_ops_c.leaves_sub_go bl memo x = ok (bx, memoX) ∧
      (bx = true ∧ cached.expr_ops_c.leaves_sub_go bl memoX y = ok (b, memo')
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.leaves_sub_pair] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-- Inverting `leaves_sub_triple`, the `.letE` arm's three-child short-circuit:
the first child, then the remaining two as a `leaves_sub_pair`. -/
theorem leaves_sub_triple_inv {bl : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {x y z : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.leaves_sub_triple bl memo x y z = ok (b, memo')) :
    ∃ bx memoX, cached.expr_ops_c.leaves_sub_go bl memo x = ok (bx, memoX) ∧
      (bx = true ∧ cached.expr_ops_c.leaves_sub_pair bl memoX y z = ok (b, memo')
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.leaves_sub_triple] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-! ### The walk -/

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
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : LeafSubQ (absLeaves bl)
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)))) true := by
        simp [LeafSubQ, fvl_bvar]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := LeafSubQ (absLeaves bl)) expr_key_exact hm hwfe (memo_b_get_hit ho), hm⟩
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.leaves_sub_fvar bl memo idx ty = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1' := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1'
          have eb : v1 = r0 := congrArg Prod.snd e1'
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            LeafSubQ (absLeaves bl)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) r0 ∧
              MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo1 := by
          obtain ⟨lm, hlm, hrest⟩ := leaves_sub_fvar_inv hfix
          have hlm' : lm = (absLeaves bl).contains (idx.val, absExpr ty) := by
            rw [leaf_mem_refines hbl hty hlm, leafMem_contains]
          rcases hrest with ⟨hlt, hgo⟩ | ⟨hlf, hb0, hmm0⟩
          · obtain ⟨hbt, hmT⟩ := ih memo memo1 r0 hm hgo
            refine ⟨?_, hmT⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hbt, fvl_fvar, List.all_cons, ← hlm', hlt]
            simp
          · rw [← hmm0] at *
            refine ⟨?_, hm⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hb0, fvl_fvar, List.all_cons, ← hlm', hlf]
            simp
        rw [Expr.dup_eq hd1] at hins
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set expr_key_exact hmF hwfe hans hins⟩
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : LeafSubQ (absLeaves bl)
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.«Sort» u)))) true := by
        simp [LeafSubQ, fvl_sort]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @mk_const n vs e hn hvs h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hvs h1
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : LeafSubQ (absLeaves bl)
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n vs)))) true := by
        simp [LeafSubQ, fvl_const]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      have e0 := Result.ok_injective (α := Bool × _) h
      have er : true = b := congrArg Prod.fst e0
      have em : memo = memo' := congrArg Prod.snd e0
      have hans : LeafSubQ (absLeaves bl)
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)))) true := by
        simp [LeafSubQ, fvl_lit]
      rw [← er, ← em]
      exact ⟨hans, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := LeafSubQ (absLeaves bl)) expr_key_exact hm hwfe (memo_b_get_hit ho), hm⟩
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.leaves_sub_pair bl memo f a = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1' := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1'
          have eb : v1 = r0 := congrArg Prod.snd e1'
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            LeafSubQ (absLeaves bl)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) r0 ∧
              MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := leaves_sub_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihf memo memoX bx hm hx
          rcases hrest with ⟨rfl, hy⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨hby, hmY⟩ := iha memoX memo1 r0 hmX hy
            refine ⟨?_, hmY⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hby, fvl_app, List.all_append, ← hbx]
            simp
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hb0, fvl_app, List.all_append, ← hbx]
            simp
        rw [Expr.dup_eq hd1] at hins
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set expr_key_exact hmF hwfe hans hins⟩
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := LeafSubQ (absLeaves bl)) expr_key_exact hm hwfe (memo_b_get_hit ho), hm⟩
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.leaves_sub_pair bl memo ty bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1' := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1'
          have eb : v1 = r0 := congrArg Prod.snd e1'
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            LeafSubQ (absLeaves bl)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r0 ∧
              MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := leaves_sub_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX bx hm hx
          rcases hrest with ⟨rfl, hy⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨hby, hmY⟩ := ihbo memoX memo1 r0 hmX hy
            refine ⟨?_, hmY⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hby, fvl_lam, List.all_append, ← hbx]
            simp
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hb0, fvl_lam, List.all_append, ← hbx]
            simp
        rw [Expr.dup_eq hd1] at hins
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set expr_key_exact hmF hwfe hans hins⟩
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := LeafSubQ (absLeaves bl)) expr_key_exact hm hwfe (memo_b_get_hit ho), hm⟩
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.leaves_sub_pair bl memo ty bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1' := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1'
          have eb : v1 = r0 := congrArg Prod.snd e1'
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            LeafSubQ (absLeaves bl)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r0 ∧
              MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := leaves_sub_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX bx hm hx
          rcases hrest with ⟨rfl, hy⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨hby, hmY⟩ := ihbo memoX memo1 r0 hmX hy
            refine ⟨?_, hmY⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hby, fvl_forallE, List.all_append, ← hbx]
            simp
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hb0, fvl_forallE, List.all_append, ← hbx]
            simp
        rw [Expr.dup_eq hd1] at hins
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set expr_key_exact hmF hwfe hans hins⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := LeafSubQ (absLeaves bl)) expr_key_exact hm hwfe (memo_b_get_hit ho), hm⟩
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.leaves_sub_triple bl memo ty w bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1' := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1'
          have eb : v1 = r0 := congrArg Prod.snd e1'
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            LeafSubQ (absLeaves bl)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)))) r0 ∧
              MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo1 := by
          obtain ⟨bx, memoX, hx, hrest⟩ := leaves_sub_triple_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX bx hm hx
          rcases hrest with ⟨rfl, hyz⟩ | ⟨rfl, hb0, hmm0⟩
          · obtain ⟨by0, memoY, hy, hrest2⟩ := leaves_sub_pair_inv hyz
            obtain ⟨hby, hmY⟩ := ihw memoX memoY by0 hmX hy
            rcases hrest2 with ⟨rfl, hz2⟩ | ⟨rfl, hb1, hmm1⟩
            · obtain ⟨hbz, hmZ⟩ := ihbo memoY memo1 r0 hmY hz2
              refine ⟨?_, hmZ⟩
              simp only [LeafSubQ, absExpr_mk, absExprKind]
              rw [hbz, fvl_letE, List.all_append, List.all_append, ← hbx, ← hby]
              simp
            · rw [← hmm1] at *
              refine ⟨?_, hmY⟩
              simp only [LeafSubQ, absExpr_mk, absExprKind]
              rw [hb1, fvl_letE, List.all_append, List.all_append, ← hbx, ← hby]
              simp
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [LeafSubQ, absExpr_mk, absExprKind]
            rw [hb0, fvl_letE, List.all_append, List.all_append, ← hbx]
            simp
        rw [Expr.dup_eq hd1] at hins
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set expr_key_exact hmF hwfe hans hins⟩
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.leaves_sub_go.eq_def] at h
    obtain ⟨fb, hfb, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hzc
      exact leaves_sub_cutoff hwfe hm hfb (by rw [hzc]; scalar_tac) h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some wv =>
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : wv = b := congrArg Prod.fst e0
        have eb : memo = memo' := congrArg Prod.snd e0
        rw [← ea, ← eb]
        exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr)
          (Q := LeafSubQ (absLeaves bl)) expr_key_exact hm hwfe (memo_b_get_hit ho), hm⟩
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memoZ, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have er : r0 = b := congrArg Prod.fst e0
        have em : memoZ = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.leaves_sub_go bl memo x = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have e1' := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea : m1 = memo1 := congrArg Prod.fst e1'
          have eb : v1 = r0 := congrArg Prod.snd e1'
          rw [← ea, ← eb]; exact hp1
        obtain ⟨hans, hmF⟩ :
            LeafSubQ (absLeaves bl)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)))) r0 ∧
              MemoInv ExprWF absExpr (LeafSubQ (absLeaves bl)) memo1 := by
          obtain ⟨hb1, hmF⟩ := ih memo memo1 r0 hm hfix
          refine ⟨?_, hmF⟩
          simp only [LeafSubQ, absExpr_mk, absExprKind]
          rw [hb1, fvl_proj]
        rw [Expr.dup_eq hd1] at hins
        rw [← er, ← em]
        exact ⟨hans, MemoInv.set expr_key_exact hmF hwfe hans hins⟩

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
  obtain ⟨lm, hlm, hrest⟩ := leaves_sub_fvar_inv h
  have hlm' : lm = (absLeaves bl).contains (idx.val, absExpr ty) := by
    rw [leaf_mem_refines hbl hty hlm, leafMem_contains]
  rcases hrest with ⟨hlt, hgo⟩ | ⟨hlf, hb0, hmm0⟩
  · obtain ⟨hbt, hmT⟩ := leaves_sub_go_refines hbl hty memo memo' b hm hgo
    refine ⟨?_, hmT⟩
    rw [hbt, ← hlm', hlt]
    simp
  · rw [← hmm0] at *
    refine ⟨?_, hm⟩
    rw [hb0, ← hlm', hlf]
    simp

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
  obtain ⟨bx, memoX, hxr, hrest⟩ := leaves_sub_pair_inv h
  obtain ⟨hbx, hmX⟩ := leaves_sub_go_refines hbl hx memo memoX bx hm hxr
  rcases hrest with ⟨rfl, hyr⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hby, hmY⟩ := leaves_sub_go_refines hbl hy memoX memo' b hmX hyr
    exact ⟨by rw [hby, ← hbx]; simp, hmY⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

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
  obtain ⟨bx, memoX, hxr, hrest⟩ := leaves_sub_triple_inv h
  obtain ⟨hbx, hmX⟩ := leaves_sub_go_refines hbl hx memo memoX bx hm hxr
  rcases hrest with ⟨rfl, hyz⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hbyz, hmYZ⟩ := leaves_sub_pair_refines hbl hy hz hmX hyz
    exact ⟨by rw [hbyz, ← hbx]; simp, hmYZ⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

/-- **`expr_ops_c::leaf_guard` refines `Expr.leafGuard`**
(`ExprOpsC.lean:744-748`): `O(1)` true off the cached range on an `fvar`-free
fabrication, otherwise the leaf walk of the subject and the subset walk of the
fabrication (`leafGuard_spec`, `Verify/Cached/GuardsC.lean:1136`). -/
theorem leaf_guard_refines {fab base : expr.Expr} {b : Bool} (hfab : ExprWF fab)
    (hbase : ExprWF base) (h : cached.expr_ops_c.leaf_guard fab base = ok b) :
    b = ConLeche.Expr.leafGuard (absExpr fab) (absExpr base) := by
  rw [ConLeche.Expr.leafGuard_spec]
  rw [cached.expr_ops_c.leaf_guard] at h
  obtain ⟨hf, hhf, h⟩ := bind_eq_ok_iff.mp h
  rw [cached.expr_ops_c.has_fvar] at hhf
  obtain ⟨fb, hfb, hhf⟩ := bind_eq_ok_iff.mp hhf
  have hfbv : fb.val = (absExpr fab).fvarB := fvar_b_refines hfab hfb
  have hhf' : hf = (fb != 0#u64) := (Result.ok_injective hhf).symm
  split at h
  · rename_i hc
    obtain ⟨bl, hblr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, memoX⟩ := p
    have hb1 : b1 = b := Result.ok_injective h
    subst hb1
    obtain ⟨hset, hwf⟩ := fvar_leaves_refines hbase hblr
    obtain ⟨hb, -⟩ := leaves_sub_go_refines hwf hfab memo memoX b1
      (new_memo_inv hnew) hgo
    rw [hb]
    exact all_contains_congr hset _
  · rename_i hc
    have hz : (absExpr fab).fvarB ≤ 0 := by
      rw [← hfbv]
      have hff : hf = false := by
        cases hf with
        | true => exact absurd rfl hc
        | false => rfl
      rw [hff] at hhf'
      have hfz : fb = 0#u64 := by
        by_cases hq : fb = 0#u64
        · exact hq
        · simp [hq] at hhf'
      rw [hfz]; scalar_tac
    have hnil := fvarLeaves_nil_of_fvarsBelow_zero _
      (ConLeche.Expr.fvarB_le hz)
    have hb : true = b := Result.ok_injective h
    rw [← hb, hnil]
    rfl

/-! ## Level-parameter definedness (`ExprOpsC.lean:791-828`)

`wscopedB`'s shape again -- probe before the match, short-circuiting callees --
with one documented exception: the two binder arms conjoin the body's answer with
the binder datum's through `expr_ops::bool_and`, *not* a short-circuit, because
the cited `(rb && m.pw.paramsDefined params, memo)` has already computed both
(task #24's rule, the module's note 4).

Discharged in task #54: the walk is `wscoped_b_go_refines` node for node, at the
node-only key, with `level::all_params_defined` /
`expr_ops::levels_all_params_defined` / `prop_when::params_defined` in the leaf
and binder arms (all three already refined, in `Refine/ExprOpsMeta.lean` and
`Refine/PropWhen.lean`).  The head shortcut `!expr::has_lp` is `alpd_cutoff`
below -- the definedness analogue of `ExprOpsCAbs`'s `ilp_cutoff`, off
con-leche's `allLevelParamsDefined_of_not_hasLevelParam` -- and `alpd_hit`
factors the node-keyed memo probe out of the ten induction cases. -/

/-- con-leche's `MemoLPDInv` (`Verify/Cached/GuardsC.lean:70`), as the `Q` of
`MemoInv`. -/
def ALPDQ (ps : List ConLeche.Name) : ConLeche.Expr → Bool → Prop :=
  fun key r => r = ConLeche.Expr.allLevelParamsDefined ps key

/-! ## The head cutoff and the memo hit

Both are node-kind-independent, so they are factored out of the ten cases of
the induction. -/

/-- The `!expr::has_lp(e)` shortcut at the head of
`all_level_params_defined_go`: the packed word's bit says the node mentions no
level parameter, and then definedness is vacuous -- con-leche's
`Expr.allLevelParamsDefined_of_not_hasLevelParam` (`Kernel/ExprOps.lean:2728`)
through `Expr.hasLP_eq` (`:2538`). -/
theorem alpd_cutoff {params : alloc.vec.Vec name.Name} {e : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (he : ExprWF e) (hm : MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo)
    (hlp : expr.has_lp e = ok false)
    (h : (ok (true, memo) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo')) :
    b = ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr e) ∧
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  have e0 := Result.ok_injective (α := Bool × _) h
  have ea : true = b := congrArg Prod.fst e0
  have eb : memo = memo' := congrArg Prod.snd e0
  rw [← ea, ← eb]
  refine ⟨?_, hm⟩
  have hlp' : (absExpr e).hasLP = false := (Expr.has_lp_refines he hlp).symm
  rw [ConLeche.Expr.Expr.hasLP_eq] at hlp'
  exact (ConLeche.Expr.allLevelParamsDefined_of_not_hasLevelParam hlp').symm

/-- A hit on the node-keyed memo is the real answer (`MemoLPDInv`'s use). -/
theorem alpd_hit {params : alloc.vec.Vec name.Name} {e : expr.Expr}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b w : Bool}
    (he : ExprWF e) (hm : MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo)
    (ho : expr_ops.memo_b_get memo e = ok (some w))
    (h : (ok (w, memo) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo')) :
    b = ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr e) ∧
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  have e0 := Result.ok_injective (α := Bool × _) h
  have ea : w = b := congrArg Prod.fst e0
  have eb : memo = memo' := congrArg Prod.snd e0
  rw [← ea, ← eb]
  exact ⟨MemoInv.hit (KWF := ExprWF) (absK := absExpr) (Q := ALPDQ (absNames params))
    expr_key_exact hm he (memo_b_get_hit ho), hm⟩

/-! ## Inverting the three branching callees

Each binds its first child's answer in a pattern `let`, which `split` and
`simp` do not see through, so the short-circuit is exposed here by `exact`
(definitional unfolding). -/

/-- Inverting `alpd_pair`: the second child is walked only when the first
answered `true`. -/
theorem alpd_pair_inv {params : alloc.vec.Vec name.Name}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {x y : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.alpd_pair params memo x y = ok (b, memo')) :
    ∃ bx memoX,
      cached.expr_ops_c.all_level_params_defined_go params memo x = ok (bx, memoX) ∧
      (bx = true ∧
          cached.expr_ops_c.all_level_params_defined_go params memoX y = ok (b, memo')
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.alpd_pair] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-- Inverting `alpd_triple`, the `.letE` arm: the first child, then the
remaining two as an `alpd_pair`. -/
theorem alpd_triple_inv {params : alloc.vec.Vec name.Name}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {x y z : expr.Expr} {b : Bool}
    (h : cached.expr_ops_c.alpd_triple params memo x y z = ok (b, memo')) :
    ∃ bx memoX,
      cached.expr_ops_c.all_level_params_defined_go params memo x = ok (bx, memoX) ∧
      (bx = true ∧ cached.expr_ops_c.alpd_pair params memoX y z = ok (b, memo')
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.alpd_triple] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true => exact Or.inl ⟨rfl, h⟩
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-- Inverting `alpd_binder`: the domain short-circuits, and on `true` the body
*and* the binder datum are both run, their answers joined by
`expr_ops::bool_and` (module note 4). -/
theorem alpd_binder_inv {params : alloc.vec.Vec name.Name}
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {ty bo : expr.Expr}
    {pw : prop_when.PropWhen} {b : Bool}
    (h : cached.expr_ops_c.alpd_binder params memo ty bo pw = ok (b, memo')) :
    ∃ bx memoX,
      cached.expr_ops_c.all_level_params_defined_go params memo ty = ok (bx, memoX) ∧
      (bx = true ∧ (∃ rb rp,
            cached.expr_ops_c.all_level_params_defined_go params memoX bo
              = ok (rb, memo') ∧
            prop_when.params_defined params pw = ok rp ∧ b = (rb && rp))
        ∨ bx = false ∧ b = false ∧ memoX = memo') := by
  rw [cached.expr_ops_c.alpd_binder] at h
  obtain ⟨p, hx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bx, memoX⟩ := p
  refine ⟨bx, memoX, hx, ?_⟩
  cases bx with
  | true =>
    obtain ⟨p2, hy, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨rb, memo2⟩ := p2
    obtain ⟨rp, hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hand, h⟩ := bind_eq_ok_iff.mp h
    have hb1 : b1 = (rb && rp) := by
      rw [bool_and_val] at hand; exact (Result.ok_injective hand).symm
    have e0 := Result.ok_injective (α := Bool × _) h
    have ea : b1 = b := congrArg Prod.fst e0
    have eb : memo2 = memo' := congrArg Prod.snd e0
    refine Or.inl ⟨rfl, rb, rp, ?_, hp, by rw [← ea, hb1]⟩
    rw [← eb]; exact hy
  | false =>
    have h2 : (ok (false, memoX) :
        Result (Bool × ron.hashmap.HashMap expr.Expr Bool)) = ok (b, memo') := h
    have e0 := Result.ok_injective (α := Bool × _) h2
    have ea : false = b := congrArg Prod.fst e0
    have eb : memoX = memo' := congrArg Prod.snd e0
    exact Or.inr ⟨rfl, ea.symm, eb⟩

/-! ## The walk -/

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
  induction he with
  | @bvar i e h1 =>
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      have e0 := Result.ok_injective (α := Bool × _) h
      have ea : true = b := congrArg Prod.fst e0
      have eb : memo = memo' := congrArg Prod.snd e0
      have hans : ALPDQ (absNames params)
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Bvar i)))) true := by
        simp [ALPDQ, ConLeche.Expr.allLevelParamsDefined]
      rw [← ea, ← eb]
      exact ⟨hans, hm⟩
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @lit l e hl h1 =>
    have hwfe : ExprWF e := ExprWF.lit hl h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      have e0 := Result.ok_injective (α := Bool × _) h
      have ea : true = b := congrArg Prod.fst e0
      have eb : memo = memo' := congrArg Prod.snd e0
      have hans : ALPDQ (absNames params)
          (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lit l)))) true := by
        simp [ALPDQ, ConLeche.Expr.allLevelParamsDefined]
      rw [← ea, ← eb]
      exact ⟨hans, hm⟩
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @sort u e hu h1 =>
    have hwfe : ExprWF e := ExprWF.sort hu h1
    obtain ⟨d1, bq, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      have e0 := Result.ok_injective (α := Bool × _) h
      have ea : r0 = b := congrArg Prod.fst e0
      have eb : memo1 = memo' := congrArg Prod.snd e0
      obtain ⟨hans, hmF⟩ :
          ALPDQ (absNames params)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.«Sort» u)))) r0 ∧
            MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
        obtain ⟨r1, hr1, hq⟩ := bind_eq_ok_iff.mp hq
        have eq1 := Result.ok_injective
          (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq
        have em1 : memo = memo1 := congrArg Prod.fst eq1
        have er1 : r1 = r0 := congrArg Prod.snd eq1
        refine ⟨?_, by rw [← em1]; exact hm⟩
        simp only [ALPDQ, absExpr_mk, absExprKind]
        rw [← er1, all_params_defined_refines hps u hu r1 hr1]
        simp [ConLeche.Expr.allLevelParamsDefined]
      rw [← ea, ← eb]
      exact ⟨hans, hmF⟩
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @mk_const n us e hn hus h1 =>
    have hwfe : ExprWF e := ExprWF.mk_const hn hus h1
    obtain ⟨d1, bq, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_false, memo_b_probe_true, memo_b_record_true] at h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      have e0 := Result.ok_injective (α := Bool × _) h
      have ea : r0 = b := congrArg Prod.fst e0
      have eb : memo1 = memo' := congrArg Prod.snd e0
      obtain ⟨hans, hmF⟩ :
          ALPDQ (absNames params)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Const n us)))) r0 ∧
            MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
        obtain ⟨r1, hr1, hq⟩ := bind_eq_ok_iff.mp hq
        have eq1 := Result.ok_injective
          (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq
        have em1 : memo = memo1 := congrArg Prod.fst eq1
        have er1 : r1 = r0 := congrArg Prod.snd eq1
        refine ⟨?_, by rw [← em1]; exact hm⟩
        simp only [ALPDQ, absExpr_mk, absExprKind]
        rw [← er1, levels_all_params_defined_refines hps hus us.val.length 0#usize r1
          (by scalar_tac) hr1]
        simp [ConLeche.Expr.allLevelParamsDefined, absLevels]
      rw [← ea, ← eb]
      exact ⟨hans, hmF⟩
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @fvar idx ty e hty h1 ih =>
    have hwfe : ExprWF e := ExprWF.fvar hty h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w => exact alpd_hit hwfe hm ho h
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memo3, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : r0 = b := congrArg Prod.fst e0
        have eb : memo3 = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.all_level_params_defined_go params memo ty
            = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have eq1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea2 : m1 = memo1 := congrArg Prod.fst eq1
          have eb2 : v1 = r0 := congrArg Prod.snd eq1
          rw [← ea2, ← eb2]; exact hp1
        obtain ⟨hans, hmF⟩ :
            ALPDQ (absNames params)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Fvar idx ty)))) r0 ∧
              MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
          obtain ⟨hb1, hmF⟩ := ih memo memo1 r0 hm hfix
          refine ⟨?_, hmF⟩
          simp only [ALPDQ, absExpr_mk, absExprKind]
          rw [hb1]
          simp [ConLeche.Expr.allLevelParamsDefined]
        rw [← ea, ← eb]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1] at hins
        exact MemoInv.set expr_key_exact hmF hwfe hans hins
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w => exact alpd_hit hwfe hm ho h
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memo3, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : r0 = b := congrArg Prod.fst e0
        have eb : memo3 = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.all_level_params_defined_go params memo x
            = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have eq1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea2 : m1 = memo1 := congrArg Prod.fst eq1
          have eb2 : v1 = r0 := congrArg Prod.snd eq1
          rw [← ea2, ← eb2]; exact hp1
        obtain ⟨hans, hmF⟩ :
            ALPDQ (absNames params)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj s i x)))) r0 ∧
              MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
          obtain ⟨hb1, hmF⟩ := ih memo memo1 r0 hm hfix
          refine ⟨?_, hmF⟩
          simp only [ALPDQ, absExpr_mk, absExprKind]
          rw [hb1]
          simp [ConLeche.Expr.allLevelParamsDefined]
        rw [← ea, ← eb]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1] at hins
        exact MemoInv.set expr_key_exact hmF hwfe hans hins
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w => exact alpd_hit hwfe hm ho h
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memo3, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : r0 = b := congrArg Prod.fst e0
        have eb : memo3 = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.alpd_pair params memo f a = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have eq1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea2 : m1 = memo1 := congrArg Prod.fst eq1
          have eb2 : v1 = r0 := congrArg Prod.snd eq1
          rw [← ea2, ← eb2]; exact hp1
        obtain ⟨hans, hmF⟩ :
            ALPDQ (absNames params)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)))) r0 ∧
              MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
          obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_pair_inv hfix
          obtain ⟨hbx, hmX⟩ := ihf memo memoX bx hm hxr
          rcases hrest with ⟨rfl, hyr⟩ | ⟨rfl, hb0', hmm0⟩
          · obtain ⟨hby, hmY⟩ := iha memoX memo1 r0 hmX hyr
            refine ⟨?_, hmY⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hby]
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hb0']
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
        rw [← ea, ← eb]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1] at hins
        exact MemoInv.set expr_key_exact hmF hwfe hans hins
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @lam ty bo m e hty hbo hbm h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hbm h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w => exact alpd_hit hwfe hm ho h
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memo3, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : r0 = b := congrArg Prod.fst e0
        have eb : memo3 = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.alpd_binder params memo ty bo m.pw
            = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have eq1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea2 : m1 = memo1 := congrArg Prod.fst eq1
          have eb2 : v1 = r0 := congrArg Prod.snd eq1
          rw [← ea2, ← eb2]; exact hp1
        obtain ⟨hans, hmF⟩ :
            ALPDQ (absNames params)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)))) r0 ∧
              MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
          obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_binder_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX bx hm hxr
          rcases hrest with ⟨rfl, rb, rp, hyr, hpr, hb0'⟩ | ⟨rfl, hb0', hmm0⟩
          · obtain ⟨hby, hmY⟩ := ihbo memoX memo1 rb hmX hyr
            have hrp := PropWhen.params_defined_refines hps hbm hpr
            refine ⟨?_, hmY⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hb0', hby, hrp]
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hb0']
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
        rw [← ea, ← eb]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1] at hins
        exact MemoInv.set expr_key_exact hmF hwfe hans hins
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @forall_e ty bo m e hty hbo hbm h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hbm h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w => exact alpd_hit hwfe hm ho h
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memo3, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : r0 = b := congrArg Prod.fst e0
        have eb : memo3 = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.alpd_binder params memo ty bo m.pw
            = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have eq1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea2 : m1 = memo1 := congrArg Prod.fst eq1
          have eb2 : v1 = r0 := congrArg Prod.snd eq1
          rw [← ea2, ← eb2]; exact hp1
        obtain ⟨hans, hmF⟩ :
            ALPDQ (absNames params)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)))) r0 ∧
              MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
          obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_binder_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX bx hm hxr
          rcases hrest with ⟨rfl, rb, rp, hyr, hpr, hb0'⟩ | ⟨rfl, hb0', hmm0⟩
          · obtain ⟨hby, hmY⟩ := ihbo memoX memo1 rb hmX hyr
            have hrp := PropWhen.params_defined_refines hps hbm hpr
            refine ⟨?_, hmY⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hb0', hby, hrp]
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hb0']
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
        rw [← ea, ← eb]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1] at hins
        exact MemoInv.set expr_key_exact hmF hwfe hans hins
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h
  | @let_e ty v bo e hty hv hbo h1 ihty ihv ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hv hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' b hm h
    rw [cached.expr_ops_c.all_level_params_defined_go.eq_def] at h
    obtain ⟨b0, hlp, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind,
        ron.node.ExprView.ofKind, cached.expr_ops_c.is_compound_f, memo_skip_eq,
        Bool.not_true, memo_b_probe_false] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | some w => exact alpd_hit hwfe hm ho h
      | none =>
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨memo1, r0⟩ := q
        obtain ⟨memo3, hrec, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, hd1, oldv, hins⟩ := memo_b_record_inv hrec
        have e0 := Result.ok_injective (α := Bool × _) h
        have ea : r0 = b := congrArg Prod.fst e0
        have eb : memo3 = memo' := congrArg Prod.snd e0
        have hfix : cached.expr_ops_c.alpd_triple params memo ty v bo = ok (r0, memo1) := by
          obtain ⟨p1, hp1, hq2⟩ := bind_eq_ok_iff.mp hq
          obtain ⟨v1, m1⟩ := p1
          have eq1 := Result.ok_injective
            (α := ron.hashmap.HashMap expr.Expr Bool × Bool) hq2
          have ea2 : m1 = memo1 := congrArg Prod.fst eq1
          have eb2 : v1 = r0 := congrArg Prod.snd eq1
          rw [← ea2, ← eb2]; exact hp1
        obtain ⟨hans, hmF⟩ :
            ALPDQ (absNames params)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty v bo)))) r0 ∧
              MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo1 := by
          obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_triple_inv hfix
          obtain ⟨hbx, hmX⟩ := ihty memo memoX bx hm hxr
          rcases hrest with ⟨rfl, hyz⟩ | ⟨rfl, hb0', hmm0⟩
          · obtain ⟨by0, memoY, hyr, hrest2⟩ := alpd_pair_inv hyz
            obtain ⟨hby, hmY⟩ := ihv memoX memoY by0 hmX hyr
            rcases hrest2 with ⟨rfl, hzr⟩ | ⟨rfl, hb1', hmm1⟩
            · obtain ⟨hbz, hmZ⟩ := ihbo memoY memo1 r0 hmY hzr
              refine ⟨?_, hmZ⟩
              simp only [ALPDQ, absExpr_mk, absExprKind]
              rw [hbz]
              simp [ConLeche.Expr.allLevelParamsDefined, ← hbx, ← hby]
            · rw [← hmm1] at *
              refine ⟨?_, hmY⟩
              simp only [ALPDQ, absExpr_mk, absExprKind]
              rw [hb1']
              simp [ConLeche.Expr.allLevelParamsDefined, ← hbx, ← hby]
          · rw [← hmm0] at *
            refine ⟨?_, hmX⟩
            simp only [ALPDQ, absExpr_mk, absExprKind]
            rw [hb0']
            simp [ConLeche.Expr.allLevelParamsDefined, ← hbx]
        rw [← ea, ← eb]
        refine ⟨hans, ?_⟩
        rw [Expr.dup_eq hd1] at hins
        exact MemoInv.set expr_key_exact hmF hwfe hans hins
    · rename_i hcut
      have hb0 : b0 = false := by simpa using hcut
      subst hb0
      exact alpd_cutoff hwfe hm hlp h

/-- **`expr_ops_c::alpd_pair` refines the `.app` arm's short-circuit**. -/
theorem alpd_pair_refines {params : alloc.vec.Vec name.Name} (hps : NamesWF params)
    {x y : expr.Expr} (hx : ExprWF x) (hy : ExprWF y)
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {b : Bool}
    (hm : MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo)
    (h : cached.expr_ops_c.alpd_pair params memo x y = ok (b, memo')) :
    b = (ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr x) &&
          ConLeche.Expr.allLevelParamsDefined (absNames params) (absExpr y)) ∧
      MemoInv ExprWF absExpr (ALPDQ (absNames params)) memo' := by
  obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_pair_inv h
  obtain ⟨hbx, hmX⟩ := all_level_params_defined_go_refines hps hx memo memoX bx hm hxr
  rcases hrest with ⟨rfl, hyr⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hby, hmY⟩ := all_level_params_defined_go_refines hps hy memoX memo' b hmX hyr
    exact ⟨by rw [hby, ← hbx]; simp, hmY⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

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
  obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_binder_inv h
  obtain ⟨hbx, hmX⟩ := all_level_params_defined_go_refines hps hty memo memoX bx hm hxr
  rcases hrest with ⟨rfl, rb, rp, hyr, hpr, hb0⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hby, hmY⟩ := all_level_params_defined_go_refines hps hbo memoX memo' rb hmX hyr
    have hrp := PropWhen.params_defined_refines hps hpw hpr
    exact ⟨by rw [hb0, hby, hrp, ← hbx]; simp, hmY⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

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
  obtain ⟨bx, memoX, hxr, hrest⟩ := alpd_triple_inv h
  obtain ⟨hbx, hmX⟩ := all_level_params_defined_go_refines hps hx memo memoX bx hm hxr
  rcases hrest with ⟨rfl, hyz⟩ | ⟨rfl, hb0, hmm0⟩
  · obtain ⟨hbyz, hmYZ⟩ := alpd_pair_refines hps hy hz hmX hyz
    exact ⟨by rw [hbyz, ← hbx]; simp, hmYZ⟩
  · rw [← hmm0] at *
    exact ⟨by rw [hb0, ← hbx]; simp, hmX⟩

/-- **`expr_ops_c::all_level_params_defined` refines
`Expr.allLevelParamsDefinedC`** (`ExprOpsC.lean:825-828`): one memoised DAG walk
under a fresh table (`allLevelParamsDefined_spec`,
`Verify/Cached/GuardsC.lean:320`). -/
theorem all_level_params_defined_refines {params : alloc.vec.Vec name.Name}
    {e : expr.Expr} {b : Bool} (hps : NamesWF params) (he : ExprWF e)
    (h : cached.expr_ops_c.all_level_params_defined params e = ok b) :
    b = ConLeche.Expr.allLevelParamsDefinedC (absNames params) (absExpr e) := by
  rw [ConLeche.Expr.allLevelParamsDefinedC_spec]
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

Discharged in task #54 on top of `instantiate_list_refines`.  The two index
loops are strong inductions on what is left of the argument list, in
`rev_append_exprs_val`'s idiom; `piResidualAcc`'s cited `termination_by
(as.length, acc.length)` becomes the single measure
`2 * (args.length - i) + (if acc = [] then 0 else 1)`, which is why one
induction suffices here where con-leche needs a lexicographic pair. -/

/-! ## `Expr.piResidualAcc`'s per-arm equations

The cited definition is well founded on `(rest.length, acc.length)`, so its
equation lemmas have to be taken off `.eq_def` one arm at a time. -/

private theorem prA_nil (acc : List ConLeche.Expr) (e : ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc e []
      = some (ConLeche.Expr.instantiateListC e acc 0) := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_forallE (acc : List ConLeche.Expr) (ty b : ConLeche.Expr)
    (m : ConLeche.BinderMeta) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.forallE ty b m) (a :: rest)
      = ConLeche.Expr.piResidualAcc (a :: acc) b rest := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_bvar_nil (j : Nat) (a : ConLeche.Expr)
    (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc [] (.bvar j) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_bvar_cons (j : Nat) (w : ConLeche.Expr)
    (acc : List ConLeche.Expr) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc (w :: acc) (.bvar j) (a :: rest)
      = ConLeche.Expr.piResidualAcc []
          (ConLeche.Expr.instantiateListC (.bvar j) (w :: acc) 0)
          (a :: rest) := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_fvar (acc : List ConLeche.Expr) (idx : Nat)
    (ty : ConLeche.Expr) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.fvar idx ty) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_sort (acc : List ConLeche.Expr) (u : ConLeche.Level)
    (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.sort u) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_const (acc : List ConLeche.Expr) (n : ConLeche.Name)
    (us : List ConLeche.Level) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.const n us) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_app (acc : List ConLeche.Expr) (f x : ConLeche.Expr)
    (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.app f x) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_lam (acc : List ConLeche.Expr) (ty b : ConLeche.Expr)
    (m : ConLeche.BinderMeta) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.lam ty b m) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_letE (acc : List ConLeche.Expr) (ty v b : ConLeche.Expr)
    (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.letE ty v b) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_lit (acc : List ConLeche.Expr) (l : ConLeche.Literal)
    (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.lit l) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

private theorem prA_proj (acc : List ConLeche.Expr) (s : ConLeche.Name)
    (k : Nat) (x : ConLeche.Expr) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.Expr.piResidualAcc acc (.proj s k x) (a :: rest) = none := by
  rw [ConLeche.Expr.piResidualAcc.eq_def]

/-! ## The telescope operations -/

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
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i t e r hN hargs he h
    rw [cached.expr_ops_c.inst_spine_chain_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      rw [Expr.dup_eq h, List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      exact ⟨by simp [ConLeche.Expr.instSpine], he⟩
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, e2, hinst, i2, hi2, t2, ht2, hrec⟩ := h
      obtain ⟨hlt, hxwf, hdrop⟩ := vec_index_expr hargs hidx
      obtain ⟨hiabs, hiwf⟩ := instantiate1_refines he hxwf hinst
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have ht2v : t2.val = t.val - 1 := by
        rw [sub_nat_val ht2, show ((1#u64 : Std.U64)).val = 1 by scalar_tac]
      obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) args i2 t2 e2 r
        rfl hargs hiwf hrec
      refine ⟨?_, hwf⟩
      rw [habs, hi2v, ht2v, hdrop, hiabs,
        ConLeche.Expr.instantiate1C_spec]
      simp [ConLeche.Expr.instSpine]

/-- **`expr_ops_c::inst_spine_chain` refines `Expr.instSpineChainC`**
(`ExprOpsC.lean:752-755`): the `i = 0` wrapper. -/
theorem inst_spine_chain_refines {args : alloc.vec.Vec expr.Expr} {t : Std.U64}
    {e r : expr.Expr} (hargs : ExprsWF args) (he : ExprWF e)
    (h : cached.expr_ops_c.inst_spine_chain args t e = ok r) :
    absExpr r
        = ConLeche.Expr.instSpineChainC (absExprs args) t.val (absExpr e) ∧
      ExprWF r := by
  rw [cached.expr_ops_c.inst_spine_chain] at h
  obtain ⟨habs, hwf⟩ :=
    inst_spine_chain_from_refines _ args 0#usize t e r rfl hargs he h
  refine ⟨?_, hwf⟩
  rw [habs, ConLeche.Expr.instSpineChainC_spec,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]

/-- **`expr_ops_c::inst_spine` refines `Expr.instSpineC`**
(`ExprOpsC.lean:757-761`): the one bulk pass when the spine spans the telescope
context, the `instantiate1` chain otherwise. -/
theorem inst_spine_refines {args : alloc.vec.Vec expr.Expr} {t : Std.U64}
    {e r : expr.Expr} (hargs : ExprsWF args) (he : ExprWF e)
    (h : cached.expr_ops_c.inst_spine args t e = ok r) :
    absExpr r = ConLeche.Expr.instSpineC (absExprs args) t.val (absExpr e) ∧
      ExprWF r := by
  rw [cached.expr_ops_c.inst_spine] at h
  dsimp only at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i1, hi1, i2, hi2, h⟩ := h
  have hi1v : i1.val = args.val.length := by
    simp only [lift_eq, Result.ok.injEq] at hi1
    rw [← hi1, usize_cast_u64_val, alloc.vec.Vec.len_val]
  have hi2v : i2.val = t.val + 1 := HashMap.uscalar_add_eq hi2
  have hlenabs : (absExprs args).length = args.val.length := by
    simp [absExprs]
  rw [ConLeche.Expr.instSpineC]
  split at h
  · rename_i heq
    have hcond : (absExprs args).length = t.val + 1 := by
      rw [hlenabs, ← hi1v, ← hi2v, heq]
    rw [if_pos hcond]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨rev, hrev, h⟩ := h
    have hlen : (alloc.vec.Vec.len args).val = args.val.length :=
      alloc.vec.Vec.len_val args
    have hrevv : rev.val = args.val.reverse := by
      rw [rev_append_exprs_val _ (alloc.vec.Vec.new expr.Expr) args rev
        (alloc.vec.Vec.len args) rfl (by omega) hrev, hlen, List.take_length]
      simp [alloc.vec.Vec.new]
    have hrevwf : ExprsWF rev := by
      intro y hy
      rw [hrevv, List.mem_reverse] at hy
      exact hargs y hy
    have hrevabs : absExprs rev = (absExprs args).reverse := by
      rw [absExprs, absExprs, hrevv, List.map_reverse]
    obtain ⟨habs, hwf⟩ := instantiate_list_refines he hrevwf h
    refine ⟨?_, hwf⟩
    rw [habs, hrevabs, show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
  · rename_i heq
    have hcond : ¬ ((absExprs args).length = t.val + 1) := by
      intro hc
      exact heq (Std.UScalar.eq_of_val_eq (by rw [hi1v, hi2v, ← hlenabs, hc]))
    rw [if_neg hcond]
    exact inst_spine_chain_refines hargs he h

/-- The strong induction behind `pi_residual_acc_refines`, on the port's
counterpart of the cited two-component measure: `2 * (args.length - i) +
(if acc = [] then 0 else 1)` -- the `forallE` arm consumes an argument, the
`bvar` arm keeps them and empties a nonempty accumulator. -/
theorem pi_residual_acc_refines_aux (N : Nat) :
    ∀ (acc args : alloc.vec.Vec expr.Expr) (e : expr.Expr) (i : Std.Usize)
      (o : Option expr.Expr),
      2 * (args.val.length - i.val) + (if acc.val.length = 0 then 0 else 1) = N →
      ExprsWF acc → ExprsWF args → ExprWF e →
      cached.expr_ops_c.pi_residual_acc acc e args i = ok o →
      o.map absExpr
          = ConLeche.Expr.piResidualAcc (absExprs acc) (absExpr e)
              ((absExprs args).drop i.val) ∧
        ∀ x ∈ o, ExprWF x := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro acc args e i o hN hacc hargs he h
    rw [cached.expr_ops_c.pi_residual_acc.eq_def] at h
    dsimp only at h
    split at h
    · -- the argument list is exhausted: one bulk pass
      rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hinst, ho⟩ := h
      simp only [Result.ok.injEq] at ho
      subst ho
      obtain ⟨habs, hwf⟩ := instantiate_list_refines he hacc hinst
      refine ⟨?_, ?_⟩
      · rw [List.drop_eq_nil_of_le (by simpa [absExprs] using hlen), prA_nil,
          Option.map_some, habs, show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
      · intro x hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        rw [← hx]; exact hwf
    · rename_i hge
      have hlt : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      have hdropx : ∃ x, args.val[i.val]? = some x := by
        rw [List.getElem?_eq_getElem hlt]; exact ⟨_, rfl⟩
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
        split at h
        · -- the accumulator is empty: no residual
          rename_i hz
          have haccnil : acc.val = [] := by
            have hl := alloc.vec.Vec.len_val acc
            have h0 : (alloc.vec.Vec.len acc).val = ((0#usize : Std.Usize)).val := by
              rw [hz]
            have hz0 : acc.val.length = 0 := by scalar_tac
            exact List.eq_nil_of_length_eq_zero hz0
          obtain ⟨x, hx⟩ := hdropx
          simp only [Result.ok.injEq] at h
          subst h
          refine ⟨?_, by intro y hy; simp at hy⟩
          rw [absExprs_drop_cons hx, absExpr_mk, absExprKind,
            show absExprs acc = [] by rw [absExprs, haccnil]; rfl,
            prA_bvar_nil]
          rfl
        · -- flush the nonempty accumulator and re-enter at the same index
          rename_i hz
          have haccpos : 0 < acc.val.length := by
            have hne : (alloc.vec.Vec.len acc).val ≠ 0 := fun hc =>
              hz (Std.UScalar.eq_of_val_eq (by rw [hc]; symm; scalar_tac))
            have hl := alloc.vec.Vec.len_val acc
            scalar_tac
          simp only [bind_eq_ok_iff] at h
          obtain ⟨e2, hinst, hrec⟩ := h
          obtain ⟨habs2, hwf2⟩ := instantiate_list_refines (ExprWF.bvar h1) hacc hinst
          obtain ⟨habs, hwf⟩ := ih (2 * (args.val.length - i.val)) (by
              rw [← hN]; rw [if_neg (by omega : ¬ acc.val.length = 0)]; omega)
            (alloc.vec.Vec.new expr.Expr) args e2 i o (by simp [alloc.vec.Vec.new])
            exprsWF_new hargs hwf2 hrec
          refine ⟨?_, hwf⟩
          obtain ⟨x, hx⟩ := hdropx
          obtain ⟨w, accs, haccv⟩ := List.exists_cons_of_ne_nil
            (show acc.val ≠ [] from fun hc => by rw [hc] at haccpos; simp at haccpos)
          have haccabs : absExprs acc = absExpr w :: accs.map absExpr := by
            rw [absExprs, haccv, List.map_cons]
          rw [habs, absExprs_new, absExprs_drop_cons hx]
          simp only [absExpr_mk, absExprKind] at habs2 ⊢
          rw [haccabs, prA_bvar_cons, habs2, haccabs,
            show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_fvar]; rfl,
          by intro y hy; simp at hy⟩
      | @sort u e hu h1 =>
        obtain ⟨d, _, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_sort]; rfl,
          by intro y hy; simp at hy⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, _, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_const]; rfl,
          by intro y hy; simp at hy⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_app]; rfl,
          by intro y hy; simp at hy⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_lam]; rfl,
          by intro y hy; simp at hy⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
        obtain ⟨x, hidx, acc2, hcons, i2, hi2, hrec⟩ := h
        obtain ⟨-, hxwf, hdrop⟩ := vec_index_expr hargs hidx
        obtain ⟨haccabs, haccwf⟩ := cons_expr_refines hxwf hacc hcons
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hacc2len : acc2.val.length = acc.val.length + 1 := by
          rw [cons_expr_val hcons]; simp
        obtain ⟨habs, hwf⟩ := ih (2 * (args.val.length - i2.val) + 1) (by
            rw [← hN]; split <;> omega)
          acc2 args bo i2 o (by rw [if_neg (by omega : ¬ acc2.val.length = 0)]) haccwf
          hargs hbo hrec
        refine ⟨?_, hwf⟩
        rw [habs, haccabs, hi2v, hdrop, absExpr_mk, absExprKind, prA_forallE]
      | @let_e ty v bo e hty hv hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_letE]; rfl,
          by intro y hy; simp at hy⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨x, hx⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hx, absExpr_mk, absExprKind, prA_lit]; rfl,
          by intro y hy; simp at hy⟩
      | @proj s k x e hs hxw h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        obtain ⟨y, hy⟩ := hdropx
        exact ⟨by rw [absExprs_drop_cons hy, absExpr_mk, absExprKind, prA_proj]; rfl,
          by intro z hz; simp at hz⟩

/-- **`expr_ops_c::pi_residual_acc` refines `Expr.piResidualAcc`**
(`ExprOpsC.lean:763-783`) at the arguments from `i` on. -/
theorem pi_residual_acc_refines {acc args : alloc.vec.Vec expr.Expr}
    {e : expr.Expr} {i : Std.Usize} {o : Option expr.Expr} (hacc : ExprsWF acc)
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : cached.expr_ops_c.pi_residual_acc acc e args i = ok o) :
    o.map absExpr
        = ConLeche.Expr.piResidualAcc (absExprs acc) (absExpr e)
            ((absExprs args).drop i.val) ∧
      ∀ x ∈ o, ExprWF x :=
  pi_residual_acc_refines_aux _ acc args e i o rfl hacc hargs he h

/-- **`expr_ops_c::pi_residual` refines `Expr.piResidual`**
(`ExprOpsC.lean:785-787`): the residual of a `∀`-telescope at an argument
spine. -/
theorem pi_residual_refines {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {o : Option expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : cached.expr_ops_c.pi_residual e args = ok o) :
    o.map absExpr = ConLeche.Expr.piResidual (absExpr e) (absExprs args) ∧
      ∀ x ∈ o, ExprWF x := by
  rw [cached.expr_ops_c.pi_residual] at h
  obtain ⟨hmap, hwf⟩ := pi_residual_acc_refines
    (by intro x hx; simp [alloc.vec.Vec.new] at hx) hargs he h
  refine ⟨?_, hwf⟩
  rw [hmap, ConLeche.Expr.piResidual,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]
  simp [absExprs, alloc.vec.Vec.new]

end ConRon.Refine.ExprOpsC

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Five representative lemmas of the four files: the memoised substitution behind
every executed `instantiate1` call site, the memoised abstraction behind every
binder close, the memoised scope walk that gates the η/ι fabrications, the bulk
substitution behind every telescope instantiation, and the gray-set leaf walk
(the last two are task #54's).  Each must depend on the three standard axioms
and nothing else -- in particular nothing may reach
`ConRon.Refine.Pins.PINS_TEXT`. -/

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

/--
info: 'ConRon.Refine.ExprOpsC.instantiate_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOpsC.instantiate_list_refines

/--
info: 'ConRon.Refine.ExprOpsC.fvar_leaves_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOpsC.fvar_leaves_refines
