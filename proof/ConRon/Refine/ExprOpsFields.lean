/-
Task #21, part: the shift walk, the bulk abstraction, the two size measures,
the scope check and the two derived-field *spec* walks of
`crates/con-ron-core/src/kernel/expr_ops.rs`, refined on the generated model.

`lift_loose_bvars_go` is `instantiate1_go`'s twin — the same `(node, cursor)`
memo, hence the same `absKey`/`KeyWF`/`key_exact` plumbing and the same
`MemoInv.hit`/`MemoInv.set` step, with the invariant parameterised by the
`amount` the wrapper fixes (con-leche's `LiftMemoInv`).  `abstract_range`,
`size_b`, `size_f`, `wscoped_b`, `bvar_bound` and `fvar_range` are plain
structural walks, unmemoized on both sides; each is proved by induction on the
`ExprWF` derivation, which is what supplies both the node's shape (`Expr.*_inv`)
and the children's well-formedness, since an Aeneas `partial_fixpoint` carries
no induction principle of its own.

Every statement is against the *logical* con-leche definition and is
exact-result-on-success; `ExprWF` is a hypothesis even of the five readers,
whose answers do not depend on the stored word, because the induction the
proofs use *is* the `ExprWF` derivation.

The one genuinely fiddly part is `abstract_range`'s `u64` arithmetic: the port
computes `c + ((d + k - 1) - idx)` with machine subtraction, which is safe only
under the two guards it sits behind (`d ≤ idx` and `idx < d + k`), and
con-leche's `Nat` expression `c + (d + k - 1 - idx)` has to be matched to it
under exactly those guards.

This file also carries the group that used to sit in `ExprOpsBvarB.lean`
(task #21's split); the two halves were merged at task #47, which is why the
section comment below repeats a module note.
-/
import ConRon.Refine.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## The two size measures (`ExprOps.lean:741-748`, `:810-819`) -/

/-- `expr_ops::size_b` refines `Expr.sizeB` (`ExprOps.lean:743-748`): the node
count with `fvar` a leaf.  Nothing in the port recurses on it (Aeneas's
`partial_fixpoint` carries no measure), but it is executable and the gate keeps
it in step with its source. -/
theorem size_b_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ {r : Std.U64}, expr_ops.size_b e = ok r → r.val = (absExpr e).sizeB := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @fvar idx ty e _hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihf hn1, iha hn2]
    simp [ConLeche.Expr.sizeB]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeB]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeB]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, n5, hn5, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn5, HashMap.uscalar_add_eq hn3,
      ihty hn1, ihw hn2, ihbo hn4]
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.sizeB, Expr.val_one]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, ih hn1]
    simp [ConLeche.Expr.sizeB]

/-- `expr_ops::size_f` refines `Expr.sizeF` (`ExprOps.lean:810-819`): the full
node count, `fvar` type annotations included. -/
theorem size_f_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ {r : Std.U64}, expr_ops.size_f e = ok r → r.val = (absExpr e).sizeF := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @fvar idx ty e _hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, ih hn1]
    simp [ConLeche.Expr.sizeF]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihf hn1, iha hn2]
    simp [ConLeche.Expr.sizeF]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeF]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeF]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, n5, hn5, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn5, HashMap.uscalar_add_eq hn3,
      ihty hn1, ihw hn2, ihbo hn4]
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.sizeF, Expr.val_one]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, ih hn1]
    simp [ConLeche.Expr.sizeF]

/-! ## The scope check (`ExprOps.lean:835-861`)

Every `&&` of the cited code is an `if` nest in the port (task #13's deviation
6, which is what Charon produces from a `&&` anyway).  `bool_and_step` is the
`Bool`-valued analogue of `Refine/Expr.lean`'s `guard_step`: given the two
components' exactness, one link of the nest is exact. -/

/-- One `if`-nested `&&`: `let y ← test; if y then rest else false`. -/
theorem bool_and_step {c P Q : Bool} {test rest : Result Bool}
    (htest : ∀ y, test = ok y → y = P) (hrest : ∀ y, rest = ok y → y = Q)
    (h : (do let y ← test; if y = true then rest else ok false) = ok c) :
    c = (P && Q) := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨y, hy, h⟩ := h
  have e := htest y hy
  cases hc : y with
  | false =>
    rw [hc] at e h
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← e]
    simp
  | true =>
    rw [hc] at e h
    simp only [if_true] at h
    rw [hrest c h, ← e]
    simp

/-- `expr_ops::wscoped_b` refines `Expr.wscopedB` (`ExprOps.lean:849-861`):
every reachable `fvar` index is below `d`, hereditarily through the
annotations. -/
theorem wscoped_b_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ {d : Std.U64} {b : Bool}, expr_ops.wscoped_b d e = ok b →
      b = ConLeche.Expr.wscopedB d.val (absExpr e) := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @fvar idx ty e _hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    split at h
    · rename_i hlt
      have hlt' : idx.val < d.val := by scalar_tac
      rw [ih h]
      simp [ConLeche.Expr.wscopedB, hlt']
    · rename_i hlt
      have hlt' : ¬ (idx.val < d.val) := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      simp [ConLeche.Expr.wscopedB, hlt']
  | @sort u e _hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [bool_and_step (fun _ hy => ihf hy) (fun _ hy => iha hy) h]
    simp [ConLeche.Expr.wscopedB]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [bool_and_step (fun _ hy => ihty hy) (fun _ hy => ihbo hy) h]
    simp [ConLeche.Expr.wscopedB]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [bool_and_step (fun _ hy => ihty hy) (fun _ hy => ihbo hy) h]
    simp [ConLeche.Expr.wscopedB]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [bool_and_step (fun _ hy => ihty hy)
      (fun _ hy => bool_and_step (fun _ hy' => ihw hy') (fun _ hy' => ihbo hy') hy) h]
    simp [ConLeche.Expr.wscopedB, Bool.and_assoc]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [ih h]
    simp [ConLeche.Expr.wscopedB]

/-! ## The two derived-field spec walks (`ExprOps.lean:1295-1325`)

`bvarBound` and `fvarRange` are the *specifications* of the packed word's two
range fields; the port carries them unmemoized and uncalled, so that the
provenance gate stays in step with their source (task #11's `beqRecursive`
rule).  `bvarBound`'s `body.bvarBound - 1` is Lean's truncated `Nat`
subtraction, which is what the module's `sub_nat` is for. -/

/-- `expr_ops::sub_nat` is Lean's truncated `Nat` subtraction (the module's one
helper with no con-leche counterpart). -/
theorem sub_nat_val_trunc {a b r : Std.U64} (h : expr_ops.sub_nat a b = ok r) :
    r.val = a.val - b.val := by
  rw [expr_ops.sub_nat] at h
  split at h
  · rename_i hge
    have : b.val ≤ a.val := by scalar_tac
    rw [HashMap.uscalar_sub_eq h]
  · rename_i hge
    have : a.val < b.val := by scalar_tac
    rw [← Result.ok_injective h]
    simp only [Expr.val_zero]
    omega

/-- `expr_ops::bvar_bound` refines `Expr.bvarBound` (`ExprOps.lean:1295-1304`):
the least `k` with `looseBVarsBounded k`. -/
theorem bvar_bound_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ {r : Std.U64}, expr_ops.bvar_bound e = ok r → r.val = (absExpr e).bvarBound := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [HashMap.uscalar_add_eq h]
    simp [ConLeche.Expr.bvarBound]
  | @fvar idx ty e _hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihf hn1, iha hn2]
    simp [ConLeche.Expr.bvarBound]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [Expr.max_u64_val hr, sub_nat_val_trunc hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.bvarBound]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [Expr.max_u64_val hr, sub_nat_val_trunc hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.bvarBound]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, n5, hn5, hr⟩ := h
    rw [Expr.max_u64_val hr, Expr.max_u64_val hn3, sub_nat_val_trunc hn5,
      ihty hn1, ihw hn2, ihbo hn4]
    simp [ConLeche.Expr.bvarBound]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [ih h]
    simp [ConLeche.Expr.bvarBound]

/-- `expr_ops::fvar_range` refines `Expr.fvarRange` (`ExprOps.lean:1315-1324`):
the least `d` with every `fvar` index below it (annotations not descended). -/
theorem fvar_range_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ {r : Std.U64}, expr_ops.fvar_range e = ok r → r.val = (absExpr e).fvarRange := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @fvar idx ty e _hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [HashMap.uscalar_add_eq h]
    simp [ConLeche.Expr.fvarRange]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihf hn1, iha hn2]
    simp [ConLeche.Expr.fvarRange]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.fvarRange]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.fvarRange]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, hr⟩ := h
    rw [Expr.max_u64_val hr, Expr.max_u64_val hn3, ihty hn1, ihw hn2, ihbo hn4]
    simp [ConLeche.Expr.fvarRange]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [ih h]
    simp [ConLeche.Expr.fvarRange]

/-! ## Bulk abstraction (`ExprOps.lean:778-808`)

Not memoized on either side.  The `fvar` arm is the cited
`d ≤ idx ∧ idx < d + k` as an `if` nest (task #13's deviation 6), and its
machine arithmetic `c + ((d + k - 1) - idx)` is safe exactly under those two
guards -- which is what makes it con-leche's `Nat` expression
`c + (d + k - 1 - idx)`: with `d ≤ idx < d + k` no subtraction truncates, so
`omega` closes the two in one step from the four `*_val` equations. -/

/-- `expr_ops::abstract_range` refines `Expr.abstractRange`
(`ExprOps.lean:791-808`): close `k` binders in one traversal, `fvar (d + i)`
becoming the bound variable of the `i`-th binder counted outermost-first. -/
theorem abstract_range_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ {d k c : Std.U64} {r : expr.Expr}, expr_ops.abstract_range e d k c = ok r →
      absExpr r = ConLeche.Expr.abstractRange (absExpr e) d.val k.val c.val ∧ ExprWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    refine ⟨?_, Expr.bvar_wf h⟩
    rw [Expr.bvar_refines h]
    simp [ConLeche.Expr.abstractRange]
  | @fvar idx ty e hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    split at h
    · rename_i hle
      have hle' : d.val ≤ idx.val := by scalar_tac
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
      split at h
      · rename_i hlt
        have hlt' : idx.val < d.val + k.val := by rw [← hiv]; scalar_tac
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have h1v : i1.val = i.val - 1 := by
          rw [HashMap.uscalar_sub_eq hi1, Expr.val_one]
        have h2v : i2.val = i1.val - idx.val := HashMap.uscalar_sub_eq hi2
        have h3v : i3.val = c.val + i2.val := HashMap.uscalar_add_eq hi3
        refine ⟨?_, Expr.bvar_wf h⟩
        rw [Expr.bvar_refines h]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstractRange,
          if_pos (show d.val ≤ idx.val ∧ idx.val < d.val + k.val from ⟨hle', hlt'⟩)]
        congr 1
        omega
      · rename_i hlt
        have hlt' : ¬ (idx.val < d.val + k.val) := by rw [← hiv]; scalar_tac
        rw [Expr.dup_eq h]
        refine ⟨?_, ExprWF.fvar hty h1⟩
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstractRange,
          if_neg (show ¬ (d.val ≤ idx.val ∧ idx.val < d.val + k.val) from
            fun hc => hlt' hc.2)]
    · rename_i hle
      have hle' : ¬ (d.val ≤ idx.val) := by scalar_tac
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.fvar hty h1⟩
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.abstractRange,
        if_neg (show ¬ (d.val ≤ idx.val ∧ idx.val < d.val + k.val) from
          fun hc => hle' hc.1)]
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.abstractRange], ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.abstractRange], ExprWF.mk_const hn hus h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.abstractRange], ExprWF.lit hl h1⟩
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨f2, hf2, a2, ha2, happ⟩ := h
    obtain ⟨e1, w1⟩ := ihf hf2
    obtain ⟨e2, w2⟩ := iha ha2
    refine ⟨?_, Expr.app_wf w1 w2 happ⟩
    rw [Expr.app_refines happ, e1, e2]
    simp [ConLeche.Expr.abstractRange]
  | @lam ty bo m e _hty _hbo hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨t, ht, i, hi, b, hb, bm, hbm, hlam⟩ := h
    obtain ⟨e1, w1⟩ := ihty ht
    obtain ⟨e2, w2⟩ := ihbo hb
    refine ⟨?_, Expr.lam_wf w1 w2 (Expr.binder_meta_dup_eq hbm ▸ hm) hlam⟩
    rw [Expr.lam_refines hlam, e1, e2, Expr.binder_meta_dup_eq hbm,
      HashMap.uscalar_add_eq hi]
    simp [ConLeche.Expr.abstractRange]
  | @forall_e ty bo m e _hty _hbo hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨t, ht, i, hi, b, hb, bm, hbm, hfa⟩ := h
    obtain ⟨e1, w1⟩ := ihty ht
    obtain ⟨e2, w2⟩ := ihbo hb
    refine ⟨?_, Expr.forall_e_wf w1 w2 (Expr.binder_meta_dup_eq hbm ▸ hm) hfa⟩
    rw [Expr.forall_e_refines hfa, e1, e2, Expr.binder_meta_dup_eq hbm,
      HashMap.uscalar_add_eq hi]
    simp [ConLeche.Expr.abstractRange]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨t, ht, w2, hw2, i, hi, b, hb, hlet⟩ := h
    obtain ⟨e1, x1⟩ := ihty ht
    obtain ⟨e2, x2⟩ := ihw hw2
    obtain ⟨e3, x3⟩ := ihbo hb
    refine ⟨?_, Expr.let_e_wf x1 x2 x3 hlet⟩
    rw [Expr.let_e_refines hlet, e1, e2, e3, HashMap.uscalar_add_eq hi]
    simp [ConLeche.Expr.abstractRange]
  | @proj s i x e hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
    obtain ⟨u, hu, n2, hn2, hproj⟩ := h
    have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
    subst hsn
    obtain ⟨e1, w1⟩ := ih hu
    refine ⟨?_, Expr.proj_wf hs w1 hproj⟩
    rw [Expr.proj_refines hproj, e1]
    simp [ConLeche.Expr.abstractRange]

/-! ## `liftLooseBVars` (`ExprOps.lean:380-539`)

`instantiate1_go`'s twin, node for node: the same `(node, cutoff)` memo, the
same five memo-skipping leaves, the same probe-recurse-record shape.  The one
difference is the fixed `amount`, which the answer depends on and the key does
not -- so, exactly as in con-leche, the invariant is parameterised by it and
the wrapper's fresh memo is what makes that sound. -/

/-- con-leche's `LiftMemoInv` (`ExprOps.lean:411-413`), as the `Q` of
`MemoInv`: every recorded answer is the real one, and it is well formed. -/
def LiftQ (amount : Nat) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun k r => ExprWF r ∧ absExpr r = ConLeche.Expr.liftLooseBVars amount k.2 k.1

/-- **The memoized shift walk is `liftLooseBVars`** (`ExprOps.lean:431-466`,
con-leche's plan `liftLooseBVarsGo_spec` `:469`). -/
theorem lift_loose_bvars_go_refines {amount : Std.U64} {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr) (c : Std.U64)
      (r : expr.Expr),
      MemoInv KeyWF absKey (LiftQ amount.val) memo →
      expr_ops.lift_loose_bvars_go amount memo e c = ok (r, memo') →
      (ExprWF r ∧
          absExpr r = ConLeche.Expr.liftLooseBVars amount.val c.val (absExpr e)) ∧
        MemoInv KeyWF absKey (LiftQ amount.val) memo' := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
    split at h
    · rename_i hge
      have hge' : c.val ≤ i.val := by scalar_tac
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨i1, hi1, cc, hcc, hr, hmm⟩ := h
      subst hr; subst hmm
      refine ⟨⟨Expr.bvar_wf hcc, ?_⟩, hm⟩
      rw [Expr.bvar_refines hcc, HashMap.uscalar_add_eq hi1]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.liftLooseBVars]
      rw [if_pos (show i.val ≥ c.val from hge')]
    · rename_i hge
      have hge' : ¬ (c.val ≤ i.val) := by scalar_tac
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨cc, hcc, hr, hmm⟩ := h
      subst hr; subst hmm
      refine ⟨⟨Expr.bvar_wf hcc, ?_⟩, hm⟩
      rw [Expr.bvar_refines hcc]
      simp only [absExpr_mk, absExprKind, ConLeche.Expr.liftLooseBVars]
      rw [if_neg (show ¬ (i.val ≥ c.val) from hge')]
  | @fvar idx ty e hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.fvar hty h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.sort hu h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.mk_const hn hus h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.lit hl h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LiftQ amount.val)
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
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihf memo memo2 c f2 hm hf2
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := iha memo2 memo1 c a2 hm2 ha2
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : LiftQ amount.val
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.App f a)), c⟩) r := by
        refine ⟨Expr.app_wf hwf2 hwf3 happ, ?_⟩
        rw [Expr.app_refines happ, habs2, habs3]
        simp [ConLeche.Expr.liftLooseBVars]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.lam hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LiftQ amount.val)
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨cc, hcc, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hlam, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 c t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hb
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : LiftQ amount.val
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), c⟩) r := by
        refine ⟨Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam, ?_⟩
        rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
          HashMap.uscalar_add_eq hcc]
        simp [ConLeche.Expr.liftLooseBVars]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
    have hwfe : ExprWF e := ExprWF.forall_e hty hbo hm0 h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LiftQ amount.val)
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨cc, hcc, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨p2, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo3⟩ := p2
      obtain ⟨bm, hbm, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨r1, hfa, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo3 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 c t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihbo memo2 memo1 cc b hm2 hb
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : LiftQ amount.val
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), c⟩) r := by
        refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
        rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
          HashMap.uscalar_add_eq hcc]
        simp [ConLeche.Expr.liftLooseBVars]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LiftQ amount.val)
        key_exact hm (keyWF_mk hwfe) (memo1_get_hit ho)
      exact ⟨hhit, hm⟩
    | none =>
      obtain ⟨q, hgo, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨memo1, r0⟩ := q
      obtain ⟨p1, ht, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨t, memo2⟩ := p1
      obtain ⟨p2, hv2, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨w2, memo3⟩ := p2
      obtain ⟨cc, hcc, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨p3, hb, hgo⟩ := bind_eq_ok_iff.mp hgo
      obtain ⟨b, memo4⟩ := p3
      obtain ⟨r1, hlet, hgo⟩ := bind_eq_ok_iff.mp hgo
      have eg := Result.ok_injective (α := ron.hashmap.HashMap expr_ops.ExprNatKey _ × _) hgo
      have eg1 : memo1 = memo4 := (congrArg Prod.fst eg).symm
      have eg2 : r0 = r1 := (congrArg Prod.snd eg).symm
      subst eg1; subst eg2
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ihty memo memo2 c t hm ht
      obtain ⟨⟨hwf3, habs3⟩, hm3⟩ := ihw memo2 memo3 c w2 hm2 hv2
      obtain ⟨⟨hwf4, habs4⟩, hm4⟩ := ihbo memo3 memo1 cc b hm3 hb
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p4, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo5⟩ := p4
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo5 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hans : LiftQ amount.val
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), c⟩) r := by
        refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
        rw [Expr.let_e_refines hlet, habs2, habs3, habs4, HashMap.uscalar_add_eq hcc]
        simp [ConLeche.Expr.liftLooseBVars]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := LiftQ amount.val)
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
      obtain ⟨⟨hwf2, habs2⟩, hm2⟩ := ih memo memo1 c u hm hu
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨p3, hins, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨oldv, memo4⟩ := p3
      have e0 := Result.ok_injective (α := expr.Expr × _) h
      have e1' : r = r0 := (congrArg Prod.fst e0).symm
      have e2' : memo' = memo4 := (congrArg Prod.snd e0).symm
      subst e1'; subst e2'
      have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
      subst hsn
      have hans : LiftQ amount.val
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)), c⟩) r := by
        refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
        rw [Expr.proj_refines hproj, habs2]
        simp [ConLeche.Expr.liftLooseBVars]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins

/-- **`expr_ops::lift_loose_bvars` refines `Expr.liftLooseBVars`.**  The fresh
memo satisfies the invariant vacuously (`LiftMemoInv.empty`), so the walk's own
lemma gives the logical function -- con-leche's `@[csimp]` lemma
`liftLooseBVars_eq_liftLooseBVarsFast` (`ExprOps.lean:536-539`). -/
theorem lift_loose_bvars_refines {amount c : Std.U64} {e r : expr.Expr} (he : ExprWF e)
    (h : expr_ops.lift_loose_bvars amount c e = ok r) :
    absExpr r = ConLeche.Expr.liftLooseBVars amount.val c.val (absExpr e) ∧ ExprWF r := by
  rw [expr_ops.lift_loose_bvars] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    lift_loose_bvars_go_refines he memo memo' c r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

/-!Task #21, the derived-field part: the *exact* accessors `bvar_b`/`fvar_b`, the
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, ron.node.ExprView.ofKind] at h
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

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`abstract_range_refines` is the deepest chain of the bulk-abstraction half
(`abstract1` under a `fvar_b` cutoff, once per variable of the block), and
`bvar_b_refines` is the one lemma that reads the *packed word* and falls back to
the memoized walk at saturation -- the two worth pinning here. -/

/--
info: 'ConRon.Refine.ExprOps.abstract_range_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOps.abstract_range_refines

/--
info: 'ConRon.Refine.ExprOps.bvar_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.ExprOps.bvar_b_refines
