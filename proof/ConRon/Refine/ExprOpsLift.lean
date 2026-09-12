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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @fvar idx ty e _hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeB]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihf hn1, iha hn2]
    simp [ConLeche.Expr.sizeB]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeB]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeB]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, n5, hn5, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn5, HashMap.uscalar_add_eq hn3,
      ihty hn1, ihw hn2, ihbo hn4]
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.sizeB, Expr.val_one]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.size_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @fvar idx ty e _hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, ih hn1]
    simp [ConLeche.Expr.sizeF]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.sizeF]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihf hn1, iha hn2]
    simp [ConLeche.Expr.sizeF]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeF]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.sizeF]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, n5, hn5, hr⟩ := h
    rw [HashMap.uscalar_add_eq hr, HashMap.uscalar_add_eq hn5, HashMap.uscalar_add_eq hn3,
      ihty hn1, ihw hn2, ihbo hn4]
    simp only [absExpr_mk, absExprKind, ConLeche.Expr.sizeF, Expr.val_one]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.size_f.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @fvar idx ty e _hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, Result.ok.injEq] at h
    rw [← h]
    simp [ConLeche.Expr.wscopedB]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [bool_and_step (fun _ hy => ihf hy) (fun _ hy => iha hy) h]
    simp [ConLeche.Expr.wscopedB]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [bool_and_step (fun _ hy => ihty hy) (fun _ hy => ihbo hy) h]
    simp [ConLeche.Expr.wscopedB]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [bool_and_step (fun _ hy => ihty hy) (fun _ hy => ihbo hy) h]
    simp [ConLeche.Expr.wscopedB]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [bool_and_step (fun _ hy => ihty hy)
      (fun _ hy => bool_and_step (fun _ hy' => ihw hy') (fun _ hy' => ihbo hy') hy) h]
    simp [ConLeche.Expr.wscopedB, Bool.and_assoc]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro d b h
    rw [expr_ops.wscoped_b.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [HashMap.uscalar_add_eq h]
    simp [ConLeche.Expr.bvarBound]
  | @fvar idx ty e _hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.bvarBound]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihf hn1, iha hn2]
    simp [ConLeche.Expr.bvarBound]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [Expr.max_u64_val hr, sub_nat_val_trunc hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.bvarBound]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, hr⟩ := h
    rw [Expr.max_u64_val hr, sub_nat_val_trunc hn3, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.bvarBound]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, n5, hn5, hr⟩ := h
    rw [Expr.max_u64_val hr, Expr.max_u64_val hn3, sub_nat_val_trunc hn5,
      ihty hn1, ihw hn2, ihbo hn4]
    simp [ConLeche.Expr.bvarBound]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.bvar_bound.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @fvar idx ty e _hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [HashMap.uscalar_add_eq h]
    simp [ConLeche.Expr.fvarRange]
  | @sort u e _hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @mk_const n us e _hn _hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @lit l e _hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    simp [ConLeche.Expr.fvarRange]
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihf hn1, iha hn2]
    simp [ConLeche.Expr.fvarRange]
  | @lam ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.fvarRange]
  | @forall_e ty bo m e _hty _hbo _hm h1 ihty ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, hr⟩ := h
    rw [Expr.max_u64_val hr, ihty hn1, ihbo hn2]
    simp [ConLeche.Expr.fvarRange]
  | @let_e ty w bo e _hty _hw _hbo h1 ihty ihw ihbo =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨n1, hn1, n2, hn2, n3, hn3, n4, hn4, hr⟩ := h
    rw [Expr.max_u64_val hr, Expr.max_u64_val hn3, ihty hn1, ihw hn2, ihbo hn4]
    simp [ConLeche.Expr.fvarRange]
  | @proj s i x e _hs _hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [expr_ops.fvar_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    refine ⟨?_, Expr.bvar_wf h⟩
    rw [Expr.bvar_refines h]
    simp [ConLeche.Expr.abstractRange]
  | @fvar idx ty e hty h1 _ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.abstractRange], ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.abstractRange], ExprWF.mk_const hn hus h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.abstractRange], ExprWF.lit hl h1⟩
  | @app f a e _hf _ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro d k c r h
    rw [expr_ops.abstract_range.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.fvar hty h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.sort hu h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨cc, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    exact ⟨⟨ExprWF.mk_const hn hus h1, by simp [ConLeche.Expr.liftLooseBVars]⟩, hm⟩
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' c r hm h
    rw [expr_ops.lift_loose_bvars_go.eq_def] at h
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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

end ConRon.Refine.ExprOps
