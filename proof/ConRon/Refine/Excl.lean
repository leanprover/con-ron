/-
The exclusivity read, in the model (task #98).

`ron::node::is_exclusive` is the port of con-leche's `withExclusive`
(`ConLeche/Kernel/Exclusive.lean`): a walk reads the reference count of the
BORROWED node it is about to rebuild, and only a SHARED node is probed and
recorded.  The hole is modelled `ok false` — "not known to be exclusive", the
conservative answer, and the one that always memoises — so in the model every
verdict is `false` and each gated `get`/`insert` is definitionally the
unguarded operation this port had before the bump.  OVERVIEW.md §8.1's row is
the trust argument for the other branch, which no proof sees.

That is the whole content of this file: eight `rfl`s and two case splits,
stated so that a walk's refinement proof reduces the new shape to the old one
by naming them in the `simp only` that opens each memoised arm — after which
the arm reads exactly as it did.
-/
import ConRon.Refine.Level

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-- The hole: the model never reports a node exclusive, so the model is the
walk that records every node it is offered. -/
@[simp] theorem is_exclusive_eq (e : expr.Expr) :
    ron.node.is_exclusive e = ok false := rfl

/-! ## The gated `get`/`insert` pairs

Each is its unguarded predecessor once the verdict is `false`; `rfl`, because
the verdict is a literal `if` on a `Bool` the model has already decided. -/

/-- The cursored node→node probe at a node the walk will memoise. -/
@[simp] theorem memo1_get_if_false
    (memo : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
    (k : expr_ops.ExprNatKey) :
    expr_ops.memo1_get_if memo false k = expr_ops.memo1_get memo k := rfl

/-- The cursored node→node record at a node the walk will memoise. -/
@[simp] theorem memo1_insert_if_false
    (memo : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr)
    (k : expr_ops.ExprNatKey) (r : expr.Expr) :
    expr_ops.memo1_insert_if memo false k r =
      (do
        let r' ← expr.dup r
        let (_, memo1) ←
          ron.hashmap.HashMap.insert
            expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
            expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 memo k r'
        ok memo1) := rfl

/-- The cursor-free node→node probe (`instLevelParams`). -/
@[simp] theorem memo_e_probe_false
    (memo : ron.hashmap.HashMap expr.Expr expr.Expr) (e : expr.Expr) :
    expr_ops.memo_e_probe memo false e = expr_ops.memo_e_get memo e := rfl

/-- The cursor-free node→node record. -/
@[simp] theorem memo_e_record_false
    (memo : ron.hashmap.HashMap expr.Expr expr.Expr) (e r : expr.Expr) :
    expr_ops.memo_e_record memo false e r =
      (do
        let e' ← expr.dup e
        let r' ← expr.dup r
        let (_, memo1) ←
          ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 memo e' r'
        ok memo1) := rfl

/-- The cursor-free node→`Bool` probe. -/
@[simp] theorem memo_b_probe_false
    (memo : ron.hashmap.HashMap expr.Expr Bool) (e : expr.Expr) :
    expr_ops.memo_b_probe memo false e = expr_ops.memo_b_get memo e := rfl

/-- The cursor-free node→`Bool` record. -/
@[simp] theorem memo_b_record_false
    (memo : ron.hashmap.HashMap expr.Expr Bool) (e : expr.Expr) (r : Bool) :
    expr_ops.memo_b_record memo false e r =
      (do
        let e' ← expr.dup e
        let (_, memo1) ←
          ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 memo e' r
        ok memo1) := rfl

/-- The cursored `Bool` probe (`wscopedB`). -/
@[simp] theorem memo_b1_get_if_false
    (memo : ron.hashmap.HashMap expr_ops.ExprNatKey Bool)
    (k : expr_ops.ExprNatKey) :
    cached.expr_ops_c.memo_b1_get_if memo false k =
      cached.expr_ops_c.memo_b1_get memo k := rfl

/-- The cursored `Bool` record. -/
@[simp] theorem memo_b1_insert_if_false
    (memo : ron.hashmap.HashMap expr_ops.ExprNatKey Bool)
    (k : expr_ops.ExprNatKey) (r : Bool) :
    cached.expr_ops_c.memo_b1_insert_if memo false k r =
      (do
        let (_, memo1) ←
          ron.hashmap.HashMap.insert
            expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
            expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 memo k r
        ok memo1) := rfl

/-! ## Reading a record back

The gated `insert` is a *function call* where the walk used to write the
insert inline, so a proof that destructured `dup`-then-`insert` now meets one
bind where it expects two.  These four are that one bind, opened: the
conclusion is exactly the pair of hypotheses the arm had before, so a site
trades two `obtain`s for two, with the same names. -/

/-- The cursored node->node record, read back. -/
theorem memo1_insert_if_inv
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr}
    {k : expr_ops.ExprNatKey} {r : expr.Expr}
    (h : expr_ops.memo1_insert_if memo false k r = ok memo') :
    ∃ r', expr.dup r = ok r' ∧
      ∃ old, ron.hashmap.HashMap.insert
        expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
        expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 memo k r'
          = ok (old, memo') := by
  rw [memo1_insert_if_false] at h
  obtain ⟨r', hdup, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old, m⟩ := p
  have hm : m = memo' := Result.ok_injective h
  subst hm
  exact ⟨r', hdup, old, hins⟩

/-- The cursored `Bool` record, read back (no `dup`: the value is a `Bool`). -/
theorem memo_b1_insert_if_inv
    {memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey Bool}
    {k : expr_ops.ExprNatKey} {r : Bool}
    (h : cached.expr_ops_c.memo_b1_insert_if memo false k r = ok memo') :
    ∃ old, ron.hashmap.HashMap.insert
      expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapHashable
      expr_ops.ExprNatKey.Insts.Con_ron_coreRonHashmapEq2 memo k r
        = ok (old, memo') := by
  rw [memo_b1_insert_if_false] at h
  obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old, m⟩ := p
  have hm : m = memo' := Result.ok_injective h
  subst hm
  exact ⟨old, hins⟩

/-- The cursor-free node->node record, read back. -/
theorem memo_e_record_inv
    {memo memo' : ron.hashmap.HashMap expr.Expr expr.Expr} {e r : expr.Expr}
    (h : expr_ops.memo_e_record memo false e r = ok memo') :
    ∃ e', expr.dup e = ok e' ∧ ∃ r', expr.dup r = ok r' ∧
      ∃ old, ron.hashmap.HashMap.insert
        expr.Expr.Insts.Con_ron_coreRonHashmapHashable
        expr.Expr.Insts.Con_ron_coreRonHashmapEq2 memo e' r' = ok (old, memo') := by
  rw [memo_e_record_false] at h
  obtain ⟨e', hde, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r', hdr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old, m⟩ := p
  have hm : m = memo' := Result.ok_injective h
  subst hm
  exact ⟨e', hde, r', hdr, old, hins⟩

/-- The cursor-free node->`Bool` record, read back. -/
theorem memo_b_record_inv
    {memo memo' : ron.hashmap.HashMap expr.Expr Bool} {e : expr.Expr} {r : Bool}
    (h : expr_ops.memo_b_record memo false e r = ok memo') :
    ∃ e', expr.dup e = ok e' ∧
      ∃ old, ron.hashmap.HashMap.insert
        expr.Expr.Insts.Con_ron_coreRonHashmapHashable
        expr.Expr.Insts.Con_ron_coreRonHashmapEq2 memo e' r = ok (old, memo') := by
  rw [memo_b_record_false] at h
  obtain ⟨e', hde, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hins, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨old, m⟩ := p
  have hm : m = memo' := Result.ok_injective h
  subst hm
  exact ⟨e', hde, old, hins⟩

/-! ## The two gates

`memo_skip` and `beq_memoise` are the only places the read is *combined* with
a test the model can see, so they need a case split rather than a `rfl`. -/

/-- The `Bool` walks' gate: in the model a node is skipped exactly when it is
not compound — the leaves, which are decided on the spot. -/
@[simp] theorem memo_skip_eq (e : expr.Expr) :
    cached.expr_ops_c.memo_skip e =
      (do let b ← cached.expr_ops_c.is_compound_f e; ok (!b)) := by
  rw [cached.expr_ops_c.memo_skip]
  congr 1
  funext b
  cases b <;> simp

/-- `beq`'s gate: in the model a pair is memoised exactly when it is
recursive. -/
@[simp] theorem beq_memoise_eq (a b : expr.Expr) :
    expr.beq_memoise a b = expr.beq_recursive a := by
  rw [expr.beq_memoise]
  have h : ∀ r : Bool,
      (if r then
        (do let b2 ← ron.node.is_exclusive a
            if b2 then ok false
            else do let b3 ← ron.node.is_exclusive b
                    if b3 then ok false else ok true)
       else ok false) = ok r := by
    intro r; cases r <;> simp
  simp only [h]
  have h2 : ∀ r : Bool, (ok r : Result Bool) = pure r := fun _ => rfl
  simp only [h2, bind_pure]

end ConRon.Refine
