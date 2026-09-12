/-
Task #21, the one-pass telescope part: `inst_pis_at_f_go`/`inst_pis_at_f` and
`inst_lams_at_f_go`/`inst_lams_at_f` (con-leche's `instPisAtFGo`
`ExprOps.lean:1183`, `instPisAtF` `:1191`, `instLamsAtFGo` `:1197`,
`instLamsAtF` `:1205`).

The `*F` walks peel the *raw* binders while the pending substitutions
accumulate in `acc` (innermost first), and give each domain and the residual a
single `instantiateList` pass instead of one `instantiate1` pass per argument;
when the raw telescope is shorter than the argument list the `Go` walk reports
`none` and the wrapper falls back to the sequential `instPisAt`/`instLamsAt`,
which is what makes the wrappers' equation unconditional.

Two shapes, both forced by the port's deviations (task #13, deviation 3):

* the port walks `args` by an **index** and accumulates the domains into `out`
  on the way *in*, where con-leche consumes a list and conses on the way out.
  So the `Go` lemma is stated at `(absExprs args).drop i` with `absExprs out`
  *prepended* to con-leche's answer: `r.map … = (instPisAtFGo acc (drop i args)
  e).map (fun p => (absExprs out ++ p.1, p.2))`.  An `Option`-valued result is
  compared under `Option.map` of the abstraction, with the well-formedness of a
  `some`'s two components as the second conjunct (`∀ p, r = some p → …`).
* the recursion descends into an expression that is *not* a subterm of `e`
  (`instantiate1 body args[i]` for the sequential walks), so the induction is
  a strong induction on `args.length - i` with `cases he` inside it, not an
  induction on the `ExprWF` derivation: nine of the ten constructors return
  `none`, and the tenth supplies the children's well-formedness.

`inst_pis_at_from`/`inst_lams_at_from` (and their `i = 0` wrappers) belong to
another worker's group but are the wrappers' fall-back arm, so the four
`*_local` lemmas below prove exactly what that arm needs; they are duplicates
to be reconciled at merge.
-/
import ConRon.Refine.ExprOpsList

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## `Vec<Expr>` plumbing -/

/-- The abstracted argument list, one index step on: what the port's `i` and
con-leche's `a :: as` have in common. -/
theorem absExprs_drop_cons {args : alloc.vec.Vec expr.Expr} {i : Nat}
    (hi : i < args.val.length) :
    (absExprs args).drop i = absExpr args.val[i] :: (absExprs args).drop (i + 1) := by
  rw [absExprs, ← List.map_drop, List.drop_eq_getElem_cons hi, List.map_cons,
    List.map_drop]

/-- `Vec::push`, through the abstraction. -/
theorem absExprs_push {out out1 : alloc.vec.Vec expr.Expr} {x : expr.Expr}
    (h : alloc.vec.Vec.push out x = ok out1) :
    absExprs out1 = absExprs out ++ [absExpr x] := by
  rw [absExprs, absExprs, vec_push_val h, List.map_append, List.map_cons, List.map_nil]

/-- `Vec::push` preserves well-formedness. -/
theorem ExprsWF_push {out out1 : alloc.vec.Vec expr.Expr} {x : expr.Expr}
    (hout : ExprsWF out) (hx : ExprWF x) (h : alloc.vec.Vec.push out x = ok out1) :
    ExprsWF out1 := by
  intro y hy
  rw [vec_push_val h] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact hout y hy
  · rw [List.mem_singleton.1 hy]; exact hx

/-- An entry of a well-formed `Vec<Expr>` is well formed. -/
theorem ExprsWF_getElem {args : alloc.vec.Vec expr.Expr} {i : Nat}
    (hargs : ExprsWF args) (hi : i < args.val.length) : ExprWF args.val[i] :=
  hargs _ (List.getElem_mem hi)

/-- `expr_ops::cons_expr` is Lean's `a :: acc` on the model (task #13's
deviation 3: a `Vec` has no cheap cons, so the accumulator is rebuilt). -/
theorem cons_expr_val_local {a : expr.Expr} {acc r : alloc.vec.Vec expr.Expr}
    (h : expr_ops.cons_expr a acc = ok r) : r.val = a :: acc.val := by
  rw [expr_ops.cons_expr] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨e, hdup, out, hpush, hcopy⟩ := h
  have he : e = a := Expr.dup_eq hdup
  have hout : out.val = [a] := by
    rw [vec_push_val hpush, he]; simp
  have hlen : (alloc.vec.Vec.len acc).val = acc.val.length := alloc.vec.Vec.len_val _
  have := exprs_copy_upto_val ((alloc.vec.Vec.len acc).val - (0#usize : Std.Usize).val)
    acc out r (alloc.vec.Vec.len acc) 0#usize rfl hcopy
  rw [this, hout, show (0#usize : Std.Usize).val = 0 by scalar_tac, hlen]
  simp

/-- `cons_expr`, as the abstraction and the invariant see it. -/
theorem cons_expr_refines_local {a : expr.Expr} {acc r : alloc.vec.Vec expr.Expr}
    (ha : ExprWF a) (hacc : ExprsWF acc) (h : expr_ops.cons_expr a acc = ok r) :
    absExprs r = absExpr a :: absExprs acc ∧ ExprsWF r := by
  refine ⟨by rw [absExprs, absExprs, cons_expr_val_local h, List.map_cons], ?_⟩
  intro y hy
  rw [cons_expr_val_local h] at hy
  rcases List.mem_cons.1 hy with hy | hy
  · rw [hy]; exact ha
  · exact hacc y hy

/-! ## The sequential fall-back (another worker's group; `*_local` duplicates)

`inst_pis_at_from`/`inst_lams_at_from` fold `instantiate1` over the argument
list, accumulating the domains on the way in.  The two lemmas below are what
the `*F` wrappers' `none` arm needs. -/

/-- `expr_ops::inst_pis_at_from` refines `Expr.instPisAt` (`ExprOps.lean:1149`)
at the remaining arguments, with the accumulated domains prepended. -/
theorem inst_pis_at_from_val_local (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprsWF args → ExprWF e → ExprsWF out →
      expr_ops.inst_pis_at_from args i e out = ok r →
      r.map (fun p => (absExprs p.1, absExpr p.2)) =
          (ConLeche.Expr.instPisAt ((absExprs args).drop i.val) (absExpr e)).map
            (fun p => (absExprs out ++ p.1, p.2)) ∧
        ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i e out r hN hargs he hout h
    rw [expr_ops.inst_pis_at_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : args.val.length ≤ i.val := by scalar_tac
      have hdrop : (absExprs args).drop i.val = [] := by
        rw [absExprs, ← List.map_drop, List.drop_eq_nil_of_le hle, List.map_nil]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hdup, hr⟩ := h
      have he1 : e1 = e := Expr.dup_eq hdup
      subst he1
      rw [← Result.ok_injective hr, hdrop]
      refine ⟨by simp [ConLeche.Expr.instPisAt], ?_⟩
      intro p hp
      rw [← Option.some.inj hp]
      exact ⟨hout, he⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by scalar_tac
      rw [absExprs_drop_cons hlt]
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨e1, hdup, out1, hpush, e2, hidx, b, hinst, i2, hi2, hrec⟩ := h
        have he1 : e1 = ty := Expr.dup_eq hdup
        subst he1
        obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
        obtain ⟨habs, hwfb⟩ := instantiate1_refines hbo (ExprsWF_getElem hargs hlt2) hinst
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec1, hrec2⟩ := ih (args.val.length - i2.val) (by omega) args i2 b out1 r
          rfl hargs hwfb (ExprsWF_push hout hty hpush) hrec
        refine ⟨?_, hrec2⟩
        rw [hrec1, hi2v, habs, Expr.val_zero, absExprs_push hpush]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instPisAt]
        cases ConLeche.Expr.instPisAt ((absExprs args).drop (i.val + 1))
            ((absExpr bo).instantiate1 (absExpr args.val[i.val])) with
        | none => rfl
        | some q => simp
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩

/-- `expr_ops::inst_pis_at` refines `Expr.instPisAt` (`ExprOps.lean:1149`). -/
theorem inst_pis_at_refines_local {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_pis_at args e = ok r) :
    r.map (fun p => (absExprs p.1, absExpr p.2)) =
        ConLeche.Expr.instPisAt (absExprs args) (absExpr e) ∧
      ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  rw [expr_ops.inst_pis_at] at h
  obtain ⟨h1, h2⟩ := inst_pis_at_from_val_local
    (args.val.length - (0#usize : Std.Usize).val) args 0#usize e
    (alloc.vec.Vec.new expr.Expr) r rfl hargs he (by intro x hx; simp at hx) h
  refine ⟨?_, h2⟩
  rw [h1, show (0#usize : Std.Usize).val = 0 by scalar_tac]
  simp [absExprs, alloc.vec.Vec.new]

/-- `expr_ops::inst_lams_at_from` refines `Expr.instLamsAt`
(`ExprOps.lean:1157`); the `λ` twin of `inst_pis_at_from_val_local`. -/
theorem inst_lams_at_from_val_local (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprsWF args → ExprWF e → ExprsWF out →
      expr_ops.inst_lams_at_from args i e out = ok r →
      r.map (fun p => (absExprs p.1, absExpr p.2)) =
          (ConLeche.Expr.instLamsAt ((absExprs args).drop i.val) (absExpr e)).map
            (fun p => (absExprs out ++ p.1, p.2)) ∧
        ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i e out r hN hargs he hout h
    rw [expr_ops.inst_lams_at_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : args.val.length ≤ i.val := by scalar_tac
      have hdrop : (absExprs args).drop i.val = [] := by
        rw [absExprs, ← List.map_drop, List.drop_eq_nil_of_le hle, List.map_nil]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hdup, hr⟩ := h
      have he1 : e1 = e := Expr.dup_eq hdup
      subst he1
      rw [← Result.ok_injective hr, hdrop]
      refine ⟨by simp [ConLeche.Expr.instLamsAt], ?_⟩
      intro p hp
      rw [← Option.some.inj hp]
      exact ⟨hout, he⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by scalar_tac
      rw [absExprs_drop_cons hlt]
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨e1, hdup, out1, hpush, e2, hidx, b, hinst, i2, hi2, hrec⟩ := h
        have he1 : e1 = ty := Expr.dup_eq hdup
        subst he1
        obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
        obtain ⟨habs, hwfb⟩ := instantiate1_refines hbo (ExprsWF_getElem hargs hlt2) hinst
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec1, hrec2⟩ := ih (args.val.length - i2.val) (by omega) args i2 b out1 r
          rfl hargs hwfb (ExprsWF_push hout hty hpush) hrec
        refine ⟨?_, hrec2⟩
        rw [hrec1, hi2v, habs, Expr.val_zero, absExprs_push hpush]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instLamsAt]
        cases ConLeche.Expr.instLamsAt ((absExprs args).drop (i.val + 1))
            ((absExpr bo).instantiate1 (absExpr args.val[i.val])) with
        | none => rfl
        | some q => simp
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩

/-- `expr_ops::inst_lams_at` refines `Expr.instLamsAt` (`ExprOps.lean:1157`). -/
theorem inst_lams_at_refines_local {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_lams_at args e = ok r) :
    r.map (fun p => (absExprs p.1, absExpr p.2)) =
        ConLeche.Expr.instLamsAt (absExprs args) (absExpr e) ∧
      ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  rw [expr_ops.inst_lams_at] at h
  obtain ⟨h1, h2⟩ := inst_lams_at_from_val_local
    (args.val.length - (0#usize : Std.Usize).val) args 0#usize e
    (alloc.vec.Vec.new expr.Expr) r rfl hargs he (by intro x hx; simp at hx) h
  refine ⟨?_, h2⟩
  rw [h1, show (0#usize : Std.Usize).val = 0 by scalar_tac]
  simp [absExprs, alloc.vec.Vec.new]

/-! ## The one-pass walks -/

/-- **`expr_ops::inst_pis_at_f_go` refines `Expr.instPisAtFGo`**
(`ExprOps.lean:1183-1188`): the domains already accumulated in `out` are
prepended to con-leche's answer, and `acc` -- the pending substitutions,
innermost first -- is what each domain and the residual are `instantiateList`ed
with. -/
theorem inst_pis_at_f_go_refines (N : Nat) :
    ∀ (acc args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprsWF acc → ExprsWF args → ExprWF e →
      ExprsWF out → expr_ops.inst_pis_at_f_go acc args i e out = ok r →
      r.map (fun p => (absExprs p.1, absExpr p.2)) =
          (ConLeche.Expr.instPisAtFGo (absExprs acc) ((absExprs args).drop i.val) (absExpr e)).map
            (fun p => (absExprs out ++ p.1, p.2)) ∧
        ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro acc args i e out r hN hacc hargs he hout h
    rw [expr_ops.inst_pis_at_f_go.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : args.val.length ≤ i.val := by scalar_tac
      have hdrop : (absExprs args).drop i.val = [] := by
        rw [absExprs, ← List.map_drop, List.drop_eq_nil_of_le hle, List.map_nil]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hfast, hr⟩ := h
      obtain ⟨habs, hwf⟩ := instantiate_list_fast_refines he hacc hfast
      rw [← Result.ok_injective hr, hdrop]
      refine ⟨?_, ?_⟩
      · rw [Option.map_some, habs, Expr.val_zero, ConLeche.Expr.instPisAtFGo]
        simp
      · intro p hp
        rw [← Option.some.inj hp]
        exact ⟨hout, hwf⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by scalar_tac
      rw [absExprs_drop_cons hlt]
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨e1, hdom, out1, hpush, e2, hidx, acc2, hcons, i2, hi2, hrec⟩ := h
        obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
        obtain ⟨habsd, hwfd⟩ := instantiate_list_fast_refines hty hacc hdom
        obtain ⟨habsa, hwfa⟩ :=
          cons_expr_refines_local (ExprsWF_getElem hargs hlt2) hacc hcons
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec1, hrec2⟩ := ih (args.val.length - i2.val) (by omega) acc2 args i2 bo
          out1 r rfl hwfa hargs hbo (ExprsWF_push hout hwfd hpush) hrec
        refine ⟨?_, hrec2⟩
        rw [hrec1, hi2v, habsa, absExprs_push hpush, habsd, Expr.val_zero]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instPisAtFGo]
        cases ConLeche.Expr.instPisAtFGo (absExpr args.val[i.val] :: absExprs acc)
            ((absExprs args).drop (i.val + 1)) (absExpr bo) with
        | none => rfl
        | some q => simp
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩

/-- **`expr_ops::inst_pis_at_f` refines `Expr.instPisAtF`**
(`ExprOps.lean:1191-1194`), *unconditionally*: on `none` the port falls back to
the sequential `inst_pis_at`, exactly as the cited definition does. -/
theorem inst_pis_at_f_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_pis_at_f args e = ok r) :
    r.map (fun p => (absExprs p.1, absExpr p.2)) =
        ConLeche.Expr.instPisAtF (absExprs args) (absExpr e) ∧
      ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  rw [expr_ops.inst_pis_at_f] at h
  obtain ⟨o, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hgo1, hgo2⟩ := inst_pis_at_f_go_refines
    (args.val.length - (0#usize : Std.Usize).val) (alloc.vec.Vec.new expr.Expr) args
    0#usize e (alloc.vec.Vec.new expr.Expr) o rfl (by intro x hx; simp at hx) hargs he
    (by intro x hx; simp at hx) hgo
  rw [show (0#usize : Std.Usize).val = 0 by scalar_tac] at hgo1
  rw [ConLeche.Expr.instPisAtF, show absExprs (alloc.vec.Vec.new expr.Expr) = [] from by
    simp [absExprs, alloc.vec.Vec.new]] at hgo1 ⊢
  cases o with
  | none =>
    rw [Option.map_none] at hgo1
    rw [(Option.map_eq_none_iff).mp hgo1.symm]
    exact inst_pis_at_refines_local hargs he h
  | some q =>
    have hr : r = some q := (Result.ok_injective h).symm
    subst hr
    cases hc : ConLeche.Expr.instPisAtFGo [] (absExprs args) (absExpr e) with
    | none => rw [hc] at hgo1; simp at hgo1
    | some q' =>
      rw [hc] at hgo1
      rw [hc, hgo1]
      simp


/-- **`expr_ops::inst_lams_at_f_go` refines `Expr.instLamsAtFGo`**
(`ExprOps.lean:1197-1202`); the `λ` twin of `inst_pis_at_f_go_refines`. -/
theorem inst_lams_at_f_go_refines (N : Nat) :
    ∀ (acc args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprsWF acc → ExprsWF args → ExprWF e →
      ExprsWF out → expr_ops.inst_lams_at_f_go acc args i e out = ok r →
      r.map (fun p => (absExprs p.1, absExpr p.2)) =
          (ConLeche.Expr.instLamsAtFGo (absExprs acc) ((absExprs args).drop i.val) (absExpr e)).map
            (fun p => (absExprs out ++ p.1, p.2)) ∧
        ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro acc args i e out r hN hacc hargs he hout h
    rw [expr_ops.inst_lams_at_f_go.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : args.val.length ≤ i.val := by scalar_tac
      have hdrop : (absExprs args).drop i.val = [] := by
        rw [absExprs, ← List.map_drop, List.drop_eq_nil_of_le hle, List.map_nil]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hfast, hr⟩ := h
      obtain ⟨habs, hwf⟩ := instantiate_list_fast_refines he hacc hfast
      rw [← Result.ok_injective hr, hdrop]
      refine ⟨?_, ?_⟩
      · rw [Option.map_some, habs, Expr.val_zero, ConLeche.Expr.instLamsAtFGo]
        simp
      · intro p hp
        rw [← Option.some.inj hp]
        exact ⟨hout, hwf⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by scalar_tac
      rw [absExprs_drop_cons hlt]
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨e1, hdom, out1, hpush, e2, hidx, acc2, hcons, i2, hi2, hrec⟩ := h
        obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
        obtain ⟨habsd, hwfd⟩ := instantiate_list_fast_refines hty hacc hdom
        obtain ⟨habsa, hwfa⟩ :=
          cons_expr_refines_local (ExprsWF_getElem hargs hlt2) hacc hcons
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec1, hrec2⟩ := ih (args.val.length - i2.val) (by omega) acc2 args i2 bo
          out1 r rfl hwfa hargs hbo (ExprsWF_push hout hwfd hpush) hrec
        refine ⟨?_, hrec2⟩
        rw [hrec1, hi2v, habsa, absExprs_push hpush, habsd, Expr.val_zero]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instLamsAtFGo]
        cases ConLeche.Expr.instLamsAtFGo (absExpr args.val[i.val] :: absExprs acc)
            ((absExprs args).drop (i.val + 1)) (absExpr bo) with
        | none => rfl
        | some q => simp
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩

/-- **`expr_ops::inst_lams_at_f` refines `Expr.instLamsAtF`**
(`ExprOps.lean:1205-1208`). -/
theorem inst_lams_at_f_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_lams_at_f args e = ok r) :
    r.map (fun p => (absExprs p.1, absExpr p.2)) =
        ConLeche.Expr.instLamsAtF (absExprs args) (absExpr e) ∧
      ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  rw [expr_ops.inst_lams_at_f] at h
  obtain ⟨o, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hgo1, hgo2⟩ := inst_lams_at_f_go_refines
    (args.val.length - (0#usize : Std.Usize).val) (alloc.vec.Vec.new expr.Expr) args
    0#usize e (alloc.vec.Vec.new expr.Expr) o rfl (by intro x hx; simp at hx) hargs he
    (by intro x hx; simp at hx) hgo
  rw [show (0#usize : Std.Usize).val = 0 by scalar_tac] at hgo1
  rw [ConLeche.Expr.instLamsAtF, show absExprs (alloc.vec.Vec.new expr.Expr) = [] from by
    simp [absExprs, alloc.vec.Vec.new]] at hgo1 ⊢
  cases o with
  | none =>
    rw [Option.map_none] at hgo1
    rw [(Option.map_eq_none_iff).mp hgo1.symm]
    exact inst_lams_at_refines_local hargs he h
  | some q =>
    have hr : r = some q := (Result.ok_injective h).symm
    subst hr
    cases hc : ConLeche.Expr.instLamsAtFGo [] (absExprs args) (absExpr e) with
    | none => rw [hc] at hgo1; simp at hgo1
    | some q' =>
      rw [hc] at hgo1
      rw [hc, hgo1]
      simp

end ConRon.Refine.ExprOps


