/-
The `instantiateList` family of `crates/con-ron-core/src/kernel/expr_ops.rs`
(task #21, part of P3.3): the two `Vec<Expr>` copies `exprs_copy_upto` and
`take_exprs`, the *pure* bulk substitution `instantiate_list`
(`ConLeche/Kernel/ExprOps.lean:211-235`), its memoized twin
`instantiate_list_go` (`:268-304`) and the executed wrapper
`instantiate_list_fast` (`:372-378`).

Statements are against the **logical** `ConLeche.Expr.instantiateList`, in the
exact-result-on-success shape of DESIGN.md §3.5.

Two things needed care.

* **`instantiateList` is not a structural recursion.**  Its `.bvar` arm
  recurses into a *replacement* `vs[j - d]` with the shorter list
  `vs.take (j - d)`, so con-leche measures `(vs.length, sizeOf e)`.  The proof
  mirrors that: a strong induction on `vs.val.length` *outside* the induction
  on the `ExprWF` derivation, and the outer step is applied to the copy
  `take_exprs vs i`, whose length is `i < vs.val.length`.
* **The `u64`/`usize` round trip.**  The port computes the list length as a
  `usize`, casts it to `u64` to compare with `j - d`, then casts the difference
  back to a `usize` index.  On a 32-bit target the second cast is a real
  truncation, so `usize_cast_u64_val` and `u64_cast_usize_val_of_lt` carry the
  two directions; the bound that makes the inner one the identity is
  `Vec.property` (a `Vec`'s length is at most `Usize.max`).

Merged at task #47 with the `abstract1`/`lowerBVars`/`instantiate1Lift` group
(task #21's `ExprOpsAbs1.lean`), whose module note is the section comment
halfway down; both are the *substitution* half of `expr_ops.rs`, and both need
`ExprOpsFields.lean`'s derived-field readers.
-/
import ConRon.Refine.ExprOpsFields

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## The two machine-word casts

`usize → u64` never loses anything (a `usize` is at most 64 bits); `u64 →
usize` does, so it needs the value to fit. -/

/-- A `usize` is at most 64 bits wide. -/
theorem platform_numBits_le : System.Platform.numBits ≤ 64 := by
  cases System.Platform.numBits_eq with
  | inl h => simp [h]
  | inr h => simp [h]

/-- A `u64` cast to a `usize` keeps its value when it fits — which it does
whenever it indexes a `Vec` (`Vec.property`). -/
theorem u64_cast_usize_val_of_lt {x : Std.U64} {n : Nat} (hn : n ≤ Std.Usize.max)
    (hx : x.val < n) : (Std.UScalar.cast .Usize x : Std.Usize).val = x.val := by
  rw [Std.UScalar.cast_val_eq, Std.UScalarTy.Usize_numBits_eq]
  refine Nat.mod_eq_of_lt ?_
  have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
  have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  omega

/-! ## The `Vec<Expr>` copies

`exprs_copy_upto xs k i out` appends `xs[i], …, xs[min k (xs.len) - 1]` to
`out` (task #13's deviation 5: Lean's lists are shared, a `Vec` has to copy);
`take_exprs` is its `i = 0`, `out = []` wrapper and *is* `List.take`. -/

/-- `Vec::index`, in the `getElem`-with-a-proof form con-leche's own
`vs[j - d]` wants.  (`HashMap.vec_index_eq` lands on `v.val[i]!`, which needs
an `Inhabited` instance the generated `Expr` has none of.) -/
theorem vec_index_val {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    ∃ hlt : i.val < v.val.length, x = v.val[i.val] := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · have hlt : i.val < v.val.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hi; simp at hi
    rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    refine ⟨hlt, ?_⟩
    rw [List.getElem?_eq_getElem hlt] at hi
    rw [← Result.ok_injective h, Option.some.inj hi]

/-- One step of an index walk over a list, in the `drop`/`take` form the
accumulator recursion produces. -/
theorem drop_take_succ {α : Type} {l : List α} {i n : Nat} (hi : i < l.length) :
    (l.drop i).take (n + 1) = l[i] :: (l.drop (i + 1)).take n := by
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]

/-- `expr_ops::take_exprs` is `List.take` on the model. -/
theorem take_exprs_val {xs r : alloc.vec.Vec expr.Expr} {k : Std.Usize}
    (h : expr_ops.take_exprs xs k = ok r) : r.val = xs.val.take k.val := by
  rw [expr_ops.take_exprs] at h
  have := exprs_copy_upto_val (k.val - (0#usize : Std.Usize).val) xs k 0#usize
    (alloc.vec.Vec.new expr.Expr) r rfl h
  simpa using this

/-- `take_exprs`, as the abstraction and the invariant see it. -/
theorem take_exprs_refines {xs r : alloc.vec.Vec expr.Expr} {k : Std.Usize}
    (hxs : ExprsWF xs) (h : expr_ops.take_exprs xs k = ok r) :
    absExprs r = (absExprs xs).take k.val ∧ ExprsWF r := by
  refine ⟨?_, ?_⟩
  · rw [absExprs, absExprs, take_exprs_val h, List.map_take]
  · intro x hx
    rw [take_exprs_val h] at hx
    exact hxs x (List.mem_of_mem_take hx)

/-! ## `instantiate_list`, the pure walk (`ExprOps.lean:191-235`) -/

/-- **`expr_ops::instantiate_list` refines `Expr.instantiateList`**, by the
nested induction con-leche's `termination_by (vs.length, sizeOf e)` calls for:
a strong induction on the replacement list's length, and inside it an
induction on the `ExprWF` derivation of the node being walked. -/
theorem instantiate_list_refines_aux (N : Nat) :
    ∀ (vs : alloc.vec.Vec expr.Expr), vs.val.length = N → ExprsWF vs →
      ∀ (e : expr.Expr), ExprWF e → ∀ (d : Std.U64) (r : expr.Expr),
        expr_ops.instantiate_list e vs d = ok r →
        absExpr r = ConLeche.Expr.instantiateList (absExpr e) (absExprs vs) d.val ∧
          ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro vs hN hvs e he
    induction he with
    | @bvar i e h1 =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
      split at h
      · rename_i hlt
        have hlt' : i.val < d.val := by scalar_tac
        refine ⟨?_, Expr.bvar_wf h⟩
        rw [Expr.bvar_refines h]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instantiateList, if_pos hlt']
      · rename_i hlt
        have hge : d.val ≤ i.val := by scalar_tac
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n, hn, i1, hi1, h⟩ := h
        have hnv : n.val = vs.val.length := by
          rw [← Result.ok_injective hn, usize_cast_u64_val, alloc.vec.Vec.len_val]
        have hi1v : i1.val = i.val - d.val := HashMap.uscalar_sub_eq hi1
        split at h
        · rename_i hin
          have hin' : i.val - d.val < vs.val.length := by
            rw [← hnv, ← hi1v]; scalar_tac
          simp only [bind_eq_ok_iff] at h
          obtain ⟨i2, hi2, pre, hpre, e1, hidx, hrec⟩ := h
          have hi2v : i2.val = i.val - d.val := by
            rw [← Result.ok_injective hi2,
              u64_cast_usize_val_of_lt (n := vs.val.length) (alloc.vec.Vec.property vs)
                (by rw [hi1v]; exact hin'), hi1v]
          obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
          have hprel : pre.val.length = i.val - d.val := by
            rw [take_exprs_val hpre, List.length_take, hi2v]
            omega
          have hwfpre : ExprsWF pre := (take_exprs_refines hvs hpre).2
          have hwfe1 : ExprWF vs.val[i2.val] := hvs _ (List.getElem_mem hlt2)
          obtain ⟨habs, hwf⟩ := ihN pre.val.length (by rw [hprel]; omega) pre rfl hwfpre
            _ hwfe1 d r hrec
          have hlen : i.val - d.val < (absExprs vs).length := by
            rw [absExprs, List.length_map]; exact hin'
          -- the replacement con-leche picks is the entry the port indexed;
          -- stated through `getElem?` so that no proof term has to be transported
          have hget : (absExprs vs)[i.val - d.val] = absExpr vs.val[i2.val] := by
            refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
            rw [absExprs, List.getElem?_map, ← hi2v, List.getElem?_eq_getElem hlt2]
            rfl
          refine ⟨?_, hwf⟩
          rw [habs, (take_exprs_refines hvs hpre).1]
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList, if_neg (show ¬ (i.val < d.val) by omega),
            dif_pos hlen, hget, ← hi2v]
        · rename_i hin
          have hin' : ¬ (i.val - d.val < vs.val.length) := by
            rw [← hnv, ← hi1v]; scalar_tac
          simp only [bind_eq_ok_iff] at h
          obtain ⟨i2, hi2, h⟩ := h
          have hi2v : i2.val = i.val - n.val := HashMap.uscalar_sub_eq hi2
          refine ⟨?_, Expr.bvar_wf h⟩
          rw [Expr.bvar_refines h, hi2v, hnv]
          simp only [absExpr_mk, absExprKind]
          rw [ConLeche.Expr.instantiateList, if_neg (by omega)]
          have hlen : ¬ (i.val - d.val < (absExprs vs).length) := by
            rw [absExprs, List.length_map]; exact hin'
          rw [dif_neg hlen, absExprs, List.length_map]
    | @fvar idx ty e hty h1 ih =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.fvar hty h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @sort u e hu h1 =>
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.sort hu h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @mk_const n us e hn hus h1 =>
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.mk_const hn hus h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @lit l e hl h1 =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.lit hl h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @app f a e hf ha h1 ihf iha =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨f2, hf2, a2, ha2, happ⟩ := h
      obtain ⟨habs2, hwf2⟩ := ihf d f2 hf2
      obtain ⟨habs3, hwf3⟩ := iha d a2 ha2
      refine ⟨?_, Expr.app_wf hwf2 hwf3 happ⟩
      rw [Expr.app_refines happ, habs2, habs3]
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @lam ty bo m e hty hbo hm0 h1 ihty ihbo =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨t, ht, dd, hdd, b, hb, bm, hbm, hlam⟩ := h
      obtain ⟨habs2, hwf2⟩ := ihty d t ht
      obtain ⟨habs3, hwf3⟩ := ihbo dd b hb
      refine ⟨?_, Expr.lam_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hlam⟩
      rw [Expr.lam_refines hlam, habs2, habs3, Expr.binder_meta_dup_eq hbm,
        HashMap.uscalar_add_eq hdd, Expr.val_one]
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @forall_e ty bo m e hty hbo hm0 h1 ihty ihbo =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨t, ht, dd, hdd, b, hb, bm, hbm, hfa⟩ := h
      obtain ⟨habs2, hwf2⟩ := ihty d t ht
      obtain ⟨habs3, hwf3⟩ := ihbo dd b hb
      refine ⟨?_, Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa⟩
      rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
        HashMap.uscalar_add_eq hdd, Expr.val_one]
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨t, ht, w2, hw2, dd, hdd, b, hb, hlet⟩ := h
      obtain ⟨habs2, hwf2⟩ := ihty d t ht
      obtain ⟨habs3, hwf3⟩ := ihw d w2 hw2
      obtain ⟨habs4, hwf4⟩ := ihbo dd b hb
      refine ⟨?_, Expr.let_e_wf hwf2 hwf3 hwf4 hlet⟩
      rw [Expr.let_e_refines hlet, habs2, habs3, habs4, HashMap.uscalar_add_eq hdd,
        Expr.val_one]
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @proj s i x e hs hx h1 ih =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨u, hu, n2, hn2, hproj⟩ := h
      obtain ⟨habs2, hwf2⟩ := ih d u hu
      have hsn : n2 = s := Result.ok_injective (hn2.symm.trans (name_dup_eq s))
      subst hsn
      refine ⟨?_, Expr.proj_wf hs hwf2 hproj⟩
      rw [Expr.proj_refines hproj, habs2]
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]

/-- **`expr_ops::instantiate_list` refines `Expr.instantiateList`** (the pure
walk, `ExprOps.lean:211-235`). -/
theorem instantiate_list_refines {e r : expr.Expr} {vs : alloc.vec.Vec expr.Expr}
    {d : Std.U64} (he : ExprWF e) (hvs : ExprsWF vs)
    (h : expr_ops.instantiate_list e vs d = ok r) :
    absExpr r = ConLeche.Expr.instantiateList (absExpr e) (absExprs vs) d.val ∧
      ExprWF r :=
  instantiate_list_refines_aux vs.val.length vs rfl hvs e he d r h

/-! ## `instantiate_list_go`, the memoized walk (`ExprOps.lean:268-304`)

con-leche's `InstLMemoInv` (`:248`), through `MemoInv`; the proof is
`instantiate1_go_refines`'s, with the `.bvar` arm deferring to the pure walk
exactly as the cited code does. -/

/-- con-leche's `InstLMemoInv` (`ExprOps.lean:248`) as the `Q` of `MemoInv`. -/
def InstLQ (vs : List ConLeche.Expr) : ConLeche.Expr × Nat → expr.Expr → Prop :=
  fun k r => ExprWF r ∧ absExpr r = ConLeche.Expr.instantiateList k.1 vs k.2

theorem instantiate_list_go_refines {vs : alloc.vec.Vec expr.Expr} (hvs : ExprsWF vs)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ (memo memo' : ron.hashmap.HashMap expr_ops.ExprNatKey expr.Expr) (d : Std.U64)
      (r : expr.Expr),
      MemoInv KeyWF absKey (InstLQ (absExprs vs)) memo →
      expr_ops.instantiate_list_go vs memo e d = ok (r, memo') →
      (ExprWF r ∧
          absExpr r = ConLeche.Expr.instantiateList (absExpr e) (absExprs vs) d.val) ∧
        MemoInv KeyWF absKey (InstLQ (absExprs vs)) memo' := by
  induction he with
  | @bvar i e h1 =>
    intro memo memo' d r hm h
    have hwfe : ExprWF e := ExprWF.bvar h1
    obtain ⟨d1, hde, -, -, -⟩ := Expr.bvar_inv h1
    rw [expr_ops.instantiate_list_go.eq_def, hde] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨r0, hpure, hr, hmm⟩ := h
    subst hr; subst hmm
    rw [← hde] at hpure
    obtain ⟨habs, hwf⟩ := instantiate_list_refines hwfe hvs hpure
    exact ⟨⟨hwf, habs⟩, hm⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    refine ⟨⟨ExprWF.fvar hty h1, ?_⟩, hm⟩
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.instantiateList]
  | @sort u e hu h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    refine ⟨⟨ExprWF.sort hu h1, ?_⟩, hm⟩
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.instantiateList]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    refine ⟨⟨ExprWF.mk_const hn hus h1, ?_⟩, hm⟩
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.instantiateList]
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind, bind_eq_ok_iff, Result.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨c, hdup, hr, hmm⟩ := h
    rw [Expr.dup_eq hdup] at hr
    subst hr; subst hmm
    refine ⟨⟨ExprWF.lit hl h1, ?_⟩, hm⟩
    simp only [absExpr_mk, absExprKind]
    rw [ConLeche.Expr.instantiateList]
  | @app f a e hf ha h1 ihf iha =>
    have hwfe : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := InstLQ (absExprs vs))
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
      have hans : InstLQ (absExprs vs)
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
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := InstLQ (absExprs vs))
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
      have hans : InstLQ (absExprs vs)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Lam ty bo m)), d⟩) r := by
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
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := InstLQ (absExprs vs))
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
      have hans : InstLQ (absExprs vs)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.ForallE ty bo m)), d⟩) r := by
        refine ⟨Expr.forall_e_wf hwf2 hwf3 (Expr.binder_meta_dup_eq hbm ▸ hm0) hfa, ?_⟩
        rw [Expr.forall_e_refines hfa, habs2, habs3, Expr.binder_meta_dup_eq hbm,
          HashMap.uscalar_add_eq hdd, Expr.val_one]
        simp only [absKey_mk, absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instantiateList]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm3 (keyWF_mk hwfe) hans hins
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    have hwfe : ExprWF e := ExprWF.let_e hty hw hbo h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := InstLQ (absExprs vs))
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
      have hans : InstLQ (absExprs vs)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.LetE ty w bo)), d⟩) r := by
        refine ⟨Expr.let_e_wf hwf2 hwf3 hwf4 hlet, ?_⟩
        rw [Expr.let_e_refines hlet, habs2, habs3, habs4, HashMap.uscalar_add_eq hdd,
          Expr.val_one]
        simp only [absKey_mk, absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instantiateList]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm4 (keyWF_mk hwfe) hans hins
  | @proj s i x e hs hx h1 ih =>
    have hwfe : ExprWF e := ExprWF.proj hs hx h1
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro memo memo' d r hm h
    rw [expr_ops.instantiate_list_go.eq_def] at h
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
      have hhit := MemoInv.hit (KWF := KeyWF) (absK := absKey) (Q := InstLQ (absExprs vs))
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
      have hans : InstLQ (absExprs vs)
          (absKey ⟨expr.Expr.mk (expr.ExprNode.mk d1 (expr.ExprKind.Proj n2 i x)), d⟩) r := by
        refine ⟨Expr.proj_wf hs hwf2 hproj, ?_⟩
        rw [Expr.proj_refines hproj, habs2]
        simp only [absKey_mk, absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instantiateList]
      refine ⟨hans, ?_⟩
      rw [Expr.dup_eq hdup] at hins
      exact MemoInv.set key_exact hm2 (keyWF_mk hwfe) hans hins

/-- **`expr_ops::instantiate_list_fast` refines `Expr.instantiateList`**: the
fresh memo satisfies `InstLMemoInv` vacuously, so the memoized walk *is* the
logical function -- con-leche's `instantiateList_eq_instantiateListFast`
(`ExprOps.lean:375-378`). -/
theorem instantiate_list_fast_refines {e r : expr.Expr} {vs : alloc.vec.Vec expr.Expr}
    {d : Std.U64} (he : ExprWF e) (hvs : ExprsWF vs)
    (h : expr_ops.instantiate_list_fast e vs d = ok r) :
    absExpr r = ConLeche.Expr.instantiateList (absExpr e) (absExprs vs) d.val ∧
      ExprWF r := by
  rw [expr_ops.instantiate_list_fast] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    instantiate_list_go_refines hvs he memo memo' d r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

/-!Task #21, the three cutoff-and-memo walks of `kernel::expr_ops`: `abstract1`
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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


/-- **`expr_ops::abstract1` refines `Expr.abstract1`.**  The fresh memo
satisfies `Abs1MemoInv` vacuously (`MemoInv.empty`), so the walk's own lemma
gives the logical function directly -- which is what con-leche's `@[csimp]`
equation for `abstract1Fast` says. -/
theorem abstract1_refines {e r : expr.Expr} {d k : Std.U64} (he : ExprWF e)
    (h : expr_ops.abstract1 e d k = ok r) :
    absExpr r = ConLeche.Expr.abstract1 (absExpr e) d.val k.val ∧ ExprWF r := by
  rw [expr_ops.abstract1] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    abstract1_go_refines he memo memo' k r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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


/-- **`expr_ops::lower_bvars` refines `Expr.lowerBVars`**: the fresh memo
satisfies `LowerMemoInv` vacuously. -/
theorem lower_bvars_refines {amount c : Std.U64} {e r : expr.Expr} (he : ExprWF e)
    (h : expr_ops.lower_bvars amount c e = ok r) :
    absExpr r = ConLeche.Expr.lowerBVars amount.val c.val (absExpr e) ∧ ExprWF r := by
  rw [expr_ops.lower_bvars] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    lower_bvars_go_refines he memo memo' c r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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
    · simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, node_kind, kernel.expr.ExprView.ofKind] at h
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


/-- **`expr_ops::instantiate1_lift` refines `Expr.instantiate1Lift`**: the
fresh memo satisfies `Inst1LMemoInv` vacuously. -/
theorem instantiate1_lift_refines {e v r : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hv : ExprWF v) (h : expr_ops.instantiate1_lift e v d = ok r) :
    absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val ∧
      ExprWF r := by
  rw [expr_ops.instantiate1_lift] at h
  obtain ⟨memo, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, memo'⟩ := p
  have hr : r0 = r := Result.ok_injective h
  subst hr
  obtain ⟨⟨hwf, habs⟩, -⟩ :=
    instantiate1_lift_go_refines hv he memo memo' d r0 (new_memo_inv hnew) hgo
  exact ⟨habs, hwf⟩

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
    simp only [Result.ok.injEq] at h
    rw [h]

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
    dsimp only at h
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
      simp only [expr_view_eq, bind_tc_ok] at h
      cases he with
      | @bvar i1 e h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @fvar idx ty e hty h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @sort u e hu h1 =>
        obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @app f a e hf ha h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @lam ty bo m e hty hbo hm0 h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @lit l e hl h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨x, hx⟩ : ∃ x, args.val[i.val]? = some x :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hx]
        simp [ConLeche.Expr.instPisAtLift]
      | @proj s i1 x e hs hx h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind, Result.ok.injEq] at h
        subst h
        refine ⟨?_, by intro r hr; simp at hr⟩
        obtain ⟨y, hy⟩ : ∃ y, args.val[i.val]? = some y :=
          ⟨args.val[i.val], List.getElem?_eq_getElem hlt⟩
        rw [absExprs_drop_cons hy]
        simp [ConLeche.Expr.instPisAtLift]
      | @forall_e ty bo m e hty hbo hm0 h1 =>
        obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [node_kind, kernel.expr.ExprView.ofKind] at h
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
