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
-/
import ConRon.Refine.ExprOps

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

/-- A `usize` cast to a `u64` keeps its value. -/
theorem usize_cast_u64_val (x : Std.Usize) :
    (Std.UScalar.cast .U64 x : Std.U64).val = x.val := by
  rw [Std.UScalar.cast_val_eq, Std.UScalarTy.U64_numBits_eq]
  refine Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by omega) platform_numBits_le))
  have hb := x.hBounds
  rwa [Std.UScalarTy.Usize_numBits_eq] at hb

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

/-- `expr_ops::exprs_copy_upto` appends the entries `[i, k)` of `xs`. -/
theorem exprs_copy_upto_val (N : Nat) :
    ∀ (xs out r : alloc.vec.Vec expr.Expr) (k i : Std.Usize), k.val - i.val = N →
      expr_ops.exprs_copy_upto xs k i out = ok r →
      r.val = out.val ++ (xs.val.drop i.val).take (k.val - i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs out r k i hN h
    rw [expr_ops.exprs_copy_upto.eq_def] at h
    split at h
    · rename_i hge
      have hk : k.val - i.val = 0 := by scalar_tac
      rw [← Result.ok_injective h, hk]
      simp
    · dsimp only at h
      split at h
      · rename_i hlen
        have hle : xs.val.length ≤ i.val := by scalar_tac
        rw [← Result.ok_injective h, List.drop_eq_nil_of_le hle]
        simp
      · rename_i hge hlen
        simp only [bind_eq_ok_iff] at h
        obtain ⟨e, hidx, e1, hdup, out1, hpush, i2, hi2, hrec⟩ := h
        obtain ⟨hlt, rfl⟩ := vec_index_val hidx
        have he1 : e1 = xs.val[i.val] := Expr.dup_eq hdup
        have hout1 : out1.val = out.val ++ [xs.val[i.val]] := by
          rw [vec_push_val hpush, he1]
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hik : i.val < k.val := by scalar_tac
        have hrec' := ih (k.val - i2.val) (by omega) xs out1 r k i2 rfl hrec
        rw [hrec', hout1, hi2v, show k.val - i.val = (k.val - (i.val + 1)) + 1 by omega,
          drop_take_succ hlt]
        simp

/-- `expr_ops::take_exprs` is `List.take` on the model. -/
theorem take_exprs_val {xs r : alloc.vec.Vec expr.Expr} {k : Std.Usize}
    (h : expr_ops.take_exprs xs k = ok r) : r.val = xs.val.take k.val := by
  rw [expr_ops.take_exprs] at h
  have := exprs_copy_upto_val (k.val - (0#usize : Std.Usize).val) xs
    (alloc.vec.Vec.new expr.Expr) r k 0#usize rfl h
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
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
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
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.fvar hty h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @sort u e hu h1 =>
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.sort hu h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @mk_const n us e hn hus h1 =>
      obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.mk_const hn hus h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @lit l e hl h1 =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, node_kind] at h
      rw [Expr.dup_eq h]
      refine ⟨?_, ExprWF.lit hl h1⟩
      simp only [absExpr_mk, absExprKind]
      rw [ConLeche.Expr.instantiateList]
    | @app f a e hf ha h1 ihf iha =>
      obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
      intro d r h
      rw [expr_ops.instantiate_list.eq_def] at h
      simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
      simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
      simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
      simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
      simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
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
    simp only [rc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff, Result.ok.injEq,
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

end ConRon.Refine.ExprOps
