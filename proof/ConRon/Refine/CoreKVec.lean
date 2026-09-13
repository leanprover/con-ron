/-
`CORE_PLAN.md` step 4 (task #49), the *plumbing* slice of
`crates/con-ron-core/src/kernel/core_k.rs`: the `Vec`/list helpers that stand
for Lean's free list operations, the two constant substitutions, the fuel-lift
and the four closed fuel budgets.  Cited Lean: `ConLeche/Kernel/Core.lean`
(`liftFueled` `:108`, `Expr.substConst0` `:686`, `Expr.substConstAll` `:694`,
`piResidual` `:862`, `majorToCtor` `:1274-1456`, `iotaRec` `:1682-1795`,
`ProjEntry.typeAt` `:1797`, `whnfCoreLoopFuel` `:1984`, `whnfLoopFuel` `:1994`,
`defeqLoopFuel` `:2640`, `checkFuel` `:2901`).

Twenty-two `pub fn`, in three shapes.

* **The index recursions** (`drop_exprs`, `append_exprs`, `leaf_contains`,
  `fvar_leaves_subset`, `rev_append_exprs`, `rules_find`, `pi_residual`) are
  all in the task-#5 shape — a `∀`-quantified statement over `len - i = N` and
  strong induction on `N`, `ExprOps.exprs_copy_upto_val` being the model.  The
  seven `*_from` twins carry the accumulator (`out ++ …`, task #13's deviation
  3: a `Vec` has no shared tail), and the wrapper is two lines.
* **The two substitutions** are plain `ExprWF` inductions: `subst_const0`
  recurses only through `app`, `subst_const_all` through every rebuilding kind,
  exactly as the cited `Expr.substConst0`/`Expr.substConstAll` do.
* **The five one-liners** (`lift_fueled` and the four budgets) are `rfl` modulo
  unfolding the cited `@[irreducible] def`s.

Three things cost thought.

1. `leaf_contains`'s `BEq (Nat × Expr)` is `Nat` equality *and* `Expr.beq`, so
   exactness of the `List.contains` needs `ExprWF` on both the probe and every
   stored leaf — hence the `ExprOps.LeavesWF` hypothesis, and `vec_index_leaf`
   below is `ExprOps.vec_index_expr`'s twin for `Vec<(u64, Expr)>`.
2. `rules_find` returns the *position*, so its lemma states both halves of the
   cited `rules.find? (fun r' => r'.ctor == cj)`: the index is `List.findIdx?`
   and reading the list at it is `List.find?`.  The `findIdx?` step needs the
   returned index to be at or past the cursor, which is therefore a third
   conjunct of the induction.
3. `rev_append_exprs` counts *down* (`targs[k-1]`, `targs[k-2]`, …), so its
   invariant is `out ++ (targs.take k).reverse` under `k ≤ targs.length`; the
   call site's `k = targs.len()` is the wrapper, `out ++ targs.reverse`.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

-- `absRecRule` lives in `BasisTables.lean`'s `T22` section, which `CoreKBase`
-- opens only locally (it goes away with task #46's merge).

/-! ## `drop_exprs` — `List.drop` on a `Vec` (`core_k.rs:137`, `:143`) -/

/-- The index recursion behind `drop_exprs`: the entries from `k` on, appended
to the accumulator.  Raw `Vec` values (`expr::dup` is the identity in the
model, DESIGN.md §3.2). -/
theorem drop_exprs_from_val (N : Nat) :
    ∀ (xs : alloc.vec.Vec expr.Expr) (k : Std.Usize)
      (out r : alloc.vec.Vec expr.Expr),
      xs.val.length - k.val = N →
      core_k.drop_exprs_from xs k out = ok r →
      r.val = out.val ++ xs.val.drop k.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs k out r hN h
    rw [core_k.drop_exprs_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : xs.val.length ≤ k.val := by
        have := alloc.vec.Vec.len_val xs; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      simp
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, out1, hpush, i1, hi1, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : k.val < xs.val.length := by
        have := alloc.vec.Vec.len_val xs; scalar_tac
      have hx : xs.val[k.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hcx : c = x := Expr.dup_eq hdup
      subst hcx
      have hi1v : i1.val = k.val + 1 := HashMap.uscalar_add_eq hi1
      rw [ih (xs.val.length - i1.val) (by omega) xs i1 out1 r rfl hrec,
        vec_push_val hpush, hi1v, List.drop_eq_getElem_cons hlt, hx]
      simp

/-- `core_k::drop_exprs_from` is Lean's `out ++ xs.drop k`. -/
theorem drop_exprs_from_refines {xs k out r} (hxs : ExprsWF xs) (hout : ExprsWF out)
    (h : core_k.drop_exprs_from xs k out = ok r) :
    absExprs r = absExprs out ++ (absExprs xs).drop k.val ∧ ExprsWF r := by
  have hv := drop_exprs_from_val _ xs k out r rfl h
  refine ⟨by unfold absExprs; rw [hv]; simp, ?_⟩
  intro e he
  rw [hv] at he
  rcases List.mem_append.1 he with h1 | h1
  · exact hout e h1
  · exact hxs e (List.mem_of_mem_drop h1)

/-- **`core_k::drop_exprs` is `List.drop`** — the port's spelling of Lean's
shared list tail `xs.drop k` (no cited Lean of its own). -/
theorem drop_exprs_refines {xs k r} (hxs : ExprsWF xs)
    (h : core_k.drop_exprs xs k = ok r) :
    absExprs r = (absExprs xs).drop k.val ∧ ExprsWF r := by
  rw [core_k.drop_exprs] at h
  obtain ⟨habs, hwf⟩ := drop_exprs_from_refines hxs ExprOps.exprsWF_new h
  exact ⟨by rw [habs]; simp, hwf⟩

/-! ## `drop_exprs_n` / `take_exprs_n` — `List.drop`/`List.take` at a **`u64`**
count (`core_k.rs:161`, `:166`, `:178`, `:184`)

Task #61.  The counts the ι cone carries (a recursor's parameter count `rP`, a
constructor's `ctorParams`, a major-premise index `mI`) are `u64`s, and `Vec`
indexing is `usize`; the port used to spell the call `take_exprs(xs, n as
usize)`, which Aeneas models as a **truncating** cast (`UScalar.cast .Usize`),
so nothing below 64-bit `usize` was provable and nothing in the cone bounds
`rP`.  DESIGN.md §3.4 rules the cast out, so the count is consumed by the
recursion instead: `i : Usize` walks the `Vec` and `n : U64` counts down, and
no value crosses between the two widths. -/

/-- The index recursion behind `take_exprs_n`: `n` entries of `xs` from `i`,
appended to the accumulator. -/
theorem take_exprs_n_from_val (N : Nat) :
    ∀ (xs : alloc.vec.Vec expr.Expr) (n : Std.U64) (i : Std.Usize)
      (out r : alloc.vec.Vec expr.Expr),
      n.val = N →
      core_k.take_exprs_n_from xs n i out = ok r →
      r.val = out.val ++ (xs.val.drop i.val).take n.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs n i out r hN h
    rw [core_k.take_exprs_n_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hz
      rw [← Result.ok_injective h, show n.val = 0 by rw [hz]; rfl]
      simp
    · rename_i hz
      split at h
      · rename_i hge
        have hlen : xs.val.length ≤ i.val := by
          have := alloc.vec.Vec.len_val xs; scalar_tac
        rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
        simp
      · rename_i hge
        simp only [bind_eq_ok_iff] at h
        obtain ⟨x, hidx, c, hdup, out1, hpush, n1, hn1, i1, hi1, hrec⟩ := h
        have hg := ExprOps.vec_index_getElem? hidx
        have hlt : i.val < xs.val.length := by
          have := alloc.vec.Vec.len_val xs; scalar_tac
        have hx : xs.val[i.val] = x := by
          rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
        have hcx : c = x := Expr.dup_eq hdup
        subst hcx
        have hnz : n.val ≠ 0 := by
          intro hc; exact hz (by scalar_tac)
        have hn1v : n1.val = n.val - 1 := (ConRon.Refine.Nat.usub_val hn1).2.trans (by simp)
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        rw [ih n1.val (by omega) xs n1 i1 out1 r rfl hrec,
          vec_push_val hpush, hi1v, hn1v, List.drop_eq_getElem_cons hlt, hx,
          show n.val = (n.val - 1) + 1 by omega]
        simp

/-- **`core_k::take_exprs_n` is `List.take`** at a `u64` count. -/
theorem take_exprs_n_val {xs r : alloc.vec.Vec expr.Expr} {n : Std.U64}
    (h : core_k.take_exprs_n xs n = ok r) : r.val = xs.val.take n.val := by
  rw [core_k.take_exprs_n] at h
  have := take_exprs_n_from_val n.val xs n 0#usize (alloc.vec.Vec.new expr.Expr) r rfl h
  simpa [alloc.vec.Vec.new] using this

/-- `take_exprs_n`, as the abstraction and the invariant see it. -/
theorem take_exprs_n_refines {xs r : alloc.vec.Vec expr.Expr} {n : Std.U64}
    (hxs : ExprsWF xs) (h : core_k.take_exprs_n xs n = ok r) :
    absExprs r = (absExprs xs).take n.val ∧ ExprsWF r := by
  refine ⟨by rw [absExprs, absExprs, take_exprs_n_val h, List.map_take], ?_⟩
  intro x hx
  rw [take_exprs_n_val h] at hx
  exact hxs x (List.mem_of_mem_take hx)

/-- The index recursion behind `drop_exprs_n`: skip `n` entries from `i`, then
copy the rest. -/
theorem drop_exprs_n_from_val (N : Nat) :
    ∀ (xs : alloc.vec.Vec expr.Expr) (n : Std.U64) (i : Std.Usize)
      (r : alloc.vec.Vec expr.Expr),
      n.val = N →
      core_k.drop_exprs_n_from xs n i = ok r →
      r.val = xs.val.drop (i.val + n.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs n i r hN h
    rw [core_k.drop_exprs_n_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hz
      have hnz : n.val = 0 := by rw [hz]; rfl
      rw [drop_exprs_from_val _ xs i (alloc.vec.Vec.new expr.Expr) r rfl h, hnz]
      simp [alloc.vec.Vec.new]
    · rename_i hz
      have hnz : n.val ≠ 0 := fun hc => hz (by scalar_tac)
      split at h
      · rename_i hge
        have hlen : xs.val.length ≤ i.val := by
          have := alloc.vec.Vec.len_val xs; scalar_tac
        rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by omega)]
        simp [alloc.vec.Vec.new]
      · rename_i hge
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n1, hn1, i1, hi1, hrec⟩ := h
        have hn1v : n1.val = n.val - 1 := (ConRon.Refine.Nat.usub_val hn1).2.trans (by simp)
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        rw [ih n1.val (by omega) xs n1 i1 r rfl hrec, hi1v, hn1v,
          show i.val + 1 + (n.val - 1) = i.val + n.val by omega]

/-- **`core_k::drop_exprs_n` is `List.drop`** at a `u64` count. -/
theorem drop_exprs_n_val {xs r : alloc.vec.Vec expr.Expr} {n : Std.U64}
    (h : core_k.drop_exprs_n xs n = ok r) : r.val = xs.val.drop n.val := by
  rw [core_k.drop_exprs_n] at h
  have := drop_exprs_n_from_val n.val xs n 0#usize r rfl h
  simpa using this

/-- `drop_exprs_n`, as the abstraction and the invariant see it. -/
theorem drop_exprs_n_refines {xs r : alloc.vec.Vec expr.Expr} {n : Std.U64}
    (hxs : ExprsWF xs) (h : core_k.drop_exprs_n xs n = ok r) :
    absExprs r = (absExprs xs).drop n.val ∧ ExprsWF r := by
  refine ⟨by rw [absExprs, absExprs, drop_exprs_n_val h, List.map_drop], ?_⟩
  intro x hx
  rw [drop_exprs_n_val h] at hx
  exact hxs x (List.mem_of_mem_drop hx)

/-! ## `append_exprs` — `List.append` on a `Vec` (`core_k.rs:155`, `:160`) -/

/-- The index recursion behind `append_exprs`: `ys`' entries from `i` on,
pushed onto `xs`. -/
theorem append_exprs_from_val (N : Nat) :
    ∀ (xs ys r : alloc.vec.Vec expr.Expr) (i : Std.Usize),
      ys.val.length - i.val = N →
      core_k.append_exprs_from xs ys i = ok r →
      r.val = xs.val ++ ys.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs ys r i hN h
    rw [core_k.append_exprs_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : ys.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val ys; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]
      simp
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, xs1, hpush, i2, hi2, hrec⟩ := h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < ys.val.length := by
        have := alloc.vec.Vec.len_val ys; scalar_tac
      have hx : ys.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hcx : c = x := Expr.dup_eq hdup
      subst hcx
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (ys.val.length - i2.val) (by omega) xs1 ys r i2 rfl hrec,
        vec_push_val hpush, hi2v, List.drop_eq_getElem_cons hlt, hx]
      simp

/-- `core_k::append_exprs_from` is `xs ++ ys.drop i`. -/
theorem append_exprs_from_refines {xs ys i r} (hxs : ExprsWF xs) (hys : ExprsWF ys)
    (h : core_k.append_exprs_from xs ys i = ok r) :
    absExprs r = absExprs xs ++ (absExprs ys).drop i.val ∧ ExprsWF r := by
  have hv := append_exprs_from_val _ xs ys r i rfl h
  refine ⟨by unfold absExprs; rw [hv]; simp, ?_⟩
  intro e he
  rw [hv] at he
  rcases List.mem_append.1 he with h1 | h1
  · exact hxs e h1
  · exact hys e (List.mem_of_mem_drop h1)

/-- **`core_k::append_exprs` is `List.append`** — Lean's `xs ++ ys` (no cited
Lean of its own: `++` shares the tail, the port copies `ys`' spine). -/
theorem append_exprs_refines {xs ys r} (hxs : ExprsWF xs) (hys : ExprsWF ys)
    (h : core_k.append_exprs xs ys = ok r) :
    absExprs r = absExprs xs ++ absExprs ys ∧ ExprsWF r := by
  rw [core_k.append_exprs] at h
  obtain ⟨habs, hwf⟩ := append_exprs_from_refines hxs hys h
  exact ⟨by rw [habs]; simp, hwf⟩

/-! ## `leaf_contains` and `fvar_leaves_subset` (`core_k.rs:173`-`:199`)

The scope guard's third conjunct of `Core.lean:1274-1456 majorToCtor`,
`fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)`.  `absLeaves` and
`LeavesWF` are `Refine/ExprOpsMeta.lean`'s (`fvar_leaves`' abstraction), and
the `BEq (Nat × Expr)` the cited `List.contains` uses is `Nat` equality and
`Expr.beq` — exact only on well-formed nodes, whence the `LeavesWF`/`ExprWF`
hypotheses. -/

/-- `ExprOps.vec_index_expr`'s twin for a leaf list: the entry is well formed,
and the abstracted list's `drop` peels it off. -/
theorem vec_index_leaf {ys : alloc.vec.Vec (Std.U64 × expr.Expr)} {j : Std.Usize}
    {p : Std.U64 × expr.Expr} (hys : ExprOps.LeavesWF ys)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Std.U64 × expr.Expr))
      ys j = ok p) :
    j.val < ys.val.length ∧ ExprWF p.2 ∧
      (ExprOps.absLeaves ys).drop j.val
        = (p.1.val, absExpr p.2) :: (ExprOps.absLeaves ys).drop (j.val + 1) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : j.val < ys.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : ys.val[j.val] = p := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, hys p (by rw [← hx]; exact List.getElem_mem hlt), ?_⟩
  rw [ExprOps.absLeaves, List.drop_eq_getElem_cons (by simpa using hlt),
    List.getElem_map, hx]

/-- The index recursion behind `leaf_contains`: is `(i, ty)` one of the leaves
from `j` on? -/
theorem leaf_contains_from_refines (N : Nat) :
    ∀ (ys : alloc.vec.Vec (Std.U64 × expr.Expr)) (i : Std.U64) (ty : expr.Expr)
      (j : Std.Usize) (b : Bool),
      ExprOps.LeavesWF ys → ExprWF ty → ys.val.length - j.val = N →
      core_k.leaf_contains_from ys i ty j = ok b →
      b = ((ExprOps.absLeaves ys).drop j.val).contains (i.val, absExpr ty) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ys i ty j b hys hty hN h
    rw [core_k.leaf_contains_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : ys.val.length ≤ j.val := by
        have := alloc.vec.Vec.len_val ys; scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [ExprOps.absLeaves] using hlen)]
      simp
    · rename_i hge
      obtain ⟨⟨i2, e⟩, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hlt, hewf, hdrop⟩ := vec_index_leaf hys hidx
      dsimp only at hewf hdrop
      -- the destructuring bind leaves a `let (i2, e) := (i2, e)` that `split`
      -- cannot see through; this `replace` is the iota step, by definition.
      replace h : (if i2 = i then
            (do let bb ← expr.beq e ty
                if bb then ok true
                else do let i3 ← j + 1#usize; core_k.leaf_contains_from ys i ty i3)
          else do let i3 ← j + 1#usize; core_k.leaf_contains_from ys i ty i3)
          = ok b := h
      have hstep : ∀ (i3 : Std.Usize), i3.val = j.val + 1 →
          core_k.leaf_contains_from ys i ty i3 = ok b →
          b = ((ExprOps.absLeaves ys).drop (j.val + 1)).contains (i.val, absExpr ty) := by
        intro i3 hi3 hrec
        rw [ih (ys.val.length - i3.val) (by omega) ys i ty i3 b hys hty rfl hrec, hi3]
      split at h
      · rename_i heq
        obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
        have hbb' : bb = decide (absExpr e = absExpr ty) := Expr.beq_refines hewf hty hbb
        cases bb with
        | true =>
          have he : absExpr e = absExpr ty := of_decide_eq_true hbb'.symm
          simp only [if_true, Result.ok.injEq] at h
          rw [← h, hdrop, List.contains_cons, heq, he]
          simp
        | false =>
          have hne : absExpr e ≠ absExpr ty := of_decide_eq_false hbb'.symm
          simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
          obtain ⟨i3, hi3, hrec⟩ := h
          rw [hstep i3 (HashMap.uscalar_add_eq hi3) hrec, hdrop, List.contains_cons]
          simp [Ne.symm hne]
      · rename_i hne
        have hnev : i2.val ≠ i.val := fun hc => hne (Std.UScalar.eq_of_val_eq hc)
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i3, hi3, hrec⟩ := h
        rw [hstep i3 (HashMap.uscalar_add_eq hi3) hrec, hdrop, List.contains_cons]
        simp [Ne.symm hnev]

/-- **`core_k::leaf_contains` is `List.contains`** on `fvarLeaves`
(`Core.lean:1274-1456 majorToCtor`'s `major.fvarLeaves.contains l`). -/
theorem leaf_contains_refines {ys : alloc.vec.Vec (Std.U64 × expr.Expr)} {i : Std.U64}
    {ty : expr.Expr} {b : Bool} (hys : ExprOps.LeavesWF ys) (hty : ExprWF ty)
    (h : core_k.leaf_contains ys i ty = ok b) :
    b = (ExprOps.absLeaves ys).contains (i.val, absExpr ty) := by
  rw [core_k.leaf_contains] at h
  rw [leaf_contains_from_refines _ ys i ty 0#usize b hys hty rfl h,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]

/-- The index recursion behind `fvar_leaves_subset`. -/
theorem fvar_leaves_subset_from_refines (N : Nat) :
    ∀ (xs ys : alloc.vec.Vec (Std.U64 × expr.Expr)) (i : Std.Usize) (b : Bool),
      ExprOps.LeavesWF xs → ExprOps.LeavesWF ys → xs.val.length - i.val = N →
      core_k.fvar_leaves_subset_from xs ys i = ok b →
      b = ((ExprOps.absLeaves xs).drop i.val).all
        (fun l => (ExprOps.absLeaves ys).contains l) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs ys i b hxs hys hN h
    rw [core_k.fvar_leaves_subset_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : xs.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val xs; scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [ExprOps.absLeaves] using hlen)]
      simp
    · rename_i hge
      obtain ⟨⟨i2, e⟩, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hlt, hewf, hdrop⟩ := vec_index_leaf hxs hidx
      dsimp only at hewf hdrop
      replace h : (do let bb ← core_k.leaf_contains ys i2 e
                      if bb then
                        (do let i3 ← i + 1#usize;
                            core_k.fvar_leaves_subset_from xs ys i3)
                      else ok false) = ok b := h
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      have hbb' : bb = (ExprOps.absLeaves ys).contains (i2.val, absExpr e) :=
        leaf_contains_refines hys hewf hbb
      cases bb with
      | true =>
        simp only [if_true, bind_eq_ok_iff] at h
        obtain ⟨i3, hi3, hrec⟩ := h
        have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
        rw [ih (xs.val.length - i3.val) (by omega) xs ys i3 b hxs hys rfl hrec, hi3v,
          hdrop, List.all_cons, ← hbb']
        simp
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, hdrop, List.all_cons, ← hbb']
        simp

/-- **`core_k::fvar_leaves_subset` refines the scope guard's third conjunct**
of `Core.lean:1274-1456 majorToCtor`:
`fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)`.  All three of
`majorToCtor`'s branches run it. -/
theorem fvar_leaves_subset_refines {xs ys : alloc.vec.Vec (Std.U64 × expr.Expr)}
    {b : Bool} (hxs : ExprOps.LeavesWF xs) (hys : ExprOps.LeavesWF ys)
    (h : core_k.fvar_leaves_subset xs ys = ok b) :
    b = (ExprOps.absLeaves xs).all (fun l => (ExprOps.absLeaves ys).contains l) := by
  rw [core_k.fvar_leaves_subset] at h
  rw [fvar_leaves_subset_from_refines _ xs ys 0#usize b hxs hys rfl h,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]

/-! ## `expr_singleton` (`core_k.rs:1907`) -/

/-- **`core_k::expr_singleton` is the one-element list** `[e]` (the `[b]` of
`targs ++ [b]`; `level::singleton` is its `Level` twin, no cited Lean of its
own). -/
theorem expr_singleton_refines {e : expr.Expr} {r : alloc.vec.Vec expr.Expr}
    (he : ExprWF e) (h : core_k.expr_singleton e = ok r) :
    absExprs r = [absExpr e] ∧ ExprsWF r := by
  rw [core_k.expr_singleton] at h
  obtain ⟨c, hdup, hpush⟩ := bind_eq_ok_iff.mp h
  rw [Expr.dup_eq hdup] at hpush
  have hv : r.val = [e] := by rw [vec_push_val hpush]; simp
  refine ⟨by unfold absExprs; rw [hv]; simp, ?_⟩
  intro x hx
  rw [hv, List.mem_singleton] at hx
  rw [hx]; exact he

/-! ## `rev_append_exprs` (`core_k.rs:2351`)

`ConLeche/Kernel/Core.lean:1797-1806 ProjEntry.typeAt`'s `pe :: targs.reverse`,
as the downward index recursion `targs[k-1]`, `targs[k-2]`, …. -/

/-- The downward recursion's invariant: the last `k` entries of `targs`,
reversed, appended to the accumulator. -/
theorem rev_append_exprs_val (N : Nat) :
    ∀ (out targs r : alloc.vec.Vec expr.Expr) (k : Std.Usize),
      k.val = N → k.val ≤ targs.val.length →
      core_k.rev_append_exprs out targs k = ok r →
      r.val = out.val ++ (targs.val.take k.val).reverse := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out targs r k hN hle h
    rw [core_k.rev_append_exprs.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hz
      subst hz
      rw [← Result.ok_injective h, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
      simp
    · rename_i hz
      have hk1 : 1 ≤ k.val := by
        by_contra hc
        refine hz (Std.UScalar.eq_of_val_eq ?_)
        have : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
        omega
      split at h
      · rename_i hgt
        exfalso
        have := alloc.vec.Vec.len_val targs
        scalar_tac
      · rename_i hgt
        simp only [bind_eq_ok_iff] at h
        obtain ⟨k1, hk1', x, hidx, c, hdup, out1, hpush, hrec⟩ := h
        have hk1v : k1.val = k.val - 1 := HashMap.uscalar_sub_eq hk1'
        have hg := ExprOps.vec_index_getElem? hidx
        have hlt : k.val - 1 < targs.val.length := by omega
        have hx : targs.val[k.val - 1] = x := by
          rw [hk1v, List.getElem?_eq_getElem hlt] at hg
          exact Option.some_injective _ hg
        have hcx : c = x := Expr.dup_eq hdup
        subst hcx
        have hg' : targs.val[k.val - 1]? = some c := by rw [← hk1v]; exact hg
        -- the `reverse` of a `take` peels its last entry off; stated on a fresh
        -- `m` so that no dependent `getElem` proof has to be rewritten.
        have hrev : (targs.val.take k.val).reverse
            = c :: (targs.val.take (k.val - 1)).reverse := by
          obtain ⟨m, hm⟩ : ∃ m, k.val = m + 1 := ⟨k.val - 1, by omega⟩
          rw [hm] at hg' ⊢
          simp only [Nat.add_sub_cancel] at hg' ⊢
          rw [List.take_add_one, hg']
          simp
        rw [ih k1.val (by omega) out1 targs r k1 rfl (by omega) hrec,
          vec_push_val hpush, hk1v, hrev]
        simp

/-- **`core_k::rev_append_exprs` is `out ++ targs.reverse`** at the call site's
`k = targs.len()` (`Core.lean:1797-1806 ProjEntry.typeAt`). -/
theorem rev_append_exprs_refines {out targs r : alloc.vec.Vec expr.Expr}
    (hout : ExprsWF out) (htargs : ExprsWF targs)
    (h : core_k.rev_append_exprs out targs (alloc.vec.Vec.len targs) = ok r) :
    absExprs r = absExprs out ++ (absExprs targs).reverse ∧ ExprsWF r := by
  have hlen : (alloc.vec.Vec.len targs).val = targs.val.length :=
    alloc.vec.Vec.len_val targs
  have hv := rev_append_exprs_val _ out targs r _ rfl (by omega) h
  rw [hlen, List.take_of_length_le (le_refl _)] at hv
  refine ⟨by unfold absExprs; rw [hv]; simp, ?_⟩
  intro e he
  rw [hv] at he
  rcases List.mem_append.1 he with h1 | h1
  · exact hout e h1
  · exact htargs e (List.mem_reverse.1 h1)

/-! ## `get_d_expr` (`core_k.rs:2288`)

`Core.lean:1682-1795 iotaRec`'s `args.getD mI (.bvar 0)`; Lean's out-of-range
default is `Inhabited Expr`'s `.bvar 0`, which the port spells
`env::default_expr`. -/

/-- **`core_k::get_d_expr` is `List.getD`** at the default `.bvar 0`. -/
theorem get_d_expr_refines {args : alloc.vec.Vec expr.Expr} {i : Std.U64}
    {r : expr.Expr} (hargs : ExprsWF args) (h : core_k.get_d_expr args i = ok r) :
    absExpr r = (absExprs args).getD i.val (.bvar 0) ∧ ExprWF r := by
  rw [core_k.get_d_expr] at h
  simp only [lift_eq] at h
  obtain ⟨n64, hn64, h⟩ := bind_eq_ok_iff.mp h
  have hbound : args.val.length ≤ Std.Usize.max := by
    have := alloc.vec.Vec.len_val args; scalar_tac
  have hn64v : n64.val = args.val.length := by
    rw [← Result.ok_injective hn64, ExprOps.usize_cast_u64_val,
      alloc.vec.Vec.len_val]
  split at h
  · rename_i hlt
    have hltv : i.val < args.val.length := by
      have h1 : i.val < n64.val := by scalar_tac
      omega
    obtain ⟨iu, hiu, h⟩ := bind_eq_ok_iff.mp h
    have hiv : iu.val = i.val := by
      rw [← Result.ok_injective hiu]
      exact ExprOps.u64_cast_usize_val (by omega)
    obtain ⟨x, hidx, hdup⟩ := bind_eq_ok_iff.mp h
    obtain ⟨-, hxwf, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
    rw [hiv] at hdrop
    refine ⟨?_, by rw [Expr.dup_eq hdup]; exact hxwf⟩
    rw [Expr.dup_eq hdup]
    have hlt' : i.val < (absExprs args).length := by
      simpa [absExprs] using hltv
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']
    have hcons := List.drop_eq_getElem_cons hlt'
    rw [hdrop] at hcons
    simpa using (List.head_eq_of_cons_eq hcons.symm).symm
  · rename_i hge
    have hgev : args.val.length ≤ i.val := by
      have h1 : ¬ (i.val < n64.val) := by scalar_tac
      omega
    obtain ⟨habs, hwf⟩ := default_expr_refines h
    refine ⟨?_, hwf⟩
    rw [habs, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa [absExprs] using hgev)]
    rfl

/-! ## `rules_find` (`core_k.rs:2300`)

`Core.lean:1682-1795 iotaRec`'s `rules.find? (fun r' => r'.ctor == cj)`, as an
index recursion returning the position (§3.4 forbids closures).  Both halves
of the cited `find?` are stated: the index is `List.findIdx?`, and the list
read at it is `List.find?`. -/

/-- The index recursion: at cursor `i`, the position is `findIdx?` of the
dropped list shifted by `i`, and reading the list there is `find?`. -/
theorem rules_find_val (N : Nat) :
    ∀ (rules : alloc.vec.Vec env.RecRule) (cj : name.Name) (i : Std.Usize)
      (o : Option Std.Usize),
      RecRulesWF rules → NameWF cj → rules.val.length - i.val = N →
      core_k.rules_find rules cj i = ok o →
      (∀ j ∈ o, i.val ≤ j.val ∧ j.val < rules.val.length) ∧
        o.map (fun j => j.val - i.val) =
          ((absRecRules rules).drop i.val).findIdx? (fun r' => r'.ctor == absName cj) ∧
        o.bind (fun j => (absRecRules rules)[j.val]?) =
          ((absRecRules rules).drop i.val).find? (fun r' => r'.ctor == absName cj) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rules cj i o hrs hcj hN h
    rw [core_k.rules_find.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : rules.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val rules; scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absRecRules] using hlen)]
      simp
    · rename_i hge
      obtain ⟨rr, hidx, h⟩ := bind_eq_ok_iff.mp h
      have hg := ExprOps.vec_index_getElem? hidx
      have hlt : i.val < rules.val.length := by
        have := alloc.vec.Vec.len_val rules; scalar_tac
      have hx : rules.val[i.val] = rr := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hrrwf : RecRuleWF rr := hrs rr (by rw [← hx]; exact List.getElem_mem hlt)
      have hdrop : (absRecRules rules).drop i.val
          = absRecRule rr :: (absRecRules rules).drop (i.val + 1) := by
        rw [absRecRules, List.drop_eq_getElem_cons (by simpa using hlt),
          List.getElem_map, hx]
      have hget : (absRecRules rules)[i.val]? = some (absRecRule rr) := by
        rw [absRecRules, List.getElem?_map, List.getElem?_eq_getElem hlt, hx]; rfl
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      have hbb' : bb = decide (absName rr.ctor = absName cj) :=
        Name.beq_refines hrrwf.1 hcj hbb
      have hpc : ((absRecRule rr).ctor == absName cj) = bb := by
        rw [hbb']
        show (absName rr.ctor == absName cj) = decide (absName rr.ctor = absName cj)
        by_cases hc : absName rr.ctor = absName cj <;> simp [hc]
      cases bb with
      | true =>
        simp only [if_true, Result.ok.injEq] at h
        rw [← h]
        refine ⟨by simp; omega, ?_, ?_⟩
        · rw [hdrop, List.findIdx?_cons, if_pos hpc]; simp
        · rw [hdrop, List.find?_cons]
          simp only [hpc]
          simpa using hget
      | false =>
        simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, hrec⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hb, hidx', hfind⟩ :=
          ih (rules.val.length - i2.val) (by omega) rules cj i2 o hrs hcj rfl hrec
        rw [hi2v] at hb hidx' hfind
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          obtain ⟨h1, h2⟩ := hb j hj
          exact ⟨by omega, h2⟩
        · rw [hdrop, List.findIdx?_cons, if_neg (by simp [hpc]), ← hidx']
          cases o with
          | none => simp
          | some j =>
            have hj := (hb j rfl).1
            simp only [Option.map_some]
            congr 1
            omega
        · rw [hdrop, List.find?_cons]
          simp only [hpc]
          rw [hfind]

/-- **`core_k::rules_find` refines `rules.find? (fun r' => r'.ctor == cj)`**
(`Core.lean:1682-1795 iotaRec`): the position it returns is the cited
`List.findIdx?`, and the rule at that position is the cited `List.find?`. -/
theorem rules_find_refines {rules : alloc.vec.Vec env.RecRule} {cj : name.Name}
    {o : Option Std.Usize} (hrs : RecRulesWF rules) (hcj : NameWF cj)
    (h : core_k.rules_find rules cj 0#usize = ok o) :
    o.map (fun j => j.val) =
        (absRecRules rules).findIdx? (fun r' => r'.ctor == absName cj) ∧
      o.bind (fun j => (absRecRules rules)[j.val]?) =
        (absRecRules rules).find? (fun r' => r'.ctor == absName cj) := by
  obtain ⟨-, hidx, hfind⟩ := rules_find_val _ rules cj 0#usize o hrs hcj rfl h
  rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero] at hidx hfind
  exact ⟨by simpa using hidx, hfind⟩

/-! ## `pi_residual` (`core_k.rs:1881`, `:1887`)

`Core.lean:862-867 piResidual`: peel a `∀`-telescope along an argument list.
Structurally `Expr.instPis`, so the proof is `ExprOps.inst_pis_from_refines`'s. -/

/-- `core_k::pi_residual_from` refines `piResidual` at the arguments from `i`
on. -/
theorem pi_residual_from_refines (N : Nat) :
    ∀ (e : expr.Expr) (args : alloc.vec.Vec expr.Expr) (i : Std.Usize)
      (r : Option expr.Expr),
      args.val.length - i.val = N → ExprWF e → ExprsWF args →
      core_k.pi_residual_from e args i = ok r →
      (Option.map absExpr r =
        ConLeche.piResidual (absExpr e) ((absExprs args).drop i.val)) ∧
      (∀ t, r = some t → ExprWF t) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro e args i r hN he hargs h
    rw [core_k.pi_residual_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr,
        List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      exact ⟨by simp [ConLeche.piResidual], fun t ht => by
        simp only [Option.some.injEq] at ht; rw [← ht]; exact he⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      obtain ⟨a0, rest0, hd⟩ :
          ∃ a0 rest0, (absExprs args).drop i.val = a0 :: rest0 := by
        rcases hh : (absExprs args).drop i.val with _ | ⟨a0, rest0⟩
        · exfalso
          have hz : ((absExprs args).drop i.val).length = 0 := by rw [hh]; rfl
          rw [List.length_drop, absExprs, List.length_map] at hz
          omega
        · exact ⟨a0, rest0, rfl⟩
      cases he with
      | @bvar i2 e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
        obtain ⟨x, hidx, b, hinst, i2, hi2, hrec⟩ := h
        obtain ⟨hlt', hxwf, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
        obtain ⟨hiabs, hiwf⟩ := ExprOps.instantiate1_refines hbo hxwf hinst
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) b args i2 r rfl
          hiwf hargs hrec
        refine ⟨?_, hwf⟩
        rw [habs, hi2v, hdrop, hiabs,
          show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
        simp [ConLeche.piResidual]
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩
      | @proj s i2 x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.piResidual], by simp⟩

/-- **`core_k::pi_residual` refines `piResidual`** (`Core.lean:862-867`). -/
theorem pi_residual_refines {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {r : Option expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : core_k.pi_residual e args = ok r) :
    Option.map absExpr r = ConLeche.piResidual (absExpr e) (absExprs args) ∧
      (∀ t, r = some t → ExprWF t) := by
  rw [core_k.pi_residual] at h
  obtain ⟨habs, hwf⟩ := pi_residual_from_refines _ e args 0#usize r rfl he hargs h
  exact ⟨by rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero],
    hwf⟩

/-! ## The two constant substitutions (`core_k.rs:1705`, `:1723`)

`Core.lean:686-692 Expr.substConst0` and `:694-710 Expr.substConstAll`.  The
cited guard is `c = n ∧ us = []`; the port tests `us.len() == 0 &&
name::beq(c, n)`, which is the same condition (`absLevels us = []` iff the
`Vec` is empty). -/

/-- **`core_k::subst_const0` refines `Expr.substConst0`**
(`Core.lean:686-692`): only `app` recurses, the equation sides being
binder-free. -/
theorem subst_const0_refines {n : name.Name} {v : expr.Expr} (hn : NameWF n)
    (hv : ExprWF v) {e : expr.Expr} (he : ExprWF e) :
    ∀ r : expr.Expr, core_k.subst_const0 n v e = ok r →
      absExpr r = ConLeche.Expr.substConst0 (absName n) (absExpr v) (absExpr e) ∧
        ExprWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 ihty =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.sort hu h1⟩
  | @mk_const cn cus e hcn hcus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    have hwfe : ExprWF (expr.Expr.mk (expr.ExprNode.mk d (.Const cn cus))) :=
      ExprWF.mk_const hcn hcus h1
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d (.Const cn cus)))
        = .const (absName cn) (absLevels cus) := by simp
    split at h
    · rename_i hz
      have hzl : absLevels cus = [] := by
        have := alloc.vec.Vec.len_val cus
        have : cus.val.length = 0 := by scalar_tac
        simp [absLevels, List.eq_nil_of_length_eq_zero this]
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      have hbb' : bb = decide (absName cn = absName n) :=
        Name.beq_refines hcn hn hbb
      cases bb with
      | true =>
        have hcn' : absName cn = absName n := of_decide_eq_true hbb'.symm
        simp only [if_true] at h
        rw [Expr.dup_eq h]
        refine ⟨?_, hv⟩
        rw [habse, ConLeche.Expr.substConst0, if_pos ⟨hcn', hzl⟩]
      | false =>
        have hcn' : ¬ (absName cn = absName n) := of_decide_eq_false hbb'.symm
        simp only [Bool.false_eq_true, if_false] at h
        rw [Expr.dup_eq h]
        refine ⟨?_, hwfe⟩
        rw [habse, ConLeche.Expr.substConst0, if_neg (fun hc => hcn' hc.1)]
    · rename_i hz
      have hzl : absLevels cus ≠ [] := by
        have hl := alloc.vec.Vec.len_val cus
        have : cus.val.length ≠ 0 := by scalar_tac
        simp only [absLevels, ne_eq, List.map_eq_nil_iff]
        intro hc; exact this (by rw [hc]; rfl)
      rw [Expr.dup_eq h]
      refine ⟨?_, hwfe⟩
      rw [habse, ConLeche.Expr.substConst0, if_neg (fun hc => hzl hc.2)]
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨e1, he1, e2, he2, happ⟩ := h
    obtain ⟨h1abs, h1wf⟩ := ihf e1 he1
    obtain ⟨h2abs, h2wf⟩ := iha e2 he2
    refine ⟨?_, Expr.app_wf h1wf h2wf happ⟩
    rw [Expr.app_refines happ, h1abs, h2abs]
    simp [ConLeche.Expr.substConst0]
  | @lam ty bo m e hty hbo hm h1 ih1 ih2 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 ih1 ih2 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.forall_e hty hbo hm h1⟩
  | @let_e ty w bo e hty hw hbo h1 ih1 ih2 ih3 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.let_e hty hw hbo h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.lit hl h1⟩
  | @proj s idx x e hs hx h1 ihx =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [core_k.subst_const0.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConst0], ExprWF.proj hs hx h1⟩

/-- **`core_k::subst_const_all` refines `Expr.substConstAll`**
(`Core.lean:694-710`): every rebuilding kind recurses, `fvar` annotations are
not entered. -/
theorem subst_const_all_refines {n : name.Name} {v : expr.Expr} (hn : NameWF n)
    (hv : ExprWF v) {e : expr.Expr} (he : ExprWF e) :
    ∀ r : expr.Expr, core_k.subst_const_all n v e = ok r →
      absExpr r = ConLeche.Expr.substConstAll (absName n) (absExpr v) (absExpr e) ∧
        ExprWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConstAll], ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 ihty =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConstAll], ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConstAll], ExprWF.sort hu h1⟩
  | @mk_const cn cus e hcn hcus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    have hwfe : ExprWF (expr.Expr.mk (expr.ExprNode.mk d (.Const cn cus))) :=
      ExprWF.mk_const hcn hcus h1
    have habse : absExpr (expr.Expr.mk (expr.ExprNode.mk d (.Const cn cus)))
        = .const (absName cn) (absLevels cus) := by simp
    split at h
    · rename_i hz
      have hzl : absLevels cus = [] := by
        have := alloc.vec.Vec.len_val cus
        have : cus.val.length = 0 := by scalar_tac
        simp [absLevels, List.eq_nil_of_length_eq_zero this]
      obtain ⟨bb, hbb, h⟩ := bind_eq_ok_iff.mp h
      have hbb' : bb = decide (absName cn = absName n) :=
        Name.beq_refines hcn hn hbb
      cases bb with
      | true =>
        have hcn' : absName cn = absName n := of_decide_eq_true hbb'.symm
        simp only [if_true] at h
        rw [Expr.dup_eq h]
        refine ⟨?_, hv⟩
        rw [habse, ConLeche.Expr.substConstAll, if_pos ⟨hcn', hzl⟩]
      | false =>
        have hcn' : ¬ (absName cn = absName n) := of_decide_eq_false hbb'.symm
        simp only [Bool.false_eq_true, if_false] at h
        rw [Expr.dup_eq h]
        refine ⟨?_, hwfe⟩
        rw [habse, ConLeche.Expr.substConstAll, if_neg (fun hc => hcn' hc.1)]
    · rename_i hz
      have hzl : absLevels cus ≠ [] := by
        have hl := alloc.vec.Vec.len_val cus
        have : cus.val.length ≠ 0 := by scalar_tac
        simp only [absLevels, ne_eq, List.map_eq_nil_iff]
        intro hc; exact this (by rw [hc]; rfl)
      rw [Expr.dup_eq h]
      refine ⟨?_, hwfe⟩
      rw [habse, ConLeche.Expr.substConstAll, if_neg (fun hc => hzl hc.2)]
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨e1, he1, e2, he2, happ⟩ := h
    obtain ⟨h1abs, h1wf⟩ := ihf e1 he1
    obtain ⟨h2abs, h2wf⟩ := iha e2 he2
    refine ⟨?_, Expr.app_wf h1wf h2wf happ⟩
    rw [Expr.app_refines happ, h1abs, h2abs]
    simp [ConLeche.Expr.substConstAll]
  | @lam ty bo m e hty hbo hm h1 ih1 ih2 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨e1, he1, e2, he2, bm, hbm, hlam⟩ := h
    obtain ⟨h1abs, h1wf⟩ := ih1 e1 he1
    obtain ⟨h2abs, h2wf⟩ := ih2 e2 he2
    have hbm' : bm = m := Expr.binder_meta_dup_eq hbm
    subst hbm'
    refine ⟨?_, Expr.lam_wf h1wf h2wf hm hlam⟩
    rw [Expr.lam_refines hlam, h1abs, h2abs]
    simp [ConLeche.Expr.substConstAll]
  | @forall_e ty bo m e hty hbo hm h1 ih1 ih2 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨e1, he1, e2, he2, bm, hbm, hfa⟩ := h
    obtain ⟨h1abs, h1wf⟩ := ih1 e1 he1
    obtain ⟨h2abs, h2wf⟩ := ih2 e2 he2
    have hbm' : bm = m := Expr.binder_meta_dup_eq hbm
    subst hbm'
    refine ⟨?_, Expr.forall_e_wf h1wf h2wf hm hfa⟩
    rw [Expr.forall_e_refines hfa, h1abs, h2abs]
    simp [ConLeche.Expr.substConstAll]
  | @let_e ty w bo e hty hw hbo h1 ih1 ih2 ih3 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨e1, he1, e2, he2, e3, he3, hlet⟩ := h
    obtain ⟨h1abs, h1wf⟩ := ih1 e1 he1
    obtain ⟨h2abs, h2wf⟩ := ih2 e2 he2
    obtain ⟨h3abs, h3wf⟩ := ih3 e3 he3
    refine ⟨?_, Expr.let_e_wf h1wf h2wf h3wf hlet⟩
    rw [Expr.let_e_refines hlet, h1abs, h2abs, h3abs]
    simp [ConLeche.Expr.substConstAll]
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.substConstAll], ExprWF.lit hl h1⟩
  | @proj s idx x e hs hx h1 ihx =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro r h
    rw [core_k.subst_const_all.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, name_dup_eq,
      bind_eq_ok_iff] at h
    obtain ⟨e1, he1, hproj⟩ := h
    obtain ⟨h1abs, h1wf⟩ := ihx e1 he1
    refine ⟨?_, Expr.proj_wf hs h1wf hproj⟩
    rw [Expr.proj_refines hproj, h1abs]
    simp [ConLeche.Expr.substConstAll]

/-! ## `lift_fueled` (`core_k.rs:328`)

`Core.lean:108-111 liftFueled`, monomorphic at `Option Bool` with `what` baked
in (§3.4).  Stated over the full outcome (task #67): `lift_fueled_refines` is
the `Ok` half and `lift_fueled_err` the mirrored `Err` half, which compares the
error *kind* only (DESIGN.md §3.1: messages need not match). -/

/-- **`core_k::lift_fueled` refines `liftFueled "level comparison"`**
(`Core.lean:108-111`) on the success constructor. -/
theorem lift_fueled_refines {o : Option Bool} {b : Bool}
    (h : core_k.lift_fueled o = ok (.Ok b)) :
    ConLeche.liftFueled (m := ConLeche.CheckM) "level comparison" o = .ok b := by
  cases o with
  | none =>
    simp only [core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, -, v, -, ce, -, hr⟩ := h
    simp at hr
  | some a =>
    simp only [core_k.lift_fueled, Result.ok.injEq] at h
    injection h with hab
    rw [← hab]
    rfl

/-- **`core_k::lift_fueled`'s failure half** (`core_k.rs:376`, mirroring
`Core.lean:111`'s `throw (.internal s!"fuel exhausted: {what}")`): the `none`
arm is `internal` on both sides, and the `some` arm cannot fail.  The message
is never compared (DESIGN.md §3.1, task #67). -/
theorem lift_fueled_err {o : Option Bool} {ce : core_types.CheckError}
    (h : core_k.lift_fueled o = ok (.Err ce)) :
    ErrSim ce (ConLeche.liftFueled (m := ConLeche.CheckM) "level comparison" o) := by
  cases o with
  | none =>
    simp only [core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, -, v, -, ce1, hce1, hr⟩ := h
    have h1 : core_types.CheckError.Internal v = ce := by
      have h2 : ce1 = ce := by simpa using Result.ok_injective hr
      rw [← h2]
      exact Result.ok_injective (by rw [core_types.internal] at hce1; exact hce1)
    rw [← h1]
    exact ErrSim.internal rfl
  | some a =>
    simp only [core_k.lift_fueled] at h
    exact absurd h (by simp)

/-! ## The four closed fuel budgets

`whnfCoreLoopFuel` (`Core.lean:1984-1992`), `whnfLoopFuel` (`:1994-2001`),
`defeqLoopFuel` (`:2640-2644`) and `checkFuel` (`:2901-2904`) — the first three
`@[irreducible]`, so each lemma unfolds the cited constant by name. -/

/-- **`core_k::whnf_core_loop_fuel` is `whnfCoreLoopFuel`**
(`Core.lean:1984-1992`). -/
theorem whnf_core_loop_fuel_refines {r : Std.U64}
    (h : core_k.whnf_core_loop_fuel = ok r) : r.val = ConLeche.whnfCoreLoopFuel := by
  rw [core_k.whnf_core_loop_fuel] at h
  rw [← Result.ok_injective h]
  simp [ConLeche.whnfCoreLoopFuel]

/-- **`core_k::whnf_loop_fuel` is `whnfLoopFuel`** (`Core.lean:1994-2001`). -/
theorem whnf_loop_fuel_refines {r : Std.U64}
    (h : core_k.whnf_loop_fuel = ok r) : r.val = ConLeche.whnfLoopFuel := by
  rw [core_k.whnf_loop_fuel] at h
  rw [← Result.ok_injective h]
  simp [ConLeche.whnfLoopFuel]

/-- **`core_k::defeq_loop_fuel` is `defeqLoopFuel`** (`Core.lean:2640-2644`). -/
theorem defeq_loop_fuel_refines {r : Std.U64}
    (h : core_k.defeq_loop_fuel = ok r) : r.val = ConLeche.defeqLoopFuel := by
  rw [core_k.defeq_loop_fuel] at h
  rw [← Result.ok_injective h]
  simp [ConLeche.defeqLoopFuel]

/-- **`core_k::check_fuel` is `checkFuel`** (`Core.lean:2901-2904`). -/
theorem check_fuel_refines {r : Std.U64}
    (h : core_k.check_fuel = ok r) : r.val = ConLeche.checkFuel := by
  rw [core_k.check_fuel] at h
  rw [← Result.ok_injective h]
  simp [ConLeche.checkFuel]

end ConRon.Refine.CoreK

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`subst_const_all_refines` is the file's deepest chain -- the ten-constructor
`ExprWF` induction, `name::beq`'s exactness and five smart constructors -- so it
is the one worth pinning. -/

/--
info: 'ConRon.Refine.CoreK.subst_const_all_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConRon.Refine.CoreK.subst_const_all_refines
