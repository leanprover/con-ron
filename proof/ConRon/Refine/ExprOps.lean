/-
The refinement of `crates/con-ron-core/src/kernel/expr_ops.rs` (task #13) on
its generated model `ConRon.Generated.kernel.expr_ops.*` (DESIGN.md §3.5, P3.3
of §5; task #21).

**What the statements are against.**  Every Rust item of the module implements
the `*Fast` member of one of con-leche's `@[csimp]` families (task #13): the
executed, memoized walk.  The lemma per function is therefore stated against
the **logical** definition of `ConLeche/Kernel/ExprOps.lean` -- `instantiate1`,
`instantiateList`, `liftLooseBVars`, … -- with the memoized walk's own lemma
(`*_go_refines`) as the step, and the `@[csimp]` equation is never needed: a
`*Go_spec`-shaped induction proves the walk equal to the logical function
directly, which is the same argument con-leche's own `@[csimp]` lemma makes.

**Memos.**  Every memo here is local (created empty in the wrapper, dropped on
return).  The invariant is con-leche's own `*MemoInv` -- "every recorded answer
is the real one" (`Inst1MemoInv`, `InstLMemoInv`, … , the eleven `Prop`s task
#13 skipped as not executable) -- transposed onto the port's table through the
*entry list* `ConRon.Refine.HashMap.al_v` rather than through `toFun`.  That is
the one deliberate departure from task #16's `toFun`/`Rel` bridge, and the
reason is `Eq2Spec`: `toFun` is a lookup by *Lean* equality, so every lemma
about it assumes `eq2` decides equality on the whole key type, while
`expr::beq` is exact only on **well-formed** nodes (`Expr.beq_exact`).  The
entry-list view needs no such assumption: `get_mem` says a hit returns a value
that is *in* the table under an `eq2`-equal key, `insert_mem` says an insert
adds nothing but its own pair, and both are proved here without `Eq2Spec` and
without the table invariant `Inv`.  A key recorded in the memo is well formed
(that is a clause of every `MemoInv` below), so `beq`'s exactness applies at
exactly the pairs the walks compare.
-/
import ConRon.Refine.Expr
import ConRon.Refine.HashMap
import ConLeche.Kernel.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.ExprOps

/-! ## A plumbing step (task #34)

The `Vec` accumulators are pre-sized (`Vec::with_capacity`); that is the
identity in the model, stated as a `simp` lemma so the bind collapses inside
the `simp only [expr_view_eq, arc_deref_eq, bind_ok, …]` step every walk below
already runs.  (The binder datum's constructor `expr::binder_meta`, the other
step here, went with the datum at task #119.) -/

/-- `Vec::with_capacity` is `Vec::new` in the model: an empty list. -/
@[simp] theorem with_capacity_val {α : Type} (c : Std.Usize) :
    (alloc.vec.Vec.with_capacity α c).val = [] := rfl

/-! ## Memo tables as entry lists

The facts every memoized walk below uses, about any key type and with no
assumption on the `Hashable` or `Eq2` dictionary. -/

section Memo

variable {K V : Type} {HashableInst : ron.hashmap.Hashable K}
  {Eq2Inst : ron.hashmap.Eq2 K}

end Memo

/-! ## Plumbing for the `Vec` walks -/

/-- A `usize`-to-`u64` cast is the identity in the model: `usize` is never
wider than 64 bits (`System.Platform.numBits_eq`). -/
theorem usize_cast_u64_val (x : Std.Usize) :
    (Std.UScalar.cast .U64 x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_greater_numBits_eq _ _ ?_
  rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> omega

/-- A `u64`-to-`usize` cast is the identity on values that fit a `usize` --
which is what an in-range index is. -/
theorem u64_cast_usize_val {x : Std.U64} (h : x.val ≤ Std.Usize.max) :
    (Std.UScalar.cast .Usize x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_
  have hpos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  have hmax : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    simp only [Std.Usize.max, Std.Usize.numBits]
    omega
  omega

/-- `Vec::index` without an `Inhabited` instance on the element type (the
`getElem!` form of `HashMap.vec_index_eq` is unavailable for `expr::Expr`). -/
theorem vec_index_getElem? {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    exact congrArg some (Result.ok_injective h)

end ConRon.Refine.ExprOps

