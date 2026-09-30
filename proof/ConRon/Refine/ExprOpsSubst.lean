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

/-! ## `instantiate_list`, the pure walk (`ExprOps.lean:191-235`) -/

/-! ## `instantiate_list_go`, the memoized walk (`ExprOps.lean:268-304`)

con-leche's `InstLMemoInv` (`:248`), through `MemoInv`; the proof is
`instantiate1_go_refines`'s, with the `.bvar` arm deferring to the pure walk
exactly as the cited code does. -/

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

/-! ## `instPisAtLift` (`ExprOps.lean:2365-2378`)

The one telescope walk that uses the *general* substitution, so it belongs with
`instantiate1Lift` rather than with the rest of the spine family.  Its
recursion is on the argument *index* (task #13's deviation 3: Lean's list
recursion becomes an index recursion over a `Vec`), and the expression changes
at every step, so the induction is a strong induction on the number of
arguments left -- not on an `ExprWF` derivation, which only supplies the node's
shape here (through `cases`). -/

end ConRon.Refine.ExprOps
