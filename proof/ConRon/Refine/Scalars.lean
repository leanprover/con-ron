import ConRon.Refine.ExprOpsSubst

/-!
# `Refine/Scalars.lean` — the `u64 → usize` index cast, in one place (task #59)

DESIGN.md §3.3's split makes every *count* and every *index* a `u64`, while
Aeneas models a `Vec` read at a `usize`.  The port therefore writes
`v[i as usize]` on a `u64` counter, and Aeneas models `i as usize` as
`UScalar.cast .Usize i`, whose value is `i.val % 2 ^ Usize.numBits` — the
width is `System.Platform.numBits`, which Aeneas keeps abstract
(`Usize.bounds_eq : Usize.max = U32.max ∨ Usize.max = U64.max`).

So the port's reading `v[i as usize]` and con-leche's `v[i]?` agree **exactly
when `i.val ≤ Usize.max`**, and on a 32-bit target with `i.val ≥ 2 ^ 32` they
genuinely disagree: the port's guard `(i as usize) >= v.len()` compares the
*cast*, so it admits a wrapped index the Lean reading answers `none` at.  That
is why the side condition is a *hypothesis* of the indexing lemmas and not a
platform axiom: no lemma below asserts the target's width, and nothing in the
tier is weakened — the bound is **discharged at every call site**, from the
`Vec` the counter came from (`Vec.property : v.val.length ≤ Usize.max`).

This file is what the inductive tier (task #57's `Ind*.lean`) points at
instead of restating the same fact four more times: task #57 found the shape at
`struct_install::check_struct_doms_at`, `sum_install::opened_resid_ok`, five
`struct_parts` indexers and two `native_parts` readers, and it recurs wherever
a `u64` counter indexes a `Vec`.  The two cast-value lemmas themselves are
`Refine/ExprOps.lean`'s and `Refine/ExprOpsSubst.lean`'s (tasks #21/#47); they
are re-exported here so that there is one name to reach for.
-/
open Aeneas Aeneas.Std

namespace ConRon.Refine.Scalars

/-! ## The two cast-value lemmas (re-exported) -/

export ConRon.Refine.ExprOps (usize_cast_u64_val u64_cast_usize_val
  platform_numBits_le u64_cast_usize_val_of_lt)

/-! ## Discharging the side condition

Every `u64` counter the port indexes a `Vec` with is bounded by that `Vec`'s
length — either directly (the loop guard) or through the count it was built
from — and a `Vec`'s length fits a `usize` by construction. -/

/-- A `Vec`'s length fits a `usize`: Aeneas's `Vec.property`, named. -/
theorem vec_len_le_usize_max {α : Type} (v : alloc.vec.Vec α) :
    v.val.length ≤ Std.Usize.max := v.property

/-- **The discharge**: a `u64` counter bounded by a `Vec`'s length fits a
`usize`.  This is the form the index recursions want — their guard is
`i < len`, or their initial value is a `len`, and the recursion only ever
decreases the counter. -/
theorem u64_le_usize_max_of_le_len {α : Type} {v : alloc.vec.Vec α}
    {i : Std.U64} (h : i.val ≤ v.val.length) : i.val ≤ Std.Usize.max :=
  le_trans h v.property

/-- The same for a strict guard. -/
theorem u64_le_usize_max_of_lt_len {α : Type} {v : alloc.vec.Vec α}
    {i : Std.U64} (h : i.val < v.val.length) : i.val ≤ Std.Usize.max :=
  le_trans (Nat.le_of_lt h) v.property

/-- A `u64` counter that came from widening a `usize` — `v.len() as u64` is
how the port reads a length — fits a `usize` again. -/
theorem u64_le_usize_max_of_cast (x : Std.Usize) :
    (Std.UScalar.cast .U64 x : Std.U64).val ≤ Std.Usize.max := by
  rw [ExprOps.usize_cast_u64_val]; scalar_tac

/-- Monotonicity: whatever bounds the loop's start bounds every later value. -/
theorem u64_le_usize_max_of_le {i j : Std.U64} (hij : i.val ≤ j.val)
    (hj : j.val ≤ Std.Usize.max) : i.val ≤ Std.Usize.max := le_trans hij hj

/-- **The cast is the identity**, packaged at the discharge: a `u64` counter
that a `Vec`'s length bounds reads that `Vec` at its own value. -/
theorem cast_val_of_le_len {α : Type} {v : alloc.vec.Vec α} {i : Std.U64}
    (h : i.val ≤ v.val.length) :
    (Std.UScalar.cast .Usize i : Std.Usize).val = i.val :=
  ExprOps.u64_cast_usize_val (u64_le_usize_max_of_le_len h)

end ConRon.Refine.Scalars
