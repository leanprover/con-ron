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
and the children's well-formedness in one step (the `partial_fixpoint`'s own
`fixpoint_induct` wants an admissible motive and supplies neither).

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

/-! ## The scope check (`ExprOps.lean:835-861`)

Every `&&` of the cited code is an `if` nest in the port (task #13's deviation
6, which is what Charon produces from a `&&` anyway).  `bool_and_step` is the
`Bool`-valued analogue of `Refine/Expr.lean`'s `guard_step`: given the two
components' exactness, one link of the nest is exact. -/

/-! ## The two derived-field spec walks (`ExprOps.lean:1295-1325`)

`bvarBound` and `fvarRange` are the *specifications* of the packed word's two
range fields; the port carries them unmemoized and uncalled, so that the
provenance gate stays in step with their source (task #11's `beqRecursive`
rule).  `bvarBound`'s `body.bvarBound - 1` is Lean's truncated `Nat`
subtraction, which is what the module's `sub_nat` is for. -/

/-! ## Bulk abstraction (`ExprOps.lean:778-808`)

Not memoized on either side.  The `fvar` arm is the cited
`d ≤ idx ∧ idx < d + k` as an `if` nest (task #13's deviation 6), and its
machine arithmetic `c + ((d + k - 1) - idx)` is safe exactly under those two
guards -- which is what makes it con-leche's `Nat` expression
`c + (d + k - 1 - idx)`: with `d ≤ idx < d + k` no subtraction truncates, so
`omega` closes the two in one step from the four `*_val` equations. -/

/-! ## `liftLooseBVars` (`ExprOps.lean:380-539`)

`instantiate1_go`'s twin, node for node: the same `(node, cutoff)` memo, the
same five memo-skipping leaves, the same probe-recurse-record shape.  The one
difference is the fixed `amount`, which the answer depends on and the key does
not -- so, exactly as in con-leche, the invariant is parameterised by it and
the wrapper's fresh memo is what makes that sound. -/

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

/-! ### The two exact accessors

`bvar_b`/`fvar_b` read the packed field and fall back to the memoized walk on
the *saturated* value alone.  con-leche's `bvarB_eq`/`fvarB_eq` is the same
two-branch argument, and `bvarBRaw_exact`/`fvarBRaw_exact` is what makes the
unsaturated branch exact -- so each lemma is: the field read (`wf_data`, task
#20), the saturation test, and one of the two upstream theorems. -/

end ConRon.Refine.ExprOps

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`abstract_range_refines` is the deepest chain of the bulk-abstraction half
(`abstract1` under a `fvar_b` cutoff, once per variable of the block), and
`bvar_b_refines` is the one lemma that reads the *packed word* and falls back to
the memoized walk at saturation -- the two worth pinning here. -/

