/-
`kernel::canon`, refined (DESIGN.md §3.5, task #83).

`crates/con-ron-core/src/kernel/canon.rs` is the port of
`vendor/con-leche/ConLeche/Kernel/Canon.lean`: the level-parameter canonical
form the pinned basis blocks are matched up to.

**Why `canon` exists at all.**  Lean's exporter picks binder names, binder
annotations and level-parameter names freely, so a stream's `Nat` block is the
checker's pinned one only *up to* renaming level parameters and erasing binder
metadata.  `canonExpr`/`ConstantInfo.canon` are that renaming, and everything
in this file is about deciding equality of two canonical forms.

**Why the port carries the `Fast` walks and not the specifications.**
con-leche spells each comparison twice: `ConstantVal.canonEq`,
`ConstantInfo.canonEq` and `canonEqList` are `decide (canon x = canon y)` --
the SPECIFICATIONS -- and `canonExprEqFast`, `ConstantVal.canonEqFast`,
`canonRulesEqFast`, `ConstantInfo.canonEqFast`, `canonEqListFast` are lockstep
twins that descend the two terms **together** and stop at the first
disagreement; `@[csimp]` swaps each pair.  Building `canon` of the *stream*
side rebuilds every node, which unshares its DAG:
`vendor/con-leche/tests/e2e/tower_quot.ndjson` is a depth-60 shared tower
(`2^60` nodes unshared) and the specification exhausts memory on it.  The port
therefore carries only the twins, and the refinement route is the same shape:
the Rust walk refines the Lean `*Fast` walk by structural induction, and
con-leche's own `canonExprEqFast_iff` / `ConstantVal.canonEqFast_iff` /
`ConstantInfo.canonEqFast_iff` / `canonEqListFast_iff` carry that to the
specification, which is what the rest of the tier reads
(`basisPinHit`/`quotPinHit`, `ConRon/Refine/BasisRaw.lean`).

These are *pure* functions: there is no `CheckError` here, only Aeneas's
`Result`, so task #67's full-outcome convention does not apply and nothing
below claims anything about a `fail`.
-/
import ConRon.Generated
import ConRon.Refine.Abs
import ConRon.Refine.Name
import ConRon.Refine.Level
import ConRon.Refine.Expr
import ConRon.Refine.ExprOps
import ConRon.Refine.Env
import ConLeche.Kernel.Canon

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Canon

/-! ## `canon_name_map`: the renaming a level-parameter list induces -/

/-! ## `canon_level`: the renaming, applied to a level

A `Level` is a handful of nodes, so the port renames one outright rather than
comparing in lockstep (`canon.rs`'s module note); the two `*Fast` arms that
need a level compare *built* canonical levels.  The walk therefore has to
deliver a well-formed result as well as the right one: `level::beq` is exact
only on well-formed arguments. -/

/-! ## `canon_level_list`: `us.map (canonLevel m)`, the `.const` arm's list

The index recursion of `canon.rs`'s `canon_level_list_from` (§3.4 forbids
closures and loops); the accumulator is a `Vec`, so the invariant is
`out ++ …` (task #13's deviation 3: a `Vec` has no shared tail). -/

/-! ## `canon_expr_eq_fast`: the lockstep descent

The port's walk against con-leche's `canonExprEqFast`, by structural induction
on the left argument (`ExprWF.ind_node`) with the right one destructured in
each arm.  Ten constructors against ten: the ninety off-diagonal pairs are
`ok false` on the Rust side and the catch-all `_, _ => false` on the Lean's,
because `absExpr` maps the port's ten kinds onto con-leche's ten
constructors. -/

/-! ## The rule lists

`canonRulesEqFast` compares a recursor's iota rules through the canonical form
of each rule's right-hand side; every other field is compared verbatim, which
is what `canon::rec_rule_eq_but_rhs` spells out. -/

/-! ## `ConstantVal`, `ConstantInfo` and the block

Each of the three ends at con-leche's *specification* — `decide (canon x =
canon y)` — through the `@[csimp]` lemma that identifies it with the lockstep
twin the port carries. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

end ConRon.Refine.Canon
