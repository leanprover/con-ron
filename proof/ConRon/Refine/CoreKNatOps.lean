/-
`CORE_PLAN.md` step 4 (task #49): the **`Nat`-operation pinning guards** of
`crates/con-ron-core/src/kernel/core_k.rs` — the eight predicates that license
the arithmetic fast path by pinning the stored declarations of `Nat.add` and
friends (`core_k.rs:1634-1852`).

Cited Lean: `ConLeche/Kernel/Core.lean:656-772` (`natOpGuard`, `natOpCod`,
`natOpTyPinned`, `natOpStoredOk`, `natOpStored`) and the index twins that
actually get stated here — `ConLeche/Kernel/FEnv.lean:133-152`
(`natOpGuardF`, `natOpStoredF`) and `ConLeche/Kernel/DeclCheck.lean:209-238`
(`natOpCodF`, `natOpTyPinnedF`, `natOpStoredOkF`).  `CoreKBase.lean`'s
`FindAgree` is *find*-agreement only, so the `F` twin is what a refinement of an
`FEnv`-reading guard can say; `ConLeche/Verify/CheckerF.lean:74-119`
(`natOpCodF_eq`, `natOpTyPinnedF_eq`, `natOpStoredOkF_eq`, `natOpGuardF_eq`)
turns each back into the `Env` version under `mkFEnv`.

Three things are worth recording.

* **The imported hypotheses.**  Five of these eight functions call something
  another task-#49 agent owns — the pinned names of `core_k.rs`
  (`bool_name`, `bool_true_name`, …, and the `nat_op_deps`/`nat_div_mod_names`
  name *lists*), `lp_empty`, `nat_lit_supported`, `defn_probe` — and
  `bool_stored_ok`/`lp_empty` both go through `env::to_constant_val`, which
  belongs to task #46's `Refine/Env.lean`.  Each is taken as an explicit
  hypothesis, packaged as one of the `*Spec`/`Pinned*` predicates below
  so the statements stay readable; the parent agent discharges them at merge.
  Nothing here proves a pinned name.

* **`nat_op_ty_pinned` is a depth-two node match**, so its proof cases the
  node twice (not an induction — the port's function does not recurse) and
  gets the children's well-formedness from `forall_e_wf_inv`, an inversion of
  the `ExprWF` derivation at a `.forallE` node that belongs in
  `Refine/Expr.lean`.  The Rust's `if dom then (if dom2 then cod else false)
  else false` nesting is the Lean's `&&` chain, and the nine non-`forallE`
  arms are `false` on both sides.

* **`rw` on a con-leche `match` definition generates splitter side goals**
  (`natOpTyPinnedF`, `natOpStoredOkF`): `unfold` is what leaves the matcher in
  place so it can iota-reduce once the node has been cased.  For the two
  guards whose Lean body stays opaque (`natOpGuardF`, `natOpCodF`) there is a
  spelled-out mirror (`natOpGuardL`, `natOpCodL`) with the shared clauses
  named; each mirror is the cited function by `rfl`.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.FEnv
import ConLeche.Kernel.DeclCheck

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## Plumbing -/

/-! ## The imported facts, as hypotheses

Every predicate in this section is somebody else's refinement lemma, stated
here so that this file proves none of them (`BRIEF.md` rule 1).  `PinnedName`
and `PinnedNames` are the §3.5 statement of a pinned name and of a pinned
`Vec<Name>`; the `*Spec`s are the statements of `core_k::lp_empty`,
`core_k::nat_lit_supported`, `env::to_constant_val` and (further down, where
its `defnProbeL` is) `core_k::defn_probe`. -/

/-! ## `defn_lp_empty` and `deps_all_stored` (`Core.lean:660-662`) -/

/-! ## `nat_op_guard` (`Core.lean:656-672`, `FEnv.lean:133-147`) -/

/-! ## `nat_op_cod` and `bool_stored_ok` (`Core.lean:712-722`,
`DeclCheck.lean:209-217`) -/

/-! ## `nat_op_ty_pinned` (`Core.lean:724-739`, `DeclCheck.lean:219-231`) -/

/-! ## `nat_op_stored_ok` and `nat_op_stored` (`Core.lean:741-772`,
`DeclCheck.lean:233-238`, `FEnv.lean:148-152`) -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`nat_op_guard_refines` is the headline lemma of the file and the one that goes
through everything else here (`defn_lp_empty`, the `deps_all_stored`
recursion, `Refine/Name.lean`'s exactness lemmas). -/

end ConRon.Refine.CoreK
