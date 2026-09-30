/-
`CORE_PLAN.md` step 4 (task #49), one of the `CoreK*` family: the **syntactic
readers, shape guards and owning environment probes** of
`crates/con-ron-core/src/kernel/core_k.rs`, against `ConLeche/Kernel/Core.lean`
(with `ConLeche/Kernel/FEnv.lean` supplying the indexed environment and
`ConLeche/Cached/StateC.lean` the `*C` twins, which are the *same* functions on
`Expr` and are named in each doc comment rather than stated twice).

Twenty-seven functions, in three groups:

* the five **environment probes** (`defn_probe`, `ctor_probe`, `ind_probe`,
  `rec_probe`, `lp_empty`) -- task #14's rule that the index's borrow dies at
  the call boundary, so each is Lean's `ConstantInfo` destructuring returning
  *owned copies*.  Their lemmas therefore carry `FindWF` and conclude the
  well-formedness of what comes back;
* the **guards** that read the environment (`is_ctor_app`, `is_unit_like_ty`
  with `is_punit_ind`/`is_punit_rec_shape`, `unfoldable_head`, `head_hint`,
  `str_expansion_fires`);
* the **pure readers** (`pi_result_is_prop`, `pi_result_z`,
  `pi_result_never_zero`, `caps_never_zero`, `same_const_heads`, `quick_pair`
  with `is_sort`/`is_lit`/`is_forall`/`is_lam_k`, `pw_written`,
  `annot_binder_meta`, `beta_gate_fires`, `fire_is_inert`, `rec_rule_k`).

Four things are worth recording.

**(1) `Env` versus `FEnv`.**  The cited `Core.lean` guards read `env.find?` on
an `Env`; the port reads `fenv::find` on the index (module note deviation 3),
and `CoreKBase.lean`'s `FindAgree` is *find-agreement only* -- it says nothing
about `lfe.env`.  So every environment-reading guard here is stated against the
cited definition's body with `lfe.find?` in place of `env.find?`, spelled out in
the statement: exactly the transposition `FEnv.lean` itself performs for
`natOpGuardF`/`strLitSupportedF` and `Cached/StateC.lean` for
`isCtorAppC`/`headHintC`/`unfoldableHeadC`/`isUnitLikeTyC`.  Nothing is
weakened: those matches *are* the cited functions once `Env.find?` is replaced
by the index lookup they agree with (`mkFEnv_find?`).

**(2) The `env`-module copies.**  A probe's result goes through
`env::constant_val_dup`, `env::ind_caps_dup`, `env::reducibility_hint_dup`,
`env::rec_rules_copy` and `env::to_constant_val`, none of which has a
refinement yet (task #46 owns `Refine/Env.lean`), and neither has
`env::beta_gate`.  The ten lemmas they need are proved locally in the first
section below and **belong in `Refine/Env.lean` on merge**; `reducibility_hint_dup` and `ind_caps_dup` turn out to be the
identity in the model, the other three only preserve the abstraction and the
well-formedness.

**(3) `wf_const_inv`.**  Casing on a node's *kind* (which is what a guard's
`match &f.0.kind` forces) loses the `ExprWF` derivation, so the `.const` arms
need "a well-formed `Const` node has a well-formed name and levels" as a
separate inversion.  It belongs in `Refine/Expr.lean` beside the other
`*_inv`s.

**(4) Pinned names and `str_lit_supported` are hypotheses.**  `punit_name`,
`punit_rec_name` and `string_of_list_name` are being proved in
`CoreKGuards`'s sibling `CoreKNames.lean`, and `core_k::str_lit_supported`
belongs to another agent's file; each is taken here as an explicit hypothesis
of the lemma that needs it, listed in its doc comment, for the parent agent to
discharge at merge.
-/
import ConRon.Refine.CoreKBase

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The `env`-module plumbing the probes need

Ten lemmas about `kernel/env.rs`'s copies and `beta_gate`.  **To be moved to
task #46's `Refine/Env.lean`** (see the file note, point 2). -/

/-! ## A missing `Expr` inversion

**To be moved to `Refine/Expr.lean`** beside the other `*_inv` lemmas (see the
file note, point 3). -/

/-! ## The four owning environment probes (`Core.lean`'s `ConstantInfo` destructurings)

Task #14's probe rule: the index's borrow dies at the call boundary, so each
probe returns *owned copies* of the pattern variables Lean's value semantics
hands its `match`.  Each lemma therefore takes `FindWF` and concludes the
well-formedness of what came back.  The Lean side is the destructuring itself,
named below. -/

/-! ## The one-constructor tests and `quick_pair` (`Core.lean:531-543`)

`Expr.quickPair` is the only cited definition here: Rust has no `.sort _`
pattern outside a `match`, so each slot of the cited pair is a named function
(`Core.lean`'s note).  Each therefore gets the arm of `quickPair` it computes. -/

/-! ## The remaining pure readers -/

/-! ## The `piResult` readers (`Core.lean:127-167`)

All three read the *syntactic* pi telescope through `expr_ops::pi_result`, whose
refinement (`ExprOpsSpine.lean`) supplies both the abstraction and the result's
well-formedness -- which is what the `Sort` arms' `LevelWF` comes from. -/

/-! ## The environment-reading guards

Each is stated against the cited `Core.lean` definition's body with `lfe.find?`
in place of `env.find?` (file note, point 1); the `Cached/StateC.lean` twin
named in each doc comment is that same body on `Expr`. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

end ConRon.Refine.CoreK
