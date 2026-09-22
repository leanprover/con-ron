/-
# `ConRon.Refine2.Core.Eqns` — the `partial_fixpoint` unfolding equations, derived once

**Task #97-P5-Arms, the tier's cost floor.**  Task #97-P5-Core §5 bisected
`Core/Induction.lean`'s 48.9 s of elaboration and found that **none of it is a
lemma cost**: 48 s of it is `blocked (unaccounted)` in the profiler, stubbing
all six `knotRel_succ_*` proofs with `sorry` moves it by 0.3 s, and a file
whose only content is `rw [arena.core.knot_whnf_core] at h` costs **9.6 s
net** on its own while the same file importing `Core/Induction.lean` costs
**0.0 s**.  The cost is the ONE-OFF derivation of a `partial_fixpoint`
definition's unfolding equation, and the derivation caches into the deriving
module's `.olean`.

`arena::core` is a **6 128-line mutual `partial_fixpoint` block of 100
functions** (`ConRon/Generated/Funs.lean:28309-34436`) plus a second of
**9** (`annotate_pis_leaf` … `knot_annotate`, `:40250-40798`).  At ≈ 9.4 s an
equation that is ≈ 17 minutes — *once*, if ONE module pays it and every arm
file imports that module, and ≈ 17 minutes *per arm file* otherwise, since
each would re-derive the subset it touches.

This module is that one payment.  It holds no theorem: only the realization of
each equation, in the shape `rw` / `unfold` / `simp only` ask for it
(`Lean.Meta.getEqnsFor?` and `getUnfoldEqnFor?` are literally what those
tactics call).

**Why not `#check @f.eq_def`.**  Measured: it realizes a *different* constant
and does **not** survive the `.olean` — a file importing a module whose only
content is `#check @arena.core.knot_whnf_core.eq_def` still pays the full
9.5 s at its first `rw`.  `getEqnsFor?` does survive.  That is the only reason
this file is written as a command elaborator rather than as a list of
`example`s, and it is worth keeping written down.
-/
import ConRon.Generated.Funs

namespace ConRon.Refine2.Core.Eqns

/-! **`force_eqns`** — force the unfolding equations of each named definition
into this module's `.olean`.  `Lean.Meta.getEqnsFor?` is what `rw [f]` calls
and `getUnfoldEqnFor?` what `unfold f` and `simp only [f]` call; realizing both
here is what makes both free in every importing file. -/

open Lean Elab Command in
elab "force_eqns" ids:ident+ : command => do
  for i in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    liftTermElabM do
      let _ ← Lean.Meta.getEqnsFor? n
      let _ ← Lean.Meta.getUnfoldEqnFor? n

/-! ## Block 1 — `arena::core`'s `whnf` / `infer` / `defeq` block, 100 functions

`ConRon/Generated/Funs.lean:28309-34436`: `arena.core.reduce_nat` …
`arena.core.knot_defeq`, plus `arena::core_gated`'s two. -/

open ConRon.Generated in
force_eqns
  arena.core.reduce_nat
  arena.core.reduce_nat_succ
  arena.core.reduce_nat_bin
  arena.core.reduce_nat_wf
  arena.core.iota_certs
  arena.core.iota_certs_aux
  arena.core.def_eq_list
  arena.core.iota_index_ok
  arena.core.proof_irrel
  arena.core.prop_sorts_zero
  arena.core.prop_sorts_zero_right
  arena.core.prop_irrel
  arena.core.struct_eta_proj_certs
  arena.core.struct_eta_cert_tail
  arena.core.struct_eta_cert_fam
  arena.core.struct_eta_cert_certs
  arena.core.struct_eta_cert_at
  arena.core.struct_eta_cert_with
  arena.core.struct_eta_cert
  arena.core.struct_unit_cert_tail
  arena.core.struct_unit_cert
  arena.core.eta_cert
  arena.core.eta_cert_body
  arena.core.stuck_irrel
  arena.core.major_to_ctor_certs
  arena.core.iota_certs_fam
  arena.core.major_to_ctor_k
  arena.core.major_to_ctor_eta_certs
  arena.core.major_to_ctor_eta
  arena.core.major_to_ctor_eta_build
  arena.core.major_to_ctor_and
  arena.core.major_to_ctor_and_build
  arena.core.major_to_ctor_at
  arena.core.major_to_ctor
  arena.core.lit_major_to_ctor
  arena.core.proj_lit_to_ctor
  arena.core.prepare_major
  arena.core.iota_rec_fire
  arena.core.iota_rec_params
  arena.core.iota_rec_certs
  arena.core.iota_rec_fam
  arena.core.iota_rec_major
  arena.core.iota_rec
  arena.core.iota_rec_at
  arena.core.proj_cert
  arena.core.proj_cert_at
  arena.core.whnf_core_proj
  arena.core.whnf_core_proj_at
  arena.core.whnf_core_proj_fire
  arena.core.whnf_app
  arena.core.beta_peel
  arena.core.whnf_core_stuck_app
  arena.core.whnf_core_body
  arena.core.whnf_step
  arena.core.whnf_loop
  arena.core.whnf_body
  arena.core.ensure_sort
  arena.core.infer_forall
  arena.core.infer_proj
  arena.core.infer_lam
  arena.core.infer_lam_open
  arena.core.infer_lam_cod
  arena.core.infer_spine
  arena.core.infer_app
  arena.core.infer_lams_leaf_check
  arena.core.infer_lams_leaf
  arena.core.infer_lams
  arena.core.infer_pis_leaf
  arena.core.infer_pis
  arena.core.infer_body
  arena.core.infer_body_io
  arena.core.infer_forall_io
  arena.core.infer_forall_io_at
  arena.core.infer_app_io_at
  arena.core.infer_spine_io
  arena.core.infer_proj_io
  arena.core.bool_true_shortcut
  arena.core.defeq_spine
  arena.core.defeq_binders
  arena.core.defeq_peel
  arena.core.defeq_peel_leaf
  arena.core.defeq_lit_app
  arena.core.defeq_lit_const
  arena.core.defeq_struct
  arena.core.defeq_apps
  arena.core.defeq_unfold_both
  arena.core.defeq_delta_both
  arena.core.defeq_delta
  arena.core.defeq_after_whnf
  arena.core.defeq_step
  arena.core.defeq_loop
  arena.core.defeq_body
  arena.core.knot_whnf_core
  arena.core.knot_whnf
  arena.core.knot_infer
  arena.core.knot_infer_io
  arena.core.knot_infer_at
  arena.core.knot_defeq
  arena.core_gated.whnf_core_app_gated
  arena.core_gated.whnf_core_body_gated

/-! ## Block 2 — the `annotate` block, 9 functions

`ConRon/Generated/Funs.lean:40250-40798`. -/

open ConRon.Generated in
force_eqns
  arena.core.annotate_pis_leaf
  arena.core.annotate_pis
  arena.core.annotate_lams_leaf
  arena.core.annotate_lams
  arena.core.annotate_binder
  arena.core.annotate_let
  arena.core.annotate_proj
  arena.core.annotate_body
  arena.core.knot_annotate

end ConRon.Refine2.Core.Eqns
