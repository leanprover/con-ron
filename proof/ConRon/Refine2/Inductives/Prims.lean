/-
# `ConRon.Refine2.Inductives.Prims` — the tier's `@[lockstep]` callees from other tiers

Task #97-T2-LOCKSTEP lane Inductives round 3.  The tier's Rust calls about
65 functions outside `arena::inductives` (the core's level comparison, the
environment's readers, the checker's `checker_base`, the promote tier's name
builders …).  Their Theorem-2 lemmas live with their owners, mostly as
`_refines`/`_run` statements in `Sim₀`/`LSS` form without the `@[lockstep]`
attribute; this file files them for the tactic — in `LS` form where a
conversion is needed, by `attribute [lockstep]` where not — and adds the
Rust-only specs the tier's zips need.  Nothing here restates an owner's lemma.
-/
import ConRon.Refine2.Checker.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep in
/-- `arena::monad::read_level_m` ⊑ `readLevelM` (`Refine2/Specs.lean`). -/
@[lockstep] theorem read_level_m_ls {pers st lst} {h : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = ConRon.Refine.absLevel a) (arena.monad.read_level_m pers st h) lst
      (Arena.readLevelM (absLIdx h)) :=
  LS.ofSim₀ fun _ h => read_level_m_run₀ hrel hinv h

open Lockstep in
/-- `arena::monad::intern_n_node` ⊑ `internNNode` (`Refine2/Specs.lean`). -/
@[lockstep] theorem intern_n_node_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_n_node pers st v) lst
      (Arena.internNNode (absNNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_n_node_run₀ hrel hinv v hvwf h

open Lockstep in
/-- A `usize`-to-`u64` cast (`v.len() as u64`) is the identity on the value. -/
@[lockstep] theorem lift_cast_usize_u64_spec (x : Std.Usize) :
    LSP (lift (UScalar.cast .U64 x)) (fun a => a.val = x.val) := by
  intro a h
  simp only [lift, Result.ok.injEq] at h
  subst h
  exact ConRon.Refine.ExprOps.usize_cast_u64_val x

open Lockstep in
/-- `expr_ops::sub_nat` is truncated `Nat` subtraction. -/
@[lockstep] theorem sub_nat_spec (a b : Std.U64) :
    LSP (kernel.expr_ops.sub_nat a b) (fun r => r.val = a.val - b.val) :=
  fun _ h => ConRon.Refine.ExprOps.sub_nat_val h

/-! ## The mode gates: each is its twin field, a Rust-only step -/

open Lockstep in
@[lockstep] theorem tt_checks_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.tt_checks m) (fun b => TwinEq (ConRon.Refine.absMode m).ttChecks b) := by
  intro b h
  cases m <;> (simp only [kernel.env.tt_checks, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem verified_checks_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m) (fun b => TwinEq (ConRon.Refine.absMode m).verifiedChecks b) := by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem beta_gate_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.beta_gate m) (fun b => TwinEq (ConRon.Refine.absMode m).betaGate b) := by
  intro b h
  cases m <;> (simp only [kernel.env.beta_gate, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem io_gate_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.io_gate m) (fun b => TwinEq (ConRon.Refine.absMode m).ioGate b) := by
  intro b h
  cases m <;> (simp only [kernel.env.io_gate, Result.ok.injEq] at h; rw [← h]; rfl)

open Lockstep in
@[lockstep] theorem certs_twin (m : kernel.env.CheckMode) :
    LSP (kernel.env.certs m) (fun b => TwinEq (ConRon.Refine.absMode m).certs b) := by
  intro b h
  cases m <;> (simp only [kernel.env.certs, Result.ok.injEq] at h; rw [← h]; rfl)

/-! ## The port's message and name-part constants

A name the port builds from a constant (`intern_n_node (Str n (code_points
REC))`) is the twin's `.str n "rec"`: the literal is `lift (to_slice REC)` then
`code_points`, two Rust-only steps whose specs carry the code points, and the
side goals `absString v = "rec"` / `StrWF v` are then a computation on a
three-element list. -/

open Lockstep in
@[lockstep] theorem lift_to_slice_spec {n : Std.Usize} (X : Array Std.U32 n) :
    LSP (lift (Array.to_slice X)) (fun s => s.val = X.val) := by
  intro s h
  simp only [lift, Result.ok.injEq] at h
  subst h
  simp

open Lockstep in
@[lockstep] theorem code_points_spec (s : Slice Std.U32) :
    LSP (kernel.core_types.code_points s) (fun v => v.val = s.val) :=
  fun _ h => ConRon.Refine.Env.code_points_val h

open Lean Elab Tactic in
/-- Fails unless the goal mentions a name-part string (`absString`, `StrWF`,
`NNodeViewWF`): the string tier's `simp only [global_simps] at *` is not free. -/
elab "ind_str_guard" : tactic => do
  let t ← getMainTarget
  unless t.containsConst (fun n => n == ``ConRon.Refine.absString ||
      n == ``ConRon.Refine.StrWF || n == ``NNodeViewWF || n == ``absNNodeView) do
    throwError "ind_str_guard: no string goal"

/-- The string side goals of a constant name part. -/
macro "ind_str_side" : tactic =>
  `(tactic| (ind_str_guard
             try simp only [global_simps] at *
             simp_all [Array.make, ConRon.Refine.absString, ConRon.Refine.StrWF, NNodeViewWF, absNNodeView]
             try decide))

macro_rules
  | `(tactic| lockstep_side_ext) => `(tactic| (ind_str_side; done))

/-- The name part `"proj_" ++ toString i` the port builds from the literal
`PROJ_` and `nat_to_dec i`. -/
theorem proj_name_part {a v1 dig : alloc.vec.Vec Std.U32} {sl : Slice Std.U32} {n : Nat}
    (hcat : a.val = v1.val ++ (alloc.vec.Vec.deref dig).val) (hv1 : v1.val = sl.val)
    (hsl : sl.val = (arena.core.proj_model_name.PROJ_).val)
    (hdig : ConRon.Refine.absCodes dig.val = toString n ∧ ConRon.Refine.StrWF dig) :
    ConRon.Refine.absString a = "proj_" ++ toString n ∧ ConRon.Refine.StrWF a := by
  have hl : a.val = [112#u32, 114#u32, 111#u32, 106#u32, 95#u32] ++ dig.val := by
    rw [hcat, hv1, hsl]; simp [arena.core.proj_model_name.PROJ_, alloc.vec.Vec.deref]
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absString_eq, hl, ConRon.Refine.CoreK.absCodes_append, hdig.1]; rfl
  · intro c hc
    rw [hl, List.mem_append] at hc
    rcases hc with hc | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
    · exact hdig.2 c hc

/-! ## Three Core readers the inductive routes call (task #97-T2-LOCKSTEP lane
Inductives round 4): `proj_model_name`, `pi_result_is_prop`, `pi_result_z`.
No lane owns them; both the Native/Struct/Sum tier and the Modeled lane use them. -/

open Lockstep in
@[lockstep] theorem nat_to_dec_spec (i : Std.U64) :
    LSP (kernel.core_k.nat_to_dec i)
      (fun r => ConRon.Refine.absCodes r.val = toString i.val ∧ ConRon.Refine.StrWF r) :=
  fun _ h => ConRon.Refine.CoreK.nat_to_dec_refines h

open Lockstep in
@[lockstep] theorem code_points_from_zero_spec (s : Slice Std.U32) (out : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.code_points_from s 0#usize out)
      (fun v => v.val = out.val ++ s.val) := by
  intro v h
  have := ConRon.Refine.Env.code_points_from_val s _ 0#usize out v (le_refl _) h
  simpa using this

/-- `proj_model_name` ⊑ `projModelName` — `(T.str "_model").str ("proj_" ++ toString i)`. -/
theorem proj_model_name_refines {pers st lst} {t : arena.handle.NIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.proj_model_name pers st t i = ok o) :
    Sim₀ absNIdx pers lst o (projModelName (absNIdx t) (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.core.proj_model_name, projModelName]
  lockstep
  -- the second part is a concatenation (`"proj_" ++ toString i`)
  all_goals
    rename_i dig hdig sl hsl v1 hv1
    obtain ⟨hs, hwf⟩ := proj_name_part hP hv1 hsl hdig
    have e : NNodeView.str (absNIdx ‹arena.handle.NIdx›) ("proj_" ++ toString i.val)
        = absNNodeView (.Str ‹arena.handle.NIdx› a) := by
      simp only [absNNodeView, hs]
    rw [e]
    exact intern_n_node_ls ‹_› ‹_› _ hwf

open Lockstep in
@[lockstep] theorem proj_model_name_ls {pers st lst} {t : arena.handle.NIdx} {i : Std.U64}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.proj_model_name pers st t i) lst
      (projModelName (absNIdx t) (absU i)) :=
  LS.ofSim₀ fun _ h => proj_model_name_refines hrel hinv h

/-- `pi_result_is_prop` ⊑ `piResultIsProp`.  **Waits on `expr_ops::pi_result`'s
lockstep lemma** (the ExprOps lane): past it, the zip is `tag`, `view_sort`,
`zero_level`, `lvl_eq` — all filed here — and one `lockstep` call closes it. -/
theorem pi_result_is_prop_refines {pers st lst} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.pi_result_is_prop pers st e = ok o) :
    Sim₀ id pers lst o (piResultIsProp (absEIdx e)) := by
  sorry

open Lockstep in
@[lockstep] theorem pi_result_is_prop_ls {pers st lst} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.core.pi_result_is_prop pers st e) lst
      (piResultIsProp (absEIdx e)) :=
  LS.ofSim₀ fun _ h => pi_result_is_prop_refines hrel hinv h

/-- `pi_result_z` ⊑ `piResultZ`.  **Waits on `expr_ops::pi_result`'s lockstep
lemma**, as above; past it `tag`, `view_sort`, `read_level_m` and the pure
`zeroness_of`. -/
theorem pi_result_z_refines {pers st lst} {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.pi_result_z pers st e = ok o) :
    Sim₀ ConRon.Refine.absPropWhen pers lst o (piResultZ (absEIdx e)) := by
  sorry

open Lockstep in
@[lockstep] theorem pi_result_z_ls {pers st lst} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = ConRon.Refine.absPropWhen a) (arena.core.pi_result_z pers st e) lst
      (piResultZ (absEIdx e)) :=
  LS.ofSim₀ fun _ h => pi_result_z_refines hrel hinv h

/-! ## The checker tier's statements in `LS` form

Generated from `Refine2/Checker/{Base,Pins,Axioms,Canon}.lean` (every
`_refines` without an `LS` companion): one `LS.ofSim₀`/`ofSimRel₀`/`LSR.ofSimRE`
line each, in their own namespace so a companion the checker lane adds later
does not clash. -/

namespace IndPrims

open Lockstep in
@[lockstep] theorem nidx_is_model_suffix_ls
    {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.checker_base.nidx_is_model_suffix pers st n) st lst
                   (NIdx.isModelSuffix (absNIdx n)) :=
  LSR.ofSimRE hrel hinv fun _ h => nidx_is_model_suffix_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nidx_is_proj_fn_shape_ls
    {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.checker_base.nidx_is_proj_fn_shape pers st n) st lst
                   (NIdx.isProjFnShape (absNIdx n)) :=
  LSR.ofSimRE hrel hinv fun _ h => nidx_is_proj_fn_shape_refines hrel hinv h


open Lockstep in
@[lockstep] theorem consts_resolve_f_fast_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = id a) (arena.checker_base.consts_resolve_f_fast pers vis st rf e) lst
      (constsResolveFFast (lf.restrictTo (absU vis)) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => consts_resolve_f_fast_refines hrel hinv hfe.rel hfe.inv h


open Lockstep in
@[lockstep] theorem all_level_params_defined_ls
    {pers st lst}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.checker_base.all_level_params_defined pers st lps e) st lst
                   (allLevelParamsDefined (absNIdxL lps) (absEIdx e)) :=
  LSR.ofSimRE hrel hinv fun _ h => all_level_params_defined_refines hrel hinv h


open Lockstep in
@[lockstep] theorem unresolved_consts_error_ls
    {pers st lst}
    {e : arena.handle.EIdx}
    {w : String}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v) (arena.checker_base.unresolved_consts_error pers st e) lst
      (unresolvedConstsError w (absEIdx e)) :=
  LS.ofSimRel₀ fun _ h => unresolved_consts_error_refines hrel hinv h


open Lockstep in
@[lockstep] theorem check_constant_val_guards_rest_ls
    {pers st lst}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_constant_val_guards_rest pers st cv) lst
      (checkConstantValGuardsRestSpec (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_guards_rest_refines hrel hinv h


open Lockstep in
@[lockstep] theorem check_constant_val_guards_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_constant_val_guards pers vis st rf cv) lst
      (checkConstantValGuardsSpec lf (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => check_constant_val_guards_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem install_constant_val_tail_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv : arena.env.IConstantVal}
    {ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a) (arena.checker_base.install_constant_val_tail pers vis st rf cv ty) lst
      (installConstantValTailSpec lf (absIConstantVal cv) (absEIdx ty)) :=
  LS.ofSim₀ fun _ h => install_constant_val_tail_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_constant_val_after_annot_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {cv : arena.env.IConstantVal}
    {ty : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absIConstantVal a) (arena.checker_base.check_constant_val_after_annot pers vis st mode rf cv ty) lst
      (checkConstantValAfterAnnotSpec (ConRon.Refine.absMode mode) lf
        (absIConstantVal cv) (absEIdx ty)) :=
  LS.ofSim₀ fun _ h => check_constant_val_after_annot_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem open_pis_at_fvars_ls
    {pers st lst}
    {n : Std.U64}
    {h : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a) (arena.checker_base.open_pis_at_fvars pers st n h i) lst
                 (openPisAtFvars (absU n) (absEIdx h) (absU i)) :=
  LS.ofSim₀ fun _ h => open_pis_at_fvars_refines hrel hinv h


open Lockstep in
@[lockstep] theorem open_pis_at_fvars_f_go_ls
    {pers st lst}
    {acc : alloc.vec.Vec arena.handle.EIdx}
    {n : Std.U64}
    {h : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a) (arena.checker_base.open_pis_at_fvars_f_go pers st acc n h i) lst
      (openPisAtFvarsFGo (absEIdxL acc).toArray (absU n) (absEIdx h) (absU i)) :=
  LS.ofSim₀ fun _ h => open_pis_at_fvars_f_go_refines hrel hinv h


open Lockstep in
@[lockstep] theorem open_pis_at_fvars_f_ls
    {pers st lst}
    {n : Std.U64}
    {e : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map (fun p => (absEIdxL p.1, absEIdx p.2))) a) (arena.checker_base.open_pis_at_fvars_f pers st n e i) lst
                 (openPisAtFvarsF (absU n) (absEIdx e) (absU i)) :=
  LS.ofSim₀ fun _ h => open_pis_at_fvars_f_refines hrel hinv h


open Lockstep in
@[lockstep] theorem fvar_type_ds_ls
    {pers st lst}
    {hs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdxL a) (arena.checker_base.fvar_type_ds pers st hs i out) st lst
      (do pure (absEIdxL out ++ (← fvarTypeDs (absEIdxLFrom hs i)))) :=
  LSR.ofSimRE hrel hinv fun _ h => fvar_type_ds_refines hrel hinv h


open Lockstep in
@[lockstep] theorem is_eq_head_ls
    {pers st lst}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.checker_base.is_eq_head pers st h) lst
                       (isEqHead (absEIdx h)) :=
  LS.ofSim₀ fun _ h => is_eq_head_refines hrel hinv h


open Lockstep in
@[lockstep] theorem eq_head_level_at_ls
    {pers st lst}
    {us : arena.handle.LsIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a) (arena.checker_base.eq_head_level_at pers st us) lst
      (do
        match ← viewLs (absLsIdx us) with
        | [l] => pure l
        | _ => zeroLevel) :=
  LS.ofSim₀ fun _ h => eq_head_level_at_refines hrel hinv h


open Lockstep in
@[lockstep] theorem eq_head_level_ls
    {pers st lst}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absLIdx a) (arena.checker_base.eq_head_level pers st h) lst
                            (eqHeadLevel (absEIdx h)) :=
  LS.ofSim₀ fun _ h => eq_head_level_refines hrel hinv h


open Lockstep in
@[lockstep] theorem check_typed_list_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {xs ts : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_typed_list pers vis st mode rf depth xs ts i) lst
      (checkTypedList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ts i)) :=
  LS.ofSim₀ fun _ h => check_typed_list_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_annot_list_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {xs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_annot_list pers vis st mode rf depth xs i) lst
      (checkAnnotList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i)) :=
  LS.ofSim₀ fun _ h => check_annot_list_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_def_eq_list_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {depth : Std.U64}
    {xs ys : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_def_eq_list pers vis st mode rf depth xs ys i) lst
      (checkDefEqList (ConRon.Refine.absMode mode) lf (absU depth)
        (absEIdxLFrom xs i) (absEIdxLFrom ys i)) :=
  LS.ofSim₀ fun _ h => check_def_eq_list_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem ifenv_find_cv_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = (Option.map absIConstantVal) a) (arena.checker_base.ifenv_find_cv pers vis st rf n) lst
      (lf.findCV? (absNIdx n)) :=
  LS.ofSim₀ fun _ h => ifenv_find_cv_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem pi_result_sort_ls
    {pers st lst}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (Option.map absLIdx) a) (arena.checker_base.pi_result_sort pers st e) st lst
                                     (piResultSort (absEIdx e)) :=
  LSR.ofSimRE hrel hinv fun _ h => pi_result_sort_refines hrel hinv h


open Lockstep in
@[lockstep] theorem check_proj_shape_residual_ls
    {pers st lst}
    {cbody : arena.handle.EIdx}
    {n_p : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_proj_shape_residual pers st cbody n_p) st lst
      (do
        unless (← getAppArgs coreWalkFuel (absEIdx cbody)).length == absU n_p do
          fail (.notImplemented "projection constructor residual arity")
        match ← view (← getAppFn coreWalkFuel (absEIdx cbody)) with
        | .const _ _ => pure ()
        | _ => fail (.notImplemented "projection constructor residual head")) :=
  LSR.ofSimRE hrel hinv fun _ h => check_proj_shape_residual_refines hrel hinv h


open Lockstep in
@[lockstep] theorem check_proj_shape_ls
    {pers st lst}
    {pty ctor_ty : arena.handle.EIdx}
    {n_p n_f : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_base.check_proj_shape pers st pty ctor_ty n_p n_f) st lst
      (checkProjShape (absEIdx pty) (absEIdx ctor_ty) (absU n_p) (absU n_f)) :=
  LSR.ofSimRE hrel hinv fun _ h => check_proj_shape_refines hrel hinv h


open Lockstep in
@[lockstep] theorem proj_rule_wf_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {rhs_a : arena.handle.EIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.checker_base.proj_rule_wf pers vis st rf rhs_a lps) lst
      (do
        pure ((← allLevelParamsDefined (absNIdxL lps) (absEIdx rhs_a)) &&
          (← constsResolveFFast lf (absEIdx rhs_a)) &&
          (← looseBVarsBoundedFast coreWalkFuel 0 (absEIdx rhs_a)) &&
          !(← hasFvarFast coreWalkFuel (absEIdx rhs_a)))) :=
  LS.ofSim₀ fun _ h => proj_rule_wf_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_proj_rule_frame_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {n_p n_f : Std.U64}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {crest_p rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_base.check_proj_rule_frame pers vis st mode rf n_p n_f fvs_p crest_p rhs_a) lst
      (checkProjRuleFrameSpec (ConRon.Refine.absMode mode) lf (absU n_p) (absU n_f)
        (absEIdxL fvs_p) (absEIdx crest_p) (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_frame_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_proj_rule_certs_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_base.check_proj_rule_certs pers vis st mode rf pty cvj n_p n_f rhs_a) lst
      (checkProjRuleCertsSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_certs_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_proj_rule_shape_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {n_p n_f : Std.U64}
    {bv rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_base.check_proj_rule_shape pers vis st mode rf pty cvj n_p n_f bv rhs_a) lst
      (checkProjRuleShapeSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_shape_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_proj_rule_wf_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {bv rhs_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_base.check_proj_rule_wf pers vis st mode rf pty cvj lps n_p n_f bv rhs_a) lst
      (checkProjRuleWfSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs_a)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_wf_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_proj_rule_scoped_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f : Std.U64}
    {bv rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_base.check_proj_rule_scoped pers vis st mode rf pty cvj lps n_p n_f bv rhs) lst
      (checkProjRuleScopedSpec (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absEIdx bv)
        (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_scoped_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem check_proj_rule_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {pty : arena.handle.EIdx}
    {cvj : arena.env.IConstantVal}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_f i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hvis : absU vis = lf.visibleBelow) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_base.check_proj_rule pers vis st mode rf pty cvj lps n_p n_f i) lst
      (checkProjRule (ConRon.Refine.absMode mode) lf (absEIdx pty)
        (absIConstantVal cvj) (absNIdxL lps) (absU n_p) (absU n_f) (absU i)) :=
  LS.ofSim₀ fun _ h => check_proj_rule_refines hrel hinv hfe.rel hfe.inv hvis h


open Lockstep in
@[lockstep] theorem ind_params_ok_at_ls
    {pers st lst}
    {n_p : Std.U64}
    {ci : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.checker_base.ind_params_ok_at pers st n_p ci) lst
      (indParamsOkAtSpec (absU n_p) (absIConstantInfo ci)) :=
  LS.ofSim₀ fun _ h => ind_params_ok_at_refines hrel hinv h


open Lockstep in
@[lockstep] theorem install_value_tail_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {cv : arena.env.IConstantVal}
    {value_a : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = absEIdx a) (arena.checker_split.install_value_tail pers vis st rf cv value_a) lst
      (installValueTailSpec (lf.restrictTo (absU vis)) (absIConstantVal cv)
        (absEIdx value_a)) :=
  LS.ofSim₀ fun _ h => install_value_tail_refines hrel hinv hfe.rel hfe.inv h


open Lockstep in
@[lockstep] theorem check_value_group_tail_ls
    {pers st lst}
    {vis : Std.U64}
    {rf lf}
    {mode : kernel.env.CheckMode}
    {g : arena.checker_split.ValueGroup}
    {jv : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.checker_split.check_value_group_tail pers vis st mode rf g jv) lst
      (checkValueGroupTailSpec (ConRon.Refine.absMode mode)
        (lf.restrictTo (absU vis)) (absValueGroup g) (absEIdx jv)) :=
  LS.ofSim₀ fun _ h => check_value_group_tail_refines hrel hinv hfe.rel hfe.inv h


open Lockstep in
@[lockstep] theorem name_read_sim_ls
    {pers : arena.store.PersTier}
    {st : arena.monad.AState}
    {lst : AState}
    {pin : Result (core.result.Result arena.handle.NIdx kernel.core_types.CheckError)}
    {tw : AM NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hS : ∀ r, pin = ok r → SimRE absNIdx lst r tw) :
    LS pers (fun a b => b = absNIdx a) ((do let r ← pin; ok (r, st))) lst
                            tw :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv hS h


open Lockstep in
@[lockstep] theorem intern_reserved_pins_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a) (arena.pins.intern_reserved_pins pers st) lst
                                         internReservedPins :=
  LS.ofSim₀ fun _ h => intern_reserved_pins_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_at_ls
    {pers st lst}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_at st i) st lst
                        (pinAt (absSz i)) :=
  LSR.ofSimRE hrel hinv fun _ h => pin_at_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_reserved_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxL a) (arena.pins.pin_reserved st) st lst
                         pinReserved :=
  LSR.ofSimRE hrel hinv fun _ h => pin_reserved_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reserved_basis_names_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxL a) (arena.core.reserved_basis_names st) st lst
                         reservedBasisNames :=
  LSR.ofSimRE hrel hinv fun _ h => reserved_basis_names_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_empty_levels_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a) (arena.pins.pin_empty_levels st) st lst
                         pinEmptyLevels :=
  LSR.ofSimRE hrel hinv fun _ h => pin_empty_levels_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_zero_level_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.pins.pin_zero_level st) st lst
                        pinZeroLevel :=
  LSR.ofSimRE hrel hinv fun _ h => pin_zero_level_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_sort_one_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a) (arena.pins.pin_sort_one st) st lst
                        pinSortOne :=
  LSR.ofSimRE hrel hinv fun _ h => pin_sort_one_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_eq_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_eq st) st lst
                        pinEq :=
  LSR.ofSimRE hrel hinv fun _ h => pin_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_punit_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_punit st) st lst
                        pinPUnit :=
  LSR.ofSimRE hrel hinv fun _ h => pin_punit_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_punit_rec_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_punit_rec st) st lst
                        pinPUnitRec :=
  LSR.ofSimRE hrel hinv fun _ h => pin_punit_rec_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat st) st lst
                        pinNat :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_zero_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_zero st) st lst
                        pinNatZero :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_zero_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_succ_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_succ st) st lst
                        pinNatSucc :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_succ_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_string_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string st) st lst
                        pinString :=
  LSR.ofSimRE hrel hinv fun _ h => pin_string_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_string_of_list_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string_of_list st) st lst
                        pinStringOfList :=
  LSR.ofSimRE hrel hinv fun _ h => pin_string_of_list_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_list_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_list st) st lst
                        pinList :=
  LSR.ofSimRE hrel hinv fun _ h => pin_list_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_list_nil_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_list_nil st) st lst
                        pinListNil :=
  LSR.ofSimRE hrel hinv fun _ h => pin_list_nil_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_list_cons_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_list_cons st) st lst
                        pinListCons :=
  LSR.ofSimRE hrel hinv fun _ h => pin_list_cons_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_char_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_char st) st lst
                        pinChar :=
  LSR.ofSimRE hrel hinv fun _ h => pin_char_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_and_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_and st) st lst
                        pinAnd :=
  LSR.ofSimRE hrel hinv fun _ h => pin_and_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_char_of_nat_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_char_of_nat st) st lst
                        pinCharOfNat :=
  LSR.ofSimRE hrel hinv fun _ h => pin_char_of_nat_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_sorry_ax_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_sorry_ax st) st lst
                        pinSorryAx :=
  LSR.ofSimRE hrel hinv fun _ h => pin_sorry_ax_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_pred_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_pred st) st lst
                        pinNatPred :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_pred_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_add_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_add st) st lst
                        pinNatAdd :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_add_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_sub_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_sub st) st lst
                        pinNatSub :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_sub_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_mul_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_mul st) st lst
                        pinNatMul :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_mul_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_pow_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_pow st) st lst
                        pinNatPow :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_pow_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_beq_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_beq st) st lst
                        pinNatBeq :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_beq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_ble_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_ble st) st lst
                        pinNatBle :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_ble_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_div_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_div st) st lst
                        pinNatDiv :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_div_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_mod_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_mod st) st lst
                        pinNatMod :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_mod_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_gcd_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_gcd st) st lst
                        pinNatGcd :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_gcd_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_land_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_land st) st lst
                        pinNatLand :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_land_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_lor_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_lor st) st lst
                        pinNatLor :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_lor_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_xor_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_xor st) st lst
                        pinNatXor :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_xor_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_shift_left_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_shift_left st) st lst
                        pinNatShiftLeft :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_shift_left_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_nat_shift_right_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_shift_right st) st lst
                        pinNatShiftRight :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_shift_right_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_bool_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_bool st) st lst
                        pinBool :=
  LSR.ofSimRE hrel hinv fun _ h => pin_bool_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_bool_true_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_bool_true st) st lst
                        pinBoolTrue :=
  LSR.ofSimRE hrel hinv fun _ h => pin_bool_true_refines hrel hinv h


open Lockstep in
@[lockstep] theorem pin_bool_false_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_bool_false st) st lst
                        pinBoolFalse :=
  LSR.ofSimRE hrel hinv fun _ h => pin_bool_false_refines hrel hinv h


open Lockstep in
@[lockstep] theorem intern_pin_set_proofs_ls
    {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet}
    {dp mp gp lap lop xp slp srp : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps) :
    LS pers (fun a b => b = absINatOpPinSet a) (arena.nat_op_pin_set.intern_pin_set_proofs pers st ps dp mp gp lap lop xp slp srp) lst
      (do
        let dc ← internExprList (ConRon.Refine.absExprs ps.div_proofs)
        let mc ← internExprList (ConRon.Refine.absExprs ps.mod_proofs)
        let gc ← internExprList (ConRon.Refine.absExprs ps.gcd_proofs)
        let lac ← internExprList (ConRon.Refine.absExprs ps.land_proofs)
        let loc ← internExprList (ConRon.Refine.absExprs ps.lor_proofs)
        let xc ← internExprList (ConRon.Refine.absExprs ps.xor_proofs)
        let slc ← internExprList (ConRon.Refine.absExprs ps.shift_left_proofs)
        let src ← internExprList (ConRon.Refine.absExprs ps.shift_right_proofs)
        pure ⟨ConRon.Refine.absString ps.toolchain, absEIdx dp, absEIdx mp,
          absEIdx gp, absEIdx lap, absEIdx lop, absEIdx xp, absEIdx slp,
          absEIdx srp, dc, mc, gc, lac, loc, xc, slc, src⟩) :=
  LS.ofSim₀ fun _ h => intern_pin_set_proofs_refines hrel hinv hwf h


open Lockstep in
@[lockstep] theorem intern_pin_set_ls
    {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps) :
    LS pers (fun a b => b = absINatOpPinSet a) (arena.nat_op_pin_set.intern_pin_set pers st ps) lst
      (internPinSet (ConRon.Refine.absNatOpPinSet ps)) :=
  LS.ofSim₀ fun _ h => intern_pin_set_refines hrel hinv hwf h


open Lockstep in
@[lockstep] theorem intern_pin_sets_ls
    {pers st lst}
    {pss : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pss.val, NatOpPinSetWF p) :
    LS pers (fun a b => b = absINatOpPinSetL a) (arena.nat_op_pin_set.intern_pin_sets pers st pss i out) lst
      (do pure (absINatOpPinSetL out ++
        (← internPinSets ((pss.val.drop i.val).map ConRon.Refine.absNatOpPinSet)))) :=
  LS.ofSim₀ fun _ h => intern_pin_sets_refines hrel hinv hwf h


open Lockstep in
@[lockstep] theorem basis_kind_decls_ls
    {pers st lst}
    {k : kernel.env.BasisKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a) (arena.basis.basis_kind_decls pers st k) lst
      (BasisKind.decls (ConRon.Refine.absBasisKind k)) :=
  LS.ofSim₀ fun _ h => basis_kind_decls_refines hrel hinv h


open Lockstep in
@[lockstep] theorem basis_kind_decls_a_ls
    {pers st lst}
    {k : kernel.env.BasisKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a) (arena.basis.basis_kind_decls_a pers st k) lst
      (BasisKind.declsA (ConRon.Refine.absBasisKind k)) :=
  LS.ofSim₀ fun _ h => basis_kind_decls_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem basis_pin_hit_go_ls
    {pers st lst}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {ks : alloc.vec.Vec kernel.env.BasisKind}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map ConRon.Refine.absBasisKind) a) (arena.basis.basis_pin_hit_go pers st block ks i) lst
      (basisPinHitGo (absICIL block) (absBasisKindLFrom ks i)) :=
  LS.ofSim₀ fun _ h => basis_pin_hit_go_refines hrel hinv h


open Lockstep in
@[lockstep] theorem quot_pin_hit_ls
    {pers st lst}
    {k : kernel.env.QuotKind}
    {cv : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.basis.quot_pin_hit pers st k cv) lst
      (quotPinHit (ConRon.Refine.absQuotKind k) (absIConstantVal cv)) :=
  LS.ofSim₀ fun _ h => quot_pin_hit_refines hrel hinv h


open Lockstep in
@[lockstep] theorem propext_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.propext_name st) lst
      (propextName) :=
  LS.ofSim₀ fun _ h => propext_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem choice_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.choice_name st) lst
      (choiceName) :=
  LS.ofSim₀ fun _ h => choice_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.iff_name st) lst
      (iffName) :=
  LS.ofSim₀ fun _ h => iff_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_intro_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.iff_intro_name st) lst
      (iffIntroName) :=
  LS.ofSim₀ fun _ h => iff_intro_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_rec_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.iff_rec_name st) lst
      (iffRecName) :=
  LS.ofSim₀ fun _ h => iff_rec_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.nonempty_name st) lst
      (nonemptyName) :=
  LS.ofSim₀ fun _ h => nonempty_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_intro_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.nonempty_intro_name st) lst
      (nonemptyIntroName) :=
  LS.ofSim₀ fun _ h => nonempty_intro_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_rec_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.std_axioms.nonempty_rec_name st) lst
      (nonemptyRecName) :=
  LS.ofSim₀ fun _ h => nonempty_rec_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem erase_pw_eq_ls
    {pers st lst}
    {fuel : Std.U64}
    {a : arena.handle.EIdx}
    {b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.std_axioms.erase_pw_eq pers st fuel a b) st lst
      (erasePwEq (absU fuel) (absEIdx a) (absEIdx b)) :=
  LSR.ofSimRE hrel hinv fun _ h => erase_pw_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem erase_pw_eq_at_ls
    {pers st lst}
    {fuel : Std.U64}
    {va : arena.store.ENodeView}
    {vb : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.std_axioms.erase_pw_eq_at pers st fuel va vb) st lst
      (erasePwEqAtSpec (absU fuel) (absENodeView va) (absENodeView vb)) :=
  LSR.ofSimRE hrel hinv fun _ h => erase_pw_eq_at_refines hrel hinv h


open Lockstep in
@[lockstep] theorem erase_pw_eq_two_ls
    {pers st lst}
    {fuel : Std.U64}
    {a : arena.handle.EIdx}
    {a2 : arena.handle.EIdx}
    {b : arena.handle.EIdx}
    {b2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.std_axioms.erase_pw_eq_two pers st fuel a a2 b b2) st lst
      ((do
        if ← erasePwEq (absU fuel) (absEIdx a) (absEIdx b) then
          erasePwEq (absU fuel) (absEIdx a2) (absEIdx b2)
        else pure false)) :=
  LSR.ofSimRE hrel hinv fun _ h => erase_pw_eq_two_refines hrel hinv h


open Lockstep in
@[lockstep] theorem i_constant_val_matches_pin_ls
    {pers st lst}
    {cv : arena.env.IConstantVal}
    {pin : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.std_axioms.i_constant_val_matches_pin pers st cv pin) st lst
      ((absIConstantVal cv).matchesPin (absIConstantVal pin)) :=
  LSR.ofSimRE hrel hinv fun _ h => i_constant_val_matches_pin_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.iff_raw pers st) lst
      (iffRaw) :=
  LS.ofSim₀ fun _ h => iff_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_intro_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.iff_intro_raw pers st) lst
      (iffIntroRaw) :=
  LS.ofSim₀ fun _ h => iff_intro_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_rec_intro_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.std_axioms.iff_rec_intro pers st) lst
      (iffRecIntro) :=
  LS.ofSim₀ fun _ h => iff_rec_intro_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_rec_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.iff_rec_raw pers st) lst
      (iffRecRaw) :=
  LS.ofSim₀ fun _ h => iff_rec_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem iff_family_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a) (arena.std_axioms.iff_family pers st) lst
      (iffFamily) :=
  LS.ofSim₀ fun _ h => iff_family_refines hrel hinv h


open Lockstep in
@[lockstep] theorem propext_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.std_axioms.propext_raw pers st) lst
      (propextRaw) :=
  LS.ofSim₀ fun _ h => propext_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.nonempty_raw pers st) lst
      (nonemptyRaw) :=
  LS.ofSim₀ fun _ h => nonempty_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_intro_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.nonempty_intro_raw pers st) lst
      (nonemptyIntroRaw) :=
  LS.ofSim₀ fun _ h => nonempty_intro_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_rec_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.nonempty_rec_raw pers st) lst
      (nonemptyRecRaw) :=
  LS.ofSim₀ fun _ h => nonempty_rec_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nonempty_family_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absICIL a) (arena.std_axioms.nonempty_family pers st) lst
      (nonemptyFamily) :=
  LS.ofSim₀ fun _ h => nonempty_family_refines hrel hinv h


open Lockstep in
@[lockstep] theorem choice_raw_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.std_axioms.choice_raw pers st) lst
      (choiceRaw) :=
  LS.ofSim₀ fun _ h => choice_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem eq_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.eq_a pers st) lst
      (eqA) :=
  LS.ofSim₀ fun _ h => eq_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem nat_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantInfo a) (arena.std_axioms.nat_a pers st) lst
      (natA) :=
  LS.ofSim₀ fun _ h => nat_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem true_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.true_name st) lst
      (trueName) :=
  LS.ofSim₀ fun _ h => true_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem true_intro_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.true_intro_name st) lst
      (trueIntroName) :=
  LS.ofSim₀ fun _ h => true_intro_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem trust_compiler_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.trust_compiler_name st) lst
      (trustCompilerName) :=
  LS.ofSim₀ fun _ h => trust_compiler_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_nat_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.reduce_nat_name st) lst
      (reduceNatName) :=
  LS.ofSim₀ fun _ h => reduce_nat_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_bool_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.reduce_bool_name st) lst
      (reduceBoolName) :=
  LS.ofSim₀ fun _ h => reduce_bool_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_nat_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.of_reduce_nat_name st) lst
      (ofReduceNatName) :=
  LS.ofSim₀ fun _ h => of_reduce_nat_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_bool_name_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.of_reduce_bool_name st) lst
      (ofReduceBoolName) :=
  LS.ofSim₀ fun _ h => of_reduce_bool_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_op_ls
    {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.of_reduce_op st n) lst
      (ofReduceOp (absNIdx n)) :=
  LS.ofSim₀ fun _ h => of_reduce_op_refines hrel hinv h


open Lockstep in
@[lockstep] theorem true_cv_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.true_cv_a pers st) lst
      (trueCvA) :=
  LS.ofSim₀ fun _ h => true_cv_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem true_intro_cv_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.true_intro_cv_a pers st) lst
      (trueIntroCvA) :=
  LS.ofSim₀ fun _ h => true_intro_cv_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem trust_compiler_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.trust_compiler_a pers st) lst
      (trustCompilerA) :=
  LS.ofSim₀ fun _ h => trust_compiler_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem bool_cv_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.bool_cv_a pers st) lst
      (boolCvA) :=
  LS.ofSim₀ fun _ h => bool_cv_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_elem_name_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.trust_axioms.reduce_elem_name st c) lst
      (reduceElemName (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_elem_name_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_elem_ty_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.trust_axioms.reduce_elem_ty pers st c) lst
      (reduceElemTy (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_elem_ty_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_op_raw_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.reduce_op_raw pers st c) lst
      (reduceOpRaw (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_op_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_raw_ls
    {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.of_reduce_raw pers st n) lst
      (ofReduceRaw (absNIdx n)) :=
  LS.ofSim₀ fun _ h => of_reduce_raw_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_nat_cv_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.reduce_nat_cv_a pers st) lst
      (reduceNatCvA) :=
  LS.ofSim₀ fun _ h => reduce_nat_cv_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_bool_cv_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.reduce_bool_cv_a pers st) lst
      (reduceBoolCvA) :=
  LS.ofSim₀ fun _ h => reduce_bool_cv_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_nat_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.of_reduce_nat_a pers st) lst
      (ofReduceNatA) :=
  LS.ofSim₀ fun _ h => of_reduce_nat_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_bool_a_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.of_reduce_bool_a pers st) lst
      (ofReduceBoolA) :=
  LS.ofSim₀ fun _ h => of_reduce_bool_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_op_cv_a_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.reduce_op_cv_a pers st c) lst
      (reduceOpCvA (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_op_cv_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem of_reduce_pin_a_ls
    {pers st lst}
    {n : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIConstantVal a) (arena.trust_axioms.of_reduce_pin_a pers st n) lst
      (ofReducePinA (absNIdx n)) :=
  LS.ofSim₀ fun _ h => of_reduce_pin_a_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_bool_decl_pin_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.trust_axioms.reduce_bool_decl_pin pers st) lst
      (reduceBoolDeclPin) :=
  LS.ofSim₀ fun _ h => reduce_bool_decl_pin_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_nat_decl_pin_ls
    {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.trust_axioms.reduce_nat_decl_pin pers st) lst
      (reduceNatDeclPin) :=
  LS.ofSim₀ fun _ h => reduce_nat_decl_pin_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_decl_pin_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.trust_axioms.reduce_decl_pin pers st c) lst
      (reduceDeclPin (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_decl_pin_refines hrel hinv h


open Lockstep in
@[lockstep] theorem reduce_cert_var_ls
    {pers st lst}
    {c : arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.trust_axioms.reduce_cert_var pers st c) lst
      (reduceCertVar (absNIdx c)) :=
  LS.ofSim₀ fun _ h => reduce_cert_var_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_names_go_ls
    {pers st lst}
    {i n : Std.U64}
    {out : alloc.vec.Vec arena.handle.NIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.canon.canon_names_go pers st i n out) lst
      (do pure (absNIdxL out ++ (← canonNamesGo (absU i) (absU n)))) :=
  LS.ofSim₀ fun _ h => canon_names_go_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_names_ls
    {pers st lst}
    {n : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.canon.canon_names pers st n) lst
                             (canonNames (absU n)) :=
  LS.ofSim₀ fun _ h => canon_names_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_level_eq_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {u v : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_level_eq pers st ps ps2 cs fuel u v) st lst
      (canonLevelEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdx u) (absLIdx v)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_level_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_level_eq_at_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {a b : arena.store.LNodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_level_eq_at pers st ps ps2 cs fuel a b) st lst
      (canonLevelEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLNodeView a) (absLNodeView b)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_level_eq_at_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_level_list_eq_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {us vs : alloc.vec.Vec arena.handle.LIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_level_list_eq pers st ps ps2 cs fuel us vs i) st lst
      (canonLevelListEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdxLFrom us i) (absLIdxLFrom vs i)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_level_list_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_levels_eq_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {us vs : arena.handle.LsIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_levels_eq pers st ps ps2 cs fuel us vs) st lst
      (canonLevelsEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLsIdx us) (absLsIdx vs)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_levels_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_expr_eq_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {a b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_expr_eq pers st ps ps2 cs fuel a b) st lst
      (canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absEIdx a) (absEIdx b)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_expr_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_expr_eq_at_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {va vb : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_expr_eq_at pers st ps ps2 cs fuel va vb) st lst
      (canonExprEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absENodeView va) (absENodeView vb)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_expr_eq_at_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_expr_eq_two_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {a a2 b b2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_expr_eq_two pers st ps ps2 cs fuel a a2 b b2) st lst
      (do
        if ← canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a) (absEIdx b) then
          canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a2) (absEIdx b2)
        else pure false) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_expr_eq_two_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_rules_eq_ls
    {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx}
    {fuel : Std.U64}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a) (arena.canon.canon_rules_eq pers st ps ps2 cs fuel rs rs2 i) st lst
      (canonRulesEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absIRecRuleLFrom rs i) (absIRecRuleLFrom rs2 i)) :=
  LSR.ofSimRE hrel hinv fun _ h => canon_rules_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem i_constant_val_canon_eq_ls
    {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.i_constant_val_canon_eq pers st cv cv2) lst
      ((absIConstantVal cv).canonEq (absIConstantVal cv2)) :=
  LS.ofSim₀ fun _ h => i_constant_val_canon_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_eq_cv_and_rules_ls
    {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.canon_eq_cv_and_rules pers st cv cv2 rs rs2) lst
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonRulesEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absIRecRuleL rs) (absIRecRuleL rs2)
        else pure false) :=
  LS.ofSim₀ fun _ h => canon_eq_cv_and_rules_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_eq_cv_and_value_ls
    {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {v v2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.canon_eq_cv_and_value pers st cv cv2 v v2) lst
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonExprEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absEIdx v) (absEIdx v2)
        else pure false) :=
  LS.ofSim₀ fun _ h => canon_eq_cv_and_value_refines hrel hinv h


open Lockstep in
@[lockstep] theorem i_constant_info_canon_eq_ls
    {pers st lst}
    {ci ci2 : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.i_constant_info_canon_eq pers st ci ci2) lst
      ((absIConstantInfo ci).canonEq (absIConstantInfo ci2)) :=
  LS.ofSim₀ fun _ h => i_constant_info_canon_eq_refines hrel hinv h


open Lockstep in
@[lockstep] theorem canon_eq_list_ls
    {pers st lst}
    {xs ys : alloc.vec.Vec arena.env.IConstantInfo}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.canon_eq_list pers st xs ys i) lst
      (canonEqList (absICILFrom xs i) (absICILFrom ys i)) :=
  LS.ofSim₀ fun _ h => canon_eq_list_refines hrel hinv h


end IndPrims

theorem IFEnv.restrictTo_of_eq {lf : IFEnv} {k : Nat} (h : k = lf.visibleBelow) :
    lf.restrictTo k = lf := by
  subst h; rfl

-- A checker-tier statement at a split counter reads `lf.restrictTo (absU vis)`;
-- where the counter is the environment's own (`hvis`), that IS `lf`.
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (apply IFEnv.restrictTo_of_eq; assumption))

attribute [lockstep] proj_table_name_lss

end ConRon.Refine2
