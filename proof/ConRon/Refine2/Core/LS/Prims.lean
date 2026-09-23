/-
# `ConRon.Refine2.Core.LS.Prims` — the Core tier's primitive pairs that need `CoreCtx`

Task #97-P5-Core round 5.  The `@[lockstep]` pairs whose statement needs the
Core tier's own context (`CoreCtx`, `ExprOpsHyp`) and so cannot live in
`Tactic/Prims.lean`, which the Core tier imports.
-/
import ConRon.Refine2.Core.LS.Knot

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## Converters from the `AOut₀` form -/

theorem LSR.ofAOut₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : ∀ o, m = ok o → AOut₀ A pers o st (x.run lst)) :
    LSR pers (fun a b => b = A a) m st lst x := by
  intro o hm
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := this
    exact ⟨_, lst', hx, rfl, h1, h2⟩

/-! ## Scalars and constants -/

@[lockstep_simp] theorem core_walk_fuel_val :
    (arena.core.CORE_WALK_FUEL).val = coreWalkFuel := core_walk_fuel_abs

attribute [lockstep_simp] etag_const_abs etag_lit_abs etag_fvar_abs

@[lockstep_simp] theorem absU32_beq_const (t : Std.U32) :
    (absU32 t == ETag.const) = decide (t = arena.handle.ETAG_CONST) := by
  rw [← etag_const_abs]
  by_cases h : t = arena.handle.ETAG_CONST
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_CONST := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_lit (t : Std.U32) :
    (absU32 t == ETag.lit) = decide (t = arena.handle.ETAG_LIT) := by
  rw [← etag_lit_abs]
  by_cases h : t = arena.handle.ETAG_LIT
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_LIT := fun hc => h (absU32_inj hc)
    simp [h, this]

@[lockstep_simp] theorem absU32_beq_fvar (t : Std.U32) :
    (absU32 t == ETag.fvar) = decide (t = arena.handle.ETAG_FVAR) := by
  rw [← etag_fvar_abs]
  by_cases h : t = arena.handle.ETAG_FVAR
  · subst h; simp
  · have : absU32 t ≠ absU32 arena.handle.ETAG_FVAR := fun hc => h (absU32_inj hc)
    simp [h, this]

/-! ## Handle equality, one normal form

The port's `eq2` on handles is stated `r = (absNIdx a == absNIdx b)` by some
prims and `r = decide (absNIdx a = absNIdx b)` by others; both twin spellings
occur (`c = entry.ctor` in an `if`, `n₁ == n₂` in a `pure`).  The `lockstep_simp`
normal form is `decide (_ = _)`. -/

theorem idx_beq_decide {k : IdxKind} (a b : Idx k) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-! ## The two expression-list abstractions, one normal form

`Refine2/ExprOps/Read.lean`'s `ExprOps.absEIdxList` and `ExprOps/Mut.lean`'s
`absEIdxList` are the same map; `lockstep_simp` rewrites the first to the
second, and knows the length of both. -/

@[lockstep_simp] theorem absEIdxList_length_mut (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxList v).length = v.val.length := by
  simp [absEIdxList]

/-! ## The environment -/

/-- `arena::env::IProjEntry` as the twin's `IProjEntry`, field for field. -/
def absIProjEntry (e : arena.env.IProjEntry) : IProjEntry :=
  ⟨absNIdx e.struct_name, absU e.idx, e.level_params.val.map absNIdx, absU e.num_params,
    absNIdx e.ctor, absU e.num_fields, absEIdx e.body, absLIdx e.field_sort,
    absLIdx e.struct_sort, absU e.off⟩

attribute [lockstep_simp] absIProjEntry



attribute [lockstep_simp] absIConstantInfo

/-- `arena::env::ifenv_find` against `IFEnv.find?`: the twin's lookup is a
pure expression, so the pair is a `TwinEq` the twin side is rewritten with. -/
@[lockstep] theorem ifenv_find_ls {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx vis fe lfe) (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find vis fe n)
      (fun o => TwinEq (lfe.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs hctx h).symm

@[lockstep] theorem reducibility_hint_dup_ls (h : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_dup h) (fun r => r = h) := by
  intro r hr
  cases h <;> simp [kernel.env.reducibility_hint_dup] at hr <;> exact hr.symm

/-! ## The spine readers (read-only `ExprOps` walks, proved in `Core/Arms/Delta.lean`) -/

@[lockstep] theorem get_app_fn_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.get_app_fn pers st fuel h) st lst
      (getAppFn (absU fuel) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => get_app_fn_refines₀ hrel hinv hr

@[lockstep] theorem get_app_args_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = ExprOps.absEIdxList a)
      (arena.expr_ops.get_app_args pers st fuel h) st lst
      (getAppArgs (absU fuel) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => get_app_args_refines₀ hrel hinv hr

/-! ## The `const` name projection -/

@[lockstep] theorem view_const_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absNIdx a) (arena.monad.view_const_name pers st h)
      st lst (Arena.viewConstName (absEIdx h)) := by
  intro o hrun
  refine ⟨_, lst, rfl, ?_, hrel, hinv⟩
  rw [arena.monad.view_const_name] at hrun
  exact (estore_view_const_name_abs hrel.store hrun).symm ▸ rfl

/-! ## The `ExprOps` walks, through the `ExprOpsHyp` seam

Each wrapper's `hx : ExprOpsHyp pers` premise is closed from the context by
`assumption`: a body lemma carries the bundle as a hypothesis, and
`Core/Arms.lean`'s `exprOpsHyp` is the one place it is discharged. -/

@[lockstep] theorem inst_lp_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel lps us value) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_lp_fast pers st fuel lps us value)
      lst (instLPFast (absU fuel) (lps.val.map absNIdx) (absLsIdx us) (absEIdx value)) :=
  LS.ofSim₀ fun _ h => hx.instLPFast hrel hinv h

@[lockstep] theorem mk_app_n_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (f args) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n pers st f args)
      lst (Arena.mkAppN (absEIdx f) (absEIdxList args)) :=
  LS.ofSim₀ fun _ h => hx.mkAppN hrel hinv h

@[lockstep] theorem mk_app_n_from_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (f args i) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.mk_app_n_from pers st f args i)
      lst (mkAppNFrom (absEIdx f) (absEIdxArr args) (absSz i)) :=
  LS.ofSim₀ fun _ h => hx.mkAppNFrom hrel hinv h

@[lockstep] theorem instantiate1_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e v d) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.instantiate1_fast pers st fuel e v d)
      lst (instantiate1Fast (absU fuel) (absEIdx e) (absEIdx v) (absU d)) :=
  LS.ofSim₀ fun _ h => hx.instantiate1Fast hrel hinv h

@[lockstep] theorem instantiate_list_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e vs d) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.instantiate_list_fast pers st fuel e vs d)
      lst (instantiateListFast (absU fuel) (absEIdx e) (absEIdxArr vs) (absU d)) :=
  LS.ofSim₀ fun _ h => hx.instantiateListFast hrel hinv h

@[lockstep] theorem abstract1_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e d k) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.abstract1_fast pers st fuel e d k)
      lst (abstract1Fast (absU fuel) (absEIdx e) (absU d) (absU k)) :=
  LS.ofSim₀ fun _ h => hx.abstract1Fast hrel hinv h

@[lockstep] theorem abstract_range_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e d k c) :
    LS pers (fun a b => b = absEIdx a)
      (arena.expr_ops.abstract_range_fast pers st fuel e d k c)
      lst (abstractRangeFast (absU fuel) (absEIdx e) (absU d) (absU k) (absU c)) :=
  LS.ofSim₀ fun _ h => hx.abstractRangeFast hrel hinv h

@[lockstep] theorem inst_spine_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel args t e) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.inst_spine pers st fuel args t e)
      lst (instSpine (absU fuel) (absEIdxList args) (absU t) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hx.instSpine hrel hinv h

@[lockstep] theorem intern_rebuilt_app_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (h same f a) :
    LS pers (fun a b => b = absEIdx a) (arena.expr_ops.intern_rebuilt_app pers st h same f a)
      lst (internRebuiltApp (absEIdx h) same (absEIdx f) (absEIdx a)) :=
  LS.ofSim₀ fun _ hr => hx.internRebuiltApp hrel hinv hr

@[lockstep] theorem bvar_b_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e) :
    LS pers (fun a b => b = absU a) (arena.expr_ops.bvar_b pers st fuel e)
      lst (bvarB (absU fuel) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => hx.bvarB hrel hinv h

@[lockstep] theorem has_fvar_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel e) :
    LS pers (fun a b => b = a) (arena.expr_ops.has_fvar_fast pers st fuel e)
      lst (hasFvarFast (absU fuel) (absEIdx e)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.hasFvarFast hrel hinv h

@[lockstep] theorem loose_bvars_bounded_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel k e) :
    LS pers (fun a b => b = a) (arena.expr_ops.loose_bvars_bounded_fast pers st fuel k e)
      lst (looseBVarsBoundedFast (absU fuel) (absU k) (absEIdx e)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.looseBVarsBoundedFast hrel hinv h

@[lockstep] theorem lam_pw_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (h) :
    LSR pers (fun a b => b = ExprOps.absPwOpt a) (arena.expr_ops.lam_pw pers st h) st lst
      (lamPw (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => hx.lamPw hrel hinv hr

@[lockstep] theorem pi_result_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel h) :
    LSR pers (fun a b => b = absEIdx a) (arena.expr_ops.pi_result pers st fuel h) st lst
      (piResult (absU fuel) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => hx.piResult hrel hinv hr

@[lockstep] theorem strip_pis_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (k h) :
    LSR pers (fun a b => b = ExprOps.absStrip a) (arena.expr_ops.strip_pis pers st k h) st lst
      (stripPis (absU k) (absEIdx h)) :=
  LSR.ofAOut₀ fun _ hr => hx.stripPis hrel hinv hr

@[lockstep] theorem wscoped_b_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel d h) :
    LSR pers (fun a b => b = a) (arena.expr_ops.wscoped_b_fast pers st fuel d h) st lst
      (wscopedBFast (absU fuel) (absU d) (absEIdx h)) :=
  LSR.ofAOut₀ (A := id) fun _ hr => hx.wscopedBFast hrel hinv hr

@[lockstep] theorem leaf_guard_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (fuel fab base) :
    LSR pers (fun a b => b = a) (arena.expr_ops.leaf_guard pers st fuel fab base) st lst
      (leafGuard (absU fuel) (absEIdx fab) (absEIdx base)) :=
  LSR.ofAOut₀ (A := id) fun _ hr => hx.leafGuard hrel hinv hr

@[lockstep] theorem proof_pw_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = ExprOps.absPwOpt a) (arena.prop_read.proof_pw pers vis st fe fuel a)
      lst (proofPW lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ fun _ h => hx.proofPW hrel hinv hctx h

@[lockstep] theorem type_sort_pw_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel t) :
    LS pers (fun a b => b = ExprOps.absPwOpt a)
      (arena.prop_read.type_sort_pw pers vis st fe fuel t)
      lst (typeSortPW lfe (absU fuel) (absEIdx t)) :=
  LS.ofSim₀ fun _ h => hx.typeSortPW hrel hinv hctx h

@[lockstep] theorem is_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.is_proof_fast pers vis st fe fuel a)
      lst (isProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.isProofFast hrel hinv hctx h

@[lockstep] theorem not_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.not_proof_fast pers vis st fe fuel a)
      lst (notProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.notProofFast hrel hinv hctx h

/-! ## The Core lemmas closed before round 5, as `@[lockstep]` -/

@[lockstep] theorem ensure_sort_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.ensure_sort pers vis st mode lane fu fe depth e) lst
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => ensure_sort_refines hk hrel hinv hctx hf h

@[lockstep] theorem unfold_definition_ls {pers vis st fe lfe e lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.unfold_definition pers vis st fe e) lst
      (unfoldDefinition lfe (absEIdx e)) :=
  LS.ofSim₀ fun _ h => unfold_definition_refines hx hrel hinv hctx h

@[lockstep] theorem const_val_at_ls {pers st lst n lps value us}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.const_val_at pers st n lps value us) lst
      (constValAt (absNIdx n) (lps.val.map absNIdx) (absEIdx value) (absLsIdx us)) :=
  LS.ofSim₀ fun _ h => const_val_at_refines hx hrel hinv h

/-! ## The environment's name builders (region C1's proofs, shared)

`proj_fn_name` and `proj_table_name` intern two names on the bare store and
answer `(Result, EStore)`: store-level steps (`LSS`). -/

theorem code_points_from_val' (N : Nat) :
    ∀ (codes : Slice Std.U32) (i : Std.Usize) (out r : alloc.vec.Vec Std.U32),
      codes.val.length - i.val = N →
      kernel.core_types.code_points_from codes i out = ok r →
      r.val = out.val ++ codes.val.drop i.val := by
  induction N with
  | zero =>
    intro codes i out r hN h
    rw [kernel.core_types.code_points_from] at h
    rw [if_pos (by have := Slice.len_val codes; scalar_tac)] at h
    rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by omega)]; simp
  | succ N ih =>
    intro codes i out r hN h
    rw [kernel.core_types.code_points_from] at h
    rw [if_neg (by have := Slice.len_val codes; scalar_tac)] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hlt : i.val < codes.val.length := by omega
    have hxv : codes.val[i.val] = x := by
      simp only [Slice.index_usize] at hx
      cases hq : codes[i]? with
      | none => rw [hq] at hx; simp at hx
      | some y =>
        rw [hq] at hx
        have hyx : y = x := Result.ok_injective hx
        subst hyx
        have : codes.val[i.val]? = some y := hq
        rw [List.getElem?_eq_getElem hlt] at this
        exact Option.some_injective _ this
    have h2 := ConRon.Refine.Nat.uadd_val hi1
    rw [ih codes i1 o1 r (by simp at h2; omega) h, ConRon.Refine.vec_push_val ho1,
      show i1.val = i.val + 1 by simpa using h2, List.drop_eq_getElem_cons hlt, hxv]
    simp

theorem code_points_val' {codes : Slice Std.U32} {r : alloc.vec.Vec Std.U32}
    (h : kernel.core_types.code_points codes = ok r) : r.val = codes.val := by
  rw [kernel.core_types.code_points] at h
  rw [code_points_from_val' _ codes 0#usize _ r rfl h]
  simp [alloc.vec.Vec.with_capacity]

theorem proj_fn_name_str_abs {v : alloc.vec.Vec Std.U32}
    (h : kernel.core_types.code_points (Array.to_slice arena.env.proj_fn_name.S) = ok v) :
    ConRon.Refine.absString v = "proj" ∧ ConRon.Refine.StrWF v := by
  have hv : v.val = [112#u32, 114#u32, 111#u32, 106#u32] := by
    rw [code_points_val' h, Array.val_to_slice, arena.env.proj_fn_name.S,
      Array.make_val]
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absString, hv]; rfl
  · intro c hc; rw [hv] at hc; fin_cases hc <;> decide

theorem intern_n_node_of_estore {pers : arena.store.PersTier} {st : arena.monad.AState}
    {v : arena.store.NNodeView} {r e}
    (h : arena.store.EStore.intern_name st.store pers v = ok (r, e)) :
    arena.monad.intern_n_node pers st v = ok (r, { st with store := e }) := by
  rw [arena.monad.intern_n_node, h]; simp

/-- `arena::env::proj_fn_name` (two name interns on the bare store) against
`projFnName`. -/
@[lockstep] theorem proj_fn_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (t : arena.handle.NIdx) (j : Std.U64) :
    LSS pers (fun a b => b = absNIdx a) (arena.env.proj_fn_name pers st.store t j) st lst
      (projFnName (absNIdx t) (absU j)) := by
  intro o s' hm
  rw [arena.env.proj_fn_name] at hm
  obtain ⟨n, hn, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨sl, hsl, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨v, hv, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨⟨r1, ar1⟩, h1, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  simp only [lift, Result.ok.injEq] at hsl
  subst hsl
  have hnt : n = t := dupId_nidx _ _ hn
  subst hnt
  obtain ⟨hstr, hwf⟩ := proj_fn_name_str_abs hv
  have sim1 := intern_n_node_run₀ hrel hinv _ (by exact hwf) (intern_n_node_of_estore h1)
  have htw : projFnName (absNIdx n) (absU j)
      = (Arena.internNNode (absNNodeView (.Str n v)) >>= fun s =>
          Arena.internNNode (.num s (absU j))) := by
    rw [projFnName, absNNodeView, hstr]
  rw [htw]
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hm
    cases ho
    exact errSim_bind sim1
  | Ok s1 =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := sim1.apply
    rw [run_bind_ok hx1]
    have sim2 := intern_n_node_run₀ (st := { st with store := ar1 }) hrel1 hinv1
      (.Num s1 j) trivial (intern_n_node_of_estore hm)
    show LOut pers _ o { st with store := s' } _
    cases o with
    | Err e => exact sim2
    | Ok a =>
      obtain ⟨lst2, hx2, hrel2, hinv2⟩ := sim2.apply
      exact ⟨_, lst2, hx2, rfl, hrel2, hinv2⟩


/-- The projection-table lookup (`ifenv_find_proj`): it interns the table's
reserved name (`proj_table_name`), then reads the environment.  The Rust store
argument `s` is named apart from the state `st` the caller rebuilds (`hs`),
so a second lookup on the store the first one returned matches without
unifying `?st.store` with a store (region G's form). -/
@[lockstep] theorem ifenv_find_proj_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (s : arena.store.EStore) (hs : st.store = s)
    (t : arena.handle.NIdx) (i : Std.U64) :
    LSS pers (fun a b => b = Option.map absIProjEntry a)
      (arena.env.ifenv_find_proj pers vis s fe t i) st lst
      (lfe.findProj? (absNIdx t) (absU i)) := by
  sorry

end ConRon.Refine2.Lockstep
