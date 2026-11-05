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

/-! ## The Core tier's side-goal extension

A fact about an element of a list the context quantifies over (a binder
stack's datum well-formedness, `∀ x ∈ stk.val, PropWhenWF x.2.pw`), through
the shared tactic's extension tier. -/

macro_rules
  | `(tactic| lockstep_side_ext) => `(tactic| (solve_by_elim (maxDepth := 3) [List.getElem_mem]))

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

@[local lockstep_simp] theorem core_walk_fuel_val :
    (arena.core.CORE_WALK_FUEL).val = coreWalkFuel := core_walk_fuel_abs

attribute [local lockstep_simp] etag_const_abs etag_lit_abs etag_fvar_abs

/-! ## Well-formedness facts in context

A read that carries the Rust datum's well-formedness states it as
`∀ l, o = some l → WF l`; after the case split on `o` that is
`∀ l, some x = some l → WF l`, which these reduce to `WF x`. -/

attribute [local lockstep_simp] Option.some.injEq forall_eq' ConRon.Refine.LiteralWF IConstantInfoWF

/-! ## The environment -/

/-- `arena::env::IProjEntry` as the twin's `IProjEntry`, field for field. -/
def absIProjEntry (e : arena.env.IProjEntry) : IProjEntry :=
  ⟨absNIdx e.struct_name, absU e.idx, e.level_params.val.map absNIdx, absU e.num_params,
    absNIdx e.ctor, absU e.num_fields, absEIdx e.body, absLIdx e.field_sort,
    absLIdx e.struct_sort⟩

attribute [local lockstep_simp] absIProjEntry



attribute [local lockstep_simp] absIConstantInfo

/-- `arena::env::ifenv_find` against `IFEnv.find?`: the twin's lookup is a
pure expression, so the pair is a `TwinEq` the twin side is rewritten with;
and the constant found is canonical Rust data (the coordinator's ruling (d) of
task #97-P5-Core round 5). -/
@[lockstep] theorem ifenv_find_ls {pers : arena.store.PersTier} {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers vis fe lfe) (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find pers vis fe n)
      (fun o => TwinEq (lfe.find? (absNIdx n)) (o.map absIConstantInfo) ∧
        ∀ ci, o = some ci → IConstantInfoWF ci) :=
  fun _ h => ⟨(ifenv_find_abs' hctx h).1.symm, (ifenv_find_abs' hctx h).2⟩

@[lockstep] theorem reducibility_hint_dup_ls (h : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_dup h) (fun r => r = h) := by
  intro r hr
  cases h <;> simp [kernel.env.reducibility_hint_dup] at hr <;> exact hr.symm

/-! ## The `ExprOps` walks, through the `ExprOpsHyp` seam

Each wrapper's `hx : ExprOpsHyp pers` premise is closed from the context by
`assumption`: a body lemma carries the bundle as a hypothesis, and
`Core/Arms.lean`'s `exprOpsHyp` is the one place it is discharged. -/

@[lockstep] theorem is_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx pers vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.is_proof_fast pers vis st fe fuel a)
      lst (isProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.isProofFast hrel hinv hctx h

@[lockstep] theorem not_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst vis fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx pers vis fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.not_proof_fast pers vis st fe fuel a)
      lst (notProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.notProofFast hrel hinv hctx h

/-! ## The Core lemmas closed before round 5, as `@[lockstep]` -/

@[lockstep] theorem ensure_sort_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode eager lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.ensure_sort pers vis st mode eager lane fu fe depth e) lst
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => ensure_sort_refines hk hrel hinv hctx hf h

@[lockstep] theorem unfold_definition_ls {pers vis st fe lfe e lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers vis fe lfe) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.unfold_definition pers vis st fe e) lst
      (unfoldDefinition lfe (absEIdx e)) :=
  LS.ofSim₀ fun _ h => unfold_definition_refines hx hrel hinv hctx h

/-! ## The projection-table lookups -/

theorem i_proj_table_entry_abs {tbl : arena.env.IProjTable} {i : Std.U64}
    {ie : arena.env.IProjEntry} (h : arena.env.i_proj_table_entry tbl i = ok ie) :
    absIProjEntry ie = (absIProjTable tbl).entry (absU i) := by
  rw [arena.env.i_proj_table_entry] at h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi2v : i2.val = tbl.bodies.val.length := by
    simp only [lift, Result.ok.injEq] at hi2; subst hi2
    simp
  obtain ⟨body, hbody, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi4v : i4.val = tbl.guards.val.length := by
    simp only [lift, Result.ok.injEq] at hi4; subst hi4
    simp
  obtain ⟨fs, hfs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_nidx _ _ hn1, dupId_lidx _ _ hl]
  have hvv := nidx_vec_dup_val hv
  have hb : absEIdx body = (tbl.bodies.val.map absEIdx).toArray.getD i.val default := by
    split at hbody
    · rename_i hlt
      obtain ⟨j, hj, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
      obtain ⟨e, he, hbody⟩ := ConRon.Refine.bind_eq_ok_iff.mp hbody
      have hjv : j.val = i.val := by
        simp only [lift, Result.ok.injEq] at hj; subst hj
        have hlen := tbl.bodies.property
        exact ConRon.Refine.ExprOps.u64_cast_usize_val_of_lt (n := tbl.bodies.val.length)
          hlen (by scalar_tac)
      obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
      rw [dupId_eidx _ _ hbody]
      subst hx
      have : i.val < tbl.bodies.val.length := by scalar_tac
      simp [Array.getD, this, hjv]
    · rename_i hge
      rw [← Result.ok_injective hbody]
      have : ¬ i.val < tbl.bodies.val.length := by scalar_tac
      simp [Array.getD, this]; rfl
  have hg : absLIdx fs = (tbl.guards.val.map absLIdx).getD i.val default := by
    split at hfs
    · rename_i hlt
      obtain ⟨j, hj, hfs⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfs
      obtain ⟨e, he, hfs⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfs
      have hjv : j.val = i.val := by
        simp only [lift, Result.ok.injEq] at hj; subst hj
        have hlen := tbl.guards.property
        exact ConRon.Refine.ExprOps.u64_cast_usize_val_of_lt (n := tbl.guards.val.length)
          hlen (by scalar_tac)
      obtain ⟨hb, hx⟩ := ExprOps.vecIndexAt he
      rw [dupId_lidx _ _ hfs]
      subst hx
      have : i.val < tbl.guards.val.length := by scalar_tac
      simp [List.getD, this, hjv]
    · rename_i hge
      rw [← Result.ok_injective hfs]
      have : ¬ i.val < tbl.guards.val.length := by scalar_tac
      simp [List.getD, this]; rfl
  simp only [absIProjEntry, absIProjTable, IProjTable.entry, hb, hg, hvv]

/-- A stored slot in range is read. -/
private theorem read_tbl_slot {ts : alloc.vec.Vec arena.env.IProjTable} {s : Std.U64} {o}
    (hslt : s.val < ts.val.length)
    (hrun : (do
        let i2 ← lift (Std.UScalar.cast .Usize s)
        if i2 < alloc.vec.Vec.len ts then
          (do
            let i4 ← lift (Std.UScalar.cast .Usize s)
            let it ← alloc.vec.Vec.index
              (core.slice.index.SliceIndexUsizeSlice arena.env.IProjTable) ts i4
            ok (some it))
        else ok none : Result (Option arena.env.IProjTable)) = ok o) :
    o.map absIProjTable = tblOf ts s := by
  have hsfit : s.val ≤ Std.Usize.max := le_of_lt (lt_of_lt_of_le hslt ts.property)
  obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hi2v : i2.val = s.val := by
    rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hsfit]
    exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi2).symm
  have hb : i2 < alloc.vec.Vec.len ts := by
    apply (Std.UScalar.lt_equiv _ _).mpr
    rw [hi2v, alloc.vec.Vec.len_val]
    exact hslt
  rw [ite_eq_left hb] at hrun
  obtain ⟨i4, hi4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨it, hit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  cases Result.ok_injective hrun
  have hi4v : i4.val = s.val := by
    rw [← ConRon.Refine.ExprOps.u64_cast_usize_val hsfit]
    exact congrArg Aeneas.Std.UScalar.val (Result.ok_injective hi4).symm
  have hit' := vec_index_some hit
  rw [hi4v] at hit'
  simp [tblOf, hit']

/-- **`arena::env::ifenv_table_base` against `baseTbl`**: gated on the structure's
row at the layer's bound. -/
theorem ifenv_table_base_abs {pers : arena.store.PersTier} {below : Std.U64}
    (hb : BaseOK pers) {t : arena.handle.NIdx} {o : Option arena.env.IProjTable}
    (hrun : arena.env.ifenv_table_base pers below t = ok o) :
    o.map absIProjTable = baseTbl pers below t := by
  rw [arena.env.ifenv_table_base] at hrun
  obtain ⟨oc, hoc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hf := (ifenv_find_base_abs hb hoc).1
  have hgate : oc.isSome = (baseRow pers below t).isSome := by
    have hrow : rowAt (absU below) (baseRow pers below t) =
        (baseRow pers below t).map Prod.snd := by
      unfold baseRow
      cases ConRon.Refine.HashMap2.toFun pers.env.idx t with
      | none => rfl
      | some p =>
        simp only [Option.bind_some]
        by_cases hd : absU p.1 < absU below
        · rw [ite_eq_left hd, rowOf]
          cases pers.env.env.consts.val[p.2.val]? with
          | none => rfl
          | some ci => simp [rowAt, hd]
        · rw [ite_eq_right hd]; rfl
    rw [hrow] at hf
    have := congrArg Option.isSome hf
    simpa using this
  unfold baseTbl
  rw [← hgate]
  simp only [core.option.Option.is_some] at hrun
  cases oc with
  | none =>
    simp at hrun ⊢
    cases hrun; rfl
  | some ci =>
    simp only [Option.isSome_some, ite_true] at hrun ⊢
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hb.inv.2.2.2.1
      ConRon.Refine.HashMap2.KeysOk_true trivial hr
    rw [← hto]
    cases r with
    | none => cases Result.ok_injective hrun; rfl
    | some s =>
      exact read_tbl_slot (hb.inv.2.2.2.2 t s hto.symm) hrun

/-- **`arena::env::ifenv_raw_table` against `IFEnv.rawTable?`**: the own map, then the
base's, gated: `CoreCtx.tbls` is that composition. -/
theorem ifenv_raw_table_abs {pers : arena.store.PersTier} {vis : Std.U64} {fe : arena.env.IFEnv}
    {lfe : IFEnv} (hctx : CoreCtx pers vis fe lfe) {t : arena.handle.NIdx}
    {o : Option arena.env.IProjTable}
    (hrun : arena.env.ifenv_raw_table pers fe t = ok o) :
    o.map absIProjTable = lfe.rawTable? (absNIdx t) := by
  rw [IFEnv.rawTable?, ← hctx.tbls t]
  rw [arena.env.ifenv_raw_table] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hctx.inv.2.2.2.1
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  unfold layerTbl
  rw [← hto]
  cases r with
  | none => exact ifenv_table_base_abs hctx.base hrun
  | some s => exact read_tbl_slot (hctx.inv.2.2.2.2 t s hto.symm) hrun

/-- **`arena::env::ifenv_find_table` against `IFEnv.findTable?`**: gated by
the structure's own lookup, as the twin is. -/
theorem ifenv_find_table_abs {pers : arena.store.PersTier} {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers vis fe lfe) {t : arena.handle.NIdx}
    {o : Option arena.env.IProjTable}
    (hrun : arena.env.ifenv_find_table pers vis fe t = ok o) :
    o.map absIProjTable = lfe.findTable? (absNIdx t) := by
  rw [arena.env.ifenv_find_table] at hrun
  obtain ⟨oc, hoc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hf := ifenv_find_abs hctx hoc
  rw [IFEnv.findTable?, ← hf]
  cases oc with
  | none =>
    cases Result.ok_injective hrun
    rfl
  | some ci =>
    exact ifenv_raw_table_abs hctx hrun

/-- **`arena::env::ifenv_find_proj` against `IFEnv.findProj?`**: the
structure's table, viewed at field `i`. -/
theorem ifenv_find_proj_abs {pers : arena.store.PersTier} {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers vis fe lfe) {t : arena.handle.NIdx} {i : Std.U64}
    {o : Option arena.env.IProjEntry}
    (hrun : arena.env.ifenv_find_proj pers vis fe t i = ok o) :
    o.map absIProjEntry = lfe.findProj? (absNIdx t) (absU i) := by
  rw [arena.env.ifenv_find_proj] at hrun
  obtain ⟨ot, hot, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hf := ifenv_find_table_abs hctx hot
  rw [IFEnv.findProj?, ← hf]
  cases ot with
  | none =>
    cases Result.ok_injective hrun
    rfl
  | some tbl =>
    simp only [Option.map_some]
    simp only at hrun
    split at hrun
    · rename_i hlt
      obtain ⟨ie, hie, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      have hlt' : absU i < (absIProjTable tbl).numFields := by
        simp only [absIProjTable, absU]; exact hlt
      rw [ite_eq_left hlt', Option.map_some, i_proj_table_entry_abs hie]
    · rename_i hge
      cases Result.ok_injective hrun
      have hge' : ¬ absU i < (absIProjTable tbl).numFields := by
        simp only [absIProjTable, absU]; exact hge
      rw [ite_eq_right hge']
      rfl

/-- The table lookup (`ifenv_find_table`) against `IFEnv.findTable?`, as
`ifenv_find_ls`. -/
@[lockstep] theorem ifenv_find_table_ls {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers vis fe lfe) (t : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find_table pers vis fe t)
      (fun o => TwinEq (lfe.findTable? (absNIdx t)) (o.map absIProjTable)) :=
  fun _ h => (ifenv_find_table_abs hctx h).symm

/-- The projection-table lookup (`ifenv_find_proj`) against
`IFEnv.findProj?`: a pure read on both sides, a `TwinEq` the twin side is
rewritten with, as `ifenv_find_ls`. -/
@[lockstep] theorem ifenv_find_proj_ls {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers vis fe lfe) (t : arena.handle.NIdx) (i : Std.U64) :
    LSP (arena.env.ifenv_find_proj pers vis fe t i)
      (fun o => TwinEq (lfe.findProj? (absNIdx t) (absU i)) (o.map absIProjEntry)) :=
  fun _ h => (ifenv_find_proj_abs hctx h).symm

end ConRon.Refine2.Lockstep

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2
attribute [scoped lockstep_simp] core_walk_fuel_val etag_const_abs etag_lit_abs
  etag_fvar_abs Option.some.injEq forall_eq' ConRon.Refine.LiteralWF
  IConstantInfoWF absIProjEntry absIConstantInfo
end ConRon.Refine2.Lockstep.CoreLSReg
