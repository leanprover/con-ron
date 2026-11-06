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

attribute [local lockstep_simp] Option.some.injEq forall_eq' ConRon.Refine.LiteralWF

/-! ## The environment -/

/-- `arena::env::IProjEntry` as the twin's `IProjEntry`, field for field. -/
def absIProjEntry (e : arena.env.IProjEntry) : IProjEntry :=
  ⟨absNIdx e.struct_name, absU e.idx, e.level_params.val.map absNIdx, absU e.num_params,
    absNIdx e.ctor, absU e.num_fields, absEIdx e.body⟩

attribute [local lockstep_simp] absIProjEntry



attribute [local lockstep_simp] absIConstantInfo

/-- `arena::env::ifenv_find` against `IFEnv.find?`: the twin's lookup is a
pure expression, so the pair is a `TwinEq` the twin side is rewritten with. -/
@[lockstep] theorem ifenv_find_ls {pers : arena.store.PersTier} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers fe lfe) (n : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find pers fe n)
      (fun o => TwinEq (lfe.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs hctx h).symm

@[lockstep] theorem reducibility_hint_dup_ls (h : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_dup h) (fun r => r = h) := by
  intro r hr
  cases h <;> simp [kernel.env.reducibility_hint_dup] at hr <;> exact hr.symm

/-! ## The `ExprOps` walks, through the `ExprOpsHyp` seam

Each wrapper's `hx : ExprOpsHyp pers` premise is closed from the context by
`assumption`: a body lemma carries the bundle as a hypothesis, and
`Core/Arms.lean`'s `exprOpsHyp` is the one place it is discharged. -/

@[lockstep] theorem is_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx pers fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.is_proof_fast pers st fe fuel a)
      lst (isProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.isProofFast hrel hinv hctx h

@[lockstep] theorem not_proof_fast_ls {pers} (hx : ExprOpsHyp pers) {st lst fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx pers fe lfe)
    (fuel a) :
    LS pers (fun a b => b = a) (arena.prop_read.not_proof_fast pers st fe fuel a)
      lst (notProofFast lfe (absU fuel) (absEIdx a)) :=
  LS.ofSim₀ (A := id) fun _ h => hx.notProofFast hrel hinv hctx h

/-! ## The Core lemmas closed before round 5, as `@[lockstep]` -/

@[lockstep] theorem ensure_sort_ls {f : Nat} (hk : KnotRel f)
    {pers st mode eager lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absLIdx a)
      (arena.core.ensure_sort pers st mode eager lane fu fe depth e) lst
      (ensureSort (laneKnot (ConRon.Refine.absMode mode) eager lfe lane f) lfe
        (absU depth) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => ensure_sort_refines hk hrel hinv hctx hf h

@[lockstep] theorem unfold_definition_ls {pers st fe lfe e lst}
    (hx : ExprOpsHyp pers) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx pers fe lfe) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.unfold_definition pers st fe e) lst
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
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_nidx _ _ hn1]
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
  simp only [absIProjEntry, absIProjTable, IProjTable.entry, hb, hvv]

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
    o.map absIProjTable = (ts.val[s.val]?).map absIProjTable := by
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
  simp [hit']

/-- **`arena::env::ifenv_table_base` against the stream index's table**
(`ixTbl`), visible below the layer's record bound. -/
theorem ifenv_table_base_abs {pers : arena.store.PersTier} {below : Std.U64}
    (hb : BaseOK pers) {t : arena.handle.NIdx} {o : Option arena.env.IProjTable}
    (hrun : arena.env.ifenv_table_base pers below t = ok o) :
    o.map absIProjTable =
      (ixTbl pers.env t).bind fun r => if r.1 < absU below then some r.2 else none := by
  rw [arena.env.ifenv_table_base] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hb.tbls
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  unfold ixTbl
  rw [← hto]
  cases r with
  | none => cases Result.ok_injective hrun; rfl
  | some e =>
    obtain ⟨rp, sl⟩ := e
    simp only [Option.bind_some] at ⊢
    change (if rp < below then _ else ok none) = ok o at hrun
    by_cases hd : rp < below
    · rw [ite_eq_left hd] at hrun
      have hd' : absU rp < absU below := (Std.UScalar.lt_equiv rp below).mp hd
      have hrd := read_tbl_slot (hb.tblRange t (rp, sl) hto.symm) hrun
      rw [hrd]
      cases pers.env.tables.val[sl.val]? <;> simp [hd']
    · rw [ite_eq_right hd] at hrun
      cases Result.ok_injective hrun
      have hd' : ¬ absU rp < absU below := fun h => hd ((Std.UScalar.lt_equiv rp below).mpr h)
      cases pers.env.tables.val[sl.val]? <;> simp [hd']

/-- The twin's base table lookup, as `BaseRel` and the layer's record bound read it. -/
theorem IFBase_findTable?_of_rel {ix : arena.stream_index.IStreamIndex} {b : IFBase}
    (hb : BaseRel ix b) (t : arena.handle.NIdx) :
    b.findTable? (absNIdx t) =
      (ixTbl ix t).bind fun r => if r.1 < b.belowRec then some r.2 else none := by
  rw [IFBase.findTable?, ← hb.tbls t]
  cases ixTbl ix t with
  | none => rfl
  | some r => obtain ⟨c, tb⟩ := r; rfl

/-- **`arena::env::ifenv_raw_table` against `IFEnv.rawTable?`**: the own map, then the
base's at the layer's record bound. -/
theorem ifenv_raw_table_abs {pers : arena.store.PersTier} {fe : arena.env.IFEnv}
    {lfe : IFEnv} (hctx : CoreCtx pers fe lfe) {t : arena.handle.NIdx}
    {o : Option arena.env.IProjTable}
    (hrun : arena.env.ifenv_raw_table pers fe t = ok o) :
    o.map absIProjTable = lfe.rawTable? (absNIdx t) := by
  rw [IFEnv.rawTable?, ← hctx.tbls t]
  rw [arena.env.ifenv_raw_table] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hctx.inv.2.2.1
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  unfold ownTbl
  rw [← hto]
  cases r with
  | none =>
    simp only [Option.bind_none]
    rw [IFBase_findTable?_of_rel hctx.base t, hctx.belowRec]
    exact ifenv_table_base_abs hctx.baseOK hrun
  | some s =>
    simp only [Option.bind_some]
    have hlt := hctx.inv.2.2.2 t s hto.symm
    rw [read_tbl_slot hlt hrun, List.getElem?_eq_getElem hlt]
    rfl

/-- **`arena::env::ifenv_find_table` against `IFEnv.findTable?`**: gated by
the structure's own lookup, as the twin is. -/
theorem ifenv_find_table_abs {pers : arena.store.PersTier} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers fe lfe) {t : arena.handle.NIdx}
    {o : Option arena.env.IProjTable}
    (hrun : arena.env.ifenv_find_table pers fe t = ok o) :
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
theorem ifenv_find_proj_abs {pers : arena.store.PersTier} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers fe lfe) {t : arena.handle.NIdx} {i : Std.U64}
    {o : Option arena.env.IProjEntry}
    (hrun : arena.env.ifenv_find_proj pers fe t i = ok o) :
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
@[lockstep] theorem ifenv_find_table_ls {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers fe lfe) (t : arena.handle.NIdx) :
    LSP (arena.env.ifenv_find_table pers fe t)
      (fun o => TwinEq (lfe.findTable? (absNIdx t)) (o.map absIProjTable)) :=
  fun _ h => (ifenv_find_table_abs hctx h).symm

/-- The projection-table lookup (`ifenv_find_proj`) against
`IFEnv.findProj?`: a pure read on both sides, a `TwinEq` the twin side is
rewritten with, as `ifenv_find_ls`. -/
@[lockstep] theorem ifenv_find_proj_ls {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx pers fe lfe) (t : arena.handle.NIdx) (i : Std.U64) :
    LSP (arena.env.ifenv_find_proj pers fe t i)
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
  absIProjEntry absIConstantInfo
end ConRon.Refine2.Lockstep.CoreLSReg
