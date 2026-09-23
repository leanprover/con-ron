/-
# `ConRon.Refine2.Frontend.Types` — `crates/con-ron-core/src/frontend/types.rs`

**Task #97-P5-Frontend.**  The seam's own module: the record verdict, the
three `ModelCtx` readers, the reducibility height and the two-function
`wants`.  Seven `pub fn`s and the `DeclineModeller` instance.

**All eight statements are closed**, which is what one expects of a module
with no store in it: `record_verdict_to_error` and `hint_height` are one
`rfl` each past the generated `match`, `wants`/`wants_nested` is the tier's
first cursor induction (`Refine2/ExprOps/Pure.lean`'s shape — a measure
induction on the remaining `Vec`, and the shape step *is* the proof), and the
three `ctx_*` readers are `CtxRel`'s three clauses read back.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConRon.Refine.HashMap2 (Inv toFun)

/-! ## The record verdict -/

/-- **`types::record_verdict_to_error` refines `RecordVerdict.toError`**
(`Arena/Frontend/Types.lean:58-63`).  What is claimed is the KIND: a verdict's
message is a message like any other and the theorem does not read one
(DESIGN §3.1). -/
theorem record_verdict_to_error_refines {v : frontend.types.RecordVerdict}
    {lv : Arena.Frontend.RecordVerdict} {e : kernel.core_types.CheckError}
    (hk : lVerdictKind lv = absVerdictKind v)
    (h : frontend.types.record_verdict_to_error v = ok e) :
    absAErrKind e = lAErrKind lv.toError := by
  rw [frontend.types.record_verdict_to_error.eq_def] at h
  cases v <;> cases lv <;> simp [lVerdictKind, absVerdictKind] at hk <;>
    simp only [kernel.core_types.not_implemented, kernel.core_types.invalid,
      Result.ok.injEq] at h <;> subst h <;>
    simp [Arena.Frontend.RecordVerdict.toError, absAErrKind, lAErrKind]

/-! ## The reducibility height -/

/-- **`types::hint_height` refines `hintHeight`**
(`Arena/Frontend/Types.lean:145-147`). -/
theorem hint_height_refines {h : kernel.env.ReducibilityHint} {n : Std.U64}
    (hr : frontend.types.hint_height h = ok n) :
    absU n = Arena.Frontend.hintHeight (ConRon.Refine.absHint h) := by
  rw [frontend.types.hint_height.eq_def] at hr
  cases h <;> simp only [Result.ok.injEq] at hr <;> subst hr <;>
    simp [Arena.Frontend.hintHeight, ConRon.Refine.absHint]

/-! ## The `ModelCtx` readers

The port's three are `HashMap2::get` on a borrowed table; the twin's `Ctx` has
three FUNCTIONS, because con-leche's `InModel.Ctx` does (`types.rs`'s own
deviation: §3.4 has no closures, so the port carries the tables and reads
them by hand).  `CtxRel` is the bridge and these three are it read back. -/

/-- **`types::ctx_tbl` refines the twin's `Ctx.tbl`.** -/
theorem ctx_tbl_refines {rc : frontend.types.ModelCtx} {lc : Arena.Frontend.Ctx}
    {n : arena.handle.NIdx}
    {o : Option ((alloc.vec.Vec arena.handle.NIdx) × arena.handle.EIdx)}
    (hrel : CtxRel rc lc) (h : frontend.types.ctx_tbl rc n = ok o) :
    lc.tbl (absNIdx n) = o.map fun p => (p.1.val.map absNIdx, absEIdx p.2) := by
  rw [frontend.types.ctx_tbl] at h
  rw [hrel.tbl n, nidx_get hrel.tblInv h]

/-- **`types::ctx_height` refines the twin's `Ctx.heights`.**  The port answers
`0` on a miss, where the twin's field is total — the one clause of `CtxRel`
that is not a plain probe agreement. -/
theorem ctx_height_refines {rc : frontend.types.ModelCtx} {lc : Arena.Frontend.Ctx}
    {n : arena.handle.NIdx} {v : Std.U64}
    (hrel : CtxRel rc lc) (h : frontend.types.ctx_height rc n = ok v) :
    lc.heights (absNIdx n) = absU v := by
  rw [frontend.types.ctx_height] at h
  obtain ⟨r, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hr := nidx_get hrel.heightsInv hg
  rw [hrel.heights n, ← hr]
  cases r with
  | none => simp only [Result.ok.injEq] at h; subst h; simp [absU]
  | some x => simp only [Result.ok.injEq] at h; subst h; simp

/-- **`types::ctx_block` refines the twin's `Ctx.blocks`.** -/
theorem ctx_block_refines {rc : frontend.types.ModelCtx} {lc : Arena.Frontend.Ctx}
    {n : arena.handle.NIdx} {o : Option frontend.types.BlockRec}
    (hrel : CtxRel rc lc) (h : frontend.types.ctx_block rc n = ok o) :
    lc.blocks (absNIdx n) = o.map absBlockRec := by
  rw [frontend.types.ctx_block] at h
  rw [hrel.blocks n, nidx_get hrel.blocksInv h]

/-! ## `wants`

The twin's `b.types.any (·.numNested > 0)` against the port's cursor
recursion — DESIGN §3.4's standing `List`-as-cursor deviation, and the tier's
first measure induction. -/

/-- The cursor companion, stated at the type list FROM the cursor on. -/
theorem wants_nested_refines_aux (n : Nat) :
    ∀ {b : frontend.types.BlockRec} {i : Std.Usize} {v : Bool},
      b.types.val.length - i.val = n →
      frontend.types.wants_nested b i = ok v →
      v = ((b.types.val.drop i.val).map absMIndTypeRec).any (·.numNested > 0) := by
  induction n with
  | zero =>
    intro b i v hn h
    rw [frontend.types.wants_nested] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by omega)]
      simp
    · rename_i hlt
      exfalso
      have : i.val < b.types.val.length := by scalar_tac
      omega
  | succ m ih =>
    intro b i v hn h
    rw [frontend.types.wants_nested] at h
    split at h
    · rename_i hge
      exfalso
      have : ¬ i.val < b.types.val.length := by scalar_tac
      omega
    · rename_i hlt
      have hlt' : i.val < b.types.val.length := by scalar_tac
      obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hget := ConRon.Refine2.vec_index_some ht
      have ht' : b.types.val[i.val]'hlt' = t := by
        rw [List.getElem?_eq_getElem hlt'] at hget
        exact Option.some.inj hget
      have hd : b.types.val.drop i.val = t :: b.types.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt', ht']
      rw [hd]
      simp only [List.map_cons, List.any_cons]
      split at h
      · rename_i hnz
        simp only [Result.ok.injEq] at h
        subst h
        have hpos : (absMIndTypeRec t).numNested > 0 := by
          simp only [absMIndTypeRec]
          have : (0#u64 : Std.U64).val < t.num_nested.val := by scalar_tac
          simpa [absU] using this
        simp
        exact Or.inl (by simpa [absMIndTypeRec] using hpos)
      · rename_i hz
        have hzz : ¬ ((absMIndTypeRec t).numNested > 0) := by
          simp only [absMIndTypeRec]
          have : ¬ (0#u64 : Std.U64).val < t.num_nested.val := by scalar_tac
          simpa [absU] using this
        obtain ⟨j, hj, hgo⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hjv : j.val = i.val + 1 := usize_add_one_inv hj
        have hih := ih (b := b) (i := j) (v := v) (by omega) hgo
        rw [hjv] at hih
        simp [hih]
        exact fun hc => absurd hc (by simpa [absMIndTypeRec] using hzz)

/-- **`types::wants_nested` refines the twin's `any` from the cursor on.** -/
theorem wants_nested_refines {b : frontend.types.BlockRec} {i : Std.Usize} {v : Bool}
    (h : frontend.types.wants_nested b i = ok v) :
    v = ((b.types.val.drop i.val).map absMIndTypeRec).any (·.numNested > 0) :=
  wants_nested_refines_aux _ rfl h

/-- **`types::wants` refines `wants`** (`Arena/Frontend/Types.lean:151-153`). -/
theorem wants_refines {b : frontend.types.BlockRec} {v : Bool}
    (h : frontend.types.wants b = ok v) :
    v = Arena.Frontend.wants (absBlockRec b) := by
  rw [frontend.types.wants] at h
  rw [Arena.Frontend.wants]
  simp only [absBlockRec, List.length_map]
  split at h
  · rename_i hgt
    have : 1 < b.types.val.length := by scalar_tac
    simp only [Result.ok.injEq] at h
    subst h
    simp [decide_eq_true this]
  · rename_i hle
    have hle' : ¬ 1 < b.types.val.length := by scalar_tac
    have hw := wants_nested_refines h
    rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hw
    simp [decide_eq_false hle', hw]

/-! ## The seam's trivial instantiation

`types::DeclineModeller` declines every block with a fixed sentence, and the
twin's `declineModeller` does the same.  The statement is `ModellerRefines` at
the pair, and it is the one place this tier can DISCHARGE the modeller
hypothesis rather than carry it — which is what makes the hypothesis honest:
it is satisfiable. -/

/-- **`DeclineModeller` refines `declineModeller`.**  Both decline every block
and touch no store, so the relation is the one the caller started with and
the message is not compared. -/
theorem decline_modeller_refines :
    ModellerRefines frontend.types.DeclineModeller.Insts.Con_ron_coreFrontendTypesModeller
      () Arena.Frontend.declineModeller where
  generate := by
    intro pers rst lst rc lc b o hrel hinv _hctx h
    simp only
      [frontend.types.DeclineModeller.Insts.Con_ron_coreFrontendTypesModeller.generate] at h
    obtain ⟨s', -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨lst, ?_, ?_, ?_⟩
    · simpa using hrel
    · simpa using hinv
    · exact ⟨_, rfl⟩

/-! ## The axiom census

Every closed lemma of this file, pinned.  `Classical.choice` enters through
the `DecidableEq` instances `HashMap2.toFun` needs (`Refine2/AbsState.lean`'s
note says why nothing is lost by them). -/

/-- info: 'ConRon.Refine2.Frontend.record_verdict_to_error_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms record_verdict_to_error_refines

/-- info: 'ConRon.Refine2.Frontend.hint_height_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hint_height_refines

/-- info: 'ConRon.Refine2.Frontend.ctx_tbl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ctx_tbl_refines

/-- info: 'ConRon.Refine2.Frontend.ctx_height_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ctx_height_refines

/-- info: 'ConRon.Refine2.Frontend.ctx_block_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ctx_block_refines

/-- info: 'ConRon.Refine2.Frontend.wants_nested_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wants_nested_refines

/-- info: 'ConRon.Refine2.Frontend.wants_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wants_refines

/-- info: 'ConRon.Refine2.Frontend.decline_modeller_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decline_modeller_refines

end ConRon.Refine2.Frontend
