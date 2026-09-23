/-
# `ConRon.Refine2.AbsState` — the rest of `AState`, and the environment

**Deliverable 1 of task #97 P5, part 3.**  `Refine2/AbsStore.lean` relates the
arena; this file relates the other three fields of `arena::monad::AState` —
the eleven-plus-two per-call `Memos`, the fourteen per-declaration `Caches`
(the readback memo among them) and the `Pins` record — and the declaration
layer `arena::env` puts over it: `IConstantVal`, `IRecRule`, `IIndCaps`,
`IProjTable`, `IProjEntry`, `IConstantInfo`, `IDeclaration`, `IEnv` and the
indexed `IFEnv`.

## Three representation differences, and where each is absorbed

1. **`Vec` against `List` or `Array`.**  `IConstantVal.level_params` is a
   `Vec<NIdx>` against the twin's `List NIdx`, `IProjTable.bodies` a
   `Vec<EIdx>` against an `Array EIdx`, `Pins.reserved` a `Vec` against a
   `List`.  One `map` each; the twin's own choice of container per field is
   con-leche's (`Arena/Env.lean` follows `ConLeche/Kernel/Env.lean` field for
   field), so there is nothing to decide here.
2. **`IEnv.consts` runs the other way.**  The twin's is con-leche's
   newest-first `List` and the Rust's is an oldest-first `Vec` (its index
   stores a POSITION into it), so the abstraction reverses — exactly as
   `RefineOld/Abs.lean`'s `absEnv` did for the `Expr`-tree checker.
3. **`IFEnv.idx` stores a POSITION where the twin stores the CONSTANT**
   (task #97-P6-5's lever 1, absorbed there and owed here).  The Rust's
   index is `HashMap<NIdx, (u64, u64)>` — the installation counter and the
   position — and `ifenv_find` reads the constant out of `env.consts` at that
   position; the twin's is `HashMap NIdx (Nat × IConstantInfo)`.  `IFEnvRel`
   therefore composes the probe with the array read, which is the one clause
   of this file that is not a field-for-field map.
-/
import ConRon.Refine2.Inv
import ConRon.Arena.Env

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn sl_v)

/-! ## Decidable equality of the memo and cache key types -/

noncomputable instance : DecidableEq arena.monad.EIdxNat := Classical.decEq _
noncomputable instance : DecidableEq arena.core_state.EIdxPair := Classical.decEq _
noncomputable instance : DecidableEq arena.core_state.LIdxPair := Classical.decEq _
noncomputable instance : DecidableEq arena.core_state.LsIdxPair := Classical.decEq _
noncomputable instance : DecidableEq arena.core_state.NLsKey := Classical.decEq _
noncomputable instance : DecidableEq arena.core_state.NNLsKey := Classical.decEq _
noncomputable instance : DecidableEq arena.handle.EIdx := Classical.decEq _
noncomputable instance : DecidableEq arena.handle.NIdx := Classical.decEq _
noncomputable instance : DecidableEq arena.handle.LIdx := Classical.decEq _
noncomputable instance : DecidableEq arena.handle.LsIdx := Classical.decEq _

/-! ## The memo and cache KEYS

Every one is a record of handles and one `u64` cursor, so every abstraction
is a tuple and every `Eq2Fwd` is `grind`. -/

def absEIdxNat (k : arena.monad.EIdxNat) : EIdx × Nat := (absEIdx k.h, absU k.d)
def absEIdxPair (k : arena.core_state.EIdxPair) : EIdx × EIdx :=
  (absEIdx k.a, absEIdx k.b)
def absLIdxPair (k : arena.core_state.LIdxPair) : LIdx × LIdx :=
  (absLIdx k.a, absLIdx k.b)
def absLsIdxPair (k : arena.core_state.LsIdxPair) : LsIdx × LsIdx :=
  (absLsIdx k.a, absLsIdx k.b)
def absNLsKey (k : arena.core_state.NLsKey) : NIdx × LsIdx :=
  (absNIdx k.n, absLsIdx k.us)
def absNNLsKey (k : arena.core_state.NNLsKey) : NIdx × NIdx × LsIdx :=
  (absNIdx k.rec_name, absNIdx k.ctor, absLsIdx k.us)

attribute [simp] absEIdxNat absEIdxPair absLIdxPair absLsIdxPair absNLsKey
  absNNLsKey

theorem eidxNat_eq2 :
    Eq2Fwd arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.monad.EIdxNat => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w⟩, d⟩ := a; obtain ⟨⟨w'⟩, d'⟩ := b
  simp only [arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2, bind_tc_ok] at h
  grind

theorem eidxPair_eq2 :
    Eq2Fwd arena.core_state.EIdxPair.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.core_state.EIdxPair => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.core_state.EIdxPair.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2, bind_tc_ok] at h
  grind

theorem lidxPair_eq2 :
    Eq2Fwd arena.core_state.LIdxPair.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.core_state.LIdxPair => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.core_state.LIdxPair.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2, bind_tc_ok] at h
  grind

theorem lsidxPair_eq2 :
    Eq2Fwd arena.core_state.LsIdxPair.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.core_state.LsIdxPair => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.core_state.LsIdxPair.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2, bind_tc_ok] at h
  grind

theorem nlsKey_eq2 :
    Eq2Fwd arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.core_state.NLsKey => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := a; obtain ⟨⟨w3⟩, ⟨w4⟩⟩ := b
  simp only [arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2, bind_tc_ok] at h
  grind

theorem nnlsKey_eq2 :
    Eq2Fwd arena.core_state.NNLsKey.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.core_state.NNLsKey => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨⟨w1⟩, ⟨w2⟩, ⟨w3⟩⟩ := a; obtain ⟨⟨w4⟩, ⟨w5⟩, ⟨w6⟩⟩ := b
  simp only [arena.core_state.NNLsKey.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2,
    arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2, bind_tc_ok] at h
  grind

theorem eidx_eq2 :
    Eq2Fwd arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.handle.EIdx => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨w⟩ := a; obtain ⟨w'⟩ := b
  simp only [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem nidx_eq2 :
    Eq2Fwd arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.handle.NIdx => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨w⟩ := a; obtain ⟨w'⟩ := b
  simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem lidx_eq2 :
    Eq2Fwd arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.handle.LIdx => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨w⟩ := a; obtain ⟨w'⟩ := b
  simp only [arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

theorem lsidx_eq2 :
    Eq2Fwd arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2
      (fun _ : arena.handle.LsIdx => True) := by
  apply eq2Fwd_of_iff
  intro a b c _ _ h
  obtain ⟨w⟩ := a; obtain ⟨w'⟩ := b
  simp only [arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  grind

/-! ## The per-call memo tables

Thirteen `RelOn` clauses at `P := True`: every key is handles and a cursor,
so the `Eq2` dictionaries above are unrestricted.  One structure rather than
thirteen hypotheses, so that a spec theorem states what a call touched in ONE
equation (`Arena/Monad.lean`'s own reason for grouping them). -/

structure MemosRel (rm : arena.monad.Memos) (lm : Memos) : Prop where
  inst1C : RelOn (fun _ => True) rm.inst1_c lm.inst1C absEIdxNat absEIdx
  instLC : RelOn (fun _ => True) rm.inst_l_c lm.instLC absEIdxNat absEIdx
  liftC : RelOn (fun _ => True) rm.lift_c lm.liftC absEIdxNat absEIdx
  resetC : RelOn (fun _ => True) rm.reset_c lm.resetC absEIdxNat absEIdx
  renameC : RelOn (fun _ => True) rm.rename_c lm.renameC absEIdxNat absEIdx
  abs1C : RelOn (fun _ => True) rm.abs1_c lm.abs1C absEIdxNat absEIdx
  lowerC : RelOn (fun _ => True) rm.lower_c lm.lowerC absEIdxNat absEIdx
  inst1LC : RelOn (fun _ => True) rm.inst1_l_c lm.inst1LC absEIdxNat absEIdx
  instLPC : RelOn (fun _ => True) rm.inst_lp_c lm.instLPC absEIdxNat absEIdx
  bvarBC : RelOn (fun _ => True) rm.bvar_b_c lm.bvarBC absEIdx absU
  fvarBC : RelOn (fun _ => True) rm.fvar_b_c lm.fvarBC absEIdx absU
  instLPLC : RelOn (fun _ => True) rm.inst_lp_l_c lm.instLPLC absLIdx absLIdx
  instLPLsC : RelOn (fun _ => True) rm.inst_lp_ls_c lm.instLPLsC absLsIdx absLsIdx

structure MemosInv (rm : arena.monad.Memos) : Prop where
  inst1C : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.inst1_c
  instLC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.inst_l_c
  liftC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.lift_c
  resetC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.reset_c
  renameC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.rename_c
  abs1C : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.abs1_c
  lowerC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.lower_c
  inst1LC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.inst1_l_c
  instLPC : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm.inst_lp_c
  bvarBC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm.bvar_b_c
  fvarBC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm.fvar_b_c
  instLPLC : Inv arena.handle.LIdx.Insts.Con_ron_coreRonHashmapHashable rm.inst_lp_l_c
  instLPLsC :
    Inv arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapHashable rm.inst_lp_ls_c

/-! ## The per-declaration caches

Eleven handle-valued tables plus the three readback memos of task #97-P6-13,
whose VALUES are transient `ConLeche.Level` / `Name` / `List Level` trees —
so those three carry a value-well-formedness clause in `CachesInv`, which is
what makes a memo HIT hand its caller a `LevelWF` answer (the same clause
`RefineOld/State.lean`'s `StateWF` carried for the same reason). -/

structure CachesRel (rc : arena.core_state.Caches) (lc : Caches) : Prop where
  whnfCoreC : RelOn (fun _ => True) rc.whnf_core_c lc.whnfCoreC absEIdx absEIdx
  whnfC : RelOn (fun _ => True) rc.whnf_c lc.whnfC absEIdx absEIdx
  inferC : RelOn (fun _ => True) rc.infer_c lc.inferC absEIdx absEIdx
  inferIOC : RelOn (fun _ => True) rc.infer_io_c lc.inferIOC absEIdx absEIdx
  annotC : RelOn (fun _ => True) rc.annot_c lc.annotC absEIdx absEIdx
  defeqC : RelOn (fun _ => True) rc.defeq_c lc.defeqC absEIdxPair id
  lvlEqC : RelOn (fun _ => True) rc.lvl_eq_c lc.lvlEqC absLIdxPair id
  lvlsEqC : RelOn (fun _ => True) rc.lvls_eq_c lc.lvlsEqC absLsIdxPair id
  constTyC : RelOn (fun _ => True) rc.const_ty_c lc.constTyC absNLsKey absEIdx
  constValC : RelOn (fun _ => True) rc.const_val_c lc.constValC absNLsKey absEIdx
  ruleRhsC : RelOn (fun _ => True) rc.rule_rhs_c lc.ruleRhsC absNNLsKey absEIdx
  readLC : RelOn (fun _ => True) rc.read_l_c lc.readLC absLIdx
    ConRon.Refine.absLevel
  readNC : RelOn (fun _ => True) rc.read_n_c lc.readNC absNIdx
    ConRon.Refine.absName
  readLsC : RelOn (fun _ => True) rc.read_ls_c lc.readLsC absLsIdx
    ConRon.Refine.absLevels

structure CachesInv (rc : arena.core_state.Caches) : Prop where
  whnfCoreC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable
    rc.whnf_core_c
  whnfC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rc.whnf_c
  inferC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rc.infer_c
  inferIOC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rc.infer_io_c
  annotC : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rc.annot_c
  defeqC : Inv arena.core_state.EIdxPair.Insts.Con_ron_coreRonHashmapHashable
    rc.defeq_c
  lvlEqC : Inv arena.core_state.LIdxPair.Insts.Con_ron_coreRonHashmapHashable
    rc.lvl_eq_c
  lvlsEqC : Inv arena.core_state.LsIdxPair.Insts.Con_ron_coreRonHashmapHashable
    rc.lvls_eq_c
  constTyC : Inv arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapHashable
    rc.const_ty_c
  constValC : Inv arena.core_state.NLsKey.Insts.Con_ron_coreRonHashmapHashable
    rc.const_val_c
  ruleRhsC : Inv arena.core_state.NNLsKey.Insts.Con_ron_coreRonHashmapHashable
    rc.rule_rhs_c
  readLC : Inv arena.handle.LIdx.Insts.Con_ron_coreRonHashmapHashable rc.read_l_c
  readNC : Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rc.read_n_c
  readLsC : Inv arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapHashable rc.read_ls_c
  /-- The readback memos' values are well-formed trees: what makes a HIT hand
  its caller the `LevelWF` / `NameWF` a miss would have handed it. -/
  readLVals : ∀ p ∈ sl_v rc.read_l_c, ConRon.Refine.LevelWF p.2
  readNVals : ∀ p ∈ sl_v rc.read_n_c, ConRon.Refine.NameWF p.2
  readLsVals : ∀ p ∈ sl_v rc.read_ls_c, ConRon.Refine.LevelsWF p.2

/-! ## The pin table -/

structure PinsRel (rp : arena.pins.Pins) (lp : Pins) : Prop where
  names : lp.names.toList = rp.names.val.map absNIdx
  reserved : lp.reserved = rp.reserved.val.map absNIdx
  emptyLevels : lp.emptyLevels = absLsIdx rp.empty_levels
  zeroLevel : lp.zeroLevel = absLIdx rp.zero_level
  sortOne : lp.sortOne = absEIdx rp.sort_one

/-! ## The whole state -/

/-- **Deprecated shim** (task #97-T2-LOCKSTEP): Theorem 2's relation is
`AStateRel₀` below; `storeWF` is Theorem 1's invariant and leaves Theorem 2
lane by lane.  **`absState`**, as a relation: `(pers, st)` against the twin's
`AState`.

**`storeWF` — finding 16's clause, task #97-P5-Specs.**  Task #97-P5-3 round 3
measured that an interning walk's every step needs `StoreWF` at the store it
stands on: `EStore.intern`'s own `intern_wf` is stated against it, and round 3
§2's `hchild_*` derive finding 14's child condition from it.  `AOut` said
nothing about well-formedness, so 81 % of the inductives tier and 43 of the 44
interning walks of `Refine2/ExprOps/Mut.lean` could not travel.  Task
#97-P5-Bracket then met the same gap from the other end: `AOutRel`'s `Ext`
conjunct is FALSE across a declaration bracket without it, because a
persistent node whose child is a scratch handle denotes before the drop and
not after.

The clause lives HERE, on the relation, rather than as a conditional conjunct
`StoreWF lst.store → StoreWF lst'.store` on `AOut`'s success arm, and that is
the cheaper of the two by a wide margin:

* `AOut`'s success arm already delivers `AStateRel pers st' lst'`, so the STEP
  form falls out of the STATE form — no new conjunct, and no implication to
  thread through the tier's 185 `AOut.ok` sites and 31 `SimS.mk` sites;
* it is proved once per PRODUCER — twelve sites, all in `Refine2/Specs.lean`
  — instead of once per consumer;
* and the Theorem-2 capstones keep `AStateRel`/`AStateInv` and nothing else,
  instead of growing a universally quantified `TwinWF` side condition.

`Arena/WFProofs.lean`'s `EStore.intern_wf` is what discharges it at an intern,
with `ECapAt` (round 3 §1, from the port's own `Tbl::full`) for its `capOK`
and an explicit `ViewOK` hypothesis for its children. -/
structure AStateRel (pers : arena.store.PersTier) (rs : arena.monad.AState)
    (ls : AState) : Prop where
  store : StoreRel pers rs.store ls.store
  memos : MemosRel rs.memos ls.memos
  caches : CachesRel rs.caches ls.caches
  pins : PinsRel rs.pins ls.pins
  /-- **Finding 16**: the TWIN store is well formed — Theorem 1's invariant,
  carried by Theorem 2's relation. -/
  storeWF : StoreWF ls.store

/-- **The lockstep relation**: `AStateRel` without `storeWF` (task
#97-P5-Core round 4, the coordinator's ruling (i) on its finding).  `storeWF`
is a statement about the TWIN's term DAG — Theorem 1 content — and it is what
made a knot statement false at a state both programs handle alike: the port
and the twin both intern `app d a` over a dangling `d` without looking at it,
their stores stay equal field for field, and only `StoreWF` fails.  The Core
tier's `KnotRel`/`BodyRel` are stated over this; the rest of the tier moves to
it later (tier-wide migration, scheduled separately), and until then
`AStateRel` keeps its five fields and these two lemmas convert. -/
structure AStateRel₀ (pers : arena.store.PersTier) (rs : arena.monad.AState)
    (ls : AState) : Prop where
  store : StoreRel pers rs.store ls.store
  memos : MemosRel rs.memos ls.memos
  caches : CachesRel rs.caches ls.caches
  pins : PinsRel rs.pins ls.pins

/-- The projection a consumer of the lockstep relation takes. -/
theorem AStateRel.to₀ {pers : arena.store.PersTier} {rs : arena.monad.AState}
    {ls : AState} (h : AStateRel pers rs ls) : AStateRel₀ pers rs ls :=
  ⟨h.store, h.memos, h.caches, h.pins⟩

/-- Back again, given the twin's own invariant. -/
theorem AStateRel₀.of₀ {pers : arena.store.PersTier} {rs : arena.monad.AState}
    {ls : AState} (h : AStateRel₀ pers rs ls) (hwf : StoreWF ls.store) :
    AStateRel pers rs ls :=
  ⟨h.store, h.memos, h.caches, h.pins, hwf⟩

/-- `AStateRel` is the lockstep relation and the twin's invariant, and nothing
else. -/
theorem AStateRel_iff {pers : arena.store.PersTier} {rs : arena.monad.AState}
    {ls : AState} : AStateRel pers rs ls ↔ AStateRel₀ pers rs ls ∧ StoreWF ls.store :=
  ⟨fun h => ⟨h.to₀, h.storeWF⟩, fun h => h.1.of₀ h.2⟩

/-- The Rust-side invariant of the whole state. -/
structure AStateInv (pers : arena.store.PersTier) (rs : arena.monad.AState) :
    Prop where
  store : StoreInv pers rs.store
  memos : MemosInv rs.memos
  caches : CachesInv rs.caches

/-! ## The declaration layer (`arena::env`)

Field-for-field, `Vec` to the container the twin has; the two places the
shape genuinely moves are `IEnv.consts`' order and `IFEnv.idx`'s value, and
the module note says why. -/

def absIConstantVal (cv : arena.env.IConstantVal) : IConstantVal :=
  ⟨absNIdx cv.name, cv.level_params.val.map absNIdx, absEIdx cv.ty⟩

def absIRecRuleFire : arena.env.IRecRuleFire → IRecRuleFire
  | .Inert => .inert
  | .Plain => .plain
  | .Nested lvls pins =>
    .nested (lvls.val.map absLIdx) (pins.val.map absEIdx)

def absIRecRule (r : arena.env.IRecRule) : IRecRule :=
  ⟨absNIdx r.ctor, absU r.nfields, absU r.ctor_params, absIRecRuleFire r.fire,
    absEIdx r.rhs, r.k, r.eta, r.params_blind⟩

def absIIndCaps (c : arena.env.IIndCaps) : IIndCaps :=
  ⟨c.eta, absNIdx c.eta_ctor, absU c.eta_params, absU c.eta_fields, c.unitlike,
    absU c.unit_params, c.rule_k, ConRon.Refine.absPropWhen c.sort_z⟩

def absIProjTable (t : arena.env.IProjTable) : IProjTable :=
  ⟨absNIdx t.struct_name, absNIdx t.table_name, t.level_params.val.map absNIdx,
    absU t.num_params, absNIdx t.ctor, absU t.num_fields, absLIdx t.struct_sort,
    (t.bodies.val.map absEIdx).toArray, t.guards.val.map absLIdx, absU t.off⟩

def absIConstantInfo : arena.env.IConstantInfo → IConstantInfo
  | .AxiomInfo cv => .axiomInfo (absIConstantVal cv)
  | .DefnInfo cv v hint =>
    .defnInfo (absIConstantVal cv) (absEIdx v) (ConRon.Refine.absHint hint)
  | .ThmInfo cv v => .thmInfo (absIConstantVal cv) (absEIdx v)
  | .IndInfo cv caps => .indInfo (absIConstantVal cv) (absIIndCaps caps)
  | .CtorInfo cv np nf => .ctorInfo (absIConstantVal cv) (absU np) (absU nf)
  | .RecInfo cv mi rp rules =>
    .recInfo (absIConstantVal cv) (absU mi) (absU rp)
      (rules.val.map absIRecRule)
  | .ProjInfo tbl => .projInfo (absIProjTable tbl)

def absIDeclaration : arena.env.IDeclaration → IDeclaration
  | .AxiomDecl cv => .axiomDecl (absIConstantVal cv)
  | .DefnDecl cv v hint =>
    .defnDecl (absIConstantVal cv) (absEIdx v) (ConRon.Refine.absHint hint)
  | .ThmDecl cv v => .thmDecl (absIConstantVal cv) (absEIdx v)
  | .OpaqueDecl cv v => .opaqueDecl (absIConstantVal cv) (absEIdx v)
  | .BasisDecl k => .basisDecl (ConRon.Refine.absBasisKind k)
  | .IndDecl block np =>
    .indDecl (block.val.map absIConstantInfo) (absU np)
  | .QuotDecl k cv =>
    .quotDecl (ConRon.Refine.absQuotKind k) (absIConstantVal cv)

/-- `IEnv.consts` runs the other way: con-leche's list is newest-first and the
port's `Vec` is oldest-first, its index storing a position into it. -/
def absIEnv (e : arena.env.IEnv) : IEnv :=
  ⟨(e.consts.val.map absIConstantInfo).reverse⟩

/-- **The one clause that is not a field map** (task #97-P6-5's lever 1): the
Rust's index answers `(counter, position)` and `ifenv_find` reads the constant
out of `env.consts` at that position, where the twin's index answers
`(counter, constant)`.  The relation composes the probe with the array read,
and an out-of-range position — which `ifenv_find` declines — is `none` on the
twin's side too. -/
structure IFEnvRel (rf : arena.env.IFEnv) (lf : IFEnv) : Prop where
  env : lf.env = absIEnv rf.env
  idx : ∀ n, ((ConRon.Refine.HashMap2.toFun rf.idx n).bind fun p =>
      (rf.env.consts.val[p.2.val]?).map fun ci => (absU p.1, absIConstantInfo ci))
    = lf.idx[absNIdx n]?
  visibleBelow : lf.visibleBelow = absU rf.visible_below

end ConRon.Refine2
